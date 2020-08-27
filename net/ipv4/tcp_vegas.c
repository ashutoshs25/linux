// SPDX-License-Identifier: GPL-2.0-only
/*
 * TCP Vegas congestion control
 *
 * This is based on the congestion detection/avoidance scheme described in
 *    Lawrence S. Brakmo and Larry L. Peterson.
 *    "TCP Vegas: End to end congestion avoidance on a global internet."
 *    IEEE Journal on Selected Areas in Communication, 13(8):1465--1480,
 *    October 1995. Available from:
 *	ftp://ftp.cs.arizona.edu/xkernel/Papers/jsac.ps
 *
 * See http://www.cs.arizona.edu/xkernel/ for their implementation.
 * The main aspects that distinguish this implementation from the
 * Arizona Vegas implementation are:
 *   o We do not change the loss detection or recovery mechanisms of
 *     Linux in any way. Linux already recovers from losses quite well,
 *     using fine-grained timers, NewReno, and FACK.
 *   o To avoid the performance penalty imposed by increasing cwnd
 *     only every-other RTT during slow start, we increase during
 *     every RTT during slow start, just like Reno.
 *   o Largely to allow continuous cwnd growth during slow start,
 *     we use the rate at which ACKs come back as the "actual"
 *     rate, rather than the rate at which data is sent.
 *   o To speed convergence to the right rate, we set the cwnd
 *     to achieve the right ("actual") rate when we exit slow start.
 *   o To filter out the noise caused by delayed ACKs, we use the
 *     minimum RTT sample observed during the last RTT to calculate
 *     the actual rate.
 *   o When the sender re-starts from idle, it waits until it has
 *     received ACKs for an entire flight of new data before making
 *     a cwnd adjustment decision. The original Vegas implementation
 *     assumed senders never went idle.
 */

#include <linux/mm.h>
#include <linux/module.h>
#include <linux/skbuff.h>
#include <linux/inet_diag.h>

#include <net/tcp.h>

#include "tcp_vegas.h"


static int compete = 1;
static int comeback = 1;
static int betao = 2000;
static int gamma = 4;
static int delta = 100;
static unsigned int g = 4;
static int inc_thresh = 5;
static int starve_rst = 5;
static int rtt_fairness = 2;
static int hardcoding = 3;
static int basedelay_hc = 2000;
static int m = 50;

module_param(betao, int, 0644);
MODULE_PARM_DESC(betao, "delay threshold");
module_param(gamma, int, 0644);
MODULE_PARM_DESC(gamma, "RTT fairness scaling factor");
module_param(g, uint, 0644);
MODULE_PARM_DESC(g, "WMA shift parameter");
module_param(inc_thresh, int, 0644);
MODULE_PARM_DESC(inc_thresh, "consecutive starves before increasing threshold");
module_param(starve_rst, int, 0644);
MODULE_PARM_DESC(starve_rst, "reset starve counter to this threshold");
module_param(rtt_fairness, int, 0644);
MODULE_PARM_DESC(rtt_fairness, "RTT fairness mode 0-no change, 1-increasing speed in 5ms intervals, 2- directly proportional");
module_param(hardcoding, int, 0644);
MODULE_PARM_DESC(hardcoding, "0 - using socket basedelay,1 - using hardcoded based delay");
module_param(basedelay_hc, int, 0644);
MODULE_PARM_DESC(basedelay_hc, "value of basedelay to be used if hardcoding = 1");
module_param(m, int, 0644);
MODULE_PARM_DESC(m, "threshold increase factor * 100");
module_param(compete, int, 0644);
MODULE_PARM_DESC(compete, "1- competition enabled,2- no competition");
module_param(comeback, int, 0644);
MODULE_PARM_DESC(comeback, "1- resume low delay enabled,2- no resume low delay");
module_param(delta, int, 0644);
MODULE_PARM_DESC(delta, "Delta parameter");



/* There are several situations when we must "re-start" Vegas:
 *
 *  o when a connection is established
 *  o after an RTO
 *  o after fast recovery
 *  o when we send a packet and there is no outstanding
 *    unacknowledged data (restarting an idle connection)
 *
 * In these circumstances we cannot do a Vegas calculation at the
 * end of the first RTT, because any calculation we do is using
 * stale info -- both the saved cwnd and congestion feedback are
 * stale.
 *
 * Instead we must wait until the completion of an RTT during
 * which we actually receive ACKs.
 */
static void vegas_enable(struct sock *sk)
{
	const struct tcp_sock *tp = tcp_sk(sk);
	struct vegas *vegas = inet_csk_ca(sk);
	
	if (vegas->start == 0){
		vegas->beta = betao;
		vegas->start = 1;
		vegas->alpha = 1 << 8U;
		vegas->baseRTT = 0x7fffffff;
	}

	/* Begin taking Vegas samples next time we send something. */
	vegas->doing_vegas_now = 1;

	/* Set the beginning of the next send window. */
	vegas->beg_snd_nxt = tp->snd_nxt;

	vegas->cntRTT = 0;
	vegas->marked = 0;
	vegas->minRTT = 0x7fffffff;
	vegas->maxRTT = 0;
}

/* Stop taking Vegas samples for now. */
static inline void vegas_disable(struct sock *sk)
{
	struct vegas *vegas = inet_csk_ca(sk);

	vegas->doing_vegas_now = 0;
}

void tcp_vegas_init(struct sock *sk)
{
	struct vegas *vegas = inet_csk_ca(sk);

	vegas_enable(sk);
}
EXPORT_SYMBOL_GPL(tcp_vegas_init);


void tcp_vegas_pkts_acked(struct sock *sk, const struct ack_sample *sample)
{
	struct vegas *vegas = inet_csk_ca(sk);
	u32 vrtt;
	struct tcp_sock *tp = tcp_sk(sk);
	u32 basedelay;

	vegas->baseRTT = min(vegas->baseRTT, vrtt);

	if (hardcoding == 0)
        	basedelay = basedelay_hc;
        else if (hardcoding == 1)
             	basedelay = minmax_get(&tp->rtt_min);
       	else if (hardcoding == 2)
              	basedelay = vegas->baseRTT;
       	else
          	basedelay = max(vegas->baseRTT,minmax_get(&tp->rtt_min));
	
	if (sample->rtt_us < 0)
		return;

	/* Never allow zero rtt or baseRTT */
	vrtt = sample->rtt_us + 1;
	

	if (vrtt > (basedelay + vegas->beta))
		vegas->marked++;

	/* Find the min and max RTT during the last RTT to find
	 */
	vegas->minRTT = min(vegas->minRTT, vrtt);
	vegas->maxRTT = max(vegas->maxRTT,vrtt);
	vegas->cntRTT++;
}
EXPORT_SYMBOL_GPL(tcp_vegas_pkts_acked);

void tcp_vegas_state(struct sock *sk, u8 ca_state)
{
	if (ca_state == TCP_CA_Open)
		vegas_enable(sk);
	else
		vegas_disable(sk);
}
EXPORT_SYMBOL_GPL(tcp_vegas_state);

/*
 * If the connection is idle and we are restarting,
 * then we don't want to do any Vegas calculations
 * until we get fresh RTT samples.  So when we
 * restart, we reset our Vegas state to a clean
 * slate. After we get acks for this flight of
 * packets, _then_ we can make Vegas calculations
 * again.
 */
void tcp_vegas_cwnd_event(struct sock *sk, enum tcp_ca_event event)
{
	if (event == CA_EVENT_CWND_RESTART ||
	    event == CA_EVENT_TX_START)
		tcp_vegas_init(sk);
}
EXPORT_SYMBOL_GPL(tcp_vegas_cwnd_event);

static inline u32 tcp_vegas_ssthresh(struct tcp_sock *tp)
{
	return  min(tp->snd_ssthresh, tp->snd_cwnd);
}

static void tcp_vegas_cong_avoid(struct sock *sk, u32 ack, u32 acked)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct vegas *vegas = inet_csk_ca(sk);

	if (!vegas->doing_vegas_now) {
		tcp_reno_cong_avoid(sk, ack, acked);
		return;
	}

	if (after(ack, vegas->beg_snd_nxt)) {
		
		u32 basedelay;
		
		printk(KERN_INFO "marked=%d total=%d\n",vegas->marked,vegas->cntRTT);
                if (hardcoding == 0)
                        basedelay = basedelay_hc;
                else if (hardcoding == 1)
                        basedelay = minmax_get(&tp->rtt_min);
		else if (hardcoding == 2)
			basedelay = vegas->baseRTT;
		else
			basedelay = max(vegas->baseRTT,minmax_get(&tp->rtt_min));

		
		vegas->alpha = (((1 << g)-1)*vegas->alpha + 1*((vegas->marked << 8U) / vegas->cntRTT)) >> g;
		// vegas->alpha = (vegas->marked << i8U) / vegas->cntRTT;
		
		// algorithm for competing with loss based / new flows
		
		if (vegas->marked >= ((delta * vegas->cntRTT)/100))
			vegas->starve++;
		else{
			if (vegas->starve > 0)
				vegas->starve = 0;
		}

		if (vegas->starve >= inc_thresh){

			vegas->starve = starve_rst;
			u32 current_rtt;
			u32 threshold;

			current_rtt = (tp->srtt_us >> 3);
			threshold = basedelay + vegas->beta;

			if (current_rtt > threshold){
				
				// printk(KERN_INFO "old threshold=%d\n",vegas->beta);

				if (compete == 1)		
					vegas->beta = vegas->beta + ((m*(current_rtt - threshold))/100);

				
				// printk(KERN_INFO "new threshold=%d\n",vegas->beta);
			}

		}
		
		// resuming low delay operation

		
		if (vegas->maxRTT < (basedelay + vegas->beta) >> 1){

			if ((vegas->beta > betao) && (comeback == 1)) 
				vegas->beta = betao;
		}
		
		/* Do the Vegas once-per-RTT cwnd adjustment. */

		vegas->beg_snd_nxt  = tp->snd_nxt;

		if (vegas->cntRTT <= 2) {
			/* We don't have enough RTT samples to do the Vegas
			 * calculation, so we'll behave like Reno.
			 */
			tcp_reno_cong_avoid(sk, ack, acked);
		} else {
			u32 rtt;
			u64 target_cwnd;
			
			rtt = vegas->minRTT;

			target_cwnd = (u64)tp->snd_cwnd * basedelay;
			do_div(target_cwnd, rtt);

			if (vegas->marked > 0 && tcp_in_slow_start(tp)) {
				/* Going too fast. Time to slow down
				 * and switch to congestion avoidance.
				 */
				tp->snd_cwnd = min(tp->snd_cwnd, (u32)target_cwnd+1);
				tp->snd_ssthresh = tcp_vegas_ssthresh(tp);

			} else if (tcp_in_slow_start(tp)) {
				/* Slow start.  */
				tcp_slow_start(tp, acked);
			} else {
				/* Congestion avoidance. */

				if (vegas->marked > 0) {
					
					// fractional cwnd decrease (DCTCP)
					tp->snd_cwnd = ((tp->snd_cwnd << 8U) - ((tp->snd_cwnd * vegas->alpha) >> 1U)) >> 8U;
					tp->snd_ssthresh
						= tcp_vegas_ssthresh(tp);
				} else {
					/* We don't have enough extra packets
					 * in the network, so speed up.
					 */
					
					if (rtt_fairness == 0)
                                                tp->snd_cwnd++;          // additive increase
                                    	else if (rtt_fairness == 1)
                                             	tp->snd_cwnd = tp->snd_cwnd + 1 + (basedelay/5000);
                                      	else
                              			tp->snd_cwnd = tp->snd_cwnd + 1 + ((gamma * basedelay)/(basedelay + vegas->beta));
				}
			}

			if (tp->snd_cwnd < 2)
				tp->snd_cwnd = 2;
			else if (tp->snd_cwnd > tp->snd_cwnd_clamp)
				tp->snd_cwnd = tp->snd_cwnd_clamp;

			tp->snd_ssthresh = tcp_current_ssthresh(sk);
		}

		/* Wipe the slate clean for the next RTT. */
		vegas->cntRTT = 0;
		vegas->marked = 0;
		vegas->minRTT = 0x7fffffff;
		vegas->maxRTT = 0;
	}
	/* Use normal slow start */
	else if (tcp_in_slow_start(tp))
		tcp_slow_start(tp, acked);
}

/* Extract info for Tcp socket info provided via netlink. */
size_t tcp_vegas_get_info(struct sock *sk, u32 ext, int *attr,
			  union tcp_cc_info *info)
{
	const struct vegas *ca = inet_csk_ca(sk);

	if (ext & (1 << (INET_DIAG_VEGASINFO - 1))) {
		info->vegas.tcpv_enabled = ca->doing_vegas_now,
		info->vegas.tcpv_rttcnt = ca->cntRTT,
		info->vegas.tcpv_rtt = ca->baseRTT,
		info->vegas.tcpv_minrtt = ca->minRTT,

		*attr = INET_DIAG_VEGASINFO;
		return sizeof(struct tcpvegas_info);
	}
	return 0;
}
EXPORT_SYMBOL_GPL(tcp_vegas_get_info);

static struct tcp_congestion_ops tcp_vegas __read_mostly = {
	.init		= tcp_vegas_init,
	.ssthresh	= tcp_reno_ssthresh,
	.undo_cwnd	= tcp_reno_undo_cwnd,
	.cong_avoid	= tcp_vegas_cong_avoid,
	.pkts_acked	= tcp_vegas_pkts_acked,
	.set_state	= tcp_vegas_state,
	.cwnd_event	= tcp_vegas_cwnd_event,
	.get_info	= tcp_vegas_get_info,

	.owner		= THIS_MODULE,
	.name		= "vegas",
};

static int __init tcp_vegas_register(void)
{
	BUILD_BUG_ON(sizeof(struct vegas) > ICSK_CA_PRIV_SIZE);
	tcp_register_congestion_control(&tcp_vegas);
	return 0;
}

static void __exit tcp_vegas_unregister(void)
{
	tcp_unregister_congestion_control(&tcp_vegas);
}

module_init(tcp_vegas_register);
module_exit(tcp_vegas_unregister);

MODULE_AUTHOR("Stephen Hemminger");
MODULE_LICENSE("GPL");
MODULE_DESCRIPTION("TCP Vegas");
