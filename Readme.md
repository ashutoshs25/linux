Delay-based congestion control implementation is in net/ipv4/tcp_vegas.c

Switch to the approporiate branch based on the coexistence algorithm you are looking for:

- ``testing`` branch : Threshold adaptation, threshold adaptation with delay gradient
- ``periodic_backoff`` branch : Threshold adaptation with periodic backoff solution 
- ``fair_coexistence`` branch : Cx-TCP algorithm, Cx-TCP with RTT variance scaling
- ``shadow_cwnd`` branch : Cx-TCP with shadow CWND




Linux kernel
============

There are several guides for kernel developers and users. These guides can
be rendered in a number of formats, like HTML and PDF. Please read
Documentation/admin-guide/README.rst first.

In order to build the documentation, use ``make htmldocs`` or
``make pdfdocs``.  The formatted documentation can also be read online at:

    https://www.kernel.org/doc/html/latest/

There are various text files in the Documentation/ subdirectory,
several of them using the Restructured Text markup notation.

Please read the Documentation/process/changes.rst file, as it contains the
requirements for building and running the kernel, and information about
the problems which may result by upgrading your kernel.
