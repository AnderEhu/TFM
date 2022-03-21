#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## asyncproc.py
##
##  Created on: Apr 02, 2015
##      Author: Alexey S. Ignatiev
##      E-mail: aign@sat.inesc-id.pt
##

#
#==============================================================================
import atexit
import os
import platform
from subprocess import PIPE, Popen
import sys
from threading import Thread

try:
    from Queue import Queue, Empty
except ImportError:
    from queue import Queue, Empty  # python 3.x

ON_POSIX = 'posix' in sys.builtin_module_names


#
#==============================================================================
class AsyncProc():
    """
        Basic asynchronous process class.
    """

    def __init__(self, line_buffered=True):
        """
            Primer constructor.
        """

        self.proc = None
        self.queue = None
        self.thread = None
        self.args = []

        # setting up line-buffered stdout (requires the coreutils package)
        if line_buffered:
            self.args = ['stdbuf', '-oL']
            if platform.system() == 'Darwin':
                self.args[0] = 'gstdbuf'

        atexit.register(self._at_exit)

    def call(self, args):
        """
            Calls subprocess.
        """

        self.args.extend(args)

        self.proc = Popen(self.args, stdout=PIPE, bufsize=1, close_fds=ON_POSIX)
        self.queue = Queue()
        self.thread = Thread(target=self._enqueue_output)

        self.thread.daemon = True # thread dies with the program
        self.thread.start()

    def get_line(self, timeout_=.01):
        """
            Read one line of the output without blocking.
        """

        while True:
            # try:  line = self.queue.get_nowait()
            try:  line = self.queue.get(timeout=timeout_)
            except Empty:
                if self.proc.poll() != None:
                    self.proc = None
                    return
            else: # got line
                yield line.decode('ascii')

    def _enqueue_output(self):
        """
            Enqueues output of a process.
        """

        for line in iter(self.proc.stdout.readline, b''):
            self.queue.put(line)

        self.proc.stdout.close()

    def _at_exit(self):
        """
            Kills the process at exit (if any).
        """

        if self.proc:
            self.proc.kill()
