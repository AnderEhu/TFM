#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## link-bin.py
##
##  Created on: Apr 2, 2015
##      Author: Alexey S. Ignatiev
##      E-mail: aign@sat.inesc-id.pt
##

#
#==============================================================================
import os
import platform

tools = ('primer-a', 'primer-b', 'primer-pe2', 'forqes', 'forqes-g3', 'mscg', 'hhlmuc', 'muser2')

#
#==============================================================================
if __name__ == '__main__':
    # cleaning previous configuration
    for tool in tools:
        if os.path.isfile(tool):
            os.remove(tool)

    # checking platform
    if platform.system() == 'Linux':
        suffix = 'linux-x86_64'
    elif platform.system() == 'Darwin':
        suffix = 'macosx-x86_64'

    # linking
    for tool in tools:
        os.symlink('bin/{0}-{1}'.format(tool, suffix), tool)
