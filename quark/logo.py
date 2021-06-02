# -*- coding: utf-8 -*-
# This file is part of Quark-Engine - https://github.com/quark-engine/quark-engine
# See the file 'LICENSE' for copying permission.

from quark import __version__

from quark.utils.colors import bold, lightyellow, lightblue


def logo():
    """
    Output our amazing logo

    :return: None
    """
    print(
        bold(
            lightyellow(
                """
           ________                __                 
           \_____  \  __ _______  |  | __ ___________ 
            /  / \  \|  |  \__  \ |  |/ // __ \_  __  \\
           /   \_/.  \  |  // __ \|    <\  ___/|  | \/
           \_____\ \_/____/(____  /__|_ \\___  >__|   
                  \__>          \/     \/    \/       
            v{}
    """
            ),
        ).format(__version__)
        + bold(
            lightblue(
                """
                An Obfuscation-Neglect Android Malware Scoring System
                """
            ),
        ),
    )
