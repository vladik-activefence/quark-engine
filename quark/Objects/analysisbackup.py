# -*- coding: utf-8 -*-
# This file is part of Quark-Engine - https://github.com/quark-engine/quark-engine
# See the file 'LICENSE' for copying permission.
class QuarkAnalysisBackup:
    __slots__ = ["first_api", "second_api", "level_1_result", "level_2_result", "level_3_result",
                 "level_4_result", "level_5_result"]

    def __init__(self):
        self.first_api = None
        self.second_api = None
        self.level_1_result = []
        self.level_2_result = []
        self.level_3_result = []
        self.level_4_result = []
        self.level_5_result = []

    def print(self):
        print(self.first_api)
        print(self.second_api)
        print(self.level_1_result)
        print(self.level_2_result)
        print(self.level_3_result)
        print(self.level_4_result)
        print(self.level_5_result)

if __name__ == "__main__":
    pass
