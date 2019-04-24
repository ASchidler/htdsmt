#!/usr/bin/env false
from abc import ABCMeta


class Validator(object):
    __metaclass__ = ABCMeta
    _baseclass = None

    def __init__(self):
        pass

    @classmethod
    def graph_type(cls):
        return cls._baseclass.graph_type()

    @classmethod
    def short_name(cls):
        return cls._baseclass._problem_string

    @classmethod
    def decomposition_type(cls):
        return cls._baseclass.__name__
