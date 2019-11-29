#!/usr/bin/env false
from ..decompositions import TreeDecomposition
from .validator import Validator


class TreeDecompositionValidator(Validator):
    _baseclass = TreeDecomposition
