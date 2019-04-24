#!/usr/bin/env false
from htd_validate.decompositions import TreeDecomposition
from validator import Validator


class TreeDecompositionValidator(Validator):
    _baseclass = TreeDecomposition
