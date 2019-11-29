#!/usr/bin/env false
from ..decompositions import HypertreeDecomposition
from .validator import Validator


class HypertreeDecompositionValidator(Validator):
    _baseclass = HypertreeDecomposition
