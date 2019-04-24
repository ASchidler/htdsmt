#!/usr/bin/env false
from htd_validate.decompositions import HypertreeDecomposition
from validator import Validator

class HypertreeDecompositionValidator(Validator):
    _baseclass = HypertreeDecomposition
