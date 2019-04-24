#!/usr/bin/env false
from htd_validate.decompositions import FractionalHypertreeDecomposition
from validator import Validator


class FractionalHypertreeDecompositionValidator(Validator):
    _baseclass = FractionalHypertreeDecomposition
