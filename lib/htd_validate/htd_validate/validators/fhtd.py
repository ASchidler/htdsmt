#!/usr/bin/env false
from ..decompositions import FractionalHypertreeDecomposition
from .validator import Validator


class FractionalHypertreeDecompositionValidator(Validator):
    _baseclass = FractionalHypertreeDecomposition
