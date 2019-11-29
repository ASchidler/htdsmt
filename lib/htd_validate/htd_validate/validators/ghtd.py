#!/usr/bin/env false
from ..decompositions import GeneralizedHypertreeDecomposition
from .validator import Validator


class GeneralizedHypertreeDecompositionValidator(Validator):
    _baseclass = GeneralizedHypertreeDecomposition
