#!/usr/bin/env false
from htd_validate.decompositions import GeneralizedHypertreeDecomposition
from validator import Validator


class GeneralizedHypertreeDecompositionValidator(Validator):
    _baseclass = GeneralizedHypertreeDecomposition
