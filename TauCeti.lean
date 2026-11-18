-- This is the AI-owned root of the TauCeti mathematics library.
--
-- The lakefile's `globs = ["TauCeti.*"]` determines the library's build scope, and
-- the axiom audit enumerates the source tree. The imports below record the modules
-- introduced for the Jordan star map API.

module

import TauCeti.Algebra.Algebra.Complex
import TauCeti.Algebra.Star.Jordan.Basic
import TauCeti.Algebra.Star.Jordan.Matrix
import TauCeti.Algebra.Star.SelfAdjoint.LinearMap
import TauCeti.Algebra.Star.Symmetrized
