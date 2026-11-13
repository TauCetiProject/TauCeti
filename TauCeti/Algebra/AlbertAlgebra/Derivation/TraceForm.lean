/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import TauCeti.Algebra.AlbertAlgebra.Derivation.Basic
public import TauCeti.Algebra.Jordan.TraceForm

/-!
# Derivations of the split Albert algebra preserve the operator trace form

Every derivation of the split Albert algebra is skew for the bilinear form
`(a, b) ↦ tr(L_{a * b})`. This is the general derivation invariance theorem specialized
to the split carrier; it requires neither a positive definite form nor formal reality.
-/

public section

namespace TauCeti.AlbertAlgebra

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- A split Albert derivation is skew for the unnormalized operator trace form. -/
theorem traceForm_derivation (D : derivationLieAlgebra R (AlbertAlgebra R))
    (a b : AlbertAlgebra R) :
    Jordan.traceForm R ((D : Module.End R (AlbertAlgebra R)) a) b +
      Jordan.traceForm R a ((D : Module.End R (AlbertAlgebra R)) b) = 0 :=
  Jordan.traceForm_derivation R D a b

end TauCeti.AlbertAlgebra
