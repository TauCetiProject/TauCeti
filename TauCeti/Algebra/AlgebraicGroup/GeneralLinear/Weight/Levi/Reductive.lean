/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Levi.UnipotentRadical
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic

/-!
# Weight Levi subgroups are reductive

The Levi subgroup of `GL_N` preserving the weight spaces of an integer weight is reductive over
every field. Its coordinate algebra is smooth and geometrically connected, and over an algebraic
closure its normal smooth unipotent closed subgroups are trivial. The latter statement follows
from the faithful, completely reducible standard comodule, including when weights repeat.

The result is stated for the finite-type coordinate Hopf algebra and allows rank zero and
arbitrary characteristic.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 13 and 19.
* T. A. Springer, *Linear Algebraic Groups*, §§2.2 and 2.4.
* Formal source: `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Reductive.Basic`.
-/

public section

open CategoryTheory

namespace TauCeti.GeneralLinear

universe u

noncomputable section

/-- The block-diagonal Levi subgroup of `GL_N` attached to any integer weight is reductive over
every field, including in rank zero and when weight blocks repeat. -/
theorem reductiveCommHopfAlgProperty_weightLeviFiniteTypeCoordinateHopfAlgebra
    (k : Type u) [Field k] {N : ℕ} (w : Fin N → ℤ) :
    reductiveCommHopfAlgProperty k (weightLeviFiniteTypeCoordinateHopfAlgebra k w) :=
  reductiveCommHopfAlgProperty_of_geometricFiber_iso k _
    (weightLeviFiniteTypeCoordinateHopfAlgebra (AlgebraicClosure k) w) inferInstance
    (geometricallyConnectedCommHopfAlgProperty_weightLeviCoordinateHopfAlgebra k w)
    (ObjectProperty.isoMk _
      (weightLeviCoordinateHopfAlgebraBaseChangeIso k (AlgebraicClosure k) w))
    (eq_augmentation_weightLevi_of_isNormal_of_smoothUnipotent (AlgebraicClosure k) w)

end

end TauCeti.GeneralLinear
