/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom

/-!
# The reduced coproduct of a bialgebra

For a bialgebra `B` over a commutative ring `k`, the reduced coproduct defect of `x : B` is
`Δ x - x ⊗ 1 - 1 ⊗ x + ε(x) (1 ⊗ 1)`. It is the reduced coproduct of the augmentation-ideal
component `x - ε(x) 1`, so it vanishes on scalars and on primitive elements, and bialgebra maps
commute with it.

## Main declarations

* `TauCeti.Bialgebra.reducedComul`: the reduced coproduct defect, as a linear map.
* `TauCeti.Bialgebra.reducedComul_apply`: its value as an explicit formula.
* `TauCeti.Bialgebra.map_reducedComul`: bialgebra maps commute with it.
-/

public section

open TensorProduct

namespace TauCeti.Bialgebra

variable {k : Type*} [CommRing k]

variable (k) in
/-- The reduced coproduct defect `Δ x - x ⊗ 1 - 1 ⊗ x + ε(x) (1 ⊗ 1)`, which vanishes on scalars
and on primitive elements. -/
noncomputable def reducedComul (B : Type*) [Ring B] [Bialgebra k B] :
    B →ₗ[k] B ⊗[k] B :=
  Coalgebra.comul - (TensorProduct.mk k B B).flip 1 - TensorProduct.mk k B B 1 +
    Coalgebra.counit.smulRight (1 ⊗ₜ[k] 1)

/-- The value of the reduced coproduct defect. -/
theorem reducedComul_apply {B : Type*} [Ring B] [Bialgebra k B] (x : B) :
    reducedComul k B x = Coalgebra.comul x - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x +
      algebraMap k (B ⊗[k] B) (Coalgebra.counit (R := k) x) := by
  simp [reducedComul, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def]

/-- Bialgebra maps commute with the reduced coproduct defect. -/
theorem map_reducedComul {B C : Type*} [Ring B] [Bialgebra k B] [Ring C] [Bialgebra k C]
    (φ : B →ₐc[k] C) (x : B) :
    TensorProduct.map (φ : B →ₗ[k] C) (φ : B →ₗ[k] C) (reducedComul k B x) =
      reducedComul k C (φ x) := by
  simp [reducedComul_apply, CoalgHomClass.map_comp_comul_apply, Algebra.algebraMap_eq_smul_one,
    Algebra.TensorProduct.one_def]

end TauCeti.Bialgebra
