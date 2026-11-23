/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Bialgebra.Primitive

/-!
# The reduced coproduct of a bialgebra

For a bialgebra `B` over a commutative ring `k`, the reduced coproduct defect of `x : B` is
`Δ x - x ⊗ 1 - 1 ⊗ x + ε(x) (1 ⊗ 1)`. It is the reduced coproduct of the augmentation-ideal
component `x - ε(x) 1`, so it vanishes on scalars and on primitive elements, and bialgebra maps
commute with it.

## Main declarations

* `TauCeti.Bialgebra.reducedComul`: the reduced coproduct defect, as a linear map.
* `TauCeti.Bialgebra.reducedComul_apply`: its value as an explicit formula.
* `TauCeti.Bialgebra.reducedComul_algebraMap`, `Bialgebra.IsPrimitiveElem.reducedComul_eq_zero`:
  it vanishes on scalars and on primitive elements.
* `BialgHom.map_reducedComul`: bialgebra maps commute with it.
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

/-- The reduced coproduct defect vanishes on scalars. -/
@[simp]
theorem reducedComul_algebraMap {B : Type*} [Ring B] [Bialgebra k B] (c : k) :
    reducedComul k B (algebraMap k B c) = 0 := by
  rw [reducedComul_apply, Bialgebra.comul_algebraMap, Bialgebra.counit_algebraMap,
    ← Algebra.TensorProduct.algebraMap_apply, ← Algebra.TensorProduct.algebraMap_apply']
  abel

end TauCeti.Bialgebra

namespace BialgHom

open TauCeti.Bialgebra

variable {k B C : Type*} [CommRing k] [Ring B] [Bialgebra k B] [Ring C] [Bialgebra k C]

/-- Bialgebra maps commute with the reduced coproduct defect. -/
theorem map_reducedComul (φ : B →ₐc[k] C) (x : B) :
    TensorProduct.map (φ : B →ₗ[k] C) (φ : B →ₗ[k] C) (reducedComul k B x) =
      reducedComul k C (φ x) := by
  simp [reducedComul_apply, CoalgHomClass.map_comp_comul_apply, Algebra.algebraMap_eq_smul_one,
    Algebra.TensorProduct.one_def]

end BialgHom

namespace Bialgebra.IsPrimitiveElem

variable {k B : Type*} [CommRing k] [Ring B] [Bialgebra k B]

/-- The reduced coproduct defect vanishes on primitive elements. -/
@[simp]
theorem reducedComul_eq_zero {x : B} (hx : IsPrimitiveElem k x) :
    TauCeti.Bialgebra.reducedComul k B x = 0 := by
  simp [TauCeti.Bialgebra.reducedComul_apply, hx.counit_eq_zero, hx.comul_eq_tmul_add_tmul,
    add_comm]

end Bialgebra.IsPrimitiveElem
