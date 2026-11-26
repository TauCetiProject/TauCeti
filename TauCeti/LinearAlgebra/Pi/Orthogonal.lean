/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal

/-!
# Orthogonals in `E^ι` of submodules of `O^ι`

For a commutative ring `O`, an `O`-module `E` and a finite type `ι`, the pairing
`⟨v, u⟩ = ∑ i, v i • u i` between `O^ι` and `E^ι` takes values in `E`: it is
`(Fintype.bilinearCombination O O).flip`. The orthogonal of a submodule `R ⊆ O^ι` for this pairing,
Mathlib's `Submodule.orthogonalBilin`, is identified with `Hom_O(O^ι ⧸ R, E)`, a vector `u`
corresponding to the functional `v ↦ ⟨v, u⟩`.

## Main definitions

* `Submodule.orthogonalPiEquiv`: the linear equivalence `R^⊥ ≃ Hom_O(O^ι ⧸ R, E)`.
-/

public section

namespace Submodule

variable {O E ι : Type*} [CommRing O] [AddCommGroup E] [Module O E] [Fintype ι]

variable [DecidableEq ι]

/-- The orthogonal of `R ⊆ O^ι` in `E^ι` for the pairing `⟨v, u⟩ = ∑ i, v i • u i` is
`Hom_O(O^ι / R, E)`: a vector `u` corresponds to the functional `v ↦ ⟨v, u⟩`, which vanishes on
`R`. -/
noncomputable def orthogonalPiEquiv (E : Type*) [AddCommGroup E] [Module O E]
    (R : Submodule O (ι → O)) :
    R.orthogonalBilin (Fintype.bilinearCombination O O (M := E)).flip ≃ₗ[O]
      ((ι → O) ⧸ R →ₗ[O] E) where
  toFun u := R.liftQ (Fintype.linearCombination O u.val) fun v hv ↦ by
    simpa [Fintype.linearCombination_apply] using u.property v hv
  map_add' u w := by ext; simp [Fintype.linearCombination_apply, smul_add, Finset.sum_add_distrib]
  map_smul' c u := by
    ext; simp [Fintype.linearCombination_apply, Pi.single_apply]
  invFun f := ⟨fun i ↦ f (R.mkQ (Pi.single i 1)), fun v hv ↦ by
    have hv' : v = ∑ i, v i • Pi.single i (1 : O) := by ext j; simp [Pi.single_apply]
    rw [LinearMap.flip_apply, Fintype.bilinearCombination_apply, Fintype.linearCombination_apply]
    calc ∑ i, v i • f (R.mkQ (Pi.single i 1)) = f (R.mkQ v) := by
          conv_rhs => rw [hv']
          simp only [map_sum, map_smul]
      _ = 0 := by rw [mkQ_apply, (Quotient.mk_eq_zero R).2 hv, map_zero]⟩
  left_inv u := by ext i; simp [Fintype.linearCombination_apply, Pi.single_apply]
  right_inv f := by
    ext v
    simp [Fintype.linearCombination_apply, Pi.single_apply]

@[simp]
theorem orthogonalPiEquiv_apply_mk (R : Submodule O (ι → O))
    (u : R.orthogonalBilin (Fintype.bilinearCombination O O (M := E)).flip) (v : ι → O) :
    orthogonalPiEquiv E R u (Quotient.mk v) = ∑ i, v i • (u : ι → E) i := by
  simp [orthogonalPiEquiv, Fintype.linearCombination_apply]

@[simp]
theorem coe_orthogonalPiEquiv_symm_apply (R : Submodule O (ι → O))
    (f : (ι → O) ⧸ R →ₗ[O] E) (i : ι) :
    ((orthogonalPiEquiv E R).symm f : ι → E) i = f (R.mkQ (Pi.single i 1)) := by
  simp [orthogonalPiEquiv]

end Submodule
