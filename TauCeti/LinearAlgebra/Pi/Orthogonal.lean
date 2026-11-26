/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Orthogonals in `E^ι` of submodules of `O^ι`

For a commutative ring `O`, an `O`-module `E` and a finite type `ι`, the pairing
`⟨v, u⟩ = ∑ i, v i • u i` between `O^ι` and `E^ι` takes values in `E`. The orthogonal of a
submodule `R ⊆ O^ι` is the submodule of `u ∈ E^ι` pairing to zero with every vector of `R`. It is
identified with `Hom_O(O^ι ⧸ R, E)`, a vector `u` corresponding to the functional
`v ↦ ⟨v, u⟩`.

## Main definitions

* `Submodule.orthogonalPi`: the orthogonal `R^⊥ ⊆ E^ι` of a submodule `R ⊆ O^ι`.
* `Submodule.orthogonalPiEquiv`: the linear equivalence `R^⊥ ≃ Hom_O(O^ι ⧸ R, E)`.
-/

public section

namespace Submodule

variable {O E ι : Type*} [CommRing O] [AddCommGroup E] [Module O E] [Fintype ι]

/-- The orthogonal of a submodule `R ⊆ O^ι` in `E^ι` under the pairing `⟨v, u⟩ = ∑ i, v i • u i`:
the vectors `u` with `⟨v, u⟩ = 0` for every `v ∈ R`. It is `Hom_O(O^ι ⧸ R, E)`
(`Submodule.orthogonalPiEquiv`). -/
def orthogonalPi (E : Type*) [AddCommGroup E] [Module O E] (R : Submodule O (ι → O)) :
    Submodule O (ι → E) where
  carrier := {u | ∀ v ∈ R, ∑ i, v i • u i = 0}
  add_mem' {u w} hu hw v hv := by
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib, hu v hv, hw v hv, add_zero]
  zero_mem' v _ := by simp
  smul_mem' c u hu v hv := by
    simp only [Pi.smul_apply, smul_comm (v _) c, ← Finset.smul_sum, hu v hv, smul_zero]

@[simp]
theorem mem_orthogonalPi {R : Submodule O (ι → O)} {u : ι → E} :
    u ∈ R.orthogonalPi E ↔ ∀ v ∈ R, ∑ i, v i • u i = 0 :=
  Iff.rfl

/-- The orthogonal of a span is cut out by the spanning vectors. -/
theorem mem_orthogonalPi_span {S : Set (ι → O)} {u : ι → E} :
    u ∈ (span O S).orthogonalPi E ↔ ∀ v ∈ S, ∑ i, v i • u i = 0 := by
  refine ⟨fun h v hv ↦ h v (subset_span hv), fun h v hv ↦ ?_⟩
  induction hv using span_induction with
  | mem v hv => exact h v hv
  | zero => simp
  | add v w _ _ hv hw => simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hv, hw,
      add_zero]
  | smul c v _ hv => simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, hv,
      smul_zero]

/-- Taking orthogonals reverses inclusions. -/
theorem orthogonalPi_anti {R R' : Submodule O (ι → O)} (h : R ≤ R') :
    R'.orthogonalPi E ≤ R.orthogonalPi E :=
  fun _ hu v hv ↦ hu v (h hv)

variable [DecidableEq ι]

/-- The orthogonal of `R ⊆ O^ι` in `E^ι` is `Hom_O(O^ι / R, E)`: a vector `u` corresponds to the
functional `v ↦ ∑ i, v i • u i`, which vanishes on `R`. -/
noncomputable def orthogonalPiEquiv (E : Type*) [AddCommGroup E] [Module O E]
    (R : Submodule O (ι → O)) : R.orthogonalPi E ≃ₗ[O] ((ι → O) ⧸ R →ₗ[O] E) where
  toFun u := R.liftQ (Fintype.linearCombination O u.val) fun v hv ↦ by
    simpa [Fintype.linearCombination_apply] using u.property v hv
  map_add' u w := by ext; simp [Fintype.linearCombination_apply, smul_add, Finset.sum_add_distrib]
  map_smul' c u := by
    ext; simp [Fintype.linearCombination_apply, Pi.single_apply]
  invFun f := ⟨fun i ↦ f (R.mkQ (Pi.single i 1)), fun v hv ↦ by
    have hv' : v = ∑ i, v i • Pi.single i (1 : O) := by ext j; simp [Pi.single_apply]
    calc ∑ i, v i • f (R.mkQ (Pi.single i 1)) = f (R.mkQ v) := by
          conv_rhs => rw [hv']
          simp only [map_sum, map_smul]
      _ = 0 := by rw [mkQ_apply, (Quotient.mk_eq_zero R).2 hv, map_zero]⟩
  left_inv u := by ext i; simp [Fintype.linearCombination_apply, Pi.single_apply]
  right_inv f := by
    ext v
    simp [Fintype.linearCombination_apply, Pi.single_apply]

@[simp]
theorem orthogonalPiEquiv_apply_mk (R : Submodule O (ι → O)) (u : R.orthogonalPi E)
    (v : ι → O) :
    orthogonalPiEquiv E R u (Quotient.mk v) = ∑ i, v i • (u : ι → E) i := by
  simp [orthogonalPiEquiv, Fintype.linearCombination_apply]

@[simp]
theorem coe_orthogonalPiEquiv_symm_apply (R : Submodule O (ι → O))
    (f : (ι → O) ⧸ R →ₗ[O] E) (i : ι) :
    ((orthogonalPiEquiv E R).symm f : ι → E) i = f (R.mkQ (Pi.single i 1)) := by
  simp [orthogonalPiEquiv]

end Submodule
