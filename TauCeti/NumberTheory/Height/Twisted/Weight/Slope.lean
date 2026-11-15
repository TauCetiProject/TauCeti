/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Twisted.Weight.Exceptional

/-!
# Weight slopes between subspaces for weighted systems of linear forms

For a module `V` over a field `K` equipped with finite families of linear forms `L v` and real
weights `c v`, the *weight slope* between two subspaces `U` and `W` is the difference quotient
`weightSlope L c U W = (weight L c W - weight L c U) / (finrank K W - finrank K U)`
(the quantity `μ(W, U)` in Evertse--Ferretti, §15, (15.5), defaulting to `0` when `U` and `W` have
the same `finrank`).

When one argument is the ambient space `⊤`, `weightSlope` is minus `weightRatio`; when forms are
restricted to a subspace `W`, the restricted `weightRatio` of a subspace `A ≤ W` equals minus the
ambient `weightSlope` between `A.map W.subtype` and `W`. These identities connect the single-step
`exceptionalSubspace` construction to the consecutive segment slopes and supporting-line bounds of
the Harder--Narasimhan filtration `twistedFiltration`.

## Main definitions

* `TauCeti.weightSlope`: the weight difference per dimension difference between two subspaces.

## Main results

* `TauCeti.weightSlope_comm`, `TauCeti.weightSlope_self`, `TauCeti.weightSlope_zero`: basic
  symmetry and vanishing properties.
* `TauCeti.weightSlope_top_right`, `TauCeti.weightSlope_top_left`,
  `TauCeti.weightSlope_bot_left`, `TauCeti.weightSlope_bot_right`: specialization to `⊤` and `⊥`.
* `TauCeti.weightSlope_comp_of_injective`, `TauCeti.weightSlope_comp_subtype`, and
  `TauCeti.weightRatio_comp_subtype`: invariance under injective pullback and subspace restriction.
* `TauCeti.weightSlope_mul_finrank_sub_finrank` and
  `TauCeti.weight_sub_weightSlope_mul_finrank_eq`: affine supporting-line identities for `U ≤ W`.
* `TauCeti.weightSlope_le_iff`, `TauCeti.le_weightSlope_iff`, `TauCeti.lt_weightSlope_iff`:
  equivalence between slope bounds and linear weight bounds when `U < W` is finite-dimensional.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the Quantitative Subspace Theorem*,
  §15, (15.5).
-/

public noncomputable section

open Function Module Submodule Set

namespace TauCeti

variable {K V ι Ω : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]

/-- The weight difference per dimension difference between two subspaces `U` and `W`
(Evertse--Ferretti, §15, (15.5)). By real division by zero, its value is `0` when `U` and `W` have
the same `finrank`. -/
def weightSlope (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (U W : Submodule K V) : ℝ :=
  (weight L c W - weight L c U) / ((finrank K W : ℝ) - finrank K U)

/-- The defining quotient for the weight slope between two subspaces. -/
theorem weightSlope_def (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (U W : Submodule K V) :
    weightSlope L c U W =
      (weight L c W - weight L c U) / ((finrank K W : ℝ) - finrank K U) :=
  (rfl)

/-- Weight slope is symmetric in its two subspace arguments. -/
theorem weightSlope_comm (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (U W : Submodule K V) :
    weightSlope L c U W = weightSlope L c W U := by
  rw [weightSlope_def, weightSlope_def, ← neg_sub (weight L c W),
    ← neg_sub (finrank K W : ℝ), neg_div_neg_eq]

/-- Equal `finrank` gives zero weight slope by the division-by-zero convention. -/
theorem weightSlope_of_finrank_eq (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    {U W : Submodule K V} (h : finrank K U = finrank K W) :
    weightSlope L c U W = 0 := by
  simp [weightSlope_def, h]

/-- Every subspace has zero weight slope with itself. -/
@[simp]
theorem weightSlope_self (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (U : Submodule K V) : weightSlope L c U U = 0 :=
  weightSlope_of_finrank_eq L c rfl

/-- Zero form weights give zero weight slope on every pair of subspaces. -/
@[simp]
theorem weightSlope_zero (L : Ω → ι → Module.Dual K V) (U W : Submodule K V) :
    weightSlope L 0 U W = 0 := by
  simp [weightSlope_def]

/-- Relative to the whole space on the right, the weight slope is minus `weightRatio`. -/
@[simp]
theorem weightSlope_top_right (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (U : Submodule K V) :
    weightSlope L c U ⊤ = -weightRatio L c U := by
  rw [weightSlope_def, weightRatio_def, finrank_top, ← neg_div, neg_sub]

/-- Relative to the whole space on the left, the weight slope is minus `weightRatio`. -/
@[simp]
theorem weightSlope_top_left (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (U : Submodule K V) :
    weightSlope L c ⊤ U = -weightRatio L c U := by
  rw [weightSlope_comm, weightSlope_top_right]

/-- Relative to the zero subspace on the left, the weight slope is weight divided by `finrank`. -/
@[simp]
theorem weightSlope_bot_left (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (W : Submodule K V) :
    weightSlope L c ⊥ W = weight L c W / finrank K W := by
  simp [weightSlope_def]

/-- Relative to the zero subspace on the right, the weight slope is weight divided by `finrank`. -/
@[simp]
theorem weightSlope_bot_right (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (U : Submodule K V) :
    weightSlope L c U ⊥ = weight L c U / finrank K U := by
  rw [weightSlope_comm, weightSlope_bot_left]

/-- Pulling forms back along an injective linear map preserves the weight slope via the image
subspaces. -/
theorem weightSlope_comp_of_injective (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    {M : Type*} [AddCommGroup M] [Module K M] {f : M →ₗ[K] V}
    (hf : Function.Injective f) (A B : Submodule K M) :
    weightSlope (fun v i ↦ (L v i).comp f) c A B =
      weightSlope L c (A.map f) (B.map f) := by
  rw [weightSlope_def, weightSlope_def, weight_comp_of_injective L c hf A,
    weight_comp_of_injective L c hf B,
    (Submodule.equivMapOfInjective f hf A).finrank_eq,
    (Submodule.equivMapOfInjective f hf B).finrank_eq]

/-- Restricting forms to a subspace `W` identifies the weight slope with that of the ambient image
subspaces. -/
@[simp]
theorem weightSlope_comp_subtype (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (W : Submodule K V) (A B : Submodule K W) :
    weightSlope (fun v i ↦ (L v i).comp W.subtype) c A B =
      weightSlope L c (A.map W.subtype) (B.map W.subtype) :=
  weightSlope_comp_of_injective L c W.injective_subtype A B

/-- For forms restricted to `W`, the weight ratio of `A ≤ W` is minus the ambient weight slope
between `A.map W.subtype` and `W`. -/
theorem weightRatio_comp_subtype (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    (W : Submodule K V) (A : Submodule K W) :
    weightRatio (fun v i ↦ (L v i).comp W.subtype) c A =
      -weightSlope L c (A.map W.subtype) W := by
  have htop : (⊤ : Submodule K W).map W.subtype = W := Submodule.map_subtype_top W
  rw [← neg_inj, neg_neg, ← weightSlope_top_right, weightSlope_comp_subtype, htop]

/-- Multiplying the weight slope by the dimension difference recovers the weight difference
whenever `U ≤ W` (including when `U = W` or `W` is infinite-dimensional). -/
theorem weightSlope_mul_finrank_sub_finrank (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    {U W : Submodule K V} (hUW : U ≤ W) :
    weightSlope L c U W * ((finrank K W : ℝ) - finrank K U) =
      weight L c W - weight L c U := by
  by_cases hfin : finrank K U = finrank K W
  · rw [weightSlope_of_finrank_eq L c hfin, zero_mul]
    by_cases hW : Module.Finite K W
    · obtain rfl := Submodule.eq_of_le_of_finrank_eq hUW hfin
      simp
    · rcases eq_or_ne U ⊥ with rfl | hne
      · rw [weight_eq_zero_of_not_finite L c hW, weight_bot, sub_zero]
      · have hU : ¬Module.Finite K U := fun _ ↦ by
          have : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hne
          exact hW (Module.finite_of_finrank_pos (hfin ▸ Module.finrank_pos))
        rw [weight_eq_zero_of_not_finite L c hW, weight_eq_zero_of_not_finite L c hU, sub_zero]
  · rw [weightSlope_def, div_mul_cancel₀]
    exact sub_ne_zero.mpr (by exact_mod_cast Ne.symm hfin)

/-- For `U ≤ W`, both endpoints give the same value under the affine functional
`A ↦ weight L c A - weightSlope L c U W * finrank K A`. -/
theorem weight_sub_weightSlope_mul_finrank_eq (L : Ω → ι → Module.Dual K V) (c : Ω → ι → ℝ)
    {U W : Submodule K V} (hUW : U ≤ W) :
    weight L c U - weightSlope L c U W * finrank K U =
      weight L c W - weightSlope L c U W * finrank K W := by
  linarith [weightSlope_mul_finrank_sub_finrank L c hUW]

/-- An upper bound on `weightSlope L c U W` for `U < W` inside a finite-dimensional `W` is a
linear bound on the weight difference. -/
theorem weightSlope_le_iff {L : Ω → ι → Module.Dual K V} {c : Ω → ι → ℝ}
    {U W : Submodule K V} [FiniteDimensional K W] (hUW : U < W) {a : ℝ} :
    weightSlope L c U W ≤ a ↔
      weight L c W - weight L c U ≤ a * ((finrank K W : ℝ) - finrank K U) := by
  rw [weightSlope_def]
  exact div_le_iff₀ (sub_pos.mpr (by exact_mod_cast Submodule.finrank_lt_finrank_of_lt hUW))

/-- A lower bound on `weightSlope L c U W` for `U < W` inside a finite-dimensional `W` is a
linear bound on the weight difference. -/
theorem le_weightSlope_iff {L : Ω → ι → Module.Dual K V} {c : Ω → ι → ℝ}
    {U W : Submodule K V} [FiniteDimensional K W] (hUW : U < W) {a : ℝ} :
    a ≤ weightSlope L c U W ↔
      a * ((finrank K W : ℝ) - finrank K U) ≤ weight L c W - weight L c U := by
  rw [weightSlope_def]
  exact le_div_iff₀ (sub_pos.mpr (by exact_mod_cast Submodule.finrank_lt_finrank_of_lt hUW))

/-- A strict lower bound on `weightSlope L c U W` for `U < W` inside a finite-dimensional `W` is a
strict linear bound on the weight difference. -/
theorem lt_weightSlope_iff {L : Ω → ι → Module.Dual K V} {c : Ω → ι → ℝ}
    {U W : Submodule K V} [FiniteDimensional K W] (hUW : U < W) {a : ℝ} :
    a < weightSlope L c U W ↔
      a * ((finrank K W : ℝ) - finrank K U) < weight L c W - weight L c U := by
  rw [weightSlope_def]
  exact lt_div_iff₀ (sub_pos.mpr (by exact_mod_cast Submodule.finrank_lt_finrank_of_lt hUW))

end TauCeti
