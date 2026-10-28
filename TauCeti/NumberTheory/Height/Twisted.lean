/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.NumberTheory.NumberField.Global.Places.Height

import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# Twisted heights

Let `K` be a number field and `n` a natural number. A *system of linear forms* attaches to every
place `v` of `K` a family `L v : Fin n → Fin n → K` of `n` linear forms on `K ^ n`, written as
coefficient vectors, so that the `i`-th form at `v` sends `x` to `L v i ⬝ᵥ x`. Given real weights
`c v i` and a real parameter `Q`, the *twisted height* of a nonzero `x : Fin n → K` is
`H_{L,c,Q}(x) = ∏_v max_i (|L v i ⬝ᵥ x|_v * Q ^ (-c v i))`, where `|·|_v` is the
degree-normalized absolute value `TauCeti.GlobalNumberFields.normAbs`. The twisted height of `0`
is `0`.

Twisted heights are the heights in which Evertse and Ferretti state and prove the quantitative
Subspace Theorem: for suitable data and all large `Q`, the points `x` with
`H_{L,c,Q}(x) ≤ Δ_L ^ (1 / n) * Q ^ (-δ)` lie in a proper linear subspace, one of finitely many
as `Q` varies. Here `Δ_L = ∏_v |det (L v)|_v` is the product over the places of the
degree-normalized absolute values of the determinants of the forms.

The local factors are `TauCeti.twistedLocalHeight`. The usual hypotheses on the data are that the
forms at each place are linearly independent, that only finitely many distinct systems of forms
occur, and that the weights `c v` vanish at all but finitely many places; under them the local
factors at a nonzero point are `1` at all but finitely many places
(`TauCeti.hasFiniteMulSupport_twistedLocalHeight`), so that the twisted height is a genuine finite
product. The definition does not assume these hypotheses: the product over the places is Mathlib's
`finprod`, which is `1` when infinitely many local factors differ from `1`.

## Main definitions

* `TauCeti.coordForms`: the coordinate forms `X_1, …, X_n` at every place.
* `TauCeti.twistedLocalHeight`: the local factor `max_i (|L v i ⬝ᵥ x|_v * Q ^ (-c v i))`.
* `TauCeti.twistedHeight`: the twisted height `H_{L,c,Q}`.

## Main results

* `TauCeti.twistedHeight_pos`: for `Q > 0` and forms linearly independent at every place,
  the twisted height of a nonzero point is positive.
* `TauCeti.twistedHeight_smul`: the twisted height is projective, by the product formula.
* `TauCeti.twistedHeight_coordForms_zero`: for coordinate forms and zero weights the twisted
  height is the absolute multiplicative height `Height.mulHeight x ^ (1 / [K : ℚ])`.
* `TauCeti.twistedHeight_shift_of_hasFiniteMulSupport`, `TauCeti.twistedHeight_shift`: shifting
  the weights at each place by `θ v` multiplies the twisted height by `Q ^ (∑ᶠ v, θ v)`.
* `TauCeti.twistedHeight_vecMul`: a common invertible change of variables of the forms is a change
  of variables of the point.
* `TauCeti.twistedHeight_one`: for `Q = 1` the twisted height does not depend on the weights.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace
  Theorem*, Ann. of Math. 177 (2013), §1.1, §2.2 and Lemmas 7.2, 7.3.
-/

public noncomputable section

open Function Module Matrix TauCeti.GlobalNumberFields

namespace TauCeti

variable {K : Type*} [Field K] {n : ℕ}

/-! ### Coordinate forms -/

variable (K n) in
/-- The coordinate forms `X_1, …, X_n` on `K ^ n`, at every place of `K`. -/
def coordForms : Place K → Fin n → Fin n → K :=
  fun _ i ↦ Pi.single i 1

@[simp]
theorem coordForms_apply (v : Place K) (i : Fin n) : coordForms K n v i = Pi.single i 1 := (rfl)

/-- The `i`-th coordinate form sends a point to its `i`-th coordinate. -/
theorem coordForms_dotProduct (v : Place K) (i : Fin n) (x : Fin n → K) :
    coordForms K n v i ⬝ᵥ x = x i := by
  simp

theorem linearIndependent_coordForms (v : Place K) : LinearIndependent K (coordForms K n v) :=
  Pi.linearIndependent_single_one (Fin n) K

variable [NumberField K]

/-! ### Local factors -/

/-- The local factor `max_i (|L v i ⬝ᵥ x|_v * Q ^ (-c v i))` of the twisted height at a place
`v`. -/
def twistedLocalHeight (L : Place K → Fin n → Fin n → K) (c : Place K → Fin n → ℝ) (Q : ℝ)
    (v : Place K) (x : Fin n → K) : ℝ :=
  ⨆ i, normAbs v (L v i ⬝ᵥ x) * Q ^ (-c v i)

variable {L : Place K → Fin n → Fin n → K} {c : Place K → Fin n → ℝ} {Q : ℝ}

theorem twistedLocalHeight_def (v : Place K) (x : Fin n → K) :
    twistedLocalHeight L c Q v x = ⨆ i, normAbs v (L v i ⬝ᵥ x) * Q ^ (-c v i) := (rfl)

theorem twistedLocalHeight_nonneg (hQ : 0 ≤ Q) (v : Place K) (x : Fin n → K) :
    0 ≤ twistedLocalHeight L c Q v x :=
  Real.iSup_nonneg fun _ ↦ mul_nonneg (normAbs_nonneg _ _) (Real.rpow_nonneg hQ _)

theorem twistedLocalHeight_pos (hQ : 0 < Q) {v : Place K} (hL : LinearIndependent K (L v))
    {x : Fin n → K} (hx : x ≠ 0) : 0 < twistedLocalHeight L c Q v x := by
  obtain ⟨i, hi⟩ := hL.exists_dotProduct_ne_zero hx
  exact (mul_pos (normAbs_pos v hi) (Real.rpow_pos_of_pos hQ _)).trans_le <|
    le_ciSup (f := fun i ↦ normAbs v (L v i ⬝ᵥ x) * Q ^ (-c v i)) (Set.finite_range _).bddAbove i

/-- The local factor of a multiple `a • x` is the local factor of `x` times `|a|_v`. -/
theorem twistedLocalHeight_smul (v : Place K) (a : K) (x : Fin n → K) :
    twistedLocalHeight L c Q v (a • x) = normAbs v a * twistedLocalHeight L c Q v x := by
  simp only [twistedLocalHeight_def, dotProduct_smul, smul_eq_mul, map_mul, mul_assoc]
  exact (Real.mul_iSup_of_nonneg (normAbs_nonneg v a) _).symm

/-- Shifting the weights at `v` by `θ v` multiplies the local factor by `Q ^ θ v`. -/
theorem twistedLocalHeight_shift (hQ : 0 < Q) (θ : Place K → ℝ) (v : Place K)
    (x : Fin n → K) :
    twistedLocalHeight L (fun w i ↦ c w i - θ w) Q v x =
      Q ^ θ v * twistedLocalHeight L c Q v x := by
  rw [twistedLocalHeight_def, twistedLocalHeight_def, Real.mul_iSup_of_nonneg
    (Real.rpow_nonneg hQ.le _)]
  congr 1 with i
  rw [neg_sub, sub_eq_add_neg, Real.rpow_add hQ]
  ring

@[simp]
theorem twistedLocalHeight_one (v : Place K) (x : Fin n → K) :
    twistedLocalHeight L c 1 v x = ⨆ i, normAbs v (L v i ⬝ᵥ x) := by
  simp [twistedLocalHeight_def]

@[simp]
theorem twistedLocalHeight_coordForms_zero (v : Place K) (x : Fin n → K) :
    twistedLocalHeight (coordForms K n) 0 Q v x = ⨆ i, normAbs v (x i) := by
  simp [twistedLocalHeight_def]

/-- Composing every form with the linear map `y ↦ A *ᵥ y` is evaluating at `A *ᵥ x`. -/
theorem twistedLocalHeight_vecMul (A : Matrix (Fin n) (Fin n) K) (v : Place K) (x : Fin n → K) :
    twistedLocalHeight (fun w i ↦ L w i ᵥ* A) c Q v x = twistedLocalHeight L c Q v (A *ᵥ x) := by
  simp [twistedLocalHeight_def, dotProduct_mulVec]

/-- If the forms at every place are linearly independent, only finitely many distinct systems of
forms occur and the weights `c v` vanish at all but finitely many places, then the local factors of
the twisted height of a nonzero point are `1` at all but finitely many places. -/
theorem hasFiniteMulSupport_twistedLocalHeight (hL : ∀ v, LinearIndependent K (L v))
    (hLfin : (Set.range L).Finite) (hc : HasFiniteSupport c) {x : Fin n → K} (hx : x ≠ 0) :
    HasFiniteMulSupport fun v ↦ twistedLocalHeight L c Q v x := by
  have hl (l : Fin n → Fin n → K) (hlL : l ∈ Set.range L) :
      HasFiniteMulSupport fun v : Place K ↦ ⨆ i, normAbs v (l i ⬝ᵥ x) := by
    obtain ⟨w, rfl⟩ := hlL
    obtain ⟨i, hi⟩ := (hL w).exists_dotProduct_ne_zero hx
    exact hasFiniteMulSupport_iSup_normAbs (Function.ne_iff.mpr ⟨i, hi⟩)
  refine (hc.union (hLfin.biUnion hl)).subset fun v hv ↦ ?_
  by_cases hcv : c v = 0
  · refine Or.inr (Set.mem_biUnion (Set.mem_range_self v) ?_)
    simpa [twistedLocalHeight_def, hcv] using hv
  · exact Or.inl hcv

/-! ### The twisted height -/

open Classical in
/-- The twisted height `H_{L,c,Q}(x) = ∏_v max_i (|L v i ⬝ᵥ x|_v * Q ^ (-c v i))` of a point
`x ≠ 0` of `K ^ n`, for linear forms `L v i` and weights `c v i` indexed by the places `v` of `K`.
The twisted height of `0` is `0`.

The product is Mathlib's `finprod`. It is the true product over the places when the local factors
are `1` at all but finitely many places, as under the usual hypotheses on the data
(`hasFiniteMulSupport_twistedLocalHeight`), and it is `1` otherwise. -/
def twistedHeight (L : Place K → Fin n → Fin n → K) (c : Place K → Fin n → ℝ) (Q : ℝ)
    (x : Fin n → K) : ℝ :=
  if x = 0 then 0 else ∏ᶠ v, twistedLocalHeight L c Q v x

@[simp]
theorem twistedHeight_zero : twistedHeight L c Q 0 = 0 := by
  simp [twistedHeight]

theorem twistedHeight_of_ne_zero {x : Fin n → K} (hx : x ≠ 0) :
    twistedHeight L c Q x = ∏ᶠ v, twistedLocalHeight L c Q v x := by
  simp [twistedHeight, hx]

theorem twistedHeight_nonneg (hQ : 0 ≤ Q) (x : Fin n → K) : 0 ≤ twistedHeight L c Q x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [twistedHeight_of_ne_zero hx]
    exact finprod_nonneg fun v ↦ twistedLocalHeight_nonneg hQ v x

/-- For `Q > 0` and forms linearly independent at every place, the twisted height of a nonzero
point is positive. -/
theorem twistedHeight_pos (hQ : 0 < Q) (hL : ∀ v, LinearIndependent K (L v)) {x : Fin n → K}
    (hx : x ≠ 0) : 0 < twistedHeight L c Q x := by
  rw [twistedHeight_of_ne_zero hx]
  by_cases hfin : HasFiniteMulSupport fun v ↦ twistedLocalHeight L c Q v x
  · rw [finprod_eq_prod _ hfin]
    exact Finset.prod_pos fun v _ ↦ twistedLocalHeight_pos hQ (hL v) hx
  · rw [finprod_of_infinite_mulSupport hfin]
    exact one_pos

theorem twistedHeight_eq_zero_iff (hQ : 0 < Q) (hL : ∀ v, LinearIndependent K (L v))
    {x : Fin n → K} : twistedHeight L c Q x = 0 ↔ x = 0 :=
  ⟨fun h ↦ by_contra fun hx ↦ (twistedHeight_pos hQ hL hx).ne' h, fun h ↦ h ▸ twistedHeight_zero⟩

/-- The twisted height is projective: it is unchanged by scaling with a nonzero element of `K`. -/
theorem twistedHeight_smul {a : K} (ha : a ≠ 0) (x : Fin n → K) :
    twistedHeight L c Q (a • x) = twistedHeight L c Q x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [twistedHeight_of_ne_zero (smul_ne_zero ha hx), twistedHeight_of_ne_zero hx]
  simp_rw [twistedLocalHeight_smul]
  exact finprod_mul_eq_right_of_finprod_eq_one (hasFiniteMulSupport_normAbs ha)
    (finprod_normAbs_eq_one ha)

/-- For `Q = 1` the twisted height of a nonzero point is `∏_v max_i |L v i ⬝ᵥ x|_v`; in particular
it does not depend on the weights. -/
theorem twistedHeight_one {x : Fin n → K} (hx : x ≠ 0) :
    twistedHeight L c 1 x = ∏ᶠ v, ⨆ i, normAbs v (L v i ⬝ᵥ x) := by
  simp_rw [twistedHeight_of_ne_zero hx, twistedLocalHeight_one]

/-- For the coordinate forms and zero weights, the twisted height of a nonzero point is its
absolute multiplicative height `Height.mulHeight x ^ (1 / [K : ℚ])`. -/
theorem twistedHeight_coordForms_zero {x : Fin n → K} (hx : x ≠ 0) :
    twistedHeight (coordForms K n) 0 Q x = Height.mulHeight x ^ ((1 : ℝ) / finrank ℚ K) := by
  have hD : finrank ℚ K ≠ 0 := finrank_pos.ne'
  rw [twistedHeight_of_ne_zero hx, mulHeight_eq_finprod_iSup_normalizedAbsValue hx]
  simp_rw [twistedLocalHeight_coordForms_zero, ← iSup_normAbs_pow_finrank]
  rw [← finprod_pow (hasFiniteMulSupport_iSup_normAbs hx), one_div,
    Real.pow_rpow_inv_natCast (finprod_nonneg fun v ↦
      Real.iSup_nonneg fun i ↦ normAbs_nonneg v (x i)) hD]

/-- Shifting the weights at each place `v` by a finitely supported `θ v` multiplies the twisted
height of `x` by `Q ^ (∑ᶠ v, θ v)`, provided the local factors at `x` are `1` at all but finitely
many places. -/
theorem twistedHeight_shift_of_hasFiniteMulSupport (hQ : 0 < Q) {θ : Place K → ℝ}
    (hθ : HasFiniteSupport θ) {x : Fin n → K}
    (hx : HasFiniteMulSupport fun v ↦ twistedLocalHeight L c Q v x) :
    twistedHeight L (fun v i ↦ c v i - θ v) Q x = Q ^ (∑ᶠ v, θ v) * twistedHeight L c Q x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  rw [twistedHeight_of_ne_zero hx0, twistedHeight_of_ne_zero hx0, Real.rpow_finsum_of_pos hQ hθ,
    ← finprod_mul_distrib (hθ.hasFiniteMulSupport_fun_rpow fun _ ↦ Q) hx]
  exact finprod_congr fun v ↦ twistedLocalHeight_shift hQ θ v x

/-- Shifting the weights at each place `v` by a finitely supported `θ v` multiplies the twisted
height by `Q ^ (∑ᶠ v, θ v)`, under the usual hypotheses on the data. -/
theorem twistedHeight_shift (hQ : 0 < Q) (hL : ∀ v, LinearIndependent K (L v))
    (hLfin : (Set.range L).Finite) (hc : HasFiniteSupport c) {θ : Place K → ℝ}
    (hθ : HasFiniteSupport θ) (x : Fin n → K) :
    twistedHeight L (fun v i ↦ c v i - θ v) Q x = Q ^ (∑ᶠ v, θ v) * twistedHeight L c Q x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  exact twistedHeight_shift_of_hasFiniteMulSupport hQ hθ
    (hasFiniteMulSupport_twistedLocalHeight hL hLfin hc hx)

/-- Composing every form with an invertible linear change of variables `y ↦ A *ᵥ y` is
evaluating the twisted height at `A *ᵥ x`. -/
theorem twistedHeight_vecMul {A : Matrix (Fin n) (Fin n) K} (hA : IsUnit A) (x : Fin n → K) :
    twistedHeight (fun v i ↦ L v i ᵥ* A) c Q x = twistedHeight L c Q (A *ᵥ x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hAx : A *ᵥ x ≠ 0 := fun h ↦ hx <| mulVec_injective_iff_isUnit.mpr hA <| by simpa using h
  rw [twistedHeight_of_ne_zero hx, twistedHeight_of_ne_zero hAx]
  simp_rw [twistedLocalHeight_vecMul]

end TauCeti
