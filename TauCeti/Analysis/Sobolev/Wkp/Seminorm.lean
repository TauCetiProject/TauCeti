/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Classical
public import TauCeti.Analysis.Sobolev.Wkp.Restriction

/-!
# Truncation of order and the Sobolev seminorms

For `j ≤ k`, an element `u ∈ W^{k,p}(Ω)` determines an element of `W^{j,p}(Ω)` by forgetting its
weak derivatives of order above `j`. This is the continuous linear map `TauCeti.Wkp.toOrderL`, the
`(k - j)`-fold iterate of `TauCeti.Wkp.lowerOrderL`. Through it, the weak derivative of order
`j + 1` of `u`, for `j + 1 ≤ k`, is the highest recorded derivative
`iteratedGradient j (toOrderL _ u)` of the truncation, a field in `Lᵖ(Ω; IteratedGradient E j)`.

The seminorm `|u|_{j,p}` of `u ∈ W^{k,p}(Ω)`, for `j ≤ k`, is the `Lᵖ` norm of the value of `u`
when `j = 0`, and the `Lᵖ` norm of its weak derivative of order `j` (with operator norms on the
derivative directions) when `j ≥ 1`. Each is a Mathlib `Seminorm`. These are the quantities in
which polynomial approximation estimates in Sobolev spaces, such as the Bramble–Hilbert lemma, are
stated.

The norm of `W^{k,p}(Ω)` is comparable with the Euclidean combination
`S(u) = (∑_{j ≤ k} |u|_{j,p}²)^{1/2}` of the seminorms:
`S(u) / √2 ≤ ‖u‖ ≤ √2 · S(u)` for every exponent `p` and every order `k`, and `‖u‖ = S(u)` when
`p = 2`. The constant `√2` comes from order one only, where the norm of `TauCeti.W1p` is the `Lᵖ`
norm of the pointwise Euclidean norm of the value and the gradient; from order two on, the squared
norm adds the squared norm of each further derivative exactly. For `p ≠ 2` the norm and `S` do
differ: for `sin` on `(0, 2π)` in `W^{1,∞}`, `S = √2` while the norm is `1`.

## Main definitions

* `TauCeti.Wkp.toOrderL`: the continuous projection `W^{k,p}(Ω) → W^{j,p}(Ω)` for `j ≤ k`.
* `TauCeti.Wkp.seminorm`: the seminorm `|·|_{j,p}` on `W^{k,p}(Ω)` for `j ≤ k`.

## Main results

* `TauCeti.Wkp.toOrderL_self`, `TauCeti.Wkp.toOrderL_toOrderL_apply`,
  `TauCeti.Wkp.value_toOrderL`, `TauCeti.Wkp.toOrderL_restrictL`: truncation is the identity at
  the same order, composes transitively, keeps the value, and commutes with restriction.
* `TauCeti.Wkp.hasWeakFDerivOn_iteratedGradient_toOrderL`: the weak derivative of order `j + 2`
  is the weak derivative of the weak derivative of order `j + 1`.
* `TauCeti.Wkp.iteratedGradient_toOrderL_ae_eq_of_contDiffOn`,
  `TauCeti.Wkp.seminorm_eq_lpNorm_iteratedFDeriv_of_contDiffOn`: for a representative that is
  smooth enough on `Ω`, the weak derivatives are the classical ones and the seminorms are the
  `Lᵖ` norms of the classical derivatives.
* `TauCeti.Wkp.seminorm_le_norm`, `TauCeti.Wkp.seminorm_toOrderL`: each seminorm is bounded by
  the norm and does not see truncation.
* `TauCeti.Wkp.norm_le_sqrt_two_mul`, `TauCeti.Wkp.sqrt_le_sqrt_two_mul_norm`,
  `TauCeti.Wkp.norm_eq_sqrt_sum_seminorm_sq`: the comparison of the norm with `S`.

## References

* S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, §1.3 (Sobolev norms and seminorms).
-/

public section

noncomputable section

namespace TauCeti.Wkp

open MeasureTheory TopologicalSpace
open scoped ENNReal ContDiff

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega U : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Truncation of order -/

/-- Forget the weak derivatives of order above `j`: the continuous projection
`W^{k,p}(Ω) → W^{j,p}(Ω)` for `j ≤ k`, the `(k - j)`-fold iterate of `TauCeti.Wkp.lowerOrderL`. -/
def toOrderL {j k : ℕ} (h : j ≤ k) : Wkp mu Omega p k →L[ℝ] Wkp mu Omega p j :=
  Nat.leRec (motive := fun k _ => Wkp mu Omega p k →L[ℝ] Wkp mu Omega p j)
    (ContinuousLinearMap.id ℝ _) (fun k _ T => T.comp (lowerOrderL k)) h

/-- Truncating to the same order is the identity. -/
@[simp]
theorem toOrderL_self (k : ℕ) :
    toOrderL (le_refl k) = ContinuousLinearMap.id ℝ (Wkp mu Omega p k) :=
  Nat.leRec_self _ _

/-- Truncating `u ∈ W^{k+1,p}(Ω)` to an order `j ≤ k` first forgets the highest derivative. -/
theorem toOrderL_succ_apply {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p (k + 1)) :
    toOrderL (h.trans k.le_succ) u = toOrderL h (lowerOrder k u) := by
  unfold toOrderL
  rw [Nat.leRec_succ _ _ h, ContinuousLinearMap.comp_apply, lowerOrderL_apply]

/-- Truncating to one order lower is `TauCeti.Wkp.lowerOrder`. -/
@[simp]
theorem toOrderL_succ_self_apply (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    toOrderL k.le_succ u = lowerOrder k u := by
  rw [toOrderL_succ_apply le_rfl, toOrderL_self, ContinuousLinearMap.id_apply]

/-- Truncating twice is truncating once, to the lower of the two orders. -/
@[simp]
theorem toOrderL_toOrderL_apply {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (u : Wkp mu Omega p k) :
    toOrderL hij (toOrderL hjk u) = toOrderL (hij.trans hjk) u := by
  induction k, hjk using Nat.le_induction with
  | base => rw [toOrderL_self, ContinuousLinearMap.id_apply]
  | succ k hjk ih => rw [toOrderL_succ_apply hjk, toOrderL_succ_apply (hij.trans hjk), ih]

/-- Truncating twice is truncating once, to the lower of the two orders. -/
theorem toOrderL_comp_toOrderL {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (toOrderL hij).comp (toOrderL hjk) =
      (toOrderL (hij.trans hjk) : Wkp mu Omega p k →L[ℝ] Wkp mu Omega p i) :=
  ContinuousLinearMap.ext fun u => toOrderL_toOrderL_apply hij hjk u

/-- Truncation keeps the `Lᵖ` value. -/
@[simp]
theorem value_toOrderL {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    value j (toOrderL h u) = value k u := by
  induction k, h using Nat.le_induction with
  | base => rw [toOrderL_self, ContinuousLinearMap.id_apply]
  | succ k h ih => rw [toOrderL_succ_apply h, ih, value_succ]

/-- Truncation commutes with restriction to an open subset. -/
theorem toOrderL_restrictL (hU : U ≤ Omega) {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    toOrderL h (restrictL hU k u) = restrictL hU j (toOrderL h u) :=
  ext j (by simp only [value_toOrderL, value_restrictL])

/-- Truncation does not increase the Sobolev norm. -/
theorem norm_toOrderL_apply_le {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    ‖toOrderL h u‖ ≤ ‖u‖ := by
  induction k, h using Nat.le_induction with
  | base => rw [toOrderL_self, ContinuousLinearMap.id_apply]
  | succ k h ih => exact (toOrderL_succ_apply h u ▸ ih _).trans (norm_lowerOrder_le k u)

/-- The truncation operator has norm at most one. -/
theorem opNorm_toOrderL_le {j k : ℕ} (h : j ≤ k) :
    ‖(toOrderL h : Wkp mu Omega p k →L[ℝ] Wkp mu Omega p j)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa only [one_mul] using norm_toOrderL_apply_le h u

/-- For `j + 2 ≤ k`, the weak derivative of order `j + 2` of `u ∈ W^{k,p}(Ω)` is the weak Fréchet
derivative of its weak derivative of order `j + 1`. -/
theorem hasWeakFDerivOn_iteratedGradient_toOrderL {j k : ℕ} (h : j + 2 ≤ k)
    (u : Wkp mu Omega p k) :
    HasWeakFDerivOn mu Omega (iteratedGradient j (toOrderL (Nat.le_of_succ_le h) u))
      (iteratedGradient (j + 1) (toOrderL h u)) := by
  have hlow : toOrderL (Nat.le_of_succ_le h) u = lowerOrder (j + 1) (toOrderL h u) := by
    rw [← toOrderL_succ_self_apply, toOrderL_toOrderL_apply]
  rw [hlow]
  exact hasWeakFDerivOn_iteratedGradient j (toOrderL h u)

/-- For a representative that is `C^{j+1}` on `Ω`, the weak derivative of order `j + 1` of
`u ∈ W^{k,p}(Ω)` is almost everywhere its classical iterated-gradient field. -/
theorem iteratedGradient_toOrderL_ae_eq_of_contDiffOn {j k : ℕ} (h : j + 1 ≤ k)
    (u : Wkp mu Omega p k) {f : E → ℝ} (hf : ContDiffOn ℝ (j + 1) f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    (iteratedGradient j (toOrderL h u) : E → IteratedGradient E j) =ᵐ[mu.restrict Omega]
      iteratedGradientChain f j :=
  iteratedGradient_ae_eq_of_contDiffOn j _ hf (by rwa [value_toOrderL])

/-! ### The seminorms -/

/-- The seminorm `|u|_{j,p}` on `W^{k,p}(Ω)`, for `j ≤ k`: the `Lᵖ` norm of the value of `u` when
`j = 0`, and the `Lᵖ` norm of the weak derivative of order `j` of `u` when `j ≥ 1`. -/
def seminorm (k : ℕ) : (j : ℕ) → j ≤ k → Seminorm ℝ (Wkp mu Omega p k)
  | 0, _ => (normSeminorm ℝ (Lp ℝ p (mu.restrict Omega))).comp (valueL k).toLinearMap
  | j + 1, h => (normSeminorm ℝ (Lp (IteratedGradient E j) p (mu.restrict Omega))).comp
      ((iteratedGradientL (mu := mu) (Omega := Omega) (p := p) j).comp (toOrderL h)).toLinearMap

/-- The seminorm of order zero is the `Lᵖ` norm of the value. -/
@[simp]
theorem seminorm_zero_apply (k : ℕ) (h : 0 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k 0 h u = ‖value k u‖ := by
  rw [seminorm, Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe, valueL_apply]

/-- The seminorm of order `j + 1` is the `Lᵖ` norm of the weak derivative of order `j + 1`. -/
@[simp]
theorem seminorm_succ_apply (k j : ℕ) (h : j + 1 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k (j + 1) h u = ‖iteratedGradient j (toOrderL h u)‖ := by
  rw [seminorm, Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, iteratedGradientL_apply]

/-- The top seminorm of `u ∈ W^{k+1,p}(Ω)` is the `Lᵖ` norm of its highest weak derivative. -/
theorem seminorm_self_apply (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    seminorm (k + 1) (k + 1) le_rfl u = ‖iteratedGradient k u‖ := by
  rw [seminorm_succ_apply, toOrderL_self, ContinuousLinearMap.id_apply]

/-- Each seminorm is bounded by the Sobolev norm. -/
theorem seminorm_le_norm (k j : ℕ) (h : j ≤ k) (u : Wkp mu Omega p k) :
    seminorm k j h u ≤ ‖u‖ := by
  cases j with
  | zero => exact (seminorm_zero_apply k h u).trans_le (norm_value_le k u)
  | succ j =>
      exact (seminorm_succ_apply k j h u).trans_le
        ((norm_iteratedGradient_le j _).trans (norm_toOrderL_apply_le h u))

/-- The seminorms of order at most `j` do not see the truncation to order `j`. -/
@[simp]
theorem seminorm_toOrderL {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (u : Wkp mu Omega p k) :
    seminorm j i hij (toOrderL hjk u) = seminorm k i (hij.trans hjk) u := by
  cases i with
  | zero => simp only [seminorm_zero_apply, value_toOrderL]
  | succ i => rw [seminorm_succ_apply, seminorm_succ_apply, toOrderL_toOrderL_apply]

/-- The seminorms of order at most `k` do not see the highest derivative of
`u ∈ W^{k+1,p}(Ω)`. -/
theorem seminorm_lowerOrder {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p (k + 1)) :
    seminorm k j h (lowerOrder k u) = seminorm (k + 1) j (h.trans k.le_succ) u := by
  rw [← toOrderL_succ_self_apply, seminorm_toOrderL]

/-- For a representative `f` that is `C^j` on `Ω`, the seminorm `|u|_{j,p}` is the `Lᵖ` norm of
the `j`th classical derivative of `f` on `Ω`. -/
theorem seminorm_eq_lpNorm_iteratedFDeriv_of_contDiffOn (k j : ℕ) (h : j ≤ k)
    (u : Wkp mu Omega p k) {f : E → ℝ} (hf : ContDiffOn ℝ j f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    seminorm k j h u = lpNorm (iteratedFDeriv ℝ j f) p (mu.restrict Omega) := by
  cases j with
  | zero =>
      have hfm : AEStronglyMeasurable f (mu.restrict Omega) :=
        (Lp.aestronglyMeasurable (value k u)).congr hu
      rw [seminorm_zero_apply, Lp.norm_def, lpNorm, eLpNorm_congr_ae hu]
      refine congrArg ENNReal.toReal (eLpNorm_congr_norm_ae hfm ?_
        (Filter.Eventually.of_forall fun _ => norm_iteratedFDeriv_zero.symm))
      rw [iteratedFDeriv_zero_eq_comp]
      exact (continuousMultilinearCurryFin0 ℝ E ℝ).symm.continuous.comp_aestronglyMeasurable hfm
  | succ j =>
      rw [seminorm_succ_apply]
      exact norm_iteratedGradient_eq_lpNorm_of_contDiffOn j _ hf (by rwa [value_toOrderL])

/-! ### Comparison of the norm with the seminorms -/

/-- At order zero the only seminorm is the norm. -/
theorem sum_seminorm_sq_zero (u : Wkp mu Omega p 0) :
    ∑ j : Fin 1, seminorm 0 j j.is_le u ^ 2 = ‖u‖ ^ 2 := by
  rw [Fin.sum_univ_one]
  -- At the concrete order `0`, `Wkp mu Omega p 0` is reducibly `Lp`, so instance search finds the
  -- `Lp` structures and `seminorm_zero_apply`, stated at a general order, does not fire under
  -- `simp`; it applies up to unfolding of those instances.
  exact congrArg (· ^ 2) ((seminorm_zero_apply 0 _ u).trans (congrArg norm (value_zero u)))

/-- The squared seminorms of `u ∈ W^{k+1,p}(Ω)` are those of its lower-order part together with
the squared norm of its highest weak derivative. -/
theorem sum_seminorm_sq_succ (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    ∑ j : Fin (k + 2), seminorm (k + 1) j j.is_le u ^ 2 =
      ∑ j : Fin (k + 1), seminorm k j j.is_le (lowerOrder k u) ^ 2 +
        ‖iteratedGradient k u‖ ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.val_castSucc, seminorm_lowerOrder]
  · simp only [Fin.val_last]
    rw [seminorm_self_apply]

/-- The squared Sobolev norm is at most twice the sum of the squared seminorms. -/
theorem norm_sq_le_two_mul_sum_seminorm_sq : ∀ (k : ℕ) (u : Wkp mu Omega p k),
    ‖u‖ ^ 2 ≤ 2 * ∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2
  | 0, u => by
      rw [sum_seminorm_sq_zero]
      nlinarith [sq_nonneg ‖u‖]
  | 1, u => by
      rw [sum_seminorm_sq_succ, sum_seminorm_sq_zero]
      have h := norm_le_norm_lowerOrder_add_norm_iteratedGradient 0 u
      nlinarith [norm_nonneg u, norm_nonneg (lowerOrder 0 u), norm_nonneg (iteratedGradient 0 u),
        sq_nonneg (‖lowerOrder 0 u‖ - ‖iteratedGradient 0 u‖)]
  | k + 2, u => by
      rw [sum_seminorm_sq_succ, norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ]
      nlinarith [norm_sq_le_two_mul_sum_seminorm_sq (k + 1) (lowerOrder (k + 1) u),
        sq_nonneg ‖iteratedGradient (k + 1) u‖]

/-- The sum of the squared seminorms is at most twice the squared Sobolev norm. -/
theorem sum_seminorm_sq_le_two_mul_norm_sq : ∀ (k : ℕ) (u : Wkp mu Omega p k),
    ∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2 ≤ 2 * ‖u‖ ^ 2
  | 0, u => by
      rw [sum_seminorm_sq_zero]
      nlinarith [sq_nonneg ‖u‖]
  | 1, u => by
      rw [sum_seminorm_sq_succ, sum_seminorm_sq_zero]
      have h₁ := norm_lowerOrder_le 0 u
      have h₂ := norm_iteratedGradient_le 0 u
      nlinarith [norm_nonneg (lowerOrder 0 u), norm_nonneg (iteratedGradient 0 u)]
  | k + 2, u => by
      rw [sum_seminorm_sq_succ, norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ]
      nlinarith [sum_seminorm_sq_le_two_mul_norm_sq (k + 1) (lowerOrder (k + 1) u),
        sq_nonneg ‖iteratedGradient (k + 1) u‖]

/-- At exponent two the squared Sobolev norm is the sum of the squared seminorms. -/
theorem norm_sq_eq_sum_seminorm_sq : ∀ (k : ℕ) (u : Wkp mu Omega 2 k),
    ‖u‖ ^ 2 = ∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2
  | 0, u => (sum_seminorm_sq_zero u).symm
  | k + 1, u => by
      rw [sum_seminorm_sq_succ, norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq,
        norm_sq_eq_sum_seminorm_sq k (lowerOrder k u)]

/-- **Upper comparison of the norm with the seminorms**:
`‖u‖ ≤ √2 · (∑_{j ≤ k} |u|_{j,p}²)^{1/2}`. -/
theorem norm_le_sqrt_two_mul (k : ℕ) (u : Wkp mu Omega p k) :
    ‖u‖ ≤ √2 * √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) := by
  rw [← Real.sqrt_mul zero_le_two]
  exact Real.le_sqrt_of_sq_le (norm_sq_le_two_mul_sum_seminorm_sq k u)

/-- **Lower comparison of the norm with the seminorms**:
`(∑_{j ≤ k} |u|_{j,p}²)^{1/2} ≤ √2 · ‖u‖`. -/
theorem sqrt_le_sqrt_two_mul_norm (k : ℕ) (u : Wkp mu Omega p k) :
    √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) ≤ √2 * ‖u‖ := by
  rw [← Real.sqrt_sq (norm_nonneg u), ← Real.sqrt_mul zero_le_two]
  exact Real.sqrt_le_sqrt (sum_seminorm_sq_le_two_mul_norm_sq k u)

/-- At exponent two the Sobolev norm is `(∑_{j ≤ k} |u|_{j,2}²)^{1/2}`. -/
theorem norm_eq_sqrt_sum_seminorm_sq (k : ℕ) (u : Wkp mu Omega 2 k) :
    ‖u‖ = √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) := by
  rw [← norm_sq_eq_sum_seminorm_sq, Real.sqrt_sq (norm_nonneg u)]

end TauCeti.Wkp
