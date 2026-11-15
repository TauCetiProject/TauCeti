/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Restriction
public import TauCeti.MeasureTheory.Function.Lp.Exponent

/-!
# Lowering the integrability exponent of Sobolev functions

On a domain `Ω` of finite measure, `L^q(Ω) ⊆ Lᵖ(Ω)` continuously for `1 ≤ p ≤ q ≤ ∞`, with
`‖f‖_p ≤ μ(Ω) ^ (1/p - 1/q) ‖f‖_q`
(Mathlib's `MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ`, bundled as
`MeasureTheory.Lp.ofExponentLEL`). Applying this inclusion to the value and to every weak derivative
gives continuous linear maps `W^{k,q}(Ω) → W^{k,p}(Ω)` for every natural order `k`. They do not
change the value or any weak derivative, so they are injective, commute with forgetting the
highest derivative and with restriction to an open subdomain, and compose transitively.

The first-order map is `TauCeti.W1p.ofExponentLEL`, the bundled form of
`TauCeti.W1p.ofExponentLE`. The map at order `k + 2` is assembled by `TauCeti.Wkp.mk` from the map
at order `k + 1` and the `Lᵖ` copy of the highest weak derivative, whose weak derivative identity
is unchanged up to almost everywhere equality.

## Main definitions

* `TauCeti.Wkp.ofExponentLEL`: the continuous inclusion `W^{k,q}(Ω) → W^{k,p}(Ω)`.

## Main results

* `TauCeti.Wkp.value_ofExponentLEL`, `TauCeti.Wkp.iteratedGradient_ofExponentLEL`: the value and
  the highest weak derivative are their `Lᵖ` copies.
* `TauCeti.Wkp.value_ofExponentLEL_ae`, `TauCeti.Wkp.iteratedGradient_ofExponentLEL_ae`: the value
  and the highest weak derivative are unchanged.
* `TauCeti.Wkp.lowerOrder_ofExponentLEL`, `TauCeti.Wkp.restrictL_ofExponentLEL`: compatibility with
  the lower-order projection and with restriction.
* `TauCeti.Wkp.ofExponentLEL_injective`: the inclusion is injective.
* `TauCeti.Wkp.opNorm_ofExponentLEL_le`, `TauCeti.Wkp.norm_ofExponentLEL_apply_le`: the bound
  `μ(Ω) ^ (1/p - 1/q)` on the operator norm.

## References

* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 2.14 and §3.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega U : Opens E} {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
  [IsFiniteMeasure (mu.restrict (Omega : Set E))]

namespace Wkp

/-- The inclusion at order `k + 1`, built recursively together with the facts that it keeps the
value and the highest weak derivative. -/
private def ofExponentLEAux (hpq : p ≤ q) : (k : ℕ) → (u : Wkp mu Omega q (k + 1)) →
    {v : Wkp mu Omega p (k + 1) // value (k + 1) v =ᵐ[mu.restrict Omega] value (k + 1) u ∧
      iteratedGradient k v =ᵐ[mu.restrict Omega] iteratedGradient k u}
  | 0, u => ⟨W1p.ofExponentLE hpq u, by
      simpa only [Nat.reduceAdd, value_one, value_one (W1p.ofExponentLE hpq u)] using
        W1p.value_ofExponentLE_ae hpq u, by
      simpa only [iteratedGradient_zero, iteratedGradient_zero (W1p.ofExponentLE hpq u)] using
        W1p.gradient_ofExponentLE_ae hpq u⟩
  | k + 1, u =>
      let v := ofExponentLEAux hpq k (lowerOrder (k + 1) u)
      ⟨mk k v.1 (Lp.ofExponentLEL ℝ _ hpq (iteratedGradient (k + 1) u))
          (((hasWeakFDerivOn_iteratedGradient k u).congr_ae v.2.2.symm).congr_ae_deriv
            (by rw [Lp.coeFn_ofExponentLEL])),
        by rw [value_mk, value_succ (k + 1) u]; exact v.2.1,
        by rw [iteratedGradient_mk, Lp.coeFn_ofExponentLEL]⟩

/-- The underlying function of `TauCeti.Wkp.ofExponentLEL`. -/
private def ofExponentLEFun (hpq : p ≤ q) : (k : ℕ) → Wkp mu Omega q k → Wkp mu Omega p k
  | 0, u => Lp.ofExponentLEL ℝ ℝ hpq u
  | k + 1, u => (ofExponentLEAux hpq k u).1

private theorem value_ofExponentLEFun_ae (hpq : p ≤ q) (k : ℕ) (u : Wkp mu Omega q k) :
    ⇑(value k (ofExponentLEFun hpq k u)) =ᵐ[mu.restrict Omega] value k u := by
  cases k with
  | zero =>
      simp only [value_zero]
      exact Filter.EventuallyEq.of_eq (Lp.coeFn_ofExponentLEL hpq u)
  | succ k => exact (ofExponentLEAux hpq k u).2.1

private theorem value_ofExponentLEFun (hpq : p ≤ q) (k : ℕ) (u : Wkp mu Omega q k) :
    value k (ofExponentLEFun hpq k u) = Lp.ofExponentLEL ℝ ℝ hpq (value k u) :=
  Lp.ext (by rw [Lp.coeFn_ofExponentLEL]; exact value_ofExponentLEFun_ae hpq k u)

private theorem lowerOrder_ofExponentLEFun (hpq : p ≤ q) (k : ℕ)
    (u : Wkp mu Omega q (k + 1)) :
    lowerOrder k (ofExponentLEFun hpq (k + 1) u) = ofExponentLEFun hpq k (lowerOrder k u) := by
  apply ext k
  rw [← value_succ, value_ofExponentLEFun, value_ofExponentLEFun, value_succ]

private theorem iteratedGradient_ofExponentLEFun (hpq : p ≤ q) (k : ℕ)
    (u : Wkp mu Omega q (k + 1)) :
    iteratedGradient k (ofExponentLEFun hpq (k + 1) u) =
      Lp.ofExponentLEL ℝ _ hpq (iteratedGradient k u) :=
  Lp.ext (by rw [Lp.coeFn_ofExponentLEL]; exact (ofExponentLEAux hpq k u).2.2)

private theorem continuous_ofExponentLEFun (hpq : p ≤ q) :
    ∀ k : ℕ, Continuous (ofExponentLEFun (mu := mu) (Omega := Omega) hpq k)
  | 0 => (Lp.ofExponentLEL ℝ ℝ hpq).continuous
  | k + 1 => by
      refine (continuous_iff_lowerOrder_iteratedGradient k).2 ⟨?_, ?_⟩
      · exact ((continuous_ofExponentLEFun hpq k).comp (lowerOrderL k).continuous).congr
          fun u => by rw [Function.comp_apply, lowerOrderL_apply, lowerOrder_ofExponentLEFun]
      · exact ((Lp.ofExponentLEL ℝ _ hpq).continuous.comp (iteratedGradientL k).continuous).congr
          fun u => by
            rw [Function.comp_apply, iteratedGradientL_apply, iteratedGradient_ofExponentLEFun]

/-- On a domain of finite measure, the continuous inclusion `W^{k,q}(Ω) → W^{k,p}(Ω)` for
`p ≤ q`. It keeps the value and every weak derivative, as elements of `Lᵖ` rather than `L^q`. -/
def ofExponentLEL (hpq : p ≤ q) (k : ℕ) : Wkp mu Omega q k →L[ℝ] Wkp mu Omega p k where
  toFun := ofExponentLEFun hpq k
  map_add' u v := ext k (by simp only [value_ofExponentLEFun, value_add, map_add])
  map_smul' c u := ext k (by
    simp only [value_ofExponentLEFun, value_smul, map_smul, RingHom.id_apply])
  cont := continuous_ofExponentLEFun hpq k

/-- Lowering the exponent does not change the value of a Sobolev function. -/
theorem value_ofExponentLEL_ae (hpq : p ≤ q) (k : ℕ) (u : Wkp mu Omega q k) :
    ⇑(value k (ofExponentLEL hpq k u)) =ᵐ[mu.restrict Omega] value k u :=
  value_ofExponentLEFun_ae hpq k u

/-- The value of the image of a Sobolev function is the `Lᵖ` copy of its value. -/
@[simp]
theorem value_ofExponentLEL (hpq : p ≤ q) (k : ℕ) (u : Wkp mu Omega q k) :
    value k (ofExponentLEL hpq k u) = Lp.ofExponentLEL ℝ ℝ hpq (value k u) :=
  value_ofExponentLEFun hpq k u

/-- The highest weak derivative of the image of a Sobolev function is the `Lᵖ` copy of its
highest weak derivative.
Use `rw` with this lemma: `simp` does not match its dependently indexed left-hand side. -/
theorem iteratedGradient_ofExponentLEL (hpq : p ≤ q) (k : ℕ) (u : Wkp mu Omega q (k + 1)) :
    iteratedGradient k (ofExponentLEL hpq (k + 1) u) =
      Lp.ofExponentLEL ℝ _ hpq (iteratedGradient k u) :=
  iteratedGradient_ofExponentLEFun hpq k u

/-- Lowering the exponent does not change the highest weak derivative of a Sobolev function. -/
theorem iteratedGradient_ofExponentLEL_ae (hpq : p ≤ q) (k : ℕ) (u : Wkp mu Omega q (k + 1)) :
    ⇑(iteratedGradient k (ofExponentLEL hpq (k + 1) u)) =ᵐ[mu.restrict Omega]
      iteratedGradient k u :=
  (ofExponentLEAux hpq k u).2.2

/-- Lowering the exponent commutes with forgetting the highest derivative.
Use `rw` with this lemma: `simp` does not match its dependently indexed left-hand side. -/
theorem lowerOrder_ofExponentLEL (hpq : p ≤ q) (k : ℕ) (u : Wkp mu Omega q (k + 1)) :
    lowerOrder k (ofExponentLEL hpq (k + 1) u) = ofExponentLEL hpq k (lowerOrder k u) :=
  lowerOrder_ofExponentLEFun hpq k u

/-- A Sobolev function `v` of exponent `p` is the image of a Sobolev function `u` of exponent `q`
exactly when their values agree almost everywhere. -/
theorem ofExponentLEL_eq_iff (hpq : p ≤ q) (k : ℕ) {u : Wkp mu Omega q k}
    {v : Wkp mu Omega p k} :
    ofExponentLEL hpq k u = v ↔ ⇑(value k u) =ᵐ[mu.restrict Omega] value k v := by
  refine ⟨fun h => h ▸ (value_ofExponentLEL_ae hpq k u).symm, fun h => ext k (Lp.ext ?_)⟩
  exact (value_ofExponentLEL_ae hpq k u).trans h

/-- Lowering the exponent is injective. -/
theorem ofExponentLEL_injective (hpq : p ≤ q) (k : ℕ) :
    Function.Injective (ofExponentLEL (mu := mu) (Omega := Omega) hpq k) := fun u v h =>
  ext k (Lp.ext (((value_ofExponentLEL_ae hpq k u).symm.trans (by rw [h])).trans
    (value_ofExponentLEL_ae hpq k v)))

/-- At first order, lowering the exponent is the first-order inclusion. -/
@[simp]
theorem ofExponentLEL_one (hpq : p ≤ q) :
    ofExponentLEL (mu := mu) (Omega := Omega) hpq 1 = W1p.ofExponentLEL hpq :=
  ContinuousLinearMap.ext fun u => (W1p.ofExponentLEL_apply hpq u).symm

/-- At order zero, lowering the exponent is the `Lᵖ` inclusion. -/
@[simp]
theorem ofExponentLEL_zero (hpq : p ≤ q) :
    ofExponentLEL (mu := mu) (Omega := Omega) hpq 0 = Lp.ofExponentLEL ℝ ℝ hpq :=
  ContinuousLinearMap.ext fun u => by simpa only [value_zero] using value_ofExponentLEL hpq 0 u

/-- Lowering the exponent multiplies the `W^{k,p}` norm by at most `μ(Ω) ^ (1/p - 1/q)`. -/
theorem norm_ofExponentLEL_apply_le (hpq : p ≤ q) : ∀ (k : ℕ) (u : Wkp mu Omega q k),
    ‖ofExponentLEL hpq k u‖ ≤ (mu Omega ^ (1 / p.toReal - 1 / q.toReal)).toReal * ‖u‖
  | 0, u => by
      rw [ofExponentLEL_zero, ← Measure.restrict_apply_univ]
      exact Lp.norm_ofExponentLEL_apply_le hpq u
  | 1, u => by
      rw [ofExponentLEL_one]
      exact W1p.norm_ofExponentLEL_apply_le hpq u
  | k + 2, u => by
      have hlow := norm_ofExponentLEL_apply_le hpq (k + 1) (lowerOrder (k + 1) u)
      have hgrad := Lp.norm_ofExponentLEL_apply_le (𝕜 := ℝ) hpq (iteratedGradient (k + 1) u)
      rw [Measure.restrict_apply_univ] at hgrad
      refine le_of_pow_le_pow_left₀ two_ne_zero
        (mul_nonneg ENNReal.toReal_nonneg (norm_nonneg u)) ?_
      rw [norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k
          (ofExponentLEL hpq (k + 2) u),
        mul_pow, norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k u, mul_add,
        lowerOrder_ofExponentLEL, iteratedGradient_ofExponentLEL, ← mul_pow, ← mul_pow]
      exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) hlow 2)
        (pow_le_pow_left₀ (norm_nonneg _) hgrad 2)

/-- The operator norm of `W^{k,q}(Ω) → W^{k,p}(Ω)` is at most `μ(Ω) ^ (1/p - 1/q)`. -/
theorem opNorm_ofExponentLEL_le (hpq : p ≤ q) (k : ℕ) :
    ‖ofExponentLEL (mu := mu) (Omega := Omega) hpq k‖ ≤
      (mu Omega ^ (1 / p.toReal - 1 / q.toReal)).toReal :=
  ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg (norm_ofExponentLEL_apply_le hpq k)

/-- Lowering the exponent from `p` to itself is the identity. -/
@[simp]
theorem ofExponentLEL_self (k : ℕ) (u : Wkp mu Omega p k) : ofExponentLEL le_rfl k u = u :=
  (ofExponentLEL_eq_iff le_rfl k).2 Filter.EventuallyEq.rfl

/-- Exponent inclusions compose transitively. -/
@[simp]
theorem ofExponentLEL_ofExponentLEL (hpq : p ≤ q) (hqr : q ≤ r) (k : ℕ)
    (u : Wkp mu Omega r k) :
    ofExponentLEL hpq k (ofExponentLEL hqr k u) = ofExponentLEL (hpq.trans hqr) k u :=
  (ofExponentLEL_eq_iff hpq k).2 ((value_ofExponentLEL_ae hqr k u).trans
    (value_ofExponentLEL_ae (hpq.trans hqr) k u).symm)

/-- Lowering the exponent commutes with restriction to an open subdomain. -/
theorem restrictL_ofExponentLEL [IsFiniteMeasure (mu.restrict (U : Set E))] (hU : U ≤ Omega)
    (hpq : p ≤ q) (k : ℕ) (u : Wkp mu Omega q k) :
    restrictL hU k (ofExponentLEL hpq k u) = ofExponentLEL hpq k (restrictL hU k u) := by
  symm
  refine (ofExponentLEL_eq_iff hpq k).2 ?_
  refine (value_restrictL_ae hU k u).trans (Filter.EventuallyEq.trans ?_
    (value_restrictL_ae hU k _).symm)
  exact ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 hU)
    (value_ofExponentLEL_ae hpq k u).symm

end Wkp

end TauCeti
