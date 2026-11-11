/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Restriction

/-!
# Lowering the integrability exponent of Sobolev functions

On a domain `Ω` of finite measure, `L^q(Ω) ⊆ Lᵖ(Ω)` continuously for `1 ≤ p ≤ q ≤ ∞`, with
`‖f‖_p ≤ μ(Ω) ^ (1/p - 1/q) ‖f‖_q`
(Mathlib's `MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ`).
Applying this inclusion to the value and to every weak derivative gives continuous linear maps
`W^{1,q}(Ω) → W^{1,p}(Ω)` and `W^{k,q}(Ω) → W^{k,p}(Ω)` for every natural order `k`. They do not
change the value or any weak derivative, so they are injective, commute with forgetting the
highest derivative and with restriction to an open subdomain, and compose transitively.

The first-order map is the bundled form of `TauCeti.W1p.ofExponentLE`. The map at order `k + 2` is
assembled by `TauCeti.Wkp.mk` from the map at order `k + 1` and the `Lᵖ` copy of the highest weak
derivative, whose weak derivative identity is unchanged up to almost everywhere equality.

## Main definitions

* `TauCeti.W1p.ofExponentLEL`: the continuous inclusion `W^{1,q}(Ω) → W^{1,p}(Ω)`.
* `TauCeti.Wkp.ofExponentLEL`: the continuous inclusion `W^{k,q}(Ω) → W^{k,p}(Ω)`.

## Main results

* `TauCeti.Wkp.value_ofExponentLEL_ae`, `TauCeti.Wkp.iteratedGradient_ofExponentLEL_ae`: the value
  and the highest weak derivative are unchanged.
* `TauCeti.Wkp.lowerOrder_ofExponentLEL`, `TauCeti.Wkp.restrictL_ofExponentLEL`: compatibility with
  the lower-order projection and with restriction.
* `TauCeti.Wkp.ofExponentLEL_injective`: the inclusion is injective.

## References

* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 2.14 and §3.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped ENNReal

section Lp

variable {α F : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The exponent of the measure factor in the inclusion `L^q → Lᵖ` is nonnegative. -/
private theorem one_div_sub_one_div_nonneg (hpq : p ≤ q) : 0 ≤ 1 / p.toReal - 1 / q.toReal := by
  rcases eq_or_ne q ∞ with rfl | hq
  · simp only [ENNReal.toReal_top, div_zero, sub_zero]
    positivity
  have hp : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' (hpq.trans_lt hq.lt_top).ne
  exact sub_nonneg.2 (one_div_le_one_div_of_le hp (ENNReal.toReal_mono hq hpq))

/-- The continuous inclusion `L^q(ν) → Lᵖ(ν)` for a finite measure `ν` and `p ≤ q`; it does not
change the underlying almost everywhere equivalence class. -/
private def lpOfExponentLEL (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (hpq : p ≤ q) :
    Lp F q ν →L[ℝ] Lp F p ν :=
  LinearMap.mkContinuous
    { toFun f := ⟨f.1, Lp.antitone hpq f.2⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    (ν Set.univ ^ (1 / p.toReal - 1 / q.toReal)).toReal fun f => by
      change (eLpNorm f p ν).toReal ≤ _ * (eLpNorm f q ν).toReal
      have hc : ν Set.univ ^ (1 / p.toReal - 1 / q.toReal) ≠ ∞ :=
        ENNReal.rpow_ne_top_of_nonneg (one_div_sub_one_div_nonneg hpq) (measure_ne_top ν _)
      rw [mul_comm, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) hc)
        (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq (Lp.aestronglyMeasurable f))

private theorem lpOfExponentLEL_apply (hpq : p ≤ q) (f : Lp F q ν) :
    lpOfExponentLEL F hpq f = ⟨f.1, Lp.antitone hpq f.2⟩ :=
  rfl

private theorem coeFn_lpOfExponentLEL (hpq : p ≤ q) (f : Lp F q ν) :
    ⇑(lpOfExponentLEL F hpq f) = ⇑f :=
  rfl

end Lp

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega U : Opens E} {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
  [IsFiniteMeasure (mu.restrict (Omega : Set E))]

/-- On a domain of finite measure, the continuous inclusion `W^{1,q}(Ω) → W^{1,p}(Ω)` for
`p ≤ q`; it does not change the value or the weak gradient (`TauCeti.W1p.ofExponentLE`). -/
def W1p.ofExponentLEL (hpq : p ≤ q) : W1p mu Omega q →L[ℝ] W1p mu Omega p :=
  LinearMap.mkContinuous
    { toFun := W1p.ofExponentLE hpq
      map_add' := W1p.ofExponentLE_add hpq
      map_smul' := W1p.ofExponentLE_smul hpq }
    ‖lpOfExponentLEL (ν := mu.restrict Omega) (Sobolev1Jet E) hpq‖ fun u => by
      change ‖(W1p.ofExponentLE hpq u : Sobolev1JetLp mu Omega p)‖ ≤
        _ * ‖(u : Sobolev1JetLp mu Omega q)‖
      rw [W1p.coe_ofExponentLE, ← lpOfExponentLEL_apply]
      exact (lpOfExponentLEL (Sobolev1Jet E) hpq).le_opNorm _

omit [FiniteDimensional ℝ E] in
@[simp]
theorem W1p.ofExponentLEL_apply (hpq : p ≤ q) (u : W1p mu Omega q) :
    W1p.ofExponentLEL hpq u = W1p.ofExponentLE hpq u :=
  (rfl)

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
      ⟨mk k v.1 (lpOfExponentLEL _ hpq (iteratedGradient (k + 1) u))
          (((hasWeakFDerivOn_iteratedGradient k u).congr_ae v.2.2.symm).congr_ae_deriv
            (by rw [coeFn_lpOfExponentLEL])),
        by rw [value_mk, value_succ (k + 1) u]; exact v.2.1,
        by rw [iteratedGradient_mk, coeFn_lpOfExponentLEL]⟩

/-- The underlying function of `TauCeti.Wkp.ofExponentLEL`. -/
private def ofExponentLEFun (hpq : p ≤ q) : (k : ℕ) → Wkp mu Omega q k → Wkp mu Omega p k
  | 0, u => lpOfExponentLEL ℝ hpq u
  | k + 1, u => (ofExponentLEAux hpq k u).1

private theorem value_ofExponentLEFun_ae (hpq : p ≤ q) (k : ℕ) (u : Wkp mu Omega q k) :
    ⇑(value k (ofExponentLEFun hpq k u)) =ᵐ[mu.restrict Omega] value k u := by
  cases k with
  | zero =>
      simp only [value_zero]
      exact Filter.EventuallyEq.of_eq (coeFn_lpOfExponentLEL hpq u)
  | succ k => exact (ofExponentLEAux hpq k u).2.1

private theorem value_ofExponentLEFun (hpq : p ≤ q) (k : ℕ) (u : Wkp mu Omega q k) :
    value k (ofExponentLEFun hpq k u) = lpOfExponentLEL ℝ hpq (value k u) :=
  Lp.ext (value_ofExponentLEFun_ae hpq k u)

private theorem lowerOrder_ofExponentLEFun (hpq : p ≤ q) (k : ℕ)
    (u : Wkp mu Omega q (k + 1)) :
    lowerOrder k (ofExponentLEFun hpq (k + 1) u) = ofExponentLEFun hpq k (lowerOrder k u) := by
  apply ext k
  rw [← value_succ, value_ofExponentLEFun, value_ofExponentLEFun, value_succ]

private theorem iteratedGradient_ofExponentLEFun (hpq : p ≤ q) (k : ℕ)
    (u : Wkp mu Omega q (k + 1)) :
    iteratedGradient k (ofExponentLEFun hpq (k + 1) u) =
      lpOfExponentLEL _ hpq (iteratedGradient k u) :=
  Lp.ext (ofExponentLEAux hpq k u).2.2

private theorem continuous_ofExponentLEFun (hpq : p ≤ q) :
    ∀ k : ℕ, Continuous (ofExponentLEFun (mu := mu) (Omega := Omega) hpq k)
  | 0 => (lpOfExponentLEL ℝ hpq).continuous
  | k + 1 => by
      refine (continuous_iff_lowerOrder_iteratedGradient k).2 ⟨?_, ?_⟩
      · exact ((continuous_ofExponentLEFun hpq k).comp (lowerOrderL k).continuous).congr
          fun u => by rw [Function.comp_apply, lowerOrderL_apply, lowerOrder_ofExponentLEFun]
      · exact ((lpOfExponentLEL _ hpq).continuous.comp (iteratedGradientL k).continuous).congr
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

/-- A Sobolev function of exponent `q` is the image of a Sobolev function of exponent `p` exactly
when their values agree almost everywhere. -/
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
  (rfl)

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
