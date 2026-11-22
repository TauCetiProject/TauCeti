/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Multiplicity
public import TauCeti.NumberTheory.Padics.Complex.Basic
public import TauCeti.NumberTheory.Padics.Complex.Valuation
public import TauCeti.NumberTheory.Padics.LogGauge
public import TauCeti.RingTheory.PowerSeries.Entire.Topology
public import TauCeti.RingTheory.PowerSeries.Taylor
import TauCeti.NumberTheory.NewtonPolygon.QuadraticSeries
import TauCeti.NumberTheory.NewtonPolygon.ZeroCount

/-!
# The `p`-adic quadratic-exponent series `∑ p^(n²) Xⁿ`

Specialising the general quadratic-exponent Newton polygon of
`TauCeti.NumberTheory.NewtonPolygon.QuadraticSeries` to `a = p` with
`TauCeti.padicRealValuation p p = 1`, the power series `∑ p^(n²) Xⁿ` over `ℚ_[p]` has Newton
polygon `n ↦ n ^ 2`, unit slopes `2 * n + 1`, and slope multiplicity `1` at every positive odd
integer and `0` elsewhere.

Since `‖p‖ = p⁻¹ < 1` in `ℚ_[p]` and `ℂ_[p]`, `PowerSeries.isEntire_mk_pow_sq` shows that
`∑ p^(n²) Xⁿ` is entire and nonpolynomial. Combining its Newton polygon over `ℚ_[p]` with the
zero-counting theorem of `TauCeti.NumberTheory.NewtonPolygon.ZeroCount`, over `ℂ_[p]` the series
has a unique zero `αₙ` of `p`-adic valuation `-(2 * n + 1)` for every `n : ℕ`, no other zeros in
`ℂ_[p]`, and every zero is simple. The canonical Weierstrass product factorisation
(`TauCeti.RingTheory.PowerSeries.Entire.Product`) therefore expresses `∑ p^(n²) Xⁿ` as
the unconditional infinite product `∏' n : ℕ, (1 - (α n)⁻¹ X)` in
`PowerSeries.IsEntire.subring ℂ_[p]`.

## Main results

* `TauCeti.PowerSeries.newtonPolygon_mk_padic_pow_sq`,
  `TauCeti.PowerSeries.unitSlope_newtonPolygon_mk_padic_pow_sq`,
  `TauCeti.PowerSeries.newtonSlopeMultiplicity_mk_padic_pow_sq_odd` and
  `TauCeti.PowerSeries.newtonSlopeMultiplicity_mk_padic_pow_sq_eq_zero`: the Newton polygon and
  slope multiplicities of `∑ p^(n²) Xⁿ` over `ℚ_[p]`.
* `TauCeti.PowerSeries.existsUnique_zero_mk_padicComplex_pow_sq`,
  `TauCeti.PowerSeries.exists_addValuation_eq_neg_odd_of_evalAt_mk_padicComplex_pow_sq_eq_zero` and
  `TauCeti.PowerSeries.order_taylor_zero_mk_padicComplex_pow_sq`: the zeros of `∑ p^(n²) Xⁿ` in
  `ℂ_[p]` are simple and consist of a unique zero of valuation `-(2 * n + 1)` for each `n : ℕ`.
* `TauCeti.PowerSeries.hasProd_mk_padicComplex_pow_sq` and
  `TauCeti.PowerSeries.eq_tprod_mk_padicComplex_pow_sq`: the unconditional entire Weierstrass
  product expansion of `∑ p^(n²) Xⁿ` over `ℂ_[p]`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
-/

public section

namespace TauCeti.PowerSeries

open _root_.PowerSeries

section PadicQuadraticSeries

variable (p : ℕ) [Fact p.Prime]

/-- Over `ℚ_[p]`, the entire series `∑ p^(n²) Xⁿ` has Newton polygon `n ↦ n ^ 2` with respect to
`TauCeti.padicRealValuation p`. -/
theorem newtonPolygon_mk_padic_pow_sq :
    (mk fun n ↦ (p : ℚ_[p]) ^ (n ^ 2)).newtonPolygon (padicRealValuation p) =
      fun n : ℕ ↦ (((n : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by
  have hp : padicRealValuation p (p : ℚ_[p]) = ((1 : ℝ) : WithTop ℝ) := padicRealValuation_p
  simpa only [one_mul] using PowerSeries.newtonPolygon_mk_pow_sq zero_le_one hp

/-- Over `ℚ_[p]`, the `n`-th unit slope of `∑ p^(n²) Xⁿ` is `2 * n + 1`. -/
theorem unitSlope_newtonPolygon_mk_padic_pow_sq (n : ℕ) :
    unitSlope ((mk fun k ↦ (p : ℚ_[p]) ^ (k ^ 2)).newtonPolygon (padicRealValuation p)) n =
      2 * (n : ℝ) + 1 := by
  have hp : padicRealValuation p (p : ℚ_[p]) = ((1 : ℝ) : WithTop ℝ) := padicRealValuation_p
  simpa only [one_mul] using PowerSeries.unitSlope_newtonPolygon_mk_pow_sq zero_le_one hp n

/-- Over `ℚ_[p]`, each odd slope `2 * n + 1` of `∑ p^(n²) Xⁿ` has multiplicity `1`. -/
theorem newtonSlopeMultiplicity_mk_padic_pow_sq_odd (n : ℕ) :
    (mk fun k ↦ (p : ℚ_[p]) ^ (k ^ 2)).newtonSlopeMultiplicity (padicRealValuation p)
      (2 * (n : ℝ) + 1) = 1 := by
  have hp : padicRealValuation p (p : ℚ_[p]) = ((1 : ℝ) : WithTop ℝ) := padicRealValuation_p
  simpa only [one_mul] using PowerSeries.newtonSlopeMultiplicity_mk_pow_sq_mul zero_lt_one hp n

/-- Over `ℚ_[p]`, any real number outside `{2 * n + 1 | n : ℕ}` has multiplicity `0` in the Newton
polygon of `∑ p^(n²) Xⁿ`. -/
theorem newtonSlopeMultiplicity_mk_padic_pow_sq_eq_zero {σ : ℝ}
    (hσ : σ ∉ Set.range fun n : ℕ ↦ (2 * (n : ℝ) + 1)) :
    (mk fun k ↦ (p : ℚ_[p]) ^ (k ^ 2)).newtonSlopeMultiplicity (padicRealValuation p) σ = 0 := by
  have hp : padicRealValuation p (p : ℚ_[p]) = ((1 : ℝ) : WithTop ℝ) := padicRealValuation_p
  refine PowerSeries.newtonSlopeMultiplicity_mk_pow_sq_eq_zero zero_le_one hp ?_
  simpa only [one_mul] using hσ

private theorem map_mk_padic_pow_sq :
    _root_.PowerSeries.map (algebraMap ℚ_[p] ℂ_[p]) (mk fun k ↦ (p : ℚ_[p]) ^ (k ^ 2)) =
      mk fun k ↦ (p : ℂ_[p]) ^ (k ^ 2) := by
  ext k
  simp

private theorem mk_padic_pow_sq_ne_zero : (mk fun k ↦ (p : ℚ_[p]) ^ (k ^ 2)) ≠ 0 := by
  intro h0
  have hc := congrArg (constantCoeff (R := ℚ_[p])) h0
  simp at hc

private theorem card_filter_zeroMultiset_mk_padic_pow_sq (σ : ℝ) :
    (((mk fun k ↦ (p : ℚ_[p]) ^ (k ^ 2)).zeroMultiset ((p : ℝ) ^ σ) ℂ_[p]).filter
      (‖·‖ = (p : ℝ) ^ σ)).card =
      (mk fun k ↦ (p : ℚ_[p]) ^ (k ^ 2)).newtonSlopeMultiplicity
        (padicRealValuation p) σ := by
  have hf : (mk fun k ↦ (p : ℚ_[p]) ^ (k ^ 2)).IsEntire := isEntire_mk_pow_sq Padic.norm_p_lt_one
  exact (hf.newtonSlopeMultiplicity_eq_card_filter_zeroMultiset_norm_eq (padicRealValuation p)
    (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt) (fun _ ↦ norm_eq_rpow_neg_padicRealValuation)
    ℂ_[p] (mk_padic_pow_sq_ne_zero p) σ).symm

private theorem mem_filter_zeroMultiset_mk_padic_pow_sq (σ : ℝ) (β : ℂ_[p]) :
    β ∈ ((mk fun k ↦ (p : ℚ_[p]) ^ (k ^ 2)).zeroMultiset ((p : ℝ) ^ σ) ℂ_[p]).filter
      (‖·‖ = (p : ℝ) ^ σ) ↔
      ‖β‖ = (p : ℝ) ^ σ ∧ (mk fun k ↦ (p : ℂ_[p]) ^ (k ^ 2)).evalAt β = 0 := by
  have hr : 0 < (p : ℝ) ^ σ :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) σ
  rw [Multiset.mem_filter,
    ((isEntire_mk_pow_sq Padic.norm_p_lt_one).isRestricted _).mem_zeroMultiset_iff hr
      (mk_padic_pow_sq_ne_zero p),
    map_mk_padic_pow_sq p]
  exact ⟨fun ⟨⟨_, hz⟩, hnorm⟩ ↦ ⟨hnorm, hz⟩, fun ⟨hnorm, hz⟩ ↦ ⟨⟨hnorm.le, hz⟩, hnorm⟩⟩

/-- **Unique zeros of `∑ p^(n²) Xⁿ` on odd spheres in `ℂ_[p]`.** For every `n : ℕ`, the entire
series `∑ p^(k²) X^k` over `ℂ_[p]` has a unique zero of `p`-adic valuation `-(2 * n + 1)`. -/
theorem existsUnique_zero_mk_padicComplex_pow_sq (n : ℕ) :
    ∃! α : ℂ_[p],
      PadicComplex.addValuation p α = ↑(-((2 * n + 1 : ℕ) : ℚ)) ∧
        (mk fun k ↦ (p : ℂ_[p]) ^ (k ^ 2)).evalAt α = 0 := by
  let σ : ℝ := 2 * (n : ℝ) + 1
  have hcard : (((mk fun k ↦ (p : ℚ_[p]) ^ (k ^ 2)).zeroMultiset ((p : ℝ) ^ σ) ℂ_[p]).filter
      (‖·‖ = (p : ℝ) ^ σ)).card = 1 :=
    (card_filter_zeroMultiset_mk_padic_pow_sq p σ).trans
      (newtonSlopeMultiplicity_mk_padic_pow_sq_odd p n)
  obtain ⟨α, hα⟩ := Multiset.card_eq_one.mp hcard
  have hmem_iff (β : ℂ_[p]) :
      β ∈ ((mk fun k ↦ (p : ℚ_[p]) ^ (k ^ 2)).zeroMultiset ((p : ℝ) ^ σ) ℂ_[p]).filter
        (‖·‖ = (p : ℝ) ^ σ) ↔
        PadicComplex.addValuation p β = ↑(-((2 * n + 1 : ℕ) : ℚ)) ∧
          (mk fun k ↦ (p : ℂ_[p]) ^ (k ^ 2)).evalAt β = 0 := by
    rw [mem_filter_zeroMultiset_mk_padic_pow_sq p σ β, PadicComplex.addValuation_eq_coe_iff,
      Rat.cast_neg, neg_neg, Rat.cast_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one]
  have hα_in := hα ▸ Multiset.mem_singleton_self α
  refine ⟨α, (hmem_iff α).mp hα_in, fun β hβ ↦ ?_⟩
  have hβ_in := (hmem_iff β).mpr hβ
  rwa [hα, Multiset.mem_singleton] at hβ_in

/-- **All zeros of `∑ p^(n²) Xⁿ` in `ℂ_[p]` have negative odd integer valuations.** -/
theorem exists_addValuation_eq_neg_odd_of_evalAt_mk_padicComplex_pow_sq_eq_zero {α : ℂ_[p]}
    (hz : (mk fun k ↦ (p : ℂ_[p]) ^ (k ^ 2)).evalAt α = 0) :
    ∃ n : ℕ, PadicComplex.addValuation p α = ↑(-((2 * n + 1 : ℕ) : ℚ)) := by
  have hb : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at hz
  let σ : ℝ := Real.logb p ‖α‖
  have hrpow : (p : ℝ) ^ σ = ‖α‖ :=
    Real.rpow_logb (zero_lt_one.trans hb) hb.ne' (norm_pos_iff.mpr hα0)
  have hmem : α ∈ ((mk fun k ↦ (p : ℚ_[p]) ^ (k ^ 2)).zeroMultiset ((p : ℝ) ^ σ) ℂ_[p]).filter
      (‖·‖ = (p : ℝ) ^ σ) :=
    (mem_filter_zeroMultiset_mk_padic_pow_sq p σ α).mpr ⟨hrpow.symm, hz⟩
  have hpos_mult : 0 < (mk fun k ↦ (p : ℚ_[p]) ^ (k ^ 2)).newtonSlopeMultiplicity
      (padicRealValuation p) σ := by
    rw [← card_filter_zeroMultiset_mk_padic_pow_sq p σ, Multiset.card_pos_iff_exists_mem]
    exact ⟨α, hmem⟩
  by_contra hnot
  have hnot_range : σ ∉ Set.range fun n : ℕ ↦ (2 * (n : ℝ) + 1) := by
    rintro ⟨n, hn⟩
    refine hnot ⟨n, ?_⟩
    rw [PadicComplex.addValuation_eq_coe_iff, Rat.cast_neg, neg_neg, Rat.cast_natCast,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    exact (hn ▸ hrpow).symm
  exact hpos_mult.ne' (newtonSlopeMultiplicity_mk_padic_pow_sq_eq_zero p hnot_range)

/-- **Every zero of `∑ p^(n²) Xⁿ` in `ℂ_[p]` is simple.** -/
theorem order_taylor_zero_mk_padicComplex_pow_sq {α : ℂ_[p]}
    (hz : (mk fun k ↦ (p : ℂ_[p]) ^ (k ^ 2)).evalAt α = 0) :
    (_root_.PowerSeries.taylor α (mk fun k ↦ (p : ℂ_[p]) ^ (k ^ 2))).order = 1 := by
  classical
  obtain ⟨n, hval⟩ := exists_addValuation_eq_neg_odd_of_evalAt_mk_padicComplex_pow_sq_eq_zero p hz
  let σ : ℝ := 2 * (n : ℝ) + 1
  let r : ℝ := (p : ℝ) ^ σ
  have hr : 0 < r := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) σ
  have hnorm : ‖α‖ = r := by
    rwa [PadicComplex.addValuation_eq_coe_iff, Rat.cast_neg, neg_neg, Rat.cast_natCast,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hval
  obtain ⟨β, hβ⟩ := Multiset.card_eq_one.mp
    ((card_filter_zeroMultiset_mk_padic_pow_sq p σ).trans
      (newtonSlopeMultiplicity_mk_padic_pow_sq_odd p n))
  have hα_in := (mem_filter_zeroMultiset_mk_padic_pow_sq p σ α).mpr ⟨hnorm, hz⟩
  have hαβ : α = β := Multiset.mem_singleton.mp (hβ ▸ hα_in)
  rw [← map_mk_padic_pow_sq p,
    ((isEntire_mk_pow_sq Padic.norm_p_lt_one).isRestricted r).order_taylor_eq_count_zeroMultiset hr
      (mk_padic_pow_sq_ne_zero p) hnorm.le,
    ← Multiset.count_filter_of_pos (p := (‖·‖ = r)) hnorm, hβ, hαβ,
    Multiset.count_singleton_self, Nat.cast_one]

/-- **Unconditional Weierstrass product for `∑ p^(n²) Xⁿ` over `ℂ_[p]`.** If `α : ℕ → ℂ_[p]`
assigns to each `n : ℕ` the unique zero of `∑ p^(k²) X^k` of valuation `-(2 * n + 1)`, then
`∑ p^(k²) X^k` is the unconditional product of `1 - (α n)⁻¹ X` in
`PowerSeries.IsEntire.subring ℂ_[p]`. -/
theorem hasProd_mk_padicComplex_pow_sq {α : ℕ → ℂ_[p]}
    (hval : ∀ n : ℕ, PadicComplex.addValuation p (α n) = ↑(-((2 * n + 1 : ℕ) : ℚ)))
    (hz : ∀ n : ℕ, (mk fun k ↦ (p : ℂ_[p]) ^ (k ^ 2)).evalAt (α n) = 0) :
    HasProd (fun n : ℕ ↦ IsEntire.polynomialHom (1 - Polynomial.C (α n)⁻¹ * Polynomial.X))
      ⟨mk fun k ↦ (p : ℂ_[p]) ^ (k ^ 2),
        IsEntire.mem_subring.mpr (isEntire_mk_pow_sq (PadicComplex.norm_p_lt_one p))⟩ := by
  let F : ℂ_[p]⟦X⟧ := mk fun k ↦ (p : ℂ_[p]) ^ (k ^ 2)
  have hF : F.IsEntire := isEntire_mk_pow_sq (PadicComplex.norm_p_lt_one p)
  have hF0 : constantCoeff F = 1 := by simp [F]
  have hinj : Function.Injective α := fun m n hmn ↦ by
    have hv : (-((2 * m + 1 : ℕ) : ℚ)) = -((2 * n + 1 : ℕ) : ℚ) :=
      WithTop.coe_eq_coe.mp ((hval m).symm.trans (hmn ▸ hval n))
    have hnat : 2 * m + 1 = 2 * n + 1 := Nat.cast_inj.mp (neg_inj.mp hv)
    omega
  refine hF.hasProd_polynomialHom_one_sub_C_inv_mul_X hF0 fun y ↦ ?_
  symm
  by_cases hy : F.evalAt y = 0
  · obtain ⟨n, hyn_val⟩ := exists_addValuation_eq_neg_odd_of_evalAt_mk_padicComplex_pow_sq_eq_zero
      p hy
    have hyn : α n = y := (existsUnique_zero_mk_padicComplex_pow_sq p n).unique
      ⟨hval n, hz n⟩ ⟨hyn_val, hy⟩
    have hset : {m : ℕ | α m = y} = {n} := by
      ext m
      exact ⟨fun hm ↦ hinj (hm.trans hyn.symm), fun hm ↦ hm ▸ hyn⟩
    rw [order_taylor_zero_mk_padicComplex_pow_sq p hy, hset, Set.encard_singleton]
  · have hord0 : (_root_.PowerSeries.taylor y F).order = 0 :=
      not_not.mp (order_ne_zero_iff_constCoeff_eq_zero.not.mpr (by rwa [constantCoeff_taylor]))
    have hset : {m : ℕ | α m = y} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      exact fun m hm ↦ hy (hm ▸ hz m)
    rw [hord0, hset, Set.encard_empty]

/-- **Product identity `∑ p^(k²) X^k = ∏' n : ℕ, (1 - (α n)⁻¹ X)` over `ℂ_[p]`.** -/
theorem eq_tprod_mk_padicComplex_pow_sq {α : ℕ → ℂ_[p]}
    (hval : ∀ n : ℕ, PadicComplex.addValuation p (α n) = ↑(-((2 * n + 1 : ℕ) : ℚ)))
    (hz : ∀ n : ℕ, (mk fun k ↦ (p : ℂ_[p]) ^ (k ^ 2)).evalAt (α n) = 0) :
    (mk fun k ↦ (p : ℂ_[p]) ^ (k ^ 2)) =
      ((∏' n : ℕ, IsEntire.polynomialHom (1 - Polynomial.C (α n)⁻¹ * Polynomial.X) :
        IsEntire.subring ℂ_[p]) : ℂ_[p]⟦X⟧) :=
  (congrArg Subtype.val (hasProd_mk_padicComplex_pow_sq p hval hz).tprod_eq).symm

end PadicQuadraticSeries

end TauCeti.PowerSeries
