/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.ZeroCount
public import TauCeti.NumberTheory.Padics.Complex.Basic
public import TauCeti.NumberTheory.Padics.Complex.Valuation
public import TauCeti.NumberTheory.Padics.LogGauge
public import TauCeti.RingTheory.PowerSeries.Entire.WeierstrassProduct
import Mathlib.Order.Northcott

/-!
# Newton polygons of entire Weierstrass products

Let `K` be a complete ultrametric normed field whose norm comes from a real additive valuation `v`
with base `b > 1`, so `‖x‖ = b ^ (-(v x).untop₀)` for `x ≠ 0`. Let `a : ι → K` be a family of
nonzero elements with `‖a i‖ → ∞` along the cofinite filter, and let `W` be the unconditional
entire Weierstrass product

```text
W = ∏' i, (1 - (a i)⁻¹ X)
```

in `PowerSeries.IsEntire.subring K`. At every real slope `σ`, splitting `W` at the closed disc of
radius `b ^ σ` gives its normalised disc preparation `W = P_s * U` where `P_s` is the finite product
over `‖a i‖ ≤ b ^ σ`, which splits over `K` into linear factors without assuming `K` to be
algebraically closed. Consequently the finite Newton face of `W` of slope `σ` runs from
`{i | ‖a i‖ < b ^ σ}.ncard` to `{i | ‖a i‖ ≤ b ^ σ}.ncard`, and the multiplicity of the slope `σ`
in the Newton polygon of `W` is `{i | ‖a i‖ = b ^ σ}.ncard`, equivalently
`{i | v (a i) = -σ}.ncard`.

As an explicit entire nonpolynomial check, for any element `a` with finite nonnegative valuation
`v a = c`, the quadratic-exponent series `∑ a^(n²) Xⁿ` has convex coefficient heights `c * n ^ 2`,
so its Newton polygon is `n ↦ c * n ^ 2` with unit slopes `c * (2 * n + 1)`. When `a = p`, the
series `∑ p^(n²) Xⁿ` over `ℚ_[p]` and `ℂ_[p]` is entire with odd slopes `1, 3, 5, …` each of
multiplicity `1`, has a unique simple zero `αₙ ∈ ℂ_[p]` of valuation `-(2 * n + 1)` for every
`n : ℕ` and no other zeros in `ℂ_[p]`, and equals the unconditional Weierstrass product
`∏' n : ℕ, (1 - αₙ⁻¹ X)` in `PowerSeries.IsEntire.subring ℂ_[p]`.

## Main results

* `TauCeti.PowerSeries.IsEntire.isFiniteFace_newtonPolygon_of_hasProd`,
  `TauCeti.PowerSeries.IsEntire.newtonSlopeMultiplicity_of_hasProd` and
  `TauCeti.PowerSeries.IsEntire.newtonSlopeMultiplicity_eq_ncard_addValuation_of_hasProd`: the
  finite faces and slope multiplicities of an entire Weierstrass product, without assuming `K` to be
  algebraically closed.
* `PowerSeries.newtonPolygon_mk_pow_sq`, `PowerSeries.unitSlope_newtonPolygon_mk_pow_sq` and
  `PowerSeries.newtonSlopeMultiplicity_mk_pow_sq_mul`: the Newton polygon and slopes of
  `∑ a^(n²) Xⁿ`.
* `TauCeti.PowerSeries.existsUnique_zero_mk_padicComplex_pow_sq`,
  `TauCeti.PowerSeries.order_taylor_zero_mk_padicComplex_pow_sq`,
  `TauCeti.PowerSeries.exists_addValuation_eq_neg_odd_of_evalAt_mk_padicComplex_pow_sq_eq_zero` and
  `TauCeti.PowerSeries.hasProd_mk_padicComplex_pow_sq`: the zeros and entire Weierstrass product of
  `∑ p^(n²) Xⁿ` over `ℂ_[p]`.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §§1, 4.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
-/

public section

open Filter
open scoped Topology

namespace TauCeti.PowerSeries.IsEntire

open _root_.PowerSeries

section WeierstrassSlopes

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- **Finite Newton faces of an entire Weierstrass product.** Let `a : ι → K` be a family of nonzero
elements with `‖a i‖ → ∞` cofinitely, and let `W` be the product of `1 - (a i)⁻¹ X` in
`PowerSeries.IsEntire.subring K`. For every real slope `σ`, the Newton polygon of `W` has a finite
face of slope `σ` from `{i | ‖a i‖ < b ^ σ}.ncard` to `{i | ‖a i‖ ≤ b ^ σ}.ncard`. No
algebraic-closure hypothesis on `K` is needed. -/
theorem isFiniteFace_newtonPolygon_of_hasProd {ι : Type*} {a : ι → K} {W : IsEntire.subring K}
    (ha0 : ∀ i, a i ≠ 0) (ha : Tendsto (fun i ↦ ‖a i‖) cofinite atTop)
    (hW : HasProd (fun i ↦ IsEntire.polynomialHom
      (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)) W)
    (σ : ℝ) :
    IsFiniteFace ((W : K⟦X⟧).newtonPolygon v) σ
      {i : ι | ‖a i‖ < b ^ σ}.ncard {i : ι | ‖a i‖ ≤ b ^ σ}.ncard := by
  classical
  let r : ℝ := b ^ σ
  have hr : 0 < r := Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ
  have hfin : {i : ι | ‖a i‖ ≤ r}.Finite := ((northcott_iff_tendsto _).mpr ha).finite_le r
  let s : Finset ι := hfin.toFinset
  have hs (i : ι) : ‖a i‖ ≤ r ↔ i ∈ s := hfin.mem_toFinset.symm
  obtain ⟨U, -, hprep⟩ := exists_isEntire_isDiscPreparation_of_hasProd ha0 ha hW hr hs
  let P : Polynomial K := ∏ i ∈ s, (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)
  have hW_ent : (W : K⟦X⟧).IsEntire := IsEntire.mem_subring.mp W.2
  have hW_ne : (W : K⟦X⟧) ≠ 0 := ne_zero_of_hasProd_one_sub_C_inv_mul_X hW
  obtain ⟨l, u, hface⟩ := hW_ent.exists_isFiniteFace_newtonPolygon v hb hv hW_ne σ
  obtain ⟨-, hu_dist⟩ := isLowestDominant_and_isDistinguished_of_isFiniteFace_newtonPolygon
    (W : K⟦X⟧) v hb hv (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted (hW_ent.isRestricted r))
    hface
  have hu_eq : u = s.card := hu_dist.unique hprep.isDistinguished
  have hroots : P.roots = s.val.map a := by
    have hz1 := hprep.zeroMultiset_eq_roots_map (L := K) hr
    have hz2 := zeroMultiset_of_hasProd (L := K) ha0 ha hW hr hs
    simpa [P] using hz1.symm.trans hz2
  have hsplits : P.Splits := Polynomial.splits_iff_card_roots.mpr (by
    rw [hroots, Multiset.card_map, ← Finset.card_def, hprep.natDegree_eq])
  let u_sub : IsRestricted.subring (R := K) r := ⟨U, hprep.isRestricted⟩
  have hmul : (u_sub : K⟦X⟧) * (P : K⟦X⟧) = (W : K⟦X⟧) := by
    change U * (P : K⟦X⟧) = (W : K⟦X⟧)
    rw [mul_comm, ← hprep.eq_mul]
  have hl_eq : l = {i : ι | ‖a i‖ < r}.ncard := by
    have hlt := card_filter_roots_norm_lt_of_isUnit_mul v hb hv (hW_ent.isRestricted r) hface
      (hprep.isUnit hr) (hprep.natDegree_eq.trans hu_eq.symm).le hmul hsplits
    rw [← hlt, hroots]
    have hset : {i : ι | ‖a i‖ < r} = ↑(s.filter fun i ↦ ‖a i‖ < r) := by
      ext i
      simp only [Set.mem_ofPred_eq, Finset.coe_filter, ← hs]
      exact ⟨fun hi ↦ ⟨hi.le, hi⟩, fun hi ↦ hi.2⟩
    rw [hset, Set.ncard_coe_finset, Finset.card_def, Finset.filter_val, Multiset.filter_map,
      Multiset.card_map]
    rfl
  have hs_ncard : s.card = {i : ι | ‖a i‖ ≤ r}.ncard := by
    have hset : {i : ι | ‖a i‖ ≤ r} = (s : Set ι) := by
      ext i
      exact hs i
    rw [hset, Set.ncard_coe_finset]
  rwa [hl_eq, hu_eq, hs_ncard] at hface

/-- **Slope multiplicities of an entire Weierstrass product.** Let `a : ι → K` be a family of
nonzero elements with `‖a i‖ → ∞` cofinitely, and let `W` be the product of `1 - (a i)⁻¹ X` in
`PowerSeries.IsEntire.subring K`. For every real `σ`, the multiplicity of the slope `σ` in the
Newton polygon of `W` is `{i | ‖a i‖ = b ^ σ}.ncard`, without assuming `K` to be algebraically
closed. -/
theorem newtonSlopeMultiplicity_of_hasProd {ι : Type*} {a : ι → K} {W : IsEntire.subring K}
    (ha0 : ∀ i, a i ≠ 0) (ha : Tendsto (fun i ↦ ‖a i‖) cofinite atTop)
    (hW : HasProd (fun i ↦ IsEntire.polynomialHom
      (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)) W)
    (σ : ℝ) :
    (W : K⟦X⟧).newtonSlopeMultiplicity v σ = {i : ι | ‖a i‖ = b ^ σ}.ncard := by
  have hface := isFiniteFace_newtonPolygon_of_hasProd v hb hv ha0 ha hW σ
  rw [newtonSlopeMultiplicity_eq_of_isFiniteFace hface]
  have hfin_le : {i : ι | ‖a i‖ ≤ b ^ σ}.Finite :=
    ((northcott_iff_tendsto _).mpr ha).finite_le (b ^ σ)
  have hfin_lt : {i : ι | ‖a i‖ < b ^ σ}.Finite :=
    hfin_le.subset fun i (hi : ‖a i‖ < b ^ σ) ↦ hi.le
  have hfin_eq : {i : ι | ‖a i‖ = b ^ σ}.Finite :=
    hfin_le.subset fun i (hi : ‖a i‖ = b ^ σ) ↦ hi.le
  have hunion : {i : ι | ‖a i‖ ≤ b ^ σ} =
      {i : ι | ‖a i‖ < b ^ σ} ∪ {i : ι | ‖a i‖ = b ^ σ} := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    exact le_iff_lt_or_eq
  have hdisj : Disjoint {i : ι | ‖a i‖ < b ^ σ} {i : ι | ‖a i‖ = b ^ σ} :=
    Set.disjoint_left.mpr fun _ hlt heq ↦ hlt.ne heq
  rw [hunion, Set.ncard_union_eq hdisj hfin_lt hfin_eq, Nat.add_sub_cancel_left]

/-- **Slope multiplicities of an entire Weierstrass product, valuation form.** The multiplicity of
each real slope `σ` in the Newton polygon of `W = ∏ (1 - (a i)⁻¹ X)` is the number of indices `i`
with `v (a i) = -σ`. -/
theorem newtonSlopeMultiplicity_eq_ncard_addValuation_of_hasProd {ι : Type*} {a : ι → K}
    {W : IsEntire.subring K} (ha0 : ∀ i, a i ≠ 0)
    (ha : Tendsto (fun i ↦ ‖a i‖) cofinite atTop)
    (hW : HasProd (fun i ↦ IsEntire.polynomialHom
      (1 - Polynomial.C (a i)⁻¹ * Polynomial.X)) W)
    (σ : ℝ) :
    (W : K⟦X⟧).newtonSlopeMultiplicity v σ =
      {i : ι | v (a i) = ((-σ : ℝ) : WithTop ℝ)}.ncard := by
  rw [newtonSlopeMultiplicity_of_hasProd v hb hv ha0 ha hW σ]
  congr 1
  ext i
  have hne_top : v (a i) ≠ ⊤ := (v.ne_top_iff).mpr (ha0 i)
  simp only [Set.mem_ofPred_eq]
  rw [hv (a i) (ha0 i), Real.rpow_right_inj (zero_lt_one.trans hb) hb.ne',
    ← WithTop.coe_untop₀_of_ne_top hne_top, WithTop.coe_eq_coe, WithTop.untop₀_coe]
  exact ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩

/-- **Slope multiplicities of `∏' i, (1 - (a i)⁻¹ X)`.** -/
theorem newtonSlopeMultiplicity_tprod_one_sub_C_inv_mul_X {ι : Type*} {a : ι → K}
    (ha0 : ∀ i, a i ≠ 0) (ha : Tendsto (fun i ↦ ‖a i‖) cofinite atTop) (σ : ℝ) :
    (((∏' i, IsEntire.polynomialHom (1 - Polynomial.C (a i)⁻¹ * Polynomial.X) :
      IsEntire.subring K) : K⟦X⟧)).newtonSlopeMultiplicity v σ =
      {i : ι | ‖a i‖ = b ^ σ}.ncard :=
  newtonSlopeMultiplicity_of_hasProd v hb hv ha0 ha
    (multipliable_polynomialHom_one_sub_C_inv_mul_X ha).hasProd σ

end WeierstrassSlopes

end TauCeti.PowerSeries.IsEntire

namespace PowerSeries

open TauCeti

section QuadraticPowerSeries

variable {R : Type*} [CommRing R] {v : AddValuation R (WithTop ℝ)} {a : R} {c : ℝ}

/-- When `v a = c ≥ 0`, the quadratic-exponent power series `∑ a^(n²) Xⁿ` has convex coefficient
heights `n ↦ c * n ^ 2`, so its Newton polygon equals `n ↦ c * n ^ 2`. -/
theorem newtonPolygon_mk_pow_sq (hc : 0 ≤ c) (ha : v a = (c : WithTop ℝ)) :
    (mk fun n ↦ a ^ (n ^ 2)).newtonPolygon v =
      fun n : ℕ ↦ ((c * (n : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by
  have hcoeff : (fun n : ℕ ↦ v (coeff n (mk fun k ↦ a ^ (k ^ 2)))) =
      fun n : ℕ ↦ ((c * (n : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by
    ext n
    rw [coeff_mk, AddValuation.map_pow, ha, ← WithTop.coe_nsmul, nsmul_eq_mul, Nat.cast_pow,
      mul_comm]
  have hconv : IsConvexSeq (fun n : ℕ ↦ ((c * (n : ℝ) ^ 2 : ℝ) : WithTop ℝ)) := by
    refine isConvexSeq_iff_two_mul_le.mpr ⟨⟨fun _ _ _ _ _ _ ↦ WithTop.coe_ne_top⟩,
      fun n _ _ ↦ ?_⟩
    simp only [WithTop.untop₀_coe, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    nlinarith
  rw [newtonPolygon_def, hcoeff, hconv.lowerConvexEnvelope_eq]

/-- When `v a = c ≥ 0`, every index is a finite unit edge of the Newton polygon of
`∑ a^(n²) Xⁿ`. -/
theorem finiteEdges_newtonPolygon_mk_pow_sq (hc : 0 ≤ c) (ha : v a = (c : WithTop ℝ)) :
    finiteEdges ((mk fun n ↦ a ^ (n ^ 2)).newtonPolygon v) = Set.univ := by
  ext n
  rw [mem_finiteEdges, newtonPolygon_mk_pow_sq hc ha]
  simp only [Set.mem_univ, iff_true]
  exact ⟨WithTop.coe_ne_top, WithTop.coe_ne_top⟩

/-- When `v a = c ≥ 0`, the `n`-th unit slope of `∑ a^(n²) Xⁿ` is `c * (2 * n + 1)`. -/
theorem unitSlope_newtonPolygon_mk_pow_sq (hc : 0 ≤ c) (ha : v a = (c : WithTop ℝ)) (n : ℕ) :
    unitSlope ((mk fun k ↦ a ^ (k ^ 2)).newtonPolygon v) n = c * (2 * (n : ℝ) + 1) := by
  rw [unitSlope_def, newtonPolygon_mk_pow_sq hc ha]
  simp only [WithTop.untop₀_coe, Nat.cast_add, Nat.cast_one]
  ring

/-- When `v a = c > 0`, each slope `c * (2 * n + 1)` of `∑ a^(n²) Xⁿ` has multiplicity `1`. -/
theorem newtonSlopeMultiplicity_mk_pow_sq_mul (hc : 0 < c) (ha : v a = (c : WithTop ℝ)) (n : ℕ) :
    (mk fun k ↦ a ^ (k ^ 2)).newtonSlopeMultiplicity v (c * (2 * (n : ℝ) + 1)) = 1 := by
  have hset : {m | m ∈ finiteEdges ((mk fun k ↦ a ^ (k ^ 2)).newtonPolygon v) ∧
      unitSlope ((mk fun k ↦ a ^ (k ^ 2)).newtonPolygon v) m = c * (2 * (n : ℝ) + 1)} = {n} := by
    ext m
    rw [Set.mem_ofPred_eq, Set.mem_singleton_iff, finiteEdges_newtonPolygon_mk_pow_sq hc.le ha,
      unitSlope_newtonPolygon_mk_pow_sq hc.le ha]
    simp only [Set.mem_univ, true_and, mul_eq_mul_left_iff, hc.ne', or_false]
    exact ⟨fun h ↦ by exact_mod_cast (by linarith : (m : ℝ) = n), fun h ↦ by subst h; rfl⟩
  rw [newtonSlopeMultiplicity_def, hset, Set.ncard_singleton]

/-- When `v a = c ≥ 0`, any real number outside `{c * (2 * n + 1) | n : ℕ}` has multiplicity `0` in
the Newton polygon of `∑ a^(n²) Xⁿ`. -/
theorem newtonSlopeMultiplicity_mk_pow_sq_eq_zero (hc : 0 ≤ c) (ha : v a = (c : WithTop ℝ))
    {σ : ℝ} (hσ : σ ∉ Set.range fun n : ℕ ↦ c * (2 * (n : ℝ) + 1)) :
    (mk fun k ↦ a ^ (k ^ 2)).newtonSlopeMultiplicity v σ = 0 := by
  rw [newtonSlopeMultiplicity_def]
  have hset : {m | m ∈ finiteEdges ((mk fun k ↦ a ^ (k ^ 2)).newtonPolygon v) ∧
      unitSlope ((mk fun k ↦ a ^ (k ^ 2)).newtonPolygon v) m = σ} = ∅ := by
    ext m
    rw [Set.mem_ofPred_eq, finiteEdges_newtonPolygon_mk_pow_sq hc ha,
      unitSlope_newtonPolygon_mk_pow_sq hc ha]
    simp only [Set.mem_univ, true_and, Set.mem_empty_iff_false, iff_false]
    exact fun h ↦ hσ ⟨m, h⟩
  rw [hset, Set.ncard_empty]

end QuadraticPowerSeries

end PowerSeries

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
  refine hF.hasProd_polynomialHom_of_order_taylor_eq hF0 fun y ↦ ?_
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
