/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Entire.Factorization
import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.RingTheory.Polynomial.Roots

/-!
# Canonical Weierstrass products of entire power series

Over a complete ultrametric normed commutative ring `R`, a family `c : ι → R` defines a convergent
unconditional infinite product

```text
∏' i, (1 - cᵢ X)
```

in the Gauss topology of `PowerSeries.IsEntire.subring R` if and only if `c` tends to `0` along the
cofinite filter; the forward implication needs no completeness hypothesis on `R`, since the
degree-`1` coefficients of the finite partial products recover `- ∑ cᵢ`.

Specialising to a complete ultrametric normed field `K` and a family `α : ι → K` with `‖α i‖ → ∞`
cofinitely yields the canonical Weierstrass product `∏' i, (1 - αᵢ⁻¹ X)`. When every `α i` is
nonzero, splitting this product at the finite set `s` of indices with `‖α i‖ ≤ r` exhibits its
normalised Weierstrass preparation `TauCeti.PowerSeries.IsDiscPreparation` on every closed disc of
radius `r ≥ 0`: the polynomial factor is `∏_{i ∈ s} (1 - αᵢ⁻¹ X)` of degree `s.card`, and the
remaining tail product is restricted at `r` with Gauss distance strictly below `1` from `1`. In
consequence, in every complete normed field extension `L` of `K`, the multiplicity of each `x ∈ L`
as a zero of the infinite product is the number of indices `i` with `algebraMap K L (α i) = x`, the
zero multiset on `{x ∈ L : ‖x‖ ≤ r}` is the multiset image of `s`, and the zeros in `L` are
precisely the images of the `α i`.

Conversely, over an algebraically closed complete ultrametric normed field `K`, every entire power
series `f` with constant coefficient `1` is the unconditional `HasProd` of the factors `1 - αᵢ⁻¹ X`
along any family `α : ι → K` listing each zero of `f` as many times as its multiplicity, and admits
a countable such indexing. This upgrades the radius-filtered disc-subproduct convergence of
`PowerSeries.IsEntire.tendsto_polynomialHom_prod_zeroMultiset` to an enumeration-independent
unconditional infinite product in `PowerSeries.IsEntire.subring K`.

## Main results

* `TauCeti.PowerSeries.IsEntire.multipliable_polynomialHom_one_sub_C_mul_X_iff` (with
  `tendsto_cofinite_zero_of_multipliable_polynomialHom_one_sub_C_mul_X` and
  `multipliable_polynomialHom_one_sub_C_mul_X_of_tendsto_cofinite_zero`): unconditional
  convergence of `∏' i, (1 - cᵢ X)` in `PowerSeries.IsEntire.subring R` iff `c → 0` cofinitely.
* `TauCeti.PowerSeries.IsEntire.constantCoeff_tprod_polynomialHom_one_sub_C_mul_X`: the constant
  coefficient of `∏' i, (1 - cᵢ X)` is `1`.
* `TauCeti.PowerSeries.IsEntire.multipliable_polynomialHom_one_sub_C_inv_mul_X` and
  `TauCeti.PowerSeries.IsEntire.multipliable_polynomialHom_one_sub_C_inv_mul_X_iff`: unconditional
  convergence of `∏' i, (1 - αᵢ⁻¹ X)` from `‖α i‖ → ∞` cofinitely.
* `TauCeti.PowerSeries.IsEntire.isDiscPreparation_tprod_polynomialHom_one_sub_C_inv_mul_X`:
  splitting `∏' i, (1 - αᵢ⁻¹ X)` at `‖α i‖ ≤ r` gives its normalised Weierstrass disc preparation
  at every radius `r ≥ 0`.
* `TauCeti.PowerSeries.IsEntire.order_taylor_tprod_polynomialHom_one_sub_C_inv_mul_X`,
  `TauCeti.PowerSeries.IsEntire.zeroMultiset_tprod_polynomialHom_one_sub_C_inv_mul_X` and
  `TauCeti.PowerSeries.IsEntire.evalAt_tprod_polynomialHom_one_sub_C_inv_mul_X_eq_zero_iff`:
  Taylor-order multiplicities, closed-disc zero multisets, and zeros of the canonical product in
  every complete normed field extension.
* `PowerSeries.IsEntire.hasProd_polynomialHom_one_sub_C_inv_mul_X` and
  `PowerSeries.IsEntire.exists_countable_hasProd_polynomialHom_one_sub_C_inv_mul_X`: over an
  algebraically closed complete ultrametric field, every entire series with constant coefficient `1`
  is the unconditional `HasProd` over any multiplicity-accurate enumeration of its zeros, and admits
  a countable such enumeration.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §4, in particular (4.13).
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Chapter IV §4.
-/

public section

open Filter
open scoped Topology PowerSeries

namespace TauCeti.PowerSeries.IsEntire

local instance instFactRadiusPos (r : Set.Ioi (0 : ℝ)) : Fact (0 < (r : ℝ)) := ⟨r.2⟩

section NormedCommRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- The norm on the closed disc of positive radius `r` of the linear monomial `c X` is at most
`‖c‖ * r`. -/
private theorem norm_restrict_polynomialHom_C_mul_X_le (r : Set.Ioi (0 : ℝ)) (c : R) :
    ‖restrict r (_root_.PowerSeries.IsEntire.polynomialHom (Polynomial.C c * Polynomial.X))‖ ≤
      ‖c‖ * (r : ℝ) := by
  refine TauCeti.PowerSeries.norm_le_iff.mpr fun m ↦ ?_
  rw [coe_restrict, _root_.PowerSeries.IsEntire.coe_polynomialHom, Polynomial.coeff_coe]
  rcases eq_or_ne m 1 with rfl | hm
  · simp
  · have h0 : (Polynomial.C c * Polynomial.X).coeff m = 0 := by
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X, hm.symm]
    rw [h0, norm_zero, zero_mul]
    exact mul_nonneg (norm_nonneg c) r.2.le

/-- **Necessary condition for multipliability of `1 - cᵢ X`.** Over an ultrametric normed
commutative ring, if the linear factors `1 - cᵢ X` are unconditionally multipliable in the Gauss
topology of entire series, then `c` tends to `0` along the cofinite filter. Neither completeness nor
multiplicativity of the norm is needed: multiplying any constant-one partial product by `1 - cᵢ X`
changes its degree-`1` coefficient by `-cᵢ`. -/
theorem tendsto_cofinite_zero_of_multipliable_polynomialHom_one_sub_C_mul_X {ι : Type*}
    {c : ι → R} (hm : Multipliable fun i ↦
      _root_.PowerSeries.IsEntire.polynomialHom (1 - Polynomial.C (c i) * Polynomial.X)) :
    Tendsto c cofinite (𝓝 0) := by
  classical
  set g : ι → _root_.PowerSeries.IsEntire.subring R := fun i ↦
    _root_.PowerSeries.IsEntire.polynomialHom (1 - Polynomial.C (c i) * Polynomial.X)
  set a : Finset ι → R := fun s ↦
    _root_.PowerSeries.coeff 1 ((∏ j ∈ s, g j : _root_.PowerSeries.IsEntire.subring R) : R⟦X⟧)
  have hstep : ∀ (s : Finset ι) {i : ι}, i ∉ s → a s - a (insert i s) = c i := by
    intro s i hi
    dsimp only [a]
    set F : R⟦X⟧ := ((∏ j ∈ s, g j : _root_.PowerSeries.IsEntire.subring R) : R⟦X⟧)
    have hF0 : _root_.PowerSeries.coeff 0 F = 1 := by
      rw [_root_.PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp [F, g, map_prod]
    have hins : ((∏ j ∈ insert i s, g j : _root_.PowerSeries.IsEntire.subring R) : R⟦X⟧) =
        F - _root_.PowerSeries.C (c i) * (_root_.PowerSeries.X * F) := by
      rw [Finset.prod_insert hi, Subring.coe_mul]
      simp only [g, _root_.PowerSeries.IsEntire.coe_polynomialHom, Polynomial.coe_sub,
        Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X]
      ring
    simp only [hins, map_sub, _root_.PowerSeries.coeff_C_mul,
      _root_.PowerSeries.coeff_succ_X_mul 0, hF0, mul_one, sub_sub_cancel]
  set L : R :=
    _root_.PowerSeries.coeff 1 ((∏' j, g j : _root_.PowerSeries.IsEntire.subring R) : R⟦X⟧)
  have ha : Tendsto a atTop (𝓝 L) :=
    ((uniformContinuous_coeff (R := R) 1).continuous.tendsto _).comp hm.hasProd
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ eventually_cofinite.mpr ?_
  obtain ⟨s₀, hs₀⟩ := Filter.mem_atTop_sets.mp (ha (Metric.ball_mem_nhds L (half_pos hε)))
  refine s₀.finite_toSet.subset fun i hi ↦ ?_
  by_contra his₀
  have h1 : dist (a s₀) L < ε / 2 := Metric.mem_ball.mp (hs₀ s₀ le_rfl)
  have h2 : dist (a (insert i s₀)) L < ε / 2 :=
    Metric.mem_ball.mp (hs₀ (insert i s₀) (Finset.subset_insert i s₀))
  have hci : dist (c i) 0 < ε := by
    rw [dist_zero_right, ← hstep s₀ his₀, ← dist_eq_norm]
    exact (dist_triangle_right _ _ L).trans_lt ((add_lt_add h1 h2).trans_eq (add_halves ε))
  exact hi hci

/-- **Sufficient condition for multipliability of `1 - cᵢ X`.** Over a complete ultrametric normed
commutative ring, if `c` tends to `0` along the cofinite filter, then the linear factors `1 - cᵢ X`
are unconditionally multipliable in `PowerSeries.IsEntire.subring R`. -/
theorem multipliable_polynomialHom_one_sub_C_mul_X_of_tendsto_cofinite_zero [CompleteSpace R]
    {ι : Type*} {c : ι → R} (hc : Tendsto c cofinite (𝓝 0)) :
    Multipliable fun i ↦
      _root_.PowerSeries.IsEntire.polynomialHom (1 - Polynomial.C (c i) * Polynomial.X) := by
  refine multipliable_iff.mpr fun r ↦ ?_
  have heq : (fun i ↦ restrict r (_root_.PowerSeries.IsEntire.polynomialHom
      (1 - Polynomial.C (c i) * Polynomial.X))) =
      fun i ↦ 1 - restrict r (_root_.PowerSeries.IsEntire.polynomialHom
        (Polynomial.C (c i) * Polynomial.X)) := by
    ext i
    rw [map_sub, map_one, map_sub, map_one]
  rw [heq]
  refine IsUltrametricDist.multipliable_one_sub_of_tendsto_cofinite_zero ?_
  refine squeeze_zero_norm (fun i ↦ norm_restrict_polynomialHom_C_mul_X_le r (c i)) ?_
  simpa using hc.norm.mul_const (r : ℝ)

/-- **Multipliability criterion for canonical linear factors.** Over a complete ultrametric normed
commutative ring, `∏' i, (1 - cᵢ X)` converges unconditionally in the Gauss topology of entire
series if and only if `c` tends to `0` along the cofinite filter. -/
theorem multipliable_polynomialHom_one_sub_C_mul_X_iff [CompleteSpace R] {ι : Type*}
    {c : ι → R} :
    Multipliable (fun i ↦
      _root_.PowerSeries.IsEntire.polynomialHom (1 - Polynomial.C (c i) * Polynomial.X)) ↔
      Tendsto c cofinite (𝓝 0) :=
  ⟨tendsto_cofinite_zero_of_multipliable_polynomialHom_one_sub_C_mul_X,
    multipliable_polynomialHom_one_sub_C_mul_X_of_tendsto_cofinite_zero⟩

/-- The infinite product `∏' i, (1 - cᵢ X)` in `PowerSeries.IsEntire.subring R` always has constant
coefficient `1` (both when it converges and, through the `tprod` default `1`, when it does not). -/
theorem constantCoeff_tprod_polynomialHom_one_sub_C_mul_X {ι : Type*} (c : ι → R) :
    _root_.PowerSeries.constantCoeff
      ((∏' i, _root_.PowerSeries.IsEntire.polynomialHom
        (1 - Polynomial.C (c i) * Polynomial.X) :
          _root_.PowerSeries.IsEntire.subring R) : R⟦X⟧) = 1 := by
  by_cases hm : Multipliable fun i ↦
      _root_.PowerSeries.IsEntire.polynomialHom (1 - Polynomial.C (c i) * Polynomial.X)
  · rw [constantCoeff_tprod hm]
    simp
  · rw [tprod_eq_one_of_not_multipliable hm]
    simp

/-- When every `cᵢ` satisfies `‖cᵢ‖ * r < 1` (`r > 0`) and `c → 0` cofinitely, the infinite product
`∏' i, (1 - cᵢ X)` is within `< 1` of `1` in the Gauss norm at radius `r`. -/
private theorem gaussNorm_tprod_polynomialHom_one_sub_C_mul_X_sub_one_lt [CompleteSpace R]
    {ι : Type*} {c : ι → R} (hc : Tendsto c cofinite (𝓝 0)) (r : Set.Ioi (0 : ℝ))
    (hlt : ∀ i, ‖c i‖ * (r : ℝ) < 1) :
    (((∏' i, _root_.PowerSeries.IsEntire.polynomialHom
      (1 - Polynomial.C (c i) * Polynomial.X) :
        _root_.PowerSeries.IsEntire.subring R) : R⟦X⟧) - 1).gaussNorm norm (r : ℝ) < 1 := by
  set g : ι → _root_.PowerSeries.IsEntire.subring R := fun i ↦
    _root_.PowerSeries.IsEntire.polynomialHom (1 - Polynomial.C (c i) * Polynomial.X)
  have hm : Multipliable g := multipliable_polynomialHom_one_sub_C_mul_X_of_tendsto_cofinite_zero hc
  have hnorm : ‖(∏' i, restrict r (g i)) - 1‖ =
      (((∏' i, g i : _root_.PowerSeries.IsEntire.subring R) : R⟦X⟧) - 1).gaussNorm norm
        (r : ℝ) := by
    rw [← restrict_tprod hm r, ← map_one (restrict r), ← map_sub,
      TauCeti.PowerSeries.norm_eq_gaussNorm, coe_restrict, AddSubgroupClass.coe_sub,
      OneMemClass.coe_one]
  rw [← hnorm]
  refine TauCeti.norm_tprod_sub_one_lt _ zero_lt_one le_rfl fun i ↦ ?_
  have hsub : restrict r (g i) - 1 =
      -restrict r (_root_.PowerSeries.IsEntire.polynomialHom
        (Polynomial.C (c i) * Polynomial.X)) := by simp [g, sub_eq_add_neg]
  rw [hsub, norm_neg]
  exact (norm_restrict_polynomialHom_C_mul_X_le r (c i)).trans_lt (hlt i)

end NormedCommRing

section NormedField

universe u
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

omit [IsUltrametricDist K] in
/-- Over a field, a finite product of factors `1 - αᵢ⁻¹ X` with nonzero `αᵢ` is a nonzero scalar
multiple of `∏ (X - αᵢ)`. -/
private theorem prod_one_sub_C_inv_mul_X_eq {ι : Type*} (s : Finset ι) {α : ι → K}
    (hα0 : ∀ i ∈ s, α i ≠ 0) :
    ∏ i ∈ s, (1 - Polynomial.C (α i)⁻¹ * Polynomial.X) =
      Polynomial.C (∏ i ∈ s, (-α i)⁻¹) * ∏ i ∈ s, (Polynomial.X - Polynomial.C (α i)) := by
  have hfac : ∀ i ∈ s, 1 - Polynomial.C (α i)⁻¹ * Polynomial.X =
      Polynomial.C (-α i)⁻¹ * (Polynomial.X - Polynomial.C (α i)) := fun i hi ↦ by
    simp [mul_sub, ← Polynomial.C_mul, hα0 i hi, inv_neg, neg_add_eq_sub]
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, map_prod]

omit [IsUltrametricDist K] in
/-- At radius `0`, any series with constant coefficient `1` is its own normalised disc preparation
in degree `0` with polynomial factor `1`. -/
private theorem isDiscPreparation_zero {f : K⟦X⟧} (hf : f.IsRestricted 0)
    (hf0 : _root_.PowerSeries.constantCoeff f = 1) :
    TauCeti.PowerSeries.IsDiscPreparation 0 0 f 1 f := by
  have hgf : f.gaussNorm norm 0 = 1 := by
    rw [TauCeti.PowerSeries.gaussNorm_eq_of_forall_le (s := 0) fun m ↦ ?_]
    · simp [hf0]
    · rcases eq_or_ne m 0 with rfl | hm
      · rfl
      · simp [zero_pow hm, hf0]
  have hgf1 : (f - 1).gaussNorm norm 0 = 0 := by
    rw [TauCeti.PowerSeries.gaussNorm_eq_of_forall_le (s := 0) fun m ↦ ?_]
    · simp [hf0]
    · rcases eq_or_ne m 0 with rfl | hm
      · rfl
      · simp [zero_pow hm, hf0]
  refine ⟨⟨by simp [hf0, hgf], fun n hn ↦ by simp [zero_pow hn.ne', hgf]⟩,
    Polynomial.natDegree_one, AddMonoidAlgebra.coeff_one_zero, hf, hf0, by linarith, by simp⟩

/-- A finite product of factors `1 - αᵢ⁻¹ X` over nonzero roots `αᵢ` lying in `{‖x‖ ≤ r}` (`r > 0`)
has degree `s.card` and is distinguished of degree `s.card` at `r`. -/
private theorem isDistinguished_prod_one_sub_C_inv_mul_X {ι : Type*} (s : Finset ι) {α : ι → K}
    (hα0 : ∀ i ∈ s, α i ≠ 0) {r : ℝ} (hr0 : 0 < r) (hs : ∀ i ∈ s, ‖α i‖ ≤ r) :
    (∏ i ∈ s, (1 - Polynomial.C (α i)⁻¹ * Polynomial.X)).natDegree = s.card ∧
      TauCeti.PowerSeries.IsDistinguished r s.card
        ((∏ i ∈ s, (1 - Polynomial.C (α i)⁻¹ * Polynomial.X) : Polynomial K) : K⟦X⟧) := by
  classical
  have hc0 : ∏ i ∈ s, (-α i)⁻¹ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi ↦ inv_ne_zero (neg_ne_zero.mpr (hα0 i hi))
  have hPeq := prod_one_sub_C_inv_mul_X_eq s hα0
  have hQmon : ∀ i ∈ s, (Polynomial.X - Polynomial.C (α i)).Monic :=
    fun i _ ↦ Polynomial.monic_X_sub_C (α i)
  refine ⟨?_, ?_⟩
  · rw [hPeq, Polynomial.natDegree_C_mul hc0, Polynomial.natDegree_prod_of_monic _ _ hQmon]
    simp
  · have hQdist : TauCeti.PowerSeries.IsDistinguished r s.card
        ((∏ i ∈ s, (Polynomial.X - Polynomial.C (α i)) : Polynomial K) : K⟦X⟧) := by
      have hcard : ((s.val.map α).filter (‖·‖ ≤ r)).card = s.card := by
        rw [Multiset.filter_eq_self.mpr fun a ha ↦ ?_, Multiset.card_map, Finset.card_val]
        obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp ha
        exact hs i hi
      have hmprod : ((s.val.map α).map fun a ↦ Polynomial.X - Polynomial.C a).prod =
          ∏ i ∈ s, (Polynomial.X - Polynomial.C (α i)) := by
        rw [Finset.prod_eq_multiset_prod, Multiset.map_map, Function.comp_def]
      simpa only [hcard, hmprod] using
        TauCeti.PowerSeries.isDistinguished_multiset_prod_X_sub_C hr0 (s.val.map α)
    rw [hPeq, Polynomial.coe_mul, Polynomial.coe_C, ← zero_add s.card]
    simpa only [_root_.PowerSeries.monomial_zero_eq_C_apply] using
      (TauCeti.PowerSeries.isDistinguished_monomial hr0 hc0 0).mul hQdist hr0 (norm_mul _ _)

/-- **Multipliability of the canonical Weierstrass product.** Over a complete ultrametric normed
field `K`, if `‖α i‖ → ∞` along the cofinite filter, then the canonical factors `1 - αᵢ⁻¹ X` are
unconditionally multipliable in `PowerSeries.IsEntire.subring K`. -/
theorem multipliable_polynomialHom_one_sub_C_inv_mul_X [CompleteSpace K] {ι : Type*}
    {α : ι → K} (hα : Tendsto (fun i ↦ ‖α i‖) cofinite atTop) :
    Multipliable fun i ↦
      _root_.PowerSeries.IsEntire.polynomialHom (1 - Polynomial.C (α i)⁻¹ * Polynomial.X) :=
  multipliable_polynomialHom_one_sub_C_mul_X_of_tendsto_cofinite_zero
    (tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.mp hα))

/-- **Multipliability criterion for nonzero prescribed zeros.** Over a complete ultrametric normed
field `K`, for a family `α : ι → K` of nonzero elements, `∏' i, (1 - αᵢ⁻¹ X)` converges
unconditionally in `PowerSeries.IsEntire.subring K` if and only if `‖α i‖ → ∞` cofinitely. -/
theorem multipliable_polynomialHom_one_sub_C_inv_mul_X_iff [CompleteSpace K] {ι : Type*}
    {α : ι → K} (hα0 : ∀ i, α i ≠ 0) :
    Multipliable (fun i ↦
      _root_.PowerSeries.IsEntire.polynomialHom (1 - Polynomial.C (α i)⁻¹ * Polynomial.X)) ↔
      Tendsto (fun i ↦ ‖α i‖) cofinite atTop := by
  rw [multipliable_polynomialHom_one_sub_C_mul_X_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.mp h)⟩
  have hgt : Tendsto (fun i ↦ ‖(α i)⁻¹‖) cofinite (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by simpa using h.norm) (.of_forall fun i ↦ norm_pos_iff.mpr (inv_ne_zero (hα0 i)))
  simpa only [Pi.inv_def, norm_inv, inv_inv] using hgt.inv_tendsto_nhdsGT_zero

/-- **Normalised Weierstrass disc preparation of the canonical product.** Let `α : ι → K` be a
family of nonzero elements of a complete ultrametric normed field `K` with `‖α i‖ → ∞` cofinitely,
and let `s` be the finite set of indices with `‖α i‖ ≤ r` for a radius `r ≥ 0`. Splitting the
canonical product `∏' i, (1 - αᵢ⁻¹ X)` into the finite polynomial `∏_{i ∈ s} (1 - αᵢ⁻¹ X)` and the
complementary infinite product exhibits its normalised preparation on the closed disc of radius `r`
in degree `s.card`. -/
theorem isDiscPreparation_tprod_polynomialHom_one_sub_C_inv_mul_X [CompleteSpace K] {ι : Type*}
    {α : ι → K} (hα : Tendsto (fun i ↦ ‖α i‖) cofinite atTop) (hα0 : ∀ i, α i ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) {s : Finset ι} (hs : ∀ i, i ∈ s ↔ ‖α i‖ ≤ r) :
    TauCeti.PowerSeries.IsDiscPreparation r s.card
      ((∏' i, _root_.PowerSeries.IsEntire.polynomialHom
        (1 - Polynomial.C (α i)⁻¹ * Polynomial.X) :
          _root_.PowerSeries.IsEntire.subring K) : K⟦X⟧)
      (∏ i ∈ s, (1 - Polynomial.C (α i)⁻¹ * Polynomial.X))
      ((∏' i : ↑((s : Set ι)ᶜ), _root_.PowerSeries.IsEntire.polynomialHom
        (1 - Polynomial.C (α i)⁻¹ * Polynomial.X) :
          _root_.PowerSeries.IsEntire.subring K) : K⟦X⟧) := by
  classical
  let φ : ι → _root_.PowerSeries.IsEntire.subring K := fun i ↦
    _root_.PowerSeries.IsEntire.polynomialHom (1 - Polynomial.C (α i)⁻¹ * Polynomial.X)
  set F : _root_.PowerSeries.IsEntire.subring K := ∏' i, φ i
  set U : _root_.PowerSeries.IsEntire.subring K := ∏' i : ↑((s : Set ι)ᶜ), φ i
  change TauCeti.PowerSeries.IsDiscPreparation r s.card (F : K⟦X⟧)
    (∏ i ∈ s, (1 - Polynomial.C (α i)⁻¹ * Polynomial.X)) (U : K⟦X⟧)
  have hmU : Multipliable (fun j : ↑((s : Set ι)ᶜ) ↦ φ j) :=
    multipliable_polynomialHom_one_sub_C_inv_mul_X
      (hα.comp Subtype.val_injective.tendsto_cofinite)
  have hmul : (F : K⟦X⟧) =
      ((∏ i ∈ s, (1 - Polynomial.C (α i)⁻¹ * Polynomial.X) : Polynomial K) : K⟦X⟧) *
        (U : K⟦X⟧) := by
    have hval := congrArg Subtype.val (((s.hasProd φ).mul_compl hmU.hasProd).tprod_eq)
    rw [Subring.coe_mul, ← map_prod, _root_.PowerSeries.IsEntire.coe_polynomialHom] at hval
    exact hval
  rcases hr.eq_or_lt with rfl | hr0
  · have hs0 : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun i hi ↦
      (norm_pos_iff.mpr (hα0 i)).not_ge ((hs i).mp hi)
    have hUF : (U : K⟦X⟧) = (F : K⟦X⟧) := by simpa [hs0, Polynomial.coe_one] using hmul.symm
    rw [hUF, hs0, Finset.card_empty, Finset.prod_empty]
    exact isDiscPreparation_zero ((_root_.PowerSeries.IsEntire.mem_subring.mp F.2).isRestricted 0)
      (constantCoeff_tprod_polynomialHom_one_sub_C_mul_X _)
  · obtain ⟨hPdeg, hPdist⟩ := isDistinguished_prod_one_sub_C_inv_mul_X s (fun i _ ↦ hα0 i) hr0
      fun i hi ↦ (hs i).mp hi
    have hP0 : (∏ i ∈ s, (1 - Polynomial.C (α i)⁻¹ * Polynomial.X)).coeff 0 = 1 := by
      simp [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
    have hUent : (U : K⟦X⟧).IsEntire := _root_.PowerSeries.IsEntire.mem_subring.mp U.2
    have hcinv : Tendsto (fun j : ↑((s : Set ι)ᶜ) ↦ (α j.1)⁻¹) cofinite (𝓝 0) :=
      (tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.mp hα)).comp
        Subtype.val_injective.tendsto_cofinite
    have hUlt : ((U : K⟦X⟧) - 1).gaussNorm norm r < 1 :=
      gaussNorm_tprod_polynomialHom_one_sub_C_mul_X_sub_one_lt hcinv ⟨r, hr0⟩ fun j ↦ by
        have hj : r < ‖α j.1‖ := lt_of_not_ge (mt (hs j.1).mpr j.2)
        rw [norm_inv, inv_mul_lt_iff₀ (hr0.trans hj), mul_one]
        exact hj
    have hU0 : _root_.PowerSeries.constantCoeff (U : K⟦X⟧) = 1 :=
      constantCoeff_tprod_polynomialHom_one_sub_C_mul_X _
    have hUdist : TauCeti.PowerSeries.IsDistinguished r 0 (U : K⟦X⟧) :=
      (TauCeti.PowerSeries.gaussNorm_sub_one_lt_one_iff hr0 (hUent.isRestricted r) hU0).mp hUlt
    refine ⟨?_, hPdeg, hP0, hUent.isRestricted r, hU0, hUlt, hmul⟩
    rw [hmul, ← add_zero s.card]
    exact hPdist.mul hUdist hr0 (norm_mul _ _)

/-- **Multiplicities of zeros of the canonical product.** Let `α : ι → K` be a family of nonzero
elements of a complete ultrametric normed field `K` with `‖α i‖ → ∞` cofinitely. In every complete
normed field extension `L` of `K`, the multiplicity of any `x ∈ L` as a zero of
`∏' i, (1 - αᵢ⁻¹ X)` (the order of its Taylor translate at `x`) is the cardinality of the fiber
`{i : ι | algebraMap K L (α i) = x}`. -/
theorem order_taylor_tprod_polynomialHom_one_sub_C_inv_mul_X [CompleteSpace K]
    {ι L : Type*} [NormedField L] [NormedAlgebra K L] [CompleteSpace L]
    {α : ι → K} (hα : Tendsto (fun i ↦ ‖α i‖) cofinite atTop) (hα0 : ∀ i, α i ≠ 0) (x : L) :
    (_root_.PowerSeries.taylor x (_root_.PowerSeries.map (algebraMap K L)
      ((∏' i, _root_.PowerSeries.IsEntire.polynomialHom
        (1 - Polynomial.C (α i)⁻¹ * Polynomial.X) :
          _root_.PowerSeries.IsEntire.subring K) : K⟦X⟧))).order =
      {i : ι | algebraMap K L (α i) = x}.encard := by
  classical
  set r : ℝ := max ‖x‖ 1
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hx : ‖x‖ ≤ r := le_max_left _ _
  have hfin : {i : ι | ‖α i‖ ≤ r}.Finite := by
    simpa only [not_lt] using eventually_cofinite.mp (hα.eventually_gt_atTop r)
  set s : Finset ι := hfin.toFinset
  have hs : ∀ i, i ∈ s ↔ ‖α i‖ ≤ r := fun i ↦ hfin.mem_toFinset
  set F : _root_.PowerSeries.IsEntire.subring K :=
    ∏' i, _root_.PowerSeries.IsEntire.polynomialHom (1 - Polynomial.C (α i)⁻¹ * Polynomial.X)
  have hF0 : (F : K⟦X⟧) ≠ 0 := by
    intro h
    have h1 : _root_.PowerSeries.constantCoeff (F : K⟦X⟧) = 1 :=
      constantCoeff_tprod_polynomialHom_one_sub_C_mul_X (fun i ↦ (α i)⁻¹)
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  have hFent : (F : K⟦X⟧).IsEntire := _root_.PowerSeries.IsEntire.mem_subring.mp F.2
  have hdisc := isDiscPreparation_tprod_polynomialHom_one_sub_C_inv_mul_X hα hα0 hr0.le hs
  rw [(hFent.isRestricted r).order_taylor_eq_count_zeroMultiset hr0 hF0 hx,
    hdisc.zeroMultiset_eq_roots_map hr0, prod_one_sub_C_inv_mul_X_eq s fun i _ ↦ hα0 i,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
  have hc0 : algebraMap K L (∏ i ∈ s, (-α i)⁻¹) ≠ 0 :=
    (map_ne_zero _).mpr
      (Finset.prod_ne_zero_iff.mpr fun i _ ↦ inv_ne_zero (neg_ne_zero.mpr (hα0 i)))
  have hmap_lin : (∏ i ∈ s, (Polynomial.X - Polynomial.C (α i)).map (algebraMap K L)) =
      ∏ i ∈ s, (Polynomial.X - Polynomial.C (algebraMap K L (α i))) := by simp
  rw [hmap_lin, Polynomial.roots_C_mul_prod_X_sub_C s _ hc0, Multiset.count_map]
  have hset : {i : ι | algebraMap K L (α i) = x} =
      ↑(s.filter fun i ↦ x = algebraMap K L (α i)) := by
    ext i
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, hs, @eq_comm L _ x]
    exact ⟨fun h ↦ ⟨by rw [← norm_algebraMap' L (α i), ← h]; exact hx, h⟩, fun h ↦ h.2⟩
  rw [hset, Set.encard_coe_eq_coe_finsetCard, Finset.card_def, Finset.filter_val]

/-- **Zero multiset of the canonical product on a closed disc.** Let `α : ι → K` be a family of
nonzero elements of a complete ultrametric normed field `K` with `‖α i‖ → ∞` cofinitely, and let
`s` be the finite set of indices with `‖α i‖ ≤ r` (for any real `r`, including `r ≤ 0`). In every
complete normed field extension `L` of `K`, the zero multiset of `∏' i, (1 - αᵢ⁻¹ X)` on the closed
disc of radius `r` is the multiset image of `s` under `algebraMap K L ∘ α`. -/
theorem zeroMultiset_tprod_polynomialHom_one_sub_C_inv_mul_X [CompleteSpace K]
    {ι L : Type*} [NormedField L] [NormedAlgebra K L] [CompleteSpace L]
    {α : ι → K} (hα : Tendsto (fun i ↦ ‖α i‖) cofinite atTop) (hα0 : ∀ i, α i ≠ 0)
    {r : ℝ} {s : Finset ι} (hs : ∀ i, i ∈ s ↔ ‖α i‖ ≤ r) :
    (((∏' i, _root_.PowerSeries.IsEntire.polynomialHom
      (1 - Polynomial.C (α i)⁻¹ * Polynomial.X) :
        _root_.PowerSeries.IsEntire.subring K) : K⟦X⟧)).zeroMultiset r L =
      s.val.map fun i ↦ algebraMap K L (α i) := by
  classical
  refine _root_.PowerSeries.zeroMultiset_eq_of_order_taylor_eq (fun z hz ↦ ?_) fun x hx ↦ ?_
  · obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hz
    rw [norm_algebraMap']
    exact (hs i).mp hi
  · rw [order_taylor_tprod_polynomialHom_one_sub_C_inv_mul_X hα hα0 x, Multiset.count_map]
    have hset : {i : ι | algebraMap K L (α i) = x} =
        ↑(s.filter fun i ↦ x = algebraMap K L (α i)) := by
      ext i
      simp only [Set.mem_ofPred_eq, Finset.coe_filter, hs, @eq_comm L _ x]
      exact ⟨fun h ↦ ⟨by rw [← norm_algebraMap' L (α i), ← h]; exact hx, h⟩, fun h ↦ h.2⟩
    rw [hset, Set.encard_coe_eq_coe_finsetCard, Finset.card_def, Finset.filter_val]

/-- **Zeros of the canonical product in a field extension.** Let `α : ι → K` be a family of nonzero
elements of a complete ultrametric normed field `K` with `‖α i‖ → ∞` cofinitely. In every complete
normed field extension `L` of `K`, a point `x : L` is a zero of `∏' i, (1 - αᵢ⁻¹ X)` if and only if
`x = algebraMap K L (α i)` for some `i`. -/
theorem evalAt_tprod_polynomialHom_one_sub_C_inv_mul_X_eq_zero_iff [CompleteSpace K]
    {ι L : Type*} [NormedField L] [NormedAlgebra K L] [CompleteSpace L]
    {α : ι → K} (hα : Tendsto (fun i ↦ ‖α i‖) cofinite atTop) (hα0 : ∀ i, α i ≠ 0) (x : L) :
    (((∏' i, _root_.PowerSeries.IsEntire.polynomialHom
      (1 - Polynomial.C (α i)⁻¹ * Polynomial.X) :
        _root_.PowerSeries.IsEntire.subring K) : K⟦X⟧)).evalAt x = 0 ↔
      ∃ i, algebraMap K L (α i) = x := by
  rw [← _root_.PowerSeries.evalAt_map_algebraMap (S := L),
    ← _root_.PowerSeries.constantCoeff_taylor,
    ← _root_.PowerSeries.order_ne_zero_iff_constCoeff_eq_zero,
    order_taylor_tprod_polynomialHom_one_sub_C_inv_mul_X hα hα0 x, ne_eq, Set.encard_eq_zero]
  exact Set.nonempty_iff_ne_empty.symm.trans Set.nonempty_def

/-- **Enumeration-independent unconditional Weierstrass product.** Let `f` be an entire power series
with constant coefficient `1` over an algebraically closed complete ultrametric normed field `K`.
For any indexing type `ι` and any family `α : ι → K` listing each point `x : K` as many times as the
multiplicity of `f` at `x` (the order of its Taylor translate), the factors `1 - αᵢ⁻¹ X` have
unconditional product `f` in `PowerSeries.IsEntire.subring K`. -/
theorem _root_.PowerSeries.IsEntire.hasProd_polynomialHom_one_sub_C_inv_mul_X
    [CompleteSpace K] [IsAlgClosed K] {f : K⟦X⟧} (hf : f.IsEntire)
    (h0 : _root_.PowerSeries.constantCoeff f = 1) {ι : Type*} {α : ι → K}
    (hα : ∀ x : K, {i : ι | α i = x}.encard = (_root_.PowerSeries.taylor x f).order) :
    HasProd (fun i ↦ _root_.PowerSeries.IsEntire.polynomialHom
      (1 - Polynomial.C (α i)⁻¹ * Polynomial.X))
      ⟨f, _root_.PowerSeries.IsEntire.mem_subring.mpr hf⟩ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at h0
  have hα0 : ∀ i, α i ≠ 0 := by
    intro i hi
    have h1 : (1 : ℕ∞) ≤ (_root_.PowerSeries.taylor 0 f).order := by
      rw [← hα 0]
      exact Set.one_le_encard_iff_nonempty.mpr ⟨i, hi⟩
    rw [_root_.PowerSeries.taylor_zero, Order.one_le_iff_ne_zero,
      _root_.PowerSeries.order_ne_zero_iff_constCoeff_eq_zero, h0] at h1
    exact one_ne_zero h1
  have hfid : _root_.PowerSeries.map (algebraMap K K) f = f := by ext n; simp
  have hgrow : Tendsto (fun i ↦ ‖α i‖) cofinite atTop :=
    hf.tendsto_norm_cofinite_atTop_of_encard_le_order_taylor (L := K) hf0 fun i ↦ by
      rw [hfid, hα (α i)]
  have hm := multipliable_polynomialHom_one_sub_C_inv_mul_X hgrow
  set G : _root_.PowerSeries.IsEntire.subring K :=
    ∏' i, _root_.PowerSeries.IsEntire.polynomialHom (1 - Polynomial.C (α i)⁻¹ * Polynomial.X)
  have hGeq : f = (G : K⟦X⟧) := by
    refine hf.eq_of_order_taylor_eq (_root_.PowerSeries.IsEntire.mem_subring.mp G.2) h0
      (constantCoeff_tprod_polynomialHom_one_sub_C_mul_X _) fun x ↦ ?_
    have hord := order_taylor_tprod_polynomialHom_one_sub_C_inv_mul_X (L := K) hgrow hα0 x
    have hGid : _root_.PowerSeries.map (algebraMap K K) (G : K⟦X⟧) = (G : K⟦X⟧) := by ext n; simp
    rw [hGid] at hord
    simp only [Algebra.algebraMap_self_apply] at hord
    exact (hα x).symm.trans hord.symm
  have hsub : G = ⟨f, _root_.PowerSeries.IsEntire.mem_subring.mpr hf⟩ := Subtype.ext hGeq.symm
  exact hsub ▸ hm.hasProd

/-- **Existence of a countable canonical Weierstrass product.** Over an algebraically closed
complete ultrametric normed field `K`, every entire power series `f` with constant coefficient `1`
admits a countable family `α : ι → K` of nonzero elements listing the zeros of `f` with their
multiplicities such that `∏' i, (1 - αᵢ⁻¹ X)` converges unconditionally to `f` in
`PowerSeries.IsEntire.subring K`. -/
theorem _root_.PowerSeries.IsEntire.exists_countable_hasProd_polynomialHom_one_sub_C_inv_mul_X
    [CompleteSpace K] [IsAlgClosed K] {f : K⟦X⟧} (hf : f.IsEntire)
    (h0 : _root_.PowerSeries.constantCoeff f = 1) :
    ∃ (ι : Type u) (_ : Countable ι) (α : ι → K), (∀ i, α i ≠ 0) ∧
      (∀ x : K, {i : ι | α i = x}.encard = (_root_.PowerSeries.taylor x f).order) ∧
      HasProd (fun i ↦ _root_.PowerSeries.IsEntire.polynomialHom
        (1 - Polynomial.C (α i)⁻¹ * Polynomial.X))
        ⟨f, _root_.PowerSeries.IsEntire.mem_subring.mpr hf⟩ := by
  classical
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at h0
  have hfid : _root_.PowerSeries.map (algebraMap K K) f = f := by ext n; simp
  have hcnt : {x : K | f.evalAt x = 0}.Countable := by
    simpa only [hfid] using hf.countable_setOf_evalAt_eq_zero (L := K) hf0
  have : Countable {x : K | f.evalAt x = 0} := hcnt.to_subtype
  let ι : Type u :=
    Σ x : {x : K | f.evalAt x = 0}, Fin (_root_.PowerSeries.taylor x.1 f).order.toNat
  let α : ι → K := fun p ↦ p.1.1
  have hα0 : ∀ i, α i ≠ 0 := by
    rintro ⟨⟨x, hx⟩, _⟩ rfl
    have hx0 : f.evalAt (0 : K) = 0 := hx
    rw [_root_.PowerSeries.evalAt_at_zero, Algebra.algebraMap_self_apply, h0] at hx0
    exact one_ne_zero hx0
  have hα : ∀ x : K, {i : ι | α i = x}.encard = (_root_.PowerSeries.taylor x f).order := by
    intro x
    by_cases hx : f.evalAt x = 0
    · have htop : (_root_.PowerSeries.taylor x f).order ≠ ⊤ := by
        have hR0 : 0 < max ‖x‖ 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
        have ho := (hf.isRestricted (max ‖x‖ 1)).order_taylor_eq_count_zeroMultiset (L := K) hR0
          hf0 (le_max_left _ _)
        rw [hfid] at ho
        exact ho.trans_lt (ENat.natCast_lt_top _) |>.ne
      let e : Fin (_root_.PowerSeries.taylor x f).order.toNat → ι := fun j ↦ ⟨⟨x, hx⟩, j⟩
      have hinj : Function.Injective e := fun _ _ h ↦ (Sigma.mk.inj_iff.mp h).2 |> eq_of_heq
      have himg : e '' Set.univ = {i : ι | α i = x} := by
        ext ⟨⟨y, hy⟩, j⟩
        simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_ofPred_eq, α, e]
        refine ⟨fun ⟨_, h⟩ ↦ congrArg (fun p : ι ↦ p.1.1) h.symm, fun h ↦ ?_⟩
        subst h
        exact ⟨j, rfl⟩
      rw [← himg, hinj.encard_image, Set.encard_univ, ENat.card_eq_coe_fintype_card,
        Fintype.card_fin, ENat.natCast_toNat_eq_self.mpr htop]
    · have hemp : {i : ι | α i = x} = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun i hi ↦
        hx (hi ▸ i.1.2)
      have hord : (_root_.PowerSeries.taylor x f).order = 0 := by
        by_contra hne
        exact hx ((_root_.PowerSeries.constantCoeff_taylor x f).symm.trans
          (_root_.PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp hne))
      rw [hemp, Set.encard_empty, hord]
  exact ⟨ι, inferInstance, α, hα0, hα, hf.hasProd_polynomialHom_one_sub_C_inv_mul_X h0 hα⟩

end NormedField

end TauCeti.PowerSeries.IsEntire
