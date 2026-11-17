/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.SymmetricPower
public import TauCeti.RingTheory.Polynomial.Roots

import TauCeti.Topology.MetricSpace.SeparatedBalls

/-!
# Continuity of the roots of a polynomial, with multiplicities

Mathlib's `Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt` shows that each root of a monic
polynomial `f` has a root of every nearby monic polynomial `g` close to it. That does not control
multiplicities: a double root of `f` could be approximated by a single root of `g`, the second
root of `g` going elsewhere. This file proves the multiplicity-sensitive statement over a proper
algebraically closed normed field, `ℂ` being the case of interest: the roots of `g`, counted with
multiplicity, can be **matched bijectively** with those of `f` so that matched roots are close.

The input is `Sym.eventually_exists_ofFn_eq_coeffEquiv_symm`, the continuity of the inverse
of the elementary symmetric chart `Sym.coeffHomeomorph`, which comes from Cauchy's bound
`Polynomial.cauchyBound` through properness of the coefficient map. Nothing here chooses a
continuous labelling of the roots; the matching is made separately for each nearby polynomial.

## Main results

* `Polynomial.Monic.exists_prod_X_sub_C_norm_sub_lt`: **continuity of roots.** For monic `f` and
  `ε > 0` there is `δ > 0` such that every monic `g` of the same degree whose coefficients are
  `δ`-close to those of `f` below their degree admits enumerations `a`, `b` of their roots, with
  multiplicity, satisfying `‖a i - b i‖ < ε`.
* `Polynomial.Monic.exists_prod_X_sub_C_norm_sub_lt_iff`: for split monic `f` and `g` over a
  seminormed domain, when the `ε`-discs around the distinct roots of `f` are disjoint, a matching
  exists exactly when every disc contains as many roots of `g` as the multiplicity of its centre,
  and no root of `g` lies outside the discs.
* `Polynomial.Monic.exists_countP_roots_mem_ball_eq_rootMultiplicity`: the resulting disc form of
  continuity of roots.
* `Polynomial.Monic.exists_rel_roots_norm_sub_lt`: the multiset form of continuity of roots, the
  root multisets of `f` and `g` being related by `Multiset.Rel` for `‖z - w‖ < ε`.
* `Polynomial.rel_roots_iff_countP_roots_mem_ball`: when the `ε`-discs around the distinct roots of
  `f` are disjoint, the multiset form and the disc form are equivalent.
* `Polynomial.eventually_exists_C_mul_prod_X_sub_C_norm_sub_lt`: the matching for a family of
  polynomials of fixed degree with continuous coefficients, normalized by its nonvanishing leading
  coefficient.
* `Polynomial.eventually_rel_roots_norm_sub_lt`: the multiset form of the same matching.
* `Polynomial.eventually_exists_bijOn_roots_toFinset`: if moreover no nearby member of the family
  has more distinct roots than the central one, the distinct roots of nearby members correspond
  bijectively to those of the central one, with matched roots close and of equal multiplicity.
* `Polynomial.continuousAt_sum_map_roots`: the sum of a function over the roots, with multiplicity,
  is continuous in the family, at a point where the function is continuous at the roots, except
  possibly at one point whose multiplicity as a root stays constant nearby.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Springer, 2006, §5.1 (continuity of the roots of a polynomial with respect to its coefficients).
-/

public section

open Filter Metric Topology TauCeti

namespace Polynomial

section Chart

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- A monic polynomial of degree `n` is the product of the linear factors of the ordered tuple
presenting its roots in the elementary symmetric chart. -/
private theorem prod_X_sub_C_eq_of_ofFn_eq {n : ℕ} {p : K[X]} (hp : p.Monic)
    (hdeg : p.natDegree = n) {a : Fin n → K}
    (ha : Sym.ofFn a = (Sym.coeffEquiv K n).symm fun i => p.coeff i) :
    ∏ i, (X - C (a i)) = p := by
  rw [← Sym.toMonic_ofFn, ha, Sym.toMonic_coeffEquiv_symm,
    TauCeti.Polynomial.monicOfCoeff_coeff hp hdeg]

/-- A polynomial of degree `d` is its leading coefficient times the product of the linear factors of
the ordered tuple presenting, in the elementary symmetric chart, its normalized lower
coefficients. -/
private theorem C_mul_prod_X_sub_C_eq_of_ofFn_eq {d : ℕ} {p : K[X]} (hp : p.degree = d)
    {a : Fin d → K}
    (ha : Sym.ofFn a = (Sym.coeffEquiv K d).symm fun i => (p.coeff d)⁻¹ * p.coeff i) :
    C p.leadingCoeff * ∏ i, (X - C (a i)) = p := by
  have hnat : p.natDegree = d := natDegree_eq_of_degree_eq_some hp
  have hlead : p.coeff d = p.leadingCoeff := by rw [leadingCoeff, hnat]
  have hlc : p.leadingCoeff ≠ 0 := hlead ▸ coeff_ne_zero_of_eq_degree hp
  have hmonic : (C p.leadingCoeff⁻¹ * p).Monic :=
    monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hlc)
  have hdeg' : (C p.leadingCoeff⁻¹ * p).natDegree = d := by
    rw [natDegree_C_mul (inv_ne_zero hlc), hnat]
  rw [prod_X_sub_C_eq_of_ofFn_eq hmonic hdeg' (by simpa only [coeff_C_mul, hlead] using ha),
    ← mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, one_mul]

end Chart

section Matching

variable {K : Type*} [SeminormedCommRing K] [IsDomain K]

open scoped Classical in
/-- **The multiset and disc forms of a matching agree.** Suppose the `ε`-discs around the distinct
roots of `f` are pairwise disjoint. Then the root multisets of `f` and `g` are related by
`Multiset.Rel` for the relation `‖z - w‖ < ε` exactly when each disc around a root `z` of `f`
contains `rootMultiplicity z f` roots of `g`, counted with multiplicity, and every root of `g` lies
in one of these discs. -/
theorem rel_roots_iff_countP_roots_mem_ball {f g : K[X]} {ε : ℝ}
    (hsep : ∀ z ∈ f.roots, ∀ w ∈ f.roots, z ≠ w → 2 * ε ≤ ‖z - w‖) :
    f.roots.Rel (fun z w => ‖z - w‖ < ε) g.roots ↔
      (∀ z ∈ f.roots, g.roots.countP (· ∈ ball z ε) = f.rootMultiplicity z) ∧
        ∀ w ∈ g.roots, ∃ z ∈ f.roots, ‖w - z‖ < ε := by
  -- a point of `K` is within `ε` of at most one root of `f`
  have huniq : ∀ w ∈ g.roots, ∀ z ∈ f.roots, ∀ z' ∈ f.roots, ‖z - w‖ < ε → ‖z' - w‖ < ε →
      z = z' := by
    intro w _ z hz z' hz' h h'
    by_contra hne
    have := hsep z hz z' hz' hne
    have := norm_sub_le_norm_sub_add_norm_sub z w z'
    have := norm_sub_rev z' w
    linarith
  rw [Multiset.rel_iff_forall_countP_eq_count huniq]
  simp only [mem_ball, dist_eq_norm, norm_sub_rev _ (_ : K), count_roots]

open scoped Classical in
/-- **Matching roots versus counting them in discs.** Let `f` and `g` be split monic polynomials,
and suppose the `ε`-discs around the distinct roots of `f` are pairwise disjoint. Then the roots of
`f` and `g`, with multiplicity, can be enumerated so that matched roots are at distance less than
`ε` exactly when each disc around a root `z` of `f` contains `rootMultiplicity z f` roots of `g`,
counted with multiplicity, and every root of `g` lies in one of these discs. -/
theorem Monic.exists_prod_X_sub_C_norm_sub_lt_iff {f g : K[X]} (hf : f.Monic) (hg : g.Monic)
    (hfs : f.Splits) (hgs : g.Splits) {ε : ℝ}
    (hsep : ∀ z ∈ f.roots, ∀ w ∈ f.roots, z ≠ w → 2 * ε ≤ ‖z - w‖) :
    (∃ a b : Fin f.natDegree → K,
        f = ∏ i, (X - C (a i)) ∧ g = ∏ i, (X - C (b i)) ∧ ∀ i, ‖a i - b i‖ < ε) ↔
      (∀ z ∈ f.roots, g.roots.countP (· ∈ ball z ε) = f.rootMultiplicity z) ∧
        ∀ w ∈ g.roots, ∃ z ∈ f.roots, ‖w - z‖ < ε := by
  exact (hf.rel_roots_iff_exists_prod_X_sub_C hg hfs hgs).symm.trans
    (rel_roots_iff_countP_roots_mem_ball hsep)

/-- **Distinct roots under a matching of roots.** Let `a` and `b` enumerate the roots of `f` and
`g` with multiplicity, with `‖a i - b i‖ < ρ`, where the distinct roots of `f` are more than `2 * ρ`
apart. If `g` has at most as many distinct roots as `f`, then `a i ↦ b i` is a well-defined
bijection between the distinct roots, and it preserves multiplicities. -/
private theorem exists_bijOn_roots_toFinset_of_norm_sub_lt [DecidableEq K] {f g : K[X]} {d : ℕ}
    {a b : Fin d → K} {ρ : ℝ} (hf : f.roots = Finset.univ.val.map a)
    (hg : g.roots = Finset.univ.val.map b) (hab : ∀ i, ‖a i - b i‖ < ρ)
    (hsep : ∀ z ∈ f.roots.toFinset, ∀ w ∈ f.roots.toFinset, z ≠ w → 2 * ρ < dist z w)
    (hcard : g.roots.toFinset.card ≤ f.roots.toFinset.card) :
    ∃ e : K → K, Set.BijOn e f.roots.toFinset g.roots.toFinset ∧
      ∀ z ∈ f.roots, ‖e z - z‖ < ρ ∧ g.rootMultiplicity (e z) = f.rootMultiplicity z := by
  have hmem : ∀ i, a i ∈ f.roots.toFinset := fun i => by simp [hf]
  -- matched roots of `g` agree only if their partners agree, by disjointness of the discs
  have hba : Function.FactorsThrough a b := by
    intro i j h
    apply eq_of_dist_lt_of_dist_lt (hsep (a i) (hmem i) (a j) (hmem j))
    · rw [dist_eq_norm, norm_sub_rev]
      exact hab i
    · rw [dist_eq_norm, h, norm_sub_rev]
      exact hab j
  -- conversely, `a = ψ ∘ b` and counting values shows that `ψ` is injective on the values of `b`
  have hab' : Function.FactorsThrough b a := by
    have hψ : ∀ k, Function.extend b a id (b k) = a k := fun k => hba.extend_apply id k
    have hinj : Set.InjOn (Function.extend b a id) (Finset.univ.image b) := by
      refine Finset.card_image_iff.1 (le_antisymm Finset.card_image_le ?_)
      rw [Finset.image_image, hba.extend_comp]
      simpa only [hf, hg, Multiset.toFinset_map, Finset.val_toFinset] using hcard
    intro i j h
    exact hinj (by simp) (by simp) (by rw [hψ, hψ, h])
  have he : ∀ i, Function.extend a b id (a i) = b i := hab'.extend_apply id
  have hcount : ∀ i, g.rootMultiplicity (b i) = f.rootMultiplicity (a i) := fun i => by
    rw [← count_roots, ← count_roots, hf, hg, Multiset.count_map, Multiset.count_map]
    exact congrArg Multiset.card (Multiset.filter_congr fun j _ =>
      ⟨fun h => (hba h.symm).symm, fun h => (hab' h.symm).symm⟩)
  simp only [Set.BijOn, Set.MapsTo, Set.InjOn, Set.SurjOn, Set.subset_def, Finset.mem_coe,
    Multiset.mem_toFinset, hf, hg, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and,
    Set.mem_image, forall_exists_index, forall_apply_eq_imp_iff]
  refine ⟨Function.extend a b id, ⟨fun i => ⟨i, (he i).symm⟩, fun i j h => ?_,
    fun i => ⟨a i, ⟨i, rfl⟩, he i⟩⟩, fun i => ⟨?_, ?_⟩⟩
  · rw [he, he] at h
    exact hba h
  · rw [he, norm_sub_rev]
    exact hab i
  · rw [he]
    exact hcount i

end Matching

section Continuity

variable {K : Type*} [NormedField K] [IsAlgClosed K] [ProperSpace K]

/-- **Continuity of roots, with multiplicities.** For a monic polynomial `f` and `ε > 0`, every
monic polynomial `g` of the same degree with lower coefficients close enough to those of `f` has
its roots matched bijectively with those of `f`, counted with multiplicity: there are enumerations
`a` and `b` of their roots with `‖a i - b i‖ < ε` for every `i`. This includes degree zero. -/
theorem Monic.exists_prod_X_sub_C_norm_sub_lt {f : K[X]} (hf : f.Monic) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g : K[X], g.Monic → g.natDegree = f.natDegree →
      (∀ i < f.natDegree, ‖g.coeff i - f.coeff i‖ < δ) →
      ∃ a b : Fin f.natDegree → K,
        f = ∏ i, (X - C (a i)) ∧ g = ∏ i, (X - C (b i)) ∧ ∀ i, ‖a i - b i‖ < ε := by
  obtain ⟨a, ha⟩ := Sym.ofFn_surjective ((Sym.coeffEquiv K f.natDegree).symm fun i => f.coeff i)
  have hc : Sym.coeffEquiv K _ (Sym.ofFn a) = fun i : Fin f.natDegree => f.coeff i := by
    rw [ha, Equiv.apply_symm_apply]
  have hev := Sym.eventually_exists_ofFn_eq_coeffEquiv_symm a hε
  rw [hc] at hev
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ, hδ, fun g hg hdeg hcoeff => ?_⟩
  obtain ⟨b, hb, hab⟩ := hball (y := fun i : Fin f.natDegree => g.coeff i) <|
    (dist_pi_lt_iff hδ).2 fun i => by simpa [dist_eq_norm] using hcoeff i i.is_lt
  exact ⟨a, b, (prod_X_sub_C_eq_of_ofFn_eq hf rfl ha).symm,
    (prod_X_sub_C_eq_of_ofFn_eq hg hdeg hb).symm, hab⟩

open scoped Classical in
/-- **Continuity of roots in discs.** If the `ε`-discs around the distinct roots of a monic
polynomial `f` are pairwise disjoint, then every monic polynomial `g` of the same degree with
lower coefficients close enough to those of `f` has, counted with multiplicity, exactly
`rootMultiplicity z f` roots in the disc around each root `z` of `f`, and no roots outside these
discs. -/
theorem Monic.exists_countP_roots_mem_ball_eq_rootMultiplicity {f : K[X]} (hf : f.Monic) {ε : ℝ}
    (hε : 0 < ε) (hsep : ∀ z ∈ f.roots, ∀ w ∈ f.roots, z ≠ w → 2 * ε ≤ ‖z - w‖) :
    ∃ δ > 0, ∀ g : K[X], g.Monic → g.natDegree = f.natDegree →
      (∀ i < f.natDegree, ‖g.coeff i - f.coeff i‖ < δ) →
      (∀ z ∈ f.roots, g.roots.countP (· ∈ ball z ε) = f.rootMultiplicity z) ∧
        ∀ w ∈ g.roots, ∃ z ∈ f.roots, ‖w - z‖ < ε := by
  obtain ⟨δ, hδ, h⟩ := hf.exists_prod_X_sub_C_norm_sub_lt hε
  exact ⟨δ, hδ, fun g hg hdeg hcoeff =>
    (hf.exists_prod_X_sub_C_norm_sub_lt_iff hg (IsAlgClosed.splits f) (IsAlgClosed.splits g)
      hsep).1 (h g hg hdeg hcoeff)⟩

/-- **Continuity of roots as multisets.** For a monic polynomial `f` and `ε > 0`, every monic
polynomial `g` of the same degree with lower coefficients close enough to those of `f` has its root
multiset related to that of `f` by `Multiset.Rel` for the relation `‖z - w‖ < ε`: the roots, with
multiplicity, pair off one-to-one with paired roots at distance less than `ε`. -/
theorem Monic.exists_rel_roots_norm_sub_lt {f : K[X]} (hf : f.Monic) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g : K[X], g.Monic → g.natDegree = f.natDegree →
      (∀ i < f.natDegree, ‖g.coeff i - f.coeff i‖ < δ) →
      f.roots.Rel (fun z w => ‖z - w‖ < ε) g.roots := by
  obtain ⟨δ, hδ, h⟩ := hf.exists_prod_X_sub_C_norm_sub_lt hε
  exact ⟨δ, hδ, fun g hg hdeg hcoeff =>
    (hf.rel_roots_iff_exists_prod_X_sub_C hg (IsAlgClosed.splits f) (IsAlgClosed.splits g)).2
      (h g hg hdeg hcoeff)⟩

/-- **Continuity of roots in a family.** Let `F x` be polynomials of degree `d`, near `x₀`, whose
coefficients of index at most `d` are continuous at `x₀`. Then for `x` near `x₀` the roots of
`F x` are matched bijectively, with multiplicity, with those of `F x₀`: there are enumerations `a`
and `b` of the roots of `F x₀` and `F x` with `‖a i - b i‖ < ε` for every `i`. -/
theorem eventually_exists_C_mul_prod_X_sub_C_norm_sub_lt {B : Type*} [TopologicalSpace B]
    {F : B → K[X]} {x₀ : B} {d : ℕ} (hF : ∀ i ≤ d, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).degree = d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∃ a b : Fin d → K,
      F x₀ = C (F x₀).leadingCoeff * ∏ i, (X - C (a i)) ∧
        F x = C (F x).leadingCoeff * ∏ i, (X - C (b i)) ∧ ∀ i, ‖a i - b i‖ < ε := by
  have hdeg₀ : (F x₀).degree = d := hdeg.self_of_nhds
  have hlc : (F x₀).coeff d ≠ 0 := coeff_ne_zero_of_eq_degree hdeg₀
  -- the normalized lower coefficients depend continuously on `x` at `x₀`
  set v : B → Fin d → K := fun x i => ((F x).coeff d)⁻¹ * (F x).coeff i
  have hv : ContinuousAt v x₀ :=
    continuousAt_pi.2 fun i => ((hF d le_rfl).inv₀ hlc).mul (hF i i.is_lt.le)
  obtain ⟨a, ha⟩ := Sym.ofFn_surjective ((Sym.coeffEquiv K d).symm (v x₀))
  have hc : Sym.coeffEquiv K d (Sym.ofFn a) = v x₀ := by rw [ha, Equiv.apply_symm_apply]
  have hev := Sym.eventually_exists_ofFn_eq_coeffEquiv_symm a hε
  rw [hc] at hev
  filter_upwards [hv.eventually hev, hdeg] with x ⟨b, hb, hab⟩ hx
  exact ⟨a, b, (C_mul_prod_X_sub_C_eq_of_ofFn_eq hdeg₀ ha).symm,
    (C_mul_prod_X_sub_C_eq_of_ofFn_eq hx hb).symm, hab⟩

/-- **Continuity of roots in a family, as multisets.** Let `F x` be polynomials of degree `d`, near
`x₀`, whose coefficients of index at most `d` are continuous at `x₀`. Then for `x` near `x₀` the
root multisets of `F x₀` and `F x` are related by `Multiset.Rel` for the relation
`‖z - w‖ < ε`. -/
theorem eventually_rel_roots_norm_sub_lt {B : Type*} [TopologicalSpace B]
    {F : B → K[X]} {x₀ : B} {d : ℕ} (hF : ∀ i ≤ d, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).degree = d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, (F x₀).roots.Rel (fun z w => ‖z - w‖ < ε) (F x).roots := by
  filter_upwards [eventually_exists_C_mul_prod_X_sub_C_norm_sub_lt hF hdeg hε, hdeg]
    with x ⟨a, b, hfa, hgb, hab⟩ hx
  exact Multiset.rel_iff_exists_fin.2 ⟨d, a, b,
    roots_eq_map_of_eq_C_mul_prod_X_sub_C (ne_zero_of_coe_le_degree hdeg.self_of_nhds.ge) hfa,
    roots_eq_map_of_eq_C_mul_prod_X_sub_C (ne_zero_of_coe_le_degree hx.ge) hgb, hab⟩

open scoped Classical in
/-- **Distinct roots in a family.** Let `F x` be polynomials of degree `d`, near `x₀`, whose
coefficients of index at most `d` are continuous at `x₀`, and suppose that near `x₀` the polynomial
`F x` has at most as many distinct roots as `F x₀`. Then for `x` near `x₀` there is a bijection `e`
from the distinct roots of `F x₀` onto those of `F x` that moves each root by less than `ε` and
preserves its multiplicity. -/
theorem eventually_exists_bijOn_roots_toFinset {B : Type*} [TopologicalSpace B]
    {F : B → K[X]} {x₀ : B} {d : ℕ} (hF : ∀ i ≤ d, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).degree = d)
    (hcard : ∀ᶠ x in 𝓝 x₀, (F x).roots.toFinset.card ≤ (F x₀).roots.toFinset.card) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∃ e : K → K,
      Set.BijOn e (F x₀).roots.toFinset (F x).roots.toFinset ∧
        ∀ z ∈ (F x₀).roots,
          ‖e z - z‖ < ε ∧ (F x).rootMultiplicity (e z) = (F x₀).rootMultiplicity z := by
  -- shrink `ε` so that the discs around the distinct roots of `F x₀` are pairwise disjoint
  obtain ⟨r, hr, -, hsep⟩ := exists_pos_closedBall_subset_and_lt_dist
    (T := (F x₀).roots.toFinset) (U := fun _ => Set.univ) fun _ _ => univ_mem
  filter_upwards [eventually_exists_C_mul_prod_X_sub_C_norm_sub_lt hF hdeg (lt_min hε hr), hdeg,
    hcard] with x ⟨a, b, hfa, hgb, hab⟩ hx hxcard
  obtain ⟨e, he, hed⟩ := exists_bijOn_roots_toFinset_of_norm_sub_lt
    (roots_eq_map_of_eq_C_mul_prod_X_sub_C (ne_zero_of_coe_le_degree hdeg.self_of_nhds.ge) hfa)
    (roots_eq_map_of_eq_C_mul_prod_X_sub_C (ne_zero_of_coe_le_degree hx.ge) hgb) hab
    (fun z hz w hw hzw => by linarith [hsep z hz w hw hzw, min_le_right ε r]) hxcard
  exact ⟨e, he, fun z hz => ⟨(hed z hz).1.trans_le (min_le_left ε r), (hed z hz).2⟩⟩

/-- If two enumerations `a` and `b` take the value `c` equally often, and `b i ≠ c` whenever
`a i ≠ c`, then `b i = c` whenever `a i = c`. -/
private theorem forall_eq_of_count_map_eq {ι α : Type*} [Fintype ι] [DecidableEq α]
    {a b : ι → α} {c : α} (hab : ∀ i, a i ≠ c → b i ≠ c)
    (hcount : (Finset.univ.val.map a).count c = (Finset.univ.val.map b).count c) (i : ι)
    (hi : a i = c) : b i = c := by
  have hsub : Finset.univ.filter (fun j => b j = c) ⊆ Finset.univ.filter (fun j => a j = c) :=
    fun j => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun hj => by_contra fun h => hab j h hj
  have hcard : (Finset.univ.filter (fun j => a j = c)).card ≤
      (Finset.univ.filter (fun j => b j = c)).card := by
    rw [Multiset.count_map, Multiset.count_map] at hcount
    rw [Finset.card_def, Finset.card_def, Finset.filter_val, Finset.filter_val]
    simp_rw [eq_comm (a := c)] at hcount
    omega
  simpa [hi] using (Finset.ext_iff.1 (Finset.eq_of_subset_of_card_le hsub hcard) i).2

/-- **Continuity of sums over the roots in a family.** Let `F x` be polynomials of degree `d`, near
`x₀`, whose coefficients of index at most `d` are continuous at `x₀`, and let `g` be continuous at
every root of `F x₀` other than `c`. If, near `x₀`, the multiplicity of `c` as a root of `F x` is
its multiplicity as a root of `F x₀`, then the sum of `g` over the roots of `F x`, counted with
multiplicity, is continuous at `x₀`. In particular `g` may be discontinuous at `c`. -/
theorem continuousAt_sum_map_roots {B E : Type*} [TopologicalSpace B] [SeminormedAddCommGroup E]
    {F : B → K[X]} {x₀ : B} {d : ℕ} (hF : ∀ i ≤ d, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).degree = d) {g : K → E} {c : K}
    (hg : ∀ z ∈ (F x₀).roots, z ≠ c → ContinuousAt g z)
    (hc : ∀ᶠ x in 𝓝 x₀, (F x).rootMultiplicity c = (F x₀).rootMultiplicity c) :
    ContinuousAt (fun x => ((F x).roots.map g).sum) x₀ := by
  classical
  refine Metric.tendsto_nhds.2 fun η hη => ?_
  have hη' : 0 < η / (d + 1) := by positivity
  -- a radius `δ` keeping each root `z ≠ c` of `F x₀` away from `c` and controlling `g` near `z`
  have hδ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ z ∈ (F x₀).roots.toFinset.filter (· ≠ c), ∀ w,
      ‖w - z‖ < δ → w ≠ c ∧ ‖g w - g z‖ < η / (d + 1) := by
    refine (eventually_all_finset _).2 fun z hz => ?_
    obtain ⟨hzr, hzc⟩ := Finset.mem_filter.1 hz
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 <| (isOpen_ne.eventually_mem hzc).and
      (Metric.tendsto_nhds.1 (hg z (Multiset.mem_toFinset.1 hzr) hzc) _ hη')
    filter_upwards [Ioo_mem_nhdsGT hr] with δ hδ w hw
    simpa only [dist_eq_norm, Set.mem_ofPred_eq] using
      hball (y := w) (by rw [dist_eq_norm]; exact hw.trans hδ.2)
  obtain ⟨δ, hδ, hδpos⟩ := (hδ.and self_mem_nhdsWithin).exists
  filter_upwards [eventually_exists_C_mul_prod_X_sub_C_norm_sub_lt hF hdeg hδpos, hdeg, hc]
    with x ⟨a, b, ha, hb, hab⟩ hx hcx
  have hra := roots_eq_map_of_eq_C_mul_prod_X_sub_C
    (ne_zero_of_coe_le_degree hdeg.self_of_nhds.ge) ha
  have hrb := roots_eq_map_of_eq_C_mul_prod_X_sub_C (ne_zero_of_coe_le_degree hx.ge) hb
  -- matched roots away from `c` stay away from `c`, and `g` moves little along them
  have hne (i : Fin d) (hi : a i ≠ c) : b i ≠ c ∧ ‖g (b i) - g (a i)‖ < η / (d + 1) :=
    hδ (a i) (Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2
      (hra ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)), hi⟩) (b i)
      (by rw [norm_sub_rev]; exact hab i)
  -- matched roots at `c` stay at `c`, as `F x` and `F x₀` have equally many roots at `c`
  have hbc := forall_eq_of_count_map_eq (fun i hi => (hne i hi).1) <| by
    rw [← hra, ← hrb, count_roots, count_roots, hcx]
  rw [dist_eq_norm, hra, hrb, Multiset.map_map, Multiset.map_map, ← Finset.sum_eq_multiset_sum,
    ← Finset.sum_eq_multiset_sum, ← Finset.sum_sub_distrib]
  calc ‖∑ i, ((g ∘ b) i - (g ∘ a) i)‖ ≤ ∑ i, ‖g (b i) - g (a i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, η / (d + 1) := Finset.sum_le_sum fun i _ => by
      by_cases hi : a i = c
      · simp [hi, hbc i hi, hη'.le]
      · exact (hne i hi).2.le
    _ < η := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_assoc',
        div_lt_iff₀ (by positivity)]
      nlinarith

end Continuity

end Polynomial
