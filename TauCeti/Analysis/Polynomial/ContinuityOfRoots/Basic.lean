/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.SymmetricPower
public import TauCeti.Data.Fintype.Fiber

import TauCeti.Topology.MetricSpace.SeparatedBalls

/-!
# Continuity of the roots of a polynomial, with multiplicities

Mathlib's `Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt` shows that each root of a monic
polynomial `f` has a root of every nearby monic polynomial `g` close to it. That does not control
multiplicities: a double root of `f` could be approximated by a single root of `g`, the second
root of `g` going elsewhere. This file proves the multiplicity-sensitive statement over a proper
algebraically closed normed field, `ℂ` being the case of interest: the roots of `g`, counted with
multiplicity, can be **matched bijectively** with those of `f` so that matched roots are close.

The input is `TauCeti.Sym.eventually_exists_ofFn_eq_coeffEquiv_symm`, the continuity of the inverse
of the elementary symmetric chart `TauCeti.Sym.coeffHomeomorph`, which comes from Cauchy's bound
`Polynomial.cauchyBound` through properness of the coefficient map. Nothing here chooses a
continuous labelling of the roots; the matching is made separately for each nearby polynomial.

## Main results

* `Polynomial.Monic.exists_prod_X_sub_C_norm_sub_lt`: **continuity of roots.** For monic `f` and
  `ε > 0` there is `δ > 0` such that every monic `g` of the same degree whose coefficients are
  `δ`-close to those of `f` admits enumerations `a`, `b` of the roots of `f` and `g`, with
  multiplicity, satisfying `‖a i - b i‖ < ε`.
* `Polynomial.Monic.exists_prod_X_sub_C_norm_sub_lt_iff`: when the `ε`-discs around the distinct
  roots of `f` are disjoint, such a matching exists exactly when every disc contains as many roots
  of `g` as the multiplicity of its centre, and no root of `g` lies outside the discs.
* `Polynomial.Monic.exists_countP_roots_mem_ball_eq_rootMultiplicity`: the resulting disc form of
  continuity of roots.
* `Polynomial.eventually_exists_C_mul_prod_X_sub_C_norm_sub_lt`: the matching for a family of
  polynomials of fixed degree with continuous coefficients, normalized by its nonvanishing leading
  coefficient.
* `Polynomial.eventually_exists_bijOn_roots_toFinset`: if moreover no nearby member of the family
  has more distinct roots than the central one, the distinct roots of nearby members correspond
  bijectively to those of the central one, with matched roots close and of equal multiplicity.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Springer, 2006, §5.1 (continuity of the roots of a polynomial with respect to its coefficients).
-/

public section

open Filter Metric Topology TauCeti

namespace Polynomial

variable {K : Type*} [NormedField K] [IsAlgClosed K]

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

section Matching

open scoped Classical in
/-- **Matching roots versus counting them in discs.** Let `f` and `g` be monic of the same degree,
and suppose the `ε`-discs around the distinct roots of `f` are pairwise disjoint. Then the roots of
`f` and `g`, with multiplicity, can be enumerated so that matched roots are at distance less than
`ε` exactly when each disc around a root `z` of `f` contains `rootMultiplicity z f` roots of `g`,
counted with multiplicity, and every root of `g` lies in one of these discs. -/
theorem Monic.exists_prod_X_sub_C_norm_sub_lt_iff {f g : K[X]} (hf : f.Monic) (hg : g.Monic)
    (hdeg : g.natDegree = f.natDegree) {ε : ℝ}
    (hsep : ∀ z ∈ f.roots, ∀ w ∈ f.roots, z ≠ w → 2 * ε ≤ ‖z - w‖) :
    (∃ a b : Fin f.natDegree → K,
        f = ∏ i, (X - C (a i)) ∧ g = ∏ i, (X - C (b i)) ∧ ∀ i, ‖a i - b i‖ < ε) ↔
      (∀ z ∈ f.roots, g.roots.countP (· ∈ ball z ε) = f.rootMultiplicity z) ∧
        ∀ w ∈ g.roots, ∃ z ∈ f.roots, ‖w - z‖ < ε := by
  -- Forward, a matched root of `g` lies in the disc of its partner and in no other disc. Backward,
  -- send each root of `g` to the centre of its disc, compare occurrence counts with an enumeration
  -- of the roots of `f`, and permute that enumeration to match.
  have hroots : ∀ {p : K[X]} (a : Fin f.natDegree → K), p = ∏ i, (X - C (a i)) →
      p.roots = Finset.univ.val.map a := fun a hp => by
    rw [congrArg roots hp, ← Sym.toMonic_ofFn, Sym.roots_toMonic, Sym.coe_ofFn, Fin.univ_val_map]
  have hmem : ∀ (a : Fin f.natDegree → K) i, a i ∈ Finset.univ.val.map a := fun a i =>
    Multiset.mem_map_of_mem _ (Finset.mem_univ i)
  -- a point of `K` is within `ε` of at most one root of `f`
  have huniq : ∀ w, ∀ z ∈ f.roots, ∀ z' ∈ f.roots, ‖w - z‖ < ε → ‖w - z'‖ < ε → z = z' := by
    intro w z hz z' hz' h h'
    by_contra hne
    have := hsep z hz z' hz' hne
    have := norm_sub_le_norm_sub_add_norm_sub z w z'
    have := norm_sub_rev z w
    linarith
  -- both sides compare `b` with `a` through the counting identity below
  have hcard : ∀ (b u : Fin f.natDegree → K) (z : K),
      (∀ i, u i = z ↔ ‖b i - z‖ < ε) →
        (Finset.univ.filter fun i => u i = z).card =
          ((Finset.univ.val.map b).countP (· ∈ ball z ε)) := fun b u z h => by
    rw [Multiset.countP_map, Finset.card_def, Finset.filter_val]
    exact congrArg Multiset.card (Multiset.filter_congr fun i _ => by
      simpa [dist_eq_norm] using h i)
  constructor
  · rintro ⟨a, b, hfa, hgb, hab⟩
    rw [hroots a hfa] at huniq ⊢
    rw [hroots b hgb]
    refine ⟨fun z hz => ?_, ?_⟩
    · rw [← count_roots, hroots a hfa, Multiset.count_map, ← hcard b a z fun i => ?_]
      · simp only [eq_comm (a := z), Finset.card_def, Finset.filter_val]
      · refine ⟨fun h => h ▸ by rw [norm_sub_rev]; exact hab i, fun h => ?_⟩
        exact huniq (b i) _ (hmem a i) z hz (by rw [norm_sub_rev]; exact hab i) h
    · rintro w hw
      obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hw
      exact ⟨a i, hmem a i, by rw [norm_sub_rev]; exact hab i⟩
  · rintro ⟨hcount, hin⟩
    obtain ⟨a, ha⟩ := Sym.ofFn_surjective ((Sym.coeffEquiv K _).symm fun i => f.coeff i)
    obtain ⟨b, hb⟩ := Sym.ofFn_surjective ((Sym.coeffEquiv K _).symm fun i => g.coeff i)
    have hfa := (prod_X_sub_C_eq_of_ofFn_eq hf rfl ha).symm
    have hgb := (prod_X_sub_C_eq_of_ofFn_eq hg hdeg hb).symm
    have hfr := hroots a hfa
    have hgr := hroots b hgb
    -- send each root of `g` to the root of `f` whose disc contains it
    choose! φ hφ hφε using hin
    have hb_mem : ∀ i, b i ∈ g.roots := fun i => hgr ▸ hmem b i
    -- `φ ∘ b` takes each value as often as `a` does
    have hocc : ∀ z, Function.occCount (φ ∘ b) z = Function.occCount a z := by
      intro z
      rw [Function.occCount_eq_card_filter, Function.occCount_eq_card_filter]
      by_cases hz : z ∈ f.roots
      · rw [hcard b (φ ∘ b) z fun i => ⟨fun h => h ▸ hφε _ (hb_mem i),
          fun h => huniq (b i) _ (hφ _ (hb_mem i)) z hz (hφε _ (hb_mem i)) h⟩, ← hgr, hcount z hz,
          ← count_roots, hfr, Multiset.count_map]
        simp only [eq_comm (a := z), Finset.card_def, Finset.filter_val]
      · rw [Finset.filter_false_of_mem fun i _ (h : (φ ∘ b) i = z) => hz (h ▸ hφ _ (hb_mem i)),
          Finset.filter_false_of_mem fun i _ (h : a i = z) => hz (h ▸ hfr ▸ hmem a i)]
    obtain ⟨σ, hσ⟩ := Function.exists_perm_of_occCount_eq hocc
    refine ⟨a ∘ σ, b, hfa.trans (Equiv.prod_comp σ fun i => X - C (a i)).symm, hgb, fun i => ?_⟩
    have hσi : a (σ i) = φ (b i) := congrFun hσ i
    rw [Function.comp_apply, hσi, norm_sub_rev]
    exact hφε _ (hb_mem i)

omit [IsAlgClosed K] in
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
    by_contra hne
    have hj : ‖b i - a j‖ < ρ := by rw [h, norm_sub_rev]; exact hab j
    have := hsep (a i) (hmem i) (a j) (hmem j) hne
    have := norm_sub_le_norm_sub_add_norm_sub (a i) (b i) (a j)
    rw [dist_eq_norm] at *
    linarith [hab i]
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

variable [ProperSpace K]

/-- **Continuity of roots, with multiplicities.** For a monic polynomial `f` and `ε > 0`, every
monic polynomial `g` of the same degree with coefficients close enough to those of `f` has its roots
matched bijectively with those of `f`, counted with multiplicity: there are enumerations `a` and `b`
of the roots of `f` and `g` with `‖a i - b i‖ < ε` for every `i`. This includes degree zero. -/
theorem Monic.exists_prod_X_sub_C_norm_sub_lt {f : K[X]} (hf : f.Monic) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g : K[X], g.Monic → g.natDegree = f.natDegree →
      (∀ i, ‖g.coeff i - f.coeff i‖ < δ) →
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
    (dist_pi_lt_iff hδ).2 fun i => by simpa [dist_eq_norm] using hcoeff i
  exact ⟨a, b, (prod_X_sub_C_eq_of_ofFn_eq hf rfl ha).symm,
    (prod_X_sub_C_eq_of_ofFn_eq hg hdeg hb).symm, hab⟩

open scoped Classical in
/-- **Continuity of roots in discs.** If the `ε`-discs around the distinct roots of a monic
polynomial `f` are pairwise disjoint, then every monic polynomial `g` of the same degree with
coefficients close enough to those of `f` has, counted with multiplicity, exactly
`rootMultiplicity z f` roots in the disc around each root `z` of `f`, and no roots outside these
discs. -/
theorem Monic.exists_countP_roots_mem_ball_eq_rootMultiplicity {f : K[X]} (hf : f.Monic) {ε : ℝ}
    (hε : 0 < ε) (hsep : ∀ z ∈ f.roots, ∀ w ∈ f.roots, z ≠ w → 2 * ε ≤ ‖z - w‖) :
    ∃ δ > 0, ∀ g : K[X], g.Monic → g.natDegree = f.natDegree →
      (∀ i, ‖g.coeff i - f.coeff i‖ < δ) →
      (∀ z ∈ f.roots, g.roots.countP (· ∈ ball z ε) = f.rootMultiplicity z) ∧
        ∀ w ∈ g.roots, ∃ z ∈ f.roots, ‖w - z‖ < ε := by
  obtain ⟨δ, hδ, h⟩ := hf.exists_prod_X_sub_C_norm_sub_lt hε
  exact ⟨δ, hδ, fun g hg hdeg hcoeff =>
    (hf.exists_prod_X_sub_C_norm_sub_lt_iff hg hdeg hsep).1 (h g hg hdeg hcoeff)⟩

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
  have hroots : ∀ {p : K[X]} (c : Fin d → K), p.degree = d →
      p = C p.leadingCoeff * ∏ i, (X - C (c i)) → p.roots = Finset.univ.val.map c := by
    intro p c hp hpc
    have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 (ne_zero_of_degree_gt (n := ⊥)
      (hp ▸ WithBot.bot_lt_coe d))
    rw [hpc, roots_C_mul _ hlc, Finset.prod_eq_multiset_prod,
      ← roots_multiset_prod_X_sub_C (Finset.univ.val.map c), Multiset.map_map, Function.comp_def]
  obtain ⟨e, he, hed⟩ := exists_bijOn_roots_toFinset_of_norm_sub_lt
    (hroots a hdeg.self_of_nhds hfa) (hroots b hx hgb) hab
    (fun z hz w hw hzw => by linarith [hsep z hz w hw hzw, min_le_right ε r]) hxcard
  exact ⟨e, he, fun z hz => ⟨(hed z hz).1.trans_le (min_le_left ε r), (hed z hz).2⟩⟩

end Continuity

end Polynomial
