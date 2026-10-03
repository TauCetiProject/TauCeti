/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import TauCeti.Analysis.Polynomial.ContinuityOfRoots

import TauCeti.Topology.MetricSpace.SeparatedBalls

/-!
# Real roots of a family of real polynomials

Let `F x` be real polynomials of fixed degree whose coefficients depend continuously on a
parameter `x`. Nearby members of the family can lose real roots, or gain them, when two real roots
collide and leave the real line as a pair of complex conjugates, or when such a pair lands on the
real line. Both events lower the number of distinct complex roots at the collision. This file
shows that if the number of distinct **complex** roots of `F x` does not exceed that of `F x₀` for
`x` near `x₀`, then the distinct real roots of `F x` correspond bijectively to those of `F x₀`,
each moved by an arbitrarily small amount and with its multiplicity unchanged. In particular the
number of distinct real roots is then locally constant.

The proof applies `Polynomial.eventually_exists_bijOn_roots_toFinset` to the complex roots and uses
complex conjugation. The disc around a real root of `F x₀` contains a single distinct root of
`F x`, and the conjugate of that root is a root in the same disc, so it is real. The discs around
the non-real roots of `F x₀` are chosen to miss the real line, so they contain no real roots.

## Main results

* `Polynomial.eventually_exists_bijOn_roots_toFinset_of_card_aroots_le`: the distinct real roots
  of `F x` and `F x₀` correspond bijectively, nearby and with the same multiplicities.
* `Polynomial.eventually_card_roots_toFinset_eq_of_card_aroots_le`: the number of distinct real
  roots is locally constant.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Springer, 2006, §5.1 (continuity of the roots of a polynomial with respect to its coefficients).
-/

public section

open Filter Metric Topology TauCeti ComplexConjugate

namespace Polynomial

/-- **Real roots under a matching of complex roots.** Let `e` be a bijection from the distinct
complex roots of a real polynomial `f` onto those of a real polynomial `g`, moving each root by less
than `ρ` and preserving multiplicities. If the roots of `f` are more than `2 * ρ` apart and every
point within `ρ` of a non-real root of `f` is non-real, then `e` restricts to such a bijection
between the distinct real roots. -/
private theorem exists_bijOn_roots_toFinset_of_bijOn_aroots {f g : ℝ[X]} {ρ : ℝ} {e : ℂ → ℂ}
    (hsep : ∀ z ∈ (f.aroots ℂ).toFinset, ∀ w ∈ (f.aroots ℂ).toFinset, z ≠ w → 2 * ρ < dist z w)
    (him : ∀ z ∈ (f.aroots ℂ).toFinset, z.im ≠ 0 → ∀ w, dist w z < ρ → w.im ≠ 0)
    (he : Set.BijOn e (f.aroots ℂ).toFinset (g.aroots ℂ).toFinset)
    (hed : ∀ z ∈ f.aroots ℂ, ‖e z - z‖ < ρ ∧
      (g.map (algebraMap ℝ ℂ)).rootMultiplicity (e z) =
        (f.map (algebraMap ℝ ℂ)).rootMultiplicity z) :
    ∃ e' : ℝ → ℝ, Set.BijOn e' f.roots.toFinset g.roots.toFinset ∧
      ∀ t ∈ f.roots, |e' t - t| < ρ ∧ g.rootMultiplicity (e' t) = f.rootMultiplicity t := by
  have hmem : ∀ {p : ℝ[X]} {t : ℝ}, t ∈ p.roots ↔ (t : ℂ) ∈ (p.aroots ℂ).toFinset := by
    intro p t
    rw [Multiset.mem_toFinset, mem_aroots, mem_roots', IsRoot.def, ← Complex.coe_algebraMap,
      aeval_algebraMap_apply_eq_algebraMap_eval, Complex.coe_algebraMap, Complex.ofReal_eq_zero]
  have hed' : ∀ t ∈ f.roots, ‖e t - t‖ < ρ := fun t ht =>
    (hed t (Multiset.mem_toFinset.1 (hmem.1 ht))).1
  -- the partner of a real root is real: its conjugate is a root of `g` in the same disc
  have hreal : ∀ t ∈ f.roots, ((e t).re : ℂ) = e t := by
    intro t ht
    rw [← Complex.conj_eq_iff_re]
    have hconj : conj (e t) ∈ (g.aroots ℂ).toFinset := by
      have := he.mapsTo (hmem.1 ht)
      simp only [Finset.mem_coe, Multiset.mem_toFinset, mem_aroots] at this ⊢
      exact ⟨this.1, by rw [aeval_conj, this.2, map_zero]⟩
    obtain ⟨z, hz, hez⟩ := he.surjOn hconj
    have hzt : dist z t < 2 * ρ := by
      have hc : conj (e t) - t = conj (e t - t) := by rw [map_sub, Complex.conj_ofReal]
      rw [dist_eq_norm]
      calc ‖z - t‖ = ‖(z - e z) + (conj (e t) - t)‖ := by rw [← hez, sub_add_sub_cancel]
        _ ≤ ‖e z - z‖ + ‖e t - t‖ := (norm_add_le _ _).trans_eq
          (by rw [norm_sub_rev z, hc, Complex.norm_conj])
        _ < 2 * ρ := by linarith [(hed z (Multiset.mem_toFinset.1 hz)).1, hed' t ht]
    have hzt' : z = t := by
      by_contra hne
      exact (hsep z hz t (hmem.1 ht) hne).not_gt hzt
    rw [← hez, hzt']
  -- the partner of a non-real root is not real, since its disc misses the real line
  have hnonreal : ∀ z ∈ (f.aroots ℂ).toFinset, z.im ≠ 0 → (e z).im ≠ 0 := fun z hz hzim =>
    him z hz hzim _ ((dist_eq_norm _ _).trans_lt (hed z (Multiset.mem_toFinset.1 hz)).1)
  refine ⟨fun t => (e t).re, ⟨fun t ht => ?_, fun t ht t' ht' htt' => ?_, fun s hs => ?_⟩,
    fun t ht => ⟨?_, ?_⟩⟩
  · simp only [Finset.mem_coe, Multiset.mem_toFinset] at ht ⊢
    exact hmem.2 (by rw [hreal t ht]; exact he.mapsTo (hmem.1 ht))
  · simp only [Finset.mem_coe, Multiset.mem_toFinset] at ht ht'
    have : e t = e t' := by rw [← hreal t ht, ← hreal t' ht']; exact congrArg _ htt'
    exact Complex.ofReal_injective (he.injOn (hmem.1 ht) (hmem.1 ht') this)
  · simp only [Finset.mem_coe, Multiset.mem_toFinset] at hs
    obtain ⟨z, hz, hez⟩ := he.surjOn (hmem.1 hs)
    have hzre : (z.re : ℂ) = z := Complex.conj_eq_iff_re.1 <| Complex.conj_eq_iff_im.2 <| by
      by_contra h
      exact hnonreal z hz h (by rw [hez, Complex.ofReal_im])
    refine ⟨z.re, Finset.mem_coe.2 (Multiset.mem_toFinset.2 (hmem.2 (hzre ▸ hz))), ?_⟩
    simp only [hzre, hez, Complex.ofReal_re]
  · have := hed' t ht
    rwa [← hreal t ht, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this
  · rw [eq_rootMultiplicity_map (algebraMap ℝ ℂ).injective,
      eq_rootMultiplicity_map (algebraMap ℝ ℂ).injective t, Complex.coe_algebraMap, hreal t ht]
    exact (hed t (Multiset.mem_toFinset.1 (hmem.1 ht))).2

/-- **Real roots in a family.** Let `F x` be real polynomials of degree `d`, near `x₀`, whose
coefficients of index at most `d` are continuous at `x₀`, and suppose that near `x₀` the polynomial
`F x` has at most as many distinct complex roots as `F x₀`. Then for `x` near `x₀` there is a
bijection `e` from the distinct real roots of `F x₀` onto those of `F x` that moves each root by
less than `ε` and preserves its multiplicity. -/
theorem eventually_exists_bijOn_roots_toFinset_of_card_aroots_le {B : Type*}
    [TopologicalSpace B] {F : B → ℝ[X]} {x₀ : B} {d : ℕ}
    (hF : ∀ i ≤ d, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).degree = d)
    (hcard : ∀ᶠ x in 𝓝 x₀, ((F x).aroots ℂ).toFinset.card ≤ ((F x₀).aroots ℂ).toFinset.card)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∃ e : ℝ → ℝ,
      Set.BijOn e (F x₀).roots.toFinset (F x).roots.toFinset ∧
        ∀ t ∈ (F x₀).roots,
          |e t - t| < ε ∧ (F x).rootMultiplicity (e t) = (F x₀).rootMultiplicity t := by
  -- choose the radius so that the discs around the distinct complex roots of `F x₀` are pairwise
  -- disjoint and the discs around the non-real ones miss the real line
  obtain ⟨r, hr, hU, hsep⟩ := exists_pos_closedBall_subset_and_lt_dist
    (T := ((F x₀).aroots ℂ).toFinset) (U := fun z => if z.im = 0 then Set.univ else {w | w.im ≠ 0})
    fun z _ => by
      split_ifs with hz
      · exact univ_mem
      · exact (isOpen_ne_fun Complex.continuous_im continuous_const).mem_nhds hz
  have hρ : min ε r ≤ r := min_le_right ε r
  have hG : ∀ i ≤ d, ContinuousAt (fun x => ((F x).map (algebraMap ℝ ℂ)).coeff i) x₀ :=
    fun i hi => by
      simpa only [coeff_map, Complex.coe_algebraMap, Function.comp_def] using
        Complex.continuous_ofReal.continuousAt.comp (hF i hi)
  have hGdeg : ∀ᶠ x in 𝓝 x₀, ((F x).map (algebraMap ℝ ℂ)).degree = d :=
    hdeg.mono fun x hx => by rw [degree_map, hx]
  filter_upwards [eventually_exists_bijOn_roots_toFinset hG hGdeg hcard (lt_min hε hr)]
    with x ⟨e, he, hed⟩
  simp only [← aroots_def] at he hed
  obtain ⟨e', he', hed'⟩ := exists_bijOn_roots_toFinset_of_bijOn_aroots
    (fun z hz w hw hzw => by linarith [hsep z hz w hw hzw])
    (fun z hz hzim w hw => by
      simpa only [hzim, ↓reduceIte, Set.mem_ofPred_eq] using
        hU z hz (mem_closedBall.2 (hw.le.trans hρ)))
    he hed
  exact ⟨e', he', fun t ht => ⟨(hed' t ht).1.trans_le (min_le_left ε r), (hed' t ht).2⟩⟩

/-- **Local constancy of the number of real roots.** Let `F x` be real polynomials of degree `d`,
near `x₀`, whose coefficients of index at most `d` are continuous at `x₀`, and suppose that near
`x₀` the polynomial `F x` has at most as many distinct complex roots as `F x₀`. Then for `x` near
`x₀` the polynomials `F x` and `F x₀` have the same number of distinct real roots. -/
theorem eventually_card_roots_toFinset_eq_of_card_aroots_le {B : Type*} [TopologicalSpace B]
    {F : B → ℝ[X]} {x₀ : B} {d : ℕ} (hF : ∀ i ≤ d, ContinuousAt (fun x => (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).degree = d)
    (hcard : ∀ᶠ x in 𝓝 x₀, ((F x).aroots ℂ).toFinset.card ≤ ((F x₀).aroots ℂ).toFinset.card) :
    ∀ᶠ x in 𝓝 x₀, (F x).roots.toFinset.card = (F x₀).roots.toFinset.card := by
  filter_upwards [eventually_exists_bijOn_roots_toFinset_of_card_aroots_le hF hdeg hcard
    one_pos] with x ⟨e, he, _⟩
  exact (Finset.card_nbij e he.mapsTo he.injOn he.surjOn).symm

end Polynomial
