/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GeodesicEdges
public import TauCeti.GroupTheory.HaagerupProperty.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Set.Finite.List

/-!
# Free groups have the Haagerup property

Haagerup's theorem: the free group on any countable set of generators, in particular `F_n` for
`2 ≤ n ≤ ∞`, has the Haagerup property.

Number the generators injectively by `n : ι → ℕ` and give the letter `of i` the weight `n i + 1`.
The weighted word length `W g` is the sum of the weights of the letters of the reduced word of
`g`. For `0 < r < 1` the function `g ↦ r ^ W g` is the product of the weights `r ^ (n i + 1)` over
the letters of `g`, so it is positive definite by
`FreeGroup.posSemidef_prod_map_toWord_inv_mul`. It vanishes at infinity because only finitely
many reduced words have weighted length below any bound; with unit weights this would fail for
infinitely many generators, since then infinitely many elements have word length `1`. As `r → 1`
it tends to `1` pointwise.

## Main declarations

* `TauCeti.hasHaagerupProperty_freeGroup`: free groups of countable rank have the Haagerup
  property.

## References

* U. Haagerup, *An example of a non nuclear C*-algebra, which has the metric approximation
  property*, Invent. Math. 50 (1979), 279–293.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Examples 16.1.2.
-/

public section

open Filter Topology
open scoped ComplexOrder

namespace TauCeti

/-- **Haagerup's theorem.** The free group on a countable set of generators has the Haagerup
property. -/
theorem hasHaagerupProperty_freeGroup (ι : Type*) [Countable ι] :
    HasHaagerupProperty (FreeGroup ι) := by
  classical
  obtain ⟨n, hn⟩ := exists_injective_nat ι
  -- The weighted word length: the letter `of i` has weight `n i + 1`.
  let W : FreeGroup ι → ℕ := fun g => (g.toWord.map fun x => n x.1 + 1).sum
  -- Only finitely many elements have weighted length below a given bound.
  have hW : Tendsto W cofinite atTop := by
    refine tendsto_atTop.2 fun N => eventually_cofinite.2 ?_
    let T : Set (ι × Bool) := {x | n x.1 < N}
    have hT : T.Finite :=
      (((Set.finite_Iio N).preimage hn.injOn).prod Set.finite_univ).subset fun x hx => ⟨hx, trivial⟩
    have : Finite T := hT.to_subtype
    have hlists : {l : List (ι × Bool) | l.length ≤ N ∧ ∀ x ∈ l, x ∈ T}.Finite := by
      refine ((List.finite_length_le T N).image (List.map Subtype.val)).subset ?_
      rintro l ⟨hl, hmem⟩
      exact ⟨l.attachWith (· ∈ T) hmem, by simpa using hl, List.attachWith_map_subtype_val hmem⟩
    refine (hlists.preimage FreeGroup.toWord_injective.injOn).subset fun g hg => ?_
    replace hg : (g.toWord.map fun x => n x.1 + 1).sum < N := not_le.1 hg
    refine ⟨?_, fun x hx => ?_⟩
    · have := List.length_le_sum_of_one_le (g.toWord.map fun x => n x.1 + 1) (by simp)
      simp only [List.length_map] at this
      exact (this.trans hg.le)
    · have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun x => n x.1 + 1) hx)
      exact show n x.1 < N by omega
  have hpow (r : ℝ) (g : FreeGroup ι) :
      r ^ W g = (g.toWord.map fun x => r ^ (n x.1 + 1)).prod := by
    simp only [W]
    induction g.toWord with
    | nil => simp
    | cons x l ih => rw [List.map_cons, List.sum_cons, pow_add, ih, List.map_cons, List.prod_cons]
  refine hasHaagerupProperty_iff.2 fun F ε hε => ?_
  -- For `r` close to `1`, the function `g ↦ r ^ W g` is close to `1` on `F`.
  have hnear : ∀ᶠ r in 𝓝[<] (1 : ℝ), ∀ g ∈ F, ‖((r ^ W g : ℝ) : ℂ) - 1‖ < ε := by
    refine (eventually_all_finset F).2 fun g _ => ?_
    have hcont : Tendsto (fun r : ℝ => ((r ^ W g : ℝ) : ℂ)) (𝓝[<] 1) (𝓝 1) :=
      ((Complex.continuous_ofReal.comp (continuous_pow (W g))).tendsto' 1 1 (by simp)).mono_left
        nhdsWithin_le_nhds
    filter_upwards [hcont (Metric.ball_mem_nhds 1 hε)] with r hr
    simpa [dist_eq_norm] using hr
  obtain ⟨r, hrF, hr0, hr1⟩ := (hnear.and (Ioo_mem_nhdsLT zero_lt_one)).exists
  refine ⟨fun g => ((r ^ W g : ℝ) : ℂ), ?_, by simp [W], ?_, hrF⟩
  · have hρ (i : ι) : |r ^ (n i + 1)| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_one₀ hr0.le hr1.le
    have hφ : (Matrix.of fun g h : FreeGroup ι => ((r ^ W (g⁻¹ * h) : ℝ) : ℂ)) =
        fun g h => ((((g⁻¹ * h).toWord.map fun x => r ^ (n x.1 + 1)).prod : ℝ) : ℂ) := by
      ext g h
      rw [Matrix.of_apply, hpow]
    rw [hφ]
    exact FreeGroup.posSemidef_prod_map_toWord_inv_mul _ hρ
  · exact (Complex.continuous_ofReal.tendsto' 0 0 Complex.ofReal_zero).comp
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).comp hW)

end TauCeti
