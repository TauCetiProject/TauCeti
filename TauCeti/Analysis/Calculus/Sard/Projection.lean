/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Sard.LowDimension
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Directions avoiding the secants and tangents of a map

Let `f : E → F` be a `C²` map between finite-dimensional real normed spaces with
`2 * dim E + 1 < dim F`. Then some vector `v` of `F` is neither a multiple of a secant
`f x - f y` nor a tangent vector `Df(x) w` of `f`
(`ContDiff.exists_forall_smul_sub_ne_and_fderiv_ne`). Indeed the cone of secants is the range of
the differentiable map `(x, y, c) ↦ c • (f x - f y)` on `E × E × ℝ`, and the tangent vectors form
the range of `(x, w) ↦ Df(x) w` on `E × E`; both sources have dimension smaller than `dim F`, so
both ranges are null for Haar measure by the lower-dimensional case of Sard's lemma
(`Differentiable.addHaar_range_eq_zero_of_finrank_lt_finrank`).

This is the choice of direction in Whitney's projection argument: for an injective immersion `f`,
projecting `F` linearly along such a direction `v` onto a complementary hyperplane keeps `f`
an injective immersion, and so does every stage of the straight-line motion
`f - t • φ (f) • v`, for a linear form `φ` with `φ v = 1`.

## Main results

* `ContDiff.exists_forall_smul_sub_ne_and_fderiv_ne`: a vector which is neither on a secant line
  nor a tangent vector of a `C²` map, when `2 * dim E + 1 < dim F`.
* `ContDiff.exists_forall_sub_eq_smul_and_deriv_ne`: the curve case, for an injective `C²`
  immersion of the line in dimension at least four.

## References

* H. Whitney, *Differentiable manifolds*, Ann. of Math. 37 (1936), 645–680.
* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer (1976),
  Chapter 1, §3 (the projection argument for embeddings into Euclidean space).
-/

public section

open Function MeasureTheory Module Set

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **A direction avoiding the secants and tangents.** For a `C²` map `f : E → F` between
finite-dimensional real normed spaces with `2 * dim E + 1 < dim F`, some vector `v` lies on no
line spanned by a secant `f x - f y`, and is no tangent vector `Df(x) w`. In particular `v ≠ 0`. -/
theorem ContDiff.exists_forall_smul_sub_ne_and_fderiv_ne {f : E → F} (hf : ContDiff ℝ 2 f)
    (hEF : 2 * finrank ℝ E + 1 < finrank ℝ F) :
    ∃ v : F, (∀ x y (c : ℝ), c • (f x - f y) ≠ v) ∧ ∀ x w, fderiv ℝ f x w ≠ v := by
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  let μ : Measure F := Measure.addHaar
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hsec : μ (range fun q : E × E × ℝ => q.2.2 • (f q.1 - f q.2.1)) = 0 := by
    refine Differentiable.addHaar_range_eq_zero_of_finrank_lt_finrank μ ?_ ?_
    · exact (differentiable_snd.comp differentiable_snd).smul
        ((hd.comp differentiable_fst).sub (hd.comp (differentiable_fst.comp differentiable_snd)))
    · simp only [finrank_prod, finrank_self]
      omega
  have htan : μ (range fun q : E × E => fderiv ℝ f q.1 q.2) = 0 := by
    refine Differentiable.addHaar_range_eq_zero_of_finrank_lt_finrank μ ?_ ?_
    · exact (((hf.fderiv_right (m := 1) (by norm_num)).comp contDiff_fst).clm_apply
        contDiff_snd).differentiable (by norm_num)
    · simp only [finrank_prod]
      omega
  obtain ⟨v, hv⟩ : ((range fun q : E × E × ℝ => q.2.2 • (f q.1 - f q.2.1)) ∪
      range fun q : E × E => fderiv ℝ f q.1 q.2)ᶜ.Nonempty := by
    rw [nonempty_compl]
    intro h
    have h0 := measure_union_null hsec htan
    rw [h] at h0
    exact NeZero.ne μ (Measure.measure_univ_eq_zero.mp h0)
  simp only [mem_compl_iff, mem_union, mem_range, not_or, not_exists, Prod.forall] at hv
  exact ⟨v, fun x y c => hv.1 x y c, fun x w => hv.2 x w⟩

/-- **The projection direction for an arc.** An injective `C²` immersion `γ` of the line in a real
normed space of dimension at least four has a nonzero direction `d` such that no secant
`γ s - γ s'` with `s ≠ s'` and no velocity `γ' s` is a multiple of `d`. -/
theorem ContDiff.exists_forall_sub_eq_smul_and_deriv_ne {γ : ℝ → F} (hγ : ContDiff ℝ 2 γ)
    (hF : 4 ≤ finrank ℝ F) (hinj : Injective γ) (hγ' : ∀ s, deriv γ s ≠ 0) :
    ∃ d : F, d ≠ 0 ∧ (∀ s s' (c : ℝ), γ s - γ s' = c • d → s = s') ∧
      ∀ s (c : ℝ), deriv γ s ≠ c • d := by
  obtain ⟨d, hsec, htan⟩ := hγ.exists_forall_smul_sub_ne_and_fderiv_ne
    (by simp only [finrank_self]; omega)
  refine ⟨d, fun hd => hsec 0 0 0 (by simp [hd]), fun s s' c h => ?_, fun s c h => ?_⟩
  · by_contra hne
    have hc : c ≠ 0 := by
      rintro rfl
      exact sub_ne_zero.2 (hinj.ne hne) (by simpa using h)
    exact hsec s s' c⁻¹ (by rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul])
  · have hc : c ≠ 0 := by
      rintro rfl
      exact hγ' s (by simpa using h)
    refine htan s c⁻¹ ?_
    rw [← toSpanSingleton_deriv]
    simp [h, smul_smul, inv_mul_cancel₀ hc]
