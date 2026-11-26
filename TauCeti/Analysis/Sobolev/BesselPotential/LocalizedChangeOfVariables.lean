/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.ChangeOfVariables
public import TauCeti.Analysis.Sobolev.BesselPotential.Multiplication
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Geometry.Manifold.Diffeomorph.Germ

/-!
# Localized changes of variables in Bessel-potential spaces

Let `e` be a smooth open partial homeomorphism of a finite-dimensional real inner product space
`E` with smooth inverse, such as a transition map between two charts of a manifold, and let `θ` be
a smooth function with compact support in the source of `e`. This file shows that the operator
`u ↦ θ · (u ∘ e)`, extended by `0` off the source, is bounded on Schwartz functions in the `H^s`
norm, for every real `s`
(`BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp`). These are the
estimates comparing the readings of a function on a manifold in two overlapping charts, through
which Sobolev estimates proved in charts are patched together on a manifold.

## The argument

The pullback along a bijection `Φ` of `E` with bounded derivatives is an isomorphism of `H^s`
(`BesselPotentialSpace.compCLE`), and multiplication by a Schwartz function is bounded on `H^s`
(`BesselPotentialSpace.smulLeftCLM`). Near each point of its source, `e` agrees with such a
bijection (`TauCeti.exists_equiv_eventuallyEq_of_det_fderiv_ne_zero`). A finite partition of unity
`χᵢ` on the support of `θ`, subordinate to the open sets where `e` agrees with bijections `Φᵢ`,
writes `θ · (u ∘ e)` as the finite sum `∑ᵢ (θ χᵢ) · (u ∘ Φᵢ)`, which is the image of `u` under a
bounded operator on `H^s`.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §1
  (invariance of `H^s` under diffeomorphisms, and its localization).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  Appendix B.1.
-/

public section

noncomputable section

namespace BesselPotentialSpace

open MeasureTheory TemperedDistribution Filter Set
open scoped ENNReal SchwartzMap BesselPotentialSpace ContDiff

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- **Localized changes of variables as finite sums.** Under the hypotheses of
`BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp`, there are
finitely many Schwartz functions `φ x` and bijections `Φ x` of `E` that are smooth with smooth
inverses with bounded derivatives of every positive order, such that `θ · (u ∘ e)` is
`∑ x, φ x · (u ∘ Φ x)` for every function `u`. -/
private theorem exists_sum_smul_comp_eq_smul_comp {e : OpenPartialHomeomorph E E}
    (he : ContDiffOn ℝ ∞ e e.source) (he' : ContDiffOn ℝ ∞ e.symm e.target) {θ : E → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) (hθe : tsupport θ ⊆ e.source) :
    ∃ (t : Finset e.source) (Φ : e.source → E ≃ E) (φ : e.source → 𝓢(E, ℂ)),
      (∀ x, ContDiff ℝ ∞ (Φ x) ∧ ContDiff ℝ ∞ (Φ x).symm ∧
        (∀ k, 1 ≤ k → ∃ C, ∀ y, ‖iteratedFDeriv ℝ k (Φ x) y‖ ≤ C) ∧
        (∀ k, 1 ≤ k → ∃ C, ∀ y, ‖iteratedFDeriv ℝ k (Φ x).symm y‖ ≤ C)) ∧
      ∀ (u : E → F) y, θ y • u (e y) = ∑ x ∈ t, φ x y • u (Φ x y) := by
  classical
  -- Near each point `x` of the source, `e` agrees with a bijection `Φ x` of `E` whose derivatives
  -- are bounded.
  choose Φ hΦ hΨ hΦb hΨb hΦe using fun x : e.source ↦
    TauCeti.exists_equiv_eventuallyEq_of_det_fderiv_ne_zero
      (eventually_of_mem (e.open_source.mem_nhds x.property) fun y hy ↦
        he.contDiffAt (e.open_source.mem_nhds hy))
      (e.det_fderiv_ne_zero_of_contDiffOn he he' (by simp) x.property)
  -- A finite partition of unity `χ x` on the support of `θ`, with `Φ x = e` on the support of
  -- `χ x`; the pieces `θ χ x` of `θ` are complex Schwartz functions.
  obtain ⟨t, χ, hχ, -, -, hsum⟩ := hθc.isCompact.exists_contDiff_tsupport_subset_finset_sum_eq_one
    (U := fun x : e.source ↦ interior {y | Φ x y = e y}) (fun _ ↦ isOpen_interior)
    fun y hy ↦ mem_iUnion.2 ⟨⟨y, hθe hy⟩, mem_interior_iff_mem_nhds.2 (hΦe ⟨y, hθe hy⟩)⟩
  have hχΦ (x : e.source) (y : E) (hy : χ x y ≠ 0) : Φ x y = e y :=
    interior_subset ((hχ x).2.2 (subset_tsupport _ hy))
  let φ (x : e.source) : 𝓢(E, ℂ) :=
    (hθc.mul_right.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (hθ.mul (hχ x).1))
  have hφ (x : e.source) (y : E) : φ x y = ((θ y * χ x y : ℝ) : ℂ) := (rfl)
  refine ⟨t, Φ, φ, fun x ↦ ⟨hΦ x, hΨ x, hΦb x, hΨb x⟩, fun u y ↦ ?_⟩
  simp only [hφ]
  rw [Finset.sum_congr rfl fun x _ ↦ show ((θ y * χ x y : ℝ) : ℂ) • u (Φ x y) =
      ((θ y * χ x y : ℝ) : ℂ) • u (e y) by
    by_cases h : χ x y = 0
    · simp [h]
    · rw [hχΦ x y h], ← Finset.sum_smul, ← Complex.ofReal_sum, ← Finset.mul_sum]
  by_cases hy : y ∈ tsupport θ
  · rw [hsum y hy, mul_one, Complex.coe_smul]
  · simp [image_eq_zero_of_notMem_tsupport hy]

/-- **Localized changes of variables are bounded on `H^s`.** Let `e` be a smooth open partial
homeomorphism of `E` with smooth inverse and `θ` a smooth function with compact support in the
source of `e`. Then `u ↦ θ · (u ∘ e)`, extended by `0` off the source, is bounded on Schwartz
functions in the `H^s` norm, for every real `s`: there is a constant `C` with
`‖v‖_{H^s} ≤ C ‖u‖_{H^s}` whenever `v = θ · (u ∘ e)`. -/
theorem exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp {e : OpenPartialHomeomorph E E}
    (he : ContDiffOn ℝ ∞ e e.source) (he' : ContDiffOn ℝ ∞ e.symm e.target) {θ : E → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) (hθe : tsupport θ ⊆ e.source) (s : ℝ) :
    ∃ C, ∀ u v : 𝓢(E, F), (∀ x, v x = θ x • u (e x)) →
      ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 v‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
  obtain ⟨t, Φ, φ, hΦ, hsum⟩ := exists_sum_smul_comp_eq_smul_comp (F := F) he he' hθ hθc hθe
  choose hΦs hΨs hΦb hΨb using hΦ
  have hΦt (x : e.source) :=
    Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_of_pos (hΦs x) (hΦb x)
  have hΨt (x : e.source) :=
    Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_of_pos (hΨs x) (hΨb x)
  -- `v` is the image of `u` under the bounded operator `∑ x, φ x · Φ x^*`.
  let T : H^{s}(E, F) →L[ℂ] H^{s}(E, F) := ∑ x ∈ t, smulLeftCLM s (φ x) ∘L
    (compCLE F ENNReal.one_lt_two ENNReal.ofNat_ne_top s (Φ x) (hΦt x) (hΨt x)
      (fun k hk _ ↦ hΦb x k hk) (fun k hk _ ↦ hΨb x k hk) : H^{s}(E, F) →L[ℂ] H^{s}(E, F))
  refine ⟨‖T‖, fun u v hv ↦ ?_⟩
  have hvT : v = ∑ x ∈ t, SchwartzMap.smulLeftCLM F (φ x : E → ℂ)
      (SchwartzMap.compCLM ℂ (hΦt x) ((hΨt x).exists_norm_le_of_leftInverse (Φ x).left_inv)
        u) := by
    ext y
    simp only [sum_apply, SchwartzMap.smulLeftCLM_apply_apply
      (SchwartzMap.hasTemperateGrowth _), SchwartzMap.compCLM_apply, Function.comp_apply, hv,
      hsum]
  have hT : T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM s 2 v := by
    simp only [T, hvT, sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, compCLE_toBesselPotentialSpaceCLM, map_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ext ?_
    simp [smulLeftCLM_toTemperedDistributionCLM_eq]
  rw [← hT]
  exact T.le_opNorm _

end BesselPotentialSpace
