/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Complex.ImDilation
public import TauCeti.Analysis.Sobolev.Trace.Reflection.Higher
import TauCeti.Analysis.Sobolev.Trace.Reflection.Basic
import TauCeti.LinearAlgebra.Complex.Module
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Higher-order reflection of half-disc Sobolev maps

For an open `Ω ⊆ ℂ`, the relatively open set `Ω ∩ {0 ≤ im}` of the closed upper half-plane carries
the local Sobolev class `TauCeti.MemWkpLoc p (Ω ∩ {0 ≤ im}) k`: weak derivatives on its interior
`Ω ∩ {0 < im}` (`TauCeti.interior_inter_setOf_im_nonneg`), with `Lᵖ` bounds on compact sets reaching
the real axis. This file extends such maps across the axis by the order-`k` higher reflection

`u (s - t i) = ∑ j, c j • u (s + t / (j + 1) i)` for `t > 0`,

whose weights `c = TauCeti.higherReflectionCoeff k` solve the Vandermonde system
`∑ j, c j (-1 / (j + 1)) ^ i = 1` for `i < k`. On each normal slice it is
`TauCeti.higherReflection` (`TauCeti.planarReflection_higherReflectionCoeff`); at `k = 1` it is the
even reflection and at `k = 2` it extends `z.im` to itself (`TauCeti.planarReflection_two_im`).

The construction `TauCeti.planarReflection d g` allows arbitrary weights `d`. Its weak
derivative across the axis is the reflection of the derivative: tangentially with the same
weights, and in the normal direction with the weights `d j * higherReflectionNode j`, provided
`∑ j, d j = 1` (`TauCeti.HasWeakFDerivOn.planarReflection`). No boundary condition on `g` is used:
the moment condition matches the one-sided values. The proof changes variables on each reflected
copy (`TauCeti.imDilation`) and integrates by parts up to the real axis, against test functions cut
off near the axis by the pulled-back `TauCeti.normalCutoff`;
in the normal direction the boundary layer is controlled because the combined test function
vanishes on the axis. Iterating, the moment conditions of order below `k` give the order-`k`
statement.

## Main declarations

* `TauCeti.planarReflection`, `TauCeti.planarReflectionFDeriv`: the reflection with weights and
  its candidate weak derivative.
* `TauCeti.HasWeakLineDerivOn.planarReflection_one`, `TauCeti.HasWeakLineDerivOn.planarReflection_I`
  and `TauCeti.HasWeakFDerivOn.planarReflection`: weak gluing across the real axis.
* `TauCeti.MemWkpLoc.planarReflection_higherReflectionCoeff`: a map in `W^{k,p}_loc(Ω ∩ {0 ≤ im})`
  extends to a map in `W^{k,p}_loc(Ω)` when the node dilations map the lower part of `Ω` into `Ω`;
  the cases of discs centred on the real axis and of the whole plane are
  `TauCeti.MemWkpLoc.planarReflection_higherReflectionCoeff_ball` and
  `TauCeti.MemWkpLoc.planarReflection_higherReflectionCoeff_univ`.
* `TauCeti.eLpNorm_planarReflection_le`: the `Lᵖ(Ω)` bound by the `Lᵖ(Ω ∩ {0 ≤ im})` norm, with the
  constant `TauCeti.higherReflectionBound k p` for the Vandermonde weights.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 5.19 (extension by higher
  order reflection).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter Complex
open scoped ContDiff Topology Distributions ENNReal Polynomial

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Reflection with prescribed weights -/

/-- The dilation factor of each node is nonzero. -/
theorem higherReflectionNode_ne_zero {k : ℕ} (j : Fin k) : higherReflectionNode j ≠ 0 :=
  (higherReflectionNode_neg j).ne

/-- Reflection of `g` across the real axis with weights `d j` at the normal dilations
`higherReflectionNode j = -1 / (j + 1)`: it is `g z` for `0 ≤ z.im`, and
`∑ j, d j • g (z.re + higherReflectionNode j * z.im * I)` for `z.im < 0`, which only samples `g` in
the upper half-plane. With `d = higherReflectionCoeff k` this is the order-`k` higher reflection,
`TauCeti.planarReflection_higherReflectionCoeff`. -/
def planarReflection {k : ℕ} (d : Fin k → ℝ) (g : ℂ → F) (z : ℂ) : F :=
  if 0 ≤ z.im then g z else ∑ j, d j • g (imDilation (higherReflectionNode j) z)

variable {k : ℕ} {d : Fin k → ℝ} {g : ℂ → F}

@[simp]
theorem planarReflection_of_nonneg (d : Fin k → ℝ) (g : ℂ → F) {z : ℂ} (hz : 0 ≤ z.im) :
    planarReflection d g z = g z := ite_eq_left hz

@[simp]
theorem planarReflection_of_neg (d : Fin k → ℝ) (g : ℂ → F) {z : ℂ} (hz : z.im < 0) :
    planarReflection d g z = ∑ j, d j • g (imDilation (higherReflectionNode j) z) :=
  ite_eq_right hz.not_ge

/-- The two branches of the reflection as indicator functions. -/
theorem planarReflection_eq_indicator (d : Fin k → ℝ) (g : ℂ → F) :
    planarReflection d g = {z : ℂ | 0 ≤ z.im}.indicator g +
      {z : ℂ | z.im < 0}.indicator
        fun z => ∑ j, d j • g (imDilation (higherReflectionNode j) z) := by
  funext z
  by_cases hz : 0 ≤ z.im
  · simp [hz]
  · simp [planarReflection, hz, indicator_of_mem (show z ∈ {z : ℂ | z.im < 0} from not_le.1 hz)]

/-- With the Vandermonde weights, the reflection is the higher reflection of each normal slice
`t ↦ g (z.re + t i)`. -/
theorem planarReflection_higherReflectionCoeff (k : ℕ) (g : ℂ → F) (z : ℂ) :
    planarReflection (higherReflectionCoeff k) g z =
      higherReflection k (fun t => g ⟨z.re, t⟩) z.im := by
  by_cases hz : 0 ≤ z.im
  · simp [hz]
  · rw [planarReflection_of_neg _ _ (not_le.1 hz), higherReflection_of_neg _ _ (not_le.1 hz),
      higherReflectionLower_apply]
    rfl

/-- The order-one reflection is the even reflection across the real axis. -/
theorem planarReflection_higherReflectionCoeff_one (g : ℂ → F) (z : ℂ) :
    planarReflection (higherReflectionCoeff 1) g z = g ⟨z.re, |z.im|⟩ := by
  rw [planarReflection_higherReflectionCoeff, higherReflection_one]

/-- The order-two reflection extends the normal coordinate to itself, while the even
reflection would give its absolute value. -/
theorem planarReflection_two_im :
    planarReflection (higherReflectionCoeff 2) (fun z => z.im) = fun z => z.im := by
  funext z
  rw [planarReflection_higherReflectionCoeff]
  have h := congrFun (higherReflection_eval_eq (k := 2) (Polynomial.X : ℝ[X])
    (by rw [Polynomial.degree_X]; norm_num)) z.im
  simpa using h

/-- The reflection of every nonnegative-side `Lᵖ`-on-compacts map is `Lᵖ` on compacts, provided the
dilations `higherReflectionNode j` map the lower part of `Ω` into `Ω`. -/
theorem MemLpLoc.planarReflection {p : ℝ≥0∞} {Ω : Set ℂ}
    (hΩ : ∀ z ∈ Ω, z.im < 0 → ∀ j : Fin k, imDilation (higherReflectionNode j) z ∈ Ω)
    (hg : MemLpLoc p (Ω ∩ {z : ℂ | 0 ≤ z.im}) g) (d : Fin k → ℝ) :
    MemLpLoc p Ω (planarReflection d g) := by
  refine memLpLoc_iff.2 fun K hKΩ hK => ?_
  have hH : MeasurableSet {z : ℂ | 0 ≤ z.im} := measurableSet_le measurable_const measurable_im
  have hL : MeasurableSet {z : ℂ | z.im < 0} := measurableSet_lt measurable_im measurable_const
  rw [planarReflection_eq_indicator]
  refine MemLp.add ?_ ?_
  · rw [memLp_indicator_iff_restrict hH.nullMeasurableSet, Measure.restrict_restrict hH]
    exact memLpLoc_iff.1 hg _ (fun z hz => ⟨hKΩ hz.2, hz.1⟩)
      (hK.inter_left (isClosed_le continuous_const continuous_im))
  · rw [memLp_indicator_iff_restrict hL.nullMeasurableSet, Measure.restrict_restrict hL]
    refine memLp_finsetSum _ fun j _ => MemLp.const_smul ?_ (d j)
    set K' := K ∩ {z : ℂ | z.im ≤ 0}
    have hK' : IsCompact K' := hK.inter_right (isClosed_le continuous_im continuous_const)
    have hsub : imDilation (higherReflectionNode j) '' K' ⊆ Ω ∩ {z : ℂ | 0 ≤ z.im} := by
      rintro _ ⟨z, ⟨hzK, hz⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rcases (show z.im ≤ 0 from hz).lt_or_eq with hz | hz
        · exact hΩ z (hKΩ hzK) hz j
        · rw [imDilation_of_im_eq_zero _ hz]
          exact hKΩ hzK
      · simpa using mul_nonneg_of_nonpos_of_nonpos (higherReflectionNode_neg j).le hz
    have h := memLpLoc_iff.1 hg _ hsub (hK'.image (imDilation _).continuous)
    rw [← memLp_comp_imDilation_iff (higherReflectionNode_ne_zero j),
      preimage_image_eq _
        (measurableEmbedding_imDilation (higherReflectionNode_ne_zero j)).injective] at h
    refine h.mono_measure (Measure.restrict_mono ?_ le_rfl)
    exact fun z hz => ⟨hz.2, (show z.im < 0 from hz.1).le⟩

/-! ### Integration by parts up to the real axis -/

/-- The coordinates `(z.im, z.re)` of `ℂ`, with the normal coordinate first, as in
`TauCeti.normalHalfSpace`. -/
private def imReCLM : ℂ →L[ℝ] WithLp 2 (ℝ × ℝ) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.toContinuousLinearMap.comp (imCLM.prod reCLM)

private theorem imReCLM_fst (z : ℂ) : (imReCLM z).fst = z.im := rfl

/-- The boundary-layer cutoff `TauCeti.normalCutoff` of slope `n + 1`, pulled back to `ℂ`: zero
where `(n + 1) z.im ≤ 1`, one where `(n + 1) z.im ≥ 2`. -/
private def imCutoff (n : ℕ) (z : ℂ) : ℝ := normalCutoff 0 ((n : ℝ) + 1) (imReCLM z)

private theorem contDiff_imCutoff (n : ℕ) : ContDiff ℝ ∞ (imCutoff n) :=
  (contDiff_normalCutoff 0 _).comp imReCLM.contDiff

private theorem hasFDerivAt_imCutoff (n : ℕ) (z : ℂ) :
    HasFDerivAt (imCutoff n)
      ((deriv Real.smoothTransition (((n : ℝ) + 1) * z.im - 1) * ((n : ℝ) + 1)) • imCLM) z := by
  refine ((hasFDerivAt_normalCutoff 0 _ (imReCLM z)).comp z imReCLM.hasFDerivAt).congr_fderiv ?_
  ext v
  simp [imReCLM_fst]

private theorem imCutoff_eq_zero {n : ℕ} {z : ℂ} (hz : ((n : ℝ) + 1) * z.im ≤ 1) :
    imCutoff n z = 0 :=
  normalCutoff_eq_zero (by simpa [imReCLM_fst] using hz)

private theorem norm_imCutoff_le (n : ℕ) (z : ℂ) : ‖imCutoff n z‖ ≤ 1 := by
  unfold imCutoff
  rw [Real.norm_of_nonneg (normalCutoff_nonneg _ _ _)]
  exact normalCutoff_le_one _ _ _

private theorem tsupport_imCutoff_subset (n : ℕ) : tsupport (imCutoff n) ⊆ {z : ℂ | 0 < z.im} :=
  fun z hz => by
    have h := tsupport_normalCutoff_subset (E := ℝ) 0 (c := (n : ℝ) + 1) (by positivity)
      (tsupport_comp_subset_preimage _ imReCLM.continuous hz)
    simpa [mem_normalHalfSpace, imReCLM_fst] using h

/-- Off the open upper half-plane the cutoff argument is negative, so the cutoff and the
derivative of the transition function vanish there. -/
private theorem imCutoff_arg_neg {n : ℕ} {z : ℂ} (hz : z.im ≤ 0) :
    ((n : ℝ) + 1) * z.im - 1 < 0 := by
  have : ((n : ℝ) + 1) * z.im ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hz
  linarith

private theorem eventually_imCutoff_arg {z : ℂ} (hz : 0 < z.im) :
    ∀ᶠ n : ℕ in atTop, 1 < ((n : ℝ) + 1) * z.im - 1 := by
  have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * z.im - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const hz)
  exact h.eventually_gt_atTop 1

/-- **Integration by parts up to the real axis.** Let `g'` be a weak derivative of `g` in the
direction `v` on the upper part of `Ω`, with `g` and `g'` integrable on compact subsets of
`Ω ∩ {0 ≤ im}`. Then the integration-by-parts identity on the upper half-plane holds against every
smooth compactly supported `χ` whose support meets `{0 ≤ im}` inside `Ω`, provided `v` is tangent to
the real axis or `χ` vanishes on it. -/
private theorem setIntegral_fderiv_smul_eq_neg {Ω : Opens ℂ} {g g' : ℂ → F} {v : ℂ}
    (hgW : HasWeakLineDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) g g' v)
    (hg : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g)
    (hg' : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g')
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ∩ {z : ℂ | 0 ≤ z.im} ⊆ Ω) (hv : v.im = 0 ∨ ∀ x : ℝ, χ x = 0) :
    ∫ z in {z : ℂ | 0 < z.im}, fderiv ℝ χ z v • g z =
      -∫ z in {z : ℂ | 0 < z.im}, χ z • g' z := by
  have := hgW.completeSpace
  set H := {z : ℂ | 0 < z.im} with hHdef
  have hHm : MeasurableSet H := measurableSet_lt measurable_const measurable_im
  set K := tsupport χ ∩ {z : ℂ | 0 ≤ z.im}
  have hK : IsCompact K := hχc.isCompact.inter_right (isClosed_le continuous_const continuous_im)
  have hKU : K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} := fun z hz => ⟨hχΩ hz, hz.2⟩
  have hgK : IntegrableOn g K := memLp_one_iff_integrable.1 (memLpLoc_iff.1 hg K hKU hK)
  have hg'K : IntegrableOn g' K := memLp_one_iff_integrable.1 (memLpLoc_iff.1 hg' K hKU hK)
  -- A continuous factor vanishing off `tsupport χ` makes `g` or `g'` integrable on `H`.
  have hint : ∀ {f : ℂ → ℝ} {h : ℂ → F}, Continuous f → (∀ z ∉ tsupport χ, f z = 0) →
      IntegrableOn h K → IntegrableOn (fun z => f z • h z) H := by
    intro f h hf hf0 hh
    refine ((hh.continuousOn_smul hf.continuousOn hK).of_forall_sdiff_eq_zero
      (measurableSet_le measurable_const measurable_im) fun z hz => ?_).mono_set
        fun z hz => le_of_lt hz
    simp [hf0 z fun h => hz.2 ⟨h, hz.1⟩]
  have hdχ : Continuous fun z => fderiv ℝ χ z v :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdst : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  -- `D n` is `χ` times the derivative of the `n`th cutoff in the direction `v`.
  set D : ℕ → ℂ → ℝ := fun n z => χ z *
    (deriv Real.smoothTransition (((n : ℝ) + 1) * z.im - 1) * (((n : ℝ) + 1) * v.im)) with hD
  have I1 : IntegrableOn (fun z => fderiv ℝ χ z v • g z) H :=
    hint hdχ (fun z hz => by simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) hz]) hgK
  have I3 : IntegrableOn (fun z => χ z • g' z) H :=
    hint hχ.continuous (fun z hz => image_eq_zero_of_notMem_tsupport hz) hg'K
  have I1' (n : ℕ) : IntegrableOn (fun z => (imCutoff n z * fderiv ℝ χ z v) • g z) H :=
    hint ((contDiff_imCutoff n).continuous.mul hdχ)
      (fun z hz => by simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) hz]) hgK
  have I2 (n : ℕ) : IntegrableOn (fun z => D n z • g z) H :=
    hint (hχ.continuous.mul ((hdst.comp ((continuous_const.mul continuous_im).sub
      continuous_const)).mul continuous_const))
      (fun z hz => by simp [hD, image_eq_zero_of_notMem_tsupport hz]) hgK
  have I3' (n : ℕ) : IntegrableOn (fun z => (imCutoff n z * χ z) • g' z) H :=
    hint ((contDiff_imCutoff n).continuous.mul hχ.continuous)
      (fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]) hg'K
  -- The weak derivative identity, tested against `imCutoff n * χ`.
  have key (n : ℕ) : (∫ z in H, (imCutoff n z * fderiv ℝ χ z v) • g z) +
      ∫ z in H, D n z • g z = -∫ z in H, (imCutoff n z * χ z) • g' z := by
    have hθs : tsupport (imCutoff n * χ) ⊆
        (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) : Set ℂ) := by
      intro z hz
      have h1 := tsupport_imCutoff_subset n (tsupport_mul_subset_left hz)
      have h2 := tsupport_mul_subset_right hz
      rw [Opens.coe_interior, interior_inter_setOf_im_nonneg Ω.isOpen]
      exact ⟨hχΩ ⟨h2, show (0 : ℝ) ≤ z.im from le_of_lt h1⟩, h1⟩
    let θ : 𝓓(Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), ℝ) :=
      ⟨imCutoff n * χ, (contDiff_imCutoff n).mul hχ, hχc.mul_left, hθs⟩
    have hθ := hgW.integral_lineDeriv_smul_eq_neg_integral_smul θ
    have hcoe : ((θ : 𝓓(Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), ℝ)) : ℂ → ℝ) =
        imCutoff n * χ := rfl
    have hld (z : ℂ) : lineDeriv ℝ (imCutoff n * χ) z v =
        imCutoff n z * fderiv ℝ χ z v + D n z := by
      rw [((hasFDerivAt_imCutoff n z).mul (hχ.differentiable (by simp) z).hasFDerivAt
        ).hasLineDerivAt v |>.lineDeriv]
      simp only [hD, FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
        imCLM_apply]
      ring
    simp only [hcoe, hld, Pi.mul_apply] at hθ
    have hzero (z : ℂ) (hz : z ∉ H) : imCutoff n z = 0 ∧ D n z = 0 := by
      have hz' : z.im ≤ 0 := not_lt.1 (show ¬ (0 : ℝ) < z.im from hz)
      refine ⟨imCutoff_eq_zero ?_, ?_⟩
      · nlinarith [(by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
      · simp [hD, Real.smoothTransition.deriv_of_neg (imCutoff_arg_neg (n := n) hz')]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := H)
        (f := fun z => (imCutoff n z * fderiv ℝ χ z v + D n z) • g z)
        fun z hz => by simp [hzero z hz],
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := H)
        (f := fun z => (imCutoff n z * χ z) • g' z) fun z hz => by simp [hzero z hz]] at hθ
    rw [← integral_add (I1' n) (I2 n)]
    simpa only [add_smul] using hθ
  -- Pass to the limit `n → ∞` in each of the three integrals.
  have hlimH {f : ℂ → F} (hf : IntegrableOn f H) :
      Tendsto (fun n : ℕ => ∫ z in H, imCutoff n z • f z) atTop (𝓝 (∫ z in H, f z)) := by
    refine tendsto_integral_of_dominated_convergence (fun z => ‖f z‖)
      (fun n => ((contDiff_imCutoff n).continuous.aestronglyMeasurable).smul
        hf.aestronglyMeasurable) hf.norm (fun n => Eventually.of_forall fun z => ?_)
      ((ae_restrict_iff' hHm).2 (Eventually.of_forall fun z hz => ?_))
    · rw [norm_smul]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_imCutoff_le n z)
    · exact tendsto_const_nhds.congr' <| (eventually_imCutoff_arg hz).mono fun n hn => by
        have h2 : 2 ≤ ((n : ℝ) + 1) * ((imReCLM z).fst - 0) := by
          rw [imReCLM_fst]
          linarith
        simp only [imCutoff, normalCutoff_eq_one h2, one_smul]
  have h1 := hlimH I1
  have h3 := hlimH I3
  simp only [smul_smul] at h1 h3
  have h2 : Tendsto (fun n : ℕ => ∫ z in H, D n z • g z) atTop (𝓝 0) := by
    rcases hv with hv | hχ0
    · simp [hD, hv]
    obtain ⟨B, hB⟩ := (Real.smoothTransition.contDiff.continuous_deriv le_rfl).norm
      |>.bddAbove_range_of_hasCompactSupport Real.smoothTransition.hasCompactSupport_deriv.norm
    obtain ⟨M, hM⟩ :=
      (hχ.continuous_fderiv (by simp)).bounded_above_of_compact_support (hχc.fderiv (𝕜 := ℝ))
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB ⟨0, rfl⟩)
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have hbound : Integrable (fun z => (2 * (B * M * |v.im|)) * K.indicator (fun z => ‖g z‖) z)
        (volume.restrict H) :=
      ((IntegrableOn.integrable_indicator (f := fun z => ‖g z‖) hgK.norm
        hK.measurableSet).const_mul _).integrableOn
    have hlim := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : F)) _
      (fun n => (I2 n).aestronglyMeasurable) hbound (fun n => ?_)
      ((ae_restrict_iff' hHm).2 (Eventually.of_forall fun z hz => ?_))
    · simpa using hlim
    · refine (ae_restrict_iff' hHm).2 (Eventually.of_forall fun z hz => ?_)
      have hz : 0 < z.im := hz
      have hb0 : 0 ≤ 2 * (B * M * |v.im|) * K.indicator (fun z => ‖g z‖) z :=
        mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => norm_nonneg _) _)
      by_cases hzK : z ∈ tsupport χ
      swap
      · simpa [hD, image_eq_zero_of_notMem_tsupport hzK] using hb0
      by_cases h2 : 2 < ((n : ℝ) + 1) * z.im
      · simpa [hD, Real.smoothTransition.deriv_of_one_lt
          (by linarith : 1 < ((n : ℝ) + 1) * z.im - 1)]
          using hb0
      push Not at h2
      rw [indicator_of_mem (show z ∈ K from ⟨hzK, le_of_lt hz⟩), norm_smul]
      have hχz := abs_le_mul_im_of_eq_zero_on_real (hχ.differentiable (by simp)) hM hχ0 hz.le
      have hBz : ‖deriv Real.smoothTransition (((n : ℝ) + 1) * z.im - 1)‖ ≤ B := hB ⟨_, rfl⟩
      simp only [hD, norm_mul, Real.norm_eq_abs] at hBz ⊢
      have hn : |(n : ℝ) + 1| = (n : ℝ) + 1 := abs_of_pos (by positivity)
      rw [hn]
      calc |χ z| * (|deriv Real.smoothTransition (((n : ℝ) + 1) * z.im - 1)| *
            (((n : ℝ) + 1) * |v.im|)) * ‖g z‖
          ≤ (M * z.im) * (B * (((n : ℝ) + 1) * |v.im|)) * ‖g z‖ := by gcongr
        _ = B * M * |v.im| * ‖g z‖ * (((n : ℝ) + 1) * z.im) := by ring
        _ ≤ B * M * |v.im| * ‖g z‖ * 2 := by gcongr
        _ = 2 * (B * M * |v.im|) * ‖g z‖ := by ring
    · have hz : 0 < z.im := hz
      exact tendsto_const_nhds.congr' <| (eventually_imCutoff_arg hz).mono fun n hn => by
        simp [hD, Real.smoothTransition.deriv_of_one_lt hn]
  have hlim := h1.add h2
  rw [add_zero] at hlim
  exact tendsto_nhds_unique (hlim.congr key) h3.neg

/-! ### Weak gluing across the real axis -/

/-- The dilation of a node maps the lower half-plane onto the upper one. -/
private theorem preimage_imDilation_node {k : ℕ} (j : Fin k) :
    imDilation (higherReflectionNode j) ⁻¹' {z : ℂ | 0 < z.im} = {z : ℂ | z.im < 0} := by
  ext z
  simp [mul_pos_iff, higherReflectionNode_neg j, (higherReflectionNode_neg j).not_gt]

/-- The node dilations map `{0 ≤ im} ∩ e⁻¹(Ω)` into `Ω` when they map the lower part of `Ω` into
`Ω`. -/
private theorem imDilation_mem_of_im_nonpos {Ω : Set ℂ}
    (hΩ : ∀ z ∈ Ω, z.im < 0 → ∀ j : Fin k, imDilation (higherReflectionNode j) z ∈ Ω)
    (j : Fin k) {z : ℂ} (hz : z ∈ Ω) (hz0 : z.im ≤ 0) :
    imDilation (higherReflectionNode j) z ∈ Ω := by
  rcases hz0.lt_or_eq with hz0 | hz0
  · exact hΩ z hz hz0 j
  · rwa [imDilation_of_im_eq_zero _ hz0]

/-- Undoing a node dilation on a function supported in `Ω` gives a function whose support meets
`{0 ≤ im}` inside `Ω`. -/
private theorem tsupport_comp_imDilation_inv_subset {Ω : Set ℂ}
    (hΩ : ∀ z ∈ Ω, z.im < 0 → ∀ j : Fin k, imDilation (higherReflectionNode j) z ∈ Ω)
    (j : Fin k) {f : ℂ → ℝ} (hfΩ : tsupport f ⊆ Ω) :
    tsupport (fun w => f (imDilation (higherReflectionNode j)⁻¹ w)) ∩ {z : ℂ | 0 ≤ z.im} ⊆ Ω := by
  rintro w ⟨hw, hw0⟩
  have hn := higherReflectionNode_neg j
  have hw' := tsupport_comp_subset_preimage f (imDilation (higherReflectionNode j)⁻¹).continuous hw
  have hz0 : (imDilation (higherReflectionNode j)⁻¹ w).im ≤ 0 := by
    simpa using mul_nonpos_of_nonpos_of_nonneg (inv_lt_zero.2 hn).le (show (0 : ℝ) ≤ w.im from hw0)
  have h := imDilation_mem_of_im_nonpos hΩ j (hfΩ hw') hz0
  rwa [imDilation_imDilation, mul_inv_cancel₀ hn.ne, imDilation_one_apply] at h

/-- **Splitting a pairing with the reflection.** Against a compactly supported continuous `f`
with support in `Ω`, the reflection pairs as `h` on the upper half-plane plus, for each node, the
pairing of `h` with the undilated factor, weighted by the inverse Jacobian. -/
private theorem integral_smul_planarReflection {Ω : Set ℂ}
    (hΩ : ∀ z ∈ Ω, z.im < 0 → ∀ j : Fin k, imDilation (higherReflectionNode j) z ∈ Ω)
    {h : ℂ → F} (hh : MemLpLoc 1 (Ω ∩ {z : ℂ | 0 ≤ z.im}) h) (d : Fin k → ℝ) {f : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfΩ : tsupport f ⊆ Ω) :
    ∫ z, f z • planarReflection d h z = (∫ z in {z : ℂ | 0 < z.im}, f z • h z) +
      ∑ j, (d j * |higherReflectionNode j|⁻¹) •
        ∫ w in {z : ℂ | 0 < z.im}, f (imDilation (higherReflectionNode j)⁻¹ w) • h w := by
  have hL : MeasurableSet {z : ℂ | z.im < 0} := measurableSet_lt measurable_im measurable_const
  have hclosed : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const continuous_im
  have hint : Integrable fun z => f z • planarReflection d h z := by
    have h1 := (hh.planarReflection hΩ d).integrableOn_smul hf hfc isClosed_univ
      (by simpa using hfΩ)
    rwa [integrableOn_univ] at h1
  -- Each reflected copy, after undoing its dilation, is a pairing on the upper half-plane.
  have hcopy (j : Fin k) :
      ∫ z in {z : ℂ | z.im < 0}, f z • h (imDilation (higherReflectionNode j) z) =
        |higherReflectionNode j|⁻¹ •
          ∫ w in {z : ℂ | 0 < z.im}, f (imDilation (higherReflectionNode j)⁻¹ w) • h w := by
    rw [← setIntegral_comp_imDilation (higherReflectionNode_ne_zero j), preimage_imDilation_node]
    refine setIntegral_congr_fun hL fun z _ => ?_
    simp only [imDilation_imDilation, inv_mul_cancel₀ (higherReflectionNode_ne_zero j),
      imDilation_one_apply]
  have hcopyint (j : Fin k) :
      IntegrableOn (fun z => f z • h (imDilation (higherReflectionNode j) z))
        {z : ℂ | z.im < 0} := by
    have hu : IntegrableOn
        (fun w => f (imDilation (higherReflectionNode j)⁻¹ w) • h w) {z : ℂ | 0 < z.im} :=
      (hh.integrableOn_smul (hf.comp (imDilation _).continuous)
        (hfc.comp_homeomorph (imDilationEquiv (inv_ne_zero
          (higherReflectionNode_ne_zero j))).toHomeomorph) hclosed
        (fun w hw => ⟨tsupport_comp_imDilation_inv_subset hΩ j hfΩ hw, hw.2⟩)).mono_set
        fun z (hz : 0 < z.im) => show (0 : ℝ) ≤ z.im from le_of_lt hz
    rw [← integrableOn_comp_imDilation_iff (higherReflectionNode_ne_zero j),
      preimage_imDilation_node] at hu
    refine hu.congr_fun (fun z _ => ?_) hL
    simp only [imDilation_imDilation, inv_mul_cancel₀ (higherReflectionNode_ne_zero j),
      imDilation_one_apply]
  rw [← integral_add_compl hL hint, add_comm]
  congr 1
  · rw [setIntegral_congr_set (show {z : ℂ | z.im < 0}ᶜ =ᵐ[volume] {z : ℂ | 0 < z.im} from by
      simpa [compl_ofPred] using Complex.setOf_le_im_ae_eq 0)]
    refine setIntegral_congr_fun (measurableSet_lt measurable_const measurable_im) fun z hz => ?_
    rw [planarReflection_of_nonneg _ _ (le_of_lt hz)]
  · rw [setIntegral_congr_fun hL fun z hz => by
      rw [planarReflection_of_neg _ _ hz, Finset.smul_sum]]
    rw [integral_finsetSum _ fun j _ => ?_]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp_rw [smul_comm (f _) (d j)]
      rw [integral_smul, hcopy, smul_smul]
    · simp_rw [smul_comm (f _) (d j)]
      exact (hcopyint j).smul (d j)

/-- **Weak gluing in the tangential direction.** If `g'` is the weak derivative of `g` along the
real axis on the upper part of `Ω`, with both integrable on compact subsets of `Ω ∩ {0 ≤ im}`, then
for every choice of weights the reflection of `g'` is the weak derivative of the reflection of `g`
along the real axis on all of `Ω`. -/
theorem HasWeakLineDerivOn.planarReflection_one {Ω : Opens ℂ}
    (hΩ : ∀ z ∈ Ω, z.im < 0 → ∀ j : Fin k, imDilation (higherReflectionNode j) z ∈ Ω)
    {g g' : ℂ → F}
    (hgW : HasWeakLineDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) g g' 1)
    (hg : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g)
    (hg' : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g') (d : Fin k → ℝ) :
    HasWeakLineDerivOn volume Ω (planarReflection d g) (planarReflection d g') 1 := by
  have := hgW.completeSpace
  refine (hasWeakLineDerivOn_iff
    ((hg.planarReflection hΩ d).locallyIntegrableOn le_rfl Ω.isOpen.isLocallyClosed)
    ((hg'.planarReflection hΩ d).locallyIntegrableOn le_rfl Ω.isOpen.isLocallyClosed)).2
      fun φ hφ hφc hφΩ => ?_
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hdφ : Continuous fun z => fderiv ℝ φ z 1 :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  simp_rw [(hφd _).lineDeriv_eq_fderiv]
  rw [integral_smul_planarReflection hΩ hg d hdφ (hφc.fderiv_apply (𝕜 := ℝ) 1)
      ((tsupport_fderiv_apply_subset ℝ 1).trans hφΩ),
    integral_smul_planarReflection hΩ hg' d hφ.continuous hφc hφΩ,
    setIntegral_fderiv_smul_eq_neg hgW hg hg' hφ hφc
      (fun z hz => hφΩ hz.1) (Or.inl (by simp))]
  rw [neg_add, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_neg]
  congr 1
  set c := (higherReflectionNode j)⁻¹
  have hψ := setIntegral_fderiv_smul_eq_neg hgW hg hg' (hφ.comp (imDilation c).contDiff)
    (hφc.comp_homeomorph (imDilationEquiv (inv_ne_zero (higherReflectionNode_ne_zero j))
      ).toHomeomorph)
    (tsupport_comp_imDilation_inv_subset hΩ j hφΩ) (Or.inl (by simp)) (v := 1)
  simp only [Function.comp_def, fderiv_comp_imDilation_apply hφd, imDilation_one] at hψ
  exact hψ

/-- **Weak gluing in the normal direction.** If `g'` is the weak derivative of `g` in the normal
direction `I` on the upper part of `Ω`, with both integrable on compact subsets of `Ω ∩ {0 ≤ im}`,
and the weights sum to one, then the reflection of `g'` with the weights
`d j * higherReflectionNode j` is the weak derivative of the reflection of `g` in the direction `I`
on all of `Ω`. The condition on the weights matches the two one-sided values on the real axis; no
boundary condition on `g` is needed. -/
theorem HasWeakLineDerivOn.planarReflection_I {Ω : Opens ℂ}
    (hΩ : ∀ z ∈ Ω, z.im < 0 → ∀ j : Fin k, imDilation (higherReflectionNode j) z ∈ Ω)
    {g g' : ℂ → F}
    (hgW : HasWeakLineDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) g g' I)
    (hg : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g)
    (hg' : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g') {d : Fin k → ℝ} (hd : ∑ j, d j = 1) :
    HasWeakLineDerivOn volume Ω (planarReflection d g)
      (planarReflection (fun j => d j * higherReflectionNode j) g') I := by
  have := hgW.completeSpace
  refine (hasWeakLineDerivOn_iff
    ((hg.planarReflection hΩ d).locallyIntegrableOn le_rfl Ω.isOpen.isLocallyClosed)
    ((hg'.planarReflection hΩ _).locallyIntegrableOn le_rfl Ω.isOpen.isLocallyClosed)).2
      fun φ hφ hφc hφΩ => ?_
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hdφ : Continuous fun z => fderiv ℝ φ z I :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hclosed : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const continuous_im
  have hHsub : {z : ℂ | 0 < z.im} ⊆ {z : ℂ | 0 ≤ z.im} :=
    fun z (hz : 0 < z.im) => show (0 : ℝ) ≤ z.im from le_of_lt hz
  simp_rw [(hφd _).lineDeriv_eq_fderiv]
  rw [integral_smul_planarReflection hΩ hg d hdφ (hφc.fderiv_apply (𝕜 := ℝ) I)
      ((tsupport_fderiv_apply_subset ℝ I).trans hφΩ),
    integral_smul_planarReflection hΩ hg' _ hφ.continuous hφc hφΩ]
  -- Each reflected copy of `∂_I φ` is a multiple of `∂_I` of the undilated test function, and
  -- integration by parts applies to `φ` minus that test function, which vanishes on the axis.
  have hcopy (j : Fin k) :
      (d j * |higherReflectionNode j|⁻¹) • ∫ w in {z : ℂ | 0 < z.im},
          fderiv ℝ φ (imDilation (higherReflectionNode j)⁻¹ w) I • g w =
        -(d j • ((∫ z in {z : ℂ | 0 < z.im}, fderiv ℝ φ z I • g z) +
          (∫ z in {z : ℂ | 0 < z.im}, φ z • g' z) -
            ∫ w in {z : ℂ | 0 < z.im}, φ (imDilation (higherReflectionNode j)⁻¹ w) • g' w)) := by
    set n := higherReflectionNode j
    have hn := higherReflectionNode_neg j
    set ψ : ℂ → ℝ := fun w => φ (imDilation n⁻¹ w) with hψdef
    have hψ : ContDiff ℝ ∞ ψ := hφ.comp (imDilation _).contDiff
    have hψc : HasCompactSupport ψ :=
      hφc.comp_homeomorph (imDilationEquiv (inv_ne_zero hn.ne)).toHomeomorph
    have hψΩ := tsupport_comp_imDilation_inv_subset hΩ j hφΩ
    have hdψ (w : ℂ) : fderiv ℝ ψ w I = n⁻¹ * fderiv ℝ φ (imDilation n⁻¹ w) I := by
      rw [hψdef, fderiv_comp_imDilation_apply hφd, imDilation_I, map_smul, smul_eq_mul]
    -- The test function `χ = φ - ψ`.
    have hχ : ContDiff ℝ ∞ fun w => φ w - ψ w := hφ.sub hψ
    have hχc : HasCompactSupport fun w => φ w - ψ w := hφc.sub hψc
    have hχΩ : tsupport (fun w => φ w - ψ w) ∩ {z : ℂ | 0 ≤ z.im} ⊆ Ω := by
      rintro w ⟨hw, hw0⟩
      have hw' : w ∈ tsupport φ ∪ tsupport ψ :=
        closure_minimal ((Function.support_sub _ _).trans
          (union_subset_union (subset_tsupport _) (subset_tsupport _)))
          ((isClosed_tsupport _).union (isClosed_tsupport _)) hw
      rcases hw' with hw' | hw'
      · exact hφΩ hw'
      · exact hψΩ ⟨hw', hw0⟩
    have hχ0 (x : ℝ) : φ x - ψ x = 0 := by
      simp [hψdef, imDilation_of_im_eq_zero _ (Complex.ofReal_im x)]
    have hIBP := setIntegral_fderiv_smul_eq_neg hgW hg hg' hχ hχc hχΩ (Or.inr hχ0)
    have hdχ (w : ℂ) : fderiv ℝ (fun w => φ w - ψ w) w I = fderiv ℝ φ w I - fderiv ℝ ψ w I := by
      rw [fderiv_fun_sub (hφd w) (hψ.differentiable (by simp) w)]
      rfl
    have hdψc : Continuous fun z => fderiv ℝ ψ z I :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have iA : IntegrableOn (fun z => fderiv ℝ φ z I • g z) {z : ℂ | 0 < z.im} :=
      (hg.integrableOn_smul hdφ (hφc.fderiv_apply (𝕜 := ℝ) I) hclosed
        fun z hz => ⟨(tsupport_fderiv_apply_subset ℝ I).trans hφΩ hz.1, hz.2⟩).mono_set hHsub
    have iP : IntegrableOn (fun z => fderiv ℝ ψ z I • g z) {z : ℂ | 0 < z.im} :=
      (hg.integrableOn_smul hdψc (hψc.fderiv_apply (𝕜 := ℝ) I) hclosed
        fun z hz => ⟨hψΩ ⟨tsupport_fderiv_apply_subset ℝ I hz.1, hz.2⟩, hz.2⟩).mono_set hHsub
    have iB : IntegrableOn (fun z => φ z • g' z) {z : ℂ | 0 < z.im} :=
      (hg'.integrableOn_smul hφ.continuous hφc hclosed
        fun z hz => ⟨hφΩ hz.1, hz.2⟩).mono_set hHsub
    have iQ : IntegrableOn (fun z => ψ z • g' z) {z : ℂ | 0 < z.im} :=
      (hg'.integrableOn_smul hψ.continuous hψc hclosed
        fun z hz => ⟨hψΩ hz, hz.2⟩).mono_set hHsub
    simp only [hdχ, sub_smul] at hIBP
    rw [integral_sub iA iP, integral_sub iB iQ] at hIBP
    have hn0 : n ≠ 0 := hn.ne
    have hcoef : d j * |n|⁻¹ * n = -d j := by
      rw [abs_of_neg (show n < 0 from hn)]
      field_simp
    have hscale : (fun w => fderiv ℝ φ (imDilation n⁻¹ w) I • g w) =
        fun w => n • (fderiv ℝ ψ w I • g w) := by
      funext w
      rw [hdψ, smul_smul]
      field_simp
    -- Integration by parts for `φ - ψ` expresses the pairing with `∂_I ψ` through the others.
    have hP : ∫ z in {z : ℂ | 0 < z.im}, fderiv ℝ ψ z I • g z =
        (∫ z in {z : ℂ | 0 < z.im}, fderiv ℝ φ z I • g z) +
          (∫ z in {z : ℂ | 0 < z.im}, φ z • g' z) -
            ∫ w in {z : ℂ | 0 < z.im}, ψ w • g' w := by
      rw [← sub_eq_zero, ← neg_eq_zero, ← add_eq_zero_iff_eq_neg.2 hIBP]
      abel
    rw [hscale, integral_smul, smul_smul, hcoef, hP, neg_smul]
  have hcoef' (j : Fin k) :
      d j * higherReflectionNode j * |higherReflectionNode j|⁻¹ = -d j := by
    have hn := higherReflectionNode_neg j
    have hn0 := hn.ne
    rw [abs_of_neg hn]
    field_simp
  simp only [hcopy, hcoef', neg_smul, Finset.sum_neg_distrib, smul_sub, smul_add,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_smul, hd, one_smul]
  abel

/-- The candidate weak derivative of `planarReflection d g`: the tangential component is the
reflection of the tangential derivative, and the normal component is the reflection of the normal
derivative with the weights `d j * higherReflectionNode j`. Below the axis it is the chain-rule
expression `TauCeti.planarReflectionFDeriv_of_neg`. -/
def planarReflectionFDeriv (d : Fin k → ℝ) (Dg : ℂ → ℂ →L[ℝ] F) (z : ℂ) : ℂ →L[ℝ] F :=
  ContinuousLinearMap.smulRightL ℝ ℂ F reCLM (planarReflection d (fun w => Dg w 1) z) +
    ContinuousLinearMap.smulRightL ℝ ℂ F imCLM
      (planarReflection (fun j => d j * higherReflectionNode j) (fun w => Dg w I) z)

@[simp]
theorem planarReflectionFDeriv_apply_one (d : Fin k → ℝ) (Dg : ℂ → ℂ →L[ℝ] F) (z : ℂ) :
    planarReflectionFDeriv d Dg z 1 = planarReflection d (fun w => Dg w 1) z := by
  simp [planarReflectionFDeriv]

@[simp]
theorem planarReflectionFDeriv_apply_I (d : Fin k → ℝ) (Dg : ℂ → ℂ →L[ℝ] F) (z : ℂ) :
    planarReflectionFDeriv d Dg z I =
      planarReflection (fun j => d j * higherReflectionNode j) (fun w => Dg w I) z := by
  simp [planarReflectionFDeriv]

/-- On the closed upper half-plane the candidate derivative is the given derivative. -/
@[simp]
theorem planarReflectionFDeriv_of_nonneg (d : Fin k → ℝ) (Dg : ℂ → ℂ →L[ℝ] F) {z : ℂ}
    (hz : 0 ≤ z.im) : planarReflectionFDeriv d Dg z = Dg z := by
  ext v
  have hv := LinearMap.apply_eq_re_smul_one_add_im_smul_I (Dg z : ℂ →ₗ[ℝ] F) v
  simp only [ContinuousLinearMap.coe_coe] at hv
  rw [hv]
  simp [planarReflectionFDeriv, hz]

/-- Below the real axis the candidate derivative is the chain-rule derivative of the reflected
copies. -/
@[simp]
theorem planarReflectionFDeriv_of_neg (d : Fin k → ℝ) (Dg : ℂ → ℂ →L[ℝ] F) {z : ℂ}
    (hz : z.im < 0) : planarReflectionFDeriv d Dg z =
      ∑ j, d j • (Dg (imDilation (higherReflectionNode j) z)).comp
        (imDilation (higherReflectionNode j)) := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hv := LinearMap.apply_eq_re_smul_one_add_im_smul_I
    (planarReflectionFDeriv d Dg z : ℂ →ₗ[ℝ] F) v
  simp only [ContinuousLinearMap.coe_coe] at hv
  rw [hv, planarReflectionFDeriv_apply_one, planarReflectionFDeriv_apply_I,
    planarReflection_of_neg _ _ hz, planarReflection_of_neg _ _ hz]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.comp_apply, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hv := LinearMap.apply_eq_re_smul_one_add_im_smul_I
    (Dg (imDilation (higherReflectionNode j) z) : ℂ →ₗ[ℝ] F) (imDilation (higherReflectionNode j) v)
  simp only [ContinuousLinearMap.coe_coe] at hv
  rw [hv, imDilation_apply_re, imDilation_apply_im]
  module

/-- **Weak gluing of the full derivative.** If `Dg` is the weak derivative of `g` on the upper
part of `Ω`, both integrable on compact subsets of `Ω ∩ {0 ≤ im}`, and the weights sum to one, then
`planarReflectionFDeriv d Dg` is the weak derivative of `planarReflection d g` on all of `Ω`. -/
theorem HasWeakFDerivOn.planarReflection {Ω : Opens ℂ}
    (hΩ : ∀ z ∈ Ω, z.im < 0 → ∀ j : Fin k, imDilation (higherReflectionNode j) z ∈ Ω)
    {g : ℂ → F} {Dg : ℂ → ℂ →L[ℝ] F}
    (hgW : HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) g Dg)
    (hg : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g)
    (hDg : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) Dg) {d : Fin k → ℝ} (hd : ∑ j, d j = 1) :
    HasWeakFDerivOn volume Ω (planarReflection d g) (planarReflectionFDeriv d Dg) := by
  have := hgW.completeSpace
  refine basisOneI.hasWeakFDerivOn_of_forall
    ((hg.planarReflection hΩ d).locallyIntegrableOn le_rfl Ω.isOpen.isLocallyClosed) fun i => ?_
  fin_cases i
  · simpa [planarReflectionFDeriv_apply_one] using (hgW.hasWeakLineDerivOn 1).planarReflection_one
      hΩ hg (hDg.clm_comp (ContinuousLinearMap.apply ℝ F 1)) d
  · simpa [planarReflectionFDeriv_apply_I] using (hgW.hasWeakLineDerivOn I).planarReflection_I
      hΩ hg (hDg.clm_comp (ContinuousLinearMap.apply ℝ F I)) hd

/-! ### Higher-order Sobolev membership -/

/-- **Reflection preserves local Sobolev membership at order `m`**, for weights whose moments of
order below `m` against the nodes are one: the normal derivatives of order below `m` then match
across the real axis. -/
theorem MemWkpLoc.planarReflection {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Opens ℂ}
    (hΩ : ∀ z ∈ Ω, z.im < 0 → ∀ j : Fin k, imDilation (higherReflectionNode j) z ∈ Ω)
    {m : ℕ} {d : Fin k → ℝ} (hd : ∀ i < m, ∑ j, d j * higherReflectionNode j ^ i = 1)
    {g : ℂ → F} (hg : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) m g) :
    MemWkpLoc p Ω m (planarReflection d g) := by
  induction m generalizing F d g with
  | zero => exact memWkpLoc_zero_iff.2 ((memWkpLoc_zero_iff.1 hg).planarReflection hΩ d)
  | succ m ih =>
    obtain ⟨hgp, Dg, hDg, hDgm⟩ := memWkpLoc_succ_iff.1 hg
    have := hDg.completeSpace
    have hd0 : ∑ j, d j = 1 := by simpa using hd 0 (Nat.succ_pos m)
    refine memWkpLoc_succ_iff_of_isOpen.2 ⟨hgp.planarReflection hΩ d,
      planarReflectionFDeriv d Dg, hDg.planarReflection hΩ (hgp.mono_exponent hp)
        (hDgm.memLpLoc.mono_exponent hp) hd0, ?_⟩
    have h1 := ih (fun i hi => hd i (by omega))
      (hDgm.clm_comp (ContinuousLinearMap.apply ℝ F 1))
    have h2 := ih (d := fun j => d j * higherReflectionNode j)
      (fun i hi => by simpa [mul_assoc, pow_succ'] using hd (i + 1) (by omega))
      (hDgm.clm_comp (ContinuousLinearMap.apply ℝ F I))
    have h := (h1.clm_comp (ContinuousLinearMap.smulRightL ℝ ℂ F reCLM)).add
      (h2.clm_comp (ContinuousLinearMap.smulRightL ℝ ℂ F imCLM))
    convert h using 1
    funext z
    rfl

/-- **Higher-order reflection extends half-disc Sobolev maps.** A map in `W^{k,p}_loc` of the
relatively open set `Ω ∩ {0 ≤ im}`, with derivatives tested in `Ω ∩ {0 < im}` and `Lᵖ` bounds up to
the real axis, extends by the order-`k` reflection with the Vandermonde weights to a map in
`W^{k,p}_loc(Ω)`. -/
theorem MemWkpLoc.planarReflection_higherReflectionCoeff {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Opens ℂ}
    (hΩ : ∀ z ∈ Ω, z.im < 0 → ∀ j : Fin k, imDilation (higherReflectionNode j) z ∈ Ω)
    {u : ℂ → F} (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k u) :
    MemWkpLoc p Ω k (TauCeti.planarReflection (higherReflectionCoeff k) u) :=
  hu.planarReflection hp hΩ fun _ hi => sum_higherReflectionCoeff_mul_pow hi

/-- Discs centred on the real axis are stable under the node dilations. -/
theorem imDilation_higherReflectionNode_mem_ball (x : ℝ) (r : ℝ) {k : ℕ} (j : Fin k) {z : ℂ}
    (hz : z ∈ Metric.ball (x : ℂ) r) :
    imDilation (higherReflectionNode j) z ∈ Metric.ball (x : ℂ) r := by
  have hn : |higherReflectionNode j| ≤ 1 := by
    rw [higherReflectionNode_eq, abs_neg, abs_inv, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (by simp)
  rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
  have hx : imDilation (higherReflectionNode j) (x : ℂ) = x :=
    imDilation_of_im_eq_zero _ (Complex.ofReal_im x)
  calc ‖imDilation (higherReflectionNode j) z - x‖
      = ‖imDilation (higherReflectionNode j) (z - x)‖ := by rw [map_sub, hx]
    _ ≤ ‖z - x‖ := norm_imDilation_le hn _
    _ < r := hz

/-- **Extension from a half-disc to the disc.** For a disc `D` centred on the real axis, a map in
`W^{k,p}_loc(D ∩ {0 ≤ im})` extends by the order-`k` higher reflection to a map in `W^{k,p}_loc(D)`.
-/
theorem MemWkpLoc.planarReflection_higherReflectionCoeff_ball {p : ℝ≥0∞} (hp : 1 ≤ p) (x r : ℝ)
    {u : ℂ → F} (hu : MemWkpLoc p (Metric.ball (x : ℂ) r ∩ {z | 0 ≤ z.im}) k u) :
    MemWkpLoc p (Metric.ball (x : ℂ) r) k (TauCeti.planarReflection (higherReflectionCoeff k) u) :=
  MemWkpLoc.planarReflection_higherReflectionCoeff (Ω := ⟨_, Metric.isOpen_ball⟩) hp
    (fun _ hz _ j => imDilation_higherReflectionNode_mem_ball x r j hz) hu

/-- **Extension from the closed half-plane to the plane.** -/
theorem MemWkpLoc.planarReflection_higherReflectionCoeff_univ {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : ℂ → F} (hu : MemWkpLoc p {z : ℂ | 0 ≤ z.im} k u) :
    MemWkpLoc p univ k (TauCeti.planarReflection (higherReflectionCoeff k) u) :=
  MemWkpLoc.planarReflection_higherReflectionCoeff (Ω := ⊤) hp (fun _ _ _ _ => trivial)
    (by simpa using hu)

/-! ### The `Lᵖ` bound -/

/-- The `Lᵖ` constant of the reflection with weights `d`: one for the original half, plus the
weights times the Jacobian factors `|higherReflectionNode j|^(-1 / p)` of the reflected copies.
With the Vandermonde weights it is `TauCeti.higherReflectionBound k p`. -/
def planarReflectionBound (d : Fin k → ℝ) (p : ℝ≥0∞) : ℝ≥0∞ :=
  1 + ∑ j, ‖d j‖ₑ * ENNReal.ofReal |(higherReflectionNode j)⁻¹| ^ (1 / p).toReal

/-- With the Vandermonde weights the constant is the one of the normal-slice reflection. -/
theorem planarReflectionBound_higherReflectionCoeff (k : ℕ) (p : ℝ≥0∞) :
    planarReflectionBound (higherReflectionCoeff k) p = higherReflectionBound k p := by
  rw [planarReflectionBound, higherReflectionBound_eq]

/-- **The `Lᵖ` bound for the reflection.** For `1 ≤ p ≤ ∞`, the reflection of `g` on `Ω` is
bounded in `Lᵖ(Ω)` by `planarReflectionBound d p` times the `Lᵖ` norm of `g` on `Ω ∩ {0 ≤ im}`.
Applied to the components of the weak derivatives of `planarReflectionFDeriv`, it bounds every
derivative of the extension by the corresponding derivative of `g`. -/
theorem eLpNorm_planarReflection_le {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set ℂ}
    (hΩ : ∀ z ∈ Ω, z.im < 0 → ∀ j : Fin k, imDilation (higherReflectionNode j) z ∈ Ω)
    (d : Fin k → ℝ) (g : ℂ → F) :
    eLpNorm (planarReflection d g) p (volume.restrict Ω) ≤
      planarReflectionBound d p * eLpNorm g p (volume.restrict (Ω ∩ {z : ℂ | 0 ≤ z.im})) := by
  have hH : MeasurableSet {z : ℂ | 0 ≤ z.im} := measurableSet_le measurable_const measurable_im
  have hL : MeasurableSet {z : ℂ | z.im < 0} := measurableSet_lt measurable_im measurable_const
  set U := Ω ∩ {z : ℂ | 0 ≤ z.im}
  have hcopy (j : Fin k) :
      eLpNorm (fun z => d j • g (imDilation (higherReflectionNode j) z)) p
          (volume.restrict ({z : ℂ | z.im < 0} ∩ Ω)) ≤
        ‖d j‖ₑ * (ENNReal.ofReal |(higherReflectionNode j)⁻¹| ^ (1 / p).toReal *
          eLpNorm g p (volume.restrict U)) := by
    have hsub : {z : ℂ | z.im < 0} ∩ Ω ⊆ imDilation (higherReflectionNode j) ⁻¹' U := by
      rintro z ⟨hz, hzΩ⟩
      refine ⟨hΩ z hzΩ hz j, ?_⟩
      simpa using mul_nonneg_of_nonpos_of_nonpos (higherReflectionNode_neg j).le
        (le_of_lt (show z.im < 0 from hz))
    have he := Measure.eLpNorm_comp_continuousLinearEquiv_restrict_preimage volume g
      (imDilationEquiv (higherReflectionNode_ne_zero j)) p (s := U)
    have hdet : LinearMap.det ((imDilationEquiv (higherReflectionNode_ne_zero j) : ℂ ≃L[ℝ] ℂ) :
        ℂ →ₗ[ℝ] ℂ) = higherReflectionNode j := det_imDilation _
    rw [hdet, coe_imDilationEquiv] at he
    -- Pi scalar multiplication evaluates pointwise; expose it to use the norm API.
    change eLpNorm (d j • fun z => g (imDilation (higherReflectionNode j) z)) p _ ≤ _
    rw [eLpNorm_const_smul, ← he]
    gcongr
    exact eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)
  have hsum : ({z : ℂ | z.im < 0}.indicator fun z =>
      ∑ j, d j • g (imDilation (higherReflectionNode j) z)) =
      {z : ℂ | z.im < 0}.indicator (∑ j : Fin k,
        fun z => d j • g (imDilation (higherReflectionNode j) z)) := by
    congr 1
    funext z
    simp
  rw [planarReflection_eq_indicator, hsum]
  calc _ ≤ eLpNorm ({z : ℂ | 0 ≤ z.im}.indicator g) p (volume.restrict Ω) +
        eLpNorm ({z : ℂ | z.im < 0}.indicator (∑ j : Fin k,
          fun z => d j • g (imDilation (higherReflectionNode j) z))) p (volume.restrict Ω) :=
        eLpNorm_add_le hp
    _ ≤ eLpNorm g p (volume.restrict U) + ∑ j : Fin k, ‖d j‖ₑ *
        (ENNReal.ofReal |(higherReflectionNode j)⁻¹| ^ (1 / p).toReal *
          eLpNorm g p (volume.restrict U)) := by
      gcongr
      · rw [eLpNorm_indicator_eq_eLpNorm_restrict hH.nullMeasurableSet,
          Measure.restrict_restrict hH, inter_comm]
      · rw [eLpNorm_indicator_eq_eLpNorm_restrict hL.nullMeasurableSet,
          Measure.restrict_restrict hL]
        exact (eLpNorm_sum_le hp).trans (Finset.sum_le_sum fun j _ => hcopy j)
    _ = _ := by
      rw [planarReflectionBound, add_mul, one_mul, Finset.sum_mul]
      simp only [mul_assoc]

end TauCeti
