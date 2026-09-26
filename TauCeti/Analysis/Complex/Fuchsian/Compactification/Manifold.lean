/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.CuspChart
public import TauCeti.Analysis.Complex.Fuchsian.CoarseQuotient
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Extension
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The compactified quotient of a Fuchsian group is a Riemann surface

Let `Γ ≤ PSL(2, ℝ)` be discrete. This file extends the atlas of the coarse quotient `Γ \ ℍ` to
its compactification `Subgroup.CompactifiedQuotient Γ` by the q-coordinate charts
`Subgroup.CompactifiedQuotient.cuspChart` at the cusp orbits, and proves that the resulting atlas
is holomorphic. The compactified quotient is therefore a Riemann surface, Hausdorff and second
countable by `Subgroup.CompactifiedQuotient.instT2Space` and
`Subgroup.CompactifiedQuotient.instSecondCountableTopology`, and the inclusion of the coarse
quotient is a holomorphic open embedding.

The atlas consists of the charts of `Γ \ ℍ`, transported along the open embedding `ofQuotient`
(`Subgroup.CompactifiedQuotient.ofQuotientChart`), together with the cusp charts at every cusp
datum and every height at least its width. Every chart of this atlas is holomorphic when pulled
back to the coarse quotient (`Subgroup.CompactifiedQuotient.mdifferentiableAt_comp_ofQuotient`):
for a cusp chart this is holomorphic descent at a free orbit, since high horodiscs lie in the free
locus. Consequently the transition map out of a transported chart is holomorphic by the chain rule,
and the transition map out of a cusp chart agrees, near every nonzero point of its source, with
Mathlib's periodic cusp function of a `w`-periodic function that is holomorphic at the logarithmic
lift of that point, hence is holomorphic there
(`Function.Periodic.differentiableAt_cuspFunction`); at `q = 0` the singularity is removable
because a transition map is continuous.

## Main declarations

* `Subgroup.CompactifiedQuotient.ofQuotientChart`: a chart of `Γ \ ℍ` regarded as a chart of the
  compactified quotient.
* `Subgroup.CompactifiedQuotient.instChartedSpace`: the atlas, described by
  `Subgroup.CompactifiedQuotient.mem_atlas_iff`, `Subgroup.CompactifiedQuotient.chartAt_ofQuotient`
  and `Subgroup.CompactifiedQuotient.chartAt_ofCusp`.
* `Subgroup.CompactifiedQuotient.instIsManifold`: the atlas is analytic, so the compactified
  quotient is a Riemann surface.
* `Subgroup.CompactifiedQuotient.mdifferentiable_ofQuotient`: the inclusion of the coarse quotient
  is holomorphic.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §§2.4–2.5.
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §§18–19.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, Chapter 4.
-/

public noncomputable section

open Filter Function MulAction Set Topology TauCeti.Subgroup.CuspDatum UpperHalfPlane
open scoped ContDiff Manifold MatrixGroups

namespace Subgroup.CompactifiedQuotient

variable {Γ : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ]

/-! ### Charts of the coarse quotient -/

/-- A chart of the coarse quotient `Γ \ ℍ`, regarded as a chart of the compactified quotient along
the open embedding `ofQuotient`. -/
def ofQuotientChart (e : OpenPartialHomeomorph (orbitRel.Quotient Γ ℍ) ℂ) :
    OpenPartialHomeomorph Γ.CompactifiedQuotient ℂ :=
  (isOpenEmbedding_ofQuotient.toOpenPartialHomeomorph _).symm ≫ₕ e

variable (e : OpenPartialHomeomorph (orbitRel.Quotient Γ ℍ) ℂ)

@[simp]
theorem ofQuotientChart_ofQuotient (p : orbitRel.Quotient Γ ℍ) :
    ofQuotientChart e (ofQuotient p) = e p := by
  rw [ofQuotientChart, OpenPartialHomeomorph.trans_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

@[simp]
theorem ofQuotientChart_symm_apply (u : ℂ) :
    (ofQuotientChart e).symm u = ofQuotient (e.symm u) := by
  rw [ofQuotientChart, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_apply]

@[simp]
theorem ofQuotientChart_target : (ofQuotientChart e).target = e.target := by
  simp [ofQuotientChart]

theorem ofQuotient_mem_ofQuotientChart_source_iff {p : orbitRel.Quotient Γ ℍ} :
    ofQuotient p ∈ (ofQuotientChart e).source ↔ p ∈ e.source := by
  simp [ofQuotientChart, IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

@[simp]
theorem ofQuotientChart_source : (ofQuotientChart e).source = ofQuotient '' e.source := by
  ext x
  cases x with
  | ofQuotient p =>
    rw [ofQuotient_mem_ofQuotientChart_source_iff, ofQuotient_injective.mem_set_image]
  | ofCusp C =>
    simp only [ofQuotientChart, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, IsOpenEmbedding.toOpenPartialHomeomorph_target,
      mem_inter_iff, mem_range, mem_image]
    exact iff_of_false (fun ⟨⟨p, h⟩, _⟩ ↦ by cases h) fun ⟨p, _, h⟩ ↦ by cases h

/-! ### The atlas -/

/-- **The atlas of the compactified quotient.** It consists of the charts of the coarse quotient
`Γ \ ℍ`, transported along the open embedding `ofQuotient`, together with the cusp charts at every
cusp datum and every height at least its width. The chart at a point of the coarse quotient is the
transported chart there, and the chart at a cusp orbit is the cusp chart at a chosen cusp datum
representing it, at the height equal to its width. -/
instance instChartedSpace : ChartedSpace ℂ Γ.CompactifiedQuotient where
  atlas := ofQuotientChart '' atlas ℂ (orbitRel.Quotient Γ ℍ) ∪
    {c | ∃ (D : Γ.CuspDatum) (A : ℝ) (hA : D.width ≤ A), cuspChart D hA = c}
  chartAt
    | ofQuotient p => ofQuotientChart (chartAt ℂ p)
    | ofCusp C => cuspChart C.cuspDatum le_rfl
  mem_chart_source
    | ofQuotient p => (ofQuotient_mem_ofQuotientChart_source_iff _).2 (mem_chart_source ℂ p)
    | ofCusp C => by simp
  chart_mem_atlas
    | ofQuotient p => Or.inl ⟨_, chart_mem_atlas ℂ p, rfl⟩
    | ofCusp C => Or.inr ⟨_, _, _, rfl⟩

theorem chartAt_ofQuotient (p : orbitRel.Quotient Γ ℍ) :
    chartAt ℂ (ofQuotient p) = ofQuotientChart (chartAt ℂ p) :=
  (rfl)

theorem chartAt_ofCusp (C : Γ.CuspOrbit) : chartAt ℂ (ofCusp C) = cuspChart C.cuspDatum le_rfl :=
  (rfl)

/-- A chart of the compactified quotient belongs to the atlas exactly when it is a transported chart
of the coarse quotient or a cusp chart. -/
theorem mem_atlas_iff (c : OpenPartialHomeomorph Γ.CompactifiedQuotient ℂ) :
    c ∈ atlas ℂ Γ.CompactifiedQuotient ↔
      (∃ e ∈ atlas ℂ (orbitRel.Quotient Γ ℍ), ofQuotientChart e = c) ∨
        ∃ (D : Γ.CuspDatum) (A : ℝ) (hA : D.width ≤ A), cuspChart D hA = c :=
  Iff.rfl

theorem ofQuotientChart_mem_atlas {e : OpenPartialHomeomorph (orbitRel.Quotient Γ ℍ) ℂ}
    (he : e ∈ atlas ℂ (orbitRel.Quotient Γ ℍ)) :
    ofQuotientChart e ∈ atlas ℂ Γ.CompactifiedQuotient :=
  Or.inl ⟨e, he, rfl⟩

theorem cuspChart_mem_atlas (D : Γ.CuspDatum) {A : ℝ} (hA : D.width ≤ A) :
    cuspChart D hA ∈ atlas ℂ Γ.CompactifiedQuotient :=
  Or.inr ⟨D, A, hA, rfl⟩

/-! ### Holomorphy of the transition maps -/

/-- **Every chart of the atlas is holomorphic along the coarse quotient**: pulled back along the
inclusion `ofQuotient`, a chart of the compactified quotient is holomorphic at every point of the
coarse quotient in its source. -/
theorem mdifferentiableAt_comp_ofQuotient {c : OpenPartialHomeomorph Γ.CompactifiedQuotient ℂ}
    (hc : c ∈ atlas ℂ Γ.CompactifiedQuotient) {p : orbitRel.Quotient Γ ℍ}
    (hp : ofQuotient p ∈ c.source) : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (c ∘ ofQuotient) p := by
  rcases hc with ⟨e, he, rfl⟩ | ⟨D, A, hA, rfl⟩
  · have : (ofQuotientChart e ∘ ofQuotient) = e := funext (ofQuotientChart_ofQuotient e)
    rw [this]
    exact mdifferentiableAt_atlas he ((ofQuotient_mem_ofQuotientChart_source_iff e).1 hp)
  · rw [cuspChart_source] at hp
    obtain ⟨z, hz, rfl⟩ := (ofQuotient_mem_cuspNhd_iff D A).mp hp
    refine mdifferentiableAt_of_comp_quotientMk (stabilizer_eq_bot_of_mem_horodisc D hA hz) ?_
    refine (mdifferentiable_coordinate D z).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_horodisc D A).mem_nhds hz] with τ hτ
    exact cuspChart_ofQuotient_mk D hA hτ

/-- The transition map out of a transported chart of the coarse quotient to any chart of the atlas
is holomorphic at every point of its source. -/
private theorem differentiableAt_ofQuotientChart_symm_trans
    {e : OpenPartialHomeomorph (orbitRel.Quotient Γ ℍ) ℂ}
    (he : e ∈ atlas ℂ (orbitRel.Quotient Γ ℍ)) {c' : OpenPartialHomeomorph Γ.CompactifiedQuotient ℂ}
    (hc' : c' ∈ atlas ℂ Γ.CompactifiedQuotient) {u : ℂ}
    (hu : u ∈ ((ofQuotientChart e).symm ≫ₕ c').source) :
    DifferentiableAt ℂ ((ofQuotientChart e).symm ≫ₕ c') u := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, ofQuotientChart_target,
    mem_inter_iff, mem_preimage, ofQuotientChart_symm_apply] at hu
  have h := (mdifferentiableAt_comp_ofQuotient hc' hu.2).comp u
    (mdifferentiableAt_atlas_symm he hu.1)
  refine (mdifferentiableAt_iff_differentiableAt.1 h).congr_of_eventuallyEq (.of_eq ?_)
  funext v
  simp [OpenPartialHomeomorph.trans_apply]

/-- The transition map out of a cusp chart to any chart of the atlas is holomorphic at every nonzero
point of its source. -/
private theorem differentiableAt_cuspChart_symm_trans_of_ne_zero (D : Γ.CuspDatum) {A : ℝ}
    (hA : D.width ≤ A) {c' : OpenPartialHomeomorph Γ.CompactifiedQuotient ℂ}
    (hc' : c' ∈ atlas ℂ Γ.CompactifiedQuotient) {u : ℂ}
    (hu : u ∈ ((cuspChart D hA).symm ≫ₕ c').source) (hu0 : u ≠ 0) :
    DifferentiableAt ℂ ((cuspChart D hA).symm ≫ₕ c') u := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, mem_inter_iff,
    mem_preimage] at hu
  obtain ⟨hu1, hu2⟩ := hu
  have hu1' : ‖u‖ < 1 := by
    rw [cuspChart_target, mem_ball_zero_iff] at hu1
    exact hu1.trans (cuspRadius_lt_one D (D.width_pos.trans_le hA))
  -- The second chart, pulled back to the upper half-plane: invariant under the cusp stabilizer.
  set f : ℍ → ℂ := fun τ ↦ c' (ofQuotient (Quotient.mk _ τ)) with hf
  have hfinv : ∀ (g : stabilizer Γ D.cusp) (τ : ℍ), f (g • τ) = f τ := fun g τ ↦
    congrArg (c' ∘ ofQuotient) (Quotient.sound (orbitRel_apply.mpr (mem_orbit τ (g : Γ))))
  have hper := periodic_comp_ofComplex_inv_smul D f hfinv
  -- On the punctured disc, the transition map is Mathlib's cusp function of the scaled pullback.
  have heq : ⇑((cuspChart D hA).symm ≫ₕ c') =ᶠ[𝓝 u]
      Periodic.cuspFunction D.width ((fun z : ℍ ↦ f (D.scaling⁻¹ • z)) ∘ ofComplex) := by
    filter_upwards [isOpen_ne.mem_nhds hu0, (cuspChart D hA).open_target.mem_nhds hu1] with v hv hv'
    rw [OpenPartialHomeomorph.trans_apply, cuspChart_symm_of_ne_zero D hA hv' hv,
      Periodic.cuspFunction_eq_of_nonzero _ _ hv]
    rfl
  -- The logarithmic lift of `u`, at which the scaled pullback is holomorphic.
  set τ₀ : ℍ := ⟨Periodic.invQParam D.width u,
    Periodic.im_invQParam_pos_of_norm_lt_one D.width_pos hu1' hu0⟩
  have hτ₀ : ofComplex (Periodic.invQParam D.width u) = τ₀ := ofComplex_apply τ₀
  have hτ₀mem : ofQuotient (Quotient.mk _ (D.scaling⁻¹ • τ₀)) ∈ c'.source := by
    rwa [cuspChart_symm_of_ne_zero D hA hu1 hu0, hτ₀] at hu2
  have hdiff : DifferentiableAt ℂ ((fun z : ℍ ↦ f (D.scaling⁻¹ • z)) ∘ ofComplex)
      (Periodic.invQParam D.width u) := by
    have hm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) τ₀ :=
      ((mdifferentiableAt_comp_ofQuotient hc' hτ₀mem).comp _
        (mdifferentiable_quotientMk Γ _)).comp τ₀
        ((contMDiff_const_smul (I := 𝓘(ℂ)) (n := ∞) D.scaling⁻¹).mdifferentiable (by simp) τ₀)
    exact UpperHalfPlane.mdifferentiableAt_iff.mp hm
  have h := Periodic.differentiableAt_cuspFunction D.width_pos.ne' hper hdiff
  rw [Periodic.qParam_right_inv D.width_pos.ne' hu0] at h
  exact h.congr_of_eventuallyEq heq

/-- The transition map out of a cusp chart to any chart of the atlas is holomorphic on its source,
the point `q = 0` included. -/
private theorem differentiableOn_cuspChart_symm_trans (D : Γ.CuspDatum) {A : ℝ}
    (hA : D.width ≤ A) {c' : OpenPartialHomeomorph Γ.CompactifiedQuotient ℂ}
    (hc' : c' ∈ atlas ℂ Γ.CompactifiedQuotient) :
    DifferentiableOn ℂ ((cuspChart D hA).symm ≫ₕ c') ((cuspChart D hA).symm ≫ₕ c').source := by
  intro u hu
  rcases eq_or_ne u 0 with rfl | hu0
  · -- At `q = 0` the singularity is removable: the transition map is continuous there.
    have hs := ((cuspChart D hA).symm ≫ₕ c').open_source.mem_nhds hu
    refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hs).mp
      ⟨fun v hv ↦ ?_, ((cuspChart D hA).symm ≫ₕ c').continuousOn.continuousAt hs⟩ 0 hu
    exact (differentiableAt_cuspChart_symm_trans_of_ne_zero D hA hc' hv.1
      hv.2).differentiableWithinAt
  · exact (differentiableAt_cuspChart_symm_trans_of_ne_zero D hA hc' hu
      hu0).differentiableWithinAt

/-- **The transition maps of the atlas are holomorphic.** -/
theorem differentiableOn_symm_trans {c c' : OpenPartialHomeomorph Γ.CompactifiedQuotient ℂ}
    (hc : c ∈ atlas ℂ Γ.CompactifiedQuotient) (hc' : c' ∈ atlas ℂ Γ.CompactifiedQuotient) :
    DifferentiableOn ℂ (c.symm ≫ₕ c') (c.symm ≫ₕ c').source := by
  rcases hc with ⟨e, he, rfl⟩ | ⟨D, A, hA, rfl⟩
  · exact fun u hu ↦ (differentiableAt_ofQuotientChart_symm_trans he hc' hu).differentiableWithinAt
  · exact differentiableOn_cuspChart_symm_trans D hA hc'

/-- **The compactified quotient of a Fuchsian group is a Riemann surface.** -/
instance instIsManifold : IsManifold 𝓘(ℂ) ω Γ.CompactifiedQuotient := by
  refine isManifold_of_contDiffOn 𝓘(ℂ) ω _ fun c c' hc hc' ↦ ?_
  simp only [mfld_simps]
  exact (differentiableOn_symm_trans hc hc').contDiffOn (OpenPartialHomeomorph.open_source _)

example : IsManifold 𝓘(ℂ) ∞ Γ.CompactifiedQuotient := inferInstance

/-- **The inclusion of the coarse quotient is holomorphic.** Together with
`Subgroup.CompactifiedQuotient.isOpenEmbedding_ofQuotient`, the coarse quotient is an open
submanifold of the compactified quotient. -/
theorem mdifferentiable_ofQuotient :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (ofQuotient : orbitRel.Quotient Γ ℍ → Γ.CompactifiedQuotient) := by
  intro p
  rw [mdifferentiableAt_iff_target]
  refine ⟨continuous_ofQuotient.continuousAt, ?_⟩
  simp only [mfld_simps, chartAt_ofQuotient]
  have : (ofQuotientChart (chartAt ℂ p) ∘ ofQuotient) = chartAt ℂ p :=
    funext (ofQuotientChart_ofQuotient _)
  rw [this]
  exact mdifferentiableAt_atlas (chart_mem_atlas ℂ p) (mem_chart_source ℂ p)

end Subgroup.CompactifiedQuotient
