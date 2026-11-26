/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Contour.Cauchy.Circle
import TauCeti.Topology.MetricSpace.SeparatedBalls

/-!
# Finite-disc Cauchy singularity subtraction

Let `f` take values in a complete complex normed space `E`. For finitely many isolated
singularities `P` inside pairwise disjoint closed discs `Metric.closedBall ρ r` (`r > 0`) in the
interior of a region `D`, subtracting the corresponding
exterior Cauchy integrals `z ↦ (2πi)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w` removes every
singularity without assuming an open neighbourhood of `D` or meromorphy at `P`: if `f` is
continuous on `D \ P` and complex differentiable on `interior D \ P`, the subtracted function
extends continuously to `D` and holomorphically to `interior D`
(`TauCeti.Contour.exists_continuousOn_differentiableOn_sub_sum_circleIntegral`).

The construction glues `f - ∑ ρ ∈ P, (2πi)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w` outside the
closed discs to the interior Cauchy integral over a slightly enlarged circle `C(ρ, r')` minus the
exterior Cauchy integrals of the remaining singularities inside each disc, using
`TauCeti.Contour.sub_two_pi_I_inv_smul_circleIntegral_sub_inv_smul_eq` on the overlapping open
annulus.

## Main results

* `TauCeti.Contour.exists_continuousOn_differentiableOn_sub_sum_circleIntegral`: finite-disc
  singularity removal for functions valued in a complete complex normed space.

## References

* John B. Conway, *Functions of One Complex Variable I*, Chapters IV (Complex Integration) and V
  (Singularities).
-/

public section

open Complex Set Metric Filter
open scoped Real Topology

namespace TauCeti.Contour

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [NormedSpace ℂ E] [CompleteSpace E] in
/-- If pairwise disjoint closed discs `closedBall ρ r'` (`ρ ∈ P`) lie in `U` and `f` is continuous
on `U \ P`, then `f` is circle integrable on `C(ρ, r)` for every `ρ ∈ P` and `0 < r ≤ r'`. -/
private theorem circleIntegrable_of_closedBall_subset {f : ℂ → E} {P : Finset ℂ} {U : Set ℂ}
    {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r') (hP' : ∀ ρ ∈ P, closedBall ρ r' ⊆ U)
    (hdisj' : (P : Set ℂ).Pairwise fun ρ ρ' ↦ Disjoint (closedBall ρ r') (closedBall ρ' r'))
    (hc : ContinuousOn f (U \ P)) : ∀ ρ ∈ P, CircleIntegrable f ρ r := fun _ hρ ↦
  (continuousOn_sphere_of_closedBall_subset hr hrr' hP' hdisj' hc hρ).circleIntegrable hr.le

/-- The singularity-removed gluing of
`f - ∑ ρ ∈ P, (2πi)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w`: inside each closed disc
`closedBall ρ r` (`ρ ∈ P`) it uses the interior Cauchy integral over `C(ρ, r')` minus the
exterior Cauchy integrals of the other singularities. -/
private noncomputable def gluedRegular (f : ℂ → E) (P : Finset ℂ) (r r' : ℝ) (z : ℂ) : E := by
  classical
  exact if h : ∃ ρ ∈ P, z ∈ closedBall ρ r then
    (2 * π * I : ℂ)⁻¹ • (∮ w in C(h.choose, r'), (w - z)⁻¹ • f w) -
      ∑ ρ' ∈ P.erase h.choose, (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ', r), (z - w)⁻¹ • f w
  else
    f z - ∑ ρ ∈ P, (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w

omit [CompleteSpace E] in
/-- Outside all closed discs `closedBall ρ r`, `gluedRegular` agrees with
`f - ∑ ρ ∈ P, (2πi)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w`. -/
private theorem gluedRegular_eq_out {f : ℂ → E} {P : Finset ℂ} {r r' : ℝ} {z : ℂ}
    (hz : ∀ ρ ∈ P, z ∉ closedBall ρ r) :
    gluedRegular f P r r' z =
      f z - ∑ ρ ∈ P, (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w := by
  classical
  have hneg : ¬ ∃ ρ ∈ P, z ∈ closedBall ρ r := by push Not; exact hz
  simp only [gluedRegular, hneg, ↓reduceDIte]

omit [CompleteSpace E] in
/-- Near a point outside all closed discs `closedBall ρ r` (`ρ ∈ P`), `gluedRegular` agrees with
`f - ∑ ρ ∈ P, (2πi)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w`. -/
private theorem gluedRegular_eventuallyEq_out {f : ℂ → E} {P : Finset ℂ} {r r' : ℝ} {z : ℂ}
    (hz : ∀ ρ ∈ P, z ∉ closedBall ρ r) :
    gluedRegular f P r r' =ᶠ[𝓝 z]
      fun s ↦ f s - ∑ ρ ∈ P, (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ, r), (s - w)⁻¹ • f w := by
  have hopen : IsOpen (⋃ ρ ∈ P, closedBall ρ r)ᶜ :=
    (P.finite_toSet.isClosed_biUnion fun _ _ ↦ isClosed_closedBall).isOpen_compl
  refine Filter.eventuallyEq_of_mem (hopen.mem_nhds (by simpa using hz)) fun w hw ↦ ?_
  simp only [mem_compl_iff, mem_iUnion, not_exists] at hw
  exact gluedRegular_eq_out hw

/-- On each open ball `ball ρ r'` (`ρ ∈ P`), `gluedRegular` agrees with the holomorphic formula
`(2πi)⁻¹ • ∮ w in C(ρ, r'), (w - z)⁻¹ • f w -
  ∑ ρ' ∈ P.erase ρ, (2πi)⁻¹ • ∮ w in C(ρ', r), (z - w)⁻¹ • f w`. -/
private theorem gluedRegular_eq_on_ball {f : ℂ → E} {P : Finset ℂ} {U : Set ℂ}
    {r r' : ℝ} (hr : 0 < r) (hrr' : r < r') (hU : IsOpen U)
    (hP' : ∀ ρ ∈ P, closedBall ρ r' ⊆ U)
    (hdisj' : (P : Set ℂ).Pairwise fun ρ ρ' ↦ Disjoint (closedBall ρ r') (closedBall ρ' r'))
    (hd : DifferentiableOn ℂ f (U \ P)) {ρ : ℂ} (hρ : ρ ∈ P) :
    EqOn (gluedRegular f P r r')
      (fun z ↦ (2 * π * I : ℂ)⁻¹ • (∮ w in C(ρ, r'), (w - z)⁻¹ • f w) -
        ∑ ρ' ∈ P.erase ρ, (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ', r), (z - w)⁻¹ • f w)
      (ball ρ r') := by
  classical
  intro z hz
  have hr' : 0 < r' := hr.trans hrr'
  have hsub_ann : closedBall ρ r' \ {ρ} ⊆ U \ P := fun w hw ↦
    ⟨hP' ρ hρ hw.1, fun hwP ↦ hw.2 <| by_contra fun hne ↦
      disjoint_left.1 (hdisj' hρ hwP (Ne.symm hne)) hw.1 (mem_closedBall_self hr'.le)⟩
  by_cases hzr : z ∈ closedBall ρ r
  · have hex : ∃ ρ' ∈ P, z ∈ closedBall ρ' r := ⟨ρ, hρ, hzr⟩
    have hch : hex.choose = ρ := by_contra fun hne ↦
      disjoint_left.1 (hdisj' hex.choose_spec.1 hρ hne)
        (closedBall_subset_closedBall hrr'.le hex.choose_spec.2)
        (closedBall_subset_closedBall hrr'.le hzr)
    simp only [gluedRegular, hex, ↓reduceDIte, hch]
  · have hnone : ∀ ρ' ∈ P, z ∉ closedBall ρ' r := fun ρ' hρ' hz' ↦ by
      rcases eq_or_ne ρ' ρ with rfl | hne
      · exact hzr hz'
      · exact disjoint_left.1 (hdisj' hρ hρ' hne.symm) (ball_subset_closedBall hz)
          (closedBall_subset_closedBall hrr'.le hz')
    have hsub := sub_two_pi_I_inv_smul_circleIntegral_sub_inv_smul_eq hr countable_empty
      ⟨hz, hzr⟩
      (hd.continuousOn.mono fun w hw ↦
        hsub_ann ⟨hw.1, fun heq ↦ hw.2 (heq ▸ mem_ball_self hr)⟩)
      (fun w hw ↦ hd.differentiableAt ((hU.sdiff P.finite_toSet.isClosed).mem_nhds
        (hsub_ann ⟨ball_subset_closedBall hw.1.1,
          fun heq ↦ hw.1.2 (heq ▸ mem_closedBall_self hr.le)⟩)))
    rw [gluedRegular_eq_out hnone, ← Finset.add_sum_erase _ _ hρ, ← sub_sub, hsub]

/-- `gluedRegular` is complex differentiable at every point of each open ball `ball ρ r'`. -/
private theorem differentiableAt_gluedRegular_of_mem_ball {f : ℂ → E}
    {P : Finset ℂ} {U : Set ℂ} {r r' : ℝ} (hr : 0 < r) (hrr' : r < r') (hU : IsOpen U)
    (hP' : ∀ ρ ∈ P, closedBall ρ r' ⊆ U)
    (hdisj' : (P : Set ℂ).Pairwise fun ρ ρ' ↦ Disjoint (closedBall ρ r') (closedBall ρ' r'))
    (hd : DifferentiableOn ℂ f (U \ P)) {ρ z : ℂ} (hρ : ρ ∈ P) (hz : z ∈ ball ρ r') :
    DifferentiableAt ℂ (gluedRegular f P r r') z := by
  classical
  have hr' : 0 < r' := hr.trans hrr'
  have hcont_r' := continuousOn_sphere_of_closedBall_subset hr' le_rfl hP' hdisj' hd.continuousOn hρ
  have hz' : z ∉ sphere ρ |r'| := by
    rw [abs_of_pos hr', mem_sphere]; exact ne_of_lt (mem_ball.1 hz)
  have hint : DifferentiableAt ℂ (fun s ↦ (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ, r'), (w - s)⁻¹ • f w)
      z := (hasDerivAt_circleIntegral_sub_inv_smul
        (hcont_r'.circleIntegrable hr'.le) hz').differentiableAt.const_smul _
  have hsum : DifferentiableAt ℂ
      (fun s ↦ ∑ ρ' ∈ P.erase ρ, (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ', r), (s - w)⁻¹ • f w) z :=
    differentiableAt_sum_exteriorCauchy hr.le (fun ρ' hρ' ↦
      circleIntegrable_of_closedBall_subset hr hrr'.le hP' hdisj' hd.continuousOn ρ'
        (Finset.mem_of_mem_erase hρ')) fun ρ' hρ' hzr' ↦
        disjoint_left.1 (hdisj' hρ (Finset.mem_of_mem_erase hρ')
          (Finset.ne_of_mem_erase hρ').symm) (ball_subset_closedBall hz)
          (closedBall_subset_closedBall hrr'.le hzr')
  exact (hint.sub hsum).congr_of_eventuallyEq <|
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz)
      (gluedRegular_eq_on_ball hr hrr' hU hP' hdisj' hd hρ)

/-- `gluedRegular` is continuous on `D`. -/
private theorem continuousOn_gluedRegular {D : Set ℂ} {r r' : ℝ} (hr : 0 < r)
    (hrr' : r < r') {P : Finset ℂ}
    (hP' : ∀ ρ ∈ P, closedBall ρ r' ⊆ interior D)
    (hdisj' : (P : Set ℂ).Pairwise fun ρ ρ' ↦ Disjoint (closedBall ρ r') (closedBall ρ' r'))
    {f : ℂ → E} (hc : ContinuousOn f (D \ P))
    (hd : DifferentiableOn ℂ f (interior D \ P)) :
    ContinuousOn (gluedRegular f P r r') D := by
  intro z hz
  by_cases hex : ∃ ρ ∈ P, z ∈ closedBall ρ r
  · obtain ⟨ρ, hρ, hzr⟩ := hex
    exact (differentiableAt_gluedRegular_of_mem_ball hr hrr' isOpen_interior hP' hdisj' hd hρ
      (closedBall_subset_ball hrr' hzr)).continuousAt.continuousWithinAt
  · push Not at hex
    have hzP : z ∉ (P : Set ℂ) := fun hzP ↦ hex z hzP (mem_closedBall_self hr.le)
    have hDP : D \ P ∈ 𝓝[D] z :=
      mem_nhdsWithin.2 ⟨(P : Set ℂ)ᶜ, P.finite_toSet.isClosed.isOpen_compl, hzP,
        fun w hw ↦ ⟨hw.2, hw.1⟩⟩
    have hloc : ContinuousWithinAt
        (fun s ↦ f s - ∑ ρ ∈ P, (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ, r), (s - w)⁻¹ • f w) D z :=
      ((hc.continuousWithinAt ⟨hz, hzP⟩).mono_of_mem_nhdsWithin hDP).sub
        (differentiableAt_sum_exteriorCauchy hr.le
          (circleIntegrable_of_closedBall_subset hr hrr'.le hP' hdisj' hd.continuousOn)
          hex).continuousAt.continuousWithinAt
    have heq := gluedRegular_eventuallyEq_out (f := f) (r' := r') hex
    exact hloc.congr_of_eventuallyEq (nhdsWithin_le_nhds heq) heq.eq_of_nhds

/-- `gluedRegular` is complex differentiable on `interior D`. -/
private theorem differentiableOn_gluedRegular {D : Set ℂ} {r r' : ℝ}
    (hr : 0 < r) (hrr' : r < r') {P : Finset ℂ}
    (hP' : ∀ ρ ∈ P, closedBall ρ r' ⊆ interior D)
    (hdisj' : (P : Set ℂ).Pairwise fun ρ ρ' ↦ Disjoint (closedBall ρ r') (closedBall ρ' r'))
    {f : ℂ → E} (hd : DifferentiableOn ℂ f (interior D \ P)) :
    DifferentiableOn ℂ (gluedRegular f P r r') (interior D) := by
  intro z hz
  by_cases hex : ∃ ρ ∈ P, z ∈ closedBall ρ r
  · obtain ⟨ρ, hρ, hzr⟩ := hex
    exact (differentiableAt_gluedRegular_of_mem_ball hr hrr' isOpen_interior hP' hdisj' hd hρ
      (closedBall_subset_ball hrr' hzr)).differentiableWithinAt
  · push Not at hex
    have hloc : DifferentiableAt ℂ
        (fun s ↦ f s - ∑ ρ ∈ P, (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ, r), (s - w)⁻¹ • f w) z :=
      (hd.differentiableAt ((isOpen_interior.sdiff P.finite_toSet.isClosed).mem_nhds
        ⟨hz, fun hzP ↦ hex z hzP (mem_closedBall_self hr.le)⟩)).sub
        (differentiableAt_sum_exteriorCauchy hr.le
          (circleIntegrable_of_closedBall_subset hr hrr'.le hP' hdisj' hd.continuousOn) hex)
    exact (hloc.congr_of_eventuallyEq
      (gluedRegular_eventuallyEq_out (r' := r') hex)).differentiableWithinAt

/-- **Finite-disc singularity removal.** Let `E` be a complete complex normed space, `D : Set ℂ`,
`r > 0`, and `P` a finite set whose closed discs `closedBall ρ r` are pairwise disjoint and
contained in `interior D`. If `f : ℂ → E` is continuous on `D \ P` and complex differentiable on
`interior D \ P`, then there is a function `g` continuous on `D` and complex differentiable on
`interior D` that agrees with `f z - ∑ ρ ∈ P, (2πi)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w` outside
`⋃ ρ ∈ P, closedBall ρ r`.

No open neighbourhood of `D` and no meromorphy at `P` are assumed, so points of `P` may be
essential singularities. -/
theorem exists_continuousOn_differentiableOn_sub_sum_circleIntegral {D : Set ℂ} {r : ℝ}
    (hr : 0 < r) {P : Finset ℂ} (hP : ∀ ρ ∈ P, closedBall ρ r ⊆ interior D)
    (hdisj : (P : Set ℂ).Pairwise fun ρ ρ' ↦ Disjoint (closedBall ρ r) (closedBall ρ' r))
    {f : ℂ → E} (hc : ContinuousOn f (D \ P)) (hd : DifferentiableOn ℂ f (interior D \ P)) :
    ∃ g : ℂ → E, ContinuousOn g D ∧ DifferentiableOn ℂ g (interior D) ∧
      EqOn g (fun z ↦ f z - ∑ ρ ∈ P, (2 * π * I : ℂ)⁻¹ • ∮ w in C(ρ, r), (z - w)⁻¹ • f w)
        (⋃ ρ ∈ P, closedBall ρ r)ᶜ := by
  obtain ⟨r', hrr', hP', hdisj'⟩ := TauCeti.exists_gt_closedBall_subset_and_pairwiseDisjoint
    (U := fun _ ↦ interior D) (fun _ _ ↦ isOpen_interior) hP hdisj
  refine ⟨gluedRegular f P r r',
    continuousOn_gluedRegular hr hrr' hP' hdisj' hc hd,
    differentiableOn_gluedRegular hr hrr' hP' hdisj' hd,
    fun z hz ↦ ?_⟩
  simp only [mem_compl_iff, mem_iUnion, not_exists] at hz
  exact gluedRegular_eq_out hz

end TauCeti.Contour
