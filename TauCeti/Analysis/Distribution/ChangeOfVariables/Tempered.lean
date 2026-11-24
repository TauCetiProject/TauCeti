/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ChangeOfVariables
public import TauCeti.Analysis.Distribution.TemperedDistribution.ChangeOfVariables
public import TauCeti.Analysis.Distribution.TemperedDistribution.Cutoff
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Geometry.Manifold.Diffeomorph.Germ

/-!
# Local pullbacks of distributions as tempered pullbacks

Let `e` be a smooth open partial homeomorphism of a finite-dimensional real inner product space
`E` with smooth inverse, `U` an open subset of its source and `Ω` an open set containing `e '' U`.
A complex distribution `T` on `Ω` pulls back to the distribution `e^* T` on `U`
(`Distribution.compCLMOfOpenPartialHomeomorph`). This file shows that near each point of `U`, this
pullback is the pullback of a tempered distribution along a global change of variables, so that the
mapping theorems for tempered distributions on function spaces of `E` apply to it.

* **Localized tempered comparison.** If a bijection `Φ` of `E` agrees with `e` on an open set
  `N ⊆ U` and the test function `χ` equals `1` on `e '' N`, then on `N` the pullback `e^* T` is
  the tempered pullback `Φ^* (χ T)` of the cut-off distribution `χ T`
  (`Distribution.restrictCLM_compCLMOfOpenPartialHomeomorph_eq_toDistribution`). Both pair a test
  function `φ` supported in `N` with `T` through the pushforward density
  `y ↦ |det D e⁻¹ (y)| φ (e⁻¹ y)`, which is supported in `e '' N`.
* **Localization.** Near `x ∈ U`, `e` agrees with a bijection `Φ` of `E` such that `Φ` and `Φ⁻¹`
  are smooth with bounded derivatives of every positive order
  (`TauCeti.exists_equiv_eventuallyEq_of_det_fderiv_ne_zero`), and the cutoff `χ` can be supported
  in any prescribed neighbourhood of `e x`
  (`Distribution.exists_restrictCLM_compCLMOfOpenPartialHomeomorph_eq_toDistribution`).

These are the two steps reducing the invariance of local Sobolev or Besov regularity under smooth
changes of variables to the global mapping theorems
(`Distribution.IsLocallySobolevAt.compCLMOfOpenPartialHomeomorph`,
`Distribution.IsLocallyMemBesovAt.compCLMOfOpenPartialHomeomorph`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §6.1 (pullback of
  distributions by diffeomorphisms) and *III*, Appendix B.1 (invariance of the local Sobolev
  spaces, by localization).
-/

public section

noncomputable section

open Set Filter Metric TopologicalSpace TestFunction
open scoped Distributions Topology ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {e : OpenPartialHomeomorph E E} {U Ω : Opens E}
  {he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source} {he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target}
  {hU : (U : Set E) ⊆ e.source} {hUΩ : MapsTo e U Ω}

/-- **Localized tempered comparison.** Let `Φ` be a bijection of `E` such that `Φ` and `Φ⁻¹` have
temperate growth, and which agrees with `e` on an open set `N ⊆ U`. If the test function `χ` equals
`1` on `e '' N`, then on `N` the pullback `e^* T` is the pullback `Φ^* (χ T)` of the tempered
distribution `χ T`. -/
theorem restrictCLM_compCLMOfOpenPartialHomeomorph_eq_toDistribution {N : Opens E}
    (hNU : N ≤ U) {Φ : E ≃ E} (hΦ : (Φ : E → E).HasTemperateGrowth)
    (hΨ : (Φ.symm : E → E).HasTemperateGrowth) (hΦe : EqOn Φ e N) (T : 𝓓'(Ω, ℂ))
    {χ : 𝓓(Ω, ℂ)} (hχ : EqOn χ 1 (e '' N)) :
    (restrictCLM (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T) : 𝓓'(N, ℂ)) =
      TemperedDistribution.toDistribution N
        (TemperedDistribution.compCLM ℂ Φ hΦ hΨ (T.cutoffTempered χ)) := by
  ext φ
  rw [restrictCLM_apply, compCLMOfOpenPartialHomeomorph_apply,
    TemperedDistribution.toDistribution_apply, TemperedDistribution.compCLM_apply_apply,
    ← complexPairing_postcompCLM_ofRealCLM]
  refine (cutoffTempered_apply T χ fun y ↦ ?_).symm
  -- `φ` vanishes off `N`, and `Φ⁻¹ = e⁻¹` on the open set `e '' N`.
  have hφ (z : E) (hz : z ∉ (N : Set E)) : φ z = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hz (φ.tsupport_subset h)
  have hNs : (N : Set E) ⊆ e.source := fun z hz ↦ hU (hNU hz)
  have hopen : IsOpen (e '' N) := (e.isOpen_image_iff_of_subset_source hNs).2 N.isOpen
  have hsymm : EqOn Φ.symm e.symm (e '' N) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [e.left_inv (hNs hz), Equiv.symm_apply_eq, hΦe hz]
  simp only [postcompCLM_apply, Function.comp_apply, Complex.ofRealCLM_apply,
    SchwartzMap.pushforwardCLM_apply, toSchwartzMapCLM_apply, smul_eq_mul]
  by_cases hy : y ∈ e '' N
  · obtain ⟨z, hz, rfl⟩ := hy
    have hev : (Φ.symm : E → E) =ᶠ[𝓝 (e z)] e.symm :=
      eventually_of_mem (hopen.mem_nhds ⟨z, hz, rfl⟩) hsymm
    have hd : fderiv ℝ Φ.symm (e z) = fderiv ℝ e.symm (e z) := hev.fderiv_eq
    rw [pushforwardCLM_apply_of_mem _ (e.map_source (hNs hz)), hχ ⟨z, hz, rfl⟩, hd,
      hsymm ⟨z, hz, rfl⟩]
    simp [hNU]
  · have h₁ : Φ.symm y ∉ (N : Set E) := fun h ↦ hy ⟨_, h, by rw [← hΦe h, Equiv.apply_symm_apply]⟩
    have h₂ : pushforwardCLM e he he' hU hUΩ (monoCLM ℝ φ) y = 0 := by
      by_cases hyt : y ∈ e.target
      · rw [pushforwardCLM_apply_of_mem _ hyt]
        have : e.symm y ∉ (N : Set E) := fun h ↦ hy ⟨_, h, e.right_inv hyt⟩
        simp [hNU, hφ _ this]
      · exact pushforwardCLM_apply_of_notMem _ hyt
    simp [h₂, hφ _ h₁]

/-- **Localization of a pullback.** Near a point `x ∈ U`, the pullback `e^* T` is the tempered
pullback `Φ^* (χ T)` of a cut-off of `T`: there are a bijection `Φ` of `E` such that `Φ` and `Φ⁻¹`
are smooth with bounded derivatives of every positive order, an open neighbourhood `N ⊆ U` of `x`
and a test function `χ` supported in a prescribed neighbourhood `W` of `e x` such that `e^* T` and
`Φ^* (χ T)` agree on `N`. -/
theorem exists_restrictCLM_compCLMOfOpenPartialHomeomorph_eq_toDistribution {x : E} (hx : x ∈ U)
    {W : Set E} (hW : W ∈ 𝓝 (e x)) (T : 𝓓'(Ω, ℂ)) :
    ∃ (Φ : E ≃ E) (hΦ : (Φ : E → E).HasTemperateGrowth)
      (hΨ : (Φ.symm : E → E).HasTemperateGrowth) (N : Opens E) (_ : N ≤ U) (χ : 𝓓(Ω, ℂ)),
      (∀ n, 1 ≤ n → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n Φ y‖ ≤ C) ∧
      (∀ n, 1 ≤ n → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n Φ.symm y‖ ≤ C) ∧ x ∈ N ∧ tsupport χ ⊆ W ∧
      (restrictCLM (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T) : 𝓓'(N, ℂ)) =
        TemperedDistribution.toDistribution N
          (TemperedDistribution.compCLM ℂ Φ hΦ hΨ (T.cutoffTempered χ)) := by
  have hxs : x ∈ e.source := hU hx
  obtain ⟨W', hW'W, hW', hxW'⟩ := _root_.mem_nhds_iff.1 hW
  -- A global change of variables `Φ` with bounded derivatives agreeing with `e` near `x`.
  obtain ⟨Φ, hΦ, hΨ, hΦb, hΨb, hΦe⟩ := TauCeti.exists_equiv_eventuallyEq_of_det_fderiv_ne_zero
    (eventually_of_mem (e.open_source.mem_nhds hxs) fun y hy ↦
      (he.contDiffAt (e.open_source.mem_nhds hy)))
    (e.det_fderiv_ne_zero_of_contDiffOn he he' (by simp) hxs)
  have hΦt := Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_of_pos hΦ hΦb
  have hΨt := Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_of_pos hΨ hΨb
  -- A closed ball around `x` in `U` on which `Φ = e`, mapped by `e` into `W' ∩ Ω`.
  have hxU : ∀ᶠ y in 𝓝 x, y ∈ U := U.isOpen.mem_nhds hx
  have hxWΩ : ∀ᶠ y in 𝓝 x, e y ∈ W' ∩ Ω :=
    e.continuousAt hxs |>.preimage_mem_nhds ((hW'.inter Ω.isOpen).mem_nhds ⟨hxW', hUΩ hx⟩)
  have hev : ∀ᶠ y in 𝓝 x, Φ y = e y ∧ y ∈ U ∧ e y ∈ W' ∩ Ω := hΦe.and (hxU.and hxWΩ)
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 hev
  have hball : closedBall x (ε / 2) ⊆ ball x ε := closedBall_subset_ball (by linarith)
  let N : Opens E := ⟨ball x (ε / 2), isOpen_ball⟩
  have hNU : N ≤ U := fun y hy ↦ (hεP (hball (ball_subset_closedBall hy))).2.1
  have hΦeN : EqOn Φ e N := fun y hy ↦ (hεP (hball (ball_subset_closedBall hy))).1
  -- A cutoff `χ` supported in `W' ∩ Ω` which is `1` on `e '' closedBall x (ε / 2)`.
  have hKs : closedBall x (ε / 2) ⊆ e.source := fun y hy ↦ hU (hεP (hball hy)).2.1
  have hK : IsCompact (e '' closedBall x (ε / 2)) :=
    (isCompact_closedBall x (ε / 2)).image_of_continuousOn (e.continuousOn.mono hKs)
  have hKW : e '' closedBall x (ε / 2) ⊆ W' ∩ Ω := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hεP (hball hy)).2.2
  obtain ⟨χ, hχ1, hχW⟩ :=
    exists_complex_cutoff_tsupport_subset (n := ⊤) hK (hW'.inter Ω.isOpen) hKW inter_subset_right
  have hχN : EqOn χ 1 (e '' N) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ((eventually_nhdsSet_iff_forall.1 hχ1) _ ⟨y, ball_subset_closedBall hy, rfl⟩).self_of_nhds
  exact ⟨Φ, hΦt, hΨt, N, hNU, χ, hΦb, hΨb, mem_ball_self (by linarith),
    hχW.trans (inter_subset_left.trans hW'W),
    restrictCLM_compCLMOfOpenPartialHomeomorph_eq_toDistribution hNU hΦt hΨt hΦeN T hχN⟩

end Distribution
