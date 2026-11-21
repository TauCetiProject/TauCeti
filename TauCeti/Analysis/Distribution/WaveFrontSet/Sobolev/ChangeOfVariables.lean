/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ChangeOfVariables
public import TauCeti.Analysis.Distribution.TemperedDistribution.ChangeOfVariables
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Sobolev.BesselPotential.ChangeOfVariables
import TauCeti.Geometry.Manifold.Diffeomorph.Germ

/-!
# Local Sobolev regularity under smooth changes of variables

Let `e` be a smooth open partial homeomorphism of a finite-dimensional real inner product space
`E` with smooth inverse, `U` an open subset of its source and `Ω` an open set containing `e '' U`.
A complex distribution `T` on `Ω` pulls back to the distribution `e^* T` on `U`
(`Distribution.compCLMOfOpenPartialHomeomorph`). This file proves that being `H^s` near a point
(`Distribution.IsLocallySobolevAt`) is invariant under this pullback, for every real `s`:

`e^* T` is `H^s` near `x` if and only if `T` is `H^s` near `e x`

(`Distribution.isLocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff`), so the `H^s` singular
support transforms by `e`: `singsupp_s (e^* T) = U ∩ e⁻¹ (singsupp_s T)`
(`Distribution.sobolevSingularSupport_compCLMOfOpenPartialHomeomorph`). Since chart transitions
are such maps `e`, this is the chart-change invariance needed to define the local Sobolev spaces
`H^s_loc` on manifolds chart by chart. For sections of vector bundles, invariance under frame
changes (multiplication by smooth matrix-valued functions) is needed in addition; this file does
not prove it.

## The argument

Pullback along a bijection `Φ` of `E` such that `Φ` and `Φ⁻¹` are smooth with bounded
derivatives of every positive order preserves the Bessel-potential space `H^s`
(`TemperedDistribution.MemSobolev.compCLM`). Two steps reduce the local statement to this global
statement.

* **Extension of the change of variables.** Near `x`, `e` agrees with such a global bijection `Φ`
  (`TauCeti.exists_equiv_eventuallyEq_of_det_fderiv_ne_zero`), which is affine outside a compact
  set.
* **Localized tempered comparison.** If `Φ = e` on an open set `N ⊆ U` and the test function `χ`
  equals `1` on `e '' N`, then on `N` the pullback `e^* T` is the tempered pullback `Φ^* (χ T)` of
  the cut-off distribution `χ T`
  (`Distribution.restrictCLM_compCLMOfOpenPartialHomeomorph_eq_toDistribution`). Both
  pair a test function `φ` supported in `N` with `T` through the pushforward density
  `y ↦ |det D e⁻¹ (y)| φ (e⁻¹ y)`, which is supported in `e '' N`.

If `T` is `H^s` near `e x`, then `χ T ∈ H^s` for `χ` supported near `e x`, so `Φ^* (χ T) ∈ H^s`,
and `e^* T` is `H^s` near `x`. The converse is the same statement for `e⁻¹`.

## Main results

* `Distribution.restrictCLM_compCLMOfOpenPartialHomeomorph_eq_toDistribution`: the localized
  tempered comparison.
* `Distribution.IsLocallySobolevAt.compCLMOfOpenPartialHomeomorph`,
  `Distribution.isLocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff`: invariance of local
  Sobolev regularity.
* `Distribution.sobolevSingularSupport_compCLMOfOpenPartialHomeomorph`: the `H^s` singular
  support of a pullback.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §1
  (invariance of `H^s` under diffeomorphisms, and the local Sobolev spaces on manifolds).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  Appendix B.1 (`H^s_loc` is invariant under diffeomorphisms).
-/

public section

noncomputable section

open Set Filter Metric TopologicalSpace TestFunction
open scoped Distributions Topology ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {e : OpenPartialHomeomorph E E} {U Ω : Opens E}
  {he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source} {he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target}
  {hU : (U : Set E) ⊆ e.source} {hUΩ : MapsTo e U Ω}

omit [MeasurableSpace E] [BorelSpace E] in
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

/-- **Pulling back preserves local Sobolev regularity.** If `T` is `H^s` near `e x`, then its
pullback `e^* T` along `e` is `H^s` near `x`. -/
theorem IsLocallySobolevAt.compCLMOfOpenPartialHomeomorph {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E}
    (hx : x ∈ U) (hT : T.IsLocallySobolevAt s (e x)) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsLocallySobolevAt s x := by
  have hxs : x ∈ e.source := hU hx
  -- `φ T ∈ H^s` for every test function `φ` supported in an open neighbourhood `W` of `e x`.
  obtain ⟨W₀, hW₀, hWT⟩ := hT.exists_nhds_forall_memSobolev_cutoffTempered
  obtain ⟨W, hWW₀, hW, hxW⟩ := _root_.mem_nhds_iff.1 hW₀
  -- A global change of variables `Φ` with bounded derivatives agreeing with `e` near `x`.
  obtain ⟨Φ, hΦ, hΨ, hΦb, hΨb, hΦe⟩ := TauCeti.exists_equiv_eventuallyEq_of_det_fderiv_ne_zero
    (eventually_of_mem (e.open_source.mem_nhds hxs) fun y hy ↦
      (he.contDiffAt (e.open_source.mem_nhds hy)))
    (e.det_fderiv_ne_zero_of_contDiffOn he he' (by simp) hxs)
  have hΦt := Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_of_pos hΦ hΦb
  have hΨt := Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_of_pos hΨ hΨb
  -- A closed ball around `x` in `U` on which `Φ = e`, mapped by `e` into `W ∩ Ω`.
  have hxU : ∀ᶠ y in 𝓝 x, y ∈ U := U.isOpen.mem_nhds hx
  have hxWΩ : ∀ᶠ y in 𝓝 x, e y ∈ W ∩ Ω :=
    e.continuousAt hxs |>.preimage_mem_nhds ((hW.inter Ω.isOpen).mem_nhds ⟨hxW, hUΩ hx⟩)
  have hev : ∀ᶠ y in 𝓝 x, Φ y = e y ∧ y ∈ U ∧ e y ∈ W ∩ Ω := hΦe.and (hxU.and hxWΩ)
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 hev
  have hball : closedBall x (ε / 2) ⊆ ball x ε := closedBall_subset_ball (by linarith)
  let N : Opens E := ⟨ball x (ε / 2), isOpen_ball⟩
  have hxN : x ∈ N := mem_ball_self (by linarith)
  have hNU : N ≤ U := fun y hy ↦ (hεP (hball (ball_subset_closedBall hy))).2.1
  have hΦeN : EqOn Φ e N := fun y hy ↦ (hεP (hball (ball_subset_closedBall hy))).1
  -- A cutoff `χ` supported in `W ∩ Ω` which is `1` on `e '' closedBall x (ε / 2)`.
  have hKs : closedBall x (ε / 2) ⊆ e.source := fun y hy ↦ hU (hεP (hball hy)).2.1
  have hK : IsCompact (e '' closedBall x (ε / 2)) :=
    (isCompact_closedBall x (ε / 2)).image_of_continuousOn (e.continuousOn.mono hKs)
  have hKW : e '' closedBall x (ε / 2) ⊆ W ∩ Ω := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hεP (hball hy)).2.2
  obtain ⟨χ, hχ1, hχW⟩ :=
    exists_complex_cutoff_tsupport_subset (n := ⊤) hK (hW.inter Ω.isOpen) hKW inter_subset_right
  have hχN : EqOn χ 1 (e '' N) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ((eventually_nhdsSet_iff_forall.1 hχ1) _ ⟨y, ball_subset_closedBall hy, rfl⟩).self_of_nhds
  have hmem := (hWT χ (hχW.trans (inter_subset_left.trans hWW₀))).compCLM hΦt hΨt
    (fun n ↦ hΦb (n + 1) (Nat.le_add_left 1 n)) (fun n ↦ hΨb (n + 1) (Nat.le_add_left 1 n))
  rw [← isLocallySobolevAt_restrictCLM_iff hNU hxN,
    restrictCLM_compCLMOfOpenPartialHomeomorph_eq_toDistribution hNU hΦt hΨt hΦeN T hχN]
  exact hmem.isLocallySobolevAt_toDistribution hxN

/-- **Local Sobolev regularity is invariant under changes of variables.** The pullback `e^* T` of
a distribution `T` along `e` is `H^s` near a point `x ∈ U` exactly when `T` is `H^s` near
`e x`. -/
theorem isLocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E}
    (hx : x ∈ U) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsLocallySobolevAt s x ↔
      T.IsLocallySobolevAt s (e x) := by
  refine ⟨fun h ↦ ?_, IsLocallySobolevAt.compCLMOfOpenPartialHomeomorph hx⟩
  -- Pull back along `e⁻¹` from the open set `V = e '' U`, which returns the restriction `T|_V`.
  let V : Opens E := ⟨e '' U, (e.isOpen_image_iff_of_subset_source hU).2 U.isOpen⟩
  have hV : (V : Set E) ⊆ e.symm.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact e.map_source (hU hy)
  have hVU : MapsTo e.symm V U := by
    rintro _ ⟨y, hy, rfl⟩
    rwa [e.left_inv (hU hy)]
  have hUV : MapsTo e U V := fun y hy ↦ ⟨y, hy, rfl⟩
  have hVΩ : V ≤ Ω := by
    rintro _ ⟨y, hy, rfl⟩
    exact hUΩ hy
  have hexV : e x ∈ V := ⟨x, hx, rfl⟩
  have hres : compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T =
      compCLMOfOpenPartialHomeomorph e he he' hU hUV (restrictCLM T) := by
    rw [← restrictCLM_compCLMOfOpenPartialHomeomorph le_rfl hVΩ, restrictCLM_self]
  rw [hres, ← e.left_inv (hU hx)] at h
  have := h.compCLMOfOpenPartialHomeomorph (e := e.symm) (he := he') (he' := by simpa using he)
    (hU := hV) (hUΩ := hVU) hexV
  have hid := compCLMOfOpenPartialHomeomorph_symm_apply_apply (e := e) (he := he) (he' := he')
    (hU := hU) (hV := hV) (hVU := hVU) (hUV := hUV) (he₁ := he') (he₁' := by simpa using he)
    (restrictCLM T : 𝓓'(V, ℂ))
  rw [hid] at this
  exact (isLocallySobolevAt_restrictCLM_iff hVΩ hexV).1 this

/-- **The `H^s` singular support of a pullback.** Pulling back along `e` transforms the `H^s`
singular support by `e`: `singsupp_s (e^* T) = U ∩ e⁻¹ (singsupp_s T)`. -/
theorem sobolevSingularSupport_compCLMOfOpenPartialHomeomorph (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    sobolevSingularSupport s (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T) =
      (U : Set E) ∩ e ⁻¹' sobolevSingularSupport s T := by
  ext x
  simp only [mem_sobolevSingularSupport_iff, mem_inter_iff, mem_preimage, SetLike.mem_coe]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, hUΩ hx, fun h' ↦ h ((isLocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff hx).2 h')⟩
  · rintro ⟨hx, -, h⟩
    exact ⟨hx, fun h' ↦ h ((isLocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff hx).1 h')⟩

end Distribution
