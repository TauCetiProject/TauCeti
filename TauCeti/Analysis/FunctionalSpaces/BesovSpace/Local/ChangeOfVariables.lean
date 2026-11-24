/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ChangeOfVariables
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Local
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.ChangeOfVariables
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.ChangeOfVariables
import TauCeti.Geometry.Manifold.Diffeomorph.Germ

/-!
# Local Besov regularity under smooth changes of variables

Let `e` be a smooth open partial homeomorphism of a finite-dimensional real inner product space
`E` with smooth inverse, `U` an open subset of its source and `Ω` an open set containing `e '' U`.
A complex distribution `T` on `Ω` pulls back to the distribution `e^* T` on `U`
(`Distribution.compCLMOfOpenPartialHomeomorph`). This file proves that being `B^s_{p,q}` near a
point (`Distribution.IsLocallyMemBesovAt`) is invariant under this pullback, for every real `s` and
all `1 ≤ p, q ≤ ∞`:

`e^* T` is `B^s_{p,q}` near `x` if and only if `T` is `B^s_{p,q}` near `e x`

(`Distribution.isLocallyMemBesovAt_compCLMOfOpenPartialHomeomorph_iff`). For `p = q = ∞` this is
the invariance of the local Hölder–Zygmund spaces `𝒞^s_loc`, including negative orders. Since chart
transitions are such maps `e`, this is the chart-change invariance needed to define local Besov and
Zygmund regularity on manifolds chart by chart.

## The argument

This is the argument for the Sobolev scale
(`Distribution.isLocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff`), with the Besov pullback
theorem in place of the Sobolev one. Pullback along a bijection `Φ` of `E` such that `Φ` and `Φ⁻¹`
are smooth with bounded derivatives of every positive order preserves `B^s_{p,q}`
(`TemperedDistribution.MemBesov.compCLM`). Near `x`, `e` agrees with such a bijection `Φ`
(`TauCeti.exists_equiv_eventuallyEq_of_det_fderiv_ne_zero`), and if the test function `χ` equals
`1` on `e '' N` for an open set `N` on which `Φ = e`, then on `N` the pullback `e^* T` is the
tempered pullback `Φ^* (χ T)`
(`Distribution.restrictCLM_compCLMOfOpenPartialHomeomorph_eq_toDistribution`). If `T` is
`B^s_{p,q}` near `e x`, then `χ T ∈ B^s_{p,q}` for `χ` supported near `e x`, so
`Φ^* (χ T) ∈ B^s_{p,q}`, and `e^* T` is `B^s_{p,q}` near `x`. The converse is the same statement
for `e⁻¹`.

## Main results

* `Distribution.IsLocallyMemBesovAt.compCLMOfOpenPartialHomeomorph`,
  `Distribution.isLocallyMemBesovAt_compCLMOfOpenPartialHomeomorph_iff`: invariance of local Besov
  regularity under smooth changes of variables.

## References

* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §2.10.2 (diffeomorphisms of `ℝⁿ`
  preserve the Besov spaces) and §3.2.2 (Besov spaces on manifolds, defined chart by chart).
-/

public section

noncomputable section

open Set Filter Metric TopologicalSpace TestFunction
open scoped Distributions Topology ContDiff ENNReal

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {e : OpenPartialHomeomorph E E} {U Ω : Opens E}
  {he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source} {he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target}
  {hU : (U : Set E) ⊆ e.source} {hUΩ : MapsTo e U Ω}
  {φ : ContDiffBump (0 : E)} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **Pulling back preserves local Besov regularity.** If `T` is `B^s_{p,q}` near `e x`, then its
pullback `e^* T` along `e` is `B^s_{p,q}` near `x`. -/
theorem IsLocallyMemBesovAt.compCLMOfOpenPartialHomeomorph {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E}
    (hx : x ∈ U) (hT : T.IsLocallyMemBesovAt φ s p q (e x)) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsLocallyMemBesovAt φ s p q x := by
  have hxs : x ∈ e.source := hU hx
  -- `ψ T ∈ B^s_{p,q}` for every test function `ψ` supported in an open neighbourhood `W` of `e x`.
  obtain ⟨W₀, hW₀, -, hWT⟩ := isLocallyMemBesovAt_iff.1 hT
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
    (fun n hn _ ↦ hΦb n hn) (fun n hn _ ↦ hΨb n hn)
  rw [← isLocallyMemBesovAt_restrictCLM_iff hNU hxN,
    restrictCLM_compCLMOfOpenPartialHomeomorph_eq_toDistribution hNU hΦt hΨt hΦeN T hχN]
  exact hmem.isLocallyMemBesovAt_toDistribution hxN

/-- **Local Besov regularity is invariant under changes of variables.** The pullback `e^* T` of
a distribution `T` along `e` is `B^s_{p,q}` near a point `x ∈ U` exactly when `T` is
`B^s_{p,q}` near `e x`. -/
theorem isLocallyMemBesovAt_compCLMOfOpenPartialHomeomorph_iff {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E}
    (hx : x ∈ U) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsLocallyMemBesovAt φ s p q x ↔
      T.IsLocallyMemBesovAt φ s p q (e x) := by
  refine ⟨fun h ↦ ?_, IsLocallyMemBesovAt.compCLMOfOpenPartialHomeomorph hx⟩
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
  exact (isLocallyMemBesovAt_restrictCLM_iff hVΩ hexV).1 this

end Distribution
