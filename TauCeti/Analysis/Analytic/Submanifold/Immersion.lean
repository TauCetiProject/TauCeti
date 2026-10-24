/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import TauCeti.Analysis.Analytic.Submanifold.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Analytic.Inverse

/-!
# Analytic immersions parametrize analytic submanifolds

Let `p : 𝕜ᵈ → 𝕜ⁿ` be analytic at `u₀` with injective derivative there. If `p` maps a
neighbourhood of `u₀` into a set `T`, and every point of `T` close to `p u₀` is the image of a
point close to `u₀`, then `T` is a `d`-dimensional analytic submanifold near `p u₀`, and `p` is
its local parametrization in an analytic chart
(`TauCeti.exists_isAnalyticChart_of_injective_fderiv`).

The second hypothesis says that `p` is relatively open at `u₀` as a map into `T`. It cannot be
dropped: near its crossing point, a figure-eight is not the image of a small interval.

The chart is built by extending the injective derivative to a linear automorphism `L` of `𝕜ⁿ`
(`Submodule.exists_linearEquiv_restrict_eq`) and inverting
`y ↦ p (y₁, …, y_d) + L y - L (y₁, …, y_d, 0)`, whose derivative at `(u₀, 0)` is `L`, by the
analytic inverse function theorem.

Conversely, the local parametrization `u ↦ e.symm (u, 0)` of a submanifold by an analytic chart
`e` is an immersion (`TauCeti.IsAnalyticChart.injective_fderiv_symm_firstCoords`).

## References

* S. G. Krantz and H. R. Parks, *A Primer of Real Analytic Functions*, second edition,
  Birkhäuser, 2002, Chapter 2 (real analytic submanifolds).
-/

public section

open Set Filter Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n d : ℕ}

/-- **Chart parametrizations are immersions.** If `d ≤ n`, the local parametrization
`u ↦ e.symm (u, 0)` of `S` by an analytic chart `e` has injective derivative at the coordinates
of each point of `S` in the source, since composing it with `e` gives the inclusion
`u ↦ (u, 0)`. -/
theorem IsAnalyticChart.injective_fderiv_symm_firstCoords {S : Set (Fin n → 𝕜)}
    {e : OpenPartialHomeomorph (Fin n → 𝕜) (Fin n → 𝕜)} {x : Fin n → 𝕜}
    (he : IsAnalyticChart d S e) (hx : x ∈ e.source) (hxS : x ∈ S) (hd : d ≤ n) :
    Function.Injective
      (fderiv 𝕜 (fun u ↦ e.symm (firstCoords 𝕜 d n u)) (firstCoords 𝕜 n d (e x))) := by
  set u₀ := firstCoords 𝕜 n d (e x)
  set φ : (Fin d → 𝕜) → Fin n → 𝕜 := fun u ↦ e.symm (firstCoords 𝕜 d n u)
  have hφ : AnalyticAt 𝕜 φ u₀ := he.analyticAt_symm_firstCoords hx hxS
  have heφ : (fun u ↦ e (φ u)) =ᶠ[𝓝 u₀] firstCoords 𝕜 d n := by
    have hmem : e.target ∈ 𝓝 (firstCoords 𝕜 d n u₀) := by
      rw [he.firstCoords_firstCoords_apply hx hxS]
      exact e.open_target.mem_nhds (e.map_source hx)
    filter_upwards [(firstCoords 𝕜 d n).continuous.continuousAt.preimage_mem_nhds hmem] with u hu
    exact e.right_inv hu
  have he' : DifferentiableAt 𝕜 e (φ u₀) := by
    rw [show φ u₀ = x from he.symm_firstCoords_firstCoords_apply hx hxS]
    exact (he.analyticOnNhd x hx).differentiableAt
  have hD : (fderiv 𝕜 e (φ u₀)).comp (fderiv 𝕜 φ u₀) = firstCoords 𝕜 d n := by
    rw [← fderiv_comp u₀ he' hφ.differentiableAt, ← (firstCoords 𝕜 d n).fderiv]
    exact heφ.fderiv_eq
  intro k k' hk
  simpa only [← ContinuousLinearMap.comp_apply, hD, firstCoords_firstCoords_of_le hd] using
    congrArg (firstCoords 𝕜 n d) (congrArg (fderiv 𝕜 e (φ u₀)) hk)

variable [CompleteSpace 𝕜]

/-- **Analytic immersions parametrize analytic submanifolds.** Let `p : 𝕜ᵈ → 𝕜ⁿ` be analytic at
`u₀` with injective derivative there, and let `T ⊆ 𝕜ⁿ` contain `p u` for all `u` near `u₀`.
Suppose that, for every neighbourhood `V` of `u₀`, the image `p '' V` contains all points of `T`
near `p u₀`. Then `T` has an analytic chart `e` in dimension `d` around `p u₀` in which `p` is the
local parametrization: `p u₀` has first coordinates `u₀` in `e`, and `e.symm (u, 0) = p u` for
`u` near `u₀`. -/
theorem exists_isAnalyticChart_of_injective_fderiv {T : Set (Fin n → 𝕜)}
    {p : (Fin d → 𝕜) → Fin n → 𝕜} {u₀ : Fin d → 𝕜} (hp : AnalyticAt 𝕜 p u₀)
    (hinj : Function.Injective (fderiv 𝕜 p u₀)) (hT : ∀ᶠ u in 𝓝 u₀, p u ∈ T)
    (himage : ∀ V ∈ 𝓝 u₀, p '' V ∈ 𝓝[T] (p u₀)) :
    ∃ e : OpenPartialHomeomorph (Fin n → 𝕜) (Fin n → 𝕜), p u₀ ∈ e.source ∧
      IsAnalyticChart d T e ∧ firstCoords 𝕜 n d (e (p u₀)) = u₀ ∧
        ∀ᶠ u in 𝓝 u₀, e.symm (firstCoords 𝕜 d n u) = p u := by
  have hd : d ≤ n := by
    simpa using LinearMap.finrank_le_finrank_of_injective (f := (fderiv 𝕜 p u₀).toLinearMap) hinj
  set P := fderiv 𝕜 p u₀
  set ι := firstCoords 𝕜 d n
  set π := firstCoords 𝕜 n d
  have hπι (u : Fin d → 𝕜) : π (ι u) = u := firstCoords_firstCoords_of_le hd u
  -- Extend the injective derivative `P` from the coordinate subspace to an automorphism `L`.
  have hιinj : Function.Injective ι := fun u v huv ↦ by simpa [hπι] using congrArg π huv
  let ιP := (LinearEquiv.ofInjective ι.toLinearMap hιinj).symm.trans
    (LinearEquiv.ofInjective P.toLinearMap hinj)
  obtain ⟨L₀, hL₀⟩ := Submodule.exists_linearEquiv_restrict_eq ιP
  let L := L₀.toContinuousLinearEquiv
  have hLι (u : Fin d → 𝕜) : L (ι u) = P u := by
    have hu : (LinearEquiv.ofInjective ι.toLinearMap hιinj).symm ⟨ι u, mem_range_self u⟩ = u :=
      (LinearEquiv.ofInjective ι.toLinearMap hιinj).symm_apply_eq.2 rfl
    simpa [ιP, hu, L] using (hL₀ ⟨ι u, mem_range_self u⟩).symm
  let G : (Fin n → 𝕜) → Fin n → 𝕜 := fun y ↦ p (π y) + (L y - P (π y))
  have hGι (u : Fin d → 𝕜) : G (ι u) = p u := by simp [G, hπι, hLι]
  have hp' : AnalyticAt 𝕜 (fun y ↦ p (π y)) (ι u₀) :=
    hp.comp_of_eq (π.analyticAt _) (hπι u₀)
  have hG : AnalyticAt 𝕜 G (ι u₀) :=
    hp'.add ((L.analyticAt _).sub ((P.comp π).analyticAt _))
  have hGd : fderiv 𝕜 G (ι u₀) = (L : (Fin n → 𝕜) →L[𝕜] Fin n → 𝕜) := by
    have h₀ : HasFDerivAt p P (π (ι u₀)) := by
      rw [hπι]
      exact hp.differentiableAt.hasFDerivAt
    have h₂ : HasFDerivAt G (P.comp π + ((L : (Fin n → 𝕜) →L[𝕜] Fin n → 𝕜) - P.comp π))
        (ι u₀) :=
      (h₀.comp (ι u₀) π.hasFDerivAt).add
        ((L : (Fin n → 𝕜) →L[𝕜] Fin n → 𝕜).hasFDerivAt.sub (P.comp π).hasFDerivAt)
    rw [h₂.fderiv]
    ext y
    simp
  -- Invert `G` near `(u₀, 0)`, on a source whose first coordinates are mapped into `T` by `p`.
  obtain ⟨V₀, hV₀T, hV₀, hu₀V₀⟩ := eventually_nhds_iff.1 hT
  have hs : π ⁻¹' V₀ ∈ 𝓝 (ι u₀) :=
    π.continuous.continuousAt.preimage_mem_nhds (by rw [hπι]; exact hV₀.mem_nhds hu₀V₀)
  obtain ⟨Θ, hΘ, hy₀, hΘs, hGan, hΘan⟩ := hG.exists_openPartialHomeomorph (L := L) hGd hs
  have hV : ι ⁻¹' Θ.source ∈ 𝓝 u₀ :=
    ι.continuous.continuousAt.preimage_mem_nhds (Θ.open_source.mem_nhds hy₀)
  obtain ⟨W, hW, hpW, hWT⟩ := mem_nhdsWithin.1 (himage _ hV)
  have hΘι {u : Fin d → 𝕜} (hu : ι u ∈ Θ.source) : Θ (ι u) = p u := by rw [hΘ, hGι]
  have hpu₀ : Θ (ι u₀) = p u₀ := hΘι hy₀
  have hsource : (Θ.symm.restrOpen W hW).source = Θ.target ∩ W := by
    rw [OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.symm_source]
  have htarget : (Θ.symm.restrOpen W hW).target ⊆ Θ.source := by
    simp only [OpenPartialHomeomorph.restrOpen_toPartialEquiv, PartialEquiv.restr_target,
      OpenPartialHomeomorph.coe_toPartialEquiv_symm, OpenPartialHomeomorph.symm_target]
    exact inter_subset_left
  refine ⟨Θ.symm.restrOpen W hW, hsource ▸ ⟨hpu₀ ▸ Θ.map_source hy₀, hpW⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hsource, OpenPartialHomeomorph.coe_restrOpen]
    exact hΘan.mono inter_subset_left
  · rw [OpenPartialHomeomorph.coe_restrOpen_symm, OpenPartialHomeomorph.symm_symm, hΘ]
    exact hGan.mono htarget
  · intro y hy
    rw [hsource] at hy
    obtain ⟨hyt, hyW⟩ := hy
    have hz : Θ.symm y ∈ Θ.source := Θ.map_target hyt
    rw [OpenPartialHomeomorph.coe_restrOpen, mem_ofPred_eq]
    constructor
    · -- A point of the slice is `(u, 0)`, and `Θ (u, 0) = p u` lies in `T`.
      intro hslice
      have hzι : ι (π (Θ.symm y)) = Θ.symm y := firstCoords_firstCoords_of_forall hslice
      have hz' : ι (π (Θ.symm y)) ∈ Θ.source := by rwa [hzι]
      have : p (π (Θ.symm y)) = y := by rw [← hΘι hz', hzι, Θ.right_inv hyt]
      exact this ▸ hV₀T _ (hΘs hz)
    · -- A point of `T` near `p u₀` is `p u = Θ (u, 0)` with `(u, 0)` in the source.
      intro hyT
      obtain ⟨u, hu, rfl⟩ := hWT ⟨hyW, hyT⟩
      rw [← hΘι hu, Θ.left_inv hu]
      exact fun i hi ↦ firstCoords_apply_of_le u hi
  · rw [OpenPartialHomeomorph.coe_restrOpen, ← hpu₀, Θ.left_inv hy₀, hπι]
  · filter_upwards [hV] with u hu
    rw [OpenPartialHomeomorph.coe_restrOpen_symm, OpenPartialHomeomorph.symm_symm]
    exact hΘι hu

end TauCeti
