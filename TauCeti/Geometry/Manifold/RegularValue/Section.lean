/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Local sections through regular points

Let `f : M → V` be a `C^n` map, `1 ≤ n`, from a boundaryless manifold to a finite-dimensional
real space, and let `x` be a regular point of `f`. Then `f` has a `C^n` local section through `x`:
a map `s`, `C^n` on an open neighbourhood `t` of `f x`, with `s (f x) = x` and `f (s y) = y` for
`y ∈ t` (`TauCeti.IsRegularPoint.exists_contMDiffOn_section`).

Such sections show that near a regular point the level sets of `f` are transverse to a smooth
family of points meeting each level once. For instance, a group action preserving `f` whose orbits
fill out the tangent spaces of the levels sweeps out a neighbourhood from the section.

## Main results

* `TauCeti.IsRegularPoint.exists_contMDiffOn_section`: a `C^n` map has a `C^n` local section
  through each of its regular points.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 4.26 (local section theorem).
-/

public section

open Function Set
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {n : WithTop ℕ∞} [IsManifold I n M] {f : M → V} {u : Set M} {x : M}

/-- **Local sections through regular points.** Let `f` be a map from a boundaryless manifold to a
finite-dimensional real space which is `C^n`, `1 ≤ n`, on an open set `u`, and let `x ∈ u` be a
regular point of `f`. Then there are an open neighbourhood `t` of `f x` and a map `s`, `C^n` on
`t`, such that `s (f x) = x` and `f (s y) = y` for every `y ∈ t`. -/
theorem IsRegularPoint.exists_contMDiffOn_section (hreg : IsRegularPoint I 𝓘(ℝ, V) f x)
    (hf : ContMDiffOn I 𝓘(ℝ, V) n f u) (hu : IsOpen u) (hx : x ∈ u) (hn : 1 ≤ n) :
    ∃ t : Set V, IsOpen t ∧ f x ∈ t ∧ ∃ s : V → M, s (f x) = x ∧
      ContMDiffOn 𝓘(ℝ, V) I n s t ∧ ∀ y ∈ t, f (s y) = y := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  have : IsManifold I 1 M := IsManifold.of_le hn
  set e := extChartAt I x with he
  -- A linear right inverse `A` of the surjective derivative `D = df_x`, read on the model spaces.
  set D : E →L[ℝ] V := mfderiv I 𝓘(ℝ, V) f x
  obtain ⟨A₀, hA₀⟩ := (D : E →ₗ[ℝ] V).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 (isRegularPoint_iff.1 hreg))
  set A : V →L[ℝ] E := LinearMap.toContinuousLinearMap A₀
  have hfA (w : V) : D (A w) = w := LinearMap.congr_fun hA₀ w
  -- The transversal `γ w = e⁻¹ (e x + A w)` through `x`, read in the chart at `x`.
  set γ : V → M := fun w ↦ e.symm (e x + A w) with hγ
  have hγ0 : γ 0 = x := by simp [hγ, he]
  set s₀ : Set V := (fun w ↦ e x + A w) ⁻¹' (e.target ∩ e.symm ⁻¹' u) with hs₀
  have hs₀open : IsOpen s₀ :=
    ((continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x)
      hu).preimage (continuous_const.add A.continuous)
  have hs₀0 : (0 : V) ∈ s₀ := by
    simp only [hs₀, mem_preimage, map_zero, add_zero, mem_inter_iff]
    exact ⟨mem_extChartAt_target x, by simpa [he] using hx⟩
  have haff : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) n fun w ↦ e x + A w :=
    (contDiff_const.add A.contDiff).contMDiff
  have hγs : ContMDiffOn 𝓘(ℝ, V) I n γ s₀ :=
    (contMDiffOn_extChartAt_symm x).comp haff.contMDiffOn fun w hw ↦ hw.1
  have hgs : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, V) n (f ∘ γ) s₀ := hf.comp hγs fun w hw ↦ hw.2
  -- The derivative of `f ∘ γ` at `0` is the identity: the chart inverse has derivative the
  -- identity at `e x`, and `df_x ∘ A = id`.
  have hdγ : HasMFDerivAt 𝓘(ℝ, V) I γ 0 ((ContinuousLinearMap.id ℝ E).comp A) := by
    have hsymm : mfderiv 𝓘(ℝ, E) I e.symm (e x) = ContinuousLinearMap.id ℝ E := by
      rw [← mfderivWithin_univ, ← I.range_eq_univ]
      exact mfderivWithin_range_extChartAt_symm
    have hsymmd : MDifferentiableAt 𝓘(ℝ, E) I e.symm (e x) := by
      have := mdifferentiableWithinAt_extChartAt_symm (I := I) (mem_extChartAt_target x)
      rwa [I.range_eq_univ, mdifferentiableWithinAt_univ] at this
    have haffd : HasMFDerivAt 𝓘(ℝ, V) 𝓘(ℝ, E) (fun w ↦ e x + A w) 0 A :=
      ((A.hasFDerivAt).const_add (e x)).hasMFDerivAt
    have hx0 : e x = e x + A 0 := by simp
    have h1 : HasMFDerivAt 𝓘(ℝ, E) I e.symm (e x + A 0) (ContinuousLinearMap.id ℝ E) := by
      rw [← hx0, ← hsymm]
      exact hsymmd.hasMFDerivAt
    exact h1.comp 0 haffd
  have hdg : mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) (f ∘ γ) 0 = ContinuousLinearMap.id ℝ V := by
    have hfd : MDifferentiableAt I 𝓘(ℝ, V) f x :=
      (hf.contMDiffAt (hu.mem_nhds hx)).mdifferentiableAt hn0
    ext w
    rw [mfderiv_comp_apply_of_eq 0 hfd
      ((hγs.contMDiffAt (hs₀open.mem_nhds hs₀0)).mdifferentiableAt hn0) hγ0, hdγ.mfderiv]
    exact hfA w
  -- So `f ∘ γ` is a local diffeomorphism at `0`, and `γ` composed with its local inverse is the
  -- required section.
  -- The tangent spaces of `V` are `V` itself only up to their `TangentSpace` instances, so the
  -- identity equivalence is matched with the identity derivative by `rfl`, not by `coe_refl`.
  have hL : IsLocalDiffeomorphAt 𝓘(ℝ, V) 𝓘(ℝ, V) n (f ∘ γ) 0 :=
    isLocalDiffeomorphAt_of_mfderiv_eq hgs hs₀open hs₀0 (BoundarylessManifold.isInteriorPoint) hn
      (e := ContinuousLinearEquiv.refl ℝ V) (by rw [hdg]; rfl)
  set h := hL.localInverse with hh
  have hfγ0 : (f ∘ γ) 0 = f x := by simp [hγ0]
  have hh0 : h (f x) = 0 := by
    rw [← hfγ0, hh, hL.localInverse_left_inv hL.localInverse_mem_target]
  refine ⟨h.source ∩ h ⁻¹' s₀,
    hL.contMDiffOn_localInverse.continuousOn.isOpen_inter_preimage h.open_source hs₀open,
    ⟨hfγ0 ▸ hL.localInverse_mem_source, by rw [mem_preimage, hh0]; exact hs₀0⟩,
    γ ∘ h, by rw [comp_apply, hh0, hγ0], ?_, fun y hy ↦ ?_⟩
  · exact hγs.comp (hL.contMDiffOn_localInverse.mono inter_subset_left) fun y hy ↦ hy.2
  · exact hL.localInverse_right_inv hy.1

end TauCeti
