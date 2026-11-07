/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import Mathlib.Analysis.LocallyConvex.HahnBanach
-- Supplies smooth subtraction on the normed target in the projected translated map.
import Mathlib.Geometry.Manifold.Algebra.LieGroup

-- Access the witness of the local-diffeomorphism predicate, as in LocalDiffeomorph.Basic.
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Local charts in affine subspaces

Around an interior source point, a smooth map whose image lies locally in a finite-dimensional
affine subspace, and whose differential identifies the source tangent space with the direction
subspace, gives a local chart into that direction. The chart sends the base point to zero and
identifies the original map with translation of the subtype inclusion. Its source can be chosen
inside the specified smoothness neighborhood. The regularity is at least one.

## Main results

* `ContMDiffOn.exists_plaque_chart`: a partial diffeomorphism into an affine direction
  subspace with the prescribed ambient map.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 19,
  Proposition 19.16 (Local Structure of Integral Manifolds), p. 500, for the real local-slice
  statement.
-/

public section

noncomputable section

open Set Filter Function
open scoped Topology Manifold ContDiff

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {W : Submodule 𝕜 E}

variable {H : Type*} [TopologicalSpace H] {J : ModelWithCorners 𝕜 F H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  {n : ℕ∞ω} [IsManifold J n N] {f : N → E} {x : N} {s : Set N}

/-- Around an interior source point, a `C^n` map, for `1 ≤ n`, locally contained in a
finite-dimensional affine subspace has a partial diffeomorphism into the direction subspace,
provided its differential at that point is injective with range equal to that direction.
The chart is centered at zero, lies inside the given smoothness neighborhood, and identifies
the original map with translation of the subtype inclusion. -/
theorem ContMDiffOn.exists_plaque_chart [FiniteDimensional 𝕜 W]
    (hf : ContMDiffOn J 𝓘(𝕜, E) n f s)
    (hs : IsOpen s) (hxs : x ∈ s) (hn : 1 ≤ n) (hx : J.IsInteriorPoint x)
    (hinj : Injective (mfderiv J 𝓘(𝕜, E) f x))
    (hrange : LinearMap.range (mfderiv J 𝓘(𝕜, E) f x).toLinearMap = W)
    (hplaque : ∀ᶠ y in 𝓝 x, f y - f x ∈ W) :
    ∃ e : PartialDiffeomorph J 𝓘(𝕜, W) N W n,
      x ∈ e.source ∧ e x = 0 ∧ e.source ⊆ s ∧
        ∀ y ∈ e.source, f y = f x + (e y : E) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  let df : F →L[𝕜] E := mfderiv J 𝓘(𝕜, E) f x
  let A₀ : F ≃ₗ[𝕜] W :=
    (LinearEquiv.ofInjective df.toLinearMap hinj).trans (LinearEquiv.ofEq _ _ hrange)
  let _ : FiniteDimensional 𝕜 F := FiniteDimensional.of_injective A₀.toLinearMap A₀.injective
  let _ : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  obtain ⟨p, hp⟩ := Submodule.ClosedComplemented.of_finiteDimensional W
  let A := A₀.toContinuousLinearEquiv
  have hA : (A : F →L[𝕜] W) = p.comp df := by
    -- Extensionality reduces the map and subtype equalities to their values in `E`.
    ext v
    exact (congrArg Subtype.val (hp ⟨df v, hrange ▸ ⟨v, rfl⟩⟩)).symm
  let g : N → W := fun y ↦ p (f y - f x)
  have hg : ContMDiffOn J 𝓘(𝕜, W) n g s :=
    p.contMDiff.comp_contMDiffOn (hf.sub contMDiffOn_const)
  have hfD : HasMFDerivAt J 𝓘(𝕜, E) f x df :=
    ((hf.contMDiffAt (hs.mem_nhds hxs)).mdifferentiableAt hn0).hasMFDerivAt
  have hc : HasMFDerivAt J 𝓘(𝕜, E) (fun _ : N ↦ f x) x (0 : F →L[𝕜] E) :=
    hasMFDerivAt_const (f x) x
  have hsub := hfD.sub hc
  -- Normalize the tangent-space model instances before simplifying the linear-map subtraction.
  change HasMFDerivAt J 𝓘(𝕜, E) (fun y ↦ f y - f x) x (df - (0 : F →L[𝕜] E)) at hsub
  rw [sub_zero] at hsub
  have hder : HasMFDerivAt J 𝓘(𝕜, W) g x (p.comp df) := p.hasMFDerivAt.comp x hsub
  have hAg : (A : F →L[𝕜] W) = mfderiv J 𝓘(𝕜, W) g x := hA.trans hder.mfderiv.symm
  obtain ⟨e, hxe, he⟩ :=
    TauCeti.isLocalDiffeomorphAt_of_mfderiv_eq hg hs hxs hx hn ⟨A, hAg⟩
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hplaque
  let e' := e.restrOpen (s ∩ U) (hs.inter hUopen)
  have hsource : e'.source = e.source ∩ (s ∩ U) := e.restrOpen_source (hs.inter hUopen)
  have hfun : (e' : N → W) = e := e.coe_restrOpen (hs.inter hUopen)
  have hmem (y : N) (hy : y ∈ e'.source) : y ∈ e.source ∧ y ∈ s ∧ y ∈ U := by
    simpa only [hsource, mem_inter_iff] using hy
  have hxe' : x ∈ e'.source := by
    rw [hsource]
    exact ⟨hxe, hxs, hxU⟩
  have he' (y : N) (hy : y ∈ e'.source) : e' y = g y :=
    (congrFun hfun y).trans (he (hmem y hy).1).symm
  refine ⟨e', hxe', ?_, fun y hy ↦ (hmem y hy).2.1, ?_⟩
  · rw [he' x hxe']
    simp only [g, sub_self, map_zero]
  · intro y hy
    have hpval := congrArg Subtype.val (hp ⟨f y - f x, hUsub (hmem y hy).2.2⟩)
    apply sub_eq_iff_eq_add'.mp
    rw [he' y hy]
    exact hpval.symm
