/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution
public import TauCeti.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Submodule
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import Mathlib.Analysis.LocallyConvex.HahnBanach

/-!
# Integral manifolds of a distribution

An integral manifold of a tangent distribution `D` is a `C^n` immersion of a nonempty charted space
whose differential has image exactly `D` at every point.  The source has its own topology and
charted-space structure: it is not given the subspace topology from the ambient manifold, and the
immersion need not be injective.  This is the notion needed by the Frobenius theorem and by the
construction of immersed Lie subgroups.

This file provides both the unbundled predicate `TauCeti.IsIntegralManifold` for a specified
immersion and `TauCeti.IntegralManifold`, which packages a `k`-dimensional source manifold and its
parametrization.  The rank theorem shows that, for regularity `n ≠ 0`, the dimension of any
finite-dimensional source equals the rank of the distribution at any image point; it is not extra
data hidden in the definition. For regularity at least one, integral immersions of a
finite-dimensional constant distribution have partial-diffeomorphism charts into its direction
subspace near interior source points. These charts give local changes of parameter between
interior source points with the same ambient image, intertwining the two integral immersions.

## Main definitions

* `TauCeti.IsIntegralManifold`: an immersion of a nonempty charted space whose tangent image equals
  the given distribution.
* `TauCeti.IntegralManifold`: a packaged integral manifold with Euclidean model of dimension `k`.

## Main results

* `TauCeti.IsIntegralManifold.finrank_model_eq`: for regularity `n ≠ 0`, the source model
  dimension equals the rank of the distribution at any image point.
* `TauCeti.isIntegralManifold_id`: the identity is an integral manifold of the full tangent
  distribution.
* `TauCeti.IsIntegralManifold.eventually_sub_mem`: an integral immersion, of regularity at least
  one, of a finite-dimensional constant distribution locally stays in one affine plaque, including
  at boundary source points.
* `TauCeti.IsIntegralManifold.exists_plaque_chart`: a local chart in an affine plaque with the
  prescribed ambient inclusion.
* `TauCeti.IsIntegralManifold.exists_plaque_transition`: a local change of integral parameters
  intertwining their ambient maps.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 19,
  Proposition 19.16 (Local Structure of Integral Manifolds), p. 500.
-/

public section

noncomputable section

open Function
open scoped Manifold ContDiff Topology

universe u v

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} {k : ℕ}

section Unbundled

/-- A map is an **integral manifold** of `D` when its source is a nonempty charted space, it is a
`C^n` immersion, and the image of its differential at every point is exactly the prescribed tangent
subspace.

Nonemptiness rules out the empty map, which would otherwise satisfy the remaining conditions
vacuously for every distribution.

The source topology and charted-space structure are independent of the ambient topology.  In
particular, this predicate neither requires the map to be injective nor equips its range with the
subspace topology. -/
def IsIntegralManifold {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
    (n : ℕ∞ω) {N : Type v} [TopologicalSpace N] [ChartedSpace H' N]
    (D : ∀ x : M, Submodule ℝ (TangentSpace I x)) (f : N → M) : Prop :=
  Nonempty N ∧ Manifold.IsImmersion J I n f ∧
    ∀ y, LinearMap.range (mfderiv J I f y).toLinearMap = D (f y)

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type v} [TopologicalSpace N] [ChartedSpace H' N]
  {D : ∀ x : M, Submodule ℝ (TangentSpace I x)} {f : N → M}

/-- Characterization of an integral manifold as an immersion of a nonempty charted space with the
prescribed differential range. -/
theorem isIntegralManifold_iff : IsIntegralManifold J n D f ↔
    Nonempty N ∧ Manifold.IsImmersion J I n f ∧
      ∀ y, LinearMap.range (mfderiv J I f y).toLinearMap = D (f y) :=
  Iff.rfl

/-- The source of an integral manifold is nonempty. -/
theorem IsIntegralManifold.nonempty (hf : IsIntegralManifold J n D f) : Nonempty N :=
  hf.1

/-- The parametrization of an integral manifold is an immersion. -/
theorem IsIntegralManifold.isImmersion (hf : IsIntegralManifold J n D f) :
    Manifold.IsImmersion J I n f :=
  hf.2.1

/-- The tangent image of an integral manifold is the prescribed distribution fiber. -/
theorem IsIntegralManifold.range_mfderiv (hf : IsIntegralManifold J n D f) (y : N) :
    LinearMap.range (mfderiv J I f y).toLinearMap = D (f y) :=
  hf.2.2 y

/-- The parametrization of an integral manifold is of class `C^n`. -/
theorem IsIntegralManifold.contMDiff (hf : IsIntegralManifold J n D f) :
    ContMDiff J I n f :=
  hf.isImmersion.contMDiff

/-- For regularity `n ≠ 0`, the model dimension of an integral manifold `f` equals the rank of
the distribution at the image point `f y` of any source point `y`. -/
theorem IsIntegralManifold.finrank_model_eq
    (hf : IsIntegralManifold J n D f) (hn : n ≠ 0) (y : N)
    (hD : Module.finrank ℝ (D (f y)) = k) : Module.finrank ℝ E' = k := by
  -- Integrality identifies the fiber of `D` with the range of the injective differential.
  rw [← hD, ← hf.range_mfderiv y,
    LinearMap.finrank_range_of_inj (hf.isImmersion.mfderiv_injective hn y)]
  exact finrank_tangentSpace (I := J) y

/-- The identity map of a nonempty manifold is an integral manifold of the full tangent
distribution. -/
theorem isIntegralManifold_id [IsManifold I n M] [Nonempty M] :
    IsIntegralManifold I n (fun x : M ↦ (⊤ : Submodule ℝ (TangentSpace I x))) id := by
  refine ⟨inferInstance, Manifold.IsImmersion.id, fun x ↦ ?_⟩
  rw [mfderiv_id]
  exact LinearMap.range_id

end Unbundled

section Bundled

/-- A packaged `k`-dimensional integral manifold of `D`.

Its carrier is nonempty and has an independent `C^n` manifold structure modelled on `ℝ^k`; the
map into the ambient manifold is only required to be an immersion.  Injectivity,
embeddedness, connectedness, and maximality are deliberately separate properties. -/
structure IntegralManifold (n : ℕ∞ω)
    (D : ∀ x : M, Submodule ℝ (TangentSpace I x)) (k : ℕ) where
  /-- The carrier of the integral manifold. -/
  carrier : Type v
  /-- The topology of the carrier, which need not be the subspace topology from `M`. -/
  [topologicalSpace : TopologicalSpace carrier]
  /-- The carrier is charted by the `k`-dimensional Euclidean model. -/
  [chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin k)) carrier]
  /-- The carrier is a manifold of regularity `n`. -/
  [isManifold : IsManifold (𝓡 k) n carrier]
  /-- The carrier is nonempty, so a packaged integral manifold is never vacuous. -/
  [nonempty : Nonempty carrier]
  /-- The parametrizing immersion into the ambient manifold. -/
  map : carrier → M
  /-- The parametrization is a `C^n` immersion. -/
  isImmersion : Manifold.IsImmersion (𝓡 k) I n map
  /-- The image of the differential is exactly the distribution fiber. -/
  range_mfderiv : ∀ y,
    LinearMap.range (mfderiv (𝓡 k) I map y).toLinearMap = D (map y)

attribute [instance] IntegralManifold.topologicalSpace IntegralManifold.chartedSpace
  IntegralManifold.isManifold IntegralManifold.nonempty
attribute [simp] IntegralManifold.range_mfderiv

namespace IntegralManifold

variable {D : ∀ x : M, Submodule ℝ (TangentSpace I x)}

/-- The map of a packaged integral manifold satisfies the unbundled integral-manifold
predicate. -/
theorem isIntegralManifold (N : IntegralManifold (I := I) n D k) :
    IsIntegralManifold (𝓡 k) n D N.map :=
  ⟨N.nonempty, N.isImmersion, N.range_mfderiv⟩

/-- The map of a packaged integral manifold is of class `C^n`. -/
theorem contMDiff_map (N : IntegralManifold (I := I) n D k) :
    ContMDiff (𝓡 k) I n N.map :=
  N.isImmersion.contMDiff

end IntegralManifold

end Bundled

section AffinePlaques

open Set Filter

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J n N]
  {W : Submodule ℝ E} [FiniteDimensional ℝ W] {f : N → E} {x : N} {s : Set N}

/-- An integral immersion, of regularity at least one, of a finite-dimensional constant
distribution locally stays in one affine plaque. -/
theorem IsIntegralManifold.eventually_sub_mem
    (hf : IsIntegralManifold (I := 𝓘(ℝ, E)) J n (fun _ : E ↦ W) f)
    (hn : 1 ≤ n) : ∀ᶠ z in 𝓝 x, f z - f x ∈ W := by
  let _ : IsManifold J 1 N := .of_le hn
  obtain ⟨p, hp⟩ := Submodule.ClosedComplemented.of_finiteDimensional W
  let q : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - W.subtypeL.comp p
  have hq (v : E) : q v = v - (p v : E) := by simp [q]
  have hqzero (v : E) (hv : v ∈ W) : q v = 0 := by
    rw [hq]
    exact sub_eq_zero.mpr (congrArg Subtype.val (hp ⟨v, hv⟩)).symm
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hfD := hf.contMDiff.mdifferentiable hn0
  have hqD : MDifferentiable J 𝓘(ℝ, E) (fun z ↦ q (f z)) :=
    q.mdifferentiable.comp hfD
  have hzero (z : N) : mfderiv J 𝓘(ℝ, E) (fun z ↦ q (f z)) z = 0 := by
    have hd : HasMFDerivAt J 𝓘(ℝ, E) (fun z ↦ q (f z)) z
        (q.comp (mfderiv J 𝓘(ℝ, E) f z)) :=
      q.hasMFDerivAt.comp z (hfD z).hasMFDerivAt
    rw [hd.mfderiv]
    ext v
    apply hqzero
    rw [← hf.range_mfderiv z]
    exact ⟨v, rfl⟩
  have hconst := hqD.mdifferentiableOn.eventuallyEq_const_of_mfderiv_eq_zero
    isOpen_univ (fun z _ ↦ hzero z) (mem_univ x)
  filter_upwards [hconst] with z hz
  have hsub : q (f z - f x) = 0 := by rw [map_sub, hz, sub_self]
  rw [hq] at hsub
  rw [sub_eq_zero.mp hsub]
  exact (p (f z - f x)).property

/-- An integral immersion of a finite-dimensional constant distribution has a partial-diffeomorphism
chart into its direction subspace at every interior source point. The chart sends the point to zero
and identifies the immersion with translation of the subtype inclusion. Its source lies inside
the specified open neighborhood. -/
theorem IsIntegralManifold.exists_plaque_chart
    (hf : IsIntegralManifold (I := 𝓘(ℝ, E)) J n (fun _ : E ↦ W) f)
    (hn : 1 ≤ n) (hx : J.IsInteriorPoint x) (hs : IsOpen s) (hxs : x ∈ s) :
    ∃ e : PartialDiffeomorph J 𝓘(ℝ, W) N W n,
      x ∈ e.source ∧ e x = 0 ∧ e.source ⊆ s ∧
        ∀ y ∈ e.source, f y = f x + (e y : E) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  exact ContMDiffOn.exists_plaque_chart hf.contMDiff.contMDiffOn hs hxs hn hx
    (hf.isImmersion.mfderiv_injective hn0 x) (hf.range_mfderiv x)
    (hf.eventually_sub_mem hn)

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ F' H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K n P]
  {g : P → E} {y : P}

/-- Two integral immersions of the same finite-dimensional constant distribution, through the same
ambient point, are related near interior source points by a partial diffeomorphism intertwining
their ambient maps. -/
theorem IsIntegralManifold.exists_plaque_transition
    (hf : IsIntegralManifold (I := 𝓘(ℝ, E)) J n (fun _ : E ↦ W) f)
    (hg : IsIntegralManifold (I := 𝓘(ℝ, E)) K n (fun _ : E ↦ W) g)
    (hn : 1 ≤ n) (hx : J.IsInteriorPoint x) (hy : K.IsInteriorPoint y)
    (hfg : f x = g y) :
    ∃ e : PartialDiffeomorph J K N P n,
      x ∈ e.source ∧ e x = y ∧ ∀ z ∈ e.source, f z = g (e z) := by
  obtain ⟨c, hxc, hc0, _, hfc⟩ := hf.exists_plaque_chart hn hx isOpen_univ (mem_univ x)
  obtain ⟨d, hyd, hd0, _, hgd⟩ := hg.exists_plaque_chart hn hy isOpen_univ (mem_univ y)
  obtain ⟨e, hxe, hex, hec, hed, he⟩ :=
    c.exists_transition d hxc hyd (hc0.trans hd0.symm)
  refine ⟨e, hxe, hex, ?_⟩
  intro z hz
  rw [hfc z (hec hz), hgd (e z) (hed hz), hfg, he z hz]

end AffinePlaques

end TauCeti
