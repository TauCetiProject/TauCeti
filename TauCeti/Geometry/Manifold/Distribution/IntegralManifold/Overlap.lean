/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.IntegralManifold.Basic

import TauCeti.Geometry.Manifold.Distribution.IntegralManifold.LocalUniqueness

/-!
# Overlaps of integral parametrizations

Integral immersions of one involutive distribution have open overlaps in their own parameter
manifolds. More generally, the inverse image under one integral immersion of the image of an
open part of another integral immersion is open. This does not require either immersion to be
injective and does not assert openness in the ambient manifold.

A factorization between integral immersions through an injective target parametrization is a
local diffeomorphism. In particular, two injective integral parametrizations with the same image
are diffeomorphic over the ambient manifold, even when their images are not embedded. These
results supply the compatibility of the intrinsic charts used in the construction of leaves.
The ambient manifold is finite-dimensional and real, of class `C^r`; the sources are `C^m`,
where `1 ≤ m` and `m + 1 ≤ r`. The global overlap results concern boundaryless manifolds.

## Main results

* `TauCeti.IsIntegralManifold.isOpen_preimage_image`: overlap openness for open parameter sets.
* `TauCeti.IsIntegralManifold.isLocalDiffeomorphAt_of_comp_eq`: local smoothness and invertibility
  of a transition through an injective integral parametrization.
* `TauCeti.IsIntegralManifold.exists_diffeomorph_of_range_eq`: uniqueness of the intrinsic
  smooth structure on an injectively parametrized integral submanifold.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition (2013), Lemma 19.22,
  pp. 503–504 (open overlaps of integral submanifolds and compatibility of their charts).
* `TauCeti.IsIntegralManifold.exists_partialDiffeomorph`, for local integral uniqueness.
-/

public section

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ F' H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  {m : ℕ∞} {r : ℕ∞ω} [IsManifold I r M]
  [IsManifold J m N] [IsManifold K m P]
  {D : ∀ z : M, Submodule ℝ (TangentSpace I z)} {f : N → M} {g : P → M}

/-- A factorization of integral immersions through an injective target parametrization is a
local diffeomorphism at an interior point whose image and target parameter are interior.
No continuity of the factorizing map is assumed. -/
theorem IsIntegralManifold.isLocalDiffeomorphAt_of_comp_eq
    (hf : IsIntegralManifold J m D f) (hg : IsIntegralManifold K m D g)
    (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsInvolutiveDistribution I D) {k : ℕ}
    (hD : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsContMDiffDistribution I m k D)
    (hginj : Injective g) {h : N → P} (hcomp : ∀ z, g (h z) = f z) {x : N}
    (hx : J.IsInteriorPoint x) (hhx : K.IsInteriorPoint (h x))
    (hfx : I.IsInteriorPoint (f x)) : IsLocalDiffeomorphAt J K m h x := by
  obtain ⟨e, hxe, _, he⟩ := hf.exists_partialDiffeomorph hg hm hmr hinv hD
    hx hhx hfx (hcomp x).symm
  exact isLocalDiffeomorphAt_of_eqOn hxe fun z hz ↦
    hginj ((hcomp z).trans (he z hz))

variable [BoundarylessManifold I M] [BoundarylessManifold J N] [BoundarylessManifold K P]

/-- The inverse image under an integral immersion of the image of an open parameter set of
another integral immersion of the same involutive distribution is open. The immersions need
not be injective, and the open set is in the source topology, not the ambient topology. -/
theorem IsIntegralManifold.isOpen_preimage_image
    (hf : IsIntegralManifold J m D f) (hg : IsIntegralManifold K m D g)
    (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsInvolutiveDistribution I D) {k : ℕ}
    (hD : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsContMDiffDistribution I m k D)
    {U : Set P} (hU : IsOpen U) : IsOpen (f ⁻¹' (g '' U)) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨y, hy, hxy⟩
  obtain ⟨e, hxe, hex, he⟩ := hf.exists_partialDiffeomorph hg hm hmr hinv hD
    (BoundarylessManifold.isInteriorPoint (I := J))
    (BoundarylessManifold.isInteriorPoint (I := K))
    (BoundarylessManifold.isInteriorPoint (I := I)) hxy.symm
  have hcont : ContinuousAt e x :=
    (e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hxe)).continuousAt
  have hUe : e ⁻¹' U ∈ 𝓝 x := hcont.preimage_mem_nhds (hU.mem_nhds (hex ▸ hy))
  filter_upwards [e.open_source.mem_nhds hxe, hUe] with z hz hzU
  exact ⟨e z, hzU, (he z hz).symm⟩

/-- Injective integral parametrizations of one involutive distribution with the same image
have diffeomorphic intrinsic source manifolds, with the diffeomorphism intertwining their
ambient maps. No embeddedness, connectedness or second countability is assumed. -/
theorem IsIntegralManifold.exists_diffeomorph_of_range_eq
    (hf : IsIntegralManifold J m D f) (hg : IsIntegralManifold K m D g)
    (hm : 1 ≤ m) (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsInvolutiveDistribution I D) {k : ℕ}
    (hD : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsContMDiffDistribution I m k D)
    (hfinj : Injective f) (hginj : Injective g) (hrange : range f = range g) :
    ∃ e : Diffeomorph J K N P m, ∀ z, g (e z) = f z := by
  classical
  have hpre (x : N) : ∃ y, g y = f x := by
    have hx : f x ∈ range g := hrange ▸ mem_range_self x
    exact hx
  choose h hcomp using hpre
  have hlocal : IsLocalDiffeomorph J K m h := fun x ↦
    hf.isLocalDiffeomorphAt_of_comp_eq hg hm hmr hinv hD hginj hcomp
      (BoundarylessManifold.isInteriorPoint (I := J))
      (BoundarylessManifold.isInteriorPoint (I := K))
      (BoundarylessManifold.isInteriorPoint (I := I))
  have hbij : Bijective h := by
    constructor
    · intro x y hxy
      apply hfinj
      rw [← hcomp x, ← hcomp y, hxy]
    · intro y
      have hy : g y ∈ range f := hrange.symm ▸ mem_range_self y
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, hginj ((hcomp x).trans hx)⟩
  refine ⟨hlocal.diffeomorphOfBijective hbij, fun z ↦ ?_⟩
  simpa only [IsLocalDiffeomorph.coe_diffeomorphOfBijective] using hcomp z

end TauCeti
