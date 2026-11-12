/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.IntegralManifold.LocalUniqueness
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Topology.Order.Interval

/-!
# Tangent curves in intrinsic integral manifolds

In a boundaryless real manifold with finite-dimensional model, a differentiable
curve tangent to a constant-rank involutive distribution lifts continuously through an injective
integral immersion from a boundaryless manifold through which it factors.
The integral carrier retains
its own topology. No second countability or agreement with the ambient subspace topology is
required. Working with relative derivatives on closed intervals includes their endpoints.

## Main results

* `TauCeti.IsIntegralManifold.continuousOn_factor_of_tangent_curve`: continuity of a tangent
  curve's factorization through an integral immersion.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 19, Theorem 19.21 and Lemma 19.22, pp.502–505, for intrinsic integral leaves and
  their local slice topology.
-/

public noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {D : ∀ x : M, Submodule ℝ (TangentSpace I x)}

private theorem eventually_sub_mem_of_curve {A B x : ℝ} (hAB : A < B) (hx : x ∈ Icc A B)
    {γ : ℝ → M} (hγ : MDifferentiableOn 𝓘(ℝ, ℝ) I γ (Icc A B))
    (htan : ∀ t ∈ Icc A B, curveVelocityWithin I γ (Icc A B) t ∈ D (γ t))
    (Φ : PartialEquiv M E) (hopen : IsOpen Φ.source)
    (hΦ : MDifferentiableOn I 𝓘(ℝ, E) Φ Φ.source)
    (W : Submodule ℝ E) [FiniteDimensional ℝ W]
    (hflat : ∀ z ∈ Φ.source, (D z).map (mfderiv I 𝓘(ℝ, E) Φ z).toLinearMap ≤ W)
    (hxΦ : γ x ∈ Φ.source) :
    ∀ᶠ y in 𝓝[Icc A B] x, Φ (γ y) - Φ (γ x) ∈ W := by
  have hU : γ ⁻¹' Φ.source ∈ 𝓝[Icc A B] x :=
    (hγ.continuousOn x hx).eventually (hopen.mem_nhds hxΦ)
  obtain ⟨a, b, hab, hxab, hsub, hΦsub, hnb⟩ :=
    TauCeti.exists_Icc_subset_mem_nhdsWithin_Icc hAB hx hU
  filter_upwards [hnb] with y hy
  exact sub_mem_of_tangent_curve hab hγ hsub hopen hΦ
    (fun t ht ↦ hΦsub ht) W W.closed_of_finiteDimensional hflat htan hxab hy

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {m : ℕ∞} [IsManifold J m N]
  [BoundarylessManifold J N] {f : N → M}

/-- In a boundaryless finite-dimensional real ambient manifold, a differentiable
curve tangent to a `C^m` constant-rank involutive distribution lifts continuously through an
injective integral immersion with boundaryless source. The closed interval includes endpoints.
No second countability or embeddedness is assumed for the integral carrier. -/
theorem IsIntegralManifold.continuousOn_factor_of_tangent_curve
    [FiniteDimensional ℝ E] {r : ℕ∞ω} [IsManifold I r M]
    [BoundarylessManifold I M]
    (hf : IsIntegralManifold J m D f) (hm : 1 ≤ m) (hinj : Injective f)
    (hmr : (m : ℕ∞ω) + 1 ≤ r)
    (hinv : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsInvolutiveDistribution I D) {k : ℕ}
    (hD : let _ : IsManifold I 1 M :=
      .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
      IsContMDiffDistribution I m k D)
    {A B : ℝ} (hAB : A < B) {γ : ℝ → M} {h : ℝ → N}
    (hγ : MDifferentiableOn 𝓘(ℝ, ℝ) I γ (Icc A B))
    (htan : ∀ t ∈ Icc A B, curveVelocityWithin I γ (Icc A B) t ∈ D (γ t))
    (hcomp : f ∘ h = γ) : ContinuousOn h (Icc A B) := by
  let _ : IsManifold I 1 M :=
    .of_le ((show (1 : ℕ∞ω) ≤ (m : ℕ∞ω) + 1 from le_add_self).trans hmr)
  let _ : IsManifold I (m : ℕ∞ω) M := .of_le (le_self_add.trans hmr)
  intro x hx
  have hpoint (y : ℝ) : f (h y) = γ y := congrFun hcomp y
  obtain ⟨Φ, W, hΦopen, hxΦ, _, hΦsmooth, hflatΦ, hΦinj⟩ :=
    hinv.exists_flatChart_extend (m := m) (n := r) hm hmr hD
      (BoundarylessManifold.isInteriorPoint (I := I) (x := γ x))
  have hm0 : (m : ℕ∞ω) ≠ 0 := by exact_mod_cast (ne_of_gt (zero_lt_one.trans_le hm))
  exact hf.continuousWithinAt_factor_of_flatChart (by exact_mod_cast hm) hinj
    Φ hΦopen hΦsmooth W hflatΦ (hγ.continuousOn x hx) hcomp
    BoundarylessManifold.isInteriorPoint hxΦ (hΦinj _ ((hpoint x).symm ▸ hxΦ))
    (eventually_sub_mem_of_curve hAB hx hγ htan Φ hΦopen
      (hΦsmooth.mdifferentiableOn hm0) W (fun z hz ↦ (hflatΦ z hz).le) hxΦ)

end TauCeti
