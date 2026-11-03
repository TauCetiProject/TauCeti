/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Radius
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Radial
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth disc neighbourhoods in Riemannian vector bundles

Every open neighbourhood of the zero section contains a closed disc bundle of positive smooth
radius, with the radius smaller than any prescribed positive continuous bound. Only a continuous
fibre metric is needed for this selection. If the metric is smooth, radial compression then
identifies the entire total space diffeomorphically with a smaller open neighbourhood of the zero
section, preserving base points and fixing zero vectors.

This permits tubular coordinates initially defined only near the zero section to be
parametrized by the whole normal bundle, including over noncompact submanifolds. The radius
selection uses Mathlib's `exists_contMDiffMap_forall_mem_convex_of_local_const`; compression
uses `TauCeti.vectorBundleRadialPartialDiffeomorphOfRadius`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3.
-/

public noncomputable section

open Bundle Filter Set Topology
open scoped Manifold ContDiff

variable {B F E H : Type*} [TopologicalSpace B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ChartedSpace H B] [IsManifold I ∞ B] [T2Space B] [SigmaCompactSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞}

namespace IsOpen

/-- An open neighbourhood of the zero section contains closed fibre discs of a positive
`C^n` radius smaller than any prescribed positive continuous bound. The fibre metric need
only be continuous, and the fibres need not be finite-dimensional. -/
theorem exists_contMDiffMap_norm_le_subset_bundle [IsContinuousRiemannianBundle F V]
    {U : Set (TotalSpace F V)} (hU : IsOpen U) (hzero : ∀ b, zeroSection F V b ∈ U)
    {ε : B → ℝ} (hε : Continuous ε) (hεpos : ∀ b, 0 < ε b) :
    ∃ r : C^n⟮I, B; 𝓘(ℝ), ℝ⟯, (∀ b, 0 < r b) ∧ (∀ b, r b < ε b) ∧
      ∀ b, ∀ v : V b, ‖v‖ ≤ r b → (⟨b, v⟩ : TotalSpace F V) ∈ U := by
  let T : B → Set ℝ := fun b => {r | 0 < r ∧ r < ε b ∧
    ∀ v : V b, ‖v‖ ≤ r → (⟨b, v⟩ : TotalSpace F V) ∈ U}
  have hconv : ∀ b, Convex ℝ (T b) := by
    intro b
    apply Set.OrdConnected.convex
    constructor
    rintro a ⟨ha, -⟩ c ⟨-, hcε, hc⟩ d ⟨had, hdc⟩
    exact ⟨ha.trans_le had, hdc.trans_lt hcε, fun v hv => hc v (hv.trans hdc)⟩
  have hlocal : ∀ b, ∃ c : ℝ, ∀ᶠ y in 𝓝 b, c ∈ T y := by
    intro b
    obtain ⟨δ, hδ, hdisc⟩ := hU.exists_pos_forall_norm_le_subset_bundle (hzero b)
    refine ⟨min δ (ε b / 2), ?_⟩
    filter_upwards [hdisc, hε.continuousAt.eventually
      (eventually_gt_nhds (half_lt_self (hεpos b)))] with y hy hyε
    exact ⟨lt_min hδ (half_pos (hεpos b)), (min_le_right _ _).trans_lt hyε,
      fun v hv => hy v (hv.trans (min_le_left _ _))⟩
  obtain ⟨r, hr⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const I (n := n) hconv hlocal
  exact ⟨r, fun b => (hr b).1, fun b => (hr b).2.1, fun b => (hr b).2.2⟩

end IsOpen

namespace TauCeti

/-- The whole total space of a smooth Riemannian vector bundle is diffeomorphic, over the
base and fixing the zero section, to an open neighbourhood inside any prescribed open
neighbourhood of the zero section. No compactness of the base or finite rank is required. -/
theorem exists_diffeomorph_subset_zeroSection [IsContMDiffRiemannianBundle I n F V]
    {U : Set (TotalSpace F V)} (hU : IsOpen U) (hzero : ∀ b, zeroSection F V b ∈ U) :
    ∃ W : TopologicalSpace.Opens (TotalSpace F V), (W : Set (TotalSpace F V)) ⊆ U ∧
      ∃ Φ : TotalSpace F V ≃ₘ^n⟮I.prod 𝓘(ℝ, F), I.prod 𝓘(ℝ, F)⟯ W,
        (∀ p, (Φ p).val.proj = p.proj) ∧
        ∀ b, (Φ (zeroSection F V b)).val = zeroSection F V b := by
  let : IsContinuousRiemannianBundle F V := by
    obtain ⟨g, hg, heq⟩ :=
      IsContMDiffRiemannianBundle.exists_contMDiff (IB := I) (n := n) (F := F) (E := V)
    exact ⟨g, hg.continuous, heq⟩
  obtain ⟨r, hr, -, hdisc⟩ := hU.exists_contMDiffMap_norm_le_subset_bundle
    (I := I) (n := n) hzero (continuous_const (y := (1 : ℝ))) (fun _ => zero_lt_one)
  let Ψ := vectorBundleRadialPartialDiffeomorphOfRadius (F := F) (V := V) r.contMDiff hr
  have hsource : Ψ.source = univ := vectorBundleRadialPartialDiffeomorphOfRadius_source _ _
  have htarget : Ψ.target = {p : TotalSpace F V | ‖p.2‖ < r p.proj} :=
    vectorBundleRadialPartialDiffeomorphOfRadius_target _ _
  have hforward : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) n Ψ := by
    rw [← contMDiffOn_univ, ← hsource]
    exact Ψ.contMDiffOn
  let W : TopologicalSpace.Opens (TotalSpace F V) := ⟨Ψ.target, Ψ.open_target⟩
  let Φ : TotalSpace F V ≃ₘ^n⟮I.prod 𝓘(ℝ, F), I.prod 𝓘(ℝ, F)⟯ W :=
    { toFun := fun p => ⟨Ψ p, Ψ.toPartialEquiv.map_source (hsource ▸ mem_univ p)⟩
      invFun := fun q => Ψ.toPartialEquiv.symm q
      left_inv := fun p => Ψ.toPartialEquiv.left_inv (hsource ▸ mem_univ p)
      right_inv := fun q => Subtype.ext (Ψ.toPartialEquiv.right_inv q.property)
      contMDiff_toFun := (TauCeti.ContMDiff.subtypeVal_comp_iff W _).mp hforward
      contMDiff_invFun := Ψ.contMDiffOn_invFun.comp_contMDiff contMDiff_subtype_val
        (fun q => q.property) }
  have hΦ (p : TotalSpace F V) : (Φ p).val = Ψ p := rfl
  refine ⟨W, ?_, Φ, ?_, ?_⟩
  · intro p hp
    have hp' : p ∈ Ψ.target := hp
    rw [htarget] at hp'
    exact hdisc p.proj p.2 hp'.le
  · intro p
    rw [hΦ]
    simp [Ψ]
  · intro b
    rw [hΦ]
    simp only [Ψ, vectorBundleRadialPartialDiffeomorphOfRadius_apply,
      TotalSpace.radialMap_zeroSection]
    simp [zeroSection]

end TauCeti
