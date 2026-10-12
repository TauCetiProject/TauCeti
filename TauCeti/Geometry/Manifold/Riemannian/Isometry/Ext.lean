/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal
import Mathlib.Topology.Connected.Clopen
import TauCeti.Topology.FiberBundle.Separation

/-!
# Isometries are determined by their first-order data

Two Riemannian isometries agreeing in value and differential at a point agree on a
neighbourhood of that point. On a connected source they agree everywhere. Neither
completeness nor compactness is needed.

This uniqueness theorem allows an isometry of a homogeneous space to be identified with
a candidate constructed from its value and linear action on one tangent space. In
particular it is the uniqueness input to identifying the full isometry groups of the
round sphere and the other homogeneous Riemannian models.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Proposition 5.22
  (an isometry is determined by its value and differential at one point).
-/

public section

noncomputable section

open Bundle Filter Manifold Set Topology
open scoped ContDiff Manifold

namespace TauCeti.RiemannianIsometry

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [FiniteDimensional ℝ F] [J.Boundaryless] [T2Space N]
  [RiemannianBundle (fun y : N => TangentSpace J y)] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N => TangentSpace J y)]

/-- Isometries with the same value and differential at a point agree near that point. -/
theorem eventuallyEq_of_mfderiv_eq (Φ Ψ : RiemannianIsometry I J M N) {p : M}
    (hp : Φ p = Ψ p) (hd : mfderiv I J Φ p = mfderiv I J Ψ p) :
    (Φ : M → N) =ᶠ[𝓝 p] Ψ := by
  obtain ⟨r, -, hr⟩ := exists_isNormalDomain_ball (I := I) (M := M) p
  filter_upwards [hr.image_mem_nhds] with q hq
  obtain ⟨v, -, rfl⟩ := hq
  rw [← Φ.riemannianExp_mfderiv, ← Ψ.riemannianExp_mfderiv, hp, hd]

/-- Riemannian isometries of a connected manifold are determined by their value and
differential at a single point. -/
theorem ext_of_mfderiv_eq [PreconnectedSpace M] (Φ Ψ : RiemannianIsometry I J M N)
    {p : M} (hp : Φ p = Ψ p) (hd : mfderiv I J Φ p = mfderiv I J Ψ p) : Φ = Ψ := by
  classical
  let S : Set M := {x | ∀ v : TangentSpace I x,
    tangentMap I J Φ ⟨x, v⟩ = tangentMap I J Ψ ⟨x, v⟩}
  have hdata : ∀ x ∈ S, Φ x = Ψ x ∧ mfderiv I J Φ x = mfderiv I J Ψ x := by
    intro x hx
    refine ⟨congrArg TotalSpace.proj (hx 0), ?_⟩
    ext v
    exact congrArg (fun z : TangentBundle J N => (z.2 : F)) (hx v)
  have hmem : ∀ x, Φ x = Ψ x → mfderiv I J Φ x = mfderiv I J Ψ x → x ∈ S := by
    intro x hx hd v
    exact TotalSpace.ext hx (heq_of_eq (DFunLike.congr_fun hd v))
  have hclosed : IsClosed S := by
    have hcompl : Sᶜ = Bundle.TotalSpace.proj ''
        {z : TangentBundle I M | tangentMap I J Φ z ≠ tangentMap I J Ψ z} := by
      ext x
      simp only [S, mem_compl_iff, mem_ofPred_eq, not_forall, mem_image]
      constructor
      · rintro ⟨v, hv⟩
        exact ⟨⟨x, v⟩, hv, rfl⟩
      · rintro ⟨⟨y, v⟩, hv, rfl⟩
        exact ⟨v, hv⟩
    rw [← isOpen_compl_iff, hcompl]
    exact FiberBundle.isOpenMap_proj E (TangentSpace I)
      _ (isClosed_eq (Φ.toDiffeomorph.contMDiff.continuous_tangentMap (by simp))
        (Ψ.toDiffeomorph.contMDiff.continuous_tangentMap (by simp))).isOpen_compl
  have hopen : IsOpen S := by
    refine isOpen_iff_mem_nhds.2 fun x hx => ?_
    obtain ⟨hxv, hxd⟩ := hdata x hx
    have heq := Φ.eventuallyEq_of_mfderiv_eq Ψ hxv hxd
    filter_upwards [eventually_eventually_nhds.2 heq] with y hy
    have hlocal : (Φ : M → N) =ᶠ[𝓝 y] Ψ := hy
    apply hmem y hlocal.eq_of_nhds
    -- Mathlib's congruence theorem inserts `tangentSpaceCast`, whose underlying
    -- function is the identity. Here the endpoints agree by `hlocal.eq_of_nhds`.
    ext v
    exact DFunLike.congr_fun (hlocal.mfderiv_eq (I := I) (I' := J)) v
  have hS : S = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨p, hmem p hp hd⟩
  exact ext fun x => (hdata x (hS.symm ▸ mem_univ x)).1

end TauCeti.RiemannianIsometry
