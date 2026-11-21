/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.FixedPoints.Submanifold
public import TauCeti.Geometry.Symplectic.Manifold.Invariants
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Symplectic.Basic
public import TauCeti.Geometry.Symplectic.Restrict
public import TauCeti.Geometry.Symplectic.ExistsCompatible

/-!
# The fixed locus of a group of symplectic isometries

Let a group `K` act on a Riemannian manifold `M` by smooth isometries preserving a nondegenerate
two-form `σ`, for instance a symplectic form. No topology or Lie group structure on `K` is
required. At a point `p` of `M`, the tangent vectors fixed by the differentials of all elements
of the stabilizer of `p` (`TauCeti.fixedTangentSubspace I K p`), which at a point of the fixed set
`M^K` are the vectors fixed by all of `K`, are the invariant vectors of the tangent
representation, so they form a symplectic subspace of `(T_p M, σ_p)`
(`TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectic_fixedTangentSubspace`): the differentials are
orthogonal symplectic maps, so they commute with the polar complex structure of `σ_p`, which
therefore preserves their fixed vectors. In particular this subspace has even dimension
(`TauCeti.SmoothTwoForm.IsNondegenerate.even_finrank_fixedTangentSubspace`).

The fixed set is an embedded submanifold, possibly with components of different dimensions: the
points `M^K_d` of `M^K` at which the fixed tangent subspace has dimension `d`
(`TauCeti.fixedPointsOfFinrank I K M d`) form a smooth embedded submanifold whose tangent spaces are
the fixed tangent subspaces, and every connected subset of `M^K` lies in one of them
(`TauCeti.exists_isSmoothEmbedding_fixedPointsOfFinrank`,
`TauCeti.subset_fixedPointsOfFinrank_of_isPreconnected`). Since these tangent spaces are
symplectic, the inclusion of `M^K_d` is a symplectic submanifold embedding
(`IsNondegenerate.exists_isSymplecticSubmanifoldEmbedding_fixedPointsOfFinrank`):
`σ` restricts to a nondegenerate form on `M^K_d`, which is symplectic when `σ` is
(`IsNondegenerate.IsSymplecticSubmanifoldEmbedding.isSymplectic_mpullback`). Hence each
component of the fixed set of a group of symplectic isometries is an embedded symplectic
submanifold of even dimension.

Neither completeness of the metric nor compactness of `M` or `K` is used. A compact Lie group
acting smoothly preserves the metric obtained by averaging a smooth metric
(`TauCeti.exists_contMDiffRiemannianMetric_inner_mfderiv`), so the results apply to the fixed sets
of smooth symplectic actions of compact Lie groups, such as torus actions.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectic_fixedTangentSubspace`: the fixed tangent
  subspace at a fixed point is symplectic.
* `TauCeti.SmoothTwoForm.IsNondegenerate.even_finrank_fixedTangentSubspace`: it has even
  dimension.
* `IsNondegenerate.exists_isSymplecticSubmanifoldEmbedding_fixedPointsOfFinrank`:
  each `M^K_d` is an embedded symplectic submanifold with tangent spaces the fixed tangent
  subspaces.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Homework 21, exercise 2 (fixed points of a group of symplectic isometries).
* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15.
-/

public section

open Bundle Manifold MulAction
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm

section FixedTangentSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {K : Type*} [Group K] [MulAction K M] [ContMDiffConstSMul I ∞ K M]
  {σ : SmoothTwoForm I M}
  (hK : ∀ (k : K) (x : M) (u w : TangentSpace I x),
    inner ℝ (mfderiv I I (k • ·) x u) (mfderiv I I (k • ·) x w) = inner ℝ u w)
  (hσK : ∀ k : K, SmoothForm.mpullback (fun y : M ↦ k • y) (contMDiff_const_smul k) σ = σ)

include hK hσK

/-- **The fixed tangent subspace is symplectic.** For a group acting by isometries preserving a
nondegenerate two-form `σ`, the tangent vectors at `p` fixed by the differentials of all elements
of the stabilizer of `p` form a symplectic subspace of `(T_p M, σ_p)`. At a point of the fixed
set these are the tangent vectors fixed by the differentials of all group elements. -/
theorem IsNondegenerate.isSymplectic_fixedTangentSubspace (hσ : σ.IsNondegenerate) (p : M) :
    (hσ.symplecticFormAt p).IsSymplectic (fixedTangentSubspace I K p) := by
  have hd (g : K) (_ : g ∈ stabilizer K p) :
      MDifferentiableAt I I (fun y : M ↦ g • y) p :=
    (contMDiff_const_smul (I := I) (n := ∞) g).mdifferentiableAt (by simp)
  have h := hσ.isSymplectic_invariants_tangentRepresentation_of_inner
    (fun g _ u w ↦ hK g p u w) (fun g _ ↦ hσK g) hd
  rwa [invariants_tangentRepresentation_eq_fixedTangentSubspace hd] at h

/-- **The fixed tangent subspace has even dimension.** For a group acting by isometries preserving
a nondegenerate two-form, the tangent vectors at `p` fixed by the differentials of all elements of
the stabilizer of `p` form a space of even dimension. -/
theorem IsNondegenerate.even_finrank_fixedTangentSubspace (hσ : σ.IsNondegenerate) (p : M) :
    Even (Module.finrank ℝ (fixedTangentSubspace I K p)) :=
  ((hσ.symplecticFormAt p).restrict _
    (hσ.isSymplectic_fixedTangentSubspace hK hσK p).nondegenerate_restrict).even_finrank

end FixedTangentSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  {K : Type*} [Group K] [MulAction K M] [ContMDiffConstSMul 𝓘(ℝ, E) ∞ K M]
  {σ : SmoothTwoForm 𝓘(ℝ, E) M}
  (hK : ∀ (k : K) (x : M) (u w : TangentSpace 𝓘(ℝ, E) x),
    inner ℝ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (k • ·) x u) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (k • ·) x w) =
      inner ℝ u w)
  (hσK : ∀ k : K, SmoothForm.mpullback (fun y : M ↦ k • y) (contMDiff_const_smul k) σ = σ)

include hK hσK

/-- **The fixed locus of a group of symplectic isometries is a symplectic submanifold.** For a
group acting by isometries preserving a nondegenerate two-form `σ` and a subspace `L` of the model
of dimension `d`, the points of the fixed set at which the fixed tangent subspace has dimension `d`
form a smooth manifold modelled on `L` whose inclusion into `M` is a symplectic submanifold
embedding, with tangent image the fixed tangent subspace at every point. -/
theorem IsNondegenerate.exists_isSymplecticSubmanifoldEmbedding_fixedPointsOfFinrank
    (hσ : σ.IsNondegenerate) {d : ℕ} {L : Submodule ℝ E} (hL : Module.finrank ℝ L = d) :
    ∃ C : ChartedSpace L (fixedPointsOfFinrank 𝓘(ℝ, E) K M d), letI := C
      IsManifold 𝓘(ℝ, L) ∞ (fixedPointsOfFinrank 𝓘(ℝ, E) K M d) ∧
      hσ.IsSymplecticSubmanifoldEmbedding 𝓘(ℝ, L)
        (Subtype.val : fixedPointsOfFinrank 𝓘(ℝ, E) K M d → M) ∧
      ∀ y : fixedPointsOfFinrank 𝓘(ℝ, E) K M d,
        LinearMap.range (mfderiv 𝓘(ℝ, L) 𝓘(ℝ, E) Subtype.val y).toLinearMap =
          fixedTangentSubspace 𝓘(ℝ, E) K (y : M) := by
  obtain ⟨C, hman, hemb, hrange⟩ := exists_isSmoothEmbedding_fixedPointsOfFinrank hK hL
  let := C
  refine ⟨C, hman, (isSymplecticSubmanifoldEmbedding_iff_of_isSmoothEmbedding hemb).2
    (hasSymplecticTangentImages_iff_forall.2 fun y ↦ ?_), hrange⟩
  rw [hrange y]
  exact hσ.isSymplectic_fixedTangentSubspace hK hσK _

end TauCeti.SmoothTwoForm
