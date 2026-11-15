/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.TangentRepresentation
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action
public import TauCeti.Geometry.Symplectic.Invariants
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Invariant tangent vectors of groups of symplectomorphisms

Let a group `G` act on a manifold `M` by smooth maps, and let `σ` be a nondegenerate two-form on
`M`. If the stabilizer of a point `x` acts by maps `y ↦ g • y` preserving `σ`, its tangent
representation on `T_x M`, `g ↦ d(g • ·)_x`, acts by linear symplectic maps of `(T_x M, σ_x)`
(`TauCeti.SmoothTwoForm.IsNondegenerate.symplecticFormAt_tangentRepresentation`). Its invariant
vectors form a symplectic subspace of `T_x M` in two situations:

* The differentials at `x` of the stabilizer preserve a Riemannian metric on `M`, for instance
  because `G` acts by isometries. No topology on `G` is needed: the tangent representation is then
  orthogonal (`TauCeti.inner_tangentRepresentation_apply`), so it commutes with the polar
  normalization of `σ_x`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectic_invariants_tangentRepresentation_of_inner`).
* `G` is a compact group, itself a manifold, acting by a smooth map `G × M → M` on a Hausdorff
  manifold. The tangent representation is then a continuous representation of a compact group
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectic_invariants_tangentRepresentation`).

In both cases the stabilizer acts on the symplectic complement by the normal representation
`TauCeti.SymplecticForm.normalSubrepresentation`, which has no nonzero fixed vector.

At a point of the fixed locus `M^G` of `G` the stabilizer is all of `G`, and its invariant vectors
are the tangent vectors fixed by the differential of every element
(`TauCeti.mem_invariants_tangentRepresentation_iff_of_mem_fixedPoints`). For a group of
isometries, `M^G` is near each of its points the image of this subspace under the Riemannian
exponential map, and the Riemannian logarithm is a smooth slice chart flattening `M^G` onto it
(`TauCeti.Manifold.IsNormalDomain.isSliceChart_fixedPoints`,
`TauCeti.exists_isSliceChart_fixedPoints`), and the results here show that this subspace is
symplectic for `σ_x`; its dimension may vary from one fixed point to another. Wherever `M^G` is a
submanifold whose tangent space is the space of invariant vectors, this shows that `σ` restricts
to a nondegenerate two-form on it; when `σ` is moreover closed, so is its restriction, and `M^G`
is a symplectic submanifold.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.symplecticFormAt_tangentRepresentation`: the stabilizer
  of `x` acts on `T_x M` by linear symplectic maps of `σ_x`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectic_invariants_tangentRepresentation_of_inner`:
  when the stabilizer of `x` acts by differentials at `x` preserving a Riemannian metric, for
  instance for a group of isometries, its invariant tangent vectors form a symplectic subspace.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectic_invariants_tangentRepresentation`: the same
  for a compact group acting smoothly.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Homework 21, exercise 2 (fixed points of a group of symplectic isometries).
* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15.
* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513.
-/

public section

open Bundle MulAction
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {G : Type*} [Group G] [MulAction G M] {σ : SmoothTwoForm I M} {x : M}

section ConstSMul

variable [ContMDiffConstSMul I ∞ G M]

/-- If the stabilizer of `x` acts by maps preserving a nondegenerate two-form `σ`, its tangent
representation acts by linear symplectic maps of `σ_x`. -/
theorem IsNondegenerate.symplecticFormAt_tangentRepresentation (hσ : σ.IsNondegenerate)
    (hσG : ∀ g ∈ stabilizer G x, SmoothForm.mpullback (fun y : M ↦ g • y)
      (contMDiff_const_smul g) σ = σ)
    (hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I I (fun y : M ↦ g • y) x)
    (g : stabilizer G x) (u v : TangentSpace I x) :
    hσ.symplecticFormAt x (tangentRepresentation hd g u) (tangentRepresentation hd g v) =
      hσ.symplecticFormAt x u v := by
  have h := SmoothForm.eval₂_mpullback (fun y : M ↦ (g : G) • y)
    (contMDiff_const_smul (g : G)) σ x u v
  rw [hσG g g.2] at h
  have hgx : (g : G) • x = x := g.2
  rw [IsNondegenerate.symplecticFormAt_apply, IsNondegenerate.symplecticFormAt_apply, h,
    tangentRepresentation_apply, hgx]

variable [FiniteDimensional ℝ E] [RiemannianBundle (fun y : M ↦ TangentSpace I y)]

/-- **Invariant tangent vectors of a group of symplectic isometries form a symplectic subspace.**
Let a group act on a Riemannian manifold `M` by smooth maps, and let the stabilizer of `x` act by
maps preserving a nondegenerate two-form `σ` whose differentials at `x` preserve the metric, for
instance because the group acts by isometries. Then the tangent vectors at `x` fixed by the
stabilizer form a symplectic subspace of `(T_x M, σ_x)`. No topology on the group is needed. -/
theorem IsNondegenerate.isSymplectic_invariants_tangentRepresentation_of_inner
    (hσ : σ.IsNondegenerate)
    (hK : ∀ g ∈ stabilizer G x, ∀ u w : TangentSpace I x,
      inner ℝ (mfderiv I I (g • ·) x u) (mfderiv I I (g • ·) x w) = inner ℝ u w)
    (hσG : ∀ g ∈ stabilizer G x, SmoothForm.mpullback (fun y : M ↦ g • y)
      (contMDiff_const_smul g) σ = σ)
    (hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I I (fun y : M ↦ g • y) x) :
    (hσ.symplecticFormAt x).IsSymplectic
      (tangentRepresentation hd).toRepresentation.invariants :=
  SymplecticForm.isSymplectic_invariants_of_inner
    (fun g u w ↦ (inner_tangentRepresentation_apply hd g u w).trans (hK g g.2 u w))
    (hσ.symplecticFormAt_tangentRepresentation hσG hd)

end ConstSMul

variable {F HG : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ F HG} [TopologicalSpace G] [ChartedSpace HG G]
  [ContMDiffSMul IG I ∞ G M] [FiniteDimensional ℝ E] [T2Space M] [IsManifold IG 1 G]
  [IsTopologicalGroup G] [CompactSpace G]

include IG in
/-- **Invariant tangent vectors of a compact symplectic action form a symplectic subspace.** Let
a compact group `G` act smoothly on a Hausdorff manifold `M`, and let the stabilizer of `x` act by
maps preserving a nondegenerate two-form `σ`. Then the tangent vectors at `x` fixed by the
stabilizer form a symplectic subspace of `(T_x M, σ_x)`. -/
theorem IsNondegenerate.isSymplectic_invariants_tangentRepresentation (hσ : σ.IsNondegenerate)
    (hσG : ∀ g ∈ stabilizer G x, SmoothForm.mpullback (fun y : M ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) g) σ = σ)
    (hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I I (fun y : M ↦ g • y) x) :
    (hσ.symplecticFormAt x).IsSymplectic
      (tangentRepresentation hd).toRepresentation.invariants := by
  have : ContMDiffConstSMul I ∞ G M := ⟨ContMDiffSMul.contMDiff_const_smul (I := IG)⟩
  -- The stabilizer is closed in the compact group `G`, hence compact.
  have hcont : Continuous fun g : G ↦ g • x :=
    (ContMDiffSMul.contMDiff_smul (I := IG) (I' := I) (n := ∞) (G := G) (M := M)).continuous.comp
      (continuous_id.prodMk continuous_const)
  have : CompactSpace (stabilizer G x) :=
    isCompact_iff_compactSpace.1 (isClosed_singleton.preimage hcont).isCompact
  -- Tangent spaces carry no norm instance; transport the norm of the model space `E`, whose
  -- topology is the topology of `TangentSpace I x`.
  let : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs (NormedAddCommGroup E)
  let : NormedSpace ℝ (TangentSpace I x) := inferInstanceAs (NormedSpace ℝ E)
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  exact SymplecticForm.isSymplectic_invariants (continuous_tangentRepresentation IG hd)
    (hσ.symplecticFormAt_tangentRepresentation hσG hd)

end TauCeti.SmoothTwoForm
