/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.TangentRepresentation
public import TauCeti.Geometry.Symplectic.Invariants
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Invariant tangent vectors of a compact group of symplectomorphisms

Let a compact group `G`, itself a manifold, act on a Hausdorff manifold `M` by a smooth map
`G × M → M`, and let `σ` be a nondegenerate two-form on `M`. If the stabilizer of a point `x`
acts by maps `y ↦ g • y` preserving `σ`, its tangent representation on `T_x M`, `g ↦ d(g • ·)_x`,
acts by linear symplectic maps of `(T_x M, σ_x)`
(`TauCeti.SmoothTwoForm.IsNondegenerate.symplecticFormAt_tangentRepresentation`). It is a continuous
representation of a compact group, so its invariant vectors form a symplectic subspace of `T_x M`
(`TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectic_invariants_tangentRepresentation`), and the
stabilizer acts on the symplectic complement by the normal representation
`TauCeti.SymplecticForm.normalSubrepresentation`, which has no nonzero fixed vector.

At a point of the fixed locus `M^G` of `G` the stabilizer is all of `G`. Wherever `M^G` is a
submanifold whose tangent space is the space of invariant vectors, this shows that `σ` restricts
to a nondegenerate two-form on it; when `σ` is moreover closed, so is its restriction, and `M^G`
is a symplectic submanifold.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.symplecticFormAt_tangentRepresentation`: the stabilizer
  of `x` acts on `T_x M` by linear symplectic maps of `σ_x`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectic_invariants_tangentRepresentation`: the
  tangent vectors at `x` fixed by the stabilizer of `x` form a symplectic subspace.

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15.
* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513.
-/

public section

open MulAction
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H M F HG G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace HG] {IG : ModelWithCorners ℝ F HG}
  [TopologicalSpace G] [ChartedSpace HG G] [Group G] [MulAction G M] [ContMDiffSMul IG I ∞ G M]
  {σ : SmoothTwoForm I M} {x : M}

/-- If the stabilizer of `x` acts by maps preserving a nondegenerate two-form `σ`, its tangent
representation acts by linear symplectic maps of `σ_x`. -/
theorem IsNondegenerate.symplecticFormAt_tangentRepresentation (hσ : σ.IsNondegenerate)
    (hσG : ∀ g ∈ stabilizer G x, SmoothForm.mpullback (fun y : M ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) g) σ = σ)
    (hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I I (fun y : M ↦ g • y) x)
    (g : stabilizer G x) (u v : TangentSpace I x) :
    hσ.symplecticFormAt x (tangentRepresentation hd g u) (tangentRepresentation hd g v) =
      hσ.symplecticFormAt x u v := by
  have h := SmoothForm.eval₂_mpullback (fun y : M ↦ (g : G) • y)
    (ContMDiffSMul.contMDiff_const_smul (I := IG) (g : G)) σ x u v
  rw [hσG g g.2] at h
  have hgx : (g : G) • x = x := g.2
  rw [IsNondegenerate.symplecticFormAt_apply, IsNondegenerate.symplecticFormAt_apply, h,
    tangentRepresentation_apply, hgx]

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold IG 1 G] [IsTopologicalGroup G]
  [CompactSpace G]

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
    (hσ.symplecticFormAt_tangentRepresentation (IG := IG) hσG hd)

end TauCeti.SmoothTwoForm
