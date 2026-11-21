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
import TauCeti.Geometry.Symplectic.Lagrangian.Constructions

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

These data are natural. Let `ψ : M → M₂` be a diffeomorphism pulling a nondegenerate two-form
`τ` back to `σ` and commuting near `p` with the action of every element of `K`. Its differential
at `p` carries the fixed tangent subspace at `p` onto the one at `ψ p`
(`Diffeomorph.map_fixedTangentSubspace`), and it is a linear symplectomorphism between them for
the restrictions of `σ_p` and `τ_(ψ p)`
(`TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectomorphism_fixedTangentSubspaceEquiv`); it also
carries the symplectic normal space, the `σ_p`-complement of the fixed tangent subspace, onto the
`τ_(ψ p)`-complement at `ψ p`
(`TauCeti.SmoothTwoForm.IsNondegenerate.map_orthogonal_fixedTangentSubspace`). A globally
equivariant `ψ` carries the fixed set, its parts `M^K_d` and its connected components onto those
of `M₂` (`TauCeti.MulAction.image_fixedPoints_of_bijective`,
`Diffeomorph.image_fixedPointsOfFinrank`, `Homeomorph.image_connectedComponentIn_fixedPoints`).

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
* `TauCeti.SmoothTwoForm.IsNondegenerate.symplecticFormAt_fixedTangentSubspaceEquiv_apply`: the
  restricted differential of an equivariant symplectomorphism preserves the symplectic forms.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectomorphism_fixedTangentSubspaceEquiv`,
  `IsNondegenerate.nondegenerate_restrict_fixedTangentSubspace_of_mpullback_eq`: an
  equivariant symplectomorphism restricts to a linear symplectomorphism of the fixed tangent
  subspaces with their restricted forms, and carries a nondegenerate restricted form at `p` to a
  nondegenerate restricted form at `ψ p`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.map_orthogonal_fixedTangentSubspace`: it carries the
  symplectic normal spaces of the fixed locus onto each other.

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

section FixedLocus

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

end FixedLocus

/-! ### Naturality under equivariant symplectomorphisms -/

section Naturality

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E₂ H₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  {I₂ : ModelWithCorners ℝ E₂ H₂} {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [IsManifold I₂ ∞ M₂]
  {K : Type*} [Group K] [MulAction K M] [MulAction K M₂]
  {σ : SmoothTwoForm I M} {τ : SmoothTwoForm I₂ M₂} (hσ : σ.IsNondegenerate)
  {hτ : τ.IsNondegenerate} (ψ : M ≃ₘ⟮I, I₂⟯ M₂)
  (hψ : SmoothForm.mpullback ψ ψ.contMDiff τ = σ) {p : M}
  (hK : ∀ k : K, ψ ∘ (k • ·) =ᶠ[𝓝 p] (k • ·) ∘ ψ)

include hψ hK

/-- The differential at `p` of a diffeomorphism pulling `τ` back to `σ` and commuting near `p` with
the action of every element of `K`, restricted to the fixed tangent subspaces, preserves the
symplectic forms at `p` and at `ψ p`. -/
theorem IsNondegenerate.symplecticFormAt_fixedTangentSubspaceEquiv_apply
    (v w : fixedTangentSubspace I K p) :
    hτ.symplecticFormAt (ψ p) (ψ.fixedTangentSubspaceEquiv (by simp) hK v)
        (ψ.fixedTangentSubspaceEquiv (by simp) hK w) =
      hσ.symplecticFormAt p v w := by
  simpa using
    (hσ.isSymplectomorphism_mfderivToContinuousLinearEquiv (hσ₂ := hτ) ψ hψ p).apply
    (v : TangentSpace I p) w

/-- The restriction of `τ_(ψ p)` to the fixed tangent subspace at `ψ p` is nondegenerate when the
restriction of `σ_p` to the fixed tangent subspace at `p` is, for a diffeomorphism `ψ` pulling `τ`
back to `σ` and commuting near `p` with the action of every element of `K`. -/
theorem IsNondegenerate.nondegenerate_restrict_fixedTangentSubspace_of_mpullback_eq
    (h₁ : ((hσ.symplecticFormAt p).toBilinForm.restrict
      (fixedTangentSubspace I K p)).Nondegenerate) :
    ((hτ.symplecticFormAt (ψ p)).toBilinForm.restrict
      (fixedTangentSubspace I₂ K (ψ p))).Nondegenerate := by
  rw [← SymplecticForm.isSymplectic_iff_nondegenerate_restrict,
    ← hσ.symplecticFormAt_transport ψ hψ, ← ψ.map_fixedTangentSubspace (by simp) hK,
    SymplecticForm.isSymplectic_map_transport_iff]
  exact SymplecticForm.isSymplectic_iff_nondegenerate_restrict.2 h₁

/-- **Equivariant symplectomorphisms transport the restricted forms of the fixed locus.** The
differential at `p` of a diffeomorphism pulling `τ` back to `σ` and commuting near `p` with the
action of every element of `K` restricts to a linear symplectomorphism from the fixed tangent
subspace at `p`, with the restriction of `σ_p`, to the fixed tangent subspace at `ψ p`, with the
restriction of `τ_(ψ p)`. -/
theorem IsNondegenerate.isSymplectomorphism_fixedTangentSubspaceEquiv
    (h₁ : ((hσ.symplecticFormAt p).toBilinForm.restrict
      (fixedTangentSubspace I K p)).Nondegenerate) :
    SymplecticForm.IsSymplectomorphism ((hσ.symplecticFormAt p).restrict _ h₁)
      ((hτ.symplecticFormAt (ψ p)).restrict _
        (hσ.nondegenerate_restrict_fixedTangentSubspace_of_mpullback_eq ψ hψ hK h₁))
      (ψ.fixedTangentSubspaceEquiv (by simp) hK) :=
  SymplecticForm.isSymplectomorphism_iff.2 fun v w ↦ by
    rw [SymplecticForm.restrict_apply, SymplecticForm.restrict_apply]
    exact hσ.symplecticFormAt_fixedTangentSubspaceEquiv_apply ψ hψ hK v w

/-- **Equivariant symplectomorphisms transport the symplectic normal spaces of the fixed locus.**
The differential at `p` of a diffeomorphism pulling `τ` back to `σ` and commuting near `p` with
the action of every element of `K` carries the symplectic complement of the fixed tangent
subspace at `p` onto the symplectic complement of the fixed tangent subspace at `ψ p`. -/
theorem IsNondegenerate.map_orthogonal_fixedTangentSubspace :
    ((hσ.symplecticFormAt p).orthogonal (fixedTangentSubspace I K p)).map
        (ψ.mfderivToContinuousLinearEquiv (by simp) p).toLinearEquiv.toLinearMap =
      (hτ.symplecticFormAt (ψ p)).orthogonal (fixedTangentSubspace I₂ K (ψ p)) := by
  rw [(hσ.isSymplectomorphism_mfderivToContinuousLinearEquiv (hσ₂ := hτ) ψ hψ p).map_orthogonal,
    ψ.map_fixedTangentSubspace _ hK]

end Naturality

end TauCeti.SmoothTwoForm
