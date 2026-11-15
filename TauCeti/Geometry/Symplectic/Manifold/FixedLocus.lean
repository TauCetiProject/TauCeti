/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.FixedLocus
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Symplectic.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Invariants

/-!
# The fixed locus of a group of symplectic isometries is a symplectic submanifold

Let a group `K` act on a Riemannian manifold `M` by smooth maps preserving the metric and a
nondegenerate two-form `σ`. No topology or Lie group structure on `K` is required. For each `d`,
the fixed points `p` of `K` at which the tangent vectors fixed by every differential `d(k •)_p`
form a subspace `V^K_p` of dimension `d` make up a closed embedded submanifold `M^K_d` of `M`, with
tangent space `V^K_p` at `p` (`TauCeti.exists_isSmoothEmbedding_fixedPointsFinrank`,
`TauCeti.range_mfderiv_eq_tangentInvariants`). Each `d(k •)_p` is a linear isometry and a linear
symplectomorphism of `T_p M`, so it commutes with the polar complex structure of `σ_p`, which
therefore preserves `V^K_p`; hence `V^K_p` is a symplectic subspace
(`TauCeti.SmoothTwoForm.IsNondegenerate.isSymplectic_invariants_tangentRepresentation_of_inner`).

So the inclusion of `M^K_d` is a symplectic submanifold embedding: it pulls `σ` back to a
nondegenerate two-form, which is symplectic when `σ` is.
The fixed set `M^K` is the disjoint union of the strata `M^K_d`, each of them closed, and open in
`M^K`, so every connected component of `M^K` lies in a single stratum
(`TauCeti.connectedComponentIn_fixedPoints_subset_fixedPointsFinrank`). Different strata may have
different dimensions, and every nonempty stratum has even dimension. This needs neither
completeness of the metric nor compactness of `M` or `K`. A compact Lie group acting smoothly by
symplectomorphisms preserves an averaged Riemannian metric, so the result applies to it.

## Main results

All declarations are in the namespace `TauCeti.SmoothTwoForm`.

* `IsNondegenerate.exists_isSymplecticSubmanifoldEmbedding_fixedPointsFinrank`: each stratum
  of the fixed set of a group of symplectic isometries is an embedded symplectic submanifold.
* `IsNondegenerate.even_of_mem_fixedPointsFinrank`: each nonempty stratum has even dimension.
* `IsSymplectic.exists_isSymplectic_mpullback_fixedPointsFinrank`: the restriction of a
  symplectic form to each stratum is symplectic.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Homework 21, exercise 2 (fixed sets of symplectic isometries are symplectic
  submanifolds) and Proposition 12.6 (the polar complex structure).
-/

public section

open Bundle Manifold Set MulAction
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.SmoothTwoForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {K : Type*} [Group K]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MulAction K M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [T2Space M] [ContMDiffConstSMul I ∞ K M] {σ : SmoothTwoForm I M}
  (hK : ∀ (k : K) (x : M) (u v : TangentSpace I x),
    inner ℝ (mfderiv I I (k • ·) x u) (mfderiv I I (k • ·) x v) = inner ℝ u v)
  (hσK : ∀ k : K, SmoothForm.mpullback (k • ·) (contMDiff_const_smul k) σ = σ)

include hK hσK

/-- **A stratum of the fixed set of a group of symplectic isometries is a symplectic
submanifold.** For a group acting by isometries preserving a nondegenerate two-form `σ`, the fixed
points at which the invariant tangent vectors form a subspace of dimension `d` make up a smooth
manifold modelled on any `d`-dimensional subspace `L` of the model space, whose inclusion into `M`
is an embedding with symplectic tangent images. -/
theorem IsNondegenerate.exists_isSymplecticSubmanifoldEmbedding_fixedPointsFinrank
    (hσ : σ.IsNondegenerate) {d : ℕ} {L : Submodule ℝ E} (hL : Module.finrank ℝ L = d) :
    ∃ C : ChartedSpace L (fixedPointsFinrank I K M d), letI := C
      IsManifold 𝓘(ℝ, L) ∞ (fixedPointsFinrank I K M d) ∧
        hσ.IsSymplecticSubmanifoldEmbedding 𝓘(ℝ, L)
          (Subtype.val : fixedPointsFinrank I K M d → M) := by
  obtain ⟨C, hC, hemb⟩ := exists_isSmoothEmbedding_fixedPointsFinrank hK hL
  refine ⟨C, hC, (isSymplecticSubmanifoldEmbedding_iff_of_isSmoothEmbedding hemb).2
    (hasSymplecticTangentImages_iff_forall.2 fun x ↦ ?_)⟩
  rw [range_mfderiv_eq_tangentInvariants (fun y ↦ y.2) hL
    (hemb.isImmersion.mfderiv_injective (by simp) x)]
  exact hσ.isSymplectic_invariants_tangentRepresentation_of_inner (fun k _ ↦ hK k x)
    (fun k _ ↦ hσK k) _

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [I.Boundaryless]
  [T2Space M] in
/-- **The strata of the fixed set of a group of symplectic isometries are even-dimensional.** At a
fixed point, the invariant tangent vectors form a symplectic subspace. -/
theorem IsNondegenerate.even_of_mem_fixedPointsFinrank (hσ : σ.IsNondegenerate) {d : ℕ} {p : M}
    (hp : p ∈ fixedPointsFinrank I K M d) : Even d := by
  have h := hσ.isSymplectic_invariants_tangentRepresentation_of_inner (x := p)
    (fun k _ ↦ hK k p) (fun k _ ↦ hσK k) fun k _ ↦
      (contMDiff_const_smul (I := I) (n := ∞) k).mdifferentiableAt (by simp)
  rw [← (mem_fixedPointsFinrank_iff.1 hp).2]
  exact ((hσ.symplecticFormAt p).restrict _ h.nondegenerate_restrict).even_finrank

/-- **The restriction of a symplectic form to a stratum of the fixed set is symplectic.** For a
group acting by isometries preserving a symplectic form `σ`, each stratum of the fixed set carries
a manifold structure for which the inclusion is a smooth embedding pulling `σ` back to a symplectic
form. -/
theorem IsSymplectic.exists_isSymplectic_mpullback_fixedPointsFinrank (hσ : σ.IsSymplectic)
    {d : ℕ} {L : Submodule ℝ E} (hL : Module.finrank ℝ L = d) :
    ∃ C : ChartedSpace L (fixedPointsFinrank I K M d), letI := C
      ∃ (_ : IsManifold 𝓘(ℝ, L) ∞ (fixedPointsFinrank I K M d))
        (hemb : IsSmoothEmbedding 𝓘(ℝ, L) I ∞ (Subtype.val : fixedPointsFinrank I K M d → M)),
        SmoothTwoForm.IsSymplectic (SmoothForm.mpullback _ hemb.contMDiff σ) := by
  obtain ⟨C, hC, h⟩ :=
    hσ.isNondegenerate.exists_isSymplecticSubmanifoldEmbedding_fixedPointsFinrank hK hσK hL
  exact ⟨C, hC, h.isSmoothEmbedding, h.isSymplectic_mpullback hσ⟩

end TauCeti.SmoothTwoForm
