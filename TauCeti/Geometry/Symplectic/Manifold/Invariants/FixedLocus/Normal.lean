/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.FixedPoints
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Symplectic.Normal
public import TauCeti.Geometry.Symplectic.Manifold.Invariants.FixedLocus

/-!
# The isotropy representation on the symplectic normal bundle of a fixed submanifold

Let a group `K` act on a manifold `N` by differentiable maps, and let `f : M → N` be a smooth
embedding of a submanifold of fixed points: `k • f x = f x` for every `k` and `x`. The isotropy
representation `TauCeti.SmoothEmbedding.fixedNormalRepresentation` of `K` on the normal spaces of
`f`, constructed in
`TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.FixedPoints`, acts on the
class of a tangent vector `w` at `f x` as the class of `d(k •)_(f x) w`.

Now let `σ` be a nondegenerate two-form on `N` preserved by the action, and let the submanifold be
symplectic. Its normal bundle is the symplectic normal bundle: each normal class has a unique
representative in the symplectic complement `(df_x (T_x M))^σ`
(`TauCeti.SmoothEmbedding.symplecticNormalRepresentative`), and `σ` induces the normal symplectic
form `TauCeti.SmoothEmbedding.symplecticNormalForm` on the normal spaces. The isotropy
representation is compatible with this structure:

* taking symplectic representatives is equivariant: the representative of `k • ν` is
  `d(k •)_(f x)` applied to the representative of `ν`
  (`TauCeti.SmoothEmbedding.symplecticNormalRepresentative_fixedNormalRepresentation`), so the
  normal representation is the restriction of the tangent representation to the symplectic
  complement of the tangent space of the submanifold;
* `K` acts by linear symplectic maps of the normal symplectic form
  (`TauCeti.SmoothEmbedding.symplecticNormalForm_fixedNormalRepresentation`);
* if every tangent vector at `f x` fixed by `K` is tangent to the submanifold, the normal
  representation has no nonzero fixed vector
  (`TauCeti.SmoothEmbedding.invariants_fixedNormalRepresentation_eq_bot`).

The last hypothesis holds on the parts `M^K_d` of the fixed set of a group of symplectic
isometries, whose tangent spaces are exactly the fixed tangent subspaces
(`IsNondegenerate.exists_isSymplecticSubmanifoldEmbedding_fixedPointsOfFinrank`).
So on each normal fibre of a fixed component `M^K_d`, `K` acts by linear symplectic maps of the
normal symplectic form (`TauCeti.SmoothEmbedding.symplecticNormalForm_fixedNormalRepresentation`)
without nonzero fixed vectors
(`IsNondegenerate.invariants_fixedNormalRepresentation_fixedPointsOfFinrank_eq_bot`).
For a torus action this is the input to the decomposition of the normal spaces of the fixed
components into nonzero weights. The normal symplectic form depends smoothly on the base point
(`TauCeti.SmoothEmbedding.contMDiff_symplecticNormalFlat`). The hypothesis that the submanifold
is symplectic cannot be dropped: the symplectic shear `(q, p) ↦ (q + p, p)` of `ℝ²` fixes the
Lagrangian line `p = 0`, whose tangent vectors are exactly the fixed tangent vectors, and the
normal class `[e₂]` is fixed although `e₂` is not.

## Main results

* `TauCeti.SmoothEmbedding.symplecticNormalRepresentative_fixedNormalRepresentation`: symplectic
  representatives are equivariant.
* `TauCeti.SmoothEmbedding.symplecticNormalForm_fixedNormalRepresentation`: the normal
  representation preserves the normal symplectic form.
* `TauCeti.SmoothEmbedding.invariants_fixedNormalRepresentation_eq_bot`: it has no nonzero fixed
  vector when the submanifold contains every fixed tangent direction.
* `IsNondegenerate.invariants_fixedNormalRepresentation_fixedPointsOfFinrank_eq_bot` (in
  `TauCeti.SmoothTwoForm`): this applies to the parts `M^K_d` of the fixed set of a group of
  symplectic isometries.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Homework 21, exercise 2 (fixed points of a group of symplectic isometries).
* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15
  (the normal bundles of the fixed components and their weights).
* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513.
-/

public noncomputable section

open Bundle MulAction
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {E V H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {K : Type*} [Group K] [MulAction K N]
  (f : SmoothEmbedding I J n M N) (hf : ∀ (k : K) (x : M), k • f x = f x)

/-! ### Compatibility with the symplectic normal structure -/

section Symplectic

open SmoothTwoForm

variable [FiniteDimensional ℝ V] [IsManifold J ∞ N] [ContMDiffConstSMul J ∞ K N]
  {σ : SmoothTwoForm J N} {hσ : σ.IsNondegenerate}
  (hσK : ∀ k : K, SmoothForm.mpullback (fun y : N ↦ k • y) (contMDiff_const_smul k) σ = σ)

include hσK in
/-- **Symplectic representatives are equivariant.** For an action preserving `σ` and a symplectic
submanifold of fixed points, the symplectic representative of `k • ν` is the image under
`d(k •)_(f x)` of the symplectic representative of `ν`. -/
theorem symplecticNormalRepresentative_fixedNormalRepresentation
    (h : hσ.HasSymplecticTangentImages I f)
    (x : M) (hn : n ≠ 0) (hd : ∀ k : K, MDifferentiableAt J J (fun y : N ↦ k • y) (f x))
    (k : K) (ν : f.NormalSpace x hn) :
    f.symplecticNormalRepresentative h x hn (f.fixedNormalRepresentation hf x hn hd k ν) =
      mfderiv J J (fun y : N ↦ k • y) (f x) (f.symplecticNormalRepresentative h x hn ν) := by
  refine (f.symplecticNormalRepresentative_eq_iff h x hn _ _).2 ⟨?_, ?_⟩
  · -- `d(k •)` fixes the tangent space and preserves `σ_(f x)`, so it preserves the complement.
    simpa using SymplecticForm.apply_mem_orthogonal
      (hσ.symplecticFormAt_tangentRepresentationOfMemFixedPoints hσK
        (mem_fixedPoints.2 fun g ↦ hf g x) hd)
      (fun g _ hv ↦ f.tangentRange_le_comap_tangentRepresentationOfMemFixedPoints hf x hn hd g hv)
      k (f.symplecticNormalRepresentative_mem_orthogonal h x hn ν)
  · rw [← fixedNormalRepresentation_normalClass, normalClass_symplecticNormalRepresentative]

include hσK in
/-- **The normal representation is symplectic.** For an action preserving `σ` and a symplectic
submanifold of fixed points, each `k` acts on the normal space by a linear symplectic map of the
normal symplectic form. -/
theorem symplecticNormalForm_fixedNormalRepresentation
    (h : hσ.HasSymplecticTangentImages I f)
    (x : M) (hn : n ≠ 0) (hd : ∀ k : K, MDifferentiableAt J J (fun y : N ↦ k • y) (f x))
    (k : K) (ν μ : f.NormalSpace x hn) :
    f.symplecticNormalForm h x hn (f.fixedNormalRepresentation hf x hn hd k ν)
        (f.fixedNormalRepresentation hf x hn hd k μ) =
      f.symplecticNormalForm h x hn ν μ := by
  have hsymp := hσ.symplecticFormAt_tangentRepresentationOfMemFixedPoints hσK
    (mem_fixedPoints.2 fun g ↦ hf g x) hd k (f.symplecticNormalRepresentative h x hn ν)
    (f.symplecticNormalRepresentative h x hn μ)
  rw [IsNondegenerate.symplecticFormAt_apply, IsNondegenerate.symplecticFormAt_apply,
    tangentRepresentationOfMemFixedPoints_apply, tangentRepresentationOfMemFixedPoints_apply]
    at hsymp
  simp only [symplecticNormalForm_apply,
    f.symplecticNormalRepresentative_fixedNormalRepresentation hf hσK h]
  exact hsymp

include hσK in
/-- **The normal representation has no nonzero fixed vector.** For an action preserving `σ` and a
symplectic submanifold of fixed points containing every fixed tangent direction at `f x`, the
only normal vector at `x` fixed by every element of `K` is zero. -/
theorem invariants_fixedNormalRepresentation_eq_bot
    (h : hσ.HasSymplecticTangentImages I f)
    (x : M) (hn : n ≠ 0) (hd : ∀ k : K, MDifferentiableAt J J (fun y : N ↦ k • y) (f x))
    (hfix : fixedTangentSubspace J K (f x) ≤ f.tangentRange x hn) :
    (f.fixedNormalRepresentation hf x hn hd).invariants = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun ν hν ↦ ?_
  set w := f.symplecticNormalRepresentative h x hn ν
  -- The representative `w` of a fixed class is a fixed tangent vector, hence tangent.
  have hw : w ∈ f.tangentRange x hn := hfix <| mem_fixedTangentSubspace.2 fun k _ ↦ by
    rw [← f.symplecticNormalRepresentative_fixedNormalRepresentation hf hσK h x hn hd,
      hν k]
  -- It also lies in the symplectic complement of the tangent space, which meets it in zero.
  have hw0 : w = 0 := Submodule.disjoint_def.1 (SymplecticForm.isSymplectic_iff_disjoint.1
    (IsNondegenerate.hasSymplecticTangentImages_iff_forall.1 h x)) w hw
      (f.symplecticNormalRepresentative_mem_orthogonal h x hn ν)
  have hνw : f.normalClass x hn w = ν := f.normalClass_symplecticNormalRepresentative h x hn ν
  rw [← hνw, hw0, map_zero]

end Symplectic

end TauCeti.SmoothEmbedding

/-! ### The fixed locus of a group of symplectic isometries -/

namespace TauCeti.SmoothTwoForm

open MulAction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {K : Type*} [Group K] [MulAction K M] [ContMDiffConstSMul 𝓘(ℝ, E) ∞ K M]
  {σ : SmoothTwoForm 𝓘(ℝ, E) M}

/-- **The normal representations along the fixed locus of a group of symplectomorphisms.** For
a group acting by maps preserving a nondegenerate two-form `σ`, let the part `M^K_d` of the fixed
set carry a manifold structure modelled on a subspace `L` of the model, for which the inclusion is
a symplectic submanifold embedding whose tangent image contains the fixed tangent subspace at
every point. This is the structure that
`IsNondegenerate.exists_isSymplecticSubmanifoldEmbedding_fixedPointsOfFinrank` provides for a
group of symplectic isometries. Then the normal representation at every point of `M^K_d` has no
nonzero fixed vector. -/
theorem IsNondegenerate.invariants_fixedNormalRepresentation_fixedPointsOfFinrank_eq_bot
    (hσK : ∀ k : K, SmoothForm.mpullback (fun y : M ↦ k • y) (contMDiff_const_smul k) σ = σ)
    (hσ : σ.IsNondegenerate) {d : ℕ} {L : Submodule ℝ E}
    [ChartedSpace L (fixedPointsOfFinrank 𝓘(ℝ, E) K M d)]
    (hemb : hσ.IsSymplecticSubmanifoldEmbedding 𝓘(ℝ, L)
      (Subtype.val : fixedPointsOfFinrank 𝓘(ℝ, E) K M d → M))
    (hrange : ∀ y : fixedPointsOfFinrank 𝓘(ℝ, E) K M d,
      fixedTangentSubspace 𝓘(ℝ, E) K (y : M) ≤
        LinearMap.range (mfderiv 𝓘(ℝ, L) 𝓘(ℝ, E) Subtype.val y).toLinearMap)
    (y : fixedPointsOfFinrank 𝓘(ℝ, E) K M d) :
    ((SmoothEmbedding.ofIsSmoothEmbedding (I := 𝓘(ℝ, L)) (J := 𝓘(ℝ, E)) (n := ∞) _
      hemb.isSmoothEmbedding).fixedNormalRepresentation
      (fun (k : K) y ↦ by simpa using fixedPointsOfFinrank_subset_fixedPoints d y.property k) y
      (by simp) fun k ↦ ContMDiffConstSMul.mdifferentiable_const_smul (n := ∞) (by simp) k _
      ).invariants = ⊥ := by
  refine SmoothEmbedding.invariants_fixedNormalRepresentation_eq_bot (hσ := hσ) _ _ hσK ?_ y _ _ ?_
  · simpa using hemb.hasSymplecticTangentImages
  · -- Replace the bundled embedding by its underlying inclusion, on which `hrange` is stated.
    rw [SmoothEmbedding.tangentRange]
    generalize hG : ⇑(SmoothEmbedding.ofIsSmoothEmbedding (I := 𝓘(ℝ, L)) (J := 𝓘(ℝ, E))
      (n := ∞) _ hemb.isSmoothEmbedding) = G
    rw [SmoothEmbedding.coe_ofIsSmoothEmbedding] at hG
    subst hG
    exact hrange y

end TauCeti.SmoothTwoForm
