/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.FixedPoints.Submanifold
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Hessian
public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson
import TauCeti.Analysis.Calculus.Deriv.OperatorCurve
import TauCeti.Geometry.Manifold.Riemannian.Invariant
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Polar

/-!
# Components of a moment map are Morse–Bott

Let a Lie group `G` act smoothly on a manifold `M` with a nondegenerate two-form `σ`, with moment
map `μ : M → 𝔤*`, and let `ξ ∈ 𝔤`. Write `T_ξ` for the closure of `{exp (t ξ) | t ∈ ℝ}`
(`TauCeti.Lie.closedOneParameterSubgroup ξ`). The critical set of the component `μ^ξ = ⟨μ, ξ⟩` is
the fixed-point set `M^{T_ξ}` (`TauCeti.SmoothTwoForm.IsMomentMap.criticalPoints_eq_fixedPoints`),
and at a critical point `p` the null space of the Hessian of `μ^ξ` is the space of tangent vectors
fixed by the differentials of all elements of `T_ξ`
(`TauCeti.SmoothTwoForm.IsMomentMap.criticalHessian_apply_eq_zero_iff`), the fixed tangent subspace
`TauCeti.fixedTangentSubspace`. This file proves that `μ^ξ` is a **Morse–Bott function** when
`T_ξ` preserves a smooth Riemannian metric, for instance when `G` is compact and `M` is σ-compact:
for manifolds modelled on a finite-dimensional real vector space (model `𝓘(ℝ, E')`), its critical
set is a disjoint union of embedded submanifolds, along each of which the null space of the Hessian
is exactly the tangent space. Unqualified names below are in the namespace
`TauCeti.SmoothTwoForm.IsMomentMap`.

The submanifolds come from the fixed locus of a group of isometries. When `T_ξ` preserves a smooth
Riemannian metric, the points of `M^{T_ξ}` whose fixed tangent subspace has dimension `d` form an
embedded submanifold `M^{T_ξ}_d` whose tangent space at each point is that fixed tangent subspace
(`TauCeti.exists_isSmoothEmbedding_fixedPointsOfFinrank`), and these sets partition `M^{T_ξ}`
(`TauCeti.iUnion_fixedPointsOfFinrank`, `TauCeti.pairwise_disjoint_fixedPointsOfFinrank`).
Comparing the two descriptions of the fixed tangent subspace, each `M^{T_ξ}_d` is a nondegenerate
critical submanifold of `μ^ξ` (`exists_isNondegenerateCriticalSubmanifold_fixedPointsOfFinrank`),
and so is every subset of `M^{T_ξ}_d` which is open in `M^{T_ξ}`, such as a connected component of
the critical set or a union of orbits of a group commuting with `T_ξ` that is open in `M^{T_ξ}`
(`exists_isNondegenerateCriticalSubmanifold_of_subset_fixedPointsOfFinrank`).
The comparison itself holds for every smooth embedding into `M^{T_ξ}` whose tangent images contain
the fixed tangent subspaces (`isNondegenerateCriticalSubmanifold_of_fixedTangentSubspace_le`).

For a compact group `G` acting on a σ-compact manifold, averaging a Riemannian metric over `G`
gives an invariant one (`TauCeti.exists_contMDiffRiemannianMetric_inner_mfderiv`), so no metric
needs to be supplied: every component of the moment map of a compact symplectic action, in
particular of a Hamiltonian torus action, is Morse–Bott
(`exists_isNondegenerateCriticalSubmanifold_fixedPointsOfFinrank_of_compactSpace`). For a torus
`T` and a generic `ξ`, `T_ξ = T`; when `T_ξ = G`, the critical submanifolds are the sets `M^G_d`,
the unions of the `d`-dimensional components of the fixed-point set `M^G`.

For a compact group acting by symplectomorphisms on a σ-compact manifold, the Morse index and the
coindex of `μ^ξ` at every critical point `p` are even (`even_manifoldMorseIndex`,
`even_manifoldMorseIndex_neg`). The Hessian at `p` is `σ_p(A v, w)` for the infinitesimal isotropy
action `A` of `ξ` on `T_p M`
(`TauCeti.SmoothTwoForm.IsMomentMap.criticalHessian_apply_eq_eval₂_deriv`). Being the derivative of
a curve of symplectic maps commuting with an invariant compatible complex structure `J_p`, `A` lies
in `sp(T_p M, σ_p)` and is complex linear for `J_p`, so it rotates the planes of a Darboux basis
and its quadratic Hamiltonian has indices of inertia twice the numbers of its negative and
positive rotation frequencies (`TauCeti.SymplecticForm.even_sigNeg_hamiltonianEndEquiv_symm`).

Neither closedness of `σ`, equivariance of `μ` nor compactness of `M` is used.

## Main results

All declarations are in the namespace `TauCeti.SmoothTwoForm.IsMomentMap`.

* `isNondegenerateCriticalSubmanifold_of_fixedTangentSubspace_le`: a smooth embedding into
  `M^{T_ξ}` whose tangent images contain the fixed tangent subspaces of `T_ξ` is a Morse–Bott
  critical submanifold of `μ^ξ`.
* `criticalPoints_eq_iUnion_fixedPointsOfFinrank`: the critical set of `μ^ξ` is the union of the
  sets `M^{T_ξ}_d`.
* `exists_isNondegenerateCriticalSubmanifold_of_subset_fixedPointsOfFinrank`: if `T_ξ` acts by
  isometries of a smooth metric, each subset of `M^{T_ξ}_d` open in `M^{T_ξ}` is a Morse–Bott
  critical submanifold of `μ^ξ`, with tangent spaces the fixed tangent subspaces.
* `exists_isNondegenerateCriticalSubmanifold_fixedPointsOfFinrank`: in particular so is each
  `M^{T_ξ}_d`.
* `exists_isNondegenerateCriticalSubmanifold_of_subset_fixedPointsOfFinrank_of_compactSpace`,
  `exists_isNondegenerateCriticalSubmanifold_fixedPointsOfFinrank_of_compactSpace`: the same for
  a compact group acting on a σ-compact manifold, without a metric.
* `even_manifoldMorseIndex`, `even_manifoldMorseIndex_neg`: for a compact group acting by
  symplectomorphisms on a σ-compact manifold, the index and the coindex of `μ^ξ` at every critical
  point are even.

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15,
  § 2 (the components of the moment map are Morse–Bott functions).
* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513, § 3.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, § 27.1 and Homework 21.
-/

public section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {ξ : GroupLieAlgebra I G}

omit [T2Space G] [IsTopologicalGroup G] [I'.Boundaryless] [T2Space M] in
/-- At a critical point of `μ^ξ`, the fundamental vector field `ξ_M` vanishes. -/
private theorem fundamentalVectorField_eq_zero_of_mem_criticalPoints
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate)
    {p : M} (hp : p ∈ criticalPoints I' fun y ↦ μ y ξ) : fundamentalVectorField I' ξ p = 0 := by
  rw [← InfinitesimalAction.fundamental_apply]
  exact (h.mem_criticalPoints_iff (hσ.nondegenerate_bilinFormAt _) ξ).1 hp

/-- **A moment map component is Morse–Bott along the fixed submanifolds of `T_ξ`.** Let `i` be a
smooth embedding whose points are fixed by the closure `T_ξ` of `{exp (t ξ) | t ∈ ℝ}`, and whose
tangent image at each point contains the tangent vectors fixed by the differentials of all
elements of `T_ξ`. Then `i` is a nondegenerate critical submanifold of the component `μ^ξ`. -/
theorem isNondegenerateCriticalSubmanifold_of_fixedTangentSubspace_le
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hσ : σ.IsNondegenerate) {E'' H'' S : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    [TopologicalSpace H''] {J : ModelWithCorners ℝ E'' H''} [TopologicalSpace S]
    [ChartedSpace H'' S] {n : ℕ∞ω} {i : SmoothEmbedding J I' n S M}
    (hfix : ∀ s, i s ∈ MulAction.fixedPoints (Lie.closedOneParameterSubgroup ξ) M)
    (hle : ∀ s, fixedTangentSubspace I' (Lie.closedOneParameterSubgroup ξ) (i s) ≤
      LinearMap.range (mfderiv J I' i s).toLinearMap) :
    i.IsNondegenerateCriticalSubmanifold fun y ↦ μ y ξ := by
  have hcrit (s : S) : i s ∈ criticalPoints I' fun y ↦ μ y ξ := by
    rw [h.criticalPoints_eq_fixedPoints hσ]
    exact hfix s
  refine ⟨⟨fun s ↦ (h.contMDiff ξ (i s)).of_le (by simp), hcrit⟩, fun s v hv ↦ hle s ?_⟩
  rw [mem_fixedTangentSubspace_iff_of_mem_fixedPoints (hfix s)]
  exact fun g ↦ (h.criticalHessian_apply_eq_zero_iff hσ
    (h.fundamentalVectorField_eq_zero_of_mem_criticalPoints hσ (hcrit s)) v).1 hv g g.property

/-- **The critical set of `μ^ξ` is the union of the fixed sets `M^{T_ξ}_d`**, the points fixed by
the closure `T_ξ` of `{exp (t ξ) | t ∈ ℝ}` at which the fixed tangent subspace of `T_ξ` has
dimension `d`. -/
theorem criticalPoints_eq_iUnion_fixedPointsOfFinrank
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hσ : σ.IsNondegenerate) (ξ : GroupLieAlgebra I G) :
    criticalPoints I' (fun y ↦ μ y ξ) =
      ⋃ d, fixedPointsOfFinrank I' (Lie.closedOneParameterSubgroup ξ) M d := by
  rw [h.criticalPoints_eq_fixedPoints hσ, iUnion_fixedPointsOfFinrank]

section Index

variable [CompactSpace G] [SigmaCompactSpace M]

/-- At a critical point `p` of `μ^ξ`, for a compact group acting by symplectomorphisms on a
σ-compact manifold, the Hessian of `μ^ξ` is twice the quadratic Hamiltonian of an element `A` of
`sp(T_p M, σ_p)` which is complex linear for a complex structure compatible with `σ_p`. Here `A` is
the infinitesimal isotropy action of `ξ` at `p`, and the complex structure is the value at `p` of an
invariant compatible one. -/
private theorem exists_toQuadraticMap_criticalHessian_eq
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate)
    (hσG : ∀ (a : G) (x : M) (u v : TangentSpace I' x),
      σ.eval₂ (a • x) (mfderiv I' I' (a • ·) x u) (mfderiv I' I' (a • ·) x v) = σ.eval₂ x u v)
    {p : M} (hp : p ∈ criticalPoints I' fun y ↦ μ y ξ) :
    ∃ (J : AlmostComplexStructure (TangentSpace I' p))
      (A : skewAdjointLieSubalgebra (hσ.symplecticFormAt p).toBilinForm),
      (hσ.symplecticFormAt p).Compatible J ∧
        IsComplexLinearMap J J (A : Module.End ℝ (TangentSpace I' p)) ∧
        (criticalHessian I' (fun y ↦ μ y ξ) p).toBilinForm.toQuadraticMap =
          (2 : ℝ) • (hσ.symplecticFormAt p).hamiltonianEndEquiv.symm A := by
  have hp0 := h.fundamentalVectorField_eq_zero_of_mem_criticalPoints hσ hp
  have hfix : ∀ t : ℝ, mulInvariantExp (I := I) (t • ξ) • p = p :=
    (mulInvariantExp_smul_smul_eq_iff (I' := I')).2 hp0
  obtain ⟨J, hJ, hJG⟩ := hσ.exists_compatible_mfderiv_smul_apply_of_compactSpace (IG := I) hσG
  -- The differentials `D t = d(exp (t ξ))_p` of the isotropy action and their derivative `A`, as
  -- operators on the model space `E'` of `T_p M`.
  set D : ℝ → E' →L[ℝ] E' := fun t ↦
    mfderiv I' I' (fun y : M ↦ mulInvariantExp (I := I) (t • ξ) • y) p
  set A : E' →L[ℝ] E' := deriv D 0
  have hD : HasDerivAt D A 0 :=
    (hasDerivAt_mfderiv_mulInvariantExp_smul_smul hp0).differentiableAt.hasDerivAt
  have hD₀ : D 0 = 1 := mfderiv_mulInvariantExp_zero_smul_smul ξ p
  -- Each `D t` preserves `σ_p` and commutes with `J_p`, since `exp (t ξ)` fixes `p`; so `A` is
  -- skew for `σ_p` and commutes with `J_p`. Here `β` is `σ_p` read on the model space `E'`.
  let β : LinearMap.BilinForm ℝ E' := (hσ.symplecticFormAt p).toBilinForm
  have hβ (u v : E') : β u v = σ.eval₂ p u v := hσ.symplecticFormAt_apply p u v
  have hskew (u v : E') : β (A u) v = -β u (A v) := by
    simpa only [LinearMap.toContinuousBilinearMap_apply] using
      hD.apply_left_eq_neg_of_eventually_apply_apply_eq hD₀ β.toContinuousBilinearMap
        (Filter.Eventually.of_forall fun t u v ↦ by
          have := hσG (mulInvariantExp (I := I) (t • ξ)) p u v
          rw [hfix t] at this
          rw [LinearMap.toContinuousBilinearMap_apply, LinearMap.toContinuousBilinearMap_apply,
            hβ, hβ]
          exact this) u v
  have hcomm := hD.apply_apply_eq_of_eventually_apply_apply_eq (J.toEndomorphism p)
    (Filter.Eventually.of_forall fun t v ↦ by
      have := hJG (mulInvariantExp (I := I) (t • ξ)) p v
      rwa [hfix t] at this)
  -- The same operator `A` as an endomorphism of `T_p M`: `A' v` is `A v` read in `T_p M`.
  let A' : Module.End ℝ (TangentSpace I' p) := (A : E' →ₗ[ℝ] E')
  have hA'v (v : TangentSpace I' p) : A' v = A v := rfl
  have hA' : A' ∈ skewAdjointLieSubalgebra (hσ.symplecticFormAt p).toBilinForm := by
    refine (LinearMap.mem_skewAdjointSubmodule _).2 fun u v ↦ ?_
    rw [Pi.neg_apply, map_neg, hA'v, hA'v]
    exact hskew u v
  have hAJ : IsComplexLinearMap (J.almostComplexStructureAt p) (J.almostComplexStructureAt p) A' :=
    (isComplexLinearMap_iff_apply _ _ _).2 fun v ↦ by
      rw [J.almostComplexStructureAt_apply, J.almostComplexStructureAt_apply, hA'v, hA'v]
      exact hcomm v
  refine ⟨J.almostComplexStructureAt p, ⟨A', hA'⟩, hJ.compatibleAt p, hAJ, ?_⟩
  -- The Hessian is `σ_p(A v, v)`, twice the quadratic Hamiltonian `½ σ_p(A v, v)` of `A`.
  ext v
  rw [LinearMap.BilinMap.toQuadraticMap_apply, ContinuousLinearMap.toBilinForm_apply,
    h.criticalHessian_apply_eq_eval₂_deriv hσ hp0, smul_apply,
    SymplecticForm.hamiltonianEndEquiv_symm_apply_apply, SymplecticForm.linearMomentMap_apply,
    hσ.symplecticFormAt_apply, smul_eq_mul, mul_div_cancel₀ _ two_ne_zero, hA'v]

/-- **Moment map components have even Morse index.** For a compact Lie group acting smoothly by
symplectomorphisms of a σ-compact manifold, with moment map `μ`, the Morse index of the component
`μ^ξ` at every critical point is even. -/
theorem even_manifoldMorseIndex
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate)
    (hσG : ∀ (a : G) (x : M) (u v : TangentSpace I' x),
      σ.eval₂ (a • x) (mfderiv I' I' (a • ·) x u) (mfderiv I' I' (a • ·) x v) = σ.eval₂ x u v)
    {p : M} (hp : p ∈ criticalPoints I' fun y ↦ μ y ξ) :
    Even (manifoldMorseIndex I' (fun y ↦ μ y ξ) p) := by
  obtain ⟨J, A, hJ, hA, hQ⟩ := h.exists_toQuadraticMap_criticalHessian_eq hσ hσG hp
  rw [manifoldMorseIndex_eq_sigNeg_criticalHessian, hQ,
    QuadraticForm.sigNeg_smul_of_pos _ two_pos]
  exact SymplecticForm.even_sigNeg_hamiltonianEndEquiv_symm hJ A hA

/-- **Moment map components have even coindex.** For a compact Lie group acting smoothly by
symplectomorphisms of a σ-compact manifold, with moment map `μ`, the Morse index of `-μ^ξ`, the
coindex of `μ^ξ`, at every critical point is even. -/
theorem even_manifoldMorseIndex_neg
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate)
    (hσG : ∀ (a : G) (x : M) (u v : TangentSpace I' x),
      σ.eval₂ (a • x) (mfderiv I' I' (a • ·) x u) (mfderiv I' I' (a • ·) x v) = σ.eval₂ x u v)
    {p : M} (hp : p ∈ criticalPoints I' fun y ↦ μ y ξ) :
    Even (manifoldMorseIndex I' (-fun y ↦ μ y ξ) p) := by
  obtain ⟨J, A, hJ, hA, hQ⟩ := h.exists_toQuadraticMap_criticalHessian_eq hσ hσG hp
  rw [manifoldMorseIndex_neg_eq_sigPos_criticalHessian, hQ,
    QuadraticForm.sigPos_smul_of_pos _ two_pos]
  exact SymplecticForm.even_sigPos_hamiltonianEndEquiv_symm hJ A hA

end Index

end General

section Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {M : Type*} [TopologicalSpace M] [ChartedSpace E' M] [IsManifold 𝓘(ℝ, E') ∞ M] [T2Space M]
  [MulAction G M] [ContMDiffSMul I 𝓘(ℝ, E') ∞ G M]
  {σ : SmoothTwoForm 𝓘(ℝ, E') M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {ξ : GroupLieAlgebra I G}

/-- **Open parts of the critical set of a single dimension are Morse–Bott.** Suppose that the
closure `T_ξ` of `{exp (t ξ) | t ∈ ℝ}` acts by isometries of a smooth Riemannian metric. Let `s` be
a subset of the fixed set `M^{T_ξ}`, the critical set of `μ^ξ`, which is open in it and at whose
points the fixed tangent subspace of `T_ξ` has dimension `d`. For every subspace `L` of the model of
dimension `d`, `s` is a smooth manifold modelled on `L` whose inclusion into `M` is a smooth
embedding and a nondegenerate critical submanifold of the component `μ^ξ`, with tangent image at
each point the fixed tangent subspace of `T_ξ`. -/
theorem exists_isNondegenerateCriticalSubmanifold_of_subset_fixedPointsOfFinrank
    [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E') x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E') ∞ E' (fun x : M ↦ TangentSpace 𝓘(ℝ, E') x)]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) μ)
    (hσ : σ.IsNondegenerate)
    (hK : ∀ g ∈ Lie.closedOneParameterSubgroup ξ, ∀ (x : M) (u w : TangentSpace 𝓘(ℝ, E') x),
      inner ℝ (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') (g • ·) x u) (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') (g • ·) x w) =
        inner ℝ u w)
    {s : Set M} {d : ℕ} {L : Submodule ℝ E'} (hL : Module.finrank ℝ L = d)
    (hsd : s ⊆ fixedPointsOfFinrank 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) M d)
    (hs : IsOpen ((↑) ⁻¹' s : Set (MulAction.fixedPoints (Lie.closedOneParameterSubgroup ξ) M))) :
    ∃ C : ChartedSpace L s, letI := C
      IsManifold 𝓘(ℝ, L) ∞ s ∧
        ∃ hi : IsSmoothEmbedding 𝓘(ℝ, L) 𝓘(ℝ, E') ∞ (Subtype.val : s → M),
          (SmoothEmbedding.ofIsSmoothEmbedding _ hi).IsNondegenerateCriticalSubmanifold
              (fun y ↦ μ y ξ) ∧
            ∀ y : s, LinearMap.range (mfderiv 𝓘(ℝ, L) 𝓘(ℝ, E') Subtype.val y).toLinearMap =
              fixedTangentSubspace 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) (y : M) := by
  have : ContMDiffConstSMul 𝓘(ℝ, E') ∞ G M := ⟨ContMDiffSMul.contMDiff_const_smul (I := I)⟩
  obtain ⟨C, hman, hemb, hrange⟩ :=
    exists_isSmoothEmbedding_of_subset_fixedPointsOfFinrank (K := Lie.closedOneParameterSubgroup ξ)
      (fun g ↦ hK g g.property) hL hsd hs
  let := C
  refine ⟨C, hman, hemb, h.isNondegenerateCriticalSubmanifold_of_fixedTangentSubspace_le hσ
    (fun y ↦ ?_) (fun y ↦ ?_), hrange⟩ <;> rw [SmoothEmbedding.coe_ofIsSmoothEmbedding]
  · exact (mem_fixedPointsOfFinrank.1 (hsd y.property)).1
  · exact (hrange y).ge

/-- **The components of a moment map are Morse–Bott.** Suppose that the closure `T_ξ` of
`{exp (t ξ) | t ∈ ℝ}` acts by isometries of a smooth Riemannian metric. For every subspace `L` of
the model of dimension `d`, the set `M^{T_ξ}_d` of points fixed by `T_ξ` whose fixed tangent
subspace has dimension `d` is a smooth manifold modelled on `L` whose inclusion into `M` is a
smooth embedding and a nondegenerate critical submanifold of the component `μ^ξ`, with tangent
image at each point the fixed tangent subspace of `T_ξ`. These sets cover the critical set of `μ^ξ`
(`criticalPoints_eq_iUnion_fixedPointsOfFinrank`). -/
theorem exists_isNondegenerateCriticalSubmanifold_fixedPointsOfFinrank
    [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E') x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E') ∞ E' (fun x : M ↦ TangentSpace 𝓘(ℝ, E') x)]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) μ)
    (hσ : σ.IsNondegenerate)
    (hK : ∀ g ∈ Lie.closedOneParameterSubgroup ξ, ∀ (x : M) (u w : TangentSpace 𝓘(ℝ, E') x),
      inner ℝ (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') (g • ·) x u) (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') (g • ·) x w) =
        inner ℝ u w)
    {d : ℕ} {L : Submodule ℝ E'} (hL : Module.finrank ℝ L = d) :
    ∃ C : ChartedSpace L
        (fixedPointsOfFinrank 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) M d), letI := C
      IsManifold 𝓘(ℝ, L) ∞
          (fixedPointsOfFinrank 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) M d) ∧
        ∃ hi : IsSmoothEmbedding 𝓘(ℝ, L) 𝓘(ℝ, E') ∞
          (Subtype.val : fixedPointsOfFinrank 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) M d →
            M),
          (SmoothEmbedding.ofIsSmoothEmbedding _ hi).IsNondegenerateCriticalSubmanifold
              (fun y ↦ μ y ξ) ∧
            ∀ y : fixedPointsOfFinrank 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) M d,
              LinearMap.range (mfderiv 𝓘(ℝ, L) 𝓘(ℝ, E') Subtype.val y).toLinearMap =
                fixedTangentSubspace 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) (y : M) :=
  have : ContMDiffConstSMul 𝓘(ℝ, E') ∞ G M := ⟨ContMDiffSMul.contMDiff_const_smul (I := I)⟩
  h.exists_isNondegenerateCriticalSubmanifold_of_subset_fixedPointsOfFinrank hσ hK hL subset_rfl
    (isOpen_preimage_val_fixedPointsOfFinrank (K := Lie.closedOneParameterSubgroup ξ)
      (fun g ↦ hK g g.property) d)

/-- **Open parts of the critical set of a compact group action are Morse–Bott.** For a compact Lie
group `G` acting smoothly on a σ-compact manifold with a nondegenerate two-form `σ` and moment map
`μ`, let `s` be a subset of the fixed set `M^{T_ξ}` of the closure `T_ξ` of
`{exp (t ξ) | t ∈ ℝ}`, the critical set of `μ^ξ`, which is open in it and at whose points the fixed
tangent subspace of `T_ξ` has dimension `d`. For every subspace `L` of the model of dimension `d`,
`s` is a smooth manifold modelled on `L` whose inclusion into `M` is a smooth embedding and a
nondegenerate critical submanifold of the component `μ^ξ`, with tangent image at each point the
fixed tangent subspace of `T_ξ`. -/
theorem exists_isNondegenerateCriticalSubmanifold_of_subset_fixedPointsOfFinrank_of_compactSpace
    [CompactSpace G] [SigmaCompactSpace M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) μ)
    (hσ : σ.IsNondegenerate) {s : Set M} {d : ℕ} {L : Submodule ℝ E'}
    (hL : Module.finrank ℝ L = d)
    (hsd : s ⊆ fixedPointsOfFinrank 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) M d)
    (hs : IsOpen ((↑) ⁻¹' s : Set (MulAction.fixedPoints (Lie.closedOneParameterSubgroup ξ) M))) :
    ∃ C : ChartedSpace L s, letI := C
      IsManifold 𝓘(ℝ, L) ∞ s ∧
        ∃ hi : IsSmoothEmbedding 𝓘(ℝ, L) 𝓘(ℝ, E') ∞ (Subtype.val : s → M),
          (SmoothEmbedding.ofIsSmoothEmbedding _ hi).IsNondegenerateCriticalSubmanifold
              (fun y ↦ μ y ξ) ∧
            ∀ y : s, LinearMap.range (mfderiv 𝓘(ℝ, L) 𝓘(ℝ, E') Subtype.val y).toLinearMap =
              fixedTangentSubspace 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) (y : M) :=
  of_forall_riemannianBundle_inner_mfderiv I G fun hG ↦
    h.exists_isNondegenerateCriticalSubmanifold_of_subset_fixedPointsOfFinrank hσ
      (fun a _ ↦ hG a) hL hsd hs

/-- **The components of the moment map of a compact group action are Morse–Bott.** For a compact
Lie group `G` acting smoothly on a σ-compact manifold with a nondegenerate two-form `σ` and moment
map `μ`, and for every `ξ` in the Lie algebra and every subspace `L` of the model of dimension
`d`, the set `M^{T_ξ}_d` of points fixed by the closure `T_ξ` of `{exp (t ξ) | t ∈ ℝ}` whose
fixed tangent subspace has dimension `d` is a smooth manifold modelled on `L` whose inclusion into
`M` is a smooth embedding and a nondegenerate critical submanifold of the component `μ^ξ`, with
tangent image at each point the fixed tangent subspace of `T_ξ`. -/
theorem exists_isNondegenerateCriticalSubmanifold_fixedPointsOfFinrank_of_compactSpace
    [CompactSpace G] [SigmaCompactSpace M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) μ)
    (hσ : σ.IsNondegenerate) {d : ℕ} {L : Submodule ℝ E'} (hL : Module.finrank ℝ L = d) :
    ∃ C : ChartedSpace L
        (fixedPointsOfFinrank 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) M d), letI := C
      IsManifold 𝓘(ℝ, L) ∞
          (fixedPointsOfFinrank 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) M d) ∧
        ∃ hi : IsSmoothEmbedding 𝓘(ℝ, L) 𝓘(ℝ, E') ∞
          (Subtype.val : fixedPointsOfFinrank 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) M d →
            M),
          (SmoothEmbedding.ofIsSmoothEmbedding _ hi).IsNondegenerateCriticalSubmanifold
              (fun y ↦ μ y ξ) ∧
            ∀ y : fixedPointsOfFinrank 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) M d,
              LinearMap.range (mfderiv 𝓘(ℝ, L) 𝓘(ℝ, E') Subtype.val y).toLinearMap =
                fixedTangentSubspace 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) (y : M) :=
  of_forall_riemannianBundle_inner_mfderiv I G fun hG ↦
    h.exists_isNondegenerateCriticalSubmanifold_fixedPointsOfFinrank hσ (fun a _ ↦ hG a) hL

end Model

end TauCeti.SmoothTwoForm.IsMomentMap
