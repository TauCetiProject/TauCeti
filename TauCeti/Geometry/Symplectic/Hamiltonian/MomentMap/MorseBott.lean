/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.Morse.Bott.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.FixedPoints.Submanifold
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Hessian
public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson
import TauCeti.Geometry.Manifold.MFDeriv.Opens
import TauCeti.Geometry.Manifold.Riemannian.Invariant
import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Slice.MomentMap
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Polar
import TauCeti.Topology.Algebra.ConstMulAction

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
in `sp(T_p M, σ_p)` and is complex linear for `J_p`, as is the linearized action of every element
of the isotropy algebra of `p`
(`exists_compatible_forall_mem_skewAdjointLieSubalgebra_isComplexLinearMap` in the namespace
`TauCeti.SmoothTwoForm.IsNondegenerate`), so it rotates the planes of a Darboux basis
and its quadratic Hamiltonian has indices of inertia twice the numbers of its negative and
positive rotation frequencies (`TauCeti.SymplecticForm.even_sigNeg_hamiltonianEndEquiv_symm`).

The critical submanifolds `M^{T_ξ}_d` can be refined by a symmetry. A closed subgroup `Z` of a
compact `G` commuting with `T_ξ` maps each `M^{T_ξ}_d` to itself
(`TauCeti.smul_mem_fixedPointsOfFinrank_iff`), and its orbits are compact. If it has finitely many
orbits on the critical set, each of them is therefore open in the part `M^{T_ξ}_d` containing it,
so it is again a Morse–Bott critical submanifold of `μ^ξ`
(`exists_isNondegenerateCriticalSubmanifold_orbit`). On a coadjoint orbit this applies to the
adjoint stabilizer of `ξ` and the orbits of critical points of a height.

Neither closedness of `σ`, equivariance of `μ` nor compactness of `M` is used.

## Main results

Unless otherwise noted, declarations are in the namespace `TauCeti.SmoothTwoForm.IsMomentMap`.

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
* `exists_isNondegenerateCriticalSubmanifold_orbit`: if a closed subgroup commuting with `T_ξ` has
  finitely many orbits on the critical set of `μ^ξ`, each of these orbits is a Morse–Bott critical
  submanifold of `μ^ξ`.
* `even_manifoldMorseIndex`, `even_manifoldMorseIndex_neg`: for a compact group acting by
  symplectomorphisms on a σ-compact manifold, the index and the coindex of `μ^ξ` at every critical
  point are even.
* `exists_compatible_forall_mem_skewAdjointLieSubalgebra_isComplexLinearMap`, in the namespace
  `TauCeti.SmoothTwoForm.IsNondegenerate`: for a compact group preserving `σ`, the linearized
  isotropy action at `p` lies in `sp(T_p M, σ_p)` and is complex linear for a complex structure
  compatible with `σ_p`.

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

namespace TauCeti.SmoothTwoForm.IsNondegenerate

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [CompactSpace G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [CompleteSpace E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [I'.Boundaryless] {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [T2Space M] [SigmaCompactSpace M] [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M}

/-- **The linearized isotropy action is complex linear for an invariant complex structure.** Let a
compact group act on a σ-compact manifold, preserving a nondegenerate two-form `σ`. Then `T_p M`
has a complex structure `J`, compatible with `σ_p`, such that for every `ξ` in the isotropy algebra
of `p` the linearized isotropy action `A_ξ` (`TauCeti.isotropyLinearization`) lies in
`sp(T_p M, σ_p)` and is complex linear for `J`. Here `J` is the value at `p` of an invariant
compatible almost complex structure. -/
theorem exists_compatible_forall_mem_skewAdjointLieSubalgebra_isComplexLinearMap
    (hσ : σ.IsNondegenerate)
    (hσG : ∀ (a : G) (x : M) (u v : TangentSpace I' x),
      σ.eval₂ (a • x) (mfderiv I' I' (a • ·) x u) (mfderiv I' I' (a • ·) x v) = σ.eval₂ x u v)
    (p : M) :
    ∃ J : AlmostComplexStructure (TangentSpace I' p), (hσ.symplecticFormAt p).Compatible J ∧
      ∀ ξ : (InfinitesimalAction.fundamental I G I' M).isotropy p,
        ((isotropyLinearization I' p ξ : E' →ₗ[ℝ] E') : Module.End ℝ (TangentSpace I' p)) ∈
            skewAdjointLieSubalgebra (hσ.symplecticFormAt p).toBilinForm ∧
          IsComplexLinearMap J J
            ((isotropyLinearization I' p ξ : E' →ₗ[ℝ] E') : Module.End ℝ (TangentSpace I' p)) := by
  obtain ⟨J, hJ, hJG⟩ := hσ.exists_compatible_mfderiv_smul_apply_of_compactSpace (IG := I) hσG
  -- Every element of `G`, in particular of the stabilizer of `p`, preserves `σ`.
  have hσp (g : G) (_ : g ∈ MulAction.stabilizer G p) : SmoothForm.mpullback (fun y : M ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ :=
    SmoothBundleForm.ext_eval₂ fun x u v ↦ by rw [SmoothForm.eval₂_mpullback]; exact hσG g x u v
  refine ⟨J.almostComplexStructureAt p, hJ.compatibleAt p, fun ξ ↦ ⟨?_, ?_⟩⟩
  · exact hσ.coe_isotropySkewAdjoint hσp ξ ▸ (hσ.isotropySkewAdjoint hσp ξ).property
  · refine (isComplexLinearMap_iff_apply _ _ _).2 fun v ↦ ?_
    rw [J.almostComplexStructureAt_apply, J.almostComplexStructureAt_apply]
    refine isotropyLinearization_apply_apply_eq_of_forall_mem_stabilizer ξ (J.toEndomorphism p)
      (fun g hg u ↦ ?_) v
    have := hJG g p u
    rwa [hg] at this

end TauCeti.SmoothTwoForm.IsNondegenerate

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
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : CompleteSpace E' := FiniteDimensional.completeSpace ℝ E'
  -- At the critical point `p`, `ξ` lies in the isotropy algebra and acts on `T_p M` by `A_ξ`.
  have hξ : ξ ∈ (InfinitesimalAction.fundamental I G I' M).isotropy p :=
    (h.mem_criticalPoints_iff_mem_isotropy (hσ.nondegenerate_bilinFormAt p) ξ).1 hp
  obtain ⟨J, hJ, hA⟩ :=
    hσ.exists_compatible_forall_mem_skewAdjointLieSubalgebra_isComplexLinearMap (I := I) hσG p
  refine ⟨J, ⟨_, (hA ⟨ξ, hξ⟩).1⟩, hJ, (hA ⟨ξ, hξ⟩).2, ?_⟩
  -- The Hessian is `σ_p(A v, v)`, twice the quadratic Hamiltonian `½ σ_p(A v, v)` of `A`.
  ext v
  have hH : criticalHessian I' (fun y ↦ μ y ξ) p v v =
      σ.eval₂ p (isotropyLinearization I' p ⟨ξ, hξ⟩ v) v :=
    h.criticalHessian_apply_eq_eval₂_isotropyLinearization hσ ⟨ξ, hξ⟩ v v
  rw [LinearMap.BilinMap.toQuadraticMap_apply, ContinuousLinearMap.toBilinForm_apply, hH,
    smul_apply, SymplecticForm.hamiltonianEndEquiv_symm_apply_apply,
    SymplecticForm.linearMomentMap_apply, hσ.symplecticFormAt_apply, smul_eq_mul,
    mul_div_cancel₀ _ two_ne_zero]
  rfl

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

/-- **Orbits of a centralizing subgroup on the critical set are Morse–Bott.** Let a compact Lie
group `G` act smoothly on a σ-compact manifold with a nondegenerate two-form `σ` and moment map
`μ`, let `ξ` be in the Lie algebra, and let `Z` be a closed subgroup commuting with the closure
`T_ξ` of `{exp (t ξ) | t ∈ ℝ}` and having finitely many orbits on the critical set of `μ^ξ`. Let `p`
be a critical point, `d` the dimension of the space of tangent vectors at `p` fixed by `T_ξ`, and
`L` a subspace of the model of dimension `d`. Then `M^{T_ξ}_d` is a smooth manifold modelled on `L`
whose inclusion into `M` is a smooth embedding, the `Z`-orbit of `p` is an open subset `U` of
`M^{T_ξ}_d`, and the inclusion of `U` into `M` is a nondegenerate critical submanifold of `μ^ξ`,
whose tangent space at each point is the space of tangent vectors fixed by `T_ξ`. -/
theorem exists_isNondegenerateCriticalSubmanifold_orbit [CompactSpace G] [SigmaCompactSpace M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) μ)
    (hσ : σ.IsNondegenerate) {Z : Subgroup G} (hZc : IsClosed (Z : Set G))
    (hZ : Z ≤ Subgroup.centralizer (Lie.closedOneParameterSubgroup ξ : Set G))
    (hfin : (MulAction.orbit Z '' criticalPoints 𝓘(ℝ, E') fun y ↦ μ y ξ).Finite) {p : M}
    (hp : p ∈ criticalPoints 𝓘(ℝ, E') fun y ↦ μ y ξ) {d : ℕ}
    (hd : Module.finrank ℝ
      (fixedTangentSubspace 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) p) = d)
    {L : Submodule ℝ E'} (hL : Module.finrank ℝ L = d) :
    ∃ (_ : ChartedSpace L
        (fixedPointsOfFinrank 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) M d))
      (_ : IsManifold 𝓘(ℝ, L) ∞
        (fixedPointsOfFinrank 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) M d))
      (hi : IsSmoothEmbedding 𝓘(ℝ, L) 𝓘(ℝ, E') ∞
        (Subtype.val : fixedPointsOfFinrank 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) M d → M))
      (U : TopologicalSpace.Opens
        (fixedPointsOfFinrank 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) M d)),
      range (Subtype.val ∘ (Subtype.val : U → _)) = MulAction.orbit Z p ∧
        SmoothEmbedding.IsNondegenerateCriticalSubmanifold
          ((SmoothEmbedding.ofIsSmoothEmbedding _ hi).compLocalDiffeomorph (Subtype.val : U → _)
            isLocalDiffeomorph_subtype_val Topology.IsEmbedding.subtypeVal)
          (fun y ↦ μ y ξ) ∧
        ∀ y : U, LinearMap.range
            (mfderiv 𝓘(ℝ, L) 𝓘(ℝ, E') (Subtype.val ∘ (Subtype.val : U → _)) y).toLinearMap =
          fixedTangentSubspace 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ)
            ((Subtype.val ∘ (Subtype.val : U → _)) y) := by
  obtain ⟨C, hman, hi, hMB, hrange⟩ :=
    h.exists_isNondegenerateCriticalSubmanifold_fixedPointsOfFinrank_of_compactSpace hσ (ξ := ξ) hL
  let := C
  have := hman
  have hcrit := h.criticalPoints_eq_fixedPoints hσ ξ
  have : ContMDiffConstSMul 𝓘(ℝ, E') ∞ G M := ⟨ContMDiffSMul.contMDiff_const_smul (I := I)⟩
  have : ContinuousSMul G M := ContMDiffSMul.continuousSMul (I := I) (I' := 𝓘(ℝ, E')) ∞
  have : CompactSpace Z := isCompact_iff_compactSpace.mp hZc.isCompact
  -- The `Z`-orbits are compact, hence closed, and `Z` preserves `M^{T_ξ}_d`.
  have hclosed (q : M) : IsClosed (MulAction.orbit Z q) :=
    (isCompact_range (continuous_subtypeVal.smul continuous_const)).isClosed
  have hsub : MulAction.orbit Z p ⊆
      fixedPointsOfFinrank 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) M d := by
    rintro _ ⟨k, rfl⟩
    exact (smul_mem_fixedPointsOfFinrank_iff (n := ∞) (by simp) (hZ k.property)).2
      (mem_fixedPointsOfFinrank.2 ⟨hcrit ▸ hp, hd⟩)
  -- Finitely many closed `Z`-orbits meet `M^{T_ξ}_d`, so each of them is open in it.
  have hU := (isClopen_preimage_val_orbit_of_finite (hfin.subset <| image_mono <|
    hcrit ▸ fixedPointsOfFinrank_subset_fixedPoints (I := 𝓘(ℝ, E')) d) (fun q _ ↦ hclosed q)
      p).isOpen
  refine ⟨C, hman, hi, ⟨_, hU⟩, ?_, hMB.compLocalDiffeomorph (by simp) _ _, fun y ↦ ?_⟩
  · rw [range_comp, Subtype.range_coe, TopologicalSpace.Opens.coe_mk,
      Subtype.image_preimage_coe, inter_eq_right.2 hsub]
  · rw [Manifold.range_mfderiv_comp_subtype_val, hrange, Function.comp_apply]

end Model

end TauCeti.SmoothTwoForm.IsMomentMap
