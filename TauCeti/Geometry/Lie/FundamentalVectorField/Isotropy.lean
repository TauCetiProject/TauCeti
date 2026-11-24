/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Subrepresentation
public import TauCeti.Geometry.Lie.Adjoint.Exponential.Basic
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Lie.FundamentalVectorField.Linearization

import TauCeti.RepresentationTheory.Subrepresentation

/-!
# The linearized action of the isotropy algebra

Let a Lie group `G` act smoothly on a boundaryless manifold `M`, and let `𝔥 = 𝔤_p` be the isotropy
algebra of a point `p`, the elements `ξ` of the Lie algebra whose fundamental vector field `ξ_M`
vanishes at `p` (`TauCeti.InfinitesimalAction.isotropy`). For `ξ ∈ 𝔥` every `exp (t ξ)` fixes `p`,
and the differentials `d(exp (t ξ))_p` form a one-parameter group of operators on `T_p M`. Its
generator `A_ξ`, the derivative at `t = 0`, is the linearization of `ξ_M` at its zero `p`
(`TauCeti.hasDerivAt_mfderiv_mulInvariantExp_smul_smul`). This file packages these generators as
one linear map

`A : 𝔥 → End (T_p M)`, `ξ ↦ A_ξ`

(`TauCeti.isotropyLinearization`), the infinitesimal isotropy action of `𝔥` on `T_p M`. It is
defined as the derivative at the chart image of `p` of the coordinate expression of `ξ_M` in the
preferred chart at `p`. This expression is linear in `ξ` and differentiable, because `ξ_M` is a
smooth vector field depending linearly on `ξ`; so `A` is linear. By the existing linearization
theorem it is also the derivative of `t ↦ d(exp (t ξ))_p`
(`TauCeti.hasDerivAt_mfderiv_mulInvariantExp_smul_smul_isotropyLinearization`), which makes it
intrinsic.

Two properties of `A` are inherited from the group `t ↦ d(exp (t ξ))_p`:

* **Invariant closed subspaces.** If every `d(exp (t ξ))_p` maps a vector `u` into a closed subspace
  `S`, then `A_ξ u ∈ S`, since `A_ξ u` is a limit of difference quotients in `S`
  (`TauCeti.isotropyLinearization_apply_mem_of_forall_mem`).
* **Equivariance.** For `g` in the stabilizer of `p`, `g exp (t ξ) g⁻¹ = exp (t Ad_g ξ)`
  (`TauCeti.Lie.conj_mulInvariantExp`). Differentiating the conjugated one-parameter group gives
  `dg_p ∘ A_ξ = A_η ∘ dg_p` for every `η` in `𝔥` with `η = Ad_g ξ`
  (`TauCeti.tangentRepresentation_comp_isotropyLinearization`). The element `η` is supplied by
  the caller.

These are the infinitesimal data of the slice representation in the local normal form of a
Hamiltonian action, where `𝔥` acts on the symplectic slice through `A`.

The stabilizer `G_p` maps `𝔥` into itself under the adjoint action
(`TauCeti.adjointContinuousLinearMap_mem_isotropy_of_mem_stabilizer`). The file also records `𝔥`
as a subrepresentation of the adjoint representation of any subgroup `K` of `G_p`
(`TauCeti.isotropySubrepresentation`), which is the form in which `Ad(K)`-invariant complements of
`𝔥` are chosen.

## Main definitions

* `TauCeti.isotropyLinearization I' p`: the linear map `ξ ↦ A_ξ` from the isotropy algebra of `p`
  to the operators on `T_p M`.
* `TauCeti.isotropySubrepresentation`: the isotropy algebra `𝔤_p`, as a subrepresentation of the
  adjoint representation of a subgroup of the stabilizer `G_p`.

## Main results

* `TauCeti.mulInvariantExp_smul_mem_stabilizer`: every `exp (t ξ)` fixes `p`.
* `TauCeti.hasDerivAt_mfderiv_mulInvariantExp_smul_smul_isotropyLinearization`: `A_ξ` is the
  derivative at `t = 0` of `t ↦ d(exp (t ξ))_p`.
* `TauCeti.isotropyLinearization_apply_mem_of_forall_mem`: `A_ξ` preserves every closed subspace
  preserved by every `d(exp (t ξ))_p`.
* `TauCeti.tangentRepresentation_comp_isotropyLinearization`: `dg_p ∘ A_ξ = A_η ∘ dg_p` for `g` in
  the stabilizer of `p` and `η` in the isotropy algebra with `η = Ad_g ξ`.
* `TauCeti.toSubmodule_isotropySubrepresentation` and
  `TauCeti.mem_isotropySubrepresentation_iff`: the carrier of `TauCeti.isotropySubrepresentation`
  is `𝔤_p`.

## References

* V. Guillemin, S. Sternberg, *A normal form for the moment map*, in *Differential Geometric
  Methods in Mathematical Physics* (Jerusalem, 1982), Math. Phys. Stud. 6, Reidel, 1984,
  161–175.
* J.-P. Ortega, T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in Mathematics
  222, Birkhäuser, 2004, Section 7.1.
-/

public noncomputable section

open Filter Function Set Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness ℝ 3) G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M] {p : M}

omit [CompleteSpace E] in
/-- The coordinate expression of a fundamental vector field in the preferred chart at `p` is
differentiable at the chart image of `p`. -/
private theorem differentiableAt_mpullbackWithin_fundamentalVectorField
    (ξ : GroupLieAlgebra I G) :
    DifferentiableAt ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E') I' (extChartAt I' p).symm
      (fundamentalVectorField I' ξ) (range I')) (extChartAt I' p p) := by
  have : IsManifold I' 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I' 1 M := IsManifold.of_le (n := ∞) (by simp)
  have hV : ContMDiff I' I'.tangent 1
      (fun x : M ↦ (⟨x, fundamentalVectorField I' ξ x⟩ : TangentBundle I' M)) :=
    contMDiff_fundamentalVectorField (m := 1) (n := ∞) (by simp) ξ
  have h := VectorField.contMDiffWithinAt_mpullbackWithin_extChartAt_symm (n := 2)
    (hV.contMDiffAt (x := p)).contMDiffWithinAt (s := univ) uniqueMDiffOn_univ (mem_univ p)
    (by norm_num)
  rw [preimage_univ, inter_univ] at h
  exact ((contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.1 h).contDiffAt
    ((isOpen_extChartAt_target p).mem_nhds (mem_extChartAt_target p))).differentiableAt
    one_ne_zero

omit [I'.Boundaryless] in
/-- The fundamental vector field of an element of the isotropy algebra of `p` vanishes at `p`. -/
private theorem fundamentalVectorField_isotropy_eq_zero
    (ξ : (InfinitesimalAction.fundamental I G I' M).isotropy p) :
    fundamentalVectorField I' (ξ : GroupLieAlgebra I G) p = 0 := by
  simpa using (InfinitesimalAction.mem_isotropy_iff _ p).1 ξ.property

variable (I') in
/-- The **linearized isotropy action** of the isotropy algebra `𝔥 = 𝔤_p` on `T_p M`: an element
`ξ ∈ 𝔥` acts by the linearization `A_ξ` of its fundamental vector field `ξ_M` at the zero `p`,
the derivative at the chart image of `p` of the coordinate expression of `ξ_M` in the preferred
chart at `p`. It is the derivative at `t = 0` of the differentials `d(exp (t ξ))_p`
(`TauCeti.hasDerivAt_mfderiv_mulInvariantExp_smul_smul_isotropyLinearization`). -/
def isotropyLinearization (p : M) :
    (InfinitesimalAction.fundamental I G I' M).isotropy p →ₗ[ℝ] E' →L[ℝ] E' where
  toFun ξ := fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E') I' (extChartAt I' p).symm
    (fundamentalVectorField I' (ξ : GroupLieAlgebra I G)) (range I')) (extChartAt I' p p)
  map_add' ξ η := by
    rw [AddMemClass.coe_add, fundamentalVectorField_add, VectorField.mpullbackWithin_add]
    exact fderiv_add (differentiableAt_mpullbackWithin_fundamentalVectorField _)
      (differentiableAt_mpullbackWithin_fundamentalVectorField _)
  map_smul' c ξ := by
    rw [SetLike.val_smul, fundamentalVectorField_smul,
      VectorField.mpullbackWithin_const_smul, RingHom.id_apply]
    exact fderiv_const_smul (differentiableAt_mpullbackWithin_fundamentalVectorField _) c

theorem isotropyLinearization_apply (ξ : (InfinitesimalAction.fundamental I G I' M).isotropy p) :
    isotropyLinearization I' p ξ =
      fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E') I' (extChartAt I' p).symm
        (fundamentalVectorField I' (ξ : GroupLieAlgebra I G)) (range I')) (extChartAt I' p p) := by
  rw [isotropyLinearization, LinearMap.coe_mk, AddHom.coe_mk]

variable [T2Space G] [BoundarylessManifold I G] [T2Space M]

/-- For `ξ` in the isotropy algebra of `p`, every `exp (t ξ)` fixes `p`. -/
theorem mulInvariantExp_smul_mem_stabilizer
    (ξ : (InfinitesimalAction.fundamental I G I' M).isotropy p) (t : ℝ) :
    mulInvariantExp (t • (ξ : GroupLieAlgebra I G)) ∈ MulAction.stabilizer G p := by
  have : IsManifold I' 1 M := IsManifold.of_le (n := ∞) (by simp)
  have : ContMDiffSMul I I' 2 G M := ContMDiffSMul.of_le (M := M) (m := ∞) (by simp)
  exact (mulInvariantExp_smul_smul_eq_iff (I' := I')).2
    (fundamentalVectorField_isotropy_eq_zero ξ) t

/-- **The linearized isotropy action generates the isotropy representation.** For `ξ` in the
isotropy algebra of `p`, the differentials `d(exp (t ξ))_p`, operators on `T_p M`, have derivative
`A_ξ` at `t = 0`. -/
theorem hasDerivAt_mfderiv_mulInvariantExp_smul_smul_isotropyLinearization
    (ξ : (InfinitesimalAction.fundamental I G I' M).isotropy p) :
    HasDerivAt (fun t : ℝ ↦ (mfderiv I' I'
        (fun y : M ↦ mulInvariantExp (t • (ξ : GroupLieAlgebra I G)) • y) p : E' →L[ℝ] E'))
      (isotropyLinearization I' p ξ) 0 := by
  rw [isotropyLinearization_apply]
  exact hasDerivAt_mfderiv_mulInvariantExp_smul_smul (fundamentalVectorField_isotropy_eq_zero ξ)

/-- The curves `t ↦ d(exp (t ξ))_p u` have velocity `A_ξ u` at `t = 0`. -/
theorem hasDerivAt_mfderiv_mulInvariantExp_smul_smul_apply
    (ξ : (InfinitesimalAction.fundamental I G I' M).isotropy p) (u : TangentSpace I' p) :
    HasDerivAt (F := E') (fun t : ℝ ↦ (mfderiv I' I'
        (fun y : M ↦ mulInvariantExp (t • (ξ : GroupLieAlgebra I G)) • y) p : E' →L[ℝ] E') u)
      (isotropyLinearization I' p ξ u) 0 :=
  (ContinuousLinearMap.apply ℝ (E' := E') E' u).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_mfderiv_mulInvariantExp_smul_smul_isotropyLinearization ξ)

/-- **The linearized isotropy action preserves invariant closed subspaces.** If every
`d(exp (t ξ))_p` maps the tangent vector `u` into a closed subspace `S` of `T_p M`, then so does
`A_ξ`: `A_ξ u` is the limit of the difference quotients `t⁻¹ (d(exp (t ξ))_p u - u)`, which lie
in `S`. -/
theorem isotropyLinearization_apply_mem_of_forall_mem
    (ξ : (InfinitesimalAction.fundamental I G I' M).isotropy p) {S : Submodule ℝ E'}
    (hS : IsClosed (S : Set E')) {u : TangentSpace I' p}
    (hu : ∀ t : ℝ, (mfderiv I' I'
      (fun y : M ↦ mulInvariantExp (t • (ξ : GroupLieAlgebra I G)) • y) p : E' →L[ℝ] E') u ∈ S) :
    isotropyLinearization I' p ξ u ∈ S := by
  set f : ℝ → E' := fun t ↦ (mfderiv I' I'
    (fun y : M ↦ mulInvariantExp (t • (ξ : GroupLieAlgebra I G)) • y) p : E' →L[ℝ] E') u
  have hderiv : HasDerivAt f (isotropyLinearization I' p ξ u) 0 :=
    hasDerivAt_mfderiv_mulInvariantExp_smul_smul_apply ξ u
  refine hS.mem_of_tendsto hderiv.tendsto_slope (Eventually.of_forall fun t ↦ ?_)
  rw [slope_def_module]
  exact S.smul_mem _ (S.sub_mem (hu t) (hu 0))

/-- **Equivariance of the linearized isotropy action.** Let `g` fix `p`, and let `η = Ad_g ξ` for
`ξ` in the isotropy algebra of `p`. Then `dg_p ∘ A_ξ = A_η ∘ dg_p`. Indeed
`g exp (t ξ) g⁻¹ = exp (t η)`, so `d(exp (t η))_p = dg_p ∘ d(exp (t ξ))_p ∘ dg_p⁻¹`, and
differentiating at `t = 0` gives `A_η = dg_p ∘ A_ξ ∘ dg_p⁻¹`. -/
theorem tangentRepresentation_comp_isotropyLinearization
    (hd : ∀ g ∈ MulAction.stabilizer G p, MDifferentiableAt I' I' (fun y : M ↦ g • y) p)
    (g : MulAction.stabilizer G p) (ξ η : (InfinitesimalAction.fundamental I G I' M).isotropy p)
    (hη : (η : GroupLieAlgebra I G) = Lie.tangentAd (I := I) (g : G) ξ) :
    (tangentRepresentation hd g).comp (isotropyLinearization I' p ξ) =
      (isotropyLinearization I' p η).comp (tangentRepresentation hd g) := by
  have : LieGroup I 3 G := by simpa using (inferInstance : LieGroup I (minSmoothness ℝ 3) G)
  -- `exp (t η) g = g exp (t ξ)` in the stabilizer.
  have hcomm (t : ℝ) : (⟨_, mulInvariantExp_smul_mem_stabilizer η t⟩ : MulAction.stabilizer G p) *
      g = g * ⟨_, mulInvariantExp_smul_mem_stabilizer ξ t⟩ := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, hη, ← map_smul]
    rw [← Lie.conj_mulInvariantExp (I := I) (g : G) (t • (ξ : GroupLieAlgebra I G)),
      inv_mul_cancel_right]
  set Tg : E' →L[ℝ] E' := mfderiv I' I' (fun y : M ↦ (g : G) • y) p
  -- Both sides are velocities at `t = 0` of the curve `t ↦ d(exp (t η))_p (dg_p u)`.
  have hcurve (u : TangentSpace I' p) (t : ℝ) : (mfderiv I' I'
      (fun y : M ↦ mulInvariantExp (t • (η : GroupLieAlgebra I G)) • y) p : E' →L[ℝ] E')
        (Tg u) = Tg ((mfderiv I' I'
          (fun y : M ↦ mulInvariantExp (t • (ξ : GroupLieAlgebra I G)) • y) p : E' →L[ℝ] E')
            u) := by
    have h := congrArg (fun k ↦ tangentRepresentation hd k u) (hcomm t)
    simp only [map_mul, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply] at h
    rw [tangentRepresentation_apply, tangentRepresentation_apply,
      tangentRepresentation_apply] at h
    exact h
  rw [tangentRepresentation_apply]
  ext u
  have hη' := hasDerivAt_mfderiv_mulInvariantExp_smul_smul_apply η (Tg u)
  have hξ' := Tg.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_mfderiv_mulInvariantExp_smul_smul_apply ξ u)
  exact (hη'.unique (hξ'.congr_of_eventuallyEq (Eventually.of_forall (hcurve u)))).symm

end TauCeti

/-! ### The isotropy algebra as a representation of the stabilizer -/

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness ℝ 3) G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]

attribute [local instance] lieGroupOne

variable (I I') in
/-- The isotropy algebra `𝔤_x` of the fundamental infinitesimal action, as a subrepresentation of
the adjoint representation of a subgroup `K` of the stabilizer `G_x`. -/
def isotropySubrepresentation (x : M) {K : Subgroup G} (hK : K ≤ MulAction.stabilizer G x) :
    Subrepresentation ((Lie.adjointRepresentation ℝ I G).comp K.subtype) where
  toSubmodule := ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule
  apply_mem_toSubmodule g _ hξ := by
    simpa only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      Lie.adjointRepresentation_apply, LieSubalgebra.mem_toSubmodule] using
      adjointContinuousLinearMap_mem_isotropy_of_mem_stabilizer (hK g.property) hξ

/-- The underlying submodule of `TauCeti.isotropySubrepresentation` is the isotropy algebra. -/
@[simp]
theorem toSubmodule_isotropySubrepresentation (x : M) {K : Subgroup G}
    (hK : K ≤ MulAction.stabilizer G x) :
    (isotropySubrepresentation I I' x hK).toSubmodule =
      ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule :=
  -- `(rfl)`, not `rfl`: the body of `isotropySubrepresentation` is not `@[expose]`d, so this must
  -- not be inferred `@[defeq]`.
  (rfl)

/-- Membership in `TauCeti.isotropySubrepresentation` is membership in the isotropy algebra. -/
@[simp]
theorem mem_isotropySubrepresentation_iff {x : M} {K : Subgroup G}
    {hK : K ≤ MulAction.stabilizer G x} {ξ : GroupLieAlgebra I G} :
    ξ ∈ isotropySubrepresentation I I' x hK ↔
      ξ ∈ (InfinitesimalAction.fundamental I G I' M).isotropy x := by
  rw [← Subrepresentation.mem_toSubmodule, toSubmodule_isotropySubrepresentation,
    LieSubalgebra.mem_toSubmodule]

end TauCeti
