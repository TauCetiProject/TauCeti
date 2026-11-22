/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField.Isotropy
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Slice
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Analysis.Calculus.Bilinear

/-!
# The isotropy algebra on the symplectic slice and the slice moment map

Let a Lie group `G` act smoothly on a finite-dimensional boundaryless manifold `M` with a
nondegenerate two-form `σ`, and let the stabilizer `H = G_p` of a point `p` preserve `σ`. Write
`W = 𝔤 · p` for the orbit tangent space, `W^σ` for its `σ_p`-orthogonal and

`V = W^σ ⧸ (W ∩ W^σ)`

for the symplectic slice (`TauCeti.SmoothTwoForm.IsNondegenerate.SymplecticSlice`), with its reduced
symplectic form `ω_V`. The group `H` acts on `V` by linear symplectomorphisms
(`TauCeti.SmoothTwoForm.IsNondegenerate.symplecticSliceRepresentation`). This file constructs the
corresponding action of the isotropy algebra `𝔥 = 𝔤_p` and its quadratic moment map

`μ_V : V → 𝔥*`, `μ_V(v)(ξ) = ½ ω_V(ξ v, v)`,

the moment map of the slice in the local normal form `G ×_H (𝔪* × V)` of a Hamiltonian action
near the orbit of `p`.

An element `ξ ∈ 𝔥` acts on `T_p M` by the generator `A_ξ` of the one-parameter group
`t ↦ d(exp (t ξ))_p` (`TauCeti.isotropyLinearization`). Each `d(exp (t ξ))_p` preserves `σ_p` and
`W^σ`, so differentiating at `t = 0`:

* `A_ξ` is skew-adjoint for `σ_p`, `σ_p(A_ξ u, v) = -σ_p(u, A_ξ v)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.symplecticFormAt_isotropyLinearization_apply`);
* `A_ξ` preserves `W^σ`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isotropyLinearization_apply_mem_orthogonal`).

Hence `ξ ↦ A_ξ` descends to a linear map `𝔥 → sp(V, ω_V)`, `ξ ↦ ([u] ↦ [A_ξ u])`
(`TauCeti.SmoothTwoForm.IsNondegenerate.symplecticSliceIsotropyAction`, through
`TauCeti.SymplecticForm.reducedSpaceSkewAdjoint`), and `μ_V` is the linear symplectic moment map
`TauCeti.SymplecticForm.linearMomentMap` composed with it
(`TauCeti.SmoothTwoForm.IsNondegenerate.symplecticSliceMomentMap`). It has the two properties
of a moment map:

* **The moment equation** `dμ_V^ξ = ι_(ξ v) ω_V`. Since `ξ` acts skew-adjointly, `μ_V^ξ` is a
  quadratic form whose polarization is `ω_V(ξ v, w)`
  (`TauCeti.SymplecticForm.linearMomentMap_add`), so the derivative of `μ_V^ξ` at `v` in the
  direction `w` is `ω_V(ξ v, w)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_symplecticSliceMomentMap_add_smul`). This is
  stated along lines, as `V` carries no preferred norm.
* **`H`-equivariance.** Let `h ∈ H` and `ξ, η ∈ 𝔥` with `η = Ad_h ξ`. Then
  `dh_p ∘ A_ξ = A_η ∘ dh_p` (`TauCeti.tangentRepresentation_comp_isotropyLinearization`), so `h`
  intertwines the actions of `ξ` and `η` on `V`, and as `h` preserves `ω_V`,
  `μ_V(h v)(η) = μ_V(v)(ξ)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.symplecticSliceMomentMap_symplecticSliceRepresentation`).
  The element `η` of `𝔥` is supplied by the caller; this file does not prove that `Ad_h`
  preserves `𝔥`, nor define a coadjoint action of `H` on `𝔥*`.

No moment map on `M`, no closedness of `σ` and no compactness of `H` is used.

## Main definitions

* `TauCeti.SmoothTwoForm.IsNondegenerate.symplecticSliceIsotropyAction hσ hσG`: the linear map
  `𝔥 → sp(V, ω_V)`, `ξ ↦ ([u] ↦ [A_ξ u])`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.symplecticSliceMomentMap hσ hσG`: the slice moment map
  `μ_V : V → 𝔥*`, `μ_V(v)(ξ) = ½ ω_V(ξ v, v)`.

## References

* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985), 227–251.
* V. Guillemin, S. Sternberg, *A normal form for the moment map*, in *Differential Geometric
  Methods in Mathematical Physics* (Jerusalem, 1982), Math. Phys. Stud. 6, Reidel, 1984,
  161–175.
* J.-P. Ortega, T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in Mathematics
  222, Birkhäuser, 2004, Section 7.1 (the symplectic slice and its moment map).
-/

public noncomputable section

open MulAction Filter
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness ℝ 3) G]
  [T2Space G] [BoundarylessManifold I G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {p : M} (hσ : σ.IsNondegenerate)
  (hσG : ∀ g ∈ stabilizer G p, SmoothForm.mpullback (fun y : M ↦ g • y)
    (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)

omit [CompleteSpace E] [LieGroup I (minSmoothness ℝ 3) G] [T2Space G] [BoundarylessManifold I G]
  [FiniteDimensional ℝ E'] [I'.Boundaryless] [IsManifold I' ∞ M] [T2Space M] in
include I in
variable (I G I' p) in
/-- Every element of the stabilizer of `p` acts differentiably at `p`, the differentiability
hypothesis of `TauCeti.tangentRepresentation`. -/
private theorem mdifferentiableAt_smul_of_mem_stabilizer :
    ∀ g ∈ stabilizer G p, MDifferentiableAt I' I' (fun y : M ↦ g • y) p :=
  fun g _ ↦ ContMDiffSMul.mdifferentiable_const_smul (I := I) (n := ∞) (by simp) g p

include hσG

/-! ### The isotropy algebra on `(T_p M, σ_p)` -/

/-- **The isotropy algebra acts skew-adjointly.** If the stabilizer of `p` preserves a
nondegenerate two-form `σ`, then for `ξ` in the isotropy algebra of `p` the generator `A_ξ` of
`t ↦ d(exp (t ξ))_p` is skew-adjoint for `σ_p`: `σ_p(A_ξ u, v) = -σ_p(u, A_ξ v)`. This is the
derivative at `t = 0` of `σ_p(d(exp (t ξ))_p u, d(exp (t ξ))_p v) = σ_p(u, v)`. -/
theorem symplecticFormAt_isotropyLinearization_apply
    (ξ : (InfinitesimalAction.fundamental I G I' M).isotropy p) (u v : TangentSpace I' p) :
    hσ.symplecticFormAt p (isotropyLinearization I' p ξ u) v =
      -hσ.symplecticFormAt p u (isotropyLinearization I' p ξ v) := by
  have : ContMDiffConstSMul I' ∞ G M := ⟨ContMDiffSMul.contMDiff_const_smul (I := I)⟩
  have hd := mdifferentiableAt_smul_of_mem_stabilizer I G I' p
  -- The computation takes place in the model space `E'`.
  let B : LinearMap.BilinForm ℝ E' := (hσ.symplecticFormAt p).toBilinForm
  let A : E' →L[ℝ] E' := isotropyLinearization I' p ξ
  let D : ℝ → E' →L[ℝ] E' := fun t ↦
    mfderiv I' I' (fun y : M ↦ mulInvariantExp (t • (ξ : GroupLieAlgebra I G)) • y) p
  let u' : E' := u
  let v' : E' := v
  -- `t ↦ σ_p(d(exp (t ξ))_p u, d(exp (t ξ))_p v)` is constant.
  have hconst (t : ℝ) : B.toContinuousBilinearMap (D t u') (D t v') = B u' v' := by
    have h := hσ.symplecticFormAt_tangentRepresentation hσG hd
      ⟨_, mulInvariantExp_smul_mem_stabilizer ξ t⟩ u v
    rw [tangentRepresentation_apply] at h
    exact h
  -- At `t = 0` the differential is the identity.
  have hD0 (w : E') : D 0 w = w := by
    have h1 : (⟨_, mulInvariantExp_smul_mem_stabilizer ξ 0⟩ : stabilizer G p) = 1 :=
      Subtype.ext (by simp [mulInvariantExp_zero])
    have h := congrArg (fun g ↦ tangentRepresentation hd g w) h1
    simp only [map_one] at h
    rw [tangentRepresentation_apply] at h
    exact h
  have h0 : B.toContinuousBilinearMap (A u') (D 0 v') +
      B.toContinuousBilinearMap (D 0 u') (A v') = 0 :=
    B.toContinuousBilinearMap.apply_add_apply_eq_zero_of_const
      (hasDerivAt_mfderiv_mulInvariantExp_smul_smul_apply ξ u')
      (hasDerivAt_mfderiv_mulInvariantExp_smul_smul_apply ξ v') hconst
  rw [hD0, hD0, LinearMap.toContinuousBilinearMap_apply,
    LinearMap.toContinuousBilinearMap_apply] at h0
  exact eq_neg_of_add_eq_zero_left h0

/-- **The isotropy algebra preserves the symplectic complement of the orbit.** If the stabilizer of
`p` preserves a nondegenerate two-form `σ`, then for `ξ` in the isotropy algebra of `p` the
generator `A_ξ` of `t ↦ d(exp (t ξ))_p` maps the `σ_p`-orthogonal `W^σ` of the orbit tangent space
into itself. -/
theorem isotropyLinearization_apply_mem_orthogonal
    (ξ : (InfinitesimalAction.fundamental I G I' M).isotropy p) {u : TangentSpace I' p}
    (hu : u ∈ (hσ.symplecticFormAt p).orthogonal
      ((InfinitesimalAction.fundamental I G I' M).orbitTangent p)) :
    isotropyLinearization I' p ξ u ∈ (hσ.symplecticFormAt p).orthogonal
      ((InfinitesimalAction.fundamental I G I' M).orbitTangent p) := by
  have hd := mdifferentiableAt_smul_of_mem_stabilizer I G I' p
  let S : Submodule ℝ E' := (hσ.symplecticFormAt p).orthogonal
    ((InfinitesimalAction.fundamental I G I' M).orbitTangent p)
  refine isotropyLinearization_apply_mem_of_forall_mem (S := S) ξ
    (Submodule.isClosed_of_finiteDimensional S) fun t ↦ ?_
  have h := hσ.tangentRepresentation_mem_orthogonal_orbitTangent hσG hd
    ⟨_, mulInvariantExp_smul_mem_stabilizer ξ t⟩ hu
  rw [tangentRepresentation_apply] at h
  exact h

/-- The isotropy algebra of `p` acting on `T_p M` by the skew-adjoint endomorphisms `A_ξ` of
`σ_p`. -/
private def isotropySkewAdjoint :
    (InfinitesimalAction.fundamental I G I' M).isotropy p →ₗ[ℝ]
      skewAdjointLieSubalgebra (hσ.symplecticFormAt p).toBilinForm :=
  LinearMap.codRestrict (hσ.symplecticFormAt p).toBilinForm.skewAdjointSubmodule
    ((ContinuousLinearMap.coeLM ℝ : (E' →L[ℝ] E') →ₗ[ℝ] E' →ₗ[ℝ] E').comp
      (isotropyLinearization I' p)) fun ξ ↦
      (LinearMap.mem_skewAdjointSubmodule _).2 fun u v ↦
        (hσ.symplecticFormAt_isotropyLinearization_apply hσG ξ u v).trans (map_neg _ _).symm

private theorem coe_isotropySkewAdjoint_apply
    (ξ : (InfinitesimalAction.fundamental I G I' M).isotropy p) (u : TangentSpace I' p) :
    (isotropySkewAdjoint hσ hσG ξ : Module.End ℝ (TangentSpace I' p)) u =
      isotropyLinearization I' p ξ u :=
  LinearMap.congr_fun (LinearMap.codRestrict_apply _ _ ξ) u

/-! ### The isotropy algebra on the symplectic slice -/

/-- **The isotropy algebra acts on the symplectic slice.** If the stabilizer of `p` preserves a
nondegenerate two-form `σ`, the isotropy algebra `𝔥` of `p` acts on the symplectic slice
`V = W^σ ⧸ (W ∩ W^σ)` by skew-adjoint endomorphisms of its reduced form, `ξ ↦ ([u] ↦ [A_ξ u])`,
where `A_ξ` is the generator of `t ↦ d(exp (t ξ))_p`. It is the infinitesimal counterpart of
`TauCeti.SmoothTwoForm.IsNondegenerate.symplecticSliceRepresentation`. -/
def symplecticSliceIsotropyAction :
    (InfinitesimalAction.fundamental I G I' M).isotropy p →ₗ[ℝ]
      skewAdjointLieSubalgebra ((hσ.symplecticFormAt p).reduction
        ((hσ.symplecticFormAt p).orthogonal
          ((InfinitesimalAction.fundamental I G I' M).orbitTangent p))).toBilinForm :=
  (hσ.symplecticFormAt p).reducedSpaceSkewAdjoint (isotropySkewAdjoint hσ hσG) _ fun ξ u hu ↦ by
    rw [coe_isotropySkewAdjoint_apply]
    exact hσ.isotropyLinearization_apply_mem_orthogonal hσG ξ hu

/-- The isotropy algebra acts on the symplectic slice by `[u] ↦ [A_ξ u]`. -/
@[simp]
theorem symplecticSliceIsotropyAction_mk
    (ξ : (InfinitesimalAction.fundamental I G I' M).isotropy p)
    (u : (hσ.symplecticFormAt p).orthogonal
      ((InfinitesimalAction.fundamental I G I' M).orbitTangent p)) :
    (hσ.symplecticSliceIsotropyAction hσG ξ :
        Module.End ℝ (hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) p))
        (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk ⟨isotropyLinearization I' p ξ (u : TangentSpace I' p),
        hσ.isotropyLinearization_apply_mem_orthogonal hσG ξ u.property⟩ := by
  rw [symplecticSliceIsotropyAction, SymplecticForm.reducedSpaceSkewAdjoint_mk]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (coe_isotropySkewAdjoint_apply hσ hσG ξ u))

/-- **Equivariance of the slice action.** For `g` in the stabilizer of `p` and `η = Ad_g ξ`, the
action of `g` on the symplectic slice intertwines the actions of `ξ` and `η`:
`g (ξ v) = η (g v)`. -/
theorem symplecticSliceRepresentation_symplecticSliceIsotropyAction (g : stabilizer G p)
    (ξ η : (InfinitesimalAction.fundamental I G I' M).isotropy p)
    (hη : (η : GroupLieAlgebra I G) = Lie.tangentAd (I := I) (g : G) ξ)
    (v : hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) p) :
    hσ.symplecticSliceRepresentation hσG g
        ((hσ.symplecticSliceIsotropyAction hσG ξ :
          Module.End ℝ (hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) p)) v) =
      (hσ.symplecticSliceIsotropyAction hσG η :
          Module.End ℝ (hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) p))
        (hσ.symplecticSliceRepresentation hσG g v) := by
  induction v using Submodule.Quotient.induction_on with
  | H u =>
    rw [symplecticSliceIsotropyAction_mk, symplecticSliceRepresentation_mk,
      symplecticSliceRepresentation_mk, symplecticSliceIsotropyAction_mk]
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    exact DFunLike.congr_fun (tangentRepresentation_comp_isotropyLinearization _ g ξ η hη)
      (u : TangentSpace I' p)

/-! ### The slice moment map -/

/-- The **slice moment map** `μ_V : V → 𝔥*`, `μ_V(v)(ξ) = ½ ω_V(ξ v, v)`, of the action of the
isotropy algebra `𝔥` of `p` on the symplectic slice `V`
(`TauCeti.SmoothTwoForm.IsNondegenerate.symplecticSliceIsotropyAction`): the linear symplectic
moment map of `(V, ω_V)` restricted along that action. -/
def symplecticSliceMomentMap (v : hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) p) :
    Module.Dual ℝ ((InfinitesimalAction.fundamental I G I' M).isotropy p) :=
  (((hσ.symplecticFormAt p).reduction ((hσ.symplecticFormAt p).orthogonal
    ((InfinitesimalAction.fundamental I G I' M).orbitTangent p))).linearMomentMap v).comp
      (hσ.symplecticSliceIsotropyAction hσG)

/-- `μ_V(v)(ξ) = ½ ω_V(ξ v, v)`. -/
@[simp]
theorem symplecticSliceMomentMap_apply
    (v : hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) p)
    (ξ : (InfinitesimalAction.fundamental I G I' M).isotropy p) :
    hσ.symplecticSliceMomentMap hσG v ξ =
      (hσ.symplecticFormAt p).reduction ((hσ.symplecticFormAt p).orthogonal
        ((InfinitesimalAction.fundamental I G I' M).orbitTangent p))
          ((hσ.symplecticSliceIsotropyAction hσG ξ :
            Module.End ℝ (hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) p)) v) v /
        2 := by
  rw [symplecticSliceMomentMap, LinearMap.comp_apply, SymplecticForm.linearMomentMap_apply]

/-- **The moment equation of the slice moment map.** The derivative of `μ_V^ξ` at `v` in the
direction `w` is `ω_V(ξ v, w)`, that is, `dμ_V^ξ = ι_(ξ v) ω_V`. -/
theorem hasDerivAt_symplecticSliceMomentMap_add_smul
    (v w : hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) p)
    (ξ : (InfinitesimalAction.fundamental I G I' M).isotropy p) :
    HasDerivAt (fun t : ℝ ↦ hσ.symplecticSliceMomentMap hσG (v + t • w) ξ)
      ((hσ.symplecticFormAt p).reduction ((hσ.symplecticFormAt p).orthogonal
        ((InfinitesimalAction.fundamental I G I' M).orbitTangent p))
          ((hσ.symplecticSliceIsotropyAction hσG ξ :
            Module.End ℝ (hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) p)) v) w)
      0 := by
  simp only [symplecticSliceMomentMap, LinearMap.comp_apply]
  exact SymplecticForm.hasDerivAt_linearMomentMap_add_smul _ v w _

/-- **Equivariance of the slice moment map.** For `g` in the stabilizer of `p` and `ξ, η` in the
isotropy algebra with `η = Ad_g ξ`, `μ_V(g v)(η) = μ_V(v)(ξ)`. -/
theorem symplecticSliceMomentMap_symplecticSliceRepresentation (g : stabilizer G p)
    (ξ η : (InfinitesimalAction.fundamental I G I' M).isotropy p)
    (hη : (η : GroupLieAlgebra I G) = Lie.tangentAd (I := I) (g : G) ξ)
    (v : hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) p) :
    hσ.symplecticSliceMomentMap hσG (hσ.symplecticSliceRepresentation hσG g v) η =
      hσ.symplecticSliceMomentMap hσG v ξ := by
  rw [symplecticSliceMomentMap_apply, symplecticSliceMomentMap_apply,
    ← symplecticSliceRepresentation_symplecticSliceIsotropyAction hσ hσG g ξ η hη,
    (hσ.isSymplectomorphism_symplecticSliceRepresentation hσG g).apply]

end TauCeti.SmoothTwoForm.IsNondegenerate
