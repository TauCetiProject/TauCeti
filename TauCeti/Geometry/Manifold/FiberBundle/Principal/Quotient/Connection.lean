/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff
public import TauCeti.Geometry.Manifold.FiberBundle.Principal.Connection
public import TauCeti.Geometry.Manifold.FiberBundle.Principal.Quotient

import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Stabilizer

/-!
# Connection forms of free proper quotients

Let a finite-dimensional real Lie group `G` act smoothly, freely and properly on the left on a
finite-dimensional boundaryless manifold `M`. The orbit projection `M → M ⧸ G` is a smooth
principal `G`-bundle for the right action `x · g = g⁻¹ • x`
(`ProperSMul.principalBundle_orbitRelFiber`), whose charted total space is identified with `M` by
the diffeomorphism `φ = ProperSMul.orbitRelFiberDiffeomorph`. This file reads the connection forms
of that principal bundle on `M` itself.

Since `φ(x · g) = g⁻¹ • φ(x)`, the differential of `φ` carries the fundamental vector field `ξ♯` of
the right action to the **negative** of the fundamental vector field `ξ_M` of the left action
(`ProperSMul.mfderiv_orbitRelFiberDiffeomorph_rightFundamentalVectorField`). So a connection form
`A` of the bundle of orbits, transported to the `𝔤`-valued one-form `A_M = (φ⁻¹)^* A` on `M`
(`ProperSMul.orbitConnectionForm`), satisfies

* `A_M(ξ_M) = -ξ`
  (`ProperSMul.orbitConnectionForm_apply_fundamentalVectorField`), and
* `(g • ·)^* A_M = Ad(g) ∘ A_M`
  (`ProperSMul.mpullback_smul_orbitConnectionForm`),

the left-action form of the two laws `A(ξ♯) = ξ` and `R_g^* A = Ad(g⁻¹) ∘ A` of a connection form.

Pairing with a covector `ν ∈ 𝔤*` gives the real one-form `⟨ν, A_M⟩`
(`TauCeti.SmoothForm.mapCoeff`), with `⟨ν, A_M⟩(ξ_M) = -ν(ξ)`
(`ProperSMul.mapCoeff_orbitConnectionForm_apply_fundamentalVectorField`). It is invariant under
every `g` with `Ad*_g ν = ν`, that is `ν ∘ Ad(g) = ν`
(`ProperSMul.mpullback_smul_mapCoeff_orbitConnectionForm`); so for `ν` fixed by the coadjoint
action it is `G`-invariant. These are the two properties asked of the one-form that shifts the
level `μ⁻¹(ν)` of the cotangent moment map to its zero level in magnetic cotangent reduction at a
coadjoint-fixed value.

## Main definitions

* `ProperSMul.orbitConnectionForm A`: a connection form `A` of the bundle of orbits, read on `M`.

## Main results

* `ProperSMul.mfderiv_orbitRelFiberDiffeomorph_rightFundamentalVectorField`: the identification of
  the total space with `M` negates fundamental vector fields.
* `ProperSMul.orbitConnectionForm_apply_fundamentalVectorField`: `A_M(ξ_M) = -ξ`.
* `ProperSMul.mpullback_smul_orbitConnectionForm`: `(g • ·)^* A_M = Ad(g) ∘ A_M`.
* `ProperSMul.mapCoeff_orbitConnectionForm_apply_fundamentalVectorField`:
  `⟨ν, A_M⟩(ξ_M) = -ν(ξ)`.
* `ProperSMul.mpullback_smul_mapCoeff_orbitConnectionForm`: the one-form `⟨ν, A_M⟩` is invariant
  under every `g` fixing `ν`.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter II, §1 (connection forms).
* Juan-Pablo Ortega and Tudor S. Ratiu, *Cotangent bundle reduction*, in *Encyclopedia of
  Mathematical Physics*, Elsevier, 2006 (principal connections of free actions and their pairings
  with coadjoint-fixed values).
-/

public section

noncomputable section

open Bundle Function Manifold MulOpposite TauCeti
open scoped ContDiff Manifold

namespace ProperSMul

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M] [ProperSMul G M] [IsCancelSMul G M]

/-- **The identification of the bundle of orbits with `M` negates fundamental vector fields.** The
diffeomorphism `φ` from the charted total space of the bundle of orbits onto `M` carries the
fundamental vector field `ξ♯` of the right action `x · g = g⁻¹ • x` to the negative of the
fundamental vector field `ξ_M` of the left action. -/
theorem mfderiv_orbitRelFiberDiffeomorph_rightFundamentalVectorField (ξ : GroupLieAlgebra I G)
    (x : letI := orbitRelQuotientChartedSpace I G I' M
      letI := orbitRelFiberBundle I G I' M
      ManifoldTotalSpace G (orbitRelFiber G M)) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitRelFiberBundle I G I' M
    mfderiv (𝓘(ℝ, QuotientModelSpace E E').prod I) I' (orbitRelFiberDiffeomorph I G I' M) x
        (rightFundamentalVectorField (𝓘(ℝ, QuotientModelSpace E E').prod I) ξ x) =
      -fundamentalVectorField I' ξ (orbitRelFiberDiffeomorph I G I' M x) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitRelFiberBundle I G I' M
  have := principalBundle_orbitRelFiber (I := I) (G := G) (I' := I') (M := M)
  set φ := orbitRelFiberDiffeomorph I G I' M
  -- `φ (x · g) = g⁻¹ • φ x`: the orbit map of `x` read through `φ` is the orbit map of `φ x`
  -- composed with inversion, whose differential at `1` is `-id`.
  have hfun : (φ ∘ fun g : G ↦ op g • x) = (fun g : G ↦ g • φ x) ∘ fun g : G ↦ g⁻¹ :=
    funext fun g ↦ orbitRelFiberDiffeomorph_op_smul g x
  have hinv : MDifferentiableAt I I (fun g : G ↦ g⁻¹) 1 :=
    (contMDiff_inv I ∞).mdifferentiableAt (by simp)
  have horbit : MDifferentiableAt I I' (fun g : G ↦ g • φ x) 1 :=
    (ContMDiffSMul.contMDiff_smul_const (n := ∞) (I := I) (φ x) _).mdifferentiableAt (by simp)
  rw [rightFundamentalVectorField_apply, ← mfderiv_comp_apply_of_eq (1 : G)
    (φ.mdifferentiable (by simp) x) (PrincipalBundle.mdifferentiableAt_orbit (n := ∞) (by simp) x 1)
    (by simp), hfun, mfderiv_comp_apply_of_eq (1 : G) horbit hinv inv_one,
    GroupLieAlgebra.mfderiv_inv_one_apply, map_neg, fundamentalVectorField_apply]
  -- Both sides negate the same vector, once in `TangentSpace I' (φ x)` and once in the model
  -- space `E'` it abbreviates.
  rfl

/-- The inverse of the identification of the bundle of orbits with `M` carries the fundamental
vector field `ξ_M` of the left action to the negative of the fundamental vector field `ξ♯` of the
right action `x · g = g⁻¹ • x`. -/
theorem mfderiv_orbitRelFiberDiffeomorph_symm_fundamentalVectorField (ξ : GroupLieAlgebra I G)
    (x : M) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitRelFiberBundle I G I' M
    mfderiv I' (𝓘(ℝ, QuotientModelSpace E E').prod I) (orbitRelFiberDiffeomorph I G I' M).symm x
        (fundamentalVectorField I' ξ x) =
      -rightFundamentalVectorField (𝓘(ℝ, QuotientModelSpace E E').prod I) ξ
        ((orbitRelFiberDiffeomorph I G I' M).symm x) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitRelFiberBundle I G I' M
  -- Write `x = φ y`, so that `ξ_M x = -dφ (ξ♯ y)`, and apply `dφ⁻¹`.
  obtain ⟨y, rfl⟩ : ∃ y, orbitRelFiberDiffeomorph I G I' M y = x :=
    ⟨_, Diffeomorph.apply_symm_apply _ x⟩
  rw [← neg_neg (fundamentalVectorField I' ξ _),
    ← mfderiv_orbitRelFiberDiffeomorph_rightFundamentalVectorField, map_neg,
    Diffeomorph.mfderiv_symm_apply_mfderiv_apply _ (by simp)]
  -- The two sides are the same vector of the model space, at `y = φ⁻¹ (φ y)`.
  exact congrArg (fun z ↦ (-rightFundamentalVectorField (𝓘(ℝ, QuotientModelSpace E E').prod I) ξ z :
    QuotientModelSpace E E' × E)) (Diffeomorph.symm_apply_apply _ y).symm

/-! ### Connection forms read on `M` -/

/-- A connection form `A` of the bundle of orbits of a free proper action, read on `M`: the
`𝔤`-valued one-form `(φ⁻¹)^* A` for the identification `φ` of the charted total space with `M`
(`ProperSMul.orbitRelFiberDiffeomorph`). When `A` is a connection form, it takes the value `-ξ` on
the fundamental vector field `ξ_M` (`ProperSMul.orbitConnectionForm_apply_fundamentalVectorField`)
and is transformed by `Ad(g)` under the action of `g`
(`ProperSMul.mpullback_smul_orbitConnectionForm`). -/
def orbitConnectionForm
    (A : letI := orbitRelQuotientChartedSpace I G I' M
      letI := orbitRelFiberBundle I G I' M
      haveI := contMDiffFiberBundle_orbitRelFiber (I := I) (G := G) (I' := I') (M := M)
      SmoothForm (𝓘(ℝ, QuotientModelSpace E E').prod I) (ManifoldTotalSpace G (orbitRelFiber G M))
        E 1) :
    SmoothForm I' M E 1 :=
  letI := orbitRelQuotientChartedSpace I G I' M
  letI := orbitRelFiberBundle I G I' M
  haveI := contMDiffFiberBundle_orbitRelFiber (I := I) (G := G) (I' := I') (M := M)
  SmoothForm.mpullback (orbitRelFiberDiffeomorph I G I' M).symm
    (orbitRelFiberDiffeomorph I G I' M).symm.contMDiff A

section ConnectionForm

variable {A : letI := orbitRelQuotientChartedSpace I G I' M
  letI := orbitRelFiberBundle I G I' M
  haveI := contMDiffFiberBundle_orbitRelFiber (I := I) (G := G) (I' := I') (M := M)
  SmoothForm (𝓘(ℝ, QuotientModelSpace E E').prod I) (ManifoldTotalSpace G (orbitRelFiber G M)) E 1}

/-- The value of a connection form read on `M` on a tangent vector `v` at `x` is the value of the
connection form on the image of `v` in the total space of the bundle of orbits. -/
theorem orbitConnectionForm_apply (x : M) (v : TangentSpace I' x) :
    letI := orbitRelQuotientChartedSpace I G I' M
    letI := orbitRelFiberBundle I G I' M
    haveI := contMDiffFiberBundle_orbitRelFiber (I := I) (G := G) (I' := I') (M := M)
    (orbitConnectionForm A).val x ![v] =
      A.val ((orbitRelFiberDiffeomorph I G I' M).symm x)
        ![mfderiv I' (𝓘(ℝ, QuotientModelSpace E E').prod I)
          (orbitRelFiberDiffeomorph I G I' M).symm x v] := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitRelFiberBundle I G I' M
  have := contMDiffFiberBundle_orbitRelFiber (I := I) (G := G) (I' := I') (M := M)
  exact SmoothForm.mpullback_apply_one _ _ A x v

/-- **A connection form read on `M` takes the value `-ξ` on the fundamental vector field `ξ_M`** of
the left action, since the identification of the bundle of orbits with `M` carries the
fundamental vector field `ξ♯` of the right action, on which a connection form takes the value `ξ`,
to `-ξ_M`. -/
theorem orbitConnectionForm_apply_fundamentalVectorField
    (hA : letI := orbitRelQuotientChartedSpace I G I' M
      letI := orbitRelFiberBundle I G I' M
      haveI := contMDiffFiberBundle_orbitRelFiber (I := I) (G := G) (I' := I') (M := M)
      PrincipalBundle.IsConnectionForm A)
    (x : M) (ξ : GroupLieAlgebra I G) :
    (orbitConnectionForm A).val x ![fundamentalVectorField I' ξ x] = -ξ := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitRelFiberBundle I G I' M
  have := contMDiffFiberBundle_orbitRelFiber (I := I) (G := G) (I' := I') (M := M)
  rw [orbitConnectionForm_apply, mfderiv_orbitRelFiberDiffeomorph_symm_fundamentalVectorField,
    ← neg_one_smul ℝ (rightFundamentalVectorField _ ξ _), ContinuousAlternatingMap.vecCons_smul,
    hA.apply_rightFundamentalVectorField]
  -- The value `-ξ` is read in the model space `E`, which is the Lie algebra.
  exact neg_one_smul ℝ (ξ : E)

/-- **A connection form read on `M` is transformed by `Ad(g)` under the action of `g`**:
`(g • ·)^* A_M = Ad(g) ∘ A_M`. This is the equivariance `R_g^* A = Ad(g⁻¹) ∘ A` of the connection
form, since the action of `g` on `M` is the right action of `g⁻¹` on the bundle of orbits. -/
theorem mpullback_smul_orbitConnectionForm
    (hA : letI := orbitRelQuotientChartedSpace I G I' M
      letI := orbitRelFiberBundle I G I' M
      haveI := contMDiffFiberBundle_orbitRelFiber (I := I) (G := G) (I' := I') (M := M)
      PrincipalBundle.IsConnectionForm A)
    (g : G) :
    SmoothForm.mpullback (fun x : M ↦ g • x) (ContMDiffSMul.contMDiff_const_smul (I := I) g)
        (orbitConnectionForm A) =
      SmoothForm.mapCoeff (F := E) (G := E) (Lie.adjointContinuousLinearMap (I := I) g)
        (orbitConnectionForm A) := by
  let _ := orbitRelQuotientChartedSpace I G I' M
  let _ := orbitRelFiberBundle I G I' M
  have := contMDiffFiberBundle_orbitRelFiber (I := I) (G := G) (I' := I') (M := M)
  have := principalBundle_orbitRelFiber (I := I) (G := G) (I' := I') (M := M)
  set φ := orbitRelFiberDiffeomorph I G I' M
  -- The action of `g` on `M` is the right action of `g⁻¹` on the bundle of orbits.
  have hcomp : (φ.symm ∘ fun x : M ↦ g • x) = (fun y ↦ op g⁻¹ • y) ∘ φ.symm :=
    funext fun x ↦ by
      have h := orbitRelFiberDiffeomorph_op_smul (I := I) (I' := I') g⁻¹ (φ.symm x)
      rw [inv_inv, φ.apply_symm_apply] at h
      rw [comp_apply, comp_apply, ← h, φ.symm_apply_apply]
  rw [orbitConnectionForm, SmoothForm.mpullback_mpullback_of_comp_eq _ φ.symm.contMDiff
    φ.symm.contMDiff (contMDiff_const_smul (op g⁻¹)) hcomp, hA.mpullback_op_smul, inv_inv,
    SmoothForm.mpullback_mapCoeff (F := E) (G := E) (Lie.adjointContinuousLinearMap (I := I) g)]

/-- **Pairing a connection form read on `M` with a covector.** For `ν ∈ 𝔤*`, the real one-form
`⟨ν, A_M⟩` takes the value `-ν(ξ)` on the fundamental vector field `ξ_M`. -/
theorem mapCoeff_orbitConnectionForm_apply_fundamentalVectorField
    (hA : letI := orbitRelQuotientChartedSpace I G I' M
      letI := orbitRelFiberBundle I G I' M
      haveI := contMDiffFiberBundle_orbitRelFiber (I := I) (G := G) (I' := I') (M := M)
      PrincipalBundle.IsConnectionForm A)
    (ν : Module.Dual ℝ (GroupLieAlgebra I G)) (x : M) (ξ : GroupLieAlgebra I G) :
    (SmoothForm.mapCoeff (F := E) (LinearMap.toContinuousLinearMap ν)
        (orbitConnectionForm A)).val x ![fundamentalVectorField I' ξ x] = -ν ξ := by
  rw [SmoothForm.coe_mapCoeff (F := E) (LinearMap.toContinuousLinearMap ν),
    RoughForm.mapCoeff_apply, orbitConnectionForm_apply_fundamentalVectorField hA]
  exact map_neg ν ξ

/-- **The pairing `⟨ν, A_M⟩` is invariant under every `g` fixing the covector `ν`.** Since
`(g • ·)^* A_M = Ad(g) ∘ A_M` and `ν ∘ Ad(g) = ν` when `Ad*_g ν = ν`, the action of `g` preserves
the real one-form `⟨ν, A_M⟩`. In particular, for a coadjoint-fixed `ν` this one-form is
`G`-invariant. -/
theorem mpullback_smul_mapCoeff_orbitConnectionForm
    (hA : letI := orbitRelQuotientChartedSpace I G I' M
      letI := orbitRelFiberBundle I G I' M
      haveI := contMDiffFiberBundle_orbitRelFiber (I := I) (G := G) (I' := I') (M := M)
      PrincipalBundle.IsConnectionForm A)
    {ν : Module.Dual ℝ (GroupLieAlgebra I G)} {g : G}
    (hν : Lie.coadjointRepresentation ℝ I G g ν = ν) :
    SmoothForm.mpullback (fun x : M ↦ g • x) (ContMDiffSMul.contMDiff_const_smul (I := I) g)
        (SmoothForm.mapCoeff (F := E) (LinearMap.toContinuousLinearMap ν)
          (orbitConnectionForm A)) =
      SmoothForm.mapCoeff (F := E) (LinearMap.toContinuousLinearMap ν) (orbitConnectionForm A) := by
  -- `ν ∘ Ad(g) = Ad*_(g⁻¹) ν = ν`, read as continuous linear maps of the model space.
  have hνg : (LinearMap.toContinuousLinearMap ν : E →L[ℝ] ℝ).comp
      (Lie.adjointContinuousLinearMap (I := I) g) = LinearMap.toContinuousLinearMap ν :=
    ContinuousLinearMap.ext
      (Lie.mem_stabilizer_coadjointRepresentation_iff.1 (Representation.mem_stabilizer.2 hν))
  rw [SmoothForm.mpullback_mapCoeff, mpullback_smul_orbitConnectionForm hA,
    ← LinearMap.comp_apply, ← SmoothForm.mapCoeff_comp (F := E) (G := E)
      (LinearMap.toContinuousLinearMap ν) (Lie.adjointContinuousLinearMap (I := I) g)]
  exact congrArg (fun L : E →L[ℝ] ℝ ↦ SmoothForm.mapCoeff L (orbitConnectionForm A)) hνg

end ConnectionForm

end ProperSMul
