/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Principal.FundamentalVectorField
public import TauCeti.Geometry.Manifold.FiberBundle.Submersion
public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import Mathlib.LinearAlgebra.Projection

/-!
# Principal connection forms and horizontal tangent spaces

A principal connection is a smooth Lie-algebra-valued one-form that reproduces fundamental
vectors and transforms by `Ad(g⁻¹)` under right translation. We use the existing smooth form
carrier on `ManifoldTotalSpace G P`, with smooth base, Lie group, and bundle transitions and
without choosing a second total-space topology or atlas.

The connection defines complementary continuous linear projections onto vertical and horizontal
tangent vectors. Its kernel complements the kernel of the bundle projection's differential;
restriction of that differential gives a linear equivalence from the horizontal tangent space
to the base tangent space. This is the pointwise horizontal lift needed for lifting base fields.
Right translations intertwine both projections. No integrability or completeness is asserted.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Chapter II, §1.
* I. Kolář, P. W. Michor, and J. Slovák, *Natural Operations in Differential Geometry*, §11.1.
-/

public section

noncomputable section

open Bundle Manifold MulOpposite
open scoped ContDiff Manifold

namespace TauCeti.PrincipalBundle

variable {B G : Type*}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  [Group G] [TopologicalSpace G] [ChartedSpace HG G] [LieGroup IG ∞ G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [ContMDiffFiberBundle ∞ G P IB IG]

-- Only the fixed coefficient space receives its model norm; no varying tangent-fibre norms
-- are installed. These local instances transport the model norm through the tangent type copy.
/-- The fixed Lie-algebra coefficient space carries its model norm locally in this file. -/
local instance : NormedAddCommGroup (GroupLieAlgebra IG G) :=
  inferInstanceAs (NormedAddCommGroup EG)

/-- The model norm makes the fixed Lie-algebra coefficient space a real normed space. -/
local instance : NormedSpace ℝ (GroupLieAlgebra IG G) :=
  inferInstanceAs (NormedSpace ℝ EG)

/-- A connection form on a smooth principal bundle with a right action: a smooth one-form
reproducing fundamental vectors and equivariant for the inverse adjoint action. -/
structure ConnectionForm (IB : ModelWithCorners ℝ EB HB) (IG : ModelWithCorners ℝ EG HG)
    (P : B → Type*) [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
    [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
    [IsManifold IB ∞ B] [LieGroup IG ∞ G] [ContMDiffFiberBundle ∞ G P IB IG] where
  /-- The underlying smooth Lie-algebra-valued one-form. -/
  toForm : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) (GroupLieAlgebra IG G) 1
  /-- The connection is the identity on fundamental vectors. -/
  reproduction : ∀ x ξ, SmoothForm.degreeOneEquiv toForm x
    (rightFundamentalVectorField (IB.prod IG) ξ x) = ξ
  /-- Right translation acts on the connection by the inverse adjoint representation. -/
  equivariance : ∀ (g : G) x v, SmoothForm.degreeOneEquiv toForm (op g • x)
    (mfderiv (IB.prod IG) (IB.prod IG) (fun y : ManifoldTotalSpace G P => op g • y) x v) =
      Lie.adjointContinuousLinearMap g⁻¹ (SmoothForm.degreeOneEquiv toForm x v)

namespace ConnectionForm

variable («ω» : ConnectionForm (G := G) IB IG P)

/-- A connection form is determined by its underlying smooth one-form. -/
@[ext]
theorem ext {«ω» η : ConnectionForm (G := G) IB IG P} (h : ω.toForm = η.toForm) :
    «ω» = η := by
  cases «ω»
  cases η
  cases h
  rfl

/-- The intrinsic continuous linear map of a connection at a point. The auxiliary coefficient
norm used to package the smooth form is not required to use this map. -/
def formAt (x : ManifoldTotalSpace G P) :
    TangentSpace (IB.prod IG) x →L[ℝ] GroupLieAlgebra IG G :=
  SmoothForm.degreeOneEquiv ω.toForm x

/-- Evaluation of the intrinsic map agrees with evaluation of the underlying one-form. -/
theorem formAt_apply (x : ManifoldTotalSpace G P) (v : TangentSpace (IB.prod IG) x) :
    ω.formAt x v = ω.toForm.1 x ![v] :=
  SmoothForm.degreeOneEquiv_apply_apply_vec ω.toForm x v

/-- The intrinsic map reproduces fundamental vectors. -/
@[simp]
theorem formAt_rightFundamentalVectorField (x : ManifoldTotalSpace G P)
    (ξ : GroupLieAlgebra IG G) :
    ω.formAt x (rightFundamentalVectorField (IB.prod IG) ξ x) = ξ :=
  ω.reproduction x ξ

/-- Right translation acts on the intrinsic map by the inverse adjoint representation. -/
theorem formAt_op_smul (g : G) (x : ManifoldTotalSpace G P)
    (v : TangentSpace (IB.prod IG) x) :
    ω.formAt (op g • x)
      (mfderiv (IB.prod IG) (IB.prod IG) (fun y : ManifoldTotalSpace G P => op g • y) x v) =
    Lie.adjointContinuousLinearMap g⁻¹ (ω.formAt x v) :=
  ω.equivariance g x v

/-- The vertical projection sends `v` to the fundamental vector generated by `ω(v)`. -/
def verticalProj (x : ManifoldTotalSpace G P) :
    TangentSpace (IB.prod IG) x →L[ℝ] TangentSpace (IB.prod IG) x :=
  (mfderiv IG (IB.prod IG) (fun g : G => op g • x) 1).comp
    (ω.formAt x)

/-- Evaluation of the vertical projection in terms of fundamental vector fields. -/
theorem verticalProj_apply (x : ManifoldTotalSpace G P) (v : TangentSpace (IB.prod IG) x) :
    ω.verticalProj x v = rightFundamentalVectorField (IB.prod IG)
      (ω.formAt x v) x := by
  -- The orbit differential lands at `op 1 • x`; unfolding the action identifies its tangent
  -- type copy with the one at `x`.
  erw [ContinuousLinearMap.comp_apply, rightFundamentalVectorField_apply]

/-- The horizontal projection subtracts the vertical component. -/
def horizontalProj (x : ManifoldTotalSpace G P) :
    TangentSpace (IB.prod IG) x →L[ℝ] TangentSpace (IB.prod IG) x :=
  ContinuousLinearMap.id ℝ _ - ω.verticalProj x

/-- Evaluation of the horizontal projection. -/
theorem horizontalProj_apply (x : ManifoldTotalSpace G P) (v : TangentSpace (IB.prod IG) x) :
    ω.horizontalProj x v = v - ω.verticalProj x v :=
  (rfl)

/-- The vertical and horizontal components reconstruct the original tangent vector. -/
@[simp]
theorem verticalProj_add_horizontalProj (x : ManifoldTotalSpace G P)
    (v : TangentSpace (IB.prod IG) x) :
    ω.verticalProj x v + ω.horizontalProj x v = v := by
  rw [horizontalProj_apply, add_comm, sub_add_cancel]

/-- Horizontal tangent vectors are the kernel of the connection form at a point. -/
def horizontalSpace (x : ManifoldTotalSpace G P) : Submodule ℝ (TangentSpace (IB.prod IG) x) :=
  (ω.formAt x).ker

/-- Membership in the horizontal tangent space is vanishing of the connection form. -/
@[simp]
theorem mem_horizontalSpace (x : ManifoldTotalSpace G P) (v : TangentSpace (IB.prod IG) x) :
    v ∈ ω.horizontalSpace x ↔ ω.formAt x v = 0 :=
  Iff.rfl

/-- The connection value of the vertical component is the connection value of the vector. -/
@[simp]
theorem form_verticalProj (x : ManifoldTotalSpace G P) (v : TangentSpace (IB.prod IG) x) :
    ω.formAt x (ω.verticalProj x v) = ω.formAt x v := by
  rw [verticalProj_apply, formAt_rightFundamentalVectorField]

/-- The vertical projection fixes fundamental vectors. -/
@[simp]
theorem verticalProj_rightFundamentalVectorField (x : ManifoldTotalSpace G P)
    (ξ : GroupLieAlgebra IG G) :
    ω.verticalProj x (rightFundamentalVectorField (IB.prod IG) ξ x) =
      rightFundamentalVectorField (IB.prod IG) ξ x := by
  rw [verticalProj_apply, formAt_rightFundamentalVectorField]

/-- The vertical component is killed by the differential of the bundle projection. -/
@[simp]
theorem mfderiv_proj_verticalProj (x : ManifoldTotalSpace G P)
    (v : TangentSpace (IB.prod IG) x) :
    mfderiv (IB.prod IG) IB
      (fun y : ManifoldTotalSpace G P => ((ManifoldTotalSpace.homeomorph G P).symm y).proj) x
      (ω.verticalProj x v) = 0 := by
  rw [verticalProj_apply, mfderiv_proj_rightFundamentalVectorField]

/-- The horizontal component is annihilated by the connection. -/
@[simp]
theorem form_horizontalProj (x : ManifoldTotalSpace G P) (v : TangentSpace (IB.prod IG) x) :
    ω.formAt x (ω.horizontalProj x v) = 0 := by
  simp only [horizontalProj_apply, map_sub, form_verticalProj, sub_self]

/-- Removing the vertical component does not change the projection to the base tangent space. -/
@[simp]
theorem mfderiv_proj_horizontalProj (x : ManifoldTotalSpace G P)
    (v : TangentSpace (IB.prod IG) x) :
    mfderiv (IB.prod IG) IB
      (fun y : ManifoldTotalSpace G P => ((ManifoldTotalSpace.homeomorph G P).symm y).proj) x
      (ω.horizontalProj x v) =
    mfderiv (IB.prod IG) IB
      (fun y : ManifoldTotalSpace G P =>
        ((ManifoldTotalSpace.homeomorph G P).symm y).proj) x v := by
  rw [horizontalProj_apply, map_sub, mfderiv_proj_verticalProj, sub_zero]

/-- The vertical projection is a projection onto the vertical tangent space. -/
theorem isProj_verticalProj (x : ManifoldTotalSpace G P) :
    LinearMap.IsProj
      (mfderiv (IB.prod IG) IB
        (fun y : ManifoldTotalSpace G P => ((ManifoldTotalSpace.homeomorph G P).symm y).proj) x).ker
      (ω.verticalProj x).toLinearMap := by
  refine ⟨fun v => ω.mfderiv_proj_verticalProj x v, ?_⟩
  intro v hv
  rw [← range_rightFundamentalLinearMap_eq_ker_mfderiv_proj] at hv
  obtain ⟨ξ, rfl⟩ := hv
  simpa only [ContinuousLinearMap.coe_coe, rightFundamentalLinearMap_apply] using
    ω.verticalProj_rightFundamentalVectorField x ξ

/-- The kernel of the vertical projection is the horizontal tangent space. -/
@[simp]
theorem ker_verticalProj (x : ManifoldTotalSpace G P) :
    (ω.verticalProj x).ker = ω.horizontalSpace x := by
  ext v
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, mem_horizontalSpace,
    verticalProj_apply, rightFundamentalVectorField_eq_zero_iff]

/-- Vertical and horizontal tangent spaces are complementary. -/
theorem isCompl_vertical_horizontal (x : ManifoldTotalSpace G P) :
    IsCompl
      (mfderiv (IB.prod IG) IB
        (fun y : ManifoldTotalSpace G P => ((ManifoldTotalSpace.homeomorph G P).symm y).proj) x).ker
      (ω.horizontalSpace x) := by
  simpa only [ker_verticalProj] using
    (ω.isProj_verticalProj x).isCompl

/-- The horizontal projection fixes exactly the horizontal tangent vectors. -/
@[simp]
theorem horizontalProj_eq_self_iff (x : ManifoldTotalSpace G P)
    (v : TangentSpace (IB.prod IG) x) :
    ω.horizontalProj x v = v ↔ v ∈ ω.horizontalSpace x := by
  rw [horizontalProj_apply, sub_eq_self, verticalProj_apply,
    rightFundamentalVectorField_eq_zero_iff, mem_horizontalSpace]

/-- The horizontal projection is a projection onto the horizontal tangent space. -/
theorem isProj_horizontalProj (x : ManifoldTotalSpace G P) :
    LinearMap.IsProj (ω.horizontalSpace x) (ω.horizontalProj x).toLinearMap :=
  ⟨fun v => ω.form_horizontalProj x v,
    fun v hv => (ω.horizontalProj_eq_self_iff x v).2 hv⟩

/-- Right translations intertwine the vertical projections. -/
theorem mfderiv_op_smul_verticalProj (g : G) (x : ManifoldTotalSpace G P)
    (v : TangentSpace (IB.prod IG) x) :
    mfderiv (IB.prod IG) (IB.prod IG) (fun y : ManifoldTotalSpace G P => op g • y) x
      (ω.verticalProj x v) =
    ω.verticalProj (op g • x)
      (mfderiv (IB.prod IG) (IB.prod IG) (fun y : ManifoldTotalSpace G P => op g • y) x v) := by
  simp only [verticalProj_apply, mfderiv_op_smul_rightFundamentalVectorField, formAt_op_smul]

/-- Right translations intertwine the horizontal projections. -/
theorem mfderiv_op_smul_horizontalProj (g : G) (x : ManifoldTotalSpace G P)
    (v : TangentSpace (IB.prod IG) x) :
    mfderiv (IB.prod IG) (IB.prod IG) (fun y : ManifoldTotalSpace G P => op g • y) x
      (ω.horizontalProj x v) =
    ω.horizontalProj (op g • x)
      (mfderiv (IB.prod IG) (IB.prod IG) (fun y : ManifoldTotalSpace G P => op g • y) x v) := by
  simp only [horizontalProj_apply, map_sub, mfderiv_op_smul_verticalProj]

/-- The differential of the projection restricted to horizontal tangent vectors. -/
def horizontalToBase (x : ManifoldTotalSpace G P) :
    ω.horizontalSpace x →ₗ[ℝ]
      TangentSpace IB (((ManifoldTotalSpace.homeomorph G P).symm x).proj) :=
  (mfderiv (IB.prod IG) IB
    (fun y : ManifoldTotalSpace G P =>
      ((ManifoldTotalSpace.homeomorph G P).symm y).proj) x).toLinearMap
    ∘ₗ (ω.horizontalSpace x).subtype

/-- The horizontal-to-base map is the differential of the principal projection. -/
@[simp]
theorem horizontalToBase_apply (x : ManifoldTotalSpace G P) (v : ω.horizontalSpace x) :
    ω.horizontalToBase x v = mfderiv (IB.prod IG) IB
      (fun y : ManifoldTotalSpace G P => ((ManifoldTotalSpace.homeomorph G P).symm y).proj) x v :=
  (rfl)

/-- Every base tangent vector has a unique horizontal lift at each point of the bundle. -/
theorem horizontalToBase_bijective (x : ManifoldTotalSpace G P) :
    Function.Bijective (ω.horizontalToBase x) := by
  constructor
  · apply (ω.horizontalToBase x).ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro v hv
    apply Subtype.ext
    exact Submodule.disjoint_def.mp (ω.isCompl_vertical_horizontal x).disjoint v
      (by simpa only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        horizontalToBase_apply] using hv) v.2
  · intro u
    obtain ⟨v, hv⟩ := (ManifoldTotalSpace.isSubmersion_proj 1 G P IB IG).surjective_mfderiv
      one_ne_zero x u
    exact ⟨⟨ω.horizontalProj x v, ω.form_horizontalProj x v⟩,
      (ω.mfderiv_proj_horizontalProj x v).trans hv⟩

/-- Restricting the principal projection's differential to the horizontal tangent space is a
linear equivalence. Its inverse is the pointwise horizontal lift. -/
def horizontalEquiv (x : ManifoldTotalSpace G P) :
    ω.horizontalSpace x ≃ₗ[ℝ]
      TangentSpace IB (((ManifoldTotalSpace.homeomorph G P).symm x).proj) :=
  LinearEquiv.ofBijective (ω.horizontalToBase x) (ω.horizontalToBase_bijective x)

/-- The horizontal equivalence agrees with the restricted projection differential. -/
@[simp]
theorem horizontalEquiv_apply (x : ManifoldTotalSpace G P) (v : ω.horizontalSpace x) :
    ω.horizontalEquiv x v = ω.horizontalToBase x v :=
  (rfl)

/-- The inverse horizontal equivalence lifts each base tangent vector to a vector over it. -/
@[simp]
theorem mfderiv_proj_horizontalEquiv_symm (x : ManifoldTotalSpace G P)
    (u : TangentSpace IB (((ManifoldTotalSpace.homeomorph G P).symm x).proj)) :
    mfderiv (IB.prod IG) IB
      (fun y : ManifoldTotalSpace G P => ((ManifoldTotalSpace.homeomorph G P).symm y).proj) x
      ((ω.horizontalEquiv x).symm u) = u := by
  simpa only [horizontalEquiv_apply, horizontalToBase_apply] using
    (ω.horizontalEquiv x).apply_symm_apply u

/-- Horizontally lifting the projection of a tangent vector gives its horizontal component. -/
@[simp]
theorem horizontalEquiv_symm_mfderiv_proj (x : ManifoldTotalSpace G P)
    (v : TangentSpace (IB.prod IG) x) :
    ((ω.horizontalEquiv x).symm (mfderiv (IB.prod IG) IB
      (fun y : ManifoldTotalSpace G P => ((ManifoldTotalSpace.homeomorph G P).symm y).proj) x v) :
        TangentSpace (IB.prod IG) x) = ω.horizontalProj x v := by
  have h : ω.horizontalEquiv x ⟨ω.horizontalProj x v, ω.form_horizontalProj x v⟩ =
      mfderiv (IB.prod IG) IB
        (fun y : ManifoldTotalSpace G P =>
          ((ManifoldTotalSpace.homeomorph G P).symm y).proj) x v := by
    rw [horizontalEquiv_apply, horizontalToBase_apply]
    exact ω.mfderiv_proj_horizontalProj x v
  exact congrArg Subtype.val ((ω.horizontalEquiv x).symm_apply_eq.mpr h.symm)

end ConnectionForm

end TauCeti.PrincipalBundle
