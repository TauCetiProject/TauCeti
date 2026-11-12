/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Algebra.ConnectionChange.Basic
public import TauCeti.Algebra.Homology.Curved.Module.Right.ClosedCategory

/-!
# Change of connection on curved right modules

Changing the algebra differential to `d + [a, -]`, for `a` of degree one, changes its stored
right curvature to `w - d a - a * a`. The corresponding differential on a right module is
`dM x - (-1)^p • (x * a)` on elements of degree `p`. The minus sign and the degree-dependent
sign are both necessary for the right Leibniz rule and the curvature equation.

Simultaneous change of connection leaves the differential on homogeneous right-linear Hom
cochains unchanged. In particular, it preserves closed morphisms and homotopy boundaries.
`CurvedDGRightModuleCat.connectionChangeClosed` is the resulting additive functor on closed
morphisms. Successive connection corrections add, and the zero correction is the identity.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 6.2.
  Our stored right curvature is the negative of his curvature.
-/

public section

open MulOpposite

namespace TauCeti

universe uR uA uM uN

variable {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]
  (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]

/-- Change a right-module connection by `a`. On degree `p`, the correction is
`-(-1)^p • (x * a)`. The underlying grading and right action are unchanged. -/
noncomputable def rightModuleConnectionChange (dM : M →ₗ[R] M) (a : A) : M →ₗ[R] M where
  toFun x := dM x - op a • (InternalGrading.ofDecomposition ℳ).koszulTwist 1 x
  map_add' x y := by simp only [map_add, smul_add]; abel
  map_smul' r x := by simp only [map_smul, RingHom.id_apply, smul_sub, smul_comm r]

/-- Evaluation of the changed connection using the grading's Koszul twist. -/
@[simp]
theorem rightModuleConnectionChange_apply (dM : M →ₗ[R] M) (a : A) (x : M) :
    rightModuleConnectionChange ℳ dM a x =
      dM x - op a • (InternalGrading.ofDecomposition ℳ).koszulTwist 1 x := (rfl)

/-- The changed connection on a homogeneous module element. -/
theorem rightModuleConnectionChange_apply_of_mem (dM : M →ₗ[R] M) (a : A)
    {p : ℤ} {x : M} (hx : x ∈ ℳ p) :
    rightModuleConnectionChange ℳ dM a x = dM x - p.negOnePow • (op a • x) := by
  rw [rightModuleConnectionChange_apply,
    InternalGrading.koszulTwist_ofDecomposition_apply_of_mem ℳ hx]
  simp only [one_mul, Int.cast_smul_eq_zsmul, Units.smul_def, smul_comm (op a)]

/-- Changing a right-module connection by zero does nothing. -/
@[simp]
theorem rightModuleConnectionChange_zero (dM : M →ₗ[R] M) :
    rightModuleConnectionChange ℳ dM (0 : A) = dM := by
  ext x
  simp only [rightModuleConnectionChange_apply, op_zero, zero_smul, sub_zero]

/-- Successive changes of right-module connection add their connection forms. -/
@[simp]
theorem rightModuleConnectionChange_add (dM : M →ₗ[R] M) (a b : A) :
    rightModuleConnectionChange ℳ (rightModuleConnectionChange ℳ dM a) b =
      rightModuleConnectionChange ℳ dM (a + b) := by
  ext x
  simp only [rightModuleConnectionChange_apply, op_add, add_smul]
  abel

variable {ℳ} [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  {d : A →ₗ[R] A} {w : A} {h : IsCurvedDGAlgebra 𝒜 d w} {dM : M →ₗ[R] M}

/-- **Change of connection for curved right modules.** The signed right action correction
transports a module to the algebra of differential `d + [a, -]` and curvature
`w - d a - a * a`. -/
theorem IsCurvedDGRightModule.connectionChange (hM : IsCurvedDGRightModule h ℳ dM)
    {a : A} (ha : a ∈ 𝒜 1) :
    IsCurvedDGRightModule (h.connectionChange ha) ℳ (rightModuleConnectionChange ℳ dM a) where
  isHomogeneous := LinearMap.isHomogeneous_def.mpr fun p x hx ↦ by
    rw [rightModuleConnectionChange_apply_of_mem _ _ _ hx]
    exact sub_mem (hM.isHomogeneous.map_mem hx)
      (zsmul_mem (op_smul_mem_of_mem_graded ha hx) _)
  leibniz {p x} hx b := by
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous q b =>
      obtain ⟨b, hb⟩ := b
      simp only
      rw [rightModuleConnectionChange_apply_of_mem _ _ _ (op_smul_mem_of_mem_graded hb hx),
        rightModuleConnectionChange_apply_of_mem _ _ _ hx,
        connectionChange_apply_of_mem 𝒜 hb, hM.leibniz hx, Int.negOnePow_add]
      rcases Int.units_eq_one_or p.negOnePow with hp | hp <;>
        rcases Int.units_eq_one_or q.negOnePow with hq | hq <;>
        simp [hp, hq, add_smul, sub_smul, smul_add, smul_sub] <;>
        simp only [mul_smul] <;> abel
    | add b c hb hc =>
      simp only [op_add, add_smul, map_add, hb, hc, smul_add]
      abel
  sq_eq x := by
    induction x using DirectSum.Decomposition.inductionOn ℳ with
    | zero => simp
    | @homogeneous p x =>
      obtain ⟨x, hx⟩ := x
      simp only
      rw [rightModuleConnectionChange_apply_of_mem _ _ _ hx, map_sub, Units.smul_def,
        map_zsmul,
        rightModuleConnectionChange_apply_of_mem _ _ _ (hM.isHomogeneous.map_mem hx),
        rightModuleConnectionChange_apply_of_mem _ _ _ (op_smul_mem_of_mem_graded ha hx),
        hM.sq_eq, hM.leibniz hx, Int.negOnePow_succ]
      rcases Int.units_eq_one_or p.negOnePow with hp | hp <;>
        simp [hp, sub_smul, smul_add, smul_sub] <;>
        simp only [mul_smul] <;> abel
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]

variable [AddCommGroup N] [Module R N] [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]
  {ℳN : ℤ → Submodule R N} [DirectSum.Decomposition ℳN]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳN]
  {dN : N →ₗ[R] N}

/-- Simultaneous change of connection does not change the Hom differential on any homogeneous
right-linear cochain. The degree `-1` case says that homotopy boundaries are unchanged. -/
@[simp]
theorem dgRightModuleCochains.curvedDifferential_connectionChange
    (hM : IsCurvedDGRightModule h ℳ dM) (hN : IsCurvedDGRightModule h ℳN dN)
    {a : A} (ha : a ∈ 𝒜 1) (p : ℤ)
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) p) :
    dgRightModuleCochains.curvedDifferential (hM := hM.connectionChange ha)
        (hN := hN.connectionChange ha) p f =
      dgRightModuleCochains.curvedDifferential (hM := hM) (hN := hN) p f := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  induction x using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous q x =>
    obtain ⟨x, hx⟩ := x
    simp only
    rw [dgRightModuleCochains.curvedDifferential_apply,
      dgRightModuleCochains.curvedDifferential_apply,
      rightModuleConnectionChange_apply_of_mem _ _ _ (dgRightModuleCochains.map_mem f hx),
      rightModuleConnectionChange_apply_of_mem _ _ _ hx, Int.negOnePow_add]
    simp only [Units.smul_def, Units.val_mul, map_sub, map_zsmul, map_smul]
    rcases Int.units_eq_one_or p.negOnePow with hp | hp <;>
      rcases Int.units_eq_one_or q.negOnePow with hq | hq <;>
      simp only [hp, hq, Units.val_one, Units.val_neg, one_mul, neg_one_mul, one_zsmul,
        neg_one_zsmul, neg_neg] <;> abel
  | add x y hx hy =>
    simp only [map_add] at hx hy ⊢
    exact congrArg₂ (· + ·) hx hy

namespace CurvedDGRightModuleCat

/-- Change the connection of a bundled curved right module. Its carrier, grading and right
action are retained. -/
-- Retaining the carrier makes the unchanged right-linear maps type-correct.
@[expose, implicit_reducible]
noncomputable def connectionChangeObj (M : CurvedDGRightModuleCat.{uR, uA, uM} h)
    {a : A} (ha : a ∈ 𝒜 1) : CurvedDGRightModuleCat.{uR, uA, uM} (h.connectionChange ha) where
  carrier := M
  grading := M.grading
  differential := rightModuleConnectionChange M.grading M.differential a
  isCurvedDGRightModule := M.isCurvedDGRightModule.connectionChange ha

/-- Change of connection preserves the homogeneous pieces. -/
@[simp]
theorem connectionChangeObj_grading (M : CurvedDGRightModuleCat.{uR, uA, uM} h)
    {a : A} (ha : a ∈ 𝒜 1) (p : ℤ) :
    (connectionChangeObj M ha).grading p = M.grading p := (rfl)

/-- The differential of the changed module is the changed right-module connection. -/
@[simp]
theorem connectionChangeObj_differential (M : CurvedDGRightModuleCat.{uR, uA, uM} h)
    {a : A} (ha : a ∈ 𝒜 1) :
    (connectionChangeObj M ha).differential =
      rightModuleConnectionChange M.grading M.differential a := (rfl)

/-- On homogeneous elements the bundled change of connection subtracts the signed right
action of the connection form. -/
theorem connectionChangeObj_differential_apply_of_mem
    (M : CurvedDGRightModuleCat.{uR, uA, uM} h) {a : A} (ha : a ∈ 𝒜 1)
    {p : ℤ} {x : M} (hx : x ∈ M.grading p) :
    (connectionChangeObj M ha).differential x = M.differential x - p.negOnePow • (op a • x) :=
  rightModuleConnectionChange_apply_of_mem M.grading M.differential a hx

end CurvedDGRightModuleCat

end TauCeti

namespace TauCeti.CurvedDGRightModuleCat

open CategoryTheory

universe u

-- Closed-category objects retain the original curved-module objects.
attribute [local implicit_reducible] ForgetEnrichment

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w} {a : A} (ha : a ∈ 𝒜 1)
  {M N : CurvedDGRightModuleCat.{u, u, u} h}

/-- Simultaneous change of connection retains a closed morphism's underlying right-linear map. -/
noncomputable def connectionChangeHom
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (connectionChangeObj M ha) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (connectionChangeObj N ha) :=
  closedHomOf (closedHom (M := M) (N := N) f) (fun _ _ hx ↦ closedHom_mem f hx) (by
    let c : dgRightModuleCochains (R := R) (A := A)
        (ℳ := M.grading) (ℳN := N.grading) 0 :=
      ⟨closedHom f, (dgRightModuleCochains.mem_iff).2 (isHomogeneous_closedHom f)⟩
    apply (dgRightModuleCochains.curvedDifferential_zero_eq_zero_iff
      (hM := M.isCurvedDGRightModule.connectionChange ha)
      (hN := N.isCurvedDGRightModule.connectionChange ha) c).1
    rw [dgRightModuleCochains.curvedDifferential_connectionChange
      M.isCurvedDGRightModule N.isCurvedDGRightModule ha]
    exact (dgRightModuleCochains.curvedDifferential_zero_eq_zero_iff
      (hM := M.isCurvedDGRightModule) (hN := N.isCurvedDGRightModule) c).2
      (differential_closedHom f))

/-- The right-linear map of a changed closed morphism is unchanged. -/
@[simp]
theorem closedHom_connectionChangeHom
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    closedHom (connectionChangeHom ha f) = closedHom f := by
  simp only [connectionChangeHom, closedHom_closedHomOf]

/-- Change of connection as a functor on the closed degree-zero categories of curved right
modules. This is not restriction along a strict curved algebra map: the differential changes. -/
-- The object projection must be available for formulas on underlying right-linear maps.
@[expose]
noncomputable def connectionChangeClosed :
    ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h) ⥤
      ForgetEnrichment (CochainComplex (ModuleCat R) ℤ)
        (CurvedDGRightModuleCat.{u, u, u} (h.connectionChange ha)) where
  obj M := ForgetEnrichment.of _ (connectionChangeObj M ha)
  map {M N} f := connectionChangeHom (M := M) (N := N) ha f
  map_id M := by
    apply closedHom_ext
    intro x
    rw [closedHom_connectionChangeHom, closedHom_id]
    exact congrArg (fun l : M.carrier →ₗ[Aᵐᵒᵖ] M.carrier ↦ l x) (closedHom_id (R := R) (h := h) M)
  map_comp f g := by
    apply closedHom_ext
    intro x
    simp

/-- The connection-change functor acts on objects by changing the module differential. -/
@[simp]
theorem connectionChangeClosed_obj (M : CurvedDGRightModuleCat.{u, u, u} h) :
    (connectionChangeClosed ha).obj (ForgetEnrichment.of _ M) =
      ForgetEnrichment.of _ (connectionChangeObj M ha) := (rfl)

/-- The connection-change functor acts on morphisms by the unchanged right-linear map. -/
@[simp]
theorem closedHom_connectionChangeClosed_map
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    closedHom ((connectionChangeClosed ha).map f) = closedHom f :=
  closedHom_connectionChangeHom ha f

/-- Change of connection is additive because its maps on closed morphisms are unchanged. -/
instance : (connectionChangeClosed (h := h) ha).Additive where
  map_add {X Y} f g := by
    apply closedHom_ext
    intro x
    rw [closedHom_add, closedHom_connectionChangeClosed_map, closedHom_add]
    simp only [closedHom_connectionChangeClosed_map]
    rfl

end TauCeti.CurvedDGRightModuleCat
