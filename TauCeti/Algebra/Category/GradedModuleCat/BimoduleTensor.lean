/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Basic
public import TauCeti.Algebra.Module.TensorProductActions
public import TauCeti.Algebra.Module.GradedModule.Opposite
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Actions
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Balanced tensor products of graded bimodules

Graded bimodules over a graded algebra `A` are objects of `GradedModuleCat` over the
enveloping algebra `A ⊗[k] Aᵐᵒᵖ`, with the tensor-product internal grading. Restricting
the enveloping action gives the two commuting actions used to balance over `A`.
The quotient has the sum internal grading and the outer enveloping action.

This file packages the existing balanced tensor product and its grading as a bifunctor
on graded bimodules. It supplies ordinary tensor composition; its internal grading
does not introduce a Koszul sign. Cohomological tensor signs come from Mathlib's
totalization when this bifunctor is applied to cochain complexes.

## References

* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public section

open CategoryTheory MulOpposite
open scoped TensorProduct

namespace TauCeti.GradedModuleCat

universe v uk uA

variable {k : Type uk} {A : Type uA} [CommRing k] [Ring A] [Algebra k A]
  (Γ : InternalGrading k A)

local notation "E" => A ⊗[k] Aᵐᵒᵖ

/-- The left action obtained by restricting the envelope action to its first factor. -/
local instance (M : GradedModuleCat.{v} (Γ.tensorProduct Γ.opposite).piece) : Module A M :=
  TauCeti.Algebra.TensorProduct.moduleLeft (k := k) (A := A) (B := Aᵐᵒᵖ) M

/-- The right action obtained by restricting the envelope action to its second factor. -/
local instance (M : GradedModuleCat.{v} (Γ.tensorProduct Γ.opposite).piece) : Module Aᵐᵒᵖ M :=
  TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := A) (B := Aᵐᵒᵖ) M

local instance (M : GradedModuleCat.{v} (Γ.tensorProduct Γ.opposite).piece) : IsScalarTower k A M :=
  TauCeti.Algebra.TensorProduct.moduleLeftIsScalarTower (k := k) (A := A) (B := Aᵐᵒᵖ) M

local instance (M : GradedModuleCat.{v} (Γ.tensorProduct Γ.opposite).piece) :
    IsScalarTower k Aᵐᵒᵖ M :=
  TauCeti.Algebra.TensorProduct.moduleRightIsScalarTower (k := k) (A := A) (B := Aᵐᵒᵖ) M

local instance (M : GradedModuleCat.{v} (Γ.tensorProduct Γ.opposite).piece) :
    SMulCommClass A Aᵐᵒᵖ M :=
  TauCeti.Algebra.TensorProduct.moduleSMulCommClass (k := k) (A := A) (B := Aᵐᵒᵖ) M

local instance [SetLike.GradedOne Γ.piece]
    (M : GradedModuleCat.{v} (Γ.tensorProduct Γ.opposite).piece) :
    SetLike.GradedSMul Γ.piece M.grading.piece where
  smul_mem {p q} {a m} ha hm := by
    -- Express the restricted action through its defining inclusion into the envelope.
    change (a ⊗ₜ[k] (1 : Aᵐᵒᵖ)) • m ∈ M.grading.piece (p + q)
    have h1 : (1 : Aᵐᵒᵖ) ∈ Γ.opposite.piece 0 :=
      (Γ.mem_opposite_piece_iff 0 1).2 (SetLike.one_mem_graded Γ.piece)
    have h := Γ.tmul_mem_tensorProduct Γ.opposite ha h1
    rw [add_zero] at h
    exact SetLike.GradedSMul.smul_mem h hm

local instance rightGradedSMul [DirectSum.Decomposition Γ.piece]
    [SetLike.GradedOne Γ.piece] (M : GradedModuleCat.{v} (Γ.tensorProduct Γ.opposite).piece) :
    SetLike.GradedSMul (InternalGrading.ofDecomposition Γ.piece).opposite.piece
      M.grading.piece where
  smul_mem {p q} {a m} ha hm := by
    -- Express the restricted right action through the other envelope inclusion.
    change ((1 : A) ⊗ₜ[k] a) • m ∈ M.grading.piece (p + q)
    rw [InternalGrading.mem_opposite_piece_iff, InternalGrading.ofDecomposition_piece] at ha
    have ha' : a ∈ Γ.opposite.piece p := (Γ.mem_opposite_piece_iff p a).2 ha
    have h := Γ.tmul_mem_tensorProduct Γ.opposite (SetLike.one_mem_graded Γ.piece) ha'
    rw [zero_add] at h
    exact SetLike.GradedSMul.smul_mem h hm

section Tensor

variable [GradedAlgebra Γ.piece]

variable (M N : GradedModuleCat.{v} (Γ.tensorProduct Γ.opposite).piece)

local notation "T" => BalancedTensorProduct k A M N

/-- The left outer action on the balanced tensor quotient. -/
local instance : Module A T := BalancedTensorProduct.leftModule A
/-- The right outer action on the balanced tensor quotient. -/
local instance : Module Aᵐᵒᵖ T := BalancedTensorProduct.rightModule Aᵐᵒᵖ
local instance : IsScalarTower k A T := BalancedTensorProduct.leftIsScalarTower A
local instance : IsScalarTower k Aᵐᵒᵖ T := BalancedTensorProduct.rightIsScalarTower Aᵐᵒᵖ
local instance : SMulCommClass A Aᵐᵒᵖ T :=
  BalancedTensorProduct.outerSMulCommClass A Aᵐᵒᵖ
/-- The commuting outer actions combine into an action of the envelope. -/
local instance : Module E T := TensorProduct.Algebra.module

local instance : IsScalarTower k E T :=
  IsScalarTower.of_algebraMap_smul fun r z ↦ by
    rw [Algebra.TensorProduct.algebraMap_apply (R := k) (S := k) (A := A) (B := Aᵐᵒᵖ),
      TensorProduct.Algebra.smul_def (R := k) (A := A) (B := Aᵐᵒᵖ) (M := T), one_smul]
    exact IsScalarTower.algebraMap_smul A r z

local instance : SetLike.GradedSMul Γ.piece
    (BalancedTensorProduct.grading (𝒜 := Γ.piece) M.grading N.grading).piece :=
  BalancedTensorProduct.gradedSMul_left (𝒜 := Γ.piece) M.grading N.grading A Γ.piece

local instance : SetLike.GradedSMul (InternalGrading.ofDecomposition Γ.piece).opposite.piece
    (BalancedTensorProduct.grading (𝒜 := Γ.piece) M.grading N.grading).piece :=
  BalancedTensorProduct.gradedSMul_right (𝒜 := Γ.piece) M.grading N.grading Aᵐᵒᵖ
    (InternalGrading.ofDecomposition Γ.piece).opposite.piece

/-- The balanced tensor product of two internally graded bimodules, with its outer
enveloping action and sum internal grading. -/
-- Expose the quotient carrier so the existing balanced-tensor instances apply to its elements.
@[expose]
noncomputable def bimoduleTensorObj : GradedModuleCat.{v} (Γ.tensorProduct Γ.opposite).piece where
  carrier := T
  grading := BalancedTensorProduct.grading (𝒜 := Γ.piece) M.grading N.grading
  gradedSMul := ⟨fun {p q} {a z} ha hz ↦ by
    rw [InternalGrading.tensorProduct_piece_eq_iSup] at ha
    refine (iSup_le fun r ↦ Submodule.map₂_le.mpr fun x hx y hy ↦ ?_ :
      _ ≤ ((BalancedTensorProduct.grading (𝒜 := Γ.piece) M.grading N.grading).piece
        (p + q)).comap (LinearMap.applyₗ (R := k) z ∘ₗ
          (Algebra.lsmul k k T (A := E)).toLinearMap)) ha
    simp only [Submodule.mem_comap, TensorProduct.mk_apply, LinearMap.comp_apply,
      LinearMap.applyₗ_apply_apply, AlgHom.toLinearMap_apply, Algebra.lsmul_apply,
      TensorProduct.Algebra.smul_def]
    have hy' : y ∈ (InternalGrading.ofDecomposition Γ.piece).opposite.piece (p - r) := by
      simpa only [InternalGrading.mem_opposite_piece_iff,
        InternalGrading.ofDecomposition_piece] using hy
    have h := SetLike.GradedSMul.smul_mem hx (SetLike.GradedSMul.smul_mem hy' hz)
    -- The envelope degrees are r and p - r, whose sum is p.
    simpa only [vadd_eq_add, show r + (p - r + q) = p + q by omega] using h⟩

/-- The pure tensor in the graded bimodule tensor product. -/
def bimoduleTensorTmul (m : M) (n : N) : bimoduleTensorObj Γ M N :=
  BalancedTensorProduct.tmul k A m n

/-- Internal degrees add on pure bimodule tensors. -/
theorem bimoduleTensorTmul_mem {p q : ℤ} {m : M} {n : N}
    (hm : m ∈ M.grading.piece p) (hn : n ∈ N.grading.piece q) :
    bimoduleTensorTmul Γ M N m n ∈ (bimoduleTensorObj Γ M N).grading.piece (p + q) :=
  BalancedTensorProduct.tmul_mem_grading (𝒜 := Γ.piece) M.grading N.grading hm hn

/-- Every bimodule tensor is a sum of pure tensors. -/
@[elab_as_elim]
theorem bimoduleTensor_induction_on {P : bimoduleTensorObj Γ M N → Prop}
    (z : bimoduleTensorObj Γ M N)
    (ht : ∀ m n, P (bimoduleTensorTmul Γ M N m n))
    (ha : ∀ x y, P x → P y → P (x + y)) : P z :=
  BalancedTensorProduct.induction_on k A z ht ha

/-- The quotient map from the ground-ring tensor product. -/
noncomputable def bimoduleTensorMkQ : M ⊗[k] N →ₗ[k] bimoduleTensorObj Γ M N :=
  BalancedTensorProduct.mkQ k A

@[simp]
theorem bimoduleTensorMkQ_tmul (m : M) (n : N) :
    bimoduleTensorMkQ Γ M N (m ⊗ₜ[k] n) = bimoduleTensorTmul Γ M N m n :=
  BalancedTensorProduct.mkQ_tmul k A m n

/-- The internal degree piece is the image of the ground-ring tensor degree piece. -/
theorem bimoduleTensorObj_grading_piece (p : ℤ) :
    (bimoduleTensorObj Γ M N).grading.piece p =
      ((M.grading.tensorProduct N.grading).piece p).map (bimoduleTensorMkQ Γ M N) :=
  BalancedTensorProduct.grading_piece M.grading N.grading p

/-- A homogeneous balanced tensor has a homogeneous ground-ring representative. -/
theorem mem_bimoduleTensorObj_piece_iff {p : ℤ} {z : bimoduleTensorObj Γ M N} :
    z ∈ (bimoduleTensorObj Γ M N).grading.piece p ↔
      ∃ x ∈ (M.grading.tensorProduct N.grading).piece p, bimoduleTensorMkQ Γ M N x = z :=
  BalancedTensorProduct.mem_grading_piece_iff M.grading N.grading

/-- Balancing moves the right action on the first factor to the left action on the second. -/
theorem bimoduleTensorTmul_balance (a : A) (m : M) (n : N) :
    bimoduleTensorTmul Γ M N (((1 : A) ⊗ₜ[k] op a) • m) n =
      bimoduleTensorTmul Γ M N m ((a ⊗ₜ[k] (1 : Aᵐᵒᵖ)) • n) :=
  BalancedTensorProduct.balance k A a m n

/-- A pure enveloping scalar acts on the two outer factors. -/
@[simp]
theorem tmul_smul_bimoduleTensorTmul (a : A) (b : Aᵐᵒᵖ) (m : M) (n : N) :
    (a ⊗ₜ[k] b) • bimoduleTensorTmul Γ M N m n =
      bimoduleTensorTmul Γ M N ((a ⊗ₜ[k] (1 : Aᵐᵒᵖ)) • m)
        (((1 : A) ⊗ₜ[k] b) • n) := by
  -- Compute the envelope action on the quotient using the two outer actions.
  change (a ⊗ₜ[k] b) • BalancedTensorProduct.tmul k A m n =
    BalancedTensorProduct.tmul k A (a • m) (b • n)
  rw [TensorProduct.Algebra.smul_def (R := k) (A := A) (B := Aᵐᵒᵖ)
    (M := BalancedTensorProduct k A M N)]
  simp only [BalancedTensorProduct.smul_tmul_right, BalancedTensorProduct.smul_tmul_left]

variable {M N}
  {M' N' M'' N'' : GradedModuleCat.{v} (Γ.tensorProduct Γ.opposite).piece}

private def tensorMapBase (f : M ⟶ M') (g : N ⟶ N') :
    BalancedTensorProduct k A M N →ₗ[k] BalancedTensorProduct k A M' N' :=
  BalancedTensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k)
    (fun a m ↦ f.hom.map_smul ((1 : A) ⊗ₜ[k] op a) m)
    (fun a n ↦ g.hom.map_smul (a ⊗ₜ[k] (1 : Aᵐᵒᵖ)) n)

private noncomputable def tensorMapLinear (f : M ⟶ M') (g : N ⟶ N') :
    BalancedTensorProduct k A M N →ₗ[E] BalancedTensorProduct k A M' N' where
  toFun := tensorMapBase Γ f g
  map_add' := (tensorMapBase Γ f g).map_add
  map_smul' c z := by
    -- Remove the identity ring homomorphism in the linear-map structure field.
    change tensorMapBase Γ f g (c • z) = c • tensorMapBase Γ f g z
    have hleft (a : A) (z : BalancedTensorProduct k A M N) :
        tensorMapBase Γ f g (a • z) = a • tensorMapBase Γ f g z :=
      BalancedTensorProduct.map_smul_left A
        (f.hom.restrictScalars k) (g.hom.restrictScalars k)
        (fun a m ↦ f.hom.map_smul ((1 : A) ⊗ₜ[k] op a) m)
        (fun a n ↦ g.hom.map_smul (a ⊗ₜ[k] (1 : Aᵐᵒᵖ)) n)
        (fun a m ↦ f.hom.map_smul (a ⊗ₜ[k] (1 : Aᵐᵒᵖ)) m) a z
    have hright (b : Aᵐᵒᵖ) (z : BalancedTensorProduct k A M N) :
        tensorMapBase Γ f g (b • z) = b • tensorMapBase Γ f g z :=
      BalancedTensorProduct.map_smul_right Aᵐᵒᵖ
        (f.hom.restrictScalars k) (g.hom.restrictScalars k)
        (fun a m ↦ f.hom.map_smul ((1 : A) ⊗ₜ[k] op a) m)
        (fun a n ↦ g.hom.map_smul (a ⊗ₜ[k] (1 : Aᵐᵒᵖ)) n)
        (fun b n ↦ g.hom.map_smul ((1 : A) ⊗ₜ[k] b) n) b z
    induction c using TensorProduct.inductionOn with
    | tmul a b =>
      rw [TensorProduct.Algebra.smul_def (R := k) (A := A) (B := Aᵐᵒᵖ)
        (M := BalancedTensorProduct k A M N),
        TensorProduct.Algebra.smul_def (R := k) (A := A) (B := Aᵐᵒᵖ)
          (M := BalancedTensorProduct k A M' N')]
      rw [hleft, hright]
    | add c d hc hd => simp only [add_smul, map_add, hc, hd]

private theorem tensorMapBase_mem (f : M ⟶ M') (g : N ⟶ N') {p : ℤ}
    {z : BalancedTensorProduct k A M N}
    (hz : z ∈ (BalancedTensorProduct.grading (𝒜 := Γ.piece) M.grading N.grading).piece p) :
    tensorMapBase Γ f g z ∈
      (BalancedTensorProduct.grading (𝒜 := Γ.piece) M'.grading N'.grading).piece p := by
  have hf : LinearMap.IsHomogeneous (f.hom.restrictScalars k)
      M.grading.piece M'.grading.piece 0 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by simpa using map_mem f hx
  have hg : LinearMap.IsHomogeneous (g.hom.restrictScalars k)
      N.grading.piece N'.grading.piece 0 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by simpa using map_mem g hx
  have h := BalancedTensorProduct.isHomogeneous_map (𝒜 := Γ.piece)
    M.grading N.grading M'.grading N'.grading
    (f.hom.restrictScalars k) (g.hom.restrictScalars k)
    (fun a m ↦ f.hom.map_smul ((1 : A) ⊗ₜ[k] op a) m)
    (fun a n ↦ g.hom.map_smul (a ⊗ₜ[k] (1 : Aᵐᵒᵖ)) n) hf hg
  simpa only [tensorMapBase, add_zero] using h.map_mem hz

/-- Tensor the degree-zero bimodule maps in both factors. -/
noncomputable def bimoduleTensorMap (f : M ⟶ M') (g : N ⟶ N') :
    bimoduleTensorObj Γ M N ⟶ bimoduleTensorObj Γ M' N' :=
  ofHom (tensorMapLinear Γ f g) (LinearMap.isHomogeneous_def.2 fun p z hz ↦ by
    -- The bundled morphism uses the same underlying map and quotient grading.
    change tensorMapBase Γ f g z ∈
      (BalancedTensorProduct.grading (𝒜 := Γ.piece) M'.grading N'.grading).piece (p + 0)
    rw [add_zero]
    exact tensorMapBase_mem Γ f g hz)

@[simp]
theorem bimoduleTensorMap_tmul (f : M ⟶ M') (g : N ⟶ N') (m : M) (n : N) :
    (bimoduleTensorMap Γ f g).hom (bimoduleTensorTmul Γ M N m n) =
      bimoduleTensorTmul Γ M' N' (f.hom m) (g.hom n) :=
  BalancedTensorProduct.map_tmul _ _ _ _ _ _

/-- Morphisms out of a bimodule tensor product agree if they agree on pure tensors. -/
@[ext]
theorem bimoduleTensor_hom_ext {P : GradedModuleCat.{v} (Γ.tensorProduct Γ.opposite).piece}
    {f g : bimoduleTensorObj Γ M N ⟶ P}
    (h : ∀ m n, f.hom (bimoduleTensorTmul Γ M N m n) =
      g.hom (bimoduleTensorTmul Γ M N m n)) : f = g := by
  apply hom_ext
  apply LinearMap.ext
  intro z
  induction z using BalancedTensorProduct.induction_on with
  | ht m n => exact h m n
  | ha x y hx hy =>
    exact (f.hom.map_add x y).trans ((congrArg₂ (· + ·) hx hy).trans
      (g.hom.map_add x y).symm)

@[simp]
theorem bimoduleTensorMap_id :
    bimoduleTensorMap Γ (𝟙 M) (𝟙 N) = 𝟙 (bimoduleTensorObj Γ M N) := by
  apply bimoduleTensor_hom_ext Γ
  intro m n
  simp

/-- Tensoring bimodule maps respects composition. -/
theorem bimoduleTensorMap_comp (f : M ⟶ M') (g : N ⟶ N')
    (f' : M' ⟶ M'') (g' : N' ⟶ N'') :
    bimoduleTensorMap Γ (f ≫ f') (g ≫ g') =
      bimoduleTensorMap Γ f g ≫ bimoduleTensorMap Γ f' g' := by
  apply bimoduleTensor_hom_ext Γ
  intro m n
  simp

@[simp]
theorem bimoduleTensorMap_add_left (f f' : M ⟶ M') (g : N ⟶ N') :
    bimoduleTensorMap Γ (f + f') g = bimoduleTensorMap Γ f g + bimoduleTensorMap Γ f' g := by
  apply bimoduleTensor_hom_ext Γ
  intro m n
  simp only [hom_add, LinearMap.add_apply, bimoduleTensorMap_tmul]
  exact BalancedTensorProduct.add_tmul k A _ _ _

@[simp]
theorem bimoduleTensorMap_add_right (f : M ⟶ M') (g g' : N ⟶ N') :
    bimoduleTensorMap Γ f (g + g') = bimoduleTensorMap Γ f g + bimoduleTensorMap Γ f g' := by
  apply bimoduleTensor_hom_ext Γ
  intro m n
  simp only [hom_add, LinearMap.add_apply, bimoduleTensorMap_tmul]
  exact BalancedTensorProduct.tmul_add k A _ _ _

@[simp]
theorem bimoduleTensorMap_smul_left (c : k) (f : M ⟶ M') (g : N ⟶ N') :
    bimoduleTensorMap Γ (c • f) g = c • bimoduleTensorMap Γ f g := by
  apply bimoduleTensor_hom_ext Γ
  intro m n
  simp only [hom_smul, LinearMap.smul_apply, bimoduleTensorMap_tmul]
  exact BalancedTensorProduct.smul_tmul k A _ _ _

@[simp]
theorem bimoduleTensorMap_smul_right (c : k) (f : M ⟶ M') (g : N ⟶ N') :
    bimoduleTensorMap Γ f (c • g) = c • bimoduleTensorMap Γ f g := by
  apply bimoduleTensor_hom_ext Γ
  intro m n
  simp only [hom_smul, LinearMap.smul_apply, bimoduleTensorMap_tmul]
  exact BalancedTensorProduct.tmul_smul k A _ _ _

/-- Balanced tensor composition of internally graded bimodules. -/
-- Expose the object assignment so the tensor maps have the computed source and target types.
@[expose]
noncomputable def bimoduleTensor :
    GradedModuleCat.{v} (Γ.tensorProduct Γ.opposite).piece ⥤
      GradedModuleCat.{v} (Γ.tensorProduct Γ.opposite).piece ⥤
        GradedModuleCat.{v} (Γ.tensorProduct Γ.opposite).piece where
  obj M :=
    { obj N := bimoduleTensorObj Γ M N
      map g := bimoduleTensorMap Γ (𝟙 M) g
      map_id N := bimoduleTensorMap_id Γ
      map_comp g g' := by
        rw [← bimoduleTensorMap_comp, Category.id_comp] }
  map f :=
    { app N := bimoduleTensorMap Γ f (𝟙 N)
      naturality N N' g := by
        -- Compute the components of the two curried tensor maps.
        change bimoduleTensorMap Γ (𝟙 _) g ≫ bimoduleTensorMap Γ f (𝟙 _) =
          bimoduleTensorMap Γ f (𝟙 _) ≫ bimoduleTensorMap Γ (𝟙 _) g
        simp only [← bimoduleTensorMap_comp, Category.id_comp, Category.comp_id] }
  map_id M := by
    apply NatTrans.ext
    funext N
    exact bimoduleTensorMap_id Γ
  map_comp f f' := by
    apply NatTrans.ext
    funext N
    -- Compute composition componentwise in the functor category.
    change bimoduleTensorMap Γ (f ≫ f') (𝟙 N) =
      bimoduleTensorMap Γ f (𝟙 N) ≫ bimoduleTensorMap Γ f' (𝟙 N)
    rw [← bimoduleTensorMap_comp, Category.id_comp]

@[simp]
theorem bimoduleTensor_obj_obj : ((bimoduleTensor Γ).obj M).obj N =
    bimoduleTensorObj Γ M N := rfl

@[simp]
theorem bimoduleTensor_obj_map (g : N ⟶ N') :
    ((bimoduleTensor Γ).obj M).map g = bimoduleTensorMap Γ (𝟙 M) g := rfl

@[simp]
theorem bimoduleTensor_map_app (f : M ⟶ M') :
    ((bimoduleTensor Γ).map f).app N = bimoduleTensorMap Γ f (𝟙 N) := rfl

instance : ((bimoduleTensor Γ).obj M).Additive where
  map_add := bimoduleTensorMap_add_right Γ (𝟙 M) _ _

instance : ((bimoduleTensor Γ).flip.obj N).Additive where
  map_add := bimoduleTensorMap_add_left Γ _ _ (𝟙 N)

instance : ((bimoduleTensor Γ).obj M).Linear k where
  map_smul f c := bimoduleTensorMap_smul_right Γ c (𝟙 M) f

instance : ((bimoduleTensor Γ).flip.obj N).Linear k where
  map_smul f c := bimoduleTensorMap_smul_left Γ c f (𝟙 N)

end Tensor

end TauCeti.GradedModuleCat
