/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.StarModuleCat.Basic
public import TauCeti.LinearAlgebra.Complex.Conjugation
public import Mathlib.CategoryTheory.Equivalence

/-!
# Real descent as an equivalence of categories

Complexification, equipped with conjugation on its scalar factor, is an equivalence
from real modules to complex modules with conjugation. Morphisms on the complex side
are complex-linear maps commuting with conjugation; the inverse functor takes fixed
points. No finite-dimensionality or Hermitian pairing is needed.

`TauCeti.complexDescent` has unit `w ↦ 1 ⊗ w` and counit `z ⊗ w ↦ z • w`.
In particular it preserves the chosen real structure, not merely the underlying real
dimension. These functorial comparisons allow real field generators and their
complexifications to be transported without choosing a basis.

The counit is the fixed-point equivalence of
`TauCeti.LinearAlgebra.Complex.Conjugation`; see also Serre, *Linear Representations
of Finite Groups*, §13.2 for real forms.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace TauCeti

/-- Complexification with its canonical conjugation. The carrier is reducible so that
native tensor and fixed-point operations can be used on the functor's objects. -/
noncomputable abbrev complexificationFunctor : ModuleCat.{u} ℝ ⥤ StarModuleCat.{u} ℂ where
  obj W :=
    -- Do not install this on arbitrary tensors: the real factor may have another star.
    let starW : StarAddMonoid (ℂ ⊗[ℝ] W) := {
      star := tmulConj W
      star_involutive := tmulConj_involutive W
      star_add := map_add _ }
    { toModuleCat := ModuleCat.of ℂ (ℂ ⊗[ℝ] W)
      starAddMonoid := starW
      starModule := @StarModule.mk ℂ (ℂ ⊗[ℝ] W) _ starW.toStar _
        (fun z v => (tmulConj W).map_smulₛₗ z v) }
  map f := ⟨f.hom.baseChange ℂ, fun v => (tmulConj_baseChange f.hom v).symm⟩
  map_id W := by ext v; simp
  map_comp f g := by ext v; simp [LinearMap.baseChange_comp]

/-- On pure tensors, conjugation conjugates just the scalar factor. The star instance
is specified explicitly because the tensor carrier can carry other involutions. -/
@[simp] theorem _root_.ModuleCat.star_complexification_tmul (W : ModuleCat.{u} ℝ)
    (z : ℂ) (w : W) :
    @star (complexificationFunctor.obj W) (complexificationFunctor.obj W).starAddMonoid.toStar
      (z ⊗ₜ[ℝ] w) = (starRingEnd ℂ) z ⊗ₜ[ℝ] w :=
  tmulConj_tmul W z w

/-- Complexification acts on the real factor of pure tensors. -/
@[simp] theorem _root_.ModuleCat.complexificationFunctor_map_tmul
    {W W' : ModuleCat.{u} ℝ} (f : W ⟶ W') (z : ℂ) (w : W) :
    (complexificationFunctor.map f).hom (z ⊗ₜ[ℝ] w) = z ⊗ₜ[ℝ] f.hom w :=
  LinearMap.baseChange_tmul _ _ _

/-- The fixed-point real module of a complex module with conjugation. The carrier is
reducible to the native fixed-point submodule. -/
noncomputable abbrev realPointsFunctor : StarModuleCat.{u} ℂ ⥤ ModuleCat.{u} ℝ where
  obj V := ModuleCat.of ℝ (realPoints (starLinearEquiv ℂ (A := V)).toLinearMap)
  map f := ModuleCat.ofHom {
    toFun v := ⟨f.hom v, by
      exact mem_realPoints.mpr ((f.map_star' (v : _)).symm.trans
        (congrArg f.hom (mem_realPoints.mp v.property)))⟩
    map_add' _ _ := Subtype.ext (map_add _ _ _)
    map_smul' r v := Subtype.ext (f.hom.restrictScalars ℝ |>.map_smul r v) }

/-- Taking real points restricts a morphism to its fixed vectors. -/
@[simp] theorem StarModuleCat.realPointsFunctor_map_apply
    {V V' : StarModuleCat.{u} ℂ} (f : V ⟶ V') (v : realPointsFunctor.obj V) :
    ((realPointsFunctor.map f).hom v : V') = f.hom v := rfl

/-- A real module is canonically the fixed points of its complexification. -/
noncomputable def _root_.ModuleCat.complexificationRealPointsEquiv (W : ModuleCat.{u} ℝ) :
    W ≃ₗ[ℝ] realPointsFunctor.obj (complexificationFunctor.obj W) :=
  LinearEquiv.ofBijective
    ({ toFun w := ⟨(1 : ℂ) ⊗ₜ[ℝ] w, by
         simpa only [mem_realPoints, LinearEquiv.coe_coe, starLinearEquiv_apply, map_one]
           using W.star_complexification_tmul (1 : ℂ) w⟩
       map_add' _ _ := Subtype.ext (TensorProduct.tmul_add _ _ _)
       map_smul' r w := Subtype.ext (by
         simp only [RingHom.id_apply, Submodule.coe_smul_of_tower]
         rw [← Complex.coe_smul]
         simp [TensorProduct.tmul_smul, TensorProduct.smul_tmul']) } :
      W →ₗ[ℝ] realPointsFunctor.obj (complexificationFunctor.obj W))
    ⟨fun x y h => by
        simpa using congrArg (realPart W) (congrArg Subtype.val h),
      fun v => by
        obtain ⟨w, hw⟩ := (tmulConj_eq_self_iff W (v : ℂ ⊗[ℝ] W)).mp
          (mem_realPoints.mp v.property)
        exact ⟨w, Subtype.ext hw.symm⟩⟩

/-- The unit embeds a real vector as a tensor with scalar one. -/
@[simp] theorem _root_.ModuleCat.coe_complexificationRealPointsEquiv
    (W : ModuleCat.{u} ℝ) (w : W) :
    (W.complexificationRealPointsEquiv w : ℂ ⊗[ℝ] W) = 1 ⊗ₜ[ℝ] w := (rfl)

/-- The inverse unit reads off the real part of a fixed tensor. -/
@[simp] theorem _root_.ModuleCat.complexificationRealPointsEquiv_symm_apply
    (W : ModuleCat.{u} ℝ) (v : realPointsFunctor.obj (complexificationFunctor.obj W)) :
    W.complexificationRealPointsEquiv.symm v = realPart W (v : ℂ ⊗[ℝ] W) := by
  have h := congrArg (fun w : realPointsFunctor.obj (complexificationFunctor.obj W) =>
    realPart W (w : ℂ ⊗[ℝ] W)) (W.complexificationRealPointsEquiv.apply_symm_apply v)
  rw [ModuleCat.coe_complexificationRealPointsEquiv] at h
  simpa only [realPart_tmul, Complex.one_re, one_smul] using h

/-- The fixed-point equivalence is an isomorphism preserving conjugation. -/
noncomputable def StarModuleCat.complexificationRealPointsIso (V : StarModuleCat.{u} ℂ) :
    complexificationFunctor.obj (realPointsFunctor.obj V) ≅ V := by
  let e := realPointsEquiv (K := (starLinearEquiv ℂ (A := V)).toLinearMap) star_star
  have he : ∀ v, e (@star _ (complexificationFunctor.obj
      (realPointsFunctor.obj V)).starAddMonoid.toStar v) = star (e v) :=
    realPointsEquiv_tmulConj
      (K := (starLinearEquiv ℂ (A := V)).toLinearMap) star_star
  exact {
    hom := ⟨e.toLinearMap, he⟩
    inv := ⟨e.symm.toLinearMap, fun v => by
      apply e.injective
      rw [he]
      simp⟩
    hom_inv_id := StarModuleCat.hom_ext (LinearMap.ext e.symm_apply_apply)
    inv_hom_id := StarModuleCat.hom_ext (LinearMap.ext e.apply_symm_apply) }

/-- The counit evaluates a pure tensor by scalar multiplication. -/
@[simp] theorem StarModuleCat.complexificationRealPointsIso_hom_tmul
    (V : StarModuleCat.{u} ℂ) (z : ℂ) (v : realPointsFunctor.obj V) :
    V.complexificationRealPointsIso.hom.hom (z ⊗ₜ[ℝ] v) = z • (v : V) :=
  realPointsEquiv_tmul _ _ _

/-- The inverse counit is the inverse of the supplied fixed-point equivalence, so its
real/imaginary decomposition is given by `TauCeti.realPointsEquiv_symm_apply`. -/
@[simp] theorem StarModuleCat.complexificationRealPointsIso_inv_hom
    (V : StarModuleCat.{u} ℂ) :
    V.complexificationRealPointsIso.inv.hom =
      (realPointsEquiv (K := (starLinearEquiv ℂ (A := V)).toLinearMap)
        star_star).symm.toLinearMap := (rfl)

/-- The natural identification of a real module with the real points of its
complexification. -/
noncomputable def complexificationUnitIso :
    𝟭 (ModuleCat.{u} ℝ) ≅ complexificationFunctor ⋙ realPointsFunctor :=
  NatIso.ofComponents
    (fun W => W.complexificationRealPointsEquiv.toModuleIso)
    (fun f => by
      ext w
      apply Subtype.ext
      simp only [LinearEquiv.toModuleIso, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
        LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
      rw [ModuleCat.coe_complexificationRealPointsEquiv]
      dsimp
      rw [ModuleCat.coe_complexificationRealPointsEquiv]
      simp)

@[simp] theorem _root_.ModuleCat.complexificationUnitIso_hom_app_hom (W : ModuleCat.{u} ℝ) :
    (complexificationUnitIso.hom.app W).hom = W.complexificationRealPointsEquiv.toLinearMap :=
  (rfl)

@[simp] theorem _root_.ModuleCat.complexificationUnitIso_inv_app_hom (W : ModuleCat.{u} ℝ) :
    (complexificationUnitIso.inv.app W).hom = W.complexificationRealPointsEquiv.symm.toLinearMap :=
  (rfl)

/-- The natural identification of a conjugate module with the complexification of
its real points. -/
noncomputable def complexificationCounitIso :
    realPointsFunctor ⋙ complexificationFunctor ≅ 𝟭 (StarModuleCat.{u} ℂ) :=
  NatIso.ofComponents StarModuleCat.complexificationRealPointsIso (fun f => by
    apply StarModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    induction v using TensorProduct.inductionOn with
    | tmul z w =>
      simp only [Functor.comp_map, Functor.id_map, StarModuleCat.comp_hom,
        LinearMap.comp_apply]
      rw [ModuleCat.complexificationFunctor_map_tmul (realPointsFunctor.map f) z w,
        StarModuleCat.complexificationRealPointsIso_hom_tmul,
        StarModuleCat.complexificationRealPointsIso_hom_tmul]
      simp
    | add v w hv hw => simp_all)

@[simp] theorem StarModuleCat.complexificationCounitIso_hom_app (V : StarModuleCat.{u} ℂ) :
    complexificationCounitIso.hom.app V = V.complexificationRealPointsIso.hom := (rfl)

@[simp] theorem StarModuleCat.complexificationCounitIso_inv_app (V : StarModuleCat.{u} ℂ) :
    complexificationCounitIso.inv.app V = V.complexificationRealPointsIso.inv := (rfl)

/-- Real modules are equivalent to complex modules equipped with conjugation.
The unit is `w ↦ 1 ⊗ w`, and the counit is `z ⊗ w ↦ z • w`. The equivalence
includes naturality and both triangle identities. This abbreviation assembles the
preceding functors and natural isomorphisms. -/
noncomputable abbrev complexDescent : ModuleCat.{u} ℝ ≌ StarModuleCat.{u} ℂ where
  functor := complexificationFunctor
  inverse := realPointsFunctor
  unitIso := complexificationUnitIso
  counitIso := complexificationCounitIso
  functor_unitIso_comp W := by
    apply StarModuleCat.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro z w
    dsimp [complexificationUnitIso, complexificationCounitIso]
    rw [StarModuleCat.complexificationRealPointsIso_hom_tmul]
    simp only [LinearEquiv.toModuleIso, ModuleCat.hom_ofHom, LinearEquiv.coe_coe]
    rw [ModuleCat.coe_complexificationRealPointsEquiv]
    simp [TensorProduct.smul_tmul']

end TauCeti
