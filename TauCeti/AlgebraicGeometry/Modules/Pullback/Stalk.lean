/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pullback.Stalk
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
public import TauCeti.AlgebraicGeometry.Modules.Stalk

/-!
# Stalks of pulled-back `𝒪_X`-modules

Establishes `pullbackStalkEquiv : 𝒪_{X,x} ⊗[𝒪_{Y,f(x)}] M_{f(x)} ≃ₗ[𝒪_{X,x}] (f^* M)_x` for
arbitrary scheme morphisms `f : X ⟶ Y` and `M : Y.Modules` (Tag 0098), with naturality, unit and
composition compatibilities, and `pullbackStalkEquivOfIsOpenImmersion`.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct
universe u
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
private def algebraTensorCongrOfEq {R₀ A₀ : CommRingCat.{u}} {M₀ : Type u}
    [AddCommGroup M₀] [Module R₀ M₀] {ρ₁ ρ₂ : R₀ ⟶ A₀} (h : ρ₁ = ρ₂) :
    @TensorProduct R₀ _ A₀ M₀ _ _ ρ₁.hom.toAlgebra.toModule _ ≃ₗ[A₀]
      @TensorProduct R₀ _ A₀ M₀ _ _ ρ₂.hom.toAlgebra.toModule _ :=
  h ▸ LinearEquiv.refl A₀ _
private theorem algebraTensorCongrOfEq_tmul {R₀ A₀ : CommRingCat.{u}} {M₀ : Type u}
    [AddCommGroup M₀] [Module R₀ M₀] {ρ₁ ρ₂ : R₀ ⟶ A₀} (h : ρ₁ = ρ₂) (a : A₀) (m : M₀) :
    algebraTensorCongrOfEq h
        (@TensorProduct.tmul R₀ _ A₀ M₀ _ _ ρ₁.hom.toAlgebra.toModule _ a m) =
      @TensorProduct.tmul R₀ _ A₀ M₀ _ _ ρ₂.hom.toAlgebra.toModule _ a m := by
  subst h; rfl
section
variable (X : Scheme.{u}) (x : X)

/-- The canonical `𝒪_{X,x}`-linear equivalence `(𝟙_ X.Modules)_x ≃ₗ[𝒪_{X,x}] 𝒪_{X,x}`. -/
def unitStalkEquiv : (𝟙_ X.Modules).presheaf.stalk x ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
  _root_.SheafOfModules.unitStalkEquiv X.sheaf x
@[simp] theorem unitStalkEquiv_germ (U : X.Opens) (hx : x ∈ U) (r : Γ(𝟙_ X.Modules, U)) :
    unitStalkEquiv X x ((𝟙_ X.Modules).presheaf.germ U x hx r) = X.presheaf.germ U x hx r :=
  _root_.SheafOfModules.unitStalkEquiv_germ X.sheaf x U hx r
@[simp] theorem unitStalkEquiv_symm_germ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) :
    (unitStalkEquiv X x).symm (X.presheaf.germ U x hx r) =
      (𝟙_ X.Modules).presheaf.germ U x hx r :=
  (unitStalkEquiv X x).symm_apply_eq.mpr (unitStalkEquiv_germ X x U hx r).symm
end
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (x : X)

/-- `SheafOfModules.stalkRingHom` for `f : X ⟶ Y` agrees with `f.stalkMap x`. -/
@[simp] theorem stalkRingHom_toRingCatSheafHom :
    _root_.SheafOfModules.stalkRingHom f.base f.toRingCatSheafHom x = f.stalkMap x := by
  refine TopCat.Presheaf.stalk_hom_ext Y.presheaf fun U hx ↦ ?_
  ext r
  exact (_root_.SheafOfModules.stalkRingHom_germ_apply f.base f.toRingCatSheafHom x U hx r).trans
    (ConcreteCategory.congr_hom (f.germ_stalkMap U x hx) r).symm

/-- The canonical `𝒪_{X,x}`-linear comparison
`𝒪_{X,x} ⊗[𝒪_{Y,f(x)}] M_{f(x)} →ₗ[𝒪_{X,x}] (f^* M)_x` along `f.stalkMap x`. -/
def pullbackStalkComparison :
    letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)] M.presheaf.stalk (f x) →ₗ[X.presheaf.stalk x]
      ((pullback f).obj M).presheaf.stalk x :=
  letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  let e := algebraTensorCongrOfEq (M₀ := M.presheaf.stalk (f x))
    (stalkRingHom_toRingCatSheafHom f x).symm
  let g := _root_.SheafOfModules.pullbackStalkComparison f.base f.toRingCatSheafHom M x
  { toFun t := g (e t)
    map_add' t₁ t₂ := (congrArg g (e.map_add t₁ t₂)).trans (g.map_add (e t₁) (e t₂))
    map_smul' c t := (congrArg g (e.map_smul c t)).trans (g.map_smul c (e t)) }
@[simp] theorem pullbackStalkComparison_tmul_germ (a : X.presheaf.stalk x) (U : Y.Opens)
    (hx : f x ∈ U) (m : Γ(M, U)) :
    letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    pullbackStalkComparison f M x (a ⊗ₜ[Y.presheaf.stalk (f x)] M.presheaf.germ U (f x) hx m) =
      a • ((pullback f).obj M).presheaf.germ (f ⁻¹ᵁ U) x hx (f.pullbackSections M U m) := by
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  exact (congrArg (_root_.SheafOfModules.pullbackStalkComparison f.base f.toRingCatSheafHom M x)
      (algebraTensorCongrOfEq_tmul (stalkRingHom_toRingCatSheafHom f x).symm a
        (M.presheaf.germ U (f x) hx m))).trans
    ((_root_.SheafOfModules.pullbackStalkComparison_tmul_germ f.base f.toRingCatSheafHom M x
      a U hx m).trans
      (congrArg (fun s ↦ a • ((pullback f).obj M).presheaf.germ (f ⁻¹ᵁ U) x hx s)
        (f.pullbackSections_apply M U m).symm))
theorem pullbackStalkComparison_one_tmul_germ (U : Y.Opens) (hx : f x ∈ U) (m : Γ(M, U)) :
    letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    pullbackStalkComparison f M x
        ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x)] M.presheaf.germ U (f x) hx m) =
      ((pullback f).obj M).presheaf.germ (f ⁻¹ᵁ U) x hx (f.pullbackSections M U m) := by
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  exact (pullbackStalkComparison_tmul_germ f M x 1 U hx m).trans (one_smul _ _)

/-- `𝒪_{X,x} ⊗[𝒪_{Y,f(x)}] M_{f(x)} →ₗ[𝒪_{X,x}] (f^* M)_x` is bijective (Tag 0098). -/
@[stacks 0098] theorem pullbackStalkComparison_bijective :
    letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    Function.Bijective (pullbackStalkComparison f M x) := by
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  exact (_root_.SheafOfModules.pullbackStalkComparison_bijective
    f.base f.toRingCatSheafHom M x).comp
    (algebraTensorCongrOfEq (M₀ := M.presheaf.stalk (f x))
      (stalkRingHom_toRingCatSheafHom f x).symm).bijective

/-- The canonical `𝒪_{X,x}`-linear equivalence
`𝒪_{X,x} ⊗[𝒪_{Y,f(x)}] M_{f(x)} ≃ₗ[𝒪_{X,x}] (f^* M)_x` (Tag 0098). -/
@[stacks 0098] def pullbackStalkEquiv :
    letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)] M.presheaf.stalk (f x) ≃ₗ[X.presheaf.stalk x]
      ((pullback f).obj M).presheaf.stalk x :=
  letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  LinearEquiv.ofBijective (pullbackStalkComparison f M x) (pullbackStalkComparison_bijective f M x)
@[simp] theorem pullbackStalkEquiv_apply :
    letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    ∀ t : X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)] M.presheaf.stalk (f x),
      pullbackStalkEquiv f M x t = pullbackStalkComparison f M x t := fun _ ↦ (rfl)
@[simp]
theorem pullbackStalkEquiv_symm_germ_pullbackSections (U : Y.Opens) (hx : f x ∈ U) (m : Γ(M, U)) :
    letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    (pullbackStalkEquiv f M x).symm
        (((pullback f).obj M).presheaf.germ (f ⁻¹ᵁ U) x hx (f.pullbackSections M U m)) =
      (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x)] M.presheaf.germ U (f x) hx m := by
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  exact (pullbackStalkEquiv f M x).symm_apply_eq.mpr
    (pullbackStalkComparison_one_tmul_germ f M x U hx m).symm

/-- Value of `β.stalkMap x ∘ pullbackStalkComparison f M x` on `a ⊗ germ(m)`. -/
theorem stalkMap_pullbackStalkComparison_tmul_germ {H : X.Modules}
    (β : (pullback f).obj M ⟶ H) (a : X.presheaf.stalk x) (U : Y.Opens) (hx : f x ∈ U)
    (m : Γ(M, U)) :
    letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    β.stalkMap x (pullbackStalkComparison f M x
        (a ⊗ₜ[Y.presheaf.stalk (f x)] M.presheaf.germ U (f x) hx m)) =
      a • H.presheaf.germ (f ⁻¹ᵁ U) x hx (β.app (f ⁻¹ᵁ U) (f.pullbackSections M U m)) := by
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  exact (congrArg (β.stalkMap x) (pullbackStalkComparison_tmul_germ f M x a U hx m)).trans
    ((_root_.map_smul (β.stalkMap x) a _).trans
      (congrArg (a • ·) (Hom.stalkMap_germ β x (f ⁻¹ᵁ U) hx _)))

/-- Naturality of `pullbackStalkComparison` in `M`. -/
theorem pullbackStalkComparison_naturality {M' : Y.Modules} (α : M ⟶ M') :
    letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    (((pullback f).map α).stalkMap x).comp (pullbackStalkComparison f M x) =
      (pullbackStalkComparison f M' x).comp
        ((α.stalkMap (f x)).baseChange (X.presheaf.stalk x)) := by
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  let _ : Module (Y.presheaf.stalk (f x)) (((pullback f).obj M').presheaf.stalk x) :=
    Module.compHom _ (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x))
  have _ : IsScalarTower (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
      (((pullback f).obj M').presheaf.stalk x) := IsScalarTower.of_compHom _ _ _
  refine TensorProduct.AlgebraTensorModule.ext fun a s ↦ ?_
  obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf s
  exact (stalkMap_pullbackStalkComparison_tmul_germ f M x ((pullback f).map α) a U hx m).trans
    ((congrArg (fun t ↦ a • ((pullback f).obj M').presheaf.germ (f ⁻¹ᵁ U) x hx t)
      (f.pullbackSections_naturality M U α m)).trans
      ((congrArg (pullbackStalkComparison f M' x) ((α.stalkMap (f x)).baseChange_tmul a _)).trans
        ((congrArg (fun t ↦ pullbackStalkComparison f M' x (a ⊗ₜ t))
          (Hom.stalkMap_germ α (f x) U hx m)).trans
          (pullbackStalkComparison_tmul_germ f M' x a U hx (α.app U m)))).symm)

/-- Naturality of `pullbackStalkEquiv` in `M`. -/
theorem pullbackStalkEquiv_naturality {M' : Y.Modules} (α : M ⟶ M') :
    letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    (((pullback f).map α).stalkMap x).comp (pullbackStalkEquiv f M x).toLinearMap =
      (pullbackStalkEquiv f M' x).toLinearMap.comp
        ((α.stalkMap (f x)).baseChange (X.presheaf.stalk x)) :=
  pullbackStalkComparison_naturality f M x α

/-- Compatibility of `pullbackStalkComparison` at `𝟙_ Y.Modules` with `pullbackObjUnitIso f`. -/
theorem unitStalkEquiv_stalkMap_pullbackObjUnitIso_hom :
    letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    (unitStalkEquiv X x).toLinearMap.comp
        (((pullbackObjUnitIso f).hom.stalkMap x).comp
          (pullbackStalkComparison f (𝟙_ Y.Modules) x)) =
      (TensorProduct.AlgebraTensorModule.rid
          (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) (X.presheaf.stalk x)).toLinearMap.comp
        ((unitStalkEquiv Y (f x)).toLinearMap.baseChange (X.presheaf.stalk x)) := by
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  refine TensorProduct.AlgebraTensorModule.ext fun a s ↦ ?_
  obtain ⟨U, hx, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq (𝟙_ Y.Modules).presheaf s
  let r' : Γ(Y, U) := r
  have hε₁ : Functor.LaxMonoidal.ε (sectionsFunctor U) r' = r :=
    (congrArg (· r') (sectionsFunctor_ε U)).trans (ConcreteCategory.id_apply r')
  have hε₂ : Functor.LaxMonoidal.ε (sectionsFunctor (f ⁻¹ᵁ U)) (f.app U r') = f.app U r' :=
    (congrArg (· (f.app U r')) (sectionsFunctor_ε (f ⁻¹ᵁ U))).trans (ConcreteCategory.id_apply _)
  have h₁ : (pullbackObjUnitIso f).hom.app (f ⁻¹ᵁ U) (f.pullbackSections (𝟙_ Y.Modules) U r) =
      f.app U r' :=
    (congrArg (fun z ↦ (pullbackObjUnitIso f).hom.app (f ⁻¹ᵁ U)
      (f.pullbackSections (𝟙_ Y.Modules) U z)) hε₁.symm).trans
      ((f.pullbackObjUnitIso_hom_app_pullbackSections_ε U r').trans hε₂)
  have hL : unitStalkEquiv X x ((pullbackObjUnitIso f).hom.stalkMap x
      (pullbackStalkComparison f (𝟙_ Y.Modules) x
        (a ⊗ₜ (𝟙_ Y.Modules).presheaf.germ U (f x) hx r))) =
      a • X.presheaf.germ (f ⁻¹ᵁ U) x hx (f.app U r') :=
    (congrArg (unitStalkEquiv X x) (stalkMap_pullbackStalkComparison_tmul_germ f (𝟙_ Y.Modules) x
      (pullbackObjUnitIso f).hom a U hx r)).trans
      ((_root_.map_smul (unitStalkEquiv X x) a _).trans (congrArg (a • ·)
        ((congrArg (fun t ↦ unitStalkEquiv X x
          ((𝟙_ X.Modules).presheaf.germ (f ⁻¹ᵁ U) x hx t)) h₁).trans
          (unitStalkEquiv_germ X x (f ⁻¹ᵁ U) hx (f.app U r')))))
  have hR' : TensorProduct.AlgebraTensorModule.rid
      (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) (X.presheaf.stalk x)
      (((unitStalkEquiv Y (f x)).toLinearMap.baseChange (X.presheaf.stalk x))
        (a ⊗ₜ (𝟙_ Y.Modules).presheaf.germ U (f x) hx r)) =
      a • X.presheaf.germ (f ⁻¹ᵁ U) x hx (f.app U r') := by
    rw [LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.rid_tmul]
    change unitStalkEquiv Y (f x) ((𝟙_ Y.Modules).presheaf.germ U (f x) hx r) • a = _
    rw [unitStalkEquiv_germ]
    change f.stalkMap x (Y.presheaf.germ U (f x) hx r') * a = a * _
    exact (congrArg (· * a)
      (ConcreteCategory.congr_hom (f.germ_stalkMap U x hx) r')).trans (mul_comm _ a)
  exact hL.trans hR'.symm

/-- Compatibility of `pullbackStalkComparison` with `(pullbackComp f g).inv.app N`. -/
theorem stalkMap_pullbackComp_inv_pullbackStalkComparison {Z : Scheme.{u}} (g : Y ⟶ Z)
    (N : Z.Modules) :
    letI : Algebra (Z.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x)) :=
      (g.stalkMap (f x)).hom.toAlgebra
    letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    letI : Algebra (Z.presheaf.stalk (g (f x))) (X.presheaf.stalk x) :=
      ((f ≫ g).stalkMap x).hom.toAlgebra
    haveI : IsScalarTower (Z.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x))
        (X.presheaf.stalk x) :=
      IsScalarTower.of_algebraMap_eq fun z ↦
        ConcreteCategory.congr_hom (Scheme.Hom.stalkMap_comp f g x) z
    (((pullbackComp f g).inv.app N).stalkMap x).comp (pullbackStalkComparison (f ≫ g) N x) =
      (pullbackStalkComparison f ((pullback g).obj N) x).comp
        (((pullbackStalkComparison g N (f x)).baseChange (X.presheaf.stalk x)).comp
          (TensorProduct.AlgebraTensorModule.cancelBaseChange
            (Z.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x))
            (X.presheaf.stalk x) (X.presheaf.stalk x)
            (N.presheaf.stalk (g (f x)))).symm.toLinearMap) := by
  let _ : Algebra (Z.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x)) :=
    (g.stalkMap (f x)).hom.toAlgebra
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  let _ : Algebra (Z.presheaf.stalk (g (f x))) (X.presheaf.stalk x) :=
    ((f ≫ g).stalkMap x).hom.toAlgebra
  have _ : IsScalarTower (Z.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x))
      (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun z ↦
      ConcreteCategory.congr_hom (Scheme.Hom.stalkMap_comp f g x) z
  let Cod := ((pullback g ⋙ pullback f).obj N).presheaf.stalk x
  let _ : Module (Z.presheaf.stalk (g (f x))) Cod :=
    Module.compHom Cod (algebraMap (Z.presheaf.stalk (g (f x))) (X.presheaf.stalk x))
  have _ : IsScalarTower (Z.presheaf.stalk (g (f x))) (X.presheaf.stalk x) Cod :=
    IsScalarTower.of_compHom _ _ _
  refine TensorProduct.AlgebraTensorModule.ext (R := Z.presheaf.stalk (g (f x)))
    (N := N.presheaf.stalk (g (f x))) fun a s ↦ ?_
  obtain ⟨U, hx, n, rfl⟩ := TopCat.Presheaf.exists_germ_eq N.presheaf s
  have hL := (stalkMap_pullbackStalkComparison_tmul_germ (f ≫ g) N x
    ((pullbackComp f g).inv.app N) a U hx n).trans
    (congrArg (fun t ↦ a • ((pullback f).obj ((pullback g).obj N)).presheaf.germ
      ((f ≫ g) ⁻¹ᵁ U) x hx t) (g.pullbackSections_comp N U f n))
  have hc := TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul
    (Z.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
    a (N.presheaf.germ U (g (f x)) hx n)
  have hR := (congrArg (fun t ↦ pullbackStalkComparison f ((pullback g).obj N) x
      (((pullbackStalkComparison g N (f x)).baseChange (X.presheaf.stalk x)) t)) hc).trans
    ((congrArg (pullbackStalkComparison f ((pullback g).obj N) x)
      ((pullbackStalkComparison g N (f x)).baseChange_tmul a _)).trans
      ((congrArg (fun t ↦ pullbackStalkComparison f ((pullback g).obj N) x (a ⊗ₜ t))
        (pullbackStalkComparison_one_tmul_germ g N (f x) U hx n)).trans
        (pullbackStalkComparison_tmul_germ f ((pullback g).obj N) x a (g ⁻¹ᵁ U) hx
          (g.pullbackSections N U n))))
  exact hL.trans hR.symm
attribute [local instance] RingHomInvPair.of_ringEquiv
private theorem bijective_one_tmul_of_isIso {R₀ A₀ : CommRingCat.{u}} (ρ : R₀ ⟶ A₀) [IsIso ρ]
    (M₀ : Type u) [AddCommGroup M₀] [Module R₀ M₀] :
    letI : Algebra R₀ A₀ := ρ.hom.toAlgebra
    Function.Bijective (fun m : M₀ ↦ (1 : A₀) ⊗ₜ[R₀] m) := by
  let _ : Algebra R₀ A₀ := ρ.hom.toAlgebra
  have h₁ (r : R₀) : (inv ρ).hom (ρ.hom r) = r := ConcreteCategory.congr_hom (IsIso.hom_inv_id ρ) r
  have h₂ (a : A₀) : ρ.hom ((inv ρ).hom a) = a := ConcreteCategory.congr_hom (IsIso.inv_hom_id ρ) a
  let ρI : A₀ →ₗ[R₀] R₀ :=
    { toFun := (inv ρ).hom
      map_add' := _root_.map_add _
      map_smul' r a := (map_mul (inv ρ).hom (ρ.hom r) a).trans
        (congrArg (· * (inv ρ).hom a) (h₁ r)) }
  let g : A₀ ⊗[R₀] M₀ →ₗ[R₀] M₀ :=
    (TensorProduct.lid R₀ M₀).toLinearMap.comp (TensorProduct.map ρI .id)
  refine Function.bijective_iff_has_inverse.mpr ⟨g,
    fun m ↦ (congrArg (· • m) (map_one (inv ρ).hom)).trans (one_smul R₀ m), fun t ↦ ?_⟩
  induction t using TensorProduct.inductionOn with
  | tmul a m =>
    exact (TensorProduct.smul_tmul ((inv ρ).hom a) (1 : A₀) m).symm.trans
      (congrArg (· ⊗ₜ[R₀] m) ((mul_one (ρ.hom ((inv ρ).hom a))).trans (h₂ a)))
  | add u v hu hv =>
    exact (congrArg (fun m ↦ (1 : A₀) ⊗ₜ[R₀] m) (g.map_add u v)).trans
      ((TensorProduct.tmul_add (1 : A₀) (g u) (g v)).trans (congrArg₂ (· + ·) hu hv))

/-- Semilinear stalk equivalence `M_{f(x)} ≃ₛₗ[f.stalkMap x] (f^* M)_x` for an open immersion. -/
def pullbackStalkEquivOfIsOpenImmersion [IsOpenImmersion f] :
    M.presheaf.stalk (f x) ≃ₛₗ[
      ((asIso (f.stalkMap x)).commRingCatIsoToRingEquiv :
        Y.presheaf.stalk (f x) →+* X.presheaf.stalk x)]
      ((pullback f).obj M).presheaf.stalk x :=
  letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  LinearEquiv.ofBijective
    { toFun m := pullbackStalkComparison f M x ((1 : X.presheaf.stalk x) ⊗ₜ m)
      map_add' m₁ m₂ := by rw [TensorProduct.tmul_add, map_add]
      map_smul' r m := by
        have hr1 : r • (1 : X.presheaf.stalk x) = (f.stalkMap x).hom r • (1 : X.presheaf.stalk x) :=
          (Algebra.smul_def r (1 : X.presheaf.stalk x)).trans
            (smul_eq_mul ((f.stalkMap x).hom r) 1).symm
        have htmul : (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x)] (r • m) =
            (f.stalkMap x).hom r • ((1 : X.presheaf.stalk x) ⊗ₜ m) :=
          (TensorProduct.smul_tmul r (1 : X.presheaf.stalk x) m).symm.trans
            ((congrArg (· ⊗ₜ[Y.presheaf.stalk (f x)] m) hr1).trans
              (TensorProduct.smul_tmul' ((f.stalkMap x).hom r) 1 m))
        have hcoe : (((asIso (f.stalkMap x)).commRingCatIsoToRingEquiv :
            Y.presheaf.stalk (f x) →+* X.presheaf.stalk x) r) = (f.stalkMap x).hom r := by
          simp [Iso.commRingCatIsoToRingEquiv]
        rw [hcoe]
        exact (congrArg (pullbackStalkComparison f M x) htmul).trans
          (_root_.map_smul (pullbackStalkComparison f M x) ((f.stalkMap x).hom r) _) }
    ((pullbackStalkComparison_bijective f M x).comp
      (bijective_one_tmul_of_isIso (f.stalkMap x) (M.presheaf.stalk (f x))))
@[simp] theorem pullbackStalkEquivOfIsOpenImmersion_germ [IsOpenImmersion f] (U : Y.Opens)
    (hx : f x ∈ U) (m : Γ(M, U)) :
    pullbackStalkEquivOfIsOpenImmersion f M x (M.presheaf.germ U (f x) hx m) =
      ((pullback f).obj M).presheaf.germ (f ⁻¹ᵁ U) x hx (f.pullbackSections M U m) :=
  pullbackStalkComparison_one_tmul_germ f M x U hx m
end AlgebraicGeometry.Scheme.Modules
end
