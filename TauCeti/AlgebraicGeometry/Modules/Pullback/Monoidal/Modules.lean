/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pullback.Monoidal
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Identity
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Stalk
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Stalk

/-!
# Strong symmetric monoidal pullback on `Scheme.Modules`

Equips `Scheme.Modules.pullback f` with `Functor.Monoidal` and `Functor.Braided` instances for
arbitrary `f : X ⟶ Y` (`pullbackTensorIso`), proves `pullbackId`, `pullbackComp`, and
`pullbackCongr` are monoidal, and relates `δ` on stalks to `distribBaseChange` (Tag 01CD).
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- At every point `x : X`, the stalk map of `δ : f^* (M ⊗ N) ⟶ f^* M ⊗ f^* N` is bijective. -/
@[stacks 01CD] theorem bijective_stalkMap_pullback_δ (M N : Y.Modules) (x : X) :
    Function.Bijective ((Functor.OplaxMonoidal.δ (pullback f) M N).stalkMap x) :=
  _root_.SheafOfModules.bijective_stalkMap_pullback_δ f.base f.toRingCatSheafHom M N x

/-- The oplax tensor comparison `δ : f^* (M ⊗ N) ⟶ f^* M ⊗ f^* N` is an isomorphism for arbitrary
`𝒪_Y`-modules `M` and `N`. -/
@[stacks 01CD]
instance isIso_pullback_δ (M N : Y.Modules) : IsIso (Functor.OplaxMonoidal.δ (pullback f) M N) :=
  (Hom.isIso_iff_stalkMap_bijective _).mpr (bijective_stalkMap_pullback_δ f M N)

/-- The canonical isomorphism `f^* (M ⊗ N) ≅ f^* M ⊗ f^* N` for arbitrary `𝒪_Y`-modules. -/
@[stacks 01CD] def pullbackTensorIso (M N : Y.Modules) :
    (pullback f).obj (M ⊗ N) ≅ (pullback f).obj M ⊗ (pullback f).obj N :=
  asIso (Functor.OplaxMonoidal.δ (pullback f) M N)
@[simp] theorem pullbackTensorIso_hom (M N : Y.Modules) :
    (pullbackTensorIso f M N).hom = Functor.OplaxMonoidal.δ (pullback f) M N := (rfl)
theorem pullbackTensorIso_inv (M N : Y.Modules) :
    (pullbackTensorIso f M N).inv = inv (Functor.OplaxMonoidal.δ (pullback f) M N) := (rfl)

/-- Naturality of `(pullbackTensorIso f M N).hom` in both arguments. -/
@[reassoc]
theorem pullbackTensorIso_hom_naturality {M M' N N' : Y.Modules} (α : M ⟶ M') (β : N ⟶ N') :
    (pullback f).map (α ⊗ₘ β) ≫ (pullbackTensorIso f M' N').hom =
      (pullbackTensorIso f M N).hom ≫ ((pullback f).map α ⊗ₘ (pullback f).map β) :=
  (Functor.OplaxMonoidal.δ_natural (pullback f) α β).symm

/-- Pullback of `𝒪_Y`-modules along `f : X ⟶ Y` is strong monoidal. -/
@[stacks 01CD]
instance pullbackMonoidal : (pullback f).Monoidal := Functor.Monoidal.ofOplaxMonoidal (pullback f)
theorem pullback_μ (M N : Y.Modules) :
    Functor.LaxMonoidal.μ (pullback f) M N = inv (Functor.OplaxMonoidal.δ (pullback f) M N) :=
  IsIso.eq_inv_of_hom_inv_id (Functor.Monoidal.δ_μ (pullback f) M N)
@[simp] theorem pullback_ε : Functor.LaxMonoidal.ε (pullback f) = (pullbackObjUnitIso f).inv :=
  (Iso.comp_hom_eq_id (pullbackObjUnitIso f)).mp
    ((congrArg (_ ≫ ·) (pullback_η f).symm).trans (Functor.Monoidal.ε_η (pullback f)))

/-- Naturality of `(pullbackTensorIso f M N).inv` in both arguments. -/
@[reassoc]
theorem pullbackTensorIso_inv_naturality {M M' N N' : Y.Modules} (α : M ⟶ M') (β : N ⟶ N') :
    ((pullback f).map α ⊗ₘ (pullback f).map β) ≫ (pullbackTensorIso f M' N').inv =
      (pullbackTensorIso f M N).inv ≫ (pullback f).map (α ⊗ₘ β) := by
  rw [pullbackTensorIso_inv, pullbackTensorIso_inv, ← pullback_μ, ← pullback_μ]
  exact Functor.LaxMonoidal.μ_natural (pullback f) α β

/-- Pullback of `𝒪_Y`-modules along `f : X ⟶ Y` is strong symmetric monoidal. -/
instance pullbackBraided : (pullback f).Braided where
  toMonoidal := pullbackMonoidal f
  braided M N := by
    rw [← cancel_epi (Functor.OplaxMonoidal.δ (pullback f) M N),
      ← cancel_mono (Functor.OplaxMonoidal.δ (pullback f) N M),
      Functor.Monoidal.δ_μ_assoc, Category.assoc, Category.assoc, Functor.Monoidal.μ_δ,
      Category.comp_id]
    exact pullback_map_braiding_hom_comp_δ f M N

/-- Mathlib's identity isomorphism `pullbackId X : pullback (𝟙 X) ≅ 𝟭 X.Modules` is monoidal. -/
instance isMonoidal_pullbackId_hom (X : Scheme.{u}) :
    NatTrans.IsMonoidal (pullbackId X).hom where
  unit := by rw [Functor.LaxMonoidal.id_ε, pullback_ε, ← pullbackObjUnitIso_id, Iso.inv_hom_id]
  tensor M N := by
    rw [← cancel_epi (Functor.OplaxMonoidal.δ (pullback (𝟙 X)) M N),
      Functor.Monoidal.δ_μ_assoc, Functor.LaxMonoidal.id_μ, Category.comp_id]
    exact (pullback_id_δ X M N).symm

/-- Mathlib's composition isomorphism
`pullbackComp f g : pullback g ⋙ pullback f ≅ pullback (f ≫ g)` is monoidal. -/
instance isMonoidal_pullbackComp_hom {Z : Scheme.{u}} (g : Y ⟶ Z) :
    NatTrans.IsMonoidal (pullbackComp f g).hom where
  unit := by
    rw [Functor.LaxMonoidal.comp_ε, Category.assoc, pullback_ε, pullback_ε, pullback_ε]
    exact pullbackObjUnitIso_inv_comp f g
  tensor M N := by
    rw [Functor.LaxMonoidal.comp_μ, Category.assoc, pullback_μ, pullback_μ, pullback_μ]
    exact inv_δ_comp_pullbackComp_hom_app f g M N

/-- The pullback congruence isomorphism `pullbackCongr h` for `h : f = g` is monoidal. -/
instance isMonoidal_pullbackCongr_hom {f g : X ⟶ Y} (h : f = g) :
    NatTrans.IsMonoidal (pullbackCongr h).hom := by
  subst h; dsimp [pullbackCongr]; infer_instance

/-- At every point `x : X`, the stalk map of `δ (pullback f) M N` intertwines
`pullbackStalkComparison` and `tensorStalkComparison` via `distribBaseChange`. -/
theorem tensorStalkComparison_stalkMap_pullback_δ (M N : Y.Modules) (x : X) :
    letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    (tensorStalkComparison ((pullback f).obj M) ((pullback f).obj N) x).comp
        (((Functor.OplaxMonoidal.δ (pullback f) M N).stalkMap x).comp
          (pullbackStalkComparison f (M ⊗ N) x)) =
      (TensorProduct.map (pullbackStalkComparison f M x)
          (pullbackStalkComparison f N x)).comp
        ((TensorProduct.AlgebraTensorModule.distribBaseChange
            (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
            (M.presheaf.stalk (f x)) (N.presheaf.stalk (f x))).toLinearMap.comp
          ((tensorStalkComparison M N (f x)).baseChange (X.presheaf.stalk x))) := by
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  let e := (tensorStalkEquiv M N (f x)).symm
  let tX := tensorStalkComparison ((pullback f).obj M) ((pullback f).obj N) x
  let pMap := TensorProduct.map (pullbackStalkComparison f M x) (pullbackStalkComparison f N x)
  let L := tX.comp (((Functor.OplaxMonoidal.δ (pullback f) M N).stalkMap x).comp
    (pullbackStalkComparison f (M ⊗ N) x))
  let R := pMap.comp ((TensorProduct.AlgebraTensorModule.distribBaseChange
      (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
      (M.presheaf.stalk (f x)) (N.presheaf.stalk (f x))).toLinearMap.comp
    ((tensorStalkComparison M N (f x)).baseChange (X.presheaf.stalk x)))
  let Cod := ((pullback f).obj M).presheaf.stalk x ⊗[X.presheaf.stalk x]
    ((pullback f).obj N).presheaf.stalk x
  let _ : Module (Y.presheaf.stalk (f x)) Cod :=
    Module.compHom Cod (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x))
  have _ : IsScalarTower (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) Cod :=
    IsScalarTower.of_compHom _ _ _
  change L = R
  refine TensorProduct.AlgebraTensorModule.ext fun a s ↦ ?_
  obtain ⟨t, rfl⟩ := e.surjective s
  induction t using TensorProduct.inductionOn with
  | tmul u v =>
    obtain ⟨U, hxU, m₀, hu⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf u
    obtain ⟨V, hVU, hxV, n₀, hv⟩ := TopCat.Presheaf.exists_le_germ_eq N.presheaf v hxU
    let m₁ : Γ(M, V) := M.presheaf.map (homOfLE hVU).op m₀
    let gM := M.presheaf.germ V (f x) hxV m₁
    let gN := N.presheaf.germ V (f x) hxV n₀
    have hu' : u = gM := hu.symm.trans (M.presheaf.germ_res_apply (homOfLE hVU) (f x) hxV m₀).symm
    have h₁ := congrArg (fun z ↦ L (a ⊗ₜ z)) (tensorStalkEquiv_symm_tmul_germ M N (f x) V hxV m₁ n₀)
    have h₂ := (congrArg tX (stalkMap_pullbackStalkComparison_tmul_germ f (M ⊗ N) x
        (Functor.OplaxMonoidal.δ (pullback f) M N) a V hxV _)).trans
      ((_root_.map_smul tX a _).trans (congrArg (a • ·)
        ((congrArg (fun s ↦ tX
          (((pullback f).obj M ⊗ (pullback f).obj N).presheaf.germ (f ⁻¹ᵁ V) x hxV s))
          (f.δ_app_pullbackSections_μ M V N m₁ n₀)).trans
          (tensorStalkComparison_germ_μ_tmul ((pullback f).obj M) ((pullback f).obj N) x
            (f ⁻¹ᵁ V) hxV _ _))))
    have he : tensorStalkComparison M N (f x) (e (gM ⊗ₜ gN)) = gM ⊗ₜ gN :=
      (tensorStalkEquiv_apply M N (f x) _).symm.trans
        ((tensorStalkEquiv M N (f x)).apply_symm_apply _)
    have hR := (congrArg (fun z ↦ pMap (TensorProduct.AlgebraTensorModule.distribBaseChange
          (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) _ _ z))
        ((tensorStalkComparison M N (f x)).baseChange_tmul a (e (gM ⊗ₜ gN)))).trans
      ((congrArg (fun z ↦ pMap (TensorProduct.AlgebraTensorModule.distribBaseChange
          (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) _ _ (a ⊗ₜ z))) he).trans
        ((congrArg pMap (TensorProduct.AlgebraTensorModule.distribBaseChange_tmul
          (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) gM gN a)).trans
          ((TensorProduct.map_tmul (pullbackStalkComparison f M x)
              (pullbackStalkComparison f N x) _ _).trans
            ((congrArg₂ (· ⊗ₜ ·) (pullbackStalkComparison_tmul_germ f M x a V hxV m₁)
              (pullbackStalkComparison_one_tmul_germ f N x V hxV n₀)).trans
              (TensorProduct.smul_tmul' a _ _)))))
    exact (congrArg (fun z ↦ L (a ⊗ₜ e z)) (congrArg₂ (· ⊗ₜ ·) hu' hv.symm)).trans
      ((h₁.trans h₂).trans (hR.symm.trans
        (congrArg (fun z ↦ R (a ⊗ₜ e z)) (congrArg₂ (· ⊗ₜ ·) hu' hv.symm)).symm))
  | add z w hz hw =>
    have hLz := (congrArg (fun q ↦ L (a ⊗ₜ q)) (e.map_add z w)).trans
      ((congrArg L (TensorProduct.tmul_add a _ _)).trans (L.map_add _ _))
    have hRz := (congrArg (fun q ↦ R (a ⊗ₜ q)) (e.map_add z w)).trans
      ((congrArg R (TensorProduct.tmul_add a _ _)).trans (R.map_add _ _))
    exact hLz.trans ((congrArg₂ (· + ·) hz hw).trans hRz.symm)
end AlgebraicGeometry.Scheme.Modules
end
