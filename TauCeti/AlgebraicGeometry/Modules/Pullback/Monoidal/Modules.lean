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

For an arbitrary morphism of schemes `f : X ⟶ Y` and arbitrary `𝒪_Y`-modules `M` and `N`, the
canonical oplax tensor comparison `δ : f^* (M ⊗ N) ⟶ f^* M ⊗ f^* N` of `Scheme.Modules.pullback f`
is an isomorphism, with no quasi-coherence, flatness, or finiteness hypotheses on `M`, `N`, or `f`.

Consequently, `Scheme.Modules.pullback f : Y.Modules ⥤ X.Modules` carries a canonical strong
symmetric monoidal structure (`AlgebraicGeometry.Scheme.Modules.pullbackMonoidal` and
`AlgebraicGeometry.Scheme.Modules.pullbackBraided`), and the pseudofunctorial coherence
isomorphisms `pullbackId`, `pullbackComp`, and `pullbackCongr` are monoidal natural isomorphisms.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.bijective_stalkMap_pullback_δ` and
  `AlgebraicGeometry.Scheme.Modules.isIso_pullback_δ`: stalkwise bijectivity and invertibility of
  `Functor.OplaxMonoidal.δ (pullback f) M N` for arbitrary `M, N : Y.Modules`;
* `AlgebraicGeometry.Scheme.Modules.pullbackTensorIso`: the canonical isomorphism
  `f^* (M ⊗ N) ≅ f^* M ⊗ f^* N`;
* `AlgebraicGeometry.Scheme.Modules.pullbackMonoidal` and
  `AlgebraicGeometry.Scheme.Modules.pullbackBraided`: the strong symmetric monoidal structure on
  `Scheme.Modules.pullback f`;
* `AlgebraicGeometry.Scheme.Modules.isMonoidal_pullbackId_hom`,
  `AlgebraicGeometry.Scheme.Modules.isMonoidal_pullbackComp_hom`, and
  `AlgebraicGeometry.Scheme.Modules.isMonoidal_pullbackCongr_hom`: monoidal compatibility of the
  identity, composition, and congruence isomorphisms of module pullback;
* `AlgebraicGeometry.Scheme.Modules.tensorStalkComparison_stalkMap_pullback_δ`: compatibility of
  `δ (pullback f) M N` on stalks with `pullbackStalkComparison`, `tensorStalkComparison`, and
  `TensorProduct.AlgebraTensorModule.distribBaseChange`.

## References

* [The Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD).
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

private theorem algebraTensor_ext' {R₀ A₀ N₀ P₀ : Type*} [CommRing R₀] [CommRing A₀]
    [Algebra R₀ A₀] [AddCommGroup N₀] [Module R₀ N₀] [AddCommGroup P₀] [Module A₀ P₀]
    {g h : A₀ ⊗[R₀] N₀ →ₗ[A₀] P₀} (H : ∀ a n, g (a ⊗ₜ n) = h (a ⊗ₜ n)) : g = h := by
  let _ : Module R₀ P₀ := Module.compHom P₀ (algebraMap R₀ A₀)
  have _ : IsScalarTower R₀ A₀ P₀ := IsScalarTower.of_compHom R₀ A₀ P₀
  exact LinearMap.restrictScalars_injective R₀ (TensorProduct.ext' fun a n ↦ H a n)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- At every point `x : X`, the stalk map of the oplax tensor comparison
`δ : f^* (M ⊗ N) ⟶ f^* M ⊗ f^* N` is bijective for arbitrary `𝒪_Y`-modules `M` and `N`. -/
@[stacks 01CD]
theorem bijective_stalkMap_pullback_δ (M N : Y.Modules) (x : X) :
    Function.Bijective ((Functor.OplaxMonoidal.δ (pullback f) M N).stalkMap x) :=
  TauCeti.SheafOfModules.bijective_stalkMap_pullback_δ f.base f.toRingCatSheafHom M N x

/-- The oplax tensor comparison `δ : f^* (M ⊗ N) ⟶ f^* M ⊗ f^* N` is an isomorphism for arbitrary
`𝒪_Y`-modules `M` and `N` along any morphism of schemes `f : X ⟶ Y`. -/
@[stacks 01CD]
instance isIso_pullback_δ (M N : Y.Modules) :
    IsIso (Functor.OplaxMonoidal.δ (pullback f) M N) :=
  (Hom.isIso_iff_stalkMap_bijective _).mpr (bijective_stalkMap_pullback_δ f M N)

/-- The canonical isomorphism `f^* (M ⊗ N) ≅ f^* M ⊗ f^* N` for arbitrary `𝒪_Y`-modules `M` and `N`
along any morphism of schemes `f : X ⟶ Y`. -/
@[stacks 01CD]
def pullbackTensorIso (M N : Y.Modules) :
    (pullback f).obj (M ⊗ N) ≅ (pullback f).obj M ⊗ (pullback f).obj N :=
  asIso (Functor.OplaxMonoidal.δ (pullback f) M N)

@[simp]
theorem pullbackTensorIso_hom (M N : Y.Modules) :
    (pullbackTensorIso f M N).hom = Functor.OplaxMonoidal.δ (pullback f) M N :=
  (rfl)

theorem pullbackTensorIso_inv (M N : Y.Modules) :
    (pullbackTensorIso f M N).inv = inv (Functor.OplaxMonoidal.δ (pullback f) M N) :=
  (rfl)

/-- Naturality of `(pullbackTensorIso f M N).hom` with respect to morphisms `α : M ⟶ M'` and
`β : N ⟶ N'`. -/
@[reassoc]
theorem pullbackTensorIso_hom_naturality {M M' N N' : Y.Modules} (α : M ⟶ M') (β : N ⟶ N') :
    (pullback f).map (α ⊗ₘ β) ≫ (pullbackTensorIso f M' N').hom =
      (pullbackTensorIso f M N).hom ≫ ((pullback f).map α ⊗ₘ (pullback f).map β) :=
  (Functor.OplaxMonoidal.δ_natural (pullback f) α β).symm

/-- Pullback of `𝒪_Y`-modules along an arbitrary morphism of schemes `f : X ⟶ Y` is strong
monoidal, with no quasi-coherence or finiteness hypotheses. -/
@[stacks 01CD]
instance pullbackMonoidal : (pullback f).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal (pullback f)

theorem pullback_μ (M N : Y.Modules) :
    Functor.LaxMonoidal.μ (pullback f) M N = inv (Functor.OplaxMonoidal.δ (pullback f) M N) :=
  IsIso.eq_inv_of_hom_inv_id (Functor.Monoidal.δ_μ (pullback f) M N)

@[simp]
theorem pullback_ε :
    Functor.LaxMonoidal.ε (pullback f) = (pullbackObjUnitIso f).inv :=
  (Iso.comp_hom_eq_id (pullbackObjUnitIso f)).mp
    ((congrArg (_ ≫ ·) (pullback_η f).symm).trans (Functor.Monoidal.ε_η (pullback f)))

/-- Naturality of `(pullbackTensorIso f M N).inv` with respect to morphisms `α : M ⟶ M'` and
`β : N ⟶ N'`. -/
@[reassoc]
theorem pullbackTensorIso_inv_naturality {M M' N N' : Y.Modules} (α : M ⟶ M') (β : N ⟶ N') :
    ((pullback f).map α ⊗ₘ (pullback f).map β) ≫ (pullbackTensorIso f M' N').inv =
      (pullbackTensorIso f M N).inv ≫ (pullback f).map (α ⊗ₘ β) := by
  rw [pullbackTensorIso_inv, pullbackTensorIso_inv, ← pullback_μ, ← pullback_μ]
  exact Functor.LaxMonoidal.μ_natural (pullback f) α β

/-- Pullback of `𝒪_Y`-modules along an arbitrary morphism of schemes `f : X ⟶ Y` is strong
symmetric monoidal. -/
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
  unit := by
    rw [Functor.LaxMonoidal.id_ε, pullback_ε, ← pullbackObjUnitIso_id, Iso.inv_hom_id]
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

/-- The pullback congruence isomorphism `pullbackCongr h : pullback f ≅ pullback g` for equal
scheme morphisms `h : f = g` is monoidal. -/
instance isMonoidal_pullbackCongr_hom {f g : X ⟶ Y} (h : f = g) :
    NatTrans.IsMonoidal (pullbackCongr h).hom := by
  subst h
  dsimp [pullbackCongr]
  infer_instance

private theorem stalk_pullback_δ_tmul_germ (M N : Y.Modules) (x : X)
    (a : X.presheaf.stalk x) (V : Y.Opens) (hxV : f x ∈ V)
    (m₁ : Γ(M, V)) (n₀ : Γ(N, V)) :
    letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    tensorStalkComparison ((pullback f).obj M) ((pullback f).obj N) x
        ((Functor.OplaxMonoidal.δ (pullback f) M N).stalkMap x
          (pullbackStalkComparison f (M ⊗ N) x
            (a ⊗ₜ (tensorStalkEquiv M N (f x)).symm
              (M.presheaf.germ V (f x) hxV m₁ ⊗ₜ N.presheaf.germ V (f x) hxV n₀)))) =
      TensorProduct.map (pullbackStalkComparison f M x) (pullbackStalkComparison f N x)
        (TensorProduct.AlgebraTensorModule.distribBaseChange
          (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) _ _
          (a ⊗ₜ tensorStalkComparison M N (f x)
            ((tensorStalkEquiv M N (f x)).symm
              (M.presheaf.germ V (f x) hxV m₁ ⊗ₜ N.presheaf.germ V (f x) hxV n₀)))) := by
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have h₁ := congrArg (fun z ↦ tensorStalkComparison ((pullback f).obj M) ((pullback f).obj N) x
      ((Functor.OplaxMonoidal.δ (pullback f) M N).stalkMap x
        (pullbackStalkComparison f (M ⊗ N) x (a ⊗ₜ z))))
    (tensorStalkEquiv_symm_tmul_germ M N (f x) V hxV m₁ n₀)
  have h₂ := (congrArg (tensorStalkComparison ((pullback f).obj M) ((pullback f).obj N) x)
      (stalkMap_pullbackStalkComparison_tmul_germ f (M ⊗ N) x
        (Functor.OplaxMonoidal.δ (pullback f) M N) a V hxV _)).trans
    ((_root_.map_smul (tensorStalkComparison ((pullback f).obj M) ((pullback f).obj N) x) a _).trans
      (congrArg (a • ·)
        ((congrArg (fun s ↦ tensorStalkComparison ((pullback f).obj M) ((pullback f).obj N) x
          (((pullback f).obj M ⊗ (pullback f).obj N).presheaf.germ (f ⁻¹ᵁ V) x hxV s))
          (f.δ_app_pullbackSections_μ M V N m₁ n₀)).trans
          (tensorStalkComparison_germ_μ_tmul ((pullback f).obj M) ((pullback f).obj N) x
            (f ⁻¹ᵁ V) hxV _ _))))
  have he : tensorStalkComparison M N (f x)
      ((tensorStalkEquiv M N (f x)).symm
        (M.presheaf.germ V (f x) hxV m₁ ⊗ₜ N.presheaf.germ V (f x) hxV n₀)) =
      M.presheaf.germ V (f x) hxV m₁ ⊗ₜ N.presheaf.germ V (f x) hxV n₀ :=
    (tensorStalkEquiv_apply M N (f x) _).symm.trans
      ((tensorStalkEquiv M N (f x)).apply_symm_apply _)
  have hn : pullbackStalkComparison f N x (1 ⊗ₜ N.presheaf.germ V (f x) hxV n₀) =
      ((pullback f).obj N).presheaf.germ (f ⁻¹ᵁ V) x hxV (f.pullbackSections N V n₀) :=
    (pullbackStalkComparison_tmul_germ f N x 1 V hxV n₀).trans (one_smul _ _)
  have hR := (congrArg (fun z ↦ TensorProduct.map
        (pullbackStalkComparison f M x) (pullbackStalkComparison f N x)
        (TensorProduct.AlgebraTensorModule.distribBaseChange
          (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) _ _ (a ⊗ₜ z))) he).trans
    ((congrArg (TensorProduct.map (pullbackStalkComparison f M x) (pullbackStalkComparison f N x))
      (TensorProduct.AlgebraTensorModule.distribBaseChange_tmul
        (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
        (M.presheaf.germ V (f x) hxV m₁) (N.presheaf.germ V (f x) hxV n₀) a)).trans
      ((TensorProduct.map_tmul
          (pullbackStalkComparison f M x) (pullbackStalkComparison f N x) _ _).trans
        ((congrArg₂ (· ⊗ₜ ·) (pullbackStalkComparison_tmul_germ f M x a V hxV m₁) hn).trans
          (TensorProduct.smul_tmul' a _ _))))
  exact (h₁.trans h₂).trans hR.symm

/-- At every point `x : X`, the stalk map of `δ (pullback f) M N` intertwines
`pullbackStalkComparison` and `tensorStalkComparison` via
`TensorProduct.AlgebraTensorModule.distribBaseChange`. -/
theorem tensorStalkComparison_stalkMap_pullback_δ (M N : Y.Modules) (x : X) :
    letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    (tensorStalkComparison ((pullback f).obj M) ((pullback f).obj N) x).comp
        (((Functor.OplaxMonoidal.δ (pullback f) M N).stalkMap x).comp
          (pullbackStalkComparison f (M ⊗ N) x)) =
      (TensorProduct.map
          (pullbackStalkComparison f M x)
          (pullbackStalkComparison f N x)).comp
        ((TensorProduct.AlgebraTensorModule.distribBaseChange
            (Y.presheaf.stalk (f x))
            (X.presheaf.stalk x)
            (M.presheaf.stalk (f x))
            (N.presheaf.stalk (f x))).toLinearMap.comp
          ((tensorStalkComparison M N (f x)).baseChange (X.presheaf.stalk x))) := by
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let e := (tensorStalkEquiv M N (f x)).symm
  let L := (tensorStalkComparison ((pullback f).obj M) ((pullback f).obj N) x).comp
    (((Functor.OplaxMonoidal.δ (pullback f) M N).stalkMap x).comp
      (pullbackStalkComparison f (M ⊗ N) x))
  let R := (TensorProduct.map (pullbackStalkComparison f M x) (pullbackStalkComparison f N x)).comp
    ((TensorProduct.AlgebraTensorModule.distribBaseChange
        (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
        (M.presheaf.stalk (f x)) (N.presheaf.stalk (f x))).toLinearMap.comp
      ((tensorStalkComparison M N (f x)).baseChange (X.presheaf.stalk x)))
  change L = R
  apply algebraTensor_ext'
  intro a s
  obtain ⟨t, rfl⟩ := e.surjective s
  induction t using TensorProduct.inductionOn with
  | tmul u v =>
    obtain ⟨U, hxU, m₀, hu⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf u
    obtain ⟨V, hVU, hxV, n₀, hv⟩ := TopCat.Presheaf.exists_le_germ_eq N.presheaf v hxU
    let m₁ : Γ(M, V) := M.presheaf.map (homOfLE hVU).op m₀
    have hu' : u = M.presheaf.germ V (f x) hxV m₁ :=
      hu.symm.trans (M.presheaf.germ_res_apply (homOfLE hVU) (f x) hxV m₀).symm
    have hR := congrArg (fun z ↦ TensorProduct.map
        (pullbackStalkComparison f M x) (pullbackStalkComparison f N x)
        (TensorProduct.AlgebraTensorModule.distribBaseChange
          (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) _ _ z))
      ((tensorStalkComparison M N (f x)).baseChange_tmul a
        (e (M.presheaf.germ V (f x) hxV m₁ ⊗ₜ N.presheaf.germ V (f x) hxV n₀)))
    exact (congrArg (fun z ↦ L (a ⊗ₜ e z)) (congrArg₂ (· ⊗ₜ ·) hu' hv.symm)).trans
      ((stalk_pullback_δ_tmul_germ f M N x a V hxV m₁ n₀).trans
        (hR.symm.trans
          (congrArg (fun z ↦ R (a ⊗ₜ e z)) (congrArg₂ (· ⊗ₜ ·) hu' hv.symm)).symm))
  | add z w hz hw =>
    have hLz := (congrArg (fun q ↦ L (a ⊗ₜ q)) (e.map_add z w)).trans
      ((congrArg L (TensorProduct.tmul_add a _ _)).trans (L.map_add _ _))
    have hRz := (congrArg (fun q ↦ R (a ⊗ₜ q)) (e.map_add z w)).trans
      ((congrArg R (TensorProduct.tmul_add a _ _)).trans (R.map_add _ _))
    exact hLz.trans ((congrArg₂ (· + ·) hz hw).trans hRz.symm)

end AlgebraicGeometry.Scheme.Modules

end
