/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import TauCeti.Algebra.Category.ModuleCat.Colimits
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.Evaluation
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct

/-!
# The sheaf associated with a tensor product of modules

For a commutative ring `R`, the functor `M ↦ M~` from `R`-modules to `𝒪_{Spec R}`-modules is
strong monoidal: `(M ⊗_R N)~ ≅ M~ ⊗ N~` naturally in `M` and `N`, and `R~ = 𝒪_{Spec R}`.

The comparison maps come from adjunction. Taking global sections is lax monoidal: it is taking
sections over `⊤` of the underlying presheaf of modules, whose tensor product is computed
sectionwise, followed by restriction of scalars along `R ≅ Γ(Spec R, ⊤)`. Its left adjoint
`M ↦ M~` is therefore oplax monoidal. Its unit comparison is the identification of `R~` with
`𝒪_{Spec R}`. For a fixed `M`, the tensor comparison
`(M ⊗_R N)~ ⟶ M~ ⊗ N~` is a natural transformation between functors of `N` which preserve
colimits, since `M ↦ M~` and both tensor products are left adjoints. By unitality it is invertible
at `N = R`, hence everywhere (`TauCeti.ModuleCat.isIso_of_isIso_app_self`).

## Main declarations

* `TauCeti.AlgebraicGeometry.tildeMonoidal`: the functor `M ↦ M~` is monoidal;
* `TauCeti.AlgebraicGeometry.tilde_ε` and `TauCeti.AlgebraicGeometry.tilde_η`: its unit
  comparisons are the identification `AlgebraicGeometry.tildeSelf` of `R~` with `𝒪_{Spec R}`;
* `TauCeti.AlgebraicGeometry.tilde_μ_app_top_toOpen`: on global sections, the tensor comparison
  sends the product of the sections `m` and `n` to the section `m ⊗ₜ n`.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2 (b)
-/

public section

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal Functor.OplaxMonoidal

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {R : CommRingCat.{u}}

/-- The inclusion of `𝒪_{Spec R}`-modules into presheaves of modules, with its target written as
presheaves of modules over the presheaf of commutative rings of `Spec R`. -/
private def forgetSpec :
    (Spec R).Modules ⥤ PresheafOfModulesOfCommRing.{u} (Spec R).presheaf :=
  _root_.SheafOfModules.forget _

private instance : (forgetSpec (R := R)).LaxMonoidal :=
  SheafOfModules.forgetLaxMonoidal (Spec R).sheaf

/-- Global sections of `𝒪_{Spec R}`-modules, as a composite of lax monoidal functors: sections
over `⊤` of the underlying presheaf of modules, with scalars restricted along `R ≅ Γ(Spec R, ⊤)`.
-/
private def globalSections : (Spec R).Modules ⥤ ModuleCat.{u} R :=
  forgetSpec ⋙ PresheafOfModulesOfCommRing.evaluation (R := (Spec R).presheaf) (.op ⊤) ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom

private instance : (globalSections (R := R)).LaxMonoidal := by
  unfold globalSections
  infer_instance

private lemma globalSections_ε_apply (r : R) :
    ε (globalSections (R := R)) r = (Scheme.ΓSpecIso R).inv r := by
  have h : ε (forgetSpec (R := R)) = 𝟙 _ := SheafOfModules.forget_ε (Spec R).sheaf
  dsimp only [globalSections]
  simp only [Functor.LaxMonoidal.comp_ε, h]
  exact ModuleCat.restrictScalars_η (Scheme.ΓSpecIso R).inv.hom r

private instance : IsIso (ε (globalSections (R := R))) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  have h := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv
  exact ⟨fun a b hab ↦ h.1 (by rwa [globalSections_ε_apply, globalSections_ε_apply] at hab),
    fun y ↦ (h.2 y).imp fun a ha ↦ (globalSections_ε_apply a).trans ha⟩

/-- Mathlib's global sections functor agrees with `globalSections`: both are the sections over
`⊤`, with the same action of `R`. -/
private def moduleSpecΓFunctorIso : moduleSpecΓFunctor (R := R) ≅ globalSections :=
  NatIso.ofComponents (fun M ↦
    let e : moduleSpecΓFunctor.obj M ≃ₗ[R] globalSections.obj M :=
      { AddEquiv.refl _ with
        map_smul' := fun r x ↦ by
          -- `moduleSpecΓFunctor` lets `R` act through the restriction of `Γ(Spec R, ⊤)` along the
          -- endomorphism of `⊤` given by initiality, which is the identity.
          have h : ((Spec R).ringCatSheaf.obj.map
              ((initialOpOfTerminal isTerminalTop).to (.op ⊤))).hom = RingHom.id _ := by
            rw [IsInitial.to_self, CategoryTheory.Functor.map_id]
            rfl
          exact congrArg (fun f : _ →+* _ ↦ f ((Scheme.ΓSpecIso R).inv.hom r) •
            (show M.val.obj (.op ⊤) from x)) h }
    e.toModuleIso)
    (fun _ ↦ by ext; rfl)

/-- The tilde--global sections adjunction, with right adjoint the lax monoidal `globalSections`. -/
private def tildeAdjunction : tilde.functor R ⊣ globalSections :=
  tilde.adjunction.ofNatIsoRight moduleSpecΓFunctorIso

private lemma isIso_η :
    letI := (tildeAdjunction (R := R)).leftAdjointOplaxMonoidal
    IsIso (η (tilde.functor R)) := by
  let := (tildeAdjunction (R := R)).leftAdjointOplaxMonoidal
  rw [Adjunction.leftAdjointOplaxMonoidal_η, tildeAdjunction,
    Adjunction.homEquiv_ofNatIsoRight_symm_apply, Adjunction.homEquiv_counit]
  have : IsIso (tilde.adjunction.counit.app (𝟙_ (Spec R).Modules)) :=
    inferInstanceAs (IsIso (Scheme.Modules.fromTildeΓ (_root_.SheafOfModules.unit _)))
  infer_instance

private lemma isIso_δ (M N : ModuleCat.{u} R) :
    letI := (tildeAdjunction (R := R)).leftAdjointOplaxMonoidal
    IsIso (δ (tilde.functor R) M N) := by
  let := (tildeAdjunction (R := R)).leftAdjointOplaxMonoidal
  have := isIso_η (R := R)
  -- By unitality, the comparison is invertible when the second factor is the unit `R`.
  have hunit (M : ModuleCat.{u} R) : IsIso (δ (tilde.functor R) M (𝟙_ _)) := by
    have : IsIso (δ (tilde.functor R) M (𝟙_ _) ≫
        (tilde.functor R).obj M ◁ η (tilde.functor R) ≫ (ρ_ _).hom) := by
      rw [Functor.OplaxMonoidal.right_unitality_hom]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((tilde.functor R).obj M ◁ η (tilde.functor R) ≫ (ρ_ _).hom)
  -- As a transformation of colimit-preserving functors of the second factor, it is invertible.
  let α : tensorLeft M ⋙ tilde.functor R ⟶
      tilde.functor R ⋙ tensorLeft ((tilde.functor R).obj M) :=
    { app N := δ (tilde.functor R) M N
      naturality _ _ g := (δ_natural_right (tilde.functor R) M g).symm }
  have : IsIso (α.app (ModuleCat.of R R)) := hunit M
  have := ModuleCat.isIso_of_isIso_app_self α
  exact NatIso.isIso_app_of_isIso α N

/-- The functor `M ↦ M~` from `R`-modules to `𝒪_{Spec R}`-modules is monoidal:
`(M ⊗_R N)~ ≅ M~ ⊗ N~` and `R~ = 𝒪_{Spec R}`. Its inverse comparison maps are the mates, under
the tilde--global sections adjunction, of the lax monoidal structure of global sections. -/
-- A definition rather than an `instance`, whose body would be exported, so that its body may use
-- the private adjunction `tildeAdjunction`.
@[instance_reducible]
def tildeMonoidal : (tilde.functor R).Monoidal :=
  letI := (tildeAdjunction (R := R)).leftAdjointOplaxMonoidal
  haveI := isIso_η (R := R)
  haveI := isIso_δ (R := R)
  Functor.Monoidal.ofOplaxMonoidal _

attribute [instance] tildeMonoidal

/-- The inverse unit comparison `R~ ⟶ 𝒪_{Spec R}` of `M ↦ M~` is the identification
`AlgebraicGeometry.tildeSelf` of `R~` with `𝒪_{Spec R}`. -/
@[simp]
theorem tilde_η : η (tilde.functor R) = (tildeSelf (R := R)).hom := by
  -- By construction, `η` is the mate of the unit map of `globalSections`.
  apply (tildeAdjunction.homEquiv _ _).injective
  rw [show η (tilde.functor R) = (tildeAdjunction.homEquiv _ _).symm (ε globalSections) from rfl,
    Equiv.apply_symm_apply]
  ext
  rw [globalSections_ε_apply]
  -- Both sides are the image of `1` in `Γ(Spec R, ⊤)`.
  rfl

/-- The unit comparison `𝒪_{Spec R} ⟶ R~` of `M ↦ M~` is the identification
`AlgebraicGeometry.tildeSelf` of `R~` with `𝒪_{Spec R}`. -/
@[simp]
theorem tilde_ε : ε (tilde.functor R) = (tildeSelf (R := R)).inv := by
  refine Iso.inv_ext' ?_
  rw [← tilde_η]
  exact Functor.Monoidal.η_ε _

private lemma globalSections_μ_apply (A B : (Spec R).Modules) (a : globalSections.obj A)
    (b : globalSections.obj B) :
    μ globalSections A B (a ⊗ₜ b) =
      (μ forgetSpec A B).app' (.op ⊤) ((show A.val.obj (.op ⊤) from a) ⊗ₜ
        (show B.val.obj (.op ⊤) from b)) := by
  -- The tensor map of `globalSections` is that of restriction of scalars, which is the identity
  -- on pure tensors, followed by the tensor map of `forgetSpec` on sections over `⊤`.
  exact congrArg (fun x ↦ (μ forgetSpec A B).app' (.op ⊤) x)
    (ModuleCat.restrictScalars_μ_tmul (Scheme.ΓSpecIso R).inv.hom _ _ a b)

/-- On global sections, the tensor comparison `M~ ⊗ N~ ⟶ (M ⊗_R N)~` of `M ↦ M~` sends the
product of the sections `m` and `n` to the section `m ⊗ₜ n`. Here the product of two sections is
their image under the tensor map of the inclusion of sheaves of modules into presheaves of modules,
whose tensor product is computed sectionwise. -/
theorem tilde_μ_app_top_toOpen (M N : ModuleCat.{u} R) (m : M) (n : N) :
    letI F : (Spec R).Modules ⥤ PresheafOfModulesOfCommRing.{u} (Spec R).presheaf :=
      _root_.SheafOfModules.forget _
    letI : F.LaxMonoidal := SheafOfModules.forgetLaxMonoidal (Spec R).sheaf
    (F.map (μ (tilde.functor R) M N)).app' (.op ⊤) ((μ F (tilde M) (tilde N)).app' (.op ⊤)
        (tilde.toOpen M ⊤ m ⊗ₜ tilde.toOpen N ⊤ n)) =
      tilde.toOpen (M ⊗ N) ⊤ (m ⊗ₜ n) := by
  -- The inverse comparison `δ` is the mate of the tensor map of `globalSections`.
  have h : tildeAdjunction.unit.app (M ⊗ N) ≫ globalSections.map (δ (tilde.functor R) M N) =
      (tildeAdjunction.unit.app M ⊗ₘ tildeAdjunction.unit.app N) ≫ μ globalSections _ _ :=
    (tildeAdjunction.homEquiv_unit _ _ _).symm.trans
      ((tildeAdjunction.homEquiv _ _).apply_symm_apply _)
  have key : globalSections.map (δ (tilde.functor R) M N) (tildeAdjunction.unit.app (M ⊗ N)
      (m ⊗ₜ n)) =
      (μ forgetSpec (tilde M) (tilde N)).app' (.op ⊤)
        (tilde.toOpen M ⊤ m ⊗ₜ tilde.toOpen N ⊤ n) := by
    have hA := ConcreteCategory.congr_hom h (m ⊗ₜ n)
    simp only [ConcreteCategory.comp_apply] at hA
    exact hA.trans (globalSections_μ_apply (tilde M) (tilde N) (tilde.toOpen M ⊤ m)
      (tilde.toOpen N ⊤ n))
  -- The goal is stated with `SheafOfModules.forget`, which is `forgetSpec` with the same lax
  -- monoidal structure.
  change (forgetSpec.map (μ (tilde.functor R) M N)).app' (.op ⊤)
    ((μ forgetSpec (tilde M) (tilde N)).app' (.op ⊤)
      (tilde.toOpen M ⊤ m ⊗ₜ tilde.toOpen N ⊤ n)) = _
  rw [← key]
  -- It remains to see that `μ` undoes `δ`. On underlying sections, `globalSections.map f` is
  -- `(forgetSpec.map f).app' (.op ⊤)`, and the unit of `tildeAdjunction` is `tilde.toOpen`.
  change globalSections.map (μ (tilde.functor R) M N)
    (globalSections.map (δ (tilde.functor R) M N) (tildeAdjunction.unit.app (M ⊗ N) (m ⊗ₜ n))) =
      tildeAdjunction.unit.app (M ⊗ N) (m ⊗ₜ n)
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp, Functor.Monoidal.δ_μ,
    CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

end

end AlgebraicGeometry

end TauCeti
