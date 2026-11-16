/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Basic
public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Etale
public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.RelativeSpec.BaseChange
public import TauCeti.AlgebraicGeometry.RelativeSpec.Equivalence
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
import TauCeti.AlgebraicGeometry.VectorBundle.Pushforward

/-!
# Formal comparison for finite étale covers

Let `X` be a scheme and `I` a quasi-coherent ideal sheaf on `X`, with formal completion
`X.formalCompletion I` and closed subscheme `V(I)`. Suppose the completion functor from finite
locally free `𝒪_X`-modules to coherent formal modules on `X/V(I)` is fully faithful. Then
pullback of finite étale schemes along any closed immersion `j : X₀ ⟶ X` with kernel `I` — in
particular along `I.subschemeι : I.subscheme ⟶ X` — is fully faithful (Stacks, Lemma 58.17.1
(0EL8)). Neither Noetherian, quasi-compact, nor affine assumptions on `X` are required.

The argument proceeds in three steps:

1. **Formal completion of a relative spectrum.** For a quasi-coherent commutative `𝒪_X`-algebra
   `A`, the relative spectra `Spec_{V(I^(n+1))} (i_n^* A)` of its pullbacks along
   `i_n : V(I^(n+1)) ⟶ X` assemble into an adic thickening system
   `formalCompletionRelativeSpec X I A` over `X.formalCompletion I`. Its transition squares are
   cartesian because relative Spec commutes with arbitrary base change, and when `Spec_X A ⟶ X` is
   formally unramified or étale, every level inherits the same property.
2. **Algebraization of formal morphisms.** A morphism of adic thickening systems
   `formalCompletionRelativeSpec X I A ⟶ formalCompletionRelativeSpec X I B` over
   `X.formalCompletion I` corresponds, through the relative-Spec anti-equivalence on each level, to
   a compatible family of algebra homomorphisms `i_n^* B ⟶ i_n^* A`, hence to a morphism of
   coherent formal modules between the completions of `B` and `A`. When `A` and `B` are finite
   locally free and completion is fully faithful on finite locally free sheaves, this lifts uniquely
   to a module map `φ : B ⟶ A`. Because `𝒪_X` and `B ⊗ B` are again finite locally free,
   faithfulness of completion forces `φ` to preserve the unit and multiplication, yielding a unique
   algebra morphism `B ⟶ A`
   (`QuasicoherentAlgebra.existsUnique_algebraHom_of_formalCompletionRelativeSpec_hom`).
3. **Infinitesimal lifting and restriction.** For a finite, flat, locally finitely presented
   morphism `f : Y ⟶ X`, its coordinate algebra `f_* 𝒪_Y` is finite locally free
   (`AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFree_pushforward_unit`). Given a morphism over
   `X₀ ≅ V(I)` from a finite locally free scheme `Y` into a finite étale scheme `Z`, étale lifting
   over adic thickening systems (`AdicThickeningSystem.liftOfEtale`) extends it uniquely to the
   formal completions, and step 2 algebraizes the resulting formal morphism back to a unique
   morphism `Y ⟶ Z` over `X`. For injectivity (faithfulness) alone, `Z ⟶ X` only needs to be
   finite locally free and formally unramified, and completion only needs to be faithful on finite
   locally free sheaves.

## Main definitions

* `TauCeti.AlgebraicGeometry.QuasicoherentAlgebra.formalCompletionRelativeSpec`: the adic
  thickening system of infinitesimal base changes of `Spec_X A` over `X.formalCompletion I`, with
  structure map `formalCompletionRelativeSpecToBase` and functoriality
  `formalCompletionRelativeSpecMap`.
* `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackOfCompletionFiniteLocallyFree` and
  `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackSubschemeιOfCompletionFiniteLocallyFree`:
  Stacks, Lemma 58.17.1 (0EL8), for an arbitrary closed immersion `j` with `j.ker = I` and for
  `I.subschemeι`, assuming full faithfulness of completion on finite locally free sheaves.
* `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackOfCompletion` and
  `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackSubschemeιOfCompletion`: the corresponding
  corollaries when completion is fully faithful on all finitely presented sheaves.

## Main results

* `TauCeti.AlgebraicGeometry.QuasicoherentAlgebra.isMonHom_of_completion_faithful`: if completion
  is faithful on finite locally free sheaves, a module map between finite locally free algebras
  whose pullbacks to all infinitesimal neighbourhoods are algebra homomorphisms is itself an
  algebra homomorphism.
* `QuasicoherentAlgebra.existsUnique_algebraHom_of_formalCompletionRelativeSpec_hom`:
  morphisms between the formal completions of relative spectra of finite locally free algebras
  algebraize uniquely.
* `TauCeti.AlgebraicGeometry.overPullback_map_injective_of_completion_finiteLocallyFree` and
  `TauCeti.AlgebraicGeometry.overPullback_map_bijective_of_completion_finiteLocallyFree`:
  scheme-morphism level injectivity (for formally unramified target) and bijectivity (for étale
  target) of restriction along a closed immersion.

## References

* [The Stacks Project, Lemma 58.17.1](https://stacks.math.columbia.edu/tag/0EL8).
-/

public section

open CategoryTheory Limits MonoidalCategory Opposite AlgebraicGeometry

universe u

noncomputable section

/-! ### Formal completion of a relative spectrum -/

namespace TauCeti.AlgebraicGeometry.QuasicoherentAlgebra

section FormalCompletion

variable (X : Scheme.{u}) (I : X.IdealSheafData)

/-- The canonical algebra isomorphism identifying the reduction along `(X.formalCompletion I).ι n`
of the `(n + 1)`-st pullback of `A` with its `n`-th pullback. -/
def formalCompletionTransitionIso (A : QuasicoherentAlgebra X) (n : ℕ) :
    (pullback ((X.formalCompletion I).ι n)).obj
        ((pullback (Scheme.formalCompletion.toScheme X I (n + 1))).obj A) ≅
      (pullback (Scheme.formalCompletion.toScheme X I n)).obj A :=
  (pullbackComp ((X.formalCompletion I).ι n) (Scheme.formalCompletion.toScheme X I (n + 1)) ≪≫
    pullbackCongr (Scheme.formalCompletion.ι_toScheme X I n)).app A

/-- Naturality of `formalCompletionTransitionIso` in the quasi-coherent algebra `A`. -/
@[reassoc]
theorem formalCompletionTransitionIso_hom_naturality {A B : QuasicoherentAlgebra X} (φ : B ⟶ A)
    (n : ℕ) :
    (pullback ((X.formalCompletion I).ι n)).map
        ((pullback (Scheme.formalCompletion.toScheme X I (n + 1))).map φ) ≫
        (formalCompletionTransitionIso X I A n).hom =
      (formalCompletionTransitionIso X I B n).hom ≫
        (pullback (Scheme.formalCompletion.toScheme X I n)).map φ :=
  (pullbackComp ((X.formalCompletion I).ι n) (Scheme.formalCompletion.toScheme X I (n + 1)) ≪≫
    pullbackCongr (Scheme.formalCompletion.ι_toScheme X I n)).hom.naturality φ

/-- On underlying modules, `formalCompletionTransitionIso` agrees with the transition isomorphism
of `Scheme.formalCompletion.completionFunctor`, transported along `pullback_obj_X`. -/
theorem formalCompletionTransitionIso_hom_hom_hom_hom (A : QuasicoherentAlgebra X) (n : ℕ) :
    (formalCompletionTransitionIso X I A n).hom.hom.hom.hom =
      eqToHom ((pullback_obj_X ((X.formalCompletion I).ι n) _).trans
        (congrArg (Scheme.Modules.pullback ((X.formalCompletion I).ι n)).obj
          (pullback_obj_X (Scheme.formalCompletion.toScheme X I (n + 1)) A))) ≫
        ((Scheme.Modules.pullbackComp ((X.formalCompletion I).ι n)
            (Scheme.formalCompletion.toScheme X I (n + 1)) ≪≫
          Scheme.Modules.pullbackCongr
            (Scheme.formalCompletion.ι_toScheme X I n)).app A.obj.X).hom ≫
        eqToHom (pullback_obj_X (Scheme.formalCompletion.toScheme X I n) A).symm := by
  dsimp only [formalCompletionTransitionIso, Iso.trans_hom, Iso.app_hom, NatTrans.comp_app]
  rw [ObjectProperty.FullSubcategory.comp_hom, CommMon.comp_hom,
    pullbackComp_hom_app_hom_hom_hom, pullbackCongr_hom_app_hom_hom_hom]
  -- Cancel the middle `eqToHom` pair generically across the `Modules` / `SheafOfModules` instances.
  have key : ∀ {a₁ a₂ b₁ b₂ c₁ c₂ : ((X.formalCompletion I).X n).Modules}
      (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) (f : a₂ ⟶ b₂) (g : b₂ ⟶ c₂),
      (eqToHom ha ≫ f ≫ eqToHom hb.symm) ≫ (eqToHom hb ≫ g ≫ eqToHom hc.symm) =
        eqToHom ha ≫ (f ≫ g) ≫ eqToHom hc.symm := by
    intros; subst_vars; simp
  exact key _ (pullback_obj_X (((X.formalCompletion I).ι n) ≫
    Scheme.formalCompletion.toScheme X I (n + 1)) A)
    (pullback_obj_X (Scheme.formalCompletion.toScheme X I n) A) _ _

/-- Each transition square from the relative spectrum of the pulled-back algebra to the formal
completion `X/V(I)` is cartesian. -/
private lemma isPullback_formalCompletionRelativeSpecStep (A : QuasicoherentAlgebra X) (n : ℕ) :
    IsPullback
      (CommMon.relativeSpecMap (formalCompletionTransitionIso X I A n).hom.hom ≫
        relativeSpecPullbackFst ((pullback (Scheme.formalCompletion.toScheme X I (n + 1))).obj A)
          ((X.formalCompletion I).ι n))
      ((pullback (Scheme.formalCompletion.toScheme X I n)).obj A).obj.relativeSpecToBase
      ((pullback (Scheme.formalCompletion.toScheme X I (n + 1))).obj A).obj.relativeSpecToBase
      ((X.formalCompletion I).ι n) := by
  let e : ((pullback (Scheme.formalCompletion.toScheme X I n)).obj A).obj.relativeSpec ≅
      ((pullback ((X.formalCompletion I).ι n)).obj
        ((pullback (Scheme.formalCompletion.toScheme X I (n + 1))).obj A)).obj.relativeSpec :=
    { hom := CommMon.relativeSpecMap (formalCompletionTransitionIso X I A n).hom.hom
      inv := CommMon.relativeSpecMap (formalCompletionTransitionIso X I A n).inv.hom
      hom_inv_id := by
        rw [← CommMon.relativeSpecMap_comp, ← ObjectProperty.FullSubcategory.comp_hom,
          Iso.inv_hom_id, ObjectProperty.FullSubcategory.id_hom, CommMon.relativeSpecMap_id]
      inv_hom_id := by
        rw [← CommMon.relativeSpecMap_comp, ← ObjectProperty.FullSubcategory.comp_hom,
          Iso.hom_inv_id, ObjectProperty.FullSubcategory.id_hom, CommMon.relativeSpecMap_id] }
  have hbase := isPullback_relativeSpecPullbackFst
    ((pullback (Scheme.formalCompletion.toScheme X I (n + 1))).obj A)
    ((X.formalCompletion I).ι n)
  exact hbase.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      dsimp only [Iso.symm_hom, Iso.refl_hom]
      rw [Category.comp_id, ← Category.assoc, e.inv_hom_id, Category.id_comp])
    (by simp [e])
    (by simp)
    (by simp)

/-- Pasting the cartesian transition squares shows that the level map of the relative-Spec tower
is the base change of `(X.formalCompletion I).levelMap m`. -/
private lemma isPullback_levelMap_formalCompletionRelativeSpecStep (A : QuasicoherentAlgebra X)
    (m : ℕ) :
    IsPullback
      (levelMap
        (fun n ↦ ((pullback (Scheme.formalCompletion.toScheme X I n)).obj A).obj.relativeSpec)
        (fun n ↦ CommMon.relativeSpecMap (formalCompletionTransitionIso X I A n).hom.hom ≫
          relativeSpecPullbackFst ((pullback (Scheme.formalCompletion.toScheme X I (n + 1))).obj A)
            ((X.formalCompletion I).ι n)) m)
      ((pullback (Scheme.formalCompletion.toScheme X I 0)).obj A).obj.relativeSpecToBase
      ((pullback (Scheme.formalCompletion.toScheme X I m)).obj A).obj.relativeSpecToBase
      ((X.formalCompletion I).levelMap m) := by
  induction m with
  | zero =>
    rw [levelMap_zero, (X.formalCompletion I).levelMap_zero]
    exact IsPullback.of_horiz_isIso (fst := 𝟙 _) (g := 𝟙 _) ⟨by simp⟩
  | succ m ih =>
    rw [levelMap_succ, (X.formalCompletion I).levelMap_succ]
    exact ih.paste_horiz (isPullback_formalCompletionRelativeSpecStep X I A m)

/-- The adic thickening system of infinitesimal base changes of `Spec_X A` over
`X.formalCompletion I`: its `n`-th level is `Spec_{V(I^(n+1))} (i_n^* A)` where
`i_n : V(I^(n+1)) ⟶ X` is the closed immersion of the `n`-th infinitesimal neighbourhood. -/
-- `@[expose]` is forced by dependent typing of component morphisms: without
-- `(formalCompletionRelativeSpec X I A).X n` reducing definitionally to the relative spectrum of
-- the `n`-th pullback of `A`, the component equalities for `formalCompletionRelativeSpecToBase`
-- and `formalCompletionRelativeSpecMap` do not typecheck.
@[expose, simps X]
def formalCompletionRelativeSpec (A : QuasicoherentAlgebra X) : AdicThickeningSystem.{u} where
  X n := ((pullback (Scheme.formalCompletion.toScheme X I n)).obj A).obj.relativeSpec
  ι n :=
    CommMon.relativeSpecMap (formalCompletionTransitionIso X I A n).hom.hom ≫
      relativeSpecPullbackFst ((pullback (Scheme.formalCompletion.toScheme X I (n + 1))).obj A)
        ((X.formalCompletion I).ι n)
  isThickening n := by
    exact MorphismProperty.of_isPullback (P := @IsThickening)
      (isPullback_formalCompletionRelativeSpecStep X I A n).flip inferInstance
  adic n := by
    have hι := Scheme.IdealSheafData.ker_eq_comap_of_isPullback ((X.formalCompletion I).ι n)
      (isPullback_formalCompletionRelativeSpecStep X I A n)
    have hlev := Scheme.IdealSheafData.ker_eq_comap_of_isPullback
      ((X.formalCompletion I).levelMap (n + 1))
      (isPullback_levelMap_formalCompletionRelativeSpecStep X I A (n + 1))
    rw [hι, hlev, (X.formalCompletion I).ker_ι n, Scheme.IdealSheafData.comap_pow]

/-- The step transition morphism of `formalCompletionRelativeSpec`. -/
@[simp]
theorem formalCompletionRelativeSpec_ι (A : QuasicoherentAlgebra X) (n : ℕ) :
    (formalCompletionRelativeSpec X I A).ι n =
      CommMon.relativeSpecMap (formalCompletionTransitionIso X I A n).hom.hom ≫
        relativeSpecPullbackFst ((pullback (Scheme.formalCompletion.toScheme X I (n + 1))).obj A)
          ((X.formalCompletion I).ι n) :=
  (rfl)

/-- The structure morphism from the formal completion of `Spec_X A` to `X.formalCompletion I`. -/
def formalCompletionRelativeSpecToBase (A : QuasicoherentAlgebra X) :
    formalCompletionRelativeSpec X I A ⟶ X.formalCompletion I where
  app n := ((pullback (Scheme.formalCompletion.toScheme X I n)).obj A).obj.relativeSpecToBase
  naturality n := (isPullback_formalCompletionRelativeSpecStep X I A n).w

@[simp]
theorem formalCompletionRelativeSpecToBase_app (A : QuasicoherentAlgebra X) (n : ℕ) :
    (formalCompletionRelativeSpecToBase X I A).app n =
      ((pullback (Scheme.formalCompletion.toScheme X I n)).obj A).obj.relativeSpecToBase :=
  (rfl)

/-- The structure morphism from the formal completion of `Spec_X A` to `X/V(I)` is adic. -/
instance isAdicHom_formalCompletionRelativeSpecToBase (A : QuasicoherentAlgebra X) :
    AdicThickeningSystem.IsAdicHom (formalCompletionRelativeSpecToBase X I A) where
  isPullback := isPullback_formalCompletionRelativeSpecStep X I A

/-- If `Spec_X A ⟶ X` is formally unramified, then every level of its formal completion is
formally unramified over the corresponding level of `X/V(I)`. -/
instance formallyUnramified_formalCompletionRelativeSpecToBase_app (A : QuasicoherentAlgebra X)
    [FormallyUnramified A.obj.relativeSpecToBase] (n : ℕ) :
    FormallyUnramified ((formalCompletionRelativeSpecToBase X I A).app n) :=
  MorphismProperty.of_isPullback (P := @FormallyUnramified)
    (isPullback_relativeSpecPullbackFst A (Scheme.formalCompletion.toScheme X I n))
    inferInstance

/-- If `Spec_X A ⟶ X` is étale, then every level of its formal completion is étale over the
corresponding level of `X/V(I)`. -/
instance etale_formalCompletionRelativeSpecToBase_app (A : QuasicoherentAlgebra X)
    [Etale A.obj.relativeSpecToBase] (n : ℕ) :
    Etale ((formalCompletionRelativeSpecToBase X I A).app n) :=
  MorphismProperty.of_isPullback (P := @Etale)
    (isPullback_relativeSpecPullbackFst A (Scheme.formalCompletion.toScheme X I n))
    inferInstance

/-- An algebra morphism `φ : B ⟶ A` induces a morphism of adic thickening systems between the
formal completions of their relative spectra, contravariantly. -/
def formalCompletionRelativeSpecMap {A B : QuasicoherentAlgebra X} (φ : B ⟶ A) :
    formalCompletionRelativeSpec X I A ⟶ formalCompletionRelativeSpec X I B where
  app n := CommMon.relativeSpecMap
    ((pullback (Scheme.formalCompletion.toScheme X I n)).map φ).hom
  naturality n := by
    dsimp only [formalCompletionRelativeSpec]
    rw [Category.assoc, ← relativeSpecMap_pullback_map_relativeSpecPullbackFst, ← Category.assoc,
      ← CommMon.relativeSpecMap_comp, ← ObjectProperty.FullSubcategory.comp_hom,
      formalCompletionTransitionIso_hom_naturality, ObjectProperty.FullSubcategory.comp_hom,
      CommMon.relativeSpecMap_comp, Category.assoc]

@[simp]
theorem formalCompletionRelativeSpecMap_app {A B : QuasicoherentAlgebra X} (φ : B ⟶ A) (n : ℕ) :
    (formalCompletionRelativeSpecMap X I φ).app n =
      CommMon.relativeSpecMap ((pullback (Scheme.formalCompletion.toScheme X I n)).map φ).hom :=
  (rfl)

@[simp]
theorem formalCompletionRelativeSpecMap_id (A : QuasicoherentAlgebra X) :
    formalCompletionRelativeSpecMap X I (𝟙 A) = 𝟙 (formalCompletionRelativeSpec X I A) := by
  ext n
  simp [CommMon.relativeSpecMap_id]
  rfl

@[simp]
theorem formalCompletionRelativeSpecMap_comp {A B C : QuasicoherentAlgebra X}
    (φ : C ⟶ B) (ψ : B ⟶ A) :
    formalCompletionRelativeSpecMap X I (φ ≫ ψ) =
      formalCompletionRelativeSpecMap X I ψ ≫ formalCompletionRelativeSpecMap X I φ := by
  ext n
  simp [CommMon.relativeSpecMap_comp]
  rfl

/-- The morphism of formal completions induced by an algebra map commutes with the structure
morphisms to `X/V(I)`. -/
@[reassoc (attr := simp)]
theorem formalCompletionRelativeSpecMap_comp_toBase {A B : QuasicoherentAlgebra X} (φ : B ⟶ A) :
    formalCompletionRelativeSpecMap X I φ ≫ formalCompletionRelativeSpecToBase X I B =
      formalCompletionRelativeSpecToBase X I A := by
  ext n
  exact CommMon.relativeSpecMap_relativeSpecToBase _

/-! ### Algebraization of formal morphisms between relative spectra -/

open scoped MonObj in
/-- If the completion functor is faithful on finite locally free sheaves, a morphism of underlying
modules between finite locally free quasi-coherent algebras whose pullbacks to every infinitesimal
neighbourhood `V(I^(n+1))` are algebra homomorphisms is itself an algebra homomorphism. -/
theorem isMonHom_of_completion_faithful
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful]
    {A B : QuasicoherentAlgebra X}
    (hA : Scheme.Modules.isFiniteLocallyFree X A.obj.X)
    (hB : Scheme.Modules.isFiniteLocallyFree X B.obj.X)
    (φ : B.obj.X ⟶ A.obj.X)
    (hφ : ∀ n, IsMonHom
      (eqToHom (pullback_obj_X (Scheme.formalCompletion.toScheme X I n) B) ≫
        (Scheme.Modules.pullback (Scheme.formalCompletion.toScheme X I n)).map φ ≫
        eqToHom (pullback_obj_X (Scheme.formalCompletion.toScheme X I n) A).symm)) :
    IsMonHom φ := by
  let F := FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
    Scheme.formalCompletion.completionFunctor X I
  let EA : FiniteLocallyFreeSheaf X := ⟨A.obj.X, hA⟩
  let E1 : FiniteLocallyFreeSheaf X :=
    ⟨𝟙_ X.Modules, (Scheme.Modules.isMonoidal_isFiniteLocallyFree X).prop_unit⟩
  let EBB : FiniteLocallyFreeSheaf X :=
    ⟨B.obj.X ⊗ B.obj.X, (Scheme.Modules.isMonoidal_isFiniteLocallyFree X).prop_tensor _ _ hB hB⟩
  constructor
  · -- Unit compatibility: both morphisms `𝒪_X ⟶ A.obj.X` agree after completion.
    have hEq : (ObjectProperty.homMk (η[B.obj.X] ≫ φ) : E1 ⟶ EA) =
        ObjectProperty.homMk η[A.obj.X] := by
      apply F.map_injective
      refine AdicThickeningSystem.CoherentFormalModule.hom_ext fun n ↦ ?_
      let f := Scheme.formalCompletion.toScheme X I n
      have hone := (hφ n).one_hom
      rw [pullback_obj_one f B, pullback_obj_one f A] at hone
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at hone
      have hcancel := congrArg (· ≫ eqToHom (pullback_obj_X f A))
        ((cancel_epi (Scheme.Modules.pullbackObjUnitIso f).inv).mp hone)
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at hcancel
      exact ((Scheme.Modules.pullback f).map_comp η[B.obj.X] φ).trans hcancel
    exact congrArg (·.hom) hEq
  · -- Multiplication compatibility: both morphisms `B.obj.X ⊗ B.obj.X ⟶ A.obj.X` agree after
    -- completion.
    have hEq : (ObjectProperty.homMk (μ[B.obj.X] ≫ φ) : EBB ⟶ EA) =
        ObjectProperty.homMk ((φ ⊗ₘ φ) ≫ μ[A.obj.X]) := by
      apply F.map_injective
      refine AdicThickeningSystem.CoherentFormalModule.hom_ext fun n ↦ ?_
      let f := Scheme.formalCompletion.toScheme X I n
      have hmul := (hφ n).mul_hom
      rw [pullback_obj_mul f B, pullback_obj_mul f A] at hmul
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at hmul
      have hδ : inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) B.obj.X B.obj.X) ≫
          (Scheme.Modules.pullback f).map (φ ⊗ₘ φ) =
            ((Scheme.Modules.pullback f).map φ ⊗ₘ (Scheme.Modules.pullback f).map φ) ≫
              inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) A.obj.X A.obj.X) := by
        rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
        exact (Functor.OplaxMonoidal.δ_natural (Scheme.Modules.pullback f) φ φ).symm
      have htensor : ∀ {a b : ((X.formalCompletion I).X n).Modules} (h : a = b),
          (eqToHom h.symm ⊗ₘ eqToHom h.symm) ≫ (eqToHom h ⊗ₘ eqToHom h) = 𝟙 (b ⊗ b) := by
        intros; subst_vars; simp
      have hRHS :
          ((eqToHom (pullback_obj_X f B) ≫ (Scheme.Modules.pullback f).map φ ≫
              eqToHom (pullback_obj_X f A).symm) ⊗ₘ
            (eqToHom (pullback_obj_X f B) ≫ (Scheme.Modules.pullback f).map φ ≫
              eqToHom (pullback_obj_X f A).symm)) ≫
            (eqToHom (pullback_obj_X f A) ⊗ₘ eqToHom (pullback_obj_X f A)) ≫
            inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) A.obj.X A.obj.X) ≫
            (Scheme.Modules.pullback f).map μ[A.obj.X] ≫ eqToHom (pullback_obj_X f A).symm =
          (eqToHom (pullback_obj_X f B) ⊗ₘ eqToHom (pullback_obj_X f B)) ≫
            inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) B.obj.X B.obj.X) ≫
            (Scheme.Modules.pullback f).map ((φ ⊗ₘ φ) ≫ μ[A.obj.X]) ≫
            eqToHom (pullback_obj_X f A).symm := by
        rw [← tensorHom_comp_tensorHom_assoc, ← tensorHom_comp_tensorHom_assoc]
        simp only [Category.assoc, reassoc_of% (htensor (pullback_obj_X f A)),
          Functor.map_comp, reassoc_of% hδ]
      rw [hRHS] at hmul
      have hcancel1 := (cancel_epi
        ((eqToHom (pullback_obj_X f B) ⊗ₘ eqToHom (pullback_obj_X f B)) ≫
          inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) B.obj.X B.obj.X))).mp <| by
        simpa only [Category.assoc] using hmul
      have hcancel2 := congrArg (· ≫ eqToHom (pullback_obj_X f A)) hcancel1
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at hcancel2
      exact ((Scheme.Modules.pullback f).map_comp μ[B.obj.X] φ).trans hcancel2
    exact congrArg (·.hom) hEq

/-- If the completion functor is faithful on finite locally free sheaves, then passing to formal
completions of relative spectra is injective on algebra morphisms between finite locally free
quasi-coherent algebras. -/
theorem formalCompletionRelativeSpecMap_injective
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful]
    {A B : QuasicoherentAlgebra X}
    (hA : Scheme.Modules.isFiniteLocallyFree X A.obj.X)
    (hB : Scheme.Modules.isFiniteLocallyFree X B.obj.X) :
    Function.Injective (formalCompletionRelativeSpecMap X I (A := A) (B := B)) := by
  intro φ ψ h
  let F := FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
    Scheme.formalCompletion.completionFunctor X I
  let EA : FiniteLocallyFreeSheaf X := ⟨A.obj.X, hA⟩
  let EB : FiniteLocallyFreeSheaf X := ⟨B.obj.X, hB⟩
  have hmod :
      (ObjectProperty.homMk φ.hom.hom.hom : EB ⟶ EA) = ObjectProperty.homMk ψ.hom.hom.hom := by
    apply F.map_injective
    refine AdicThickeningSystem.CoherentFormalModule.hom_ext fun n ↦ ?_
    let f := Scheme.formalCompletion.toScheme X I n
    have happ : CommMon.relativeSpecMap ((pullback f).map φ).hom =
        CommMon.relativeSpecMap ((pullback f).map ψ).hom :=
      congrArg (·.app n) h
    have hrel : (relativeSpec ((X.formalCompletion I).X n)).map ((pullback f).map φ).op =
        (relativeSpec ((X.formalCompletion I).X n)).map ((pullback f).map ψ).op := by
      apply MorphismProperty.Over.Hom.ext
      exact happ
    have hpull : (pullback f).map φ = (pullback f).map ψ :=
      Quiver.Hom.op_inj ((relativeSpec ((X.formalCompletion I).X n)).map_injective hrel)
    have hX := congrArg (fun g ↦ g.hom.hom.hom) hpull
    rw [pullback_map_hom_hom_hom, pullback_map_hom_hom_hom] at hX
    have key : ∀ {a₁ a₂ b₁ b₂ : ((X.formalCompletion I).X n).Modules}
        (ha : a₁ = a₂) (hb : b₁ = b₂) (u v : a₂ ⟶ b₂),
        eqToHom ha ≫ u ≫ eqToHom hb.symm = eqToHom ha ≫ v ≫ eqToHom hb.symm → u = v := by
      intros; subst_vars; simpa using ‹_›
    exact key (pullback_obj_X f B) (pullback_obj_X f A) _ _ hX
  exact ObjectProperty.hom_ext _ (CommMon.hom_ext _ _ (congrArg (·.hom) hmod))

/-- The levelwise algebra morphisms obtained via the relative-Spec anti-equivalence from a morphism
of formal completions over `X/V(I)` commute with the transition isomorphisms
`formalCompletionTransitionIso`. -/
private lemma formalCompletionRelativeSpec_preimage_naturality
    {A B : QuasicoherentAlgebra X}
    (a : formalCompletionRelativeSpec X I A ⟶ formalCompletionRelativeSpec X I B)
    (ψ : ∀ n, (pullback (Scheme.formalCompletion.toScheme X I n)).obj B ⟶
      (pullback (Scheme.formalCompletion.toScheme X I n)).obj A)
    (hψ_spec : ∀ n, CommMon.relativeSpecMap (ψ n).hom = a.app n) (n : ℕ) :
    (pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1)) ≫
        (formalCompletionTransitionIso X I A n).hom =
      (formalCompletionTransitionIso X I B n).hom ≫ ψ n := by
  let Xn := (X.formalCompletion I).X
  let An (k : ℕ) := (pullback (Scheme.formalCompletion.toScheme X I k)).obj A
  let Bn (k : ℕ) := (pullback (Scheme.formalCompletion.toScheme X I k)).obj B
  apply Quiver.Hom.op_inj
  apply (relativeSpec (Xn n)).map_injective
  apply MorphismProperty.Over.Hom.ext
  have hpb := isPullback_relativeSpecPullbackFst (Bn (n + 1)) ((X.formalCompletion I).ι n)
  apply hpb.hom_ext
  · -- First projection to `Spec (Bn (n + 1))`: this is the naturality of `a` at level `n`.
    let tA := CommMon.relativeSpecMap (formalCompletionTransitionIso X I A n).hom.hom
    let tB := CommMon.relativeSpecMap (formalCompletionTransitionIso X I B n).hom.hom
    let mψ := CommMon.relativeSpecMap
      ((pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1))).hom
    let pA := relativeSpecPullbackFst (An (n + 1)) ((X.formalCompletion I).ι n)
    let pB := relativeSpecPullbackFst (Bn (n + 1)) ((X.formalCompletion I).ι n)
    have hL : ((relativeSpec (Xn n)).map
          ((pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1)) ≫
            (formalCompletionTransitionIso X I A n).hom).op).left ≫ pB =
        (formalCompletionRelativeSpec X I A).ι n ≫ a.app (n + 1) := by
      have h1 : ((relativeSpec (Xn n)).map
          ((pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1)) ≫
            (formalCompletionTransitionIso X I A n).hom).op).left = tA ≫ mψ :=
        (relativeSpec_map_left _).trans
          ((congrArg CommMon.relativeSpecMap
            (ObjectProperty.FullSubcategory.comp_hom _ _ _)).trans
            (CommMon.relativeSpecMap_comp _ _))
      have h2 : mψ ≫ pB = pA ≫ CommMon.relativeSpecMap (ψ (n + 1)).hom :=
        relativeSpecMap_pullback_map_relativeSpecPullbackFst (An (n + 1))
          ((X.formalCompletion I).ι n) (ψ (n + 1))
      have h3 : (tA ≫ pA) ≫ CommMon.relativeSpecMap (ψ (n + 1)).hom =
          (formalCompletionRelativeSpec X I A).ι n ≫ a.app (n + 1) :=
        (congrArg (· ≫ CommMon.relativeSpecMap (ψ (n + 1)).hom)
            (formalCompletionRelativeSpec_ι X I A n).symm).trans
          (congrArg ((formalCompletionRelativeSpec X I A).ι n ≫ ·) (hψ_spec (n + 1)))
      exact (congrArg (· ≫ pB) h1).trans
        ((Category.assoc tA mψ pB).trans
          ((congrArg (tA ≫ ·) h2).trans ((Category.assoc tA pA _).symm.trans h3)))
    have hR : ((relativeSpec (Xn n)).map
          ((formalCompletionTransitionIso X I B n).hom ≫ ψ n).op).left ≫ pB =
        a.app n ≫ (formalCompletionRelativeSpec X I B).ι n := by
      have h1 : ((relativeSpec (Xn n)).map
          ((formalCompletionTransitionIso X I B n).hom ≫ ψ n).op).left =
          CommMon.relativeSpecMap (ψ n).hom ≫ tB :=
        (relativeSpec_map_left _).trans
          ((congrArg CommMon.relativeSpecMap
            (ObjectProperty.FullSubcategory.comp_hom _ _ _)).trans
            (CommMon.relativeSpecMap_comp _ _))
      exact (congrArg (· ≫ pB) h1).trans
        ((Category.assoc _ tB pB).trans
          ((congrArg (· ≫ (tB ≫ pB)) (hψ_spec n)).trans
            (congrArg (a.app n ≫ ·) (formalCompletionRelativeSpec_ι X I B n).symm)))
    exact hL.trans ((a.naturality n).trans hR.symm)
  · -- Second projection to `Xn n`: both sides are `An n`'s structure morphism.
    exact (congrArg (· ≫ _) (relativeSpec_map_left _)).trans
      ((CommMon.relativeSpecMap_relativeSpecToBase _).trans
        ((CommMon.relativeSpecMap_relativeSpecToBase _).symm.trans
          (congrArg (· ≫ _) (relativeSpec_map_left _).symm)))

/-- **Algebraization of formal morphisms between relative spectra of finite locally free algebras.**
Suppose the completion functor is fully faithful on finite locally free sheaves on `X`. Let `A`
and `B` be finite locally free quasi-coherent commutative `𝒪_X`-algebras. Then every morphism
`a : formalCompletionRelativeSpec X I A ⟶ formalCompletionRelativeSpec X I B` over `X/V(I)` is
induced by a unique algebra morphism `φ : B ⟶ A`. -/
theorem existsUnique_algebraHom_of_formalCompletionRelativeSpec_hom
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful]
    {A B : QuasicoherentAlgebra X}
    (hA : Scheme.Modules.isFiniteLocallyFree X A.obj.X)
    (hB : Scheme.Modules.isFiniteLocallyFree X B.obj.X)
    (a : formalCompletionRelativeSpec X I A ⟶ formalCompletionRelativeSpec X I B)
    (ha : a ≫ formalCompletionRelativeSpecToBase X I B = formalCompletionRelativeSpecToBase X I A) :
    ∃! φ : B ⟶ A, formalCompletionRelativeSpecMap X I φ = a := by
  let Xn := (X.formalCompletion I).X
  let fn (n : ℕ) := Scheme.formalCompletion.toScheme X I n
  let An (n : ℕ) := (pullback (fn n)).obj A
  let Bn (n : ℕ) := (pullback (fn n)).obj B
  -- Step 1: On each level `n`, recover the algebra map `ψ n : Bn n ⟶ An n` via `relativeSpec`.
  let am (n : ℕ) : (relativeSpec (Xn n)).obj (op (An n)) ⟶ (relativeSpec (Xn n)).obj (op (Bn n)) :=
    MorphismProperty.Over.homMk (a.app n) (congrArg (·.app n) ha)
  let ψ (n : ℕ) : Bn n ⟶ An n := ((relativeSpec (Xn n)).preimage (am n)).unop
  have hψ_spec (n : ℕ) : CommMon.relativeSpecMap (ψ n).hom = a.app n :=
    congrArg (·.left) ((relativeSpec (Xn n)).map_preimage (am n))
  -- Step 2: Assemble `ψ` into a morphism of coherent formal modules between the completions.
  let F := FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
    Scheme.formalCompletion.completionFunctor X I
  let EA : FiniteLocallyFreeSheaf X := ⟨A.obj.X, hA⟩
  let EB : FiniteLocallyFreeSheaf X := ⟨B.obj.X, hB⟩
  let ψMod : F.obj EB ⟶ F.obj EA :=
    { app n := eqToHom (pullback_obj_X (fn n) B).symm ≫ (ψ n).hom.hom.hom ≫
        eqToHom (pullback_obj_X (fn n) A)
      naturality n := by
        have h := congrArg (fun g ↦ g.hom.hom.hom)
          (formalCompletionRelativeSpec_preimage_naturality X I a ψ hψ_spec n)
        rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
          CommMon.comp_hom, CommMon.comp_hom,
          pullback_map_hom_hom_hom, formalCompletionTransitionIso_hom_hom_hom_hom,
          formalCompletionTransitionIso_hom_hom_hom_hom] at h
        let G := Scheme.Modules.pullback ((X.formalCompletion I).ι n)
        have key : ∀ {b₁ b₂ a₁ a₂ : (Xn (n + 1)).Modules} {fb fa b₀ b₀' a₀ a₀' : (Xn n).Modules}
            (hb : b₁ = b₂) (ha : a₁ = a₂) (hfb : fb = G.obj b₁) (hfa : fa = G.obj a₁)
            (hb₀ : b₀ = b₀') (ha₀ : a₀ = a₀') (ψ₁ : b₁ ⟶ a₁) (ψ₀ : b₀ ⟶ a₀)
            (tA : G.obj a₂ ⟶ a₀') (tB : G.obj b₂ ⟶ b₀'),
            (eqToHom hfb ≫ G.map ψ₁ ≫ eqToHom hfa.symm) ≫
              (eqToHom (hfa.trans (congrArg G.obj ha)) ≫ tA ≫ eqToHom ha₀.symm) =
            (eqToHom (hfb.trans (congrArg G.obj hb)) ≫ tB ≫ eqToHom hb₀.symm) ≫ ψ₀ →
            G.map (eqToHom hb.symm ≫ ψ₁ ≫ eqToHom ha) ≫ tA =
              tB ≫ eqToHom hb₀.symm ≫ ψ₀ ≫ eqToHom ha₀ := by
          intros; subst_vars; simpa using ‹_›
        exact key (pullback_obj_X (fn (n + 1)) B) (pullback_obj_X (fn (n + 1)) A)
          (pullback_obj_X ((X.formalCompletion I).ι n) (Bn (n + 1)))
          (pullback_obj_X ((X.formalCompletion I).ι n) (An (n + 1)))
          (pullback_obj_X (fn n) B) (pullback_obj_X (fn n) A)
          (ψ (n + 1)).hom.hom.hom (ψ n).hom.hom.hom _ _ h }
  -- Step 3: Lift `ψMod` to a module map `φMod : B.obj.X ⟶ A.obj.X` using fullness of completion.
  let φMod : EB ⟶ EA := F.preimage ψMod
  have hφMod (n : ℕ) :
      eqToHom (pullback_obj_X (fn n) B) ≫ (Scheme.Modules.pullback (fn n)).map φMod.hom ≫
          eqToHom (pullback_obj_X (fn n) A).symm = (ψ n).hom.hom.hom := by
    have h : (Scheme.Modules.pullback (fn n)).map φMod.hom =
        eqToHom (pullback_obj_X (fn n) B).symm ≫ (ψ n).hom.hom.hom ≫
          eqToHom (pullback_obj_X (fn n) A) :=
      congrArg (·.app n) (F.map_preimage ψMod)
    have key : ∀ {a₁ a₂ b₁ b₂ : (Xn n).Modules} (ha : a₁ = a₂) (hb : b₁ = b₂) (u : a₁ ⟶ b₁),
        eqToHom ha ≫ (eqToHom ha.symm ≫ u ≫ eqToHom hb) ≫ eqToHom hb.symm = u := by
      intros; subst_vars; simp
    exact (congrArg (fun g ↦ eqToHom (pullback_obj_X (fn n) B) ≫ g ≫
      eqToHom (pullback_obj_X (fn n) A).symm) h).trans
      (key (pullback_obj_X (fn n) B) (pullback_obj_X (fn n) A) (ψ n).hom.hom.hom)
  -- Step 4: Deduce `IsMonHom φMod.hom` from faithfulness of completion.
  have hmon : IsMonHom φMod.hom :=
    isMonHom_of_completion_faithful X I hA hB φMod.hom fun n ↦ by
      rw [hφMod n]
      exact (ψ n).hom.hom.isMonHom_hom
  let φ : B ⟶ A := ObjectProperty.homMk (CommMon.homMk (@Mon.Hom.mk _ _ _ _ _ φMod.hom hmon))
  have hφ_map : formalCompletionRelativeSpecMap X I φ = a := by
    ext n
    have hpull : (pullback (fn n)).map φ = ψ n := by
      apply ObjectProperty.hom_ext
      apply CommMon.hom_ext
      rw [pullback_map_hom_hom_hom]
      exact hφMod n
    rw [formalCompletionRelativeSpecMap_app, hpull, hψ_spec n]
  exact ⟨φ, hφ_map, fun φ' hφ' ↦
    formalCompletionRelativeSpecMap_injective X I hA hB (hφ'.trans hφ_map.symm)⟩

/-- If completion is faithful on finite locally free sheaves and `Spec_X B ⟶ X` is formally
unramified, then pulling back algebra morphisms `B ⟶ A` (for finite locally free `A, B`) to the
initial level `V(I) ⟶ X` is injective. -/
theorem pullback_toScheme_zero_map_injective
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful]
    {A B : QuasicoherentAlgebra X}
    (hA : Scheme.Modules.isFiniteLocallyFree X A.obj.X)
    (hB : Scheme.Modules.isFiniteLocallyFree X B.obj.X)
    [FormallyUnramified B.obj.relativeSpecToBase] :
    Function.Injective
      (fun φ : B ⟶ A ↦ (pullback (Scheme.formalCompletion.toScheme X I 0)).map φ) := by
  intro φ ψ h₀
  dsimp only at h₀
  apply formalCompletionRelativeSpecMap_injective X I hA hB
  apply AdicThickeningSystem.hom_ext_of_formallyUnramified
    (formalCompletionRelativeSpecToBase X I B)
  · simp
  · rw [formalCompletionRelativeSpecMap_app, formalCompletionRelativeSpecMap_app, h₀]

/-- If completion is fully faithful on finite locally free sheaves and `Spec_X B ⟶ X` is étale,
then pulling back algebra morphisms `B ⟶ A` (for finite locally free `A, B`) to the initial level
`V(I) ⟶ X` is bijective. -/
theorem pullback_toScheme_zero_map_bijective
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful]
    {A B : QuasicoherentAlgebra X}
    (hA : Scheme.Modules.isFiniteLocallyFree X A.obj.X)
    (hB : Scheme.Modules.isFiniteLocallyFree X B.obj.X)
    [Etale B.obj.relativeSpecToBase] :
    Function.Bijective
      (fun φ : B ⟶ A ↦ (pullback (Scheme.formalCompletion.toScheme X I 0)).map φ) := by
  refine ⟨pullback_toScheme_zero_map_injective X I hA hB, fun φ₀ ↦ ?_⟩
  let a₀ : (formalCompletionRelativeSpec X I A).X 0 ⟶ (formalCompletionRelativeSpec X I B).X 0 :=
    CommMon.relativeSpecMap φ₀.hom
  have ha₀ : a₀ ≫ (formalCompletionRelativeSpecToBase X I B).app 0 =
      (formalCompletionRelativeSpecToBase X I A).app 0 :=
    CommMon.relativeSpecMap_relativeSpecToBase φ₀.hom
  let a := AdicThickeningSystem.liftOfEtale (formalCompletionRelativeSpecToBase X I A)
    (formalCompletionRelativeSpecToBase X I B) a₀ ha₀
  obtain ⟨φ, hφ, -⟩ := existsUnique_algebraHom_of_formalCompletionRelativeSpec_hom X I hA hB a
    (AdicThickeningSystem.liftOfEtale_comp _ _ a₀ ha₀)
  refine ⟨φ, ?_⟩
  apply Quiver.Hom.op_inj
  apply (relativeSpec ((X.formalCompletion I).X 0)).map_injective
  apply MorphismProperty.Over.Hom.ext
  have happ :
      CommMon.relativeSpecMap ((pullback (Scheme.formalCompletion.toScheme X I 0)).map φ).hom =
        a.app 0 := congrArg (·.app 0) hφ
  exact happ.trans (AdicThickeningSystem.liftOfEtale_app_zero _ _ a₀ ha₀)

end FormalCompletion

end TauCeti.AlgebraicGeometry.QuasicoherentAlgebra

/-! ### Full faithfulness of restriction along a closed immersion (Stacks, Lemma 58.17.1) -/

namespace TauCeti.AlgebraicGeometry

section ClosedImmersion

variable {X X₀ : Scheme.{u}} (I : X.IdealSheafData)

/-- Any closed immersion `j : X₀ ⟶ X` with `j.ker = I` factors through the initial level
`toScheme X I 0 : V(I^1) ⟶ X` via an isomorphism `X₀ ≅ V(I^1)`. -/
private def isoFormalCompletionZeroOfKerEq (j : X₀ ⟶ X) [IsClosedImmersion j] (hj : j.ker = I) :
    X₀ ≅ (X.formalCompletion I).X 0 := by
  have hker : (Scheme.formalCompletion.toScheme X I 0).ker = j.ker := by
    rw [Scheme.formalCompletion.ker_toScheme, pow_one, hj]
  have : IsIso (IsClosedImmersion.lift (Scheme.formalCompletion.toScheme X I 0) j hker.le) :=
    IsClosedImmersion.isIso_lift (Scheme.formalCompletion.toScheme X I 0) j hker
  exact asIso (IsClosedImmersion.lift (Scheme.formalCompletion.toScheme X I 0) j hker.le)

private lemma isoFormalCompletionZeroOfKerEq_hom_comp (j : X₀ ⟶ X) [IsClosedImmersion j]
    (hj : j.ker = I) :
    (isoFormalCompletionZeroOfKerEq I j hj).hom ≫ Scheme.formalCompletion.toScheme X I 0 = j :=
  IsClosedImmersion.lift_fac (Scheme.formalCompletion.toScheme X I 0) j _

/-- Pulling back morphisms in `Over X` along `j = e.hom ≫ i` (for an isomorphism `e`) is injective
if pulling back along `i` is injective. -/
private lemma overPullback_map_injective_of_fac_iso {X₀' : Scheme.{u}} {i : X₀' ⟶ X} {j : X₀ ⟶ X}
    (e : X₀ ≅ X₀') (he : e.hom ≫ i = j) {Y Z : Over X}
    (hi : Function.Injective (fun g : Y ⟶ Z ↦ (Over.pullback i).map g)) :
    Function.Injective (fun g : Y ⟶ Z ↦ (Over.pullback j).map g) := by
  have : (Over.pullback e.hom).IsEquivalence :=
    (Over.mapPullbackAdj e.hom).isEquivalence_right_of_isEquivalence_left
  let hiso : Over.pullback j ≅ Over.pullback i ⋙ Over.pullback e.hom :=
    eqToIso (congrArg (fun k : X₀ ⟶ X ↦ Over.pullback k) he.symm) ≪≫ Over.pullbackComp e.hom i
  intro g₁ g₂ h
  apply hi
  apply (Over.pullback e.hom).map_injective
  have hn₁ := hiso.hom.naturality g₁
  have hn₂ := hiso.hom.naturality g₂
  dsimp only at h
  rw [h] at hn₁
  exact (cancel_epi (hiso.hom.app Y)).mp (hn₁.symm.trans hn₂)

/-- Pulling back morphisms in `Over X` along `j = e.hom ≫ i` (for an isomorphism `e`) is surjective
if pulling back along `i` is surjective. -/
private lemma overPullback_map_surjective_of_fac_iso {X₀' : Scheme.{u}} {i : X₀' ⟶ X} {j : X₀ ⟶ X}
    (e : X₀ ≅ X₀') (he : e.hom ≫ i = j) {Y Z : Over X}
    (hi : Function.Surjective (fun g : Y ⟶ Z ↦ (Over.pullback i).map g)) :
    Function.Surjective (fun g : Y ⟶ Z ↦ (Over.pullback j).map g) := by
  have : (Over.pullback e.hom).IsEquivalence :=
    (Over.mapPullbackAdj e.hom).isEquivalence_right_of_isEquivalence_left
  let hiso : Over.pullback j ≅ Over.pullback i ⋙ Over.pullback e.hom :=
    eqToIso (congrArg (fun k : X₀ ⟶ X ↦ Over.pullback k) he.symm) ≪≫ Over.pullbackComp e.hom i
  intro g₀
  let g₀' : (Over.pullback i).obj Y ⟶ (Over.pullback i).obj Z :=
    (Over.pullback e.hom).preimage (hiso.inv.app Y ≫ g₀ ≫ hiso.hom.app Z)
  obtain ⟨g, hg⟩ := hi g₀'
  refine ⟨g, ?_⟩
  have hnat := hiso.hom.naturality g
  simp only [Functor.comp_map] at hnat
  dsimp only at hg
  rw [hg, (Over.pullback e.hom).map_preimage] at hnat
  have hcancel := congrArg (· ≫ hiso.inv.app Z) hnat
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app,
    Category.comp_id] using hcancel

/-- On affine schemes `V, W` over `S`, the action of `Over.pullback f` is conjugate by bijections
to the action of `QuasicoherentAlgebra.pullback f` on their coordinate algebras. -/
private lemma overPullback_map_eq_conj {S T : Scheme.{u}} (f : T ⟶ S)
    (V W : AffineSchemeOver S) :
    let eDomain : (Over.mk V.hom ⟶ Over.mk W.hom) ≃
        (((affineFunctions S).obj W).unop ⟶ ((affineFunctions S).obj V).unop) :=
      { toFun g := ((affineFunctions S).map
          (MorphismProperty.Over.homMk g.left (Over.w g) : V ⟶ W)).unop
        invFun φ := Over.homMk ((affineFunctions S).preimage φ.op).left
          (MorphismProperty.Over.w ((affineFunctions S).preimage φ.op))
        left_inv g := by
          apply Over.OverMorphism.ext
          exact congrArg (·.left) ((affineFunctions S).preimage_map
            (MorphismProperty.Over.homMk g.left (Over.w g) : V ⟶ W))
        right_inv φ := congrArg Quiver.Hom.unop ((affineFunctions S).map_preimage φ.op) }
    ∃ eCodomain :
      ((Over.pullback f).obj (Over.mk V.hom) ⟶ (Over.pullback f).obj (Over.mk W.hom)) ≃
        ((QuasicoherentAlgebra.pullback f).obj ((affineFunctions S).obj W).unop ⟶
          (QuasicoherentAlgebra.pullback f).obj ((affineFunctions S).obj V).unop),
      ∀ g : Over.mk V.hom ⟶ Over.mk W.hom,
        eCodomain ((Over.pullback f).map g) =
          (QuasicoherentAlgebra.pullback f).map (eDomain g) := by
  intro eDomain
  let A := ((affineFunctions S).obj V).unop
  let B := ((affineFunctions S).obj W).unop
  let cV : (relativeSpec S).obj (op A) ≅ V := (relativeSpecCounit S).app V
  let cW : (relativeSpec S).obj (op B) ≅ W := (relativeSpecCounit S).app W
  let bV : (relativeSpec T).obj (op ((QuasicoherentAlgebra.pullback f).obj A)) ≅
      (baseChangeAffineSchemeOver f).obj V :=
    (relativeSpecBaseChangeIso f).app (op A) ≪≫ (baseChangeAffineSchemeOver f).mapIso cV
  let bW : (relativeSpec T).obj (op ((QuasicoherentAlgebra.pullback f).obj B)) ≅
      (baseChangeAffineSchemeOver f).obj W :=
    (relativeSpecBaseChangeIso f).app (op B) ≪≫ (baseChangeAffineSchemeOver f).mapIso cW
  have : MorphismProperty.HasPullbacksAlong (@IsAffineHom : MorphismProperty Scheme.{u}) f :=
    ⟨fun _ _ ↦ inferInstance⟩
  have : MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsAffineHom : MorphismProperty Scheme.{u}) f :=
    ⟨fun h hg ↦ isAffineHom_isStableUnderBaseChange.of_isPullback h hg⟩
  let isoF := MorphismProperty.Over.pullbackCompForgetIso
    (P := (@IsAffineHom : MorphismProperty Scheme.{u})) (Q := ⊤) f
  let fV : (MorphismProperty.Over.forget (@IsAffineHom) ⊤ T).obj
      ((baseChangeAffineSchemeOver f).obj V) ≅ (Over.pullback f).obj (Over.mk V.hom) :=
    isoF.app V
  let fW : (MorphismProperty.Over.forget (@IsAffineHom) ⊤ T).obj
      ((baseChangeAffineSchemeOver f).obj W) ≅ (Over.pullback f).obj (Over.mk W.hom) :=
    isoF.app W
  let eCod :
      ((Over.pullback f).obj (Over.mk V.hom) ⟶ (Over.pullback f).obj (Over.mk W.hom)) ≃
        ((QuasicoherentAlgebra.pullback f).obj B ⟶ (QuasicoherentAlgebra.pullback f).obj A) :=
    { toFun h :=
        ((relativeSpec T).preimage
          (bV.hom ≫
            MorphismProperty.Over.homMk (fV.hom ≫ h ≫ fW.inv).left (Over.w _) ≫
            bW.inv)).unop
      invFun ψ :=
        fV.inv ≫
          (MorphismProperty.Over.forget (@IsAffineHom) ⊤ T).map
            (bV.inv ≫ (relativeSpec T).map ψ.op ≫ bW.hom) ≫
          fW.hom
      left_inv h := by
        apply Over.OverMorphism.ext
        have hpre : (relativeSpec T).map
            ((relativeSpec T).preimage
              (bV.hom ≫
                MorphismProperty.Over.homMk (fV.hom ≫ h ≫ fW.inv).left (Over.w _) ≫
                bW.inv)) =
            bV.hom ≫
              MorphismProperty.Over.homMk (fV.hom ≫ h ≫ fW.inv).left (Over.w _) ≫
              bW.inv :=
          (relativeSpec T).map_preimage _
        have hcomp : bV.inv ≫ (relativeSpec T).map
            ((relativeSpec T).preimage
              (bV.hom ≫
                MorphismProperty.Over.homMk (fV.hom ≫ h ≫ fW.inv).left (Over.w _) ≫
                bW.inv)) ≫ bW.hom =
            MorphismProperty.Over.homMk (fV.hom ≫ h ≫ fW.inv).left (Over.w _) :=
          (congrArg (fun k ↦ bV.inv ≫ k ≫ bW.hom) hpre).trans (by
            simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id])
        have hmap :
            (MorphismProperty.Over.forget (@IsAffineHom) ⊤ T).map
                (bV.inv ≫ (relativeSpec T).map
                  ((relativeSpec T).preimage
                    (bV.hom ≫
                      MorphismProperty.Over.homMk (fV.hom ≫ h ≫ fW.inv).left (Over.w _) ≫
                      bW.inv)) ≫ bW.hom) =
              fV.hom ≫ h ≫ fW.inv := by
          rw [hcomp]
          exact Over.OverMorphism.ext rfl
        have hfin : fV.inv ≫ (fV.hom ≫ h ≫ fW.inv) ≫ fW.hom = h := by
          simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
        exact congrArg Over.Hom.left ((congrArg (fun k ↦ fV.inv ≫ k ≫ fW.hom) hmap).trans hfin)
      right_inv ψ := by
        apply Quiver.Hom.op_inj
        apply (relativeSpec T).map_injective
        rw [Quiver.Hom.op_unop, (relativeSpec T).map_preimage]
        have hmid : fV.hom ≫
            (fV.inv ≫
              (MorphismProperty.Over.forget (@IsAffineHom) ⊤ T).map
                (bV.inv ≫ (relativeSpec T).map ψ.op ≫ bW.hom) ≫
              fW.hom) ≫ fW.inv =
            (MorphismProperty.Over.forget (@IsAffineHom) ⊤ T).map
              (bV.inv ≫ (relativeSpec T).map ψ.op ≫ bW.hom) := by
          simp only [Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
        have hmk : (MorphismProperty.Over.homMk
            (fV.hom ≫
              (fV.inv ≫
                (MorphismProperty.Over.forget (@IsAffineHom) ⊤ T).map
                  (bV.inv ≫ (relativeSpec T).map ψ.op ≫ bW.hom) ≫
                fW.hom) ≫ fW.inv).left (Over.w _) :
            (baseChangeAffineSchemeOver f).obj V ⟶ (baseChangeAffineSchemeOver f).obj W) =
            bV.inv ≫ (relativeSpec T).map ψ.op ≫ bW.hom := by
          apply MorphismProperty.Over.Hom.ext
          exact congrArg Over.Hom.left hmid
        exact (congrArg (fun k ↦ bV.hom ≫ k ≫ bW.inv) hmk).trans (by
          simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]) }
  refine ⟨eCod, fun g ↦ ?_⟩
  let g' : V ⟶ W := MorphismProperty.Over.homMk g.left (Over.w g)
  have h1 : (MorphismProperty.Over.homMk
      (fV.hom ≫ (Over.pullback f).map g ≫ fW.inv).left (Over.w _) :
      (baseChangeAffineSchemeOver f).obj V ⟶ (baseChangeAffineSchemeOver f).obj W) =
      (baseChangeAffineSchemeOver f).map g' := by
    apply MorphismProperty.Over.Hom.ext
    have hnat : (MorphismProperty.Over.forget (@IsAffineHom) ⊤ T).map
          ((baseChangeAffineSchemeOver f).map g') ≫ fW.hom =
        fV.hom ≫ (Over.pullback f).map g := by
      have hn := isoF.hom.naturality g'
      have hfg' : (MorphismProperty.Over.forget (@IsAffineHom) ⊤ S).map g' = g :=
        Over.OverMorphism.ext rfl
      dsimp only [Functor.comp_map] at hn
      rw [hfg'] at hn
      exact hn
    have hinv : fV.hom ≫ (Over.pullback f).map g ≫ fW.inv =
        (MorphismProperty.Over.forget (@IsAffineHom) ⊤ T).map
          ((baseChangeAffineSchemeOver f).map g') := by
      rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact congrArg Over.Hom.left hinv
  have h2 : cV.hom ≫ g' ≫ cW.inv = (relativeSpec S).map (eDomain g).op := by
    have hnat : (relativeSpec S).map (eDomain g).op ≫ cW.hom = cV.hom ≫ g' :=
      (relativeSpecCounit S).hom.naturality g'
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h3 : bV.hom ≫ (baseChangeAffineSchemeOver f).map g' ≫ bW.inv =
      (relativeSpec T).map ((QuasicoherentAlgebra.pullback f).map (eDomain g)).op := by
    have hcomp :
        (baseChangeAffineSchemeOver f).map cV.hom ≫
          (baseChangeAffineSchemeOver f).map g' ≫
          (baseChangeAffineSchemeOver f).map cW.inv =
        (baseChangeAffineSchemeOver f).map ((relativeSpec S).map (eDomain g).op) := by
      rw [← Functor.map_comp, ← Functor.map_comp, h2]
    have hnat :
        (relativeSpec T).map ((QuasicoherentAlgebra.pullback f).map (eDomain g)).op ≫
            ((relativeSpecBaseChangeIso f).app (op B)).hom =
          ((relativeSpecBaseChangeIso f).app (op A)).hom ≫
            (baseChangeAffineSchemeOver f).map ((relativeSpec S).map (eDomain g).op) :=
      (relativeSpecBaseChangeIso f).hom.naturality (eDomain g).op
    calc
      bV.hom ≫ (baseChangeAffineSchemeOver f).map g' ≫ bW.inv
          = ((relativeSpecBaseChangeIso f).app (op A)).hom ≫
              ((baseChangeAffineSchemeOver f).map cV.hom ≫
                (baseChangeAffineSchemeOver f).map g' ≫
                (baseChangeAffineSchemeOver f).map cW.inv) ≫
              ((relativeSpecBaseChangeIso f).app (op B)).inv := by
            simp only [bV, bW, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
              Category.assoc]
      _ = (((relativeSpecBaseChangeIso f).app (op A)).hom ≫
              (baseChangeAffineSchemeOver f).map ((relativeSpec S).map (eDomain g).op)) ≫
            ((relativeSpecBaseChangeIso f).app (op B)).inv := by
            rw [hcomp, Category.assoc]
      _ = (relativeSpec T).map ((QuasicoherentAlgebra.pullback f).map (eDomain g)).op := by
            rw [← hnat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply Quiver.Hom.op_inj
  apply (relativeSpec T).map_injective
  have heCod : (eCod ((Over.pullback f).map g)).op =
      (relativeSpec T).preimage
        (bV.hom ≫
          MorphismProperty.Over.homMk (fV.hom ≫ (Over.pullback f).map g ≫ fW.inv).left (Over.w _) ≫
          bW.inv) :=
    Quiver.Hom.op_unop _
  exact (congrArg (relativeSpec T).map heCod).trans
    (((relativeSpec T).map_preimage _).trans
      ((congrArg (fun k ↦ bV.hom ≫ k ≫ bW.inv) h1).trans h3))

/-- If completion is faithful on finite locally free sheaves, then base change along any closed
immersion `j : X₀ ⟶ X` with `j.ker = I` is injective on `X`-morphisms from a finite locally free
scheme `Y ⟶ X` into a finite locally free, formally unramified scheme `Z ⟶ X`. -/
theorem overPullback_map_injective_of_completion_finiteLocallyFree
    (j : X₀ ⟶ X) [IsClosedImmersion j] (hj : j.ker = I)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful]
    {Y Z : Scheme.{u}} (p : Y ⟶ X) (q : Z ⟶ X)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
    [IsFinite q] [Flat q] [LocallyOfFinitePresentation q] [FormallyUnramified q] :
    Function.Injective
      (fun g : Over.mk p ⟶ Over.mk q ↦ (Over.pullback j).map g) := by
  refine overPullback_map_injective_of_fac_iso (isoFormalCompletionZeroOfKerEq I j hj)
    (isoFormalCompletionZeroOfKerEq_hom_comp I j hj) ?_
  let i₀ : (X.formalCompletion I).X 0 ⟶ X := Scheme.formalCompletion.toScheme X I 0
  let V : AffineSchemeOver X := MorphismProperty.Over.mk ⊤ p inferInstance
  let W : AffineSchemeOver X := MorphismProperty.Over.mk ⊤ q inferInstance
  let A := ((affineFunctions X).obj V).unop
  let B := ((affineFunctions X).obj W).unop
  have hA : Scheme.Modules.isFiniteLocallyFree X A.obj.X := p.isFiniteLocallyFree_pushforward_unit
  have hB : Scheme.Modules.isFiniteLocallyFree X B.obj.X := q.isFiniteLocallyFree_pushforward_unit
  have : FormallyUnramified B.obj.relativeSpecToBase := by
    let cW := (relativeSpecCounit X).app W
    have : IsIso cW.hom.left :=
      ((MorphismProperty.Over.forget (@IsAffineHom) ⊤ X ⋙ Over.forget X).mapIso cW).isIso_hom
    have : FormallyUnramified cW.hom.left :=
      (Etale.iff_flat_and_formallyUnramified.mp inferInstance).2.1
    have hcomp : FormallyUnramified (cW.hom.left ≫ q) :=
      MorphismProperty.comp_mem (@FormallyUnramified) cW.hom.left q ‹_› ‹_›
    have hw : cW.hom.left ≫ q = B.obj.relativeSpecToBase := MorphismProperty.Over.w cW.hom
    exact hw ▸ hcomp
  obtain ⟨eCod, heCod⟩ := overPullback_map_eq_conj i₀ V W
  intro g₁ g₂ h
  have h1 := (heCod g₁).symm.trans ((congrArg eCod h).trans (heCod g₂))
  have h2 := QuasicoherentAlgebra.pullback_toScheme_zero_map_injective X I hA hB h1
  apply Over.OverMorphism.ext
  have h3 : (affineFunctions X).map (MorphismProperty.Over.homMk g₁.left (Over.w g₁) : V ⟶ W) =
      (affineFunctions X).map (MorphismProperty.Over.homMk g₂.left (Over.w g₂) : V ⟶ W) :=
    congrArg Quiver.Hom.op h2
  exact congrArg (·.left) ((affineFunctions X).map_injective h3)

/-- If completion is fully faithful on finite locally free sheaves, then base change along any
closed immersion `j : X₀ ⟶ X` with `j.ker = I` is bijective from `X`-morphisms `Y ⟶ Z` (for finite
locally free `Y ⟶ X` and finite étale `Z ⟶ X`) to `X₀`-morphisms `Y ×_X X₀ ⟶ Z ×_X X₀`. -/
theorem overPullback_map_bijective_of_completion_finiteLocallyFree
    (j : X₀ ⟶ X) [IsClosedImmersion j] (hj : j.ker = I)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful]
    {Y Z : Scheme.{u}} (p : Y ⟶ X) (q : Z ⟶ X)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
    [IsFinite q] [Etale q] :
    Function.Bijective
      (fun g : Over.mk p ⟶ Over.mk q ↦ (Over.pullback j).map g) := by
  have ⟨_, _, _⟩ : Flat q ∧ FormallyUnramified q ∧ LocallyOfFinitePresentation q :=
    Etale.iff_flat_and_formallyUnramified.mp inferInstance
  refine ⟨overPullback_map_injective_of_completion_finiteLocallyFree I j hj p q, ?_⟩
  refine overPullback_map_surjective_of_fac_iso (isoFormalCompletionZeroOfKerEq I j hj)
    (isoFormalCompletionZeroOfKerEq_hom_comp I j hj) ?_
  let i₀ : (X.formalCompletion I).X 0 ⟶ X := Scheme.formalCompletion.toScheme X I 0
  let V : AffineSchemeOver X := MorphismProperty.Over.mk ⊤ p inferInstance
  let W : AffineSchemeOver X := MorphismProperty.Over.mk ⊤ q inferInstance
  let A := ((affineFunctions X).obj V).unop
  let B := ((affineFunctions X).obj W).unop
  have hA : Scheme.Modules.isFiniteLocallyFree X A.obj.X := p.isFiniteLocallyFree_pushforward_unit
  have hB : Scheme.Modules.isFiniteLocallyFree X B.obj.X := q.isFiniteLocallyFree_pushforward_unit
  have : Etale B.obj.relativeSpecToBase := by
    let cW := (relativeSpecCounit X).app W
    have : IsIso cW.hom.left :=
      ((MorphismProperty.Over.forget (@IsAffineHom) ⊤ X ⋙ Over.forget X).mapIso cW).isIso_hom
    have : Etale cW.hom.left := inferInstance
    have hcomp : Etale (cW.hom.left ≫ q) :=
      MorphismProperty.comp_mem (@Etale) cW.hom.left q ‹_› ‹_›
    have hw : cW.hom.left ≫ q = B.obj.relativeSpecToBase := MorphismProperty.Over.w cW.hom
    exact hw ▸ hcomp
  obtain ⟨eCod, heCod⟩ := overPullback_map_eq_conj i₀ V W
  intro g₀'
  obtain ⟨φ, hφ⟩ :=
    (QuasicoherentAlgebra.pullback_toScheme_zero_map_bijective X I hA hB).2 (eCod g₀')
  let gAff : V ⟶ W := (affineFunctions X).preimage φ.op
  let g : Over.mk p ⟶ Over.mk q := Over.homMk gAff.left (MorphismProperty.Over.w gAff)
  refine ⟨g, eCod.injective ?_⟩
  have hg_eq : ((affineFunctions X).map
      (MorphismProperty.Over.homMk g.left (Over.w g) : V ⟶ W)).unop = φ := by
    have : (MorphismProperty.Over.homMk g.left (Over.w g) : V ⟶ W) = gAff :=
      MorphismProperty.Over.Hom.ext rfl
    rw [this]
    exact congrArg Quiver.Hom.unop ((affineFunctions X).map_preimage φ.op)
  exact (heCod g).trans ((congrArg (QuasicoherentAlgebra.pullback i₀).map hg_eq).trans hφ)

end ClosedImmersion

end TauCeti.AlgebraicGeometry

namespace TauCeti.FiniteEtaleScheme

open TauCeti.AlgebraicGeometry

variable {X X₀ : Scheme.{u}} (I : X.IdealSheafData)

/-- If completion is faithful on finite locally free sheaves on `X`, then restriction of finite
étale schemes along any closed immersion `j : X₀ ⟶ X` with `j.ker = I` is faithful. -/
theorem faithful_pullback_of_completion_finiteLocallyFree
    (j : X₀ ⟶ X) [IsClosedImmersion j] (hj : j.ker = I)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback j).Faithful where
  map_injective {Y Z} g₁ g₂ h := by
    have ⟨_, _, _⟩ : Flat Y.obj.hom ∧ FormallyUnramified Y.obj.hom ∧
        LocallyOfFinitePresentation Y.obj.hom :=
      Etale.iff_flat_and_formallyUnramified.mp inferInstance
    have ⟨_, _, _⟩ : Flat Z.obj.hom ∧ FormallyUnramified Z.obj.hom ∧
        LocallyOfFinitePresentation Z.obj.hom :=
      Etale.iff_flat_and_formallyUnramified.mp inferInstance
    exact ObjectProperty.hom_ext _
      (overPullback_map_injective_of_completion_finiteLocallyFree I j hj Y.obj.hom Z.obj.hom
        (congrArg (·.hom) h))

/-- If completion is fully faithful on finite locally free sheaves on `X`, then restriction of
finite étale schemes along any closed immersion `j : X₀ ⟶ X` with `j.ker = I` is full. -/
theorem full_pullback_of_completion_finiteLocallyFree
    (j : X₀ ⟶ X) [IsClosedImmersion j] (hj : j.ker = I)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback j).Full where
  map_surjective {Y Z} g₀ := by
    have ⟨_, _, _⟩ : Flat Y.obj.hom ∧ FormallyUnramified Y.obj.hom ∧
        LocallyOfFinitePresentation Y.obj.hom :=
      Etale.iff_flat_and_formallyUnramified.mp inferInstance
    obtain ⟨g, hg⟩ :=
      (overPullback_map_bijective_of_completion_finiteLocallyFree I j hj Y.obj.hom Z.obj.hom).2
        g₀.hom
    exact ⟨ObjectProperty.homMk g, ObjectProperty.hom_ext _ hg⟩

/-- **Formal comparison for finite étale covers (Stacks, Lemma 58.17.1).** Let `X` be a scheme, `I`
a quasi-coherent ideal sheaf on `X`, and `j : X₀ ⟶ X` a closed immersion with `j.ker = I`. If the
completion functor from finite locally free `𝒪_X`-modules to coherent formal modules on `X/V(I)` is
fully faithful, then pullback of finite étale schemes along `j` is fully faithful. -/
@[stacks 0EL8]
def fullyFaithfulPullbackOfCompletionFiniteLocallyFree
    (j : X₀ ⟶ X) [IsClosedImmersion j] (hj : j.ker = I)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback j).FullyFaithful :=
  have := faithful_pullback_of_completion_finiteLocallyFree I j hj
  have := full_pullback_of_completion_finiteLocallyFree I j hj
  .ofFullyFaithful _

/-- **Formal comparison for finite étale covers along `I.subschemeι` (Stacks, Lemma 58.17.1).**
If the completion functor from finite locally free `𝒪_X`-modules to coherent formal modules on
`X/V(I)` is fully faithful, then restriction of finite étale schemes to the closed subscheme `V(I)`
is fully faithful. -/
@[stacks 0EL8]
def fullyFaithfulPullbackSubschemeιOfCompletionFiniteLocallyFree
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).FullyFaithful :=
  fullyFaithfulPullbackOfCompletionFiniteLocallyFree I I.subschemeι I.ker_subschemeι

/-- If the completion functor on all finitely presented `𝒪_X`-modules is fully faithful, then
pullback of finite étale schemes along any closed immersion `j : X₀ ⟶ X` with `j.ker = I` is fully
faithful. -/
@[stacks 0EL8]
def fullyFaithfulPullbackOfCompletion
    (j : X₀ ⟶ X) [IsClosedImmersion j] (hj : j.ker = I)
    [(Scheme.formalCompletion.completionFunctor X I).Full]
    [(Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback j).FullyFaithful :=
  fullyFaithfulPullbackOfCompletionFiniteLocallyFree I j hj

/-- If the completion functor on all finitely presented `𝒪_X`-modules is fully faithful, then
restriction of finite étale schemes to the closed subscheme `V(I)` is fully faithful. -/
@[stacks 0EL8]
def fullyFaithfulPullbackSubschemeιOfCompletion
    [(Scheme.formalCompletion.completionFunctor X I).Full]
    [(Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).FullyFaithful :=
  fullyFaithfulPullbackOfCompletion I I.subschemeι I.ker_subschemeι

end TauCeti.FiniteEtaleScheme
