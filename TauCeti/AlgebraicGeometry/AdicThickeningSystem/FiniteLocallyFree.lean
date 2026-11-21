/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Basic
public import TauCeti.AlgebraicGeometry.RelativeSpec.PullbackAlgebra
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Etale
import TauCeti.AlgebraicGeometry.RelativeSpec.BaseChange
import TauCeti.AlgebraicGeometry.RelativeSpec.Equivalence
import TauCeti.AlgebraicGeometry.VectorBundle.Pushforward
import TauCeti.CategoryTheory.EqToHom
import TauCeti.CategoryTheory.Monoidal.EqToHom

/-!
# Formal algebraization for finite locally free algebras and morphisms

Given a scheme `X` and an ideal sheaf `I` on `X`, the completion functor
`Scheme.formalCompletion.completionFunctor X I` restricts to finite locally free sheaves on `X` as
`Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor X I`. In geometric algebraization
theorems (such as Stacks, Lemma 52.15.5 (0EKS) and Lemma 58.17.1 (0EL8)), completion is fully
faithful on finite locally free sheaves even when it fails to be faithful on arbitrary finitely
presented sheaves.

Because finite locally free `𝒪_X`-modules contain the structure sheaf `𝒪_X` and are closed under
tensor products, faithfulness of `finiteLocallyFreeCompletionFunctor X I` forces any `𝒪_X`-linear
map between finite locally free commutative `𝒪_X`-algebras whose reductions to all infinitesimal
neighbourhoods `V(I ^ (n + 1))` are algebra homomorphisms to be an algebra homomorphism on `X`.
Consequently:

* When `finiteLocallyFreeCompletionFunctor X I` is faithful, morphisms in `QuasicoherentAlgebra X`
  between finite locally free algebras—and hence morphisms over `X` between schemes that are
  finite, flat, and locally of finite presentation over `X`—are uniquely determined by the
  morphisms they induce on formal completions along the preimages of `I`.
* When `finiteLocallyFreeCompletionFunctor X I` is full and faithful, every compatible tower of
  algebra homomorphisms on the levels `V(I ^ (n + 1))`—and hence every morphism of formal
  completions over `X.formalCompletion I` between schemes that are finite, flat, and locally of
  finite presentation over `X`—algebraizes to a unique morphism over `X`.

No Noetherian hypothesis on `X` is needed: for any morphism `p : V ⟶ X` that is finite, flat, and
locally of finite presentation, the pushforward `p_* 𝒪_V` is already finite locally free
(`Scheme.Modules.isFiniteLocallyFree_pushforward_unit`).

## Main definitions

* `AlgebraicGeometry.Scheme.formalCompletion.algebraPullbackTransitionIso`: the canonical natural
  isomorphism identifying the pullback along `V(I ^ (n + 1)) ⟶ V(I ^ (n + 2))` of the `(n + 1)`-st
  reduction of a quasi-coherent `𝒪_X`-algebra with its `n`-th reduction.

## Main results

* `AlgebraicGeometry.Scheme.formalCompletion.hom_ext_quasicoherentAlgebra_of_isFiniteLocallyFree`
  and `exists_hom_quasicoherentAlgebra_of_isFiniteLocallyFree`: uniqueness and existence of
  algebraized morphisms in `QuasicoherentAlgebra X` between finite locally free algebras.
* `AlgebraicGeometry.Scheme.formalCompletion.hom_ext_of_isFinite_of_flat`,
  `AlgebraicGeometry.Scheme.formalCompletion.exists_hom_of_isFinite_of_flat`: uniqueness and
  existence of algebraized scheme morphisms over `X` between schemes that are finite, flat, and
  locally of finite presentation over `X`.
* `TauCeti.AlgebraicGeometry.overPullback_map_injective_of_completion_finiteLocallyFree` and
  `TauCeti.AlgebraicGeometry.overPullback_map_bijective_of_completion_finiteLocallyFree`:
  injectivity (for finite locally free, formally unramified target) and bijectivity (for finite
  étale target) of restriction along a closed immersion `j : X₀ ⟶ X` with `j.ker = I`.

## References

* [The Stacks Project, Tag 0EL8](https://stacks.math.columbia.edu/tag/0EL8)
* [The Stacks Project, Tag 0EKS](https://stacks.math.columbia.edu/tag/0EKS)
-/

public section

open CategoryTheory Limits MonoidalCategory Opposite AlgebraicGeometry
open scoped MonObj

universe u

namespace AlgebraicGeometry.Scheme.formalCompletion

open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.AdicThickeningSystem

/-! ### Algebraization for finite locally free quasi-coherent algebras -/

section Algebra

/-- Pulling back the `(n + 1)`-st formal reduction of a quasi-coherent commutative `𝒪_X`-algebra
along the transition `V(I ^ (n + 1)) ⟶ V(I ^ (n + 2))` recovers its `n`-th formal reduction,
naturally in the algebra. -/
noncomputable def algebraPullbackTransitionIso (X : Scheme.{u}) (I : X.IdealSheafData) (n : ℕ) :
    QuasicoherentAlgebra.pullback (toScheme X I (n + 1)) ⋙
        QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n) ≅
      QuasicoherentAlgebra.pullback (toScheme X I n) :=
  QuasicoherentAlgebra.pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1)) ≪≫
    QuasicoherentAlgebra.pullbackCongr (ι_toScheme X I n)

/-- Definitional expansion of `algebraPullbackTransitionIso`. -/
theorem algebraPullbackTransitionIso_def (X : Scheme.{u}) (I : X.IdealSheafData) (n : ℕ) :
    algebraPullbackTransitionIso X I n =
      QuasicoherentAlgebra.pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1)) ≪≫
        QuasicoherentAlgebra.pullbackCongr (ι_toScheme X I n) :=
  (rfl)

/-- On underlying `𝒪`-modules, `(algebraPullbackTransitionIso X I n).hom.app C` is the module
pullback composition isomorphism along `ι_toScheme X I n`, conjugated by
`QuasicoherentAlgebra.pullback_obj_X`. -/
@[simp]
theorem algebraPullbackTransitionIso_hom_app_hom_hom_hom (X : Scheme.{u}) (I : X.IdealSheafData)
    (n : ℕ) (C : QuasicoherentAlgebra X) :
    ((algebraPullbackTransitionIso X I n).hom.app C).hom.hom.hom =
      eqToHom ((QuasicoherentAlgebra.pullback_obj_X ((X.formalCompletion I).ι n) _).trans
        (congrArg (Modules.pullback ((X.formalCompletion I).ι n)).obj
          (QuasicoherentAlgebra.pullback_obj_X (toScheme X I (n + 1)) C))) ≫
        ((Modules.pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1)) ≪≫
            Modules.pullbackCongr (ι_toScheme X I n)).app C.obj.X).hom ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) C).symm :=
  QuasicoherentAlgebra.pullbackComp_pullbackCongr_hom_app_hom_hom_hom _ _ (ι_toScheme X I n) C

/-- On underlying `𝒪`-modules, `(algebraPullbackTransitionIso X I n).inv.app C` is the inverse
module pullback composition isomorphism along `ι_toScheme X I n`, conjugated by
`QuasicoherentAlgebra.pullback_obj_X`. -/
@[simp]
theorem algebraPullbackTransitionIso_inv_app_hom_hom_hom (X : Scheme.{u}) (I : X.IdealSheafData)
    (n : ℕ) (C : QuasicoherentAlgebra X) :
    ((algebraPullbackTransitionIso X I n).inv.app C).hom.hom.hom =
      eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) C) ≫
        ((Modules.pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1)) ≪≫
            Modules.pullbackCongr (ι_toScheme X I n)).app C.obj.X).inv ≫
          eqToHom ((QuasicoherentAlgebra.pullback_obj_X ((X.formalCompletion I).ι n) _).trans
            (congrArg (Modules.pullback ((X.formalCompletion I).ι n)).obj
              (QuasicoherentAlgebra.pullback_obj_X (toScheme X I (n + 1)) C))).symm :=
  QuasicoherentAlgebra.pullbackComp_pullbackCongr_inv_app_hom_hom_hom _ _ (ι_toScheme X I n) C

variable {X : Scheme.{u}}

/-- If `finiteLocallyFreeCompletionFunctor X I` is faithful, two morphisms in
`QuasicoherentAlgebra X` between algebras with finite locally free underlying `𝒪_X`-modules are
equal as soon as their pullbacks to all levels `V(I ^ (n + 1))` agree. -/
theorem hom_ext_quasicoherentAlgebra_of_isFiniteLocallyFree (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletionFunctor X I).Faithful]
    {B A : QuasicoherentAlgebra X}
    (hB : Modules.isFiniteLocallyFree X B.obj.X)
    (hA : Modules.isFiniteLocallyFree X A.obj.X)
    {f g : B ⟶ A}
    (h : ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).map f =
      (QuasicoherentAlgebra.pullback (toScheme X I n)).map g) :
    f = g := by
  apply ObjectProperty.hom_ext
  apply CommMon.hom_ext
  refine hom_ext_of_isFiniteLocallyFree I hB hA fun n ↦ ?_
  have hn := congrArg (fun k ↦ k.hom.hom.hom) (h n)
  exact TauCeti.eq_of_eqToHom_conjugate
    (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B)
    (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A).symm
    ((QuasicoherentAlgebra.pullback_map_hom_hom_hom (toScheme X I n) f).symm.trans
      (hn.trans (QuasicoherentAlgebra.pullback_map_hom_hom_hom (toScheme X I n) g)))

/-- Auxiliary lemma: if an `𝒪_X`-module morphism `f : B.obj.X ⟶ A.obj.X` between finite locally
free quasi-coherent algebras reduces on every level `V(I ^ (n + 1))` to an algebra homomorphism
`ψ n`, and `finiteLocallyFreeCompletionFunctor X I` is faithful, then `f` preserves the unit and
multiplication of `B` and `A`. -/
private lemma isMonHom_of_forall_pullback_eq (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletionFunctor X I).Faithful]
    {B A : QuasicoherentAlgebra X}
    (hB : Modules.isFiniteLocallyFree X B.obj.X)
    (hA : Modules.isFiniteLocallyFree X A.obj.X)
    (f : B.obj.X ⟶ A.obj.X)
    (ψ : ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).obj B ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A)
    (hf : ∀ n, (ψ n).hom.hom.hom =
      eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B) ≫
        (Modules.pullback (toScheme X I n)).map f ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A).symm) :
    IsMonHom f where
  one_hom :=
    hom_ext_of_isFiniteLocallyFree I
      (ObjectProperty.prop_unit (Modules.isFiniteLocallyFree X)) hA fun n ↦
        Functor.map_comp_eq_of_eqToHom_conjugate (Modules.pullback (toScheme X I n))
          (QuasicoherentAlgebra.pullback_obj_one (toScheme X I n) B)
          (QuasicoherentAlgebra.pullback_obj_one (toScheme X I n) A)
          (hf n) (IsMonHom.one_hom (ψ n).hom.hom.hom)
  mul_hom :=
    hom_ext_of_isFiniteLocallyFree I (ObjectProperty.prop_tensor hB hB) hA fun n ↦
      Functor.map_comp_eq_of_eqToHom_conjugate_tensor (Modules.pullback (toScheme X I n))
        (QuasicoherentAlgebra.pullback_obj_mul (toScheme X I n) B)
        (QuasicoherentAlgebra.pullback_obj_mul (toScheme X I n) A)
        (hf n) (hf n) (hf n) (IsMonHom.mul_hom (ψ n).hom.hom.hom)

/-- Given a compatible family `ψ n` of algebra homomorphisms between the formal reductions of two
finite locally free quasi-coherent `𝒪_X`-algebras `B` and `A`, transport them along
`QuasicoherentAlgebra.pullback_obj_X` to a morphism of coherent formal modules. -/
private noncomputable def formalModuleHomOfAlgebraPullbacks (I : X.IdealSheafData)
    {B A : QuasicoherentAlgebra X}
    (hB : Modules.isFiniteLocallyFree X B.obj.X)
    (hA : Modules.isFiniteLocallyFree X A.obj.X)
    (ψ : ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).obj B ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A)
    (hψ : ∀ n,
      (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1)) ≫
          (algebraPullbackTransitionIso X I n).hom.app A =
        (algebraPullbackTransitionIso X I n).hom.app B ≫ ψ n) :
    (finiteLocallyFreeCompletionFunctor X I).obj ⟨B.obj.X, hB⟩ ⟶
      (finiteLocallyFreeCompletionFunctor X I).obj ⟨A.obj.X, hA⟩ where
  app n := eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B).symm ≫
    (ψ n).hom.hom.hom ≫ eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A)
  naturality n := by
    simp only [Functor.comp_obj, completionFunctor_obj_transitionIso]
    dsimp only [FiniteLocallyFreeSheaf.toFinitelyPresented, ObjectProperty.ιOfLE]
    let hB₁ := QuasicoherentAlgebra.pullback_obj_X (toScheme X I (n + 1)) B
    let hA₁ := QuasicoherentAlgebra.pullback_obj_X (toScheme X I (n + 1)) A
    let hB₀ := QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B
    let hA₀ := QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A
    let hP := QuasicoherentAlgebra.pullback_obj_X ((X.formalCompletion I).ι n)
      ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj B)
    let hQ := QuasicoherentAlgebra.pullback_obj_X ((X.formalCompletion I).ι n)
      ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj A)
    let hP' := hP.trans (congrArg (Modules.pullback ((X.formalCompletion I).ι n)).obj hB₁)
    let hQ' := hQ.trans (congrArg (Modules.pullback ((X.formalCompletion I).ι n)).obj hA₁)
    refine (TauCeti.eqToHom_conjugate_square hP' hQ' hA₀ hB₀ _ _ _ _).mp ?_
    have hmap_conj := (Functor.eqToHom_conjugate_map_eqToHom_conjugate
      (Modules.pullback ((X.formalCompletion I).ι n)) hB₁ hA₁ hP hQ hP' hQ'
      (ψ (n + 1)).hom.hom.hom).trans
      (QuasicoherentAlgebra.pullback_map_hom_hom_hom ((X.formalCompletion I).ι n) (ψ (n + 1))).symm
    have hcan := TauCeti.eqToHom_conjugate_cancel hB₀.symm hA₀.symm (ψ n).hom.hom.hom
    exact (congrArg₂ CategoryStruct.comp hmap_conj
      (algebraPullbackTransitionIso_hom_app_hom_hom_hom X I n A).symm).trans
      ((congrArg (fun k ↦ k.hom.hom.hom) (hψ n)).trans
        (congrArg₂ CategoryStruct.comp
          (algebraPullbackTransitionIso_hom_app_hom_hom_hom X I n B) hcan.symm))

/-- If `finiteLocallyFreeCompletionFunctor X I` is full and faithful, every compatible family of
algebra morphisms between the formal reductions of two finite locally free quasi-coherent
`𝒪_X`-algebras comes from a morphism in `QuasicoherentAlgebra X`. -/
theorem exists_hom_quasicoherentAlgebra_of_isFiniteLocallyFree {I : X.IdealSheafData}
    [(finiteLocallyFreeCompletionFunctor X I).Full]
    [(finiteLocallyFreeCompletionFunctor X I).Faithful]
    {B A : QuasicoherentAlgebra X}
    (hB : Modules.isFiniteLocallyFree X B.obj.X)
    (hA : Modules.isFiniteLocallyFree X A.obj.X)
    (ψ : ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).obj B ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A)
    (hψ : ∀ n,
      (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1)) ≫
          (algebraPullbackTransitionIso X I n).hom.app A =
        (algebraPullbackTransitionIso X I n).hom.app B ≫ ψ n) :
    ∃ f : B ⟶ A, ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).map f = ψ n := by
  let φ := formalModuleHomOfAlgebraPullbacks I hB hA ψ hψ
  let f₀ := (finiteLocallyFreeCompletionFunctor X I).preimage φ
  have hf₀ (n : ℕ) : (ψ n).hom.hom.hom =
      eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B) ≫
        (Modules.pullback (toScheme X I n)).map f₀.hom ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A).symm := by
    have hmap := congrArg (fun k ↦ k.app n)
      ((finiteLocallyFreeCompletionFunctor X I).map_preimage φ)
    simp only [Functor.comp_map, completionFunctor_map_app] at hmap
    dsimp only [φ, formalModuleHomOfAlgebraPullbacks,
      FiniteLocallyFreeSheaf.toFinitelyPresented, ObjectProperty.ιOfLE] at hmap
    exact (TauCeti.eqToHom_conjugate_cancel
      (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B).symm
      (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A).symm
      (ψ n).hom.hom.hom).symm.trans
      (congrArg (fun u ↦ eqToHom _ ≫ u ≫ eqToHom _) hmap.symm)
  refine ⟨ObjectProperty.homMk (CommMon.homMk
    (@Mon.Hom.mk _ _ _ _ _ f₀.hom (isMonHom_of_forall_pullback_eq I hB hA f₀.hom ψ hf₀))),
    fun n ↦ ?_⟩
  apply ObjectProperty.hom_ext
  apply CommMon.hom_ext
  exact (QuasicoherentAlgebra.pullback_map_hom_hom_hom (toScheme X I n) _).trans (hf₀ n).symm

end Algebra

/-! ### Algebraization for finite locally free morphisms of schemes -/

section RelativeSpec

variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- Levelwise identification between the `n`-th level of the formal completion of `Spec_X(C)` along
`I.comap (Spec_X(C) ⟶ X)` and the relative spectrum over `V(I ^ (n + 1))` of the pulled-back
algebra `(toScheme X I n)^* C`. -/
private noncomputable def relativeSpecLevelIso (C : QuasicoherentAlgebra X) (n : ℕ) :
    (C.obj.relativeSpec.formalCompletion (I.comap C.obj.relativeSpecToBase)).X n ≅
      ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj C).obj.relativeSpec :=
  (isPullback_map_app C.obj.relativeSpecToBase rfl n).isoIsPullback _ _
    (isPullback_relativeSpecPullbackFst C (toScheme X I n))

@[reassoc (attr := simp)]
private lemma relativeSpecLevelIso_hom_fst (C : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecLevelIso (I := I) C n).hom ≫
        relativeSpecPullbackFst C (toScheme X I n) =
      toScheme C.obj.relativeSpec (I.comap C.obj.relativeSpecToBase) n :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

@[reassoc (attr := simp)]
private lemma relativeSpecLevelIso_hom_snd (C : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecLevelIso (I := I) C n).hom ≫
        ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj C).obj.relativeSpecToBase =
      (map (I := I.comap C.obj.relativeSpecToBase) C.obj.relativeSpecToBase le_rfl).app n :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

@[reassoc (attr := simp)]
private lemma relativeSpecLevelIso_inv_fst (C : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecLevelIso (I := I) C n).inv ≫
        toScheme C.obj.relativeSpec (I.comap C.obj.relativeSpecToBase) n =
      relativeSpecPullbackFst C (toScheme X I n) :=
  IsPullback.isoIsPullback_inv_fst _ _ _ _

@[reassoc (attr := simp)]
private lemma relativeSpecLevelIso_inv_snd (C : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecLevelIso (I := I) C n).inv ≫
        (map (I := I.comap C.obj.relativeSpecToBase) C.obj.relativeSpecToBase le_rfl).app n =
      ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj C).obj.relativeSpecToBase :=
  IsPullback.isoIsPullback_inv_snd _ _ _ _

/-- Under `relativeSpecLevelIso`, the `n`-th level of `formalCompletion.map` for
`CommMon.relativeSpecMap f.hom` is `CommMon.relativeSpecMap` of the pulled-back algebra map. -/
private lemma relativeSpecLevelIso_inv_map_app_hom {B A : QuasicoherentAlgebra X} (f : B ⟶ A)
    (hf : (I.comap B.obj.relativeSpecToBase).comap (CommMon.relativeSpecMap f.hom) ≤
      I.comap A.obj.relativeSpecToBase) (n : ℕ) :
    (relativeSpecLevelIso (I := I) A n).inv ≫
        (map (CommMon.relativeSpecMap f.hom) hf).app n ≫
          (relativeSpecLevelIso (I := I) B n).hom =
      CommMon.relativeSpecMap
        ((QuasicoherentAlgebra.pullback (toScheme X I n)).map f).hom := by
  refine (isPullback_relativeSpecPullbackFst B (toScheme X I n)).hom_ext ?_ ?_
  · simp [relativeSpecMap_pullback_map_relativeSpecPullbackFst]
  · have hcomp :
        map (CommMon.relativeSpecMap f.hom) hf ≫
          map (I := I.comap B.obj.relativeSpecToBase) B.obj.relativeSpecToBase le_rfl =
        map (I := I.comap A.obj.relativeSpecToBase) A.obj.relativeSpecToBase le_rfl :=
      map_comp_eq (CommMon.relativeSpecMap_relativeSpecToBase f.hom) _ _ _
    have hcomp_n : (map (CommMon.relativeSpecMap f.hom) hf).app n ≫
        (map (I := I.comap B.obj.relativeSpecToBase) B.obj.relativeSpecToBase le_rfl).app n =
        (map (I := I.comap A.obj.relativeSpecToBase) A.obj.relativeSpecToBase le_rfl).app n :=
      congrArg (·.app n) hcomp
    simp [hcomp_n, CommMon.relativeSpecMap_relativeSpecToBase]

/-- Under `relativeSpecLevelIso`, the transition morphism `ι n` of the formal completion of
`Spec_X(C)` corresponds to `algebraPullbackTransitionIso` composed with `relativeSpecPullbackFst`
along `(X.formalCompletion I).ι n`. -/
private lemma relativeSpecLevelIso_inv_ι_hom (C : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecLevelIso (I := I) C n).inv ≫
        (C.obj.relativeSpec.formalCompletion (I.comap C.obj.relativeSpecToBase)).ι n ≫
          (relativeSpecLevelIso (I := I) C (n + 1)).hom =
      CommMon.relativeSpecMap ((algebraPullbackTransitionIso X I n).hom.app C).hom ≫
        relativeSpecPullbackFst
          ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj C)
          ((X.formalCompletion I).ι n) := by
  refine (isPullback_relativeSpecPullbackFst C (toScheme X I (n + 1))).hom_ext ?_ ?_
  · simp only [Category.assoc]
    rw [algebraPullbackTransitionIso_def,
      relativeSpecMap_pullbackComp_pullbackCongr_fst C _ _ (ι_toScheme X I n)]
    simp
  · simp [AdicThickeningSystem.Hom.naturality,
      CommMon.relativeSpecMap_relativeSpecToBase_assoc,
      relativeSpecPullbackFst_relativeSpecToBase]

private lemma hom_ext_relativeSpec_of_isFiniteLocallyFree (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletionFunctor X I).Faithful]
    {B A : QuasicoherentAlgebra X}
    (hB : Modules.isFiniteLocallyFree X B.obj.X)
    (hA : Modules.isFiniteLocallyFree X A.obj.X)
    {f₁ f₂ : B ⟶ A}
    (hf₁ : (I.comap B.obj.relativeSpecToBase).comap (CommMon.relativeSpecMap f₁.hom) ≤
      I.comap A.obj.relativeSpecToBase)
    (hf₂ : (I.comap B.obj.relativeSpecToBase).comap (CommMon.relativeSpecMap f₂.hom) ≤
      I.comap A.obj.relativeSpecToBase)
    (h : map (CommMon.relativeSpecMap f₁.hom) hf₁ =
      map (CommMon.relativeSpecMap f₂.hom) hf₂) :
    f₁ = f₂ := by
  refine hom_ext_quasicoherentAlgebra_of_isFiniteLocallyFree I hB hA fun n ↦
    eq_of_relativeSpecMap_eq ?_
  rw [← relativeSpecLevelIso_inv_map_app_hom (I := I) f₁ hf₁ n,
    ← relativeSpecLevelIso_inv_map_app_hom (I := I) f₂ hf₂ n, h]

/-- Compatibility of levelwise algebra maps `ψ n` extracted from a morphism `a` of formal
completions of relative spectra with the transition morphisms `(X.formalCompletion I).ι n`. -/
private lemma relativeSpecMap_pullback_ι_eq
    {B A : QuasicoherentAlgebra X}
    (a : A.obj.relativeSpec.formalCompletion (I.comap A.obj.relativeSpecToBase) ⟶
      B.obj.relativeSpec.formalCompletion (I.comap B.obj.relativeSpecToBase))
    (ψ : ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).obj B ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A)
    (hψ_spec : ∀ n, CommMon.relativeSpecMap (ψ n).hom =
      (relativeSpecLevelIso (I := I) A n).inv ≫ a.app n ≫
        (relativeSpecLevelIso (I := I) B n).hom)
    (n : ℕ) :
    CommMon.relativeSpecMap ((algebraPullbackTransitionIso X I n).hom.app A).hom ≫
        CommMon.relativeSpecMap
          ((QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1))).hom =
      CommMon.relativeSpecMap (ψ n).hom ≫
        CommMon.relativeSpecMap ((algebraPullbackTransitionIso X I n).hom.app B).hom := by
  refine (isPullback_relativeSpecPullbackFst
    ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj B)
    ((X.formalCompletion I).ι n)).hom_ext ?_ ?_
  · rw [Category.assoc, relativeSpecMap_pullback_map_relativeSpecPullbackFst,
      ← Category.assoc, ← relativeSpecLevelIso_inv_ι_hom (I := I) A n,
      hψ_spec (n + 1), hψ_spec n, Category.assoc, Category.assoc,
      Category.assoc, ← relativeSpecLevelIso_inv_ι_hom (I := I) B n]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% (a.naturality n)]
  · simp [CommMon.relativeSpecMap_relativeSpecToBase]

private lemma exists_hom_relativeSpec_of_isFiniteLocallyFree (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletionFunctor X I).Full]
    [(finiteLocallyFreeCompletionFunctor X I).Faithful]
    {B A : QuasicoherentAlgebra X}
    (hB : Modules.isFiniteLocallyFree X B.obj.X)
    (hA : Modules.isFiniteLocallyFree X A.obj.X)
    (a : A.obj.relativeSpec.formalCompletion (I.comap A.obj.relativeSpecToBase) ⟶
      B.obj.relativeSpec.formalCompletion (I.comap B.obj.relativeSpecToBase))
    (ha : a ≫ map B.obj.relativeSpecToBase le_rfl = map A.obj.relativeSpecToBase le_rfl) :
    ∃ f : B ⟶ A,
      map (CommMon.relativeSpecMap f.hom)
        (by rw [← IdealSheafData.comap_comp, CommMon.relativeSpecMap_relativeSpecToBase]) = a := by
  -- At each level `n`, `a.app n` conjugates to a morphism of affine schemes over `V(I ^ (n + 1))`,
  -- hence comes from a unique algebra map `ψ n` by the relative-Spec anti-equivalence.
  let g (n : ℕ) :
      ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A).obj.relativeSpec ⟶
        ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj B).obj.relativeSpec :=
    (relativeSpecLevelIso (I := I) A n).inv ≫ a.app n ≫
      (relativeSpecLevelIso (I := I) B n).hom
  have hg (n : ℕ) :
      g n ≫ ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj B).obj.relativeSpecToBase =
        ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A).obj.relativeSpecToBase := by
    have ha_n : a.app n ≫ (map B.obj.relativeSpecToBase le_rfl).app n =
        (map A.obj.relativeSpecToBase le_rfl).app n :=
      congrArg (·.app n) ha
    simp [g, ha_n]
  let G (n : ℕ) :
      (relativeSpec ((X.formalCompletion I).X n)).obj
          (op ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A)) ⟶
        (relativeSpec ((X.formalCompletion I).X n)).obj
          (op ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj B)) :=
    MorphismProperty.Over.homMk (g n) (hg n)
  let ψ (n : ℕ) : (QuasicoherentAlgebra.pullback (toScheme X I n)).obj B ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A :=
    ((relativeSpec ((X.formalCompletion I).X n)).preimage (G n)).unop
  have hψ_spec (n : ℕ) : CommMon.relativeSpecMap (ψ n).hom = g n := by
    rw [← relativeSpec_map_left ((relativeSpec ((X.formalCompletion I).X n)).preimage (G n))]
    exact congrArg (·.left) ((relativeSpec ((X.formalCompletion I).X n)).map_preimage (G n))
  obtain ⟨f, hf⟩ := exists_hom_quasicoherentAlgebra_of_isFiniteLocallyFree (I := I) hB hA ψ
    fun n ↦ eq_of_relativeSpecMap_eq <| by
      simp only [ObjectProperty.FullSubcategory.comp_hom, CommMon.relativeSpecMap_comp]
      exact relativeSpecMap_pullback_ι_eq (I := I) a ψ hψ_spec n
  refine ⟨f, ?_⟩
  ext n
  have h1 := (relativeSpecLevelIso_inv_map_app_hom (I := I) f
    (by rw [← IdealSheafData.comap_comp, CommMon.relativeSpecMap_relativeSpecToBase]) n).trans
    ((congrArg (fun k ↦ CommMon.relativeSpecMap k.hom) (hf n)).trans (hψ_spec n))
  dsimp only [g] at h1
  exact (cancel_epi (relativeSpecLevelIso (I := I) A n).inv).mp
    ((cancel_mono (relativeSpecLevelIso (I := I) B n).hom).mp h1)

end RelativeSpec

section FiniteFlat

/-- Transporting algebraization of a formal-completion morphism across scheme isomorphisms over `X`.
Used to pass between arbitrary finite flat schemes and the relative spectra of their pushforward
structure algebras. -/
private lemma exists_hom_of_isIso_over {X V V' W W' : Scheme.{u}} {I : X.IdealSheafData}
    {p : V ⟶ X} {p' : V' ⟶ X} {q : W ⟶ X} {q' : W' ⟶ X}
    (u : V' ⟶ V) [IsIso u] (hu : u ≫ p = p')
    (v : W' ⟶ W) [IsIso v] (hv : v ≫ q = q')
    (a : V.formalCompletion (I.comap p) ⟶ W.formalCompletion (I.comap q))
    (ha : a ≫ map q le_rfl = map p le_rfl)
    (h_lift : ∀ a' : V'.formalCompletion (I.comap p') ⟶ W'.formalCompletion (I.comap q'),
      a' ≫ map q' le_rfl = map p' le_rfl →
      ∃ (s : V' ⟶ W') (hs : s ≫ q' = p'),
        map s (by rw [← IdealSheafData.comap_comp, hs]) = a') :
    ∃ (g : V ⟶ W) (hg : g ≫ q = p),
      map g (by rw [← IdealSheafData.comap_comp, hg]) = a := by
  have hu_eq : (I.comap p).comap (asIso u).hom = I.comap p' := by
    rw [asIso_hom, ← IdealSheafData.comap_comp, hu]
  have hv_eq : (I.comap q).comap (asIso v).hom = I.comap q' := by
    rw [asIso_hom, ← IdealSheafData.comap_comp, hv]
  let eU := mapIso (asIso u) hu_eq
  let eV := mapIso (asIso v) hv_eq
  let a' : V'.formalCompletion (I.comap p') ⟶ W'.formalCompletion (I.comap q') :=
    eU.hom ≫ a ≫ eV.inv
  have ha' : a' ≫ map q' le_rfl = map p' le_rfl := by
    have hv_inv : (asIso v).inv ≫ q' = q := by rw [asIso_inv, ← hv, IsIso.inv_hom_id_assoc]
    rw [show a' = eU.hom ≫ a ≫ eV.inv from rfl, Category.assoc, Category.assoc,
      mapIso_inv, map_comp_eq hv_inv _ _ le_rfl, ha, mapIso_hom,
      map_comp_eq (by rw [asIso_hom, hu]) _ _ le_rfl]
  obtain ⟨s, hs, hs_map⟩ := h_lift a' ha'
  have hg : (inv u ≫ s ≫ v) ≫ q = p := by
    rw [Category.assoc, Category.assoc, hv, hs, ← hu, IsIso.inv_hom_id_assoc]
  refine ⟨inv u ≫ s ≫ v, hg, ?_⟩
  have hcomp : map (inv u ≫ s ≫ v) (by rw [← IdealSheafData.comap_comp, hg]) =
      eU.inv ≫ map s (by rw [← IdealSheafData.comap_comp, hs]) ≫ eV.hom := by
    rw [mapIso_inv, mapIso_hom,
      map_comp_eq (g := (asIso v).hom) (h := s ≫ v) (by simp) _ _
        (by rw [← IdealSheafData.comap_comp, Category.assoc, hv, hs]),
      map_comp_eq (f := (asIso u).inv) (h := inv u ≫ s ≫ v) (by simp)]
  rw [hcomp, hs_map]
  simp [a', eU, eV]

/-- Formal-completion counterpart of `Scheme.Hom.relativeSpecFunctionsToScheme_naturality`:
for affine morphisms `p : V ⟶ X` and `q : W ⟶ X` and a morphism `g : V ⟶ W` over `X`,
completing the relative-Spec counit naturality square yields a commuting square of formal
completions. -/
private lemma map_relativeSpecFunctionsToScheme_naturality
    {X V W : Scheme.{u}} {I : X.IdealSheafData}
    {p : V ⟶ X} {q : W ⟶ X} [IsAffineHom p] [IsAffineHom q]
    (g : V ⟶ W) (hg : g ≫ q = p)
    (hm_le : (I.comap q.pushforwardStructureAlgebra.relativeSpecToBase).comap
        (CommMon.relativeSpecMap (Scheme.Hom.pushforwardStructureAlgebraMap g hg)) ≤
      I.comap p.pushforwardStructureAlgebra.relativeSpecToBase)
    (hq_le : (I.comap q).comap q.relativeSpecFunctionsToScheme ≤
      I.comap q.pushforwardStructureAlgebra.relativeSpecToBase)
    (hp_le : (I.comap p).comap p.relativeSpecFunctionsToScheme ≤
      I.comap p.pushforwardStructureAlgebra.relativeSpecToBase)
    (hg_le : (I.comap q).comap g ≤ I.comap p) :
    map (CommMon.relativeSpecMap (Scheme.Hom.pushforwardStructureAlgebraMap g hg)) hm_le ≫
        map q.relativeSpecFunctionsToScheme hq_le =
      map p.relativeSpecFunctionsToScheme hp_le ≫ map g hg_le :=
  (map_comp_eq (Scheme.Hom.relativeSpecFunctionsToScheme_naturality g hg) hm_le hq_le _).trans
    (map_comp p.relativeSpecFunctionsToScheme g hp_le hg_le).symm

variable {X V W : Scheme.{u}} {I : X.IdealSheafData}
  {I_V : V.IdealSheafData} {I_W : W.IdealSheafData}

/-- **Uniqueness in formal algebraization for finite locally free morphisms.** Let `p : V ⟶ X` and
`q : W ⟶ X` be finite, flat, locally finitely presented morphisms of schemes, and assume that
`finiteLocallyFreeCompletionFunctor X I` is faithful. Then two morphisms `g₁, g₂ : V ⟶ W` over `X`
are equal as soon as they induce the same morphism on formal completions along the preimages of
`I`. -/
theorem hom_ext_of_isFinite_of_flat
    [(finiteLocallyFreeCompletionFunctor X I).Faithful]
    (p : V ⟶ X) (q : W ⟶ X)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
    [IsFinite q] [Flat q] [LocallyOfFinitePresentation q]
    (hp : I.comap p = I_V) (hq : I.comap q = I_W)
    {g₁ g₂ : V ⟶ W} (hg₁ : g₁ ≫ q = p) (hg₂ : g₂ ≫ q = p)
    {h₁ : I_W.comap g₁ ≤ I_V} {h₂ : I_W.comap g₂ ≤ I_V}
    (h : map g₁ h₁ = map g₂ h₂) :
    g₁ = g₂ := by
  subst hp hq
  let m₁ := Scheme.Hom.pushforwardStructureAlgebraMap g₁ hg₁
  let m₂ := Scheme.Hom.pushforwardStructureAlgebraMap g₂ hg₂
  have hq_eq : (I.comap q).comap q.relativeSpecFunctionsToScheme =
      I.comap q.pushforwardStructureAlgebra.relativeSpecToBase := by
    rw [← IdealSheafData.comap_comp, q.relativeSpecFunctionsToScheme_comp]
  have : IsIso (map q.relativeSpecFunctionsToScheme hq_eq.le) := by
    have hq_iso : IsIso (mapIso (asIso q.relativeSpecFunctionsToScheme) hq_eq).hom :=
      inferInstance
    rwa [mapIso_hom] at hq_iso
  have hp_le : (I.comap p).comap p.relativeSpecFunctionsToScheme ≤
      I.comap p.pushforwardStructureAlgebra.relativeSpecToBase := by
    rw [← IdealSheafData.comap_comp, p.relativeSpecFunctionsToScheme_comp]
  have hmap :
      map (I := I.comap p.pushforwardStructureAlgebra.relativeSpecToBase)
        (J := I.comap q.pushforwardStructureAlgebra.relativeSpecToBase)
        (CommMon.relativeSpecMap m₁)
        (by rw [← IdealSheafData.comap_comp, CommMon.relativeSpecMap_relativeSpecToBase]) =
      map (CommMon.relativeSpecMap m₂)
        (by rw [← IdealSheafData.comap_comp, CommMon.relativeSpecMap_relativeSpecToBase]) := by
    apply (cancel_mono (map q.relativeSpecFunctionsToScheme hq_eq.le)).mp
    rw [map_relativeSpecFunctionsToScheme_naturality g₁ hg₁ _ _ hp_le h₁,
      map_relativeSpecFunctionsToScheme_naturality g₂ hg₂ _ _ hp_le h₂, h]
  have hf : (ObjectProperty.homMk m₁ :
      (⟨q.pushforwardStructureAlgebra, inferInstance⟩ : QuasicoherentAlgebra X) ⟶
        ⟨p.pushforwardStructureAlgebra, inferInstance⟩) =
      ObjectProperty.homMk m₂ :=
    hom_ext_relativeSpec_of_isFiniteLocallyFree I
      (by rw [q.pushforwardStructureAlgebra_X]
          exact Modules.isFiniteLocallyFree_pushforward_unit q)
      (by rw [p.pushforwardStructureAlgebra_X]
          exact Modules.isFiniteLocallyFree_pushforward_unit p)
      _ _ hmap
  have hspec : CommMon.relativeSpecMap m₁ = CommMon.relativeSpecMap m₂ :=
    congrArg (fun k ↦ CommMon.relativeSpecMap k.hom) hf
  rw [← cancel_epi p.relativeSpecFunctionsToScheme,
    ← Scheme.Hom.relativeSpecFunctionsToScheme_naturality g₁ hg₁,
    ← Scheme.Hom.relativeSpecFunctionsToScheme_naturality g₂ hg₂, hspec]

/-- **Existence in formal algebraization for finite locally free morphisms.** Let `p : V ⟶ X` and
`q : W ⟶ X` be finite, flat, locally finitely presented morphisms of schemes, and assume that
`finiteLocallyFreeCompletionFunctor X I` is full and faithful. Then every morphism
`a : V.formalCompletion I_V ⟶ W.formalCompletion I_W` over `X.formalCompletion I` is induced by a
morphism `g : V ⟶ W` over `X`. -/
theorem exists_hom_of_isFinite_of_flat
    [(finiteLocallyFreeCompletionFunctor X I).Full]
    [(finiteLocallyFreeCompletionFunctor X I).Faithful]
    (p : V ⟶ X) (q : W ⟶ X)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
    [IsFinite q] [Flat q] [LocallyOfFinitePresentation q]
    (hp : I.comap p = I_V) (hq : I.comap q = I_W)
    (a : V.formalCompletion I_V ⟶ W.formalCompletion I_W)
    (ha : a ≫ map q hq.le = map p hp.le) :
    ∃ (g : V ⟶ W) (hg : g ≫ q = p),
      map g (by rw [← hq, ← IdealSheafData.comap_comp, hg, hp]) = a := by
  subst hp hq
  refine exists_hom_of_isIso_over
    p.relativeSpecFunctionsToScheme p.relativeSpecFunctionsToScheme_comp
    q.relativeSpecFunctionsToScheme q.relativeSpecFunctionsToScheme_comp a ha fun a' ha' ↦ ?_
  obtain ⟨f, hf⟩ := exists_hom_relativeSpec_of_isFiniteLocallyFree I
    (B := ⟨q.pushforwardStructureAlgebra, inferInstance⟩)
    (A := ⟨p.pushforwardStructureAlgebra, inferInstance⟩)
    (by rw [q.pushforwardStructureAlgebra_X]; exact Modules.isFiniteLocallyFree_pushforward_unit q)
    (by rw [p.pushforwardStructureAlgebra_X]; exact Modules.isFiniteLocallyFree_pushforward_unit p)
    a' ha'
  exact ⟨CommMon.relativeSpecMap f.hom, CommMon.relativeSpecMap_relativeSpecToBase f.hom, hf⟩

end FiniteFlat

end AlgebraicGeometry.Scheme.formalCompletion

namespace TauCeti.AlgebraicGeometry

section OverPullback

variable {X X₀ : Scheme.{u}} (I : X.IdealSheafData)

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
  refine Over.pullback_map_injective_of_fac_iso (Scheme.formalCompletion.isoLevelZeroOfKerEq j hj)
    (Scheme.formalCompletion.isoLevelZeroOfKerEq_hom_toScheme j hj) ?_
  intro g₁ g₂ h
  dsimp only at h
  have hg₁ : g₁.left ≫ q = p := by simpa only [Over.mk_hom] using Over.w g₁
  have hg₂ : g₂.left ≫ q = p := by simpa only [Over.mk_hom] using Over.w g₂
  have hg₀ :
      (Scheme.formalCompletion.map (I := I.comap p) (J := I.comap q) g₁.left
          (by rw [← Scheme.IdealSheafData.comap_comp, hg₁])).app 0 =
        (Scheme.formalCompletion.map (I := I.comap p) (J := I.comap q) g₂.left
          (by rw [← Scheme.IdealSheafData.comap_comp, hg₂])).app 0 := by
    apply (cancel_mono (Scheme.formalCompletion.levelIsoPullback q rfl 0).hom).mp
    rw [Scheme.formalCompletion.levelIsoPullback_hom_map rfl rfl g₁ 0,
      Scheme.formalCompletion.levelIsoPullback_hom_map rfl rfl g₂ 0, h]
  have hfu : ∀ n, FormallyUnramified
      ((Scheme.formalCompletion.map (I := I.comap q) q le_rfl).app n) := fun n ↦
    MorphismProperty.of_isPullback (P := @FormallyUnramified)
      (Scheme.formalCompletion.isPullback_map_app q rfl n) inferInstance
  have hfc :
      Scheme.formalCompletion.map (I := I.comap p) (J := I.comap q) g₁.left
          (by rw [← Scheme.IdealSheafData.comap_comp, hg₁]) =
        Scheme.formalCompletion.map (I := I.comap p) (J := I.comap q) g₂.left
          (by rw [← Scheme.IdealSheafData.comap_comp, hg₂]) :=
    AdicThickeningSystem.hom_ext_of_formallyUnramified
      (Scheme.formalCompletion.map (I := I.comap q) q le_rfl)
      ((Scheme.formalCompletion.map_comp_eq (I := I.comap p) (J := I.comap q) (K := I)
        hg₁ _ le_rfl le_rfl).trans
        (Scheme.formalCompletion.map_comp_eq (I := I.comap p) (J := I.comap q) (K := I)
          hg₂ _ le_rfl le_rfl).symm)
      hg₀
  exact Over.OverMorphism.ext
    (Scheme.formalCompletion.hom_ext_of_isFinite_of_flat (I := I) p q rfl rfl hg₁ hg₂ hfc)

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
  refine Over.pullback_map_surjective_of_fac_iso (Scheme.formalCompletion.isoLevelZeroOfKerEq j hj)
    (Scheme.formalCompletion.isoLevelZeroOfKerEq_hom_toScheme j hj) ?_
  intro g₀
  let p_fc := Scheme.formalCompletion.map (I := I.comap p) p le_rfl
  let q_fc := Scheme.formalCompletion.map (I := I.comap q) q le_rfl
  let a₀ : (Y.formalCompletion (I.comap p)).X 0 ⟶ (Z.formalCompletion (I.comap q)).X 0 :=
    (Scheme.formalCompletion.levelIsoPullback p rfl 0).hom ≫ g₀.left ≫
      (Scheme.formalCompletion.levelIsoPullback q rfl 0).inv
  have ha₀ : a₀ ≫ q_fc.app 0 = p_fc.app 0 := by
    have hw : g₀.left ≫ Limits.pullback.snd q (Scheme.formalCompletion.toScheme X I 0) =
        Limits.pullback.snd p (Scheme.formalCompletion.toScheme X I 0) := by
      simpa only [Over.pullback_obj_hom, Over.mk_hom] using Over.w g₀
    simp only [a₀, p_fc, q_fc, Category.assoc, Scheme.formalCompletion.levelIsoPullback_inv_snd]
    rw [hw, Scheme.formalCompletion.levelIsoPullback_hom_snd]
  let a := AdicThickeningSystem.liftOfEtale p_fc q_fc a₀ ha₀
  obtain ⟨g, hg, hga⟩ := Scheme.formalCompletion.exists_hom_of_isFinite_of_flat (I := I) p q rfl rfl
    a (AdicThickeningSystem.liftOfEtale_comp _ _ a₀ ha₀)
  refine ⟨Over.homMk g hg, Over.OverMorphism.ext ?_⟩
  rw [← cancel_epi (Scheme.formalCompletion.levelIsoPullback p rfl 0).hom,
    ← Scheme.formalCompletion.levelIsoPullback_hom_map rfl rfl (Over.homMk g hg) 0,
    ← cancel_mono (Scheme.formalCompletion.levelIsoPullback q rfl 0).inv,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (congrArg (·.app 0) hga).trans (AdicThickeningSystem.liftOfEtale_app_zero _ _ a₀ ha₀)

end OverPullback

end TauCeti.AlgebraicGeometry
