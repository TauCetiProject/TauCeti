/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Algebra
public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Etale
public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
public import TauCeti.AlgebraicGeometry.RelativeSpec.BaseChange
public import TauCeti.AlgebraicGeometry.RelativeSpec.Equivalence

/-!
# Full faithfulness of restriction of finite étale covers from coherent formal completion

Let `X` be a scheme and `i : Z ⟶ X` a closed immersion with ideal sheaf `I = i.ker`. When the
completion functor `Scheme.formalCompletion.completionFunctor X I`, sending a finitely presented
`𝒪_X`-module `M` to the inverse system `(M / I ^ (n + 1) M)_n` on `X.formalCompletion I`, is
faithful (respectively fully faithful), base change of finite étale covers along `i`
(`FiniteEtaleScheme.pullback i : FiniteEtaleScheme X ⥤ FiniteEtaleScheme Z`) is faithful
(respectively fully faithful). This formalizes Lemma 58.17.1 (Tag 0EL8) of the Stacks Project,
with faithfulness also separated out under the weaker hypothesis that `completionFunctor X I` is
faithful, and without any Noetherian hypothesis on `X`.

The proof combines the geometric lifting of étale morphisms across thickenings with the algebraic
descent of finitely presented quasicoherent algebras:

1. Every finite étale `X`-scheme `Y` is affine and locally of finite presentation over `X`, so its
   coordinate algebra `A = p_* 𝒪_Y` is a quasicoherent `𝒪_X`-algebra whose underlying `𝒪_X`-module
   is finitely presented (Stacks Tag 0564,
   `isFinitePresentation_pushforward_of_isFinite_of_locallyOfFinitePresentation`), and
   `Y ≅ Spec_X A` over `X` (`relativeSpecEquiv`).
2. Pulling `A` back along the closed immersions `toScheme X I n : V(I ^ (n + 1)) ⟶ X` yields an
   adic thickening system `formalSpecTower X I A` of relative spectra over `X.formalCompletion I`
   whose structure maps `formalSpecToBase X I A` are levelwise étale and adic.
3. By `AdicThickeningSystem.existsUnique_hom_of_etale`, morphisms over `V(I ^ 1)` between the
   initial levels of two such towers extend uniquely to morphisms of adic thickening systems over
   `X.formalCompletion I`. Under the levelwise relative-Spec anti-equivalence (`relativeSpecEquiv`),
   such system morphisms correspond bijectively to compatible families of algebra morphisms
   `toScheme n ^* A₂ ⟶ toScheme n ^* A₁` across all levels `n`.
4. Faithfulness (respectively full faithfulness) of `completionFunctor X I` then identifies these
   compatible families with algebra morphisms `A₂ ⟶ A₁` over `X`
   (`algebra_hom_ext_of_faithful_completionFunctor` and
   `existsUnique_algebra_hom_of_completionFunctor`), hence with morphisms `Y₁ ⟶ Y₂` in
   `FiniteEtaleScheme X`. Finally, any closed immersion `i : Z ⟶ X` factors as an isomorphism
   `Z ≅ V(i.ker) ≅ V(i.ker ^ 1)` followed by `toScheme X i.ker 0`.

## Main results

* `TauCeti.FiniteEtaleScheme.isEquivalence_pullback_of_isIso`: base change of finite étale schemes
   along an isomorphism of schemes is an equivalence of categories.
* `TauCeti.FiniteEtaleScheme.faithful_pullback_subschemeι`,
  `TauCeti.FiniteEtaleScheme.full_pullback_subschemeι`, and
  `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackSubschemeι`: faithfulness and full faithfulness of
  `FiniteEtaleScheme.pullback I.subschemeι` from `completionFunctor X I` (Stacks Tag 0EL8).
* `TauCeti.FiniteEtaleScheme.faithful_pullback_of_isClosedImmersion`,
  `TauCeti.FiniteEtaleScheme.full_pullback_of_isClosedImmersion`, and
  `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackOfIsClosedImmersion`: the same for an arbitrary
  closed immersion `i : Z ⟶ X` in terms of `completionFunctor X i.ker` (Stacks Tag 0EL8).

## References

* [The Stacks Project, Lemma 58.17.1 (Tag 0EL8)](https://stacks.math.columbia.edu/tag/0EL8).
-/

public section

open CategoryTheory Limits MonoidalCategory Opposite AlgebraicGeometry
open TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

section IsoBaseChange

/-- Base change of finite étale schemes along an isomorphism of schemes is an equivalence of
categories. -/
instance isEquivalence_pullback_of_isIso {S T : Scheme.{u}} (f : T ⟶ S) [IsIso f] :
    (pullback f).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (pullback f) (pullback (inv f))
    (pullbackId.symm ≪≫ eqToIso (congrArg pullback (IsIso.inv_hom_id f).symm) ≪≫
      pullbackComp (inv f) f)
    ((pullbackComp f (inv f)).symm ≪≫ eqToIso (congrArg pullback (IsIso.hom_inv_id f)) ≪≫
      pullbackId)).isEquivalence_functor

/-- Precomposing a base-change morphism with an isomorphism preserves faithfulness of
`FiniteEtaleScheme.pullback`. -/
theorem faithful_pullback_comp_of_isIso {S Z Z' : Scheme.{u}} (g : Z' ⟶ Z) (f : Z ⟶ S) [IsIso g]
    [(pullback f).Faithful] : (pullback (g ≫ f)).Faithful :=
  Functor.Faithful.of_iso (pullbackComp g f).symm

/-- Precomposing a base-change morphism with an isomorphism preserves fullness of
`FiniteEtaleScheme.pullback`. -/
theorem full_pullback_comp_of_isIso {S Z Z' : Scheme.{u}} (g : Z' ⟶ Z) (f : Z ⟶ S) [IsIso g]
    [(pullback f).Full] : (pullback (g ≫ f)).Full :=
  Functor.Full.of_iso (pullbackComp g f).symm

end IsoBaseChange

/-! ### Relative spectra of finite étale algebras and their formal towers -/

section FormalSpecTower

open Scheme.formalCompletion

variable {S : Scheme.{u}}

/-- The relative spectrum of a quasicoherent `𝒪_S`-algebra with finite étale structure morphism,
bundled as an object of `FiniteEtaleScheme S` with exposed underlying `Over S` object. -/
private noncomputable abbrev specObj (A : QuasicoherentAlgebra S)
    [IsFinite A.obj.relativeSpecToBase] [Etale A.obj.relativeSpecToBase] :
    FiniteEtaleScheme S :=
  ⟨Over.mk A.obj.relativeSpecToBase, (finiteEtaleSchemeProperty_iff _).mpr ⟨‹_›, ‹_›⟩⟩

/-- An algebra morphism `b : A₂ ⟶ A₁` induces a morphism `Spec_S A₁ ⟶ Spec_S A₂` of finite étale
`S`-schemes when both relative spectra are finite étale over `S`. -/
private noncomputable def homOfAlgebraHom {A₁ A₂ : QuasicoherentAlgebra S}
    [IsFinite A₁.obj.relativeSpecToBase] [Etale A₁.obj.relativeSpecToBase]
    [IsFinite A₂.obj.relativeSpecToBase] [Etale A₂.obj.relativeSpecToBase] (b : A₂ ⟶ A₁) :
    specObj A₁ ⟶ specObj A₂ :=
  ObjectProperty.homMk (Over.homMk (CommMon.relativeSpecMap b.hom)
    (CommMon.relativeSpecMap_relativeSpecToBase b.hom))

/-- Morphisms `specObj A₁ ⟶ specObj A₂` in `FiniteEtaleScheme S` correspond bijectively to algebra
morphisms `A₂ ⟶ A₁` via `relativeSpec S`. -/
private noncomputable def homEquivAlgebraHom (A₁ A₂ : QuasicoherentAlgebra S)
    [IsFinite A₁.obj.relativeSpecToBase] [Etale A₁.obj.relativeSpecToBase]
    [IsFinite A₂.obj.relativeSpecToBase] [Etale A₂.obj.relativeSpecToBase] :
    (A₂ ⟶ A₁) ≃ (specObj A₁ ⟶ specObj A₂) where
  toFun := homOfAlgebraHom
  invFun g :=
    ((relativeSpec S).preimage
      (MorphismProperty.Over.homMk g.hom.left (Over.w g.hom) :
        (relativeSpec S).obj (op A₁) ⟶ (relativeSpec S).obj (op A₂))).unop
  left_inv b := by
    apply Quiver.Hom.op_inj
    exact (relativeSpec S).preimage_map b.op
  right_inv g := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact congrArg (fun k ↦ k.left) ((relativeSpec S).map_preimage
      (MorphismProperty.Over.homMk g.hom.left (Over.w g.hom) :
        (relativeSpec S).obj (op A₁) ⟶ (relativeSpec S).obj (op A₂)))

@[simp]
private theorem homEquivAlgebraHom_apply_left {A₁ A₂ : QuasicoherentAlgebra S}
    [IsFinite A₁.obj.relativeSpecToBase] [Etale A₁.obj.relativeSpecToBase]
    [IsFinite A₂.obj.relativeSpecToBase] [Etale A₂.obj.relativeSpecToBase] (b : A₂ ⟶ A₁) :
    ((homEquivAlgebraHom A₁ A₂ b).hom).left = CommMon.relativeSpecMap b.hom :=
  (rfl)

/-- Every finite étale `S`-scheme `Y` is isomorphic in `FiniteEtaleScheme S` to the relative
spectrum of a quasicoherent `𝒪_S`-algebra whose underlying `𝒪_S`-module is finitely presented. -/
private theorem exists_finitelyPresented_algebra_iso (Y : FiniteEtaleScheme S) :
    ∃ (A : QuasicoherentAlgebra S) (_ : A.obj.X.IsFinitePresentation)
      (_ : IsFinite A.obj.relativeSpecToBase) (_ : Etale A.obj.relativeSpecToBase),
      Nonempty (specObj A ≅ Y) := by
  let V : AffineSchemeOver S := MorphismProperty.Over.mk ⊤ Y.obj.hom inferInstance
  let A : QuasicoherentAlgebra S := ((affineFunctions S).obj V).unop
  have hA_fp : A.obj.X.IsFinitePresentation :=
    inferInstanceAs ((Scheme.Modules.pushforward Y.obj.hom).obj
      (𝟙_ Y.obj.left.Modules)).IsFinitePresentation
  have hcomp : Y.obj.hom.relativeSpecFunctionsToScheme ≫ Y.obj.hom = A.obj.relativeSpecToBase :=
    Y.obj.hom.relativeSpecFunctionsToScheme_comp
  have hA_fin : IsFinite A.obj.relativeSpecToBase := by
    rw [← hcomp]
    exact MorphismProperty.comp_mem _ Y.obj.hom.relativeSpecFunctionsToScheme Y.obj.hom
      inferInstance inferInstance
  have hA_et : Etale A.obj.relativeSpecToBase := by
    rw [← hcomp]
    exact MorphismProperty.comp_mem _ Y.obj.hom.relativeSpecFunctionsToScheme Y.obj.hom
      inferInstance inferInstance
  exact ⟨A, hA_fp, hA_fin, hA_et, ⟨ObjectProperty.isoMk _
    (Over.isoMk Y.obj.hom.relativeSpecFunctionsIso
      (by rw [Scheme.Hom.relativeSpecFunctionsIso_hom]; exact hcomp))⟩⟩

private instance isFinite_pullback_relativeSpecToBase {T : Scheme.{u}} (f : T ⟶ S)
    (A : QuasicoherentAlgebra S) [IsFinite A.obj.relativeSpecToBase] :
    IsFinite ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpecToBase := by
  rw [← (isPullback_relativeSpecPullbackFst A f).isoPullback_hom_snd]
  infer_instance

private instance etale_pullback_relativeSpecToBase {T : Scheme.{u}} (f : T ⟶ S)
    (A : QuasicoherentAlgebra S) [Etale A.obj.relativeSpecToBase] :
    Etale ((QuasicoherentAlgebra.pullback f).obj A).obj.relativeSpecToBase := by
  rw [← (isPullback_relativeSpecPullbackFst A f).isoPullback_hom_snd]
  infer_instance

/-- Base change of `specObj A` along `f : T ⟶ S` is canonically isomorphic in
`FiniteEtaleScheme T` to `specObj ((f^* A))`, compatibly with algebra morphisms. -/
private noncomputable def specObjPullbackAlgebraIso {T : Scheme.{u}} (f : T ⟶ S)
    (A : QuasicoherentAlgebra S) [IsFinite A.obj.relativeSpecToBase]
    [Etale A.obj.relativeSpecToBase] :
    specObj ((QuasicoherentAlgebra.pullback f).obj A) ≅ (pullback f).obj (specObj A) :=
  ObjectProperty.isoMk _
    (Over.isoMk (isPullback_relativeSpecPullbackFst A f).isoPullback
      (IsPullback.isoPullback_hom_snd _))

private theorem specObjPullbackAlgebraIso_naturality {T : Scheme.{u}} (f : T ⟶ S)
    {A₁ A₂ : QuasicoherentAlgebra S}
    [IsFinite A₁.obj.relativeSpecToBase] [Etale A₁.obj.relativeSpecToBase]
    [IsFinite A₂.obj.relativeSpecToBase] [Etale A₂.obj.relativeSpecToBase] (b : A₂ ⟶ A₁) :
    (specObjPullbackAlgebraIso f A₁).hom ≫ (pullback f).map (homEquivAlgebraHom A₁ A₂ b) =
      homEquivAlgebraHom _ _ ((QuasicoherentAlgebra.pullback f).map b) ≫
        (specObjPullbackAlgebraIso f A₂).hom := by
  let p₁ := isPullback_relativeSpecPullbackFst A₁ f
  let p₂ := isPullback_relativeSpecPullbackFst A₂ f
  let m := CommMon.relativeSpecMap ((QuasicoherentAlgebra.pullback f).map b).hom
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · exact (Category.assoc p₁.isoPullback.hom _ _).trans
      ((congrArg (p₁.isoPullback.hom ≫ ·) (Limits.pullback.lift_fst _ _ _)).trans
        ((p₁.isoPullback_hom_fst_assoc _).trans
          ((relativeSpecMap_pullback_map_relativeSpecPullbackFst A₁ f b).symm.trans
            ((congrArg (m ≫ ·) p₂.isoPullback_hom_fst.symm).trans
              (Category.assoc m p₂.isoPullback.hom _).symm))))
  · exact (Category.assoc p₁.isoPullback.hom _ _).trans
      ((congrArg (p₁.isoPullback.hom ≫ ·) (Limits.pullback.lift_snd _ _ _)).trans
        (p₁.isoPullback_hom_snd.trans
          ((CommMon.relativeSpecMap_relativeSpecToBase
              ((QuasicoherentAlgebra.pullback f).map b).hom).symm.trans
            ((congrArg (m ≫ ·) p₂.isoPullback_hom_snd.symm).trans
              (Category.assoc m p₂.isoPullback.hom _).symm))))

variable (X : Scheme.{u}) (I : X.IdealSheafData) (A : QuasicoherentAlgebra X)

/-- The step transition morphism between the relative spectra of `toScheme n ^* A` and
`toScheme (n + 1) ^* A` over the formal completion `X.formalCompletion I`. -/
private noncomputable def formalSpecTowerι (n : ℕ) :
    ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A).obj.relativeSpec ⟶
      ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj A).obj.relativeSpec :=
  CommMon.relativeSpecMap ((algebraTransitionIso X I A n).hom).hom ≫
    relativeSpecPullbackFst ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj A)
      ((X.formalCompletion I).ι n)

private instance isIso_relativeSpecMap_algebraTransitionIso_hom (n : ℕ) :
    IsIso (CommMon.relativeSpecMap ((algebraTransitionIso X I A n).hom).hom) :=
  ⟨CommMon.relativeSpecMap ((algebraTransitionIso X I A n).inv).hom,
    (CommMon.relativeSpecMap_comp _ _).symm.trans
      ((congrArg CommMon.relativeSpecMap
        (congrArg (fun k ↦ k.hom) (algebraTransitionIso X I A n).inv_hom_id)).trans
        (CommMon.relativeSpecMap_id _)),
    (CommMon.relativeSpecMap_comp _ _).symm.trans
      ((congrArg CommMon.relativeSpecMap
        (congrArg (fun k ↦ k.hom) (algebraTransitionIso X I A n).hom_inv_id)).trans
        (CommMon.relativeSpecMap_id _))⟩

/-- Every step transition of `formalSpecTowerι` forms a cartesian square over the step transition
of `X.formalCompletion I`. -/
private theorem isPullback_formalSpecTowerι (n : ℕ) :
    IsPullback (formalSpecTowerι X I A n)
      ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A).obj.relativeSpecToBase
      ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj A).obj.relativeSpecToBase
      ((X.formalCompletion I).ι n) := by
  have hleft : IsPullback
      (CommMon.relativeSpecMap ((algebraTransitionIso X I A n).hom).hom)
      ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A).obj.relativeSpecToBase
      ((QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).obj
        ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj A)).obj.relativeSpecToBase
      (𝟙 ((X.formalCompletion I).X n)) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  simpa only [formalSpecTowerι, Category.id_comp] using hleft.paste_horiz
    (isPullback_relativeSpecPullbackFst
      ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj A)
      ((X.formalCompletion I).ι n))

/-- Pasting `isPullback_formalSpecTowerι` across the first `m` steps shows that the level map of
`formalSpecTower` is the base change of `(X.formalCompletion I).levelMap m`. -/
private theorem isPullback_levelMap_formalSpecTowerι (m : ℕ) :
    IsPullback
      (TauCeti.AlgebraicGeometry.levelMap
        (fun n ↦ ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A).obj.relativeSpec)
        (formalSpecTowerι X I A) m)
      ((QuasicoherentAlgebra.pullback (toScheme X I 0)).obj A).obj.relativeSpecToBase
      ((QuasicoherentAlgebra.pullback (toScheme X I m)).obj A).obj.relativeSpecToBase
      ((X.formalCompletion I).levelMap m) := by
  induction m with
  | zero =>
    rw [TauCeti.AlgebraicGeometry.levelMap_zero, AdicThickeningSystem.levelMap_zero]
    exact IsPullback.of_horiz_isIso (fst := 𝟙 _) (g := 𝟙 _) ⟨by simp⟩
  | succ m ih =>
    rw [TauCeti.AlgebraicGeometry.levelMap_succ, AdicThickeningSystem.levelMap_succ]
    exact ih.paste_horiz (isPullback_formalSpecTowerι X I A m)

/-- The adic thickening system of relative spectra `(Spec_{V(I ^ (n + 1))} (toScheme n ^* A))_n`
over the formal completion `X.formalCompletion I`. -/
private noncomputable def formalSpecTower : AdicThickeningSystem.{u} where
  X n := ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A).obj.relativeSpec
  ι n := formalSpecTowerι X I A n
  isThickening n := by
    rw [← (isPullback_formalSpecTowerι X I A n).isoPullback_hom_fst]
    infer_instance
  adic n := by
    have hι := Scheme.IdealSheafData.ker_eq_comap_of_isPullback ((X.formalCompletion I).ι n)
      (isPullback_formalSpecTowerι X I A n)
    have hlev := Scheme.IdealSheafData.ker_eq_comap_of_isPullback
      ((X.formalCompletion I).levelMap (n + 1))
      (isPullback_levelMap_formalSpecTowerι X I A (n + 1))
    rw [hι, hlev, (X.formalCompletion I).ker_ι n, Scheme.IdealSheafData.comap_pow]

/-- The canonical adic morphism `formalSpecTower X I A ⟶ X.formalCompletion I` given levelwise by
the relative-spectrum structure morphisms. -/
private noncomputable def formalSpecToBase : formalSpecTower X I A ⟶ X.formalCompletion I where
  app n := ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A).obj.relativeSpecToBase
  naturality n := (isPullback_formalSpecTowerι X I A n).w

private instance etale_formalSpecToBase_app [Etale A.obj.relativeSpecToBase] (n : ℕ) :
    Etale ((formalSpecToBase X I A).app n) :=
  inferInstanceAs
    (Etale ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A).obj.relativeSpecToBase)

/-- A levelwise family of algebra morphisms `φ n : toScheme n ^* A₂ ⟶ toScheme n ^* A₁` induces
natural relative-spectrum maps on `formalSpecTower` if and only if `φ` commutes with the reduction
isomorphisms `algebraTransitionIso`. -/
private theorem relativeSpecMap_comm_formalSpecTowerι_iff {A₁ A₂ : QuasicoherentAlgebra X}
    (φ : ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A₂ ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A₁) (n : ℕ) :
    formalSpecTowerι X I A₁ n ≫ CommMon.relativeSpecMap (φ (n + 1)).hom =
      CommMon.relativeSpecMap (φ n).hom ≫ formalSpecTowerι X I A₂ n ↔
      (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (φ (n + 1)) ≫
        (algebraTransitionIso X I A₁ n).hom =
        (algebraTransitionIso X I A₂ n).hom ≫ φ n := by
  let ιₙ := (X.formalCompletion I).ι n
  let A₁' := (QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj A₁
  let A₂' := (QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj A₂
  have hL : formalSpecTowerι X I A₁ n ≫ CommMon.relativeSpecMap (φ (n + 1)).hom =
      CommMon.relativeSpecMap
          (((QuasicoherentAlgebra.pullback ιₙ).map (φ (n + 1)) ≫
            (algebraTransitionIso X I A₁ n).hom).hom) ≫
        relativeSpecPullbackFst A₂' ιₙ :=
    (Category.assoc _ _ _).trans
      ((congrArg (CommMon.relativeSpecMap (algebraTransitionIso X I A₁ n).hom.hom ≫ ·)
          (relativeSpecMap_pullback_map_relativeSpecPullbackFst A₁' ιₙ (φ (n + 1))).symm).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ relativeSpecPullbackFst A₂' ιₙ)
            (CommMon.relativeSpecMap_comp ((QuasicoherentAlgebra.pullback ιₙ).map (φ (n + 1))).hom
              (algebraTransitionIso X I A₁ n).hom.hom).symm)))
  have hR : CommMon.relativeSpecMap (φ n).hom ≫ formalSpecTowerι X I A₂ n =
      CommMon.relativeSpecMap (((algebraTransitionIso X I A₂ n).hom ≫ φ n).hom) ≫
        relativeSpecPullbackFst A₂' ιₙ :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ relativeSpecPullbackFst A₂' ιₙ)
        (CommMon.relativeSpecMap_comp (algebraTransitionIso X I A₂ n).hom.hom (φ n).hom).symm)
  rw [hL, hR]
  refine ⟨fun h ↦ ?_, fun h ↦ congrArg (fun k ↦ CommMon.relativeSpecMap k.hom ≫ _) h⟩
  have hmap : CommMon.relativeSpecMap
      (((QuasicoherentAlgebra.pullback ιₙ).map (φ (n + 1)) ≫
        (algebraTransitionIso X I A₁ n).hom).hom) =
      CommMon.relativeSpecMap (((algebraTransitionIso X I A₂ n).hom ≫ φ n).hom) :=
    (isPullback_relativeSpecPullbackFst A₂' ιₙ).hom_ext h
      ((CommMon.relativeSpecMap_relativeSpecToBase _).trans
        (CommMon.relativeSpecMap_relativeSpecToBase _).symm)
  apply Quiver.Hom.op_inj
  apply (relativeSpec ((X.formalCompletion I).X n)).map_injective
  apply MorphismProperty.Over.Hom.ext
  exact hmap

/-- Faithfulness of `FiniteEtaleScheme.pullback (toScheme X I 0)` on two relative spectra of
finitely presented algebras, assuming `completionFunctor X I` is faithful. -/
private theorem hom_ext_specObj_of_pullback_toScheme_zero [(completionFunctor X I).Faithful]
    {A₁ A₂ : QuasicoherentAlgebra X}
    [A₁.obj.X.IsFinitePresentation] [IsFinite A₁.obj.relativeSpecToBase]
    [Etale A₁.obj.relativeSpecToBase]
    [A₂.obj.X.IsFinitePresentation] [IsFinite A₂.obj.relativeSpecToBase]
    [Etale A₂.obj.relativeSpecToBase]
    {f g : specObj A₁ ⟶ specObj A₂}
    (h : (pullback (toScheme X I 0)).map f = (pullback (toScheme X I 0)).map g) :
    f = g := by
  obtain ⟨b₁, rfl⟩ := (homEquivAlgebraHom A₁ A₂).surjective f
  obtain ⟨b₂, rfl⟩ := (homEquivAlgebraHom A₁ A₂).surjective g
  congr 1
  let u₁ : formalSpecTower X I A₁ ⟶ formalSpecTower X I A₂ :=
    { app n := CommMon.relativeSpecMap ((QuasicoherentAlgebra.pullback (toScheme X I n)).map b₁).hom
      naturality n :=
        (relativeSpecMap_comm_formalSpecTowerι_iff X I
          (fun k ↦ (QuasicoherentAlgebra.pullback (toScheme X I k)).map b₁) n).mpr
          (pullback_map_algebraTransitionIso_hom X I b₁ n) }
  let u₂ : formalSpecTower X I A₁ ⟶ formalSpecTower X I A₂ :=
    { app n := CommMon.relativeSpecMap ((QuasicoherentAlgebra.pullback (toScheme X I n)).map b₂).hom
      naturality n :=
        (relativeSpecMap_comm_formalSpecTowerι_iff X I
          (fun k ↦ (QuasicoherentAlgebra.pullback (toScheme X I k)).map b₂) n).mpr
          (pullback_map_algebraTransitionIso_hom X I b₂ n) }
  have hu0 : u₁.app 0 = u₂.app 0 := by
    have h0 : homEquivAlgebraHom _ _ ((QuasicoherentAlgebra.pullback (toScheme X I 0)).map b₁) =
        homEquivAlgebraHom _ _ ((QuasicoherentAlgebra.pullback (toScheme X I 0)).map b₂) := by
      rw [← cancel_mono (specObjPullbackAlgebraIso (toScheme X I 0) A₂).hom,
        ← specObjPullbackAlgebraIso_naturality, ← specObjPullbackAlgebraIso_naturality, h]
    exact congrArg (fun k ↦ k.hom.left) h0
  have hu : u₁ = u₂ := AdicThickeningSystem.hom_ext_of_formallyUnramified (formalSpecToBase X I A₂)
    (AdicThickeningSystem.Hom.ext (funext fun n ↦
      (CommMon.relativeSpecMap_relativeSpecToBase _).trans
        (CommMon.relativeSpecMap_relativeSpecToBase _).symm)) hu0
  refine algebra_hom_ext_of_faithful_completionFunctor X I fun n ↦ ?_
  apply Quiver.Hom.op_inj
  apply (relativeSpec ((X.formalCompletion I).X n)).map_injective
  apply MorphismProperty.Over.Hom.ext
  exact congrArg (·.app n) hu

/-- Fullness of `FiniteEtaleScheme.pullback (toScheme X I 0)` between two relative spectra of
finitely presented algebras, assuming `completionFunctor X I` is full and faithful. -/
private theorem exists_hom_specObj_of_pullback_toScheme_zero
    [(completionFunctor X I).Full] [(completionFunctor X I).Faithful]
    (A₁ A₂ : QuasicoherentAlgebra X)
    [A₁.obj.X.IsFinitePresentation] [IsFinite A₁.obj.relativeSpecToBase]
    [Etale A₁.obj.relativeSpecToBase]
    [A₂.obj.X.IsFinitePresentation] [IsFinite A₂.obj.relativeSpecToBase]
    [Etale A₂.obj.relativeSpecToBase]
    (g₀ : (pullback (toScheme X I 0)).obj (specObj A₁) ⟶
      (pullback (toScheme X I 0)).obj (specObj A₂)) :
    ∃ f : specObj A₁ ⟶ specObj A₂,
      (pullback (toScheme X I 0)).map f = g₀ := by
  let g₀' : specObj ((QuasicoherentAlgebra.pullback (toScheme X I 0)).obj A₁) ⟶
      specObj ((QuasicoherentAlgebra.pullback (toScheme X I 0)).obj A₂) :=
    (specObjPullbackAlgebraIso (toScheme X I 0) A₁).hom ≫ g₀ ≫
      (specObjPullbackAlgebraIso (toScheme X I 0) A₂).inv
  let u : formalSpecTower X I A₁ ⟶ formalSpecTower X I A₂ :=
    AdicThickeningSystem.liftOfEtale (formalSpecToBase X I A₁) (formalSpecToBase X I A₂)
      g₀'.hom.left (Over.w g₀'.hom)
  let φ : ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A₂ ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A₁ := fun n ↦
    (homEquivAlgebraHom _ _).symm
      (ObjectProperty.homMk (Over.homMk (u.app n)
        (AdicThickeningSystem.liftOfEtale_app_comp _ _ _ _ n)))
  have hu_app (n : ℕ) : CommMon.relativeSpecMap (φ n).hom = u.app n :=
    congrArg (fun k ↦ k.hom.left) ((homEquivAlgebraHom _ _).apply_symm_apply
      (ObjectProperty.homMk (Over.homMk (u.app n)
        (AdicThickeningSystem.liftOfEtale_app_comp _ _ _ _ n))))
  have hφ (n : ℕ) :
      (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (φ (n + 1)) ≫
        (algebraTransitionIso X I A₁ n).hom =
        (algebraTransitionIso X I A₂ n).hom ≫ φ n := by
    refine (relativeSpecMap_comm_formalSpecTowerι_iff X I φ n).mp ?_
    rw [hu_app, hu_app]
    exact u.naturality n
  let b : A₂ ⟶ A₁ := descAlgebraOfCompletionFunctor X I φ hφ
  refine ⟨homEquivAlgebraHom A₁ A₂ b, ?_⟩
  rw [← cancel_epi (specObjPullbackAlgebraIso (toScheme X I 0) A₁).hom,
    specObjPullbackAlgebraIso_naturality,
    pullback_toScheme_map_descAlgebraOfCompletionFunctor]
  have hφ0 : homEquivAlgebraHom _ _ (φ 0) = g₀' :=
    ObjectProperty.hom_ext _ (Over.OverMorphism.ext
      ((homEquivAlgebraHom_apply_left (φ 0)).trans
        ((hu_app 0).trans (AdicThickeningSystem.liftOfEtale_app_zero _ _ _ _))))
  rw [hφ0]
  simp [g₀']

end FormalSpecTower

/-! ### Main theorems for closed immersions (Stacks Tag 0EL8) -/

section MainResults

open Scheme.formalCompletion

/-- If the completion functor on finitely presented `𝒪_X`-modules along `I` is faithful, then
base change of finite étale schemes along the initial formal-completion level `toScheme X I 0` is
faithful. -/
instance faithful_pullback_toScheme_zero (X : Scheme.{u}) (I : X.IdealSheafData)
    [(completionFunctor X I).Faithful] :
    (pullback (toScheme X I 0)).Faithful where
  map_injective {Y₁ Y₂} {f g} h := by
    obtain ⟨A₁, _, _, _, ⟨e₁⟩⟩ := exists_finitelyPresented_algebra_iso Y₁
    obtain ⟨A₂, _, _, _, ⟨e₂⟩⟩ := exists_finitelyPresented_algebra_iso Y₂
    rw [← cancel_epi e₁.hom, ← cancel_mono e₂.inv]
    refine hom_ext_specObj_of_pullback_toScheme_zero X I ?_
    simp only [Functor.map_comp, h]

/-- If the completion functor on finitely presented `𝒪_X`-modules along `I` is full and faithful,
then base change of finite étale schemes along `toScheme X I 0` is full. -/
instance full_pullback_toScheme_zero (X : Scheme.{u}) (I : X.IdealSheafData)
    [(completionFunctor X I).Full] [(completionFunctor X I).Faithful] :
    (pullback (toScheme X I 0)).Full where
  map_surjective {Y₁ Y₂} g₀ := by
    obtain ⟨A₁, _, _, _, ⟨e₁⟩⟩ := exists_finitelyPresented_algebra_iso Y₁
    obtain ⟨A₂, _, _, _, ⟨e₂⟩⟩ := exists_finitelyPresented_algebra_iso Y₂
    obtain ⟨f', hf'⟩ := exists_hom_specObj_of_pullback_toScheme_zero X I A₁ A₂
      ((pullback (toScheme X I 0)).map e₁.hom ≫ g₀ ≫ (pullback (toScheme X I 0)).map e₂.inv)
    refine ⟨e₁.inv ≫ f' ≫ e₂.hom, ?_⟩
    simp only [Functor.map_comp, hf']
    simp [← Functor.map_comp_assoc, ← Functor.map_comp]

/-- **Faithfulness of restriction of finite étale covers to a closed subscheme `V(I)`** when the
formal completion functor on finitely presented `𝒪_X`-modules along `I` is faithful.
Stacks, Lemma 58.17.1 (0EL8), faithfulness half. -/
@[stacks 0EL8]
instance faithful_pullback_subschemeι (X : Scheme.{u}) (I : X.IdealSheafData)
    [(completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Faithful := by
  have hfac : Scheme.IdealSheafData.inclusion (pow_one I).le ≫ toScheme X I 0 = I.subschemeι := by
    rw [toScheme_def, Scheme.IdealSheafData.inclusion_subschemeι]
  let g := Scheme.IdealSheafData.inclusion (pow_one I).le
  have hg : IsIso g :=
    ⟨Scheme.IdealSheafData.inclusion (pow_one I).ge,
      (Scheme.IdealSheafData.inclusion_comp _ _).trans (Scheme.IdealSheafData.inclusion_id _),
      (Scheme.IdealSheafData.inclusion_comp _ _).trans (Scheme.IdealSheafData.inclusion_id _)⟩
  rw [← hfac]
  exact @faithful_pullback_comp_of_isIso _ _ _ g (toScheme X I 0) hg
    (faithful_pullback_toScheme_zero X I)

/-- **Fullness of restriction of finite étale covers to a closed subscheme `V(I)`** when the formal
completion functor on finitely presented `𝒪_X`-modules along `I` is full and faithful.
Stacks, Lemma 58.17.1 (0EL8). -/
@[stacks 0EL8]
instance full_pullback_subschemeι (X : Scheme.{u}) (I : X.IdealSheafData)
    [(completionFunctor X I).Full] [(completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Full := by
  have hfac : Scheme.IdealSheafData.inclusion (pow_one I).le ≫ toScheme X I 0 = I.subschemeι := by
    rw [toScheme_def, Scheme.IdealSheafData.inclusion_subschemeι]
  let g := Scheme.IdealSheafData.inclusion (pow_one I).le
  have hg : IsIso g :=
    ⟨Scheme.IdealSheafData.inclusion (pow_one I).ge,
      (Scheme.IdealSheafData.inclusion_comp _ _).trans (Scheme.IdealSheafData.inclusion_id _),
      (Scheme.IdealSheafData.inclusion_comp _ _).trans (Scheme.IdealSheafData.inclusion_id _)⟩
  rw [← hfac]
  exact @full_pullback_comp_of_isIso _ _ _ g (toScheme X I 0) hg (full_pullback_toScheme_zero X I)

/-- **Full faithfulness of restriction of finite étale covers to `V(I)`** from full faithfulness of
the formal completion functor on finitely presented `𝒪_X`-modules along `I`.
Stacks, Lemma 58.17.1 (0EL8). -/
@[stacks 0EL8]
noncomputable def fullyFaithfulPullbackSubschemeι (X : Scheme.{u}) (I : X.IdealSheafData)
    [(completionFunctor X I).Full] [(completionFunctor X I).Faithful] :
    (pullback I.subschemeι).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful (pullback I.subschemeι)

/-- **Faithfulness of restriction of finite étale covers along a closed immersion `i : Z ⟶ X`**
when the formal completion functor on finitely presented `𝒪_X`-modules along `i.ker` is faithful.
Stacks, Lemma 58.17.1 (0EL8), faithfulness half. -/
@[stacks 0EL8]
instance faithful_pullback_of_isClosedImmersion {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [(completionFunctor X i.ker).Faithful] :
    (pullback i).Faithful := by
  let g : Z ⟶ i.ker.subscheme := IsClosedImmersion.lift i.ker.subschemeι i i.ker.ker_subschemeι.le
  have hg : IsIso g := IsClosedImmersion.isIso_lift i.ker.subschemeι i i.ker.ker_subschemeι
  have hfac : g ≫ i.ker.subschemeι = i :=
    IsClosedImmersion.lift_fac i.ker.subschemeι i i.ker.ker_subschemeι.le
  rw [← hfac]
  exact @faithful_pullback_comp_of_isIso _ _ _ g i.ker.subschemeι hg inferInstance

/-- **Fullness of restriction of finite étale covers along a closed immersion `i : Z ⟶ X`** when
the formal completion functor on finitely presented `𝒪_X`-modules along `i.ker` is full and
faithful. Stacks, Lemma 58.17.1 (0EL8). -/
@[stacks 0EL8]
instance full_pullback_of_isClosedImmersion {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [(completionFunctor X i.ker).Full]
    [(completionFunctor X i.ker).Faithful] :
    (pullback i).Full := by
  let g : Z ⟶ i.ker.subscheme := IsClosedImmersion.lift i.ker.subschemeι i i.ker.ker_subschemeι.le
  have hg : IsIso g := IsClosedImmersion.isIso_lift i.ker.subschemeι i i.ker.ker_subschemeι
  have hfac : g ≫ i.ker.subschemeι = i :=
    IsClosedImmersion.lift_fac i.ker.subschemeι i i.ker.ker_subschemeι.le
  rw [← hfac]
  exact @full_pullback_comp_of_isIso _ _ _ g i.ker.subschemeι hg inferInstance

/-- **Full faithfulness of restriction of finite étale covers along a closed immersion
`i : Z ⟶ X`** when the formal completion functor on finitely presented `𝒪_X`-modules along `i.ker`
is full and faithful. Stacks, Lemma 58.17.1 (0EL8). -/
@[stacks 0EL8]
noncomputable def fullyFaithfulPullbackOfIsClosedImmersion {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [(completionFunctor X i.ker).Full]
    [(completionFunctor X i.ker).Faithful] :
    (pullback i).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful (pullback i)

end MainResults

end TauCeti.FiniteEtaleScheme
