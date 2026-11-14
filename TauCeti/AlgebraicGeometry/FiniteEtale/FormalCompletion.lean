/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule
public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Etale
import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Pullback
import TauCeti.AlgebraicGeometry.RelativeSpec.BaseChange
import TauCeti.AlgebraicGeometry.RelativeSpec.Equivalence
import TauCeti.AlgebraicGeometry.VectorBundle.Pushforward

/-!
# Full faithfulness of finite étale pullback from formal completion

Let `X` be a scheme, `I` an ideal sheaf on `X`, and `i : Z ⟶ X` a closed immersion cut out by `I`
(`i.ker = I`), for instance `I.subschemeι : V(I) ⟶ X` or the initial level
`Scheme.formalCompletion.toScheme X I 0` of the formal completion `X/V(I)`. Suppose that the
completion functor `Scheme.formalCompletion.completionFunctor X I`, restricted to finite locally
free `𝒪_X`-modules, is fully faithful (which holds whenever `completionFunctor X I` itself is
fully faithful on finitely presented `𝒪_X`-modules, and in particular on coherent `𝒪_X`-modules
when `X` is locally Noetherian). Then pulling back finite étale schemes along `i`,
`TauCeti.FiniteEtaleScheme.pullback i : FiniteEtaleScheme X ⥤ FiniteEtaleScheme Z`, is fully
faithful (`TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackOfCompletion`, Stacks, Lemma 58.17.1,
Tag 0EL8). Faithfulness requires only faithfulness of the restricted completion functor
(`TauCeti.FiniteEtaleScheme.faithful_pullback_of_completion`).

Every finite étale scheme `Y ⟶ X` is affine, finite, flat, and locally of finite presentation over
`X`, so `Y` is canonically the relative spectrum of its coordinate algebra `p_* 𝒪_Y`, whose
underlying `𝒪_X`-module is finite locally free
(`AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFree_pushforwardStructureAlgebra`). Base changing two
finite étale schemes `Y₁, Y₂` along the levels `V(I ^ (n + 1)) ⟶ X` of `X.formalCompletion I`
yields levelwise étale adic thickening systems over `X.formalCompletion I`. By infinitesimal
lifting for étale targets (`TauCeti.AlgebraicGeometry.AdicThickeningSystem.liftOfEtale` and
`hom_ext_of_formallyUnramified`), morphisms over `V(I)` correspond bijectively to compatible
families of morphisms over all `V(I ^ (n + 1))`, which by the relative-spectrum anti-equivalence
(`TauCeti.AlgebraicGeometry.relativeSpecEquiv`) correspond to compatible families of `𝒪`-algebra
homomorphisms on the levels. Full faithfulness of formal completion on finite locally free modules
descends both the underlying module homomorphism and its unit and multiplication laws.

## Main declarations

* `TauCeti.FiniteEtaleScheme.faithful_pullback_of_completion`: pullback of finite étale schemes
  along a closed immersion with ideal sheaf `I` is faithful when formal completion along `I` is
  faithful on finite locally free sheaves;
* `TauCeti.FiniteEtaleScheme.full_pullback_of_completion`: pullback of finite étale schemes along a
  closed immersion with ideal sheaf `I` is full when formal completion along `I` is full and
  faithful on finite locally free sheaves;
* `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackOfCompletion`: the bundled `FullyFaithful`
  structure (Stacks, Lemma 58.17.1, Tag 0EL8);
* `TauCeti.FiniteEtaleScheme.faithful_pullback_subschemeι`,
  `TauCeti.FiniteEtaleScheme.full_pullback_subschemeι`,
  `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackSubschemeι`: specializations to
  `I.subschemeι : V(I) ⟶ X`;
* `TauCeti.FiniteEtaleScheme.faithful_pullback_toScheme_zero`,
  `TauCeti.FiniteEtaleScheme.full_pullback_toScheme_zero`,
  `TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackToSchemeZero`: specializations to the initial
  level `Scheme.formalCompletion.toScheme X I 0`.

## References

* [The Stacks Project, Lemma 58.17.1](https://stacks.math.columbia.edu/tag/0EL8).
-/

public section

open CategoryTheory Limits MonoidalCategory Opposite AlgebraicGeometry
open scoped MonObj
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.AdicThickeningSystem

universe u

namespace TauCeti.FiniteEtaleScheme

section Helpers

variable {X : Scheme.{u}} (I : X.IdealSheafData)

private lemma relativeSpecMap_injective {S : Scheme.{u}} {A B : QuasicoherentAlgebra S}
    {f g : B ⟶ A} (h : CommMon.relativeSpecMap f.hom = CommMon.relativeSpecMap g.hom) :
    f = g :=
  Quiver.Hom.op_inj <| (relativeSpec S).map_injective <| MorphismProperty.Over.Hom.ext h

private lemma exists_relativeSpecMap_eq {S : Scheme.{u}} (A B : QuasicoherentAlgebra S)
    (u : A.obj.relativeSpec ⟶ B.obj.relativeSpec)
    (hu : u ≫ B.obj.relativeSpecToBase = A.obj.relativeSpecToBase) :
    ∃ f : B ⟶ A, CommMon.relativeSpecMap f.hom = u := by
  let u' : (relativeSpec S).obj (op A) ⟶ (relativeSpec S).obj (op B) :=
    MorphismProperty.Over.homMk u hu
  exact ⟨((relativeSpec S).preimage u').unop,
    congrArg (·.left) ((relativeSpec S).map_preimage u')⟩

-- Cancellations for `eqToHom` in `Y.Modules` are stated with explicit module variables: inside
-- proofs involving `QuasicoherentAlgebra` morphisms, `simp` and `rw` cannot normalize the mixture
-- of `Y.Modules` and underlying `SheafOfModules` instances on full-subcategory carriers.
private lemma eqToHom_cancel_conj {Y : Scheme.{u}} {A A' B B' : Y.Modules}
    (hA : A = A') (hB : B = B') (f : A ⟶ B) :
    eqToHom hA ≫ (eqToHom hA.symm ≫ f ≫ eqToHom hB) ≫ eqToHom hB.symm = f := by
  subst hA hB
  simp

private lemma eqToHom_conj_eq_iff {Y : Scheme.{u}} {A A' B B' : Y.Modules}
    (hA : A' = A) (hB : B' = B) (f g : A ⟶ B)
    (h : eqToHom hA ≫ f ≫ eqToHom hB.symm = eqToHom hA ≫ g ≫ eqToHom hB.symm) :
    f = g := by
  subst hA hB
  simpa using h

private lemma id_eq_eqToHom_conj {Y : Scheme.{u}} {A A' : Y.Modules} (hA : A' = A) :
    𝟙 A' = eqToHom hA ≫ 𝟙 A ≫ eqToHom hA.symm := by
  subst hA
  simp

private lemma eqToHom_conj_comp {Y : Scheme.{u}} {A A' B B' C C' : Y.Modules}
    (hA : A' = A) (hB : B' = B) (hC : C' = C) (u : A ⟶ B) (v : B ⟶ C) :
    (eqToHom hA ≫ u ≫ eqToHom hB.symm) ≫ (eqToHom hB ≫ v ≫ eqToHom hC.symm) =
      eqToHom hA ≫ (u ≫ v) ≫ eqToHom hC.symm := by
  subst hA hB hC
  simp

private lemma cancel_unit_eqToHom_conj {Y : Scheme.{u}} {U U' B B' A A' : Y.Modules}
    (e : U ≅ U') (hB : B' = B) (hA : A' = A) (u₁ : U ⟶ B) (g : B ⟶ A) (u₂ : U ⟶ A)
    (h : (e.inv ≫ u₁ ≫ eqToHom hB.symm) ≫ (eqToHom hB ≫ g ≫ eqToHom hA.symm) =
      e.inv ≫ u₂ ≫ eqToHom hA.symm) :
    u₁ ≫ g = u₂ := by
  subst hB hA
  simpa using h

private lemma cancel_mul_eqToHom_conj {Y : Scheme.{u}} {TB TA B B' A A' : Y.Modules}
    (dB : TB ⟶ B ⊗ B) [IsIso dB] (dA : TA ⟶ A ⊗ A) [IsIso dA]
    (hB : B' = B) (hA : A' = A) (mB : TB ⟶ B) (mA : TA ⟶ A) (g : B ⟶ A) (gg : TB ⟶ TA)
    (hδ : (g ⊗ₘ g) ≫ inv dA = inv dB ≫ gg)
    (h : ((eqToHom hB ⊗ₘ eqToHom hB) ≫ inv dB ≫ mB ≫ eqToHom hB.symm) ≫
        (eqToHom hB ≫ g ≫ eqToHom hA.symm) =
      ((eqToHom hB ≫ g ≫ eqToHom hA.symm) ⊗ₘ (eqToHom hB ≫ g ≫ eqToHom hA.symm)) ≫
        (eqToHom hA ⊗ₘ eqToHom hA) ≫ inv dA ≫ mA ≫ eqToHom hA.symm) :
    mB ≫ g = gg ≫ mA := by
  subst hB hA
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, id_tensorHom_id, Category.assoc] at h
  rw [reassoc_of% hδ] at h
  exact (cancel_epi (inv dB)).mp h

private lemma cancel_nat_eqToHom_conj {Y Z : Scheme.{u}} (P : Z.Modules ⥤ Y.Modules)
    {B₁ B₁' A₁ A₁' : Z.Modules} {PB' PA' B₀ B₀' A₀ A₀' : Y.Modules}
    (hB₁ : B₁' = B₁) (hA₁ : A₁' = A₁) (hPB : PB' = P.obj B₁') (hPA : PA' = P.obj A₁')
    (hB₀ : B₀' = B₀) (hA₀ : A₀' = A₀)
    (g₁ : B₁ ⟶ A₁) (g₀ : B₀ ⟶ A₀) (tA : P.obj A₁ ⟶ A₀) (tB : P.obj B₁ ⟶ B₀)
    (h : (eqToHom hPB ≫ P.map (eqToHom hB₁ ≫ g₁ ≫ eqToHom hA₁.symm) ≫ eqToHom hPA.symm) ≫
        (eqToHom (hPA.trans (congrArg P.obj hA₁)) ≫ tA ≫ eqToHom hA₀.symm) =
      (eqToHom (hPB.trans (congrArg P.obj hB₁)) ≫ tB ≫ eqToHom hB₀.symm) ≫
        (eqToHom hB₀ ≫ g₀ ≫ eqToHom hA₀.symm)) :
    P.map g₁ ≫ tA = tB ≫ g₀ := by
  subst hB₁ hA₁ hPB hPA hB₀ hA₀
  simpa using h

/-- The natural isomorphism identifying pullback of `𝒪_X`-algebras to level `n + 1` followed by
reduction along `ι n` with pullback to level `n`. -/
private noncomputable def levelAlgTransitionNatIso (n : ℕ) :
    QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I (n + 1)) ⋙
        QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n) ≅
      QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n) :=
  QuasicoherentAlgebra.pullbackComp ((X.formalCompletion I).ι n)
      (Scheme.formalCompletion.toScheme X I (n + 1)) ≪≫
    eqToIso (congrArg QuasicoherentAlgebra.pullback (Scheme.formalCompletion.ι_toScheme X I n))

private lemma levelAlgTransitionNatIso_hom_app_hom (𝒜 : QuasicoherentAlgebra X)
    (h𝒜 : Scheme.Modules.isFiniteLocallyFree X 𝒜.obj.X) (n : ℕ) :
    ((levelAlgTransitionNatIso I n).hom.app 𝒜).hom.hom.hom =
      eqToHom ((QuasicoherentAlgebra.pullback_obj_X ((X.formalCompletion I).ι n) _).trans
          (congrArg _ (QuasicoherentAlgebra.pullback_obj_X
            (Scheme.formalCompletion.toScheme X I (n + 1)) 𝒜))) ≫
        (((Scheme.formalCompletion.completionFunctor X I).obj
          ⟨𝒜.obj.X, h𝒜.2⟩).transitionIso n).hom ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X
            (Scheme.formalCompletion.toScheme X I n) 𝒜).symm := by
  have hcongr {Y : Scheme.{u}} {f g : Y ⟶ X} (h : f = g) :
      ((eqToIso (congrArg QuasicoherentAlgebra.pullback h)).hom.app 𝒜).hom.hom.hom =
        eqToHom (QuasicoherentAlgebra.pullback_obj_X f 𝒜) ≫
          (Scheme.Modules.pullbackCongr h).hom.app 𝒜.obj.X ≫
            eqToHom (QuasicoherentAlgebra.pullback_obj_X g 𝒜).symm := by
    subst h
    have hid₁ : ((eqToIso (rfl : QuasicoherentAlgebra.pullback f = _)).hom.app 𝒜).hom.hom.hom =
        𝟙 (((QuasicoherentAlgebra.pullback f).obj 𝒜).obj.X) := rfl
    have hid₂ : (Scheme.Modules.pullbackCongr (rfl : f = f)).hom.app 𝒜.obj.X = 𝟙 _ := rfl
    exact hid₁.trans <| (id_eq_eqToHom_conj (QuasicoherentAlgebra.pullback_obj_X f 𝒜)).trans <|
      congrArg (fun t ↦ _ ≫ t ≫ _) hid₂.symm
  have hsplit : ((levelAlgTransitionNatIso I n).hom.app 𝒜).hom.hom.hom =
      ((QuasicoherentAlgebra.pullbackComp ((X.formalCompletion I).ι n)
          (Scheme.formalCompletion.toScheme X I (n + 1))).hom.app 𝒜).hom.hom.hom ≫
        ((eqToIso (congrArg QuasicoherentAlgebra.pullback
          (Scheme.formalCompletion.ι_toScheme X I n))).hom.app 𝒜).hom.hom.hom := rfl
  refine hsplit.trans ?_
  refine (congrArg₂ (· ≫ ·)
    (QuasicoherentAlgebra.pullbackComp_hom_app_hom_hom_hom _ _ 𝒜)
    (hcongr (Scheme.formalCompletion.ι_toScheme X I n))).trans ?_
  exact eqToHom_conj_comp
    ((QuasicoherentAlgebra.pullback_obj_X ((X.formalCompletion I).ι n) _).trans
      (congrArg _ (QuasicoherentAlgebra.pullback_obj_X
        (Scheme.formalCompletion.toScheme X I (n + 1)) 𝒜)))
    (QuasicoherentAlgebra.pullback_obj_X
      ((X.formalCompletion I).ι n ≫ Scheme.formalCompletion.toScheme X I (n + 1)) 𝒜)
    (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) 𝒜)
    ((Scheme.Modules.pullbackComp ((X.formalCompletion I).ι n)
      (Scheme.formalCompletion.toScheme X I (n + 1))).hom.app 𝒜.obj.X)
    ((Scheme.Modules.pullbackCongr (Scheme.formalCompletion.ι_toScheme X I n)).hom.app 𝒜.obj.X)

/-- The step transition between the relative spectra of the levelwise algebras. -/
private noncomputable def levelSpecTransition (𝒜 : QuasicoherentAlgebra X) (n : ℕ) :
    ((QuasicoherentAlgebra.pullback
        (Scheme.formalCompletion.toScheme X I n)).obj 𝒜).obj.relativeSpec ⟶
      ((QuasicoherentAlgebra.pullback
        (Scheme.formalCompletion.toScheme X I (n + 1))).obj 𝒜).obj.relativeSpec :=
  CommMon.relativeSpecMap ((levelAlgTransitionNatIso I n).hom.app 𝒜).hom ≫
    relativeSpecPullbackFst
      ((QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I (n + 1))).obj 𝒜)
      ((X.formalCompletion I).ι n)

private lemma levelSpecTransition_compatible_iff {𝒜 ℬ : QuasicoherentAlgebra X}
    (b : ∀ n, (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj ℬ ⟶
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj 𝒜) (n : ℕ) :
    levelSpecTransition I 𝒜 n ≫ CommMon.relativeSpecMap (b (n + 1)).hom =
        CommMon.relativeSpecMap (b n).hom ≫ levelSpecTransition I ℬ n ↔
      (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (b (n + 1)) ≫
          (levelAlgTransitionNatIso I n).hom.app 𝒜 =
        (levelAlgTransitionNatIso I n).hom.app ℬ ≫ b n := by
  let B₁ := (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I (n + 1))).obj ℬ
  let A₁ := (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I (n + 1))).obj 𝒜
  have : Mono (relativeSpecPullbackFst B₁ ((X.formalCompletion I).ι n)) := by
    rw [← (isPullback_relativeSpecPullbackFst B₁ ((X.formalCompletion I).ι n)).isoPullback_hom_fst]
    exact mono_comp _ _
  have hcomp {Y : Scheme.{u}} {M N P : QuasicoherentAlgebra Y} (u : M ⟶ N) (v : N ⟶ P) :
      CommMon.relativeSpecMap (u ≫ v).hom =
        CommMon.relativeSpecMap v.hom ≫ CommMon.relativeSpecMap u.hom :=
    CommMon.relativeSpecMap_comp u.hom v.hom
  have hlhs : levelSpecTransition I 𝒜 n ≫ CommMon.relativeSpecMap (b (n + 1)).hom =
      CommMon.relativeSpecMap
          ((QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (b (n + 1)) ≫
            (levelAlgTransitionNatIso I n).hom.app 𝒜).hom ≫
        relativeSpecPullbackFst B₁ ((X.formalCompletion I).ι n) :=
    (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·)
        (relativeSpecMap_pullback_map_relativeSpecPullbackFst A₁
          ((X.formalCompletion I).ι n) (b (n + 1))).symm).trans <|
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (hcomp _ _).symm)
  have hrhs : CommMon.relativeSpecMap (b n).hom ≫ levelSpecTransition I ℬ n =
      CommMon.relativeSpecMap ((levelAlgTransitionNatIso I n).hom.app ℬ ≫ b n).hom ≫
        relativeSpecPullbackFst B₁ ((X.formalCompletion I).ι n) :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (hcomp _ _).symm)
  exact ⟨fun h ↦ relativeSpecMap_injective ((cancel_mono _).mp (hlhs.symm.trans (h.trans hrhs))),
    fun h ↦ hlhs.trans ((congrArg (fun k ↦ CommMon.relativeSpecMap k.hom ≫ _) h).trans hrhs.symm)⟩

/-- The canonical morphism `X.formalCompletion I ⟶ ofScheme.obj X` assembled from the closed
immersions `toScheme X I n`. -/
@[simps]
private noncomputable def formalCompletionToOfScheme :
    X.formalCompletion I ⟶ AdicThickeningSystem.ofScheme.obj X where
  app n := Scheme.formalCompletion.toScheme X I n
  naturality n := (Scheme.formalCompletion.ι_toScheme X I n).trans (Category.comp_id _).symm

/-- The adic thickening system obtained by pulling back `Spec_X(𝒜) ⟶ X` along the levels of
`X.formalCompletion I`. -/
private noncomputable def formalPullbackSystem (𝒜 : QuasicoherentAlgebra X) :
    AdicThickeningSystem.{u} :=
  AdicThickeningSystem.pullback (formalCompletionToOfScheme I)
    (AdicThickeningSystem.ofScheme.map 𝒜.obj.relativeSpecToBase)

/-- The first projection `formalPullbackSystem I 𝒜 ⟶ X.formalCompletion I`. -/
private noncomputable def formalPullbackToBase (𝒜 : QuasicoherentAlgebra X) :
    formalPullbackSystem I 𝒜 ⟶ X.formalCompletion I :=
  AdicThickeningSystem.pullback.fst (formalCompletionToOfScheme I)
    (AdicThickeningSystem.ofScheme.map 𝒜.obj.relativeSpecToBase)

/-- The second projection `formalPullbackSystem I 𝒜 ⟶ ofScheme.obj Spec_X(𝒜)`. -/
private noncomputable def formalPullbackSnd (𝒜 : QuasicoherentAlgebra X) :
    formalPullbackSystem I 𝒜 ⟶ AdicThickeningSystem.ofScheme.obj 𝒜.obj.relativeSpec :=
  AdicThickeningSystem.pullback.snd (formalCompletionToOfScheme I)
    (AdicThickeningSystem.ofScheme.map 𝒜.obj.relativeSpecToBase)

/-- Level `n` of `formalPullbackSnd`, typed directly with target `𝒜.obj.relativeSpec`. -/
private noncomputable def formalPullbackSndApp (𝒜 : QuasicoherentAlgebra X) (n : ℕ) :
    (formalPullbackSystem I 𝒜).X n ⟶ 𝒜.obj.relativeSpec :=
  (formalPullbackSnd I 𝒜).app n

private lemma formalPullbackSndApp_naturality (𝒜 : QuasicoherentAlgebra X) (n : ℕ) :
    (formalPullbackSystem I 𝒜).ι n ≫ formalPullbackSndApp I 𝒜 (n + 1) =
      formalPullbackSndApp I 𝒜 n :=
  ((formalPullbackSnd I 𝒜).naturality n).trans (Category.comp_id _)

private lemma isPullback_formalPullbackSystem_X (𝒜 : QuasicoherentAlgebra X) (n : ℕ) :
    IsPullback
      ((formalPullbackToBase I 𝒜).app n)
      (formalPullbackSndApp I 𝒜 n)
      (Scheme.formalCompletion.toScheme X I n)
      𝒜.obj.relativeSpecToBase := by
  rw [formalPullbackToBase, AdicThickeningSystem.pullback.fst_app,
    formalPullbackSndApp, formalPullbackSnd, AdicThickeningSystem.pullback.snd_app]
  exact IsPullback.of_hasPullback
    ((formalCompletionToOfScheme I).app n)
    ((AdicThickeningSystem.ofScheme.map 𝒜.obj.relativeSpecToBase).app n)

private instance etale_formalPullbackToBase_app (𝒜 : QuasicoherentAlgebra X)
    [Etale 𝒜.obj.relativeSpecToBase] (n : ℕ) :
    Etale ((formalPullbackToBase I 𝒜).app n) :=
  MorphismProperty.of_isPullback (isPullback_formalPullbackSystem_X I 𝒜 n).flip ‹_›

/-- The morphism `formalPullbackSystem I 𝒜 ⟶ formalPullbackSystem I ℬ` over `X.formalCompletion I`
induced by an algebra homomorphism `β : ℬ ⟶ 𝒜`. -/
private noncomputable def formalPullbackMap {𝒜 ℬ : QuasicoherentAlgebra X} (β : ℬ ⟶ 𝒜) :
    formalPullbackSystem I 𝒜 ⟶ formalPullbackSystem I ℬ :=
  AdicThickeningSystem.pullback.lift
    (formalPullbackToBase I 𝒜)
    (formalPullbackSnd I 𝒜 ≫ AdicThickeningSystem.ofScheme.map (CommMon.relativeSpecMap β.hom))
    (calc formalPullbackToBase I 𝒜 ≫ formalCompletionToOfScheme I
        = formalPullbackSnd I 𝒜 ≫ AdicThickeningSystem.ofScheme.map 𝒜.obj.relativeSpecToBase :=
          AdicThickeningSystem.pullback.condition _ _
      _ = formalPullbackSnd I 𝒜 ≫
            AdicThickeningSystem.ofScheme.map
              (CommMon.relativeSpecMap β.hom ≫ ℬ.obj.relativeSpecToBase) :=
          congrArg (formalPullbackSnd I 𝒜 ≫ AdicThickeningSystem.ofScheme.map ·)
            (CommMon.relativeSpecMap_relativeSpecToBase β.hom).symm
      _ = (formalPullbackSnd I 𝒜 ≫
              AdicThickeningSystem.ofScheme.map (CommMon.relativeSpecMap β.hom)) ≫
            AdicThickeningSystem.ofScheme.map ℬ.obj.relativeSpecToBase := by
          rw [AdicThickeningSystem.ofScheme.map_comp, Category.assoc])

private lemma formalPullbackMap_comp_toBase {𝒜 ℬ : QuasicoherentAlgebra X} (β : ℬ ⟶ 𝒜) :
    formalPullbackMap I β ≫ formalPullbackToBase I ℬ = formalPullbackToBase I 𝒜 :=
  AdicThickeningSystem.pullback.lift_fst _ _ _

private lemma formalPullbackMap_comp_snd {𝒜 ℬ : QuasicoherentAlgebra X} (β : ℬ ⟶ 𝒜) :
    formalPullbackMap I β ≫ formalPullbackSnd I ℬ =
      formalPullbackSnd I 𝒜 ≫ AdicThickeningSystem.ofScheme.map (CommMon.relativeSpecMap β.hom) :=
  AdicThickeningSystem.pullback.lift_snd _ _ _

private lemma formalPullbackMap_app_comp_sndApp {𝒜 ℬ : QuasicoherentAlgebra X} (β : ℬ ⟶ 𝒜)
    (n : ℕ) :
    (formalPullbackMap I β).app n ≫ formalPullbackSndApp I ℬ n =
      formalPullbackSndApp I 𝒜 n ≫ CommMon.relativeSpecMap β.hom :=
  congrArg (fun k ↦ k.app n) (formalPullbackMap_comp_snd I β)

attribute [irreducible]
  formalPullbackSystem formalPullbackToBase formalPullbackSnd formalPullbackSndApp formalPullbackMap

/-- The canonical isomorphism at level `n` between `Spec_{X_n}(i_n^* 𝒜)` and the `n`-th level of
`formalPullbackSystem I 𝒜`. -/
private noncomputable def levelSpecIsoFormalPullback (𝒜 : QuasicoherentAlgebra X) (n : ℕ) :
    ((QuasicoherentAlgebra.pullback
        (Scheme.formalCompletion.toScheme X I n)).obj 𝒜).obj.relativeSpec ≅
      (formalPullbackSystem I 𝒜).X n :=
  (isPullback_relativeSpecPullbackFst 𝒜
    (Scheme.formalCompletion.toScheme X I n)).flip.isoIsPullback _ _
    (isPullback_formalPullbackSystem_X I 𝒜 n)

private lemma levelSpecIsoFormalPullback_hom_fst (𝒜 : QuasicoherentAlgebra X) (n : ℕ) :
    (levelSpecIsoFormalPullback I 𝒜 n).hom ≫ (formalPullbackToBase I 𝒜).app n =
      ((QuasicoherentAlgebra.pullback
        (Scheme.formalCompletion.toScheme X I n)).obj 𝒜).obj.relativeSpecToBase :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

private lemma levelSpecIsoFormalPullback_hom_snd (𝒜 : QuasicoherentAlgebra X) (n : ℕ) :
    (levelSpecIsoFormalPullback I 𝒜 n).hom ≫ formalPullbackSndApp I 𝒜 n =
      relativeSpecPullbackFst 𝒜 (Scheme.formalCompletion.toScheme X I n) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

attribute [irreducible] levelSpecIsoFormalPullback

private lemma relativeSpecMap_eqToIso_pullback_comp_fst (𝒜 : QuasicoherentAlgebra X)
    {Y : Scheme.{u}} {f g : Y ⟶ X} (h : f = g) :
    CommMon.relativeSpecMap
        ((eqToIso (congrArg QuasicoherentAlgebra.pullback h)).hom.app 𝒜).hom ≫
      relativeSpecPullbackFst 𝒜 f = relativeSpecPullbackFst 𝒜 g := by
  subst h
  have hid : ((eqToIso (rfl : QuasicoherentAlgebra.pullback f = _)).hom.app 𝒜).hom =
      𝟙 (((QuasicoherentAlgebra.pullback f).obj 𝒜).obj) := rfl
  exact (congrArg (· ≫ _)
    ((congrArg CommMon.relativeSpecMap hid).trans (CommMon.relativeSpecMap_id _))).trans
    (Category.id_comp _)

private lemma levelSpecTransition_comp_iso (𝒜 : QuasicoherentAlgebra X) (n : ℕ) :
    levelSpecTransition I 𝒜 n ≫ (levelSpecIsoFormalPullback I 𝒜 (n + 1)).hom =
      (levelSpecIsoFormalPullback I 𝒜 n).hom ≫ (formalPullbackSystem I 𝒜).ι n := by
  let i_n := Scheme.formalCompletion.toScheme X I n
  let i_succ := Scheme.formalCompletion.toScheme X I (n + 1)
  let ι_n := (X.formalCompletion I).ι n
  apply (isPullback_formalPullbackSystem_X I 𝒜 (n + 1)).hom_ext
  · calc (levelSpecTransition I 𝒜 n ≫ (levelSpecIsoFormalPullback I 𝒜 (n + 1)).hom) ≫
          (formalPullbackToBase I 𝒜).app (n + 1)
        = levelSpecTransition I 𝒜 n ≫
            ((QuasicoherentAlgebra.pullback i_succ).obj 𝒜).obj.relativeSpecToBase := by
          rw [Category.assoc, levelSpecIsoFormalPullback_hom_fst]
      _ = CommMon.relativeSpecMap ((levelAlgTransitionNatIso I n).hom.app 𝒜).hom ≫
            ((QuasicoherentAlgebra.pullback ι_n).obj
              ((QuasicoherentAlgebra.pullback i_succ).obj 𝒜)).obj.relativeSpecToBase ≫ ι_n := by
          rw [levelSpecTransition, Category.assoc, relativeSpecPullbackFst_relativeSpecToBase]
      _ = ((QuasicoherentAlgebra.pullback i_n).obj 𝒜).obj.relativeSpecToBase ≫ ι_n :=
          CommMon.relativeSpecMap_relativeSpecToBase_assoc _ _
      _ = (levelSpecIsoFormalPullback I 𝒜 n).hom ≫
            ((formalPullbackToBase I 𝒜).app n ≫ ι_n) := by
          rw [← levelSpecIsoFormalPullback_hom_fst I 𝒜 n, Category.assoc]
      _ = ((levelSpecIsoFormalPullback I 𝒜 n).hom ≫ (formalPullbackSystem I 𝒜).ι n) ≫
            (formalPullbackToBase I 𝒜).app (n + 1) := by
          rw [← (formalPullbackToBase I 𝒜).naturality n, Category.assoc]
  · calc (levelSpecTransition I 𝒜 n ≫ (levelSpecIsoFormalPullback I 𝒜 (n + 1)).hom) ≫
          formalPullbackSndApp I 𝒜 (n + 1)
        = levelSpecTransition I 𝒜 n ≫ relativeSpecPullbackFst 𝒜 i_succ := by
          rw [Category.assoc, levelSpecIsoFormalPullback_hom_snd]
      _ = CommMon.relativeSpecMap
            ((eqToIso (congrArg QuasicoherentAlgebra.pullback
              (Scheme.formalCompletion.ι_toScheme X I n))).hom.app 𝒜).hom ≫
            (CommMon.relativeSpecMap
                ((QuasicoherentAlgebra.pullbackComp ι_n i_succ).hom.app 𝒜).hom ≫
              relativeSpecPullbackFst ((QuasicoherentAlgebra.pullback i_succ).obj 𝒜) ι_n ≫
              relativeSpecPullbackFst 𝒜 i_succ) := by
          have hmap : CommMon.relativeSpecMap ((levelAlgTransitionNatIso I n).hom.app 𝒜).hom =
              CommMon.relativeSpecMap
                ((eqToIso (congrArg QuasicoherentAlgebra.pullback
                  (Scheme.formalCompletion.ι_toScheme X I n))).hom.app 𝒜).hom ≫
              CommMon.relativeSpecMap
                ((QuasicoherentAlgebra.pullbackComp ι_n i_succ).hom.app 𝒜).hom :=
            CommMon.relativeSpecMap_comp _ _
          rw [levelSpecTransition, hmap]
          simp only [Category.assoc]
          rfl
      _ = relativeSpecPullbackFst 𝒜 i_n := by
          rw [← relativeSpecPullbackFst_comp 𝒜 i_succ ι_n]
          exact relativeSpecMap_eqToIso_pullback_comp_fst 𝒜
            (Scheme.formalCompletion.ι_toScheme X I n)
      _ = (levelSpecIsoFormalPullback I 𝒜 n).hom ≫ formalPullbackSndApp I 𝒜 n :=
          (levelSpecIsoFormalPullback_hom_snd I 𝒜 n).symm
      _ = ((levelSpecIsoFormalPullback I 𝒜 n).hom ≫ (formalPullbackSystem I 𝒜).ι n) ≫
            formalPullbackSndApp I 𝒜 (n + 1) := by
          rw [Category.assoc, formalPullbackSndApp_naturality]

private lemma levelSpecIso_hom_formalPullbackMap_app {𝒜 ℬ : QuasicoherentAlgebra X} (β : ℬ ⟶ 𝒜)
    (n : ℕ) :
    (levelSpecIsoFormalPullback I 𝒜 n).hom ≫ (formalPullbackMap I β).app n =
      CommMon.relativeSpecMap
          ((QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).map β).hom ≫
        (levelSpecIsoFormalPullback I ℬ n).hom := by
  have hto : (formalPullbackMap I β).app n ≫ (formalPullbackToBase I ℬ).app n =
      (formalPullbackToBase I 𝒜).app n :=
    congrArg (fun k ↦ k.app n) (formalPullbackMap_comp_toBase I β)
  apply (isPullback_formalPullbackSystem_X I ℬ n).hom_ext
  · calc ((levelSpecIsoFormalPullback I 𝒜 n).hom ≫ (formalPullbackMap I β).app n) ≫
          (formalPullbackToBase I ℬ).app n
        = (levelSpecIsoFormalPullback I 𝒜 n).hom ≫ (formalPullbackToBase I 𝒜).app n := by
          rw [Category.assoc, hto]
      _ = ((QuasicoherentAlgebra.pullback
            (Scheme.formalCompletion.toScheme X I n)).obj 𝒜).obj.relativeSpecToBase :=
          levelSpecIsoFormalPullback_hom_fst I 𝒜 n
      _ = CommMon.relativeSpecMap
            ((QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).map β).hom ≫
            ((QuasicoherentAlgebra.pullback
              (Scheme.formalCompletion.toScheme X I n)).obj ℬ).obj.relativeSpecToBase :=
          (CommMon.relativeSpecMap_relativeSpecToBase _).symm
      _ = _ := by
          rw [← levelSpecIsoFormalPullback_hom_fst I ℬ n, Category.assoc]
  · calc ((levelSpecIsoFormalPullback I 𝒜 n).hom ≫ (formalPullbackMap I β).app n) ≫
          formalPullbackSndApp I ℬ n
        = (levelSpecIsoFormalPullback I 𝒜 n).hom ≫
            (formalPullbackSndApp I 𝒜 n ≫ CommMon.relativeSpecMap β.hom) := by
          rw [Category.assoc, formalPullbackMap_app_comp_sndApp]
      _ = ((levelSpecIsoFormalPullback I 𝒜 n).hom ≫ formalPullbackSndApp I 𝒜 n) ≫
            CommMon.relativeSpecMap β.hom :=
          (Category.assoc (levelSpecIsoFormalPullback I 𝒜 n).hom
            (formalPullbackSndApp I 𝒜 n) (CommMon.relativeSpecMap β.hom)).symm
      _ = relativeSpecPullbackFst 𝒜 (Scheme.formalCompletion.toScheme X I n) ≫
            CommMon.relativeSpecMap β.hom := by
          rw [levelSpecIsoFormalPullback_hom_snd]
      _ = CommMon.relativeSpecMap
            ((QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).map β).hom ≫
            relativeSpecPullbackFst ℬ (Scheme.formalCompletion.toScheme X I n) :=
          (relativeSpecMap_pullback_map_relativeSpecPullbackFst _ _ _).symm
      _ = _ := by
          rw [← levelSpecIsoFormalPullback_hom_snd I ℬ n, Category.assoc]

/-- When a morphism `γ` into a finite locally free module on `X` restricts at every level of
`X.formalCompletion I` to an `𝒪`-algebra homomorphism, `γ` preserves the algebra unit. -/
private lemma one_hom_of_forall_level {𝒜 ℬ : QuasicoherentAlgebra X}
    (h𝒜 : Scheme.Modules.isFiniteLocallyFree X 𝒜.obj.X)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful]
    (b : ∀ n, (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj ℬ ⟶
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj 𝒜)
    (γ : ℬ.obj.X ⟶ 𝒜.obj.X)
    (hb : ∀ n, (b n).hom.hom.hom =
      eqToHom (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) ℬ) ≫
        (Scheme.Modules.pullback (Scheme.formalCompletion.toScheme X I n)).map γ ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X
            (Scheme.formalCompletion.toScheme X I n) 𝒜).symm) :
    η[ℬ.obj.X] ≫ γ = η[𝒜.obj.X] := by
  let F := FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
    Scheme.formalCompletion.completionFunctor X I
  let U_X : FiniteLocallyFreeSheaf X :=
    ⟨𝟙_ X.Modules, (Scheme.Modules.isFiniteLocallyFree X).prop_unit⟩
  let E_𝒜 : FiniteLocallyFreeSheaf X := ⟨𝒜.obj.X, h𝒜⟩
  suffices h : (ObjectProperty.homMk (η[ℬ.obj.X] ≫ γ) : U_X ⟶ E_𝒜) =
      ObjectProperty.homMk η[𝒜.obj.X] from congrArg (·.hom) h
  apply F.map_injective
  refine CoherentFormalModule.hom_ext fun n ↦ ?_
  let i_n := Scheme.formalCompletion.toScheme X I n
  -- `pullback_obj_one` uses `monoidalCategorySheafOfModules`, which agrees with
  -- `Scheme.Modules.instMonoidalCategory` at `default` transparency; apply `congrArg₂` directly.
  have hone₁ : η[((QuasicoherentAlgebra.pullback i_n).obj ℬ).obj.X] ≫ (b n).hom.hom.hom =
      η[((QuasicoherentAlgebra.pullback i_n).obj 𝒜).obj.X] :=
    IsMonHom.one_hom (b n).hom.hom.hom
  have hone₂ := (congrArg₂ (· ≫ ·) (QuasicoherentAlgebra.pullback_obj_one i_n ℬ) (hb n)).symm.trans
    (hone₁.trans (QuasicoherentAlgebra.pullback_obj_one i_n 𝒜))
  exact ((Scheme.Modules.pullback i_n).map_comp η[ℬ.obj.X] γ).trans
    (cancel_unit_eqToHom_conj (Scheme.Modules.pullbackObjUnitIso i_n)
      (QuasicoherentAlgebra.pullback_obj_X i_n ℬ)
      (QuasicoherentAlgebra.pullback_obj_X i_n 𝒜) _ _ _ hone₂)

/-- When a morphism `γ` between finite locally free modules on `X` restricts at every level of
`X.formalCompletion I` to an `𝒪`-algebra homomorphism, `γ` preserves multiplication. -/
private lemma mul_hom_of_forall_level {𝒜 ℬ : QuasicoherentAlgebra X}
    (h𝒜 : Scheme.Modules.isFiniteLocallyFree X 𝒜.obj.X)
    (hℬ : Scheme.Modules.isFiniteLocallyFree X ℬ.obj.X)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful]
    (b : ∀ n, (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj ℬ ⟶
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj 𝒜)
    (γ : ℬ.obj.X ⟶ 𝒜.obj.X)
    (hb : ∀ n, (b n).hom.hom.hom =
      eqToHom (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) ℬ) ≫
        (Scheme.Modules.pullback (Scheme.formalCompletion.toScheme X I n)).map γ ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X
            (Scheme.formalCompletion.toScheme X I n) 𝒜).symm) :
    μ[ℬ.obj.X] ≫ γ = (γ ⊗ₘ γ) ≫ μ[𝒜.obj.X] := by
  let F := FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
    Scheme.formalCompletion.completionFunctor X I
  let T_ℬ : FiniteLocallyFreeSheaf X :=
    ⟨ℬ.obj.X ⊗ ℬ.obj.X, ObjectProperty.prop_tensor hℬ hℬ⟩
  let E_𝒜 : FiniteLocallyFreeSheaf X := ⟨𝒜.obj.X, h𝒜⟩
  suffices h : (ObjectProperty.homMk (μ[ℬ.obj.X] ≫ γ) : T_ℬ ⟶ E_𝒜) =
      ObjectProperty.homMk ((γ ⊗ₘ γ) ≫ μ[𝒜.obj.X]) from congrArg (·.hom) h
  apply F.map_injective
  refine CoherentFormalModule.hom_ext fun n ↦ ?_
  let i_n := Scheme.formalCompletion.toScheme X I n
  have := Scheme.Modules.isIso_pullback_δ_of_isQuasicoherent i_n ℬ.obj.X ℬ.obj.X
  have := Scheme.Modules.isIso_pullback_δ_of_isQuasicoherent i_n 𝒜.obj.X 𝒜.obj.X
  have hδ : ((Scheme.Modules.pullback i_n).map γ ⊗ₘ (Scheme.Modules.pullback i_n).map γ) ≫
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback i_n) 𝒜.obj.X 𝒜.obj.X) =
    inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback i_n) ℬ.obj.X ℬ.obj.X) ≫
      (Scheme.Modules.pullback i_n).map (γ ⊗ₘ γ) := by
    rw [IsIso.comp_inv_eq, Category.assoc,
      ← Functor.OplaxMonoidal.δ_natural (Scheme.Modules.pullback i_n) γ γ,
      IsIso.inv_hom_id_assoc]
  have hmul₁ : μ[((QuasicoherentAlgebra.pullback i_n).obj ℬ).obj.X] ≫ (b n).hom.hom.hom =
      ((b n).hom.hom.hom ⊗ₘ (b n).hom.hom.hom) ≫
        μ[((QuasicoherentAlgebra.pullback i_n).obj 𝒜).obj.X] :=
    IsMonHom.mul_hom (b n).hom.hom.hom
  have hmul₂ := (congrArg₂ (· ≫ ·) (QuasicoherentAlgebra.pullback_obj_mul i_n ℬ) (hb n)).symm.trans
    (hmul₁.trans (congrArg₂ (· ≫ ·) (congrArg₂ (· ⊗ₘ ·) (hb n) (hb n))
      (QuasicoherentAlgebra.pullback_obj_mul i_n 𝒜)))
  exact ((Scheme.Modules.pullback i_n).map_comp μ[ℬ.obj.X] γ).trans
    ((cancel_mul_eqToHom_conj
      (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback i_n) ℬ.obj.X ℬ.obj.X)
      (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback i_n) 𝒜.obj.X 𝒜.obj.X)
      (QuasicoherentAlgebra.pullback_obj_X i_n ℬ)
      (QuasicoherentAlgebra.pullback_obj_X i_n 𝒜) _ _ _ _ hδ hmul₂).trans
      ((Scheme.Modules.pullback i_n).map_comp (γ ⊗ₘ γ) μ[𝒜.obj.X]).symm)

private lemma isMonHom_of_forall_level {𝒜 ℬ : QuasicoherentAlgebra X}
    (h𝒜 : Scheme.Modules.isFiniteLocallyFree X 𝒜.obj.X)
    (hℬ : Scheme.Modules.isFiniteLocallyFree X ℬ.obj.X)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful]
    (b : ∀ n, (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj ℬ ⟶
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj 𝒜)
    (γ : ℬ.obj.X ⟶ 𝒜.obj.X)
    (hγ : ∀ n, (Scheme.Modules.pullback (Scheme.formalCompletion.toScheme X I n)).map γ =
      eqToHom (QuasicoherentAlgebra.pullback_obj_X
          (Scheme.formalCompletion.toScheme X I n) ℬ).symm ≫
        (b n).hom.hom.hom ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X
            (Scheme.formalCompletion.toScheme X I n) 𝒜)) :
    IsMonHom γ := by
  have hb (n : ℕ) : (b n).hom.hom.hom =
      eqToHom (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) ℬ) ≫
        (Scheme.Modules.pullback (Scheme.formalCompletion.toScheme X I n)).map γ ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X
            (Scheme.formalCompletion.toScheme X I n) 𝒜).symm :=
    (eqToHom_cancel_conj
      (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) ℬ)
      (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) 𝒜)
      (b n).hom.hom.hom).symm.trans
      (congrArg (fun t ↦ eqToHom _ ≫ t ≫ eqToHom _) (hγ n).symm)
  exact ⟨one_hom_of_forall_level I h𝒜 b γ hb, mul_hom_of_forall_level I h𝒜 hℬ b γ hb⟩

/-- Compatibility of a family of levelwise algebra maps with `levelAlgTransitionNatIso` yields
naturality of the underlying module maps as a morphism in `CoherentFormalModule`. -/
private lemma naturality_of_levelAlgebraHoms {𝒜 ℬ : QuasicoherentAlgebra X}
    (h𝒜 : Scheme.Modules.isFiniteLocallyFree X 𝒜.obj.X)
    (hℬ : Scheme.Modules.isFiniteLocallyFree X ℬ.obj.X)
    (b : ∀ n, (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj ℬ ⟶
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj 𝒜)
    (hb : ∀ n, (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (b (n + 1)) ≫
      (levelAlgTransitionNatIso I n).hom.app 𝒜 = (levelAlgTransitionNatIso I n).hom.app ℬ ≫ b n)
    (n : ℕ) :
    (Scheme.Modules.pullback ((X.formalCompletion I).ι n)).map
        (eqToHom (QuasicoherentAlgebra.pullback_obj_X
            (Scheme.formalCompletion.toScheme X I (n + 1)) ℬ).symm ≫
          (b (n + 1)).hom.hom.hom ≫
            eqToHom (QuasicoherentAlgebra.pullback_obj_X
              (Scheme.formalCompletion.toScheme X I (n + 1)) 𝒜)) ≫
      (((Scheme.formalCompletion.completionFunctor X I).obj ⟨𝒜.obj.X, h𝒜.2⟩).transitionIso n).hom =
    (((Scheme.formalCompletion.completionFunctor X I).obj ⟨ℬ.obj.X, hℬ.2⟩).transitionIso n).hom ≫
      (eqToHom (QuasicoherentAlgebra.pullback_obj_X
          (Scheme.formalCompletion.toScheme X I n) ℬ).symm ≫
        (b n).hom.hom.hom ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X
            (Scheme.formalCompletion.toScheme X I n) 𝒜)) := by
  have hcomp {Y : Scheme.{u}} {A B C : QuasicoherentAlgebra Y} (u : A ⟶ B) (v : B ⟶ C) :
      (u ≫ v).hom.hom.hom = u.hom.hom.hom ≫ v.hom.hom.hom := rfl
  have hbn :
      ((QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (b (n + 1))).hom.hom.hom ≫
        ((levelAlgTransitionNatIso I n).hom.app 𝒜).hom.hom.hom =
      ((levelAlgTransitionNatIso I n).hom.app ℬ).hom.hom.hom ≫ (b n).hom.hom.hom :=
    (hcomp _ _).symm.trans ((congrArg (fun k ↦ k.hom.hom.hom) (hb n)).trans (hcomp _ _))
  have hb_succ := (eqToHom_cancel_conj
    (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I (n + 1)) ℬ)
    (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I (n + 1)) 𝒜)
    (b (n + 1)).hom.hom.hom).symm
  have hb_curr := (eqToHom_cancel_conj
    (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) ℬ)
    (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) 𝒜)
    (b n).hom.hom.hom).symm
  have hbn' := (congrArg₂ (· ≫ ·)
    ((QuasicoherentAlgebra.pullback_map_hom_hom_hom _ (b (n + 1))).trans
      (congrArg (fun t ↦ eqToHom _ ≫ (Scheme.Modules.pullback _).map t ≫ eqToHom _) hb_succ))
    (levelAlgTransitionNatIso_hom_app_hom I 𝒜 h𝒜 n)).symm.trans
    (hbn.trans (congrArg₂ (· ≫ ·) (levelAlgTransitionNatIso_hom_app_hom I ℬ hℬ n) hb_curr))
  exact cancel_nat_eqToHom_conj (Scheme.Modules.pullback ((X.formalCompletion I).ι n))
    (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I (n + 1)) ℬ)
    (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I (n + 1)) 𝒜)
    (QuasicoherentAlgebra.pullback_obj_X ((X.formalCompletion I).ι n) _)
    (QuasicoherentAlgebra.pullback_obj_X ((X.formalCompletion I).ι n) _)
    (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) ℬ)
    (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) 𝒜)
    _ _ _ _ hbn'

/-- Descends a compatible family of levelwise algebra homomorphisms on `X.formalCompletion I` to an
algebra homomorphism on `X`, using fullness and faithfulness of formal completion on finite locally
free sheaves. -/
private lemma exists_algebraHom_of_levelAlgebraHoms {𝒜 ℬ : QuasicoherentAlgebra X}
    (h𝒜 : Scheme.Modules.isFiniteLocallyFree X 𝒜.obj.X)
    (hℬ : Scheme.Modules.isFiniteLocallyFree X ℬ.obj.X)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful]
    (b : ∀ n, (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj ℬ ⟶
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj 𝒜)
    (hb : ∀ n, (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (b (n + 1)) ≫
      (levelAlgTransitionNatIso I n).hom.app 𝒜 = (levelAlgTransitionNatIso I n).hom.app ℬ ≫ b n) :
    ∃ β : ℬ ⟶ 𝒜, ∀ n,
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).map β = b n := by
  let F := FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
    Scheme.formalCompletion.completionFunctor X I
  let E_𝒜 : FiniteLocallyFreeSheaf X := ⟨𝒜.obj.X, h𝒜⟩
  let E_ℬ : FiniteLocallyFreeSheaf X := ⟨ℬ.obj.X, hℬ⟩
  let gHom : F.obj E_ℬ ⟶ F.obj E_𝒜 :=
    { app n :=
        eqToHom (QuasicoherentAlgebra.pullback_obj_X
            (Scheme.formalCompletion.toScheme X I n) ℬ).symm ≫
          (b n).hom.hom.hom ≫
            eqToHom (QuasicoherentAlgebra.pullback_obj_X
              (Scheme.formalCompletion.toScheme X I n) 𝒜)
      naturality := naturality_of_levelAlgebraHoms I h𝒜 hℬ b hb }
  obtain ⟨γ, hγ⟩ := F.map_surjective gHom
  have hγ_app (n : ℕ) :
      (Scheme.Modules.pullback (Scheme.formalCompletion.toScheme X I n)).map γ.hom = gHom.app n :=
    congrArg (fun k ↦ k.app n) hγ
  have : IsMonHom γ.hom := isMonHom_of_forall_level I h𝒜 hℬ b γ.hom hγ_app
  let β : ℬ ⟶ 𝒜 := ObjectProperty.homMk (CommMon.homMk (Mon.Hom.mk' γ.hom
    (IsMonHom.one_hom γ.hom) (IsMonHom.mul_hom γ.hom)))
  refine ⟨β, fun n ↦ ?_⟩
  apply ObjectProperty.hom_ext
  apply CommMon.hom_ext
  exact (QuasicoherentAlgebra.pullback_map_hom_hom_hom _ β).trans <|
    (congrArg (fun t ↦ eqToHom _ ≫ t ≫ eqToHom _) (hγ_app n)).trans
      (eqToHom_cancel_conj
        (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) ℬ)
        (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) 𝒜)
        (b n).hom.hom.hom)

/-- Two quasi-coherent algebra homomorphisms between finite locally free `𝒪_X`-algebras are equal
once their pullbacks to all infinitesimal levels of `X.formalCompletion I` agree. -/
private lemma algebraHom_eq_of_forall_level {𝒜 ℬ : QuasicoherentAlgebra X}
    (h𝒜 : Scheme.Modules.isFiniteLocallyFree X 𝒜.obj.X)
    (hℬ : Scheme.Modules.isFiniteLocallyFree X ℬ.obj.X)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful]
    {β₁ β₂ : ℬ ⟶ 𝒜}
    (hbn : ∀ n, (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).map β₁ =
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).map β₂) :
    β₁ = β₂ := by
  let F := FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
    Scheme.formalCompletion.completionFunctor X I
  let E_𝒜 : FiniteLocallyFreeSheaf X := ⟨𝒜.obj.X, h𝒜⟩
  let E_ℬ : FiniteLocallyFreeSheaf X := ⟨ℬ.obj.X, hℬ⟩
  have hmod : (ObjectProperty.homMk β₁.hom.hom.hom : E_ℬ ⟶ E_𝒜) =
      ObjectProperty.homMk β₂.hom.hom.hom := by
    apply F.map_injective
    refine CoherentFormalModule.hom_ext fun n ↦ ?_
    have hn := (QuasicoherentAlgebra.pullback_map_hom_hom_hom _ β₁).symm.trans <|
      (congrArg (fun k ↦ k.hom.hom.hom) (hbn n)).trans
        (QuasicoherentAlgebra.pullback_map_hom_hom_hom _ β₂)
    exact eqToHom_conj_eq_iff
      (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) ℬ)
      (QuasicoherentAlgebra.pullback_obj_X (Scheme.formalCompletion.toScheme X I n) 𝒜)
      ((Scheme.Modules.pullback (Scheme.formalCompletion.toScheme X I n)).map β₁.hom.hom.hom)
      ((Scheme.Modules.pullback (Scheme.formalCompletion.toScheme X I n)).map β₂.hom.hom.hom) hn
  apply ObjectProperty.hom_ext
  apply CommMon.hom_ext
  exact congrArg (·.hom) hmod

/-- `Spec_X(𝒜)` bundled as a finite étale scheme over `X` with exposed underlying `Over.mk`. -/
private noncomputable def specOver (𝒜 : QuasicoherentAlgebra X)
    [IsFinite 𝒜.obj.relativeSpecToBase] [Etale 𝒜.obj.relativeSpecToBase] :
    FiniteEtaleScheme X :=
  ⟨Over.mk 𝒜.obj.relativeSpecToBase, (finiteEtaleSchemeProperty_iff _).mpr ⟨‹_›, ‹_›⟩⟩

/-- Every finite étale scheme over `X` is isomorphic in `FiniteEtaleScheme X` to `specOver 𝒜` for a
quasi-coherent `𝒪_X`-algebra `𝒜` whose underlying module is finite locally free. -/
private lemma exists_iso_specOver (Y : FiniteEtaleScheme X) :
    ∃ (𝒜 : QuasicoherentAlgebra X) (_ : IsFinite 𝒜.obj.relativeSpecToBase)
      (_ : Etale 𝒜.obj.relativeSpecToBase),
      Scheme.Modules.isFiniteLocallyFree X 𝒜.obj.X ∧
        Nonempty (specOver 𝒜 ≅ Y) := by
  let p := Y.obj.hom
  let 𝒜 : QuasicoherentAlgebra X := ⟨p.pushforwardStructureAlgebra, inferInstance⟩
  have hfin : IsFinite 𝒜.obj.relativeSpecToBase := by
    rw [← p.relativeSpecFunctionsToScheme_comp]
    infer_instance
  have het : Etale 𝒜.obj.relativeSpecToBase := by
    rw [← p.relativeSpecFunctionsToScheme_comp]
    infer_instance
  refine ⟨𝒜, hfin, het, p.isFiniteLocallyFree_pushforwardStructureAlgebra,
    ⟨ObjectProperty.isoMk _ (Over.isoMk p.relativeSpecFunctionsIso
      ((congrArg (· ≫ p) p.relativeSpecFunctionsIso_hom).trans
        p.relativeSpecFunctionsToScheme_comp))⟩⟩

private noncomputable def homOfAlgebraHom {𝒜 ℬ : QuasicoherentAlgebra X}
    [IsFinite 𝒜.obj.relativeSpecToBase] [Etale 𝒜.obj.relativeSpecToBase]
    [IsFinite ℬ.obj.relativeSpecToBase] [Etale ℬ.obj.relativeSpecToBase] (β : ℬ ⟶ 𝒜) :
    specOver 𝒜 ⟶ specOver ℬ :=
  ObjectProperty.homMk (Over.homMk (CommMon.relativeSpecMap β.hom)
    (CommMon.relativeSpecMap_relativeSpecToBase β.hom))

private lemma exists_eq_homOfAlgebraHom {𝒜 ℬ : QuasicoherentAlgebra X}
    [IsFinite 𝒜.obj.relativeSpecToBase] [Etale 𝒜.obj.relativeSpecToBase]
    [IsFinite ℬ.obj.relativeSpecToBase] [Etale ℬ.obj.relativeSpecToBase]
    (g : specOver 𝒜 ⟶ specOver ℬ) :
    ∃ β : ℬ ⟶ 𝒜, g = homOfAlgebraHom β := by
  obtain ⟨β, hβ⟩ := exists_relativeSpecMap_eq 𝒜 ℬ g.hom.left (Over.w g.hom)
  exact ⟨β, ObjectProperty.hom_ext _ (Over.OverMorphism.ext hβ.symm)⟩

/-- The canonical isomorphism between level `0` of `formalPullbackSystem I 𝒜` and the underlying
scheme of `(pullback (toScheme X I 0)).obj (specOver 𝒜)`. -/
private noncomputable def overPullbackZeroIsoFormalPullback (𝒜 : QuasicoherentAlgebra X)
    [IsFinite 𝒜.obj.relativeSpecToBase] [Etale 𝒜.obj.relativeSpecToBase] :
    (formalPullbackSystem I 𝒜).X 0 ≅
      (((pullback (Scheme.formalCompletion.toScheme X I 0)).obj (specOver 𝒜)).obj).left :=
  (isPullback_formalPullbackSystem_X I 𝒜 0).isoIsPullback _ _
    (IsPullback.of_hasPullback 𝒜.obj.relativeSpecToBase
      (Scheme.formalCompletion.toScheme X I 0)).flip

private lemma overPullbackZeroIsoFormalPullback_hom_hom (𝒜 : QuasicoherentAlgebra X)
    [IsFinite 𝒜.obj.relativeSpecToBase] [Etale 𝒜.obj.relativeSpecToBase] :
    (overPullbackZeroIsoFormalPullback I 𝒜).hom ≫
        (((pullback (Scheme.formalCompletion.toScheme X I 0)).obj (specOver 𝒜)).obj).hom =
      (formalPullbackToBase I 𝒜).app 0 :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

private lemma overPullbackZeroIsoFormalPullback_inv_toBase (𝒜 : QuasicoherentAlgebra X)
    [IsFinite 𝒜.obj.relativeSpecToBase] [Etale 𝒜.obj.relativeSpecToBase] :
    (overPullbackZeroIsoFormalPullback I 𝒜).inv ≫ (formalPullbackToBase I 𝒜).app 0 =
      (((pullback (Scheme.formalCompletion.toScheme X I 0)).obj (specOver 𝒜)).obj).hom :=
  IsPullback.isoIsPullback_inv_fst _ _ _ _

private lemma pullback_zero_homOfAlgebraHom_comm {𝒜 ℬ : QuasicoherentAlgebra X}
    [IsFinite 𝒜.obj.relativeSpecToBase] [Etale 𝒜.obj.relativeSpecToBase]
    [IsFinite ℬ.obj.relativeSpecToBase] [Etale ℬ.obj.relativeSpecToBase] (β : ℬ ⟶ 𝒜) :
    (overPullbackZeroIsoFormalPullback I 𝒜).hom ≫
      (((pullback (Scheme.formalCompletion.toScheme X I 0)).map (homOfAlgebraHom β)).hom).left ≫
        (overPullbackZeroIsoFormalPullback I ℬ).inv =
      (formalPullbackMap I β).app 0 := by
  let i₀ := Scheme.formalCompletion.toScheme X I 0
  let pA := 𝒜.obj.relativeSpecToBase
  let pB := ℬ.obj.relativeSpecToBase
  let eA := overPullbackZeroIsoFormalPullback I 𝒜
  let eB := overPullbackZeroIsoFormalPullback I ℬ
  let φ := (((pullback i₀).map (homOfAlgebraHom β)).hom).left
  have heA_snd : eA.hom ≫ Limits.pullback.fst pA i₀ = formalPullbackSndApp I 𝒜 0 :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  have heB_snd : eB.inv ≫ formalPullbackSndApp I ℬ 0 = Limits.pullback.fst pB i₀ :=
    IsPullback.isoIsPullback_inv_snd _ _ _ _
  have hmap_fst : φ ≫ Limits.pullback.fst pB i₀ =
      Limits.pullback.fst pA i₀ ≫ CommMon.relativeSpecMap β.hom :=
    Limits.pullback.lift_fst _ _ _
  apply (isPullback_formalPullbackSystem_X I ℬ 0).hom_ext
  · calc (eA.hom ≫ φ ≫ eB.inv) ≫ (formalPullbackToBase I ℬ).app 0
        = eA.hom ≫ (φ ≫ (((pullback i₀).obj (specOver ℬ)).obj).hom) :=
          (Category.assoc eA.hom _ _).trans <| congrArg (eA.hom ≫ ·) <|
            (Category.assoc φ _ _).trans
              (congrArg (φ ≫ ·) (overPullbackZeroIsoFormalPullback_inv_toBase I ℬ))
      _ = eA.hom ≫ (((pullback i₀).obj (specOver 𝒜)).obj).hom :=
          congrArg (eA.hom ≫ ·) (Over.w (((pullback i₀).map (homOfAlgebraHom β)).hom))
      _ = (formalPullbackToBase I 𝒜).app 0 := overPullbackZeroIsoFormalPullback_hom_hom I 𝒜
      _ = (formalPullbackMap I β).app 0 ≫ (formalPullbackToBase I ℬ).app 0 :=
          (congrArg (fun k ↦ k.app 0) (formalPullbackMap_comp_toBase I β)).symm
  · calc (eA.hom ≫ φ ≫ eB.inv) ≫ formalPullbackSndApp I ℬ 0
        = eA.hom ≫ (φ ≫ Limits.pullback.fst pB i₀) :=
          (Category.assoc eA.hom _ _).trans <| congrArg (eA.hom ≫ ·) <|
            (Category.assoc φ _ _).trans (congrArg (φ ≫ ·) heB_snd)
      _ = eA.hom ≫ (Limits.pullback.fst pA i₀ ≫ CommMon.relativeSpecMap β.hom) :=
          congrArg (eA.hom ≫ ·) hmap_fst
      _ = (eA.hom ≫ Limits.pullback.fst pA i₀) ≫ CommMon.relativeSpecMap β.hom :=
          (Category.assoc eA.hom (Limits.pullback.fst pA i₀) (CommMon.relativeSpecMap β.hom)).symm
      _ = formalPullbackSndApp I 𝒜 0 ≫ CommMon.relativeSpecMap β.hom :=
          congrArg (· ≫ CommMon.relativeSpecMap β.hom) heA_snd
      _ = (formalPullbackMap I β).app 0 ≫ formalPullbackSndApp I ℬ 0 :=
          (formalPullbackMap_app_comp_sndApp I β 0).symm

attribute [irreducible] overPullbackZeroIsoFormalPullback specOver homOfAlgebraHom

private lemma hom_left_eq_of_eq {S : Scheme.{u}} {U V : FiniteEtaleScheme S}
    {φ₁ φ₂ : U ⟶ V} (h : φ₁ = φ₂) : φ₁.hom.left = φ₂.hom.left :=
  congrArg (fun φ ↦ φ.hom.left) h

private lemma eq_of_iso_conj_eq {C : Type*} [Category* C] {A A' B B' : C}
    (eA : A ≅ A') (eB : B ≅ B') {f₁ f₂ : A' ⟶ B'} {a₁ a₂ : A ⟶ B}
    (ha₁ : eA.hom ≫ f₁ ≫ eB.inv = a₁) (ha₂ : eA.hom ≫ f₂ ≫ eB.inv = a₂)
    (hf : f₁ = f₂) : a₁ = a₂ := by
  rw [← ha₁, ← ha₂, hf]

private lemma formalPullbackMap_app_zero_eq_of_pullback_eq {𝒜 ℬ : QuasicoherentAlgebra X}
    [IsFinite 𝒜.obj.relativeSpecToBase] [Etale 𝒜.obj.relativeSpecToBase]
    [IsFinite ℬ.obj.relativeSpecToBase] [Etale ℬ.obj.relativeSpecToBase]
    {β₁ β₂ : ℬ ⟶ 𝒜}
    (h : (pullback (Scheme.formalCompletion.toScheme X I 0)).map (homOfAlgebraHom β₁) =
      (pullback (Scheme.formalCompletion.toScheme X I 0)).map (homOfAlgebraHom β₂)) :
    (formalPullbackMap I β₁).app 0 = (formalPullbackMap I β₂).app 0 :=
  eq_of_iso_conj_eq
    (overPullbackZeroIsoFormalPullback I 𝒜)
    (overPullbackZeroIsoFormalPullback I ℬ)
    (pullback_zero_homOfAlgebraHom_comm I β₁)
    (pullback_zero_homOfAlgebraHom_comm I β₂)
    (hom_left_eq_of_eq h)

private lemma map_eq_of_eq {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {X₁ X₂ : C} {g₁ g₂ f₁ f₂ : X₁ ⟶ X₂}
    (hg₁ : g₁ = f₁) (hg₂ : g₂ = f₂) (h : G.map g₁ = G.map g₂) :
    G.map f₁ = G.map f₂ := by
  rw [← hg₁, ← hg₂, h]

private lemma injective_pullback_toScheme_zero_specOver {𝒜 ℬ : QuasicoherentAlgebra X}
    [IsFinite 𝒜.obj.relativeSpecToBase] [Etale 𝒜.obj.relativeSpecToBase]
    [IsFinite ℬ.obj.relativeSpecToBase] [Etale ℬ.obj.relativeSpecToBase]
    (h𝒜 : Scheme.Modules.isFiniteLocallyFree X 𝒜.obj.X)
    (hℬ : Scheme.Modules.isFiniteLocallyFree X ℬ.obj.X)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    Function.Injective (fun g : specOver 𝒜 ⟶ specOver ℬ ↦
      (pullback (Scheme.formalCompletion.toScheme X I 0)).map g) := by
  intro g₁ g₂ hg
  obtain ⟨β₁, hg₁⟩ := exists_eq_homOfAlgebraHom g₁
  obtain ⟨β₂, hg₂⟩ := exists_eq_homOfAlgebraHom g₂
  have ha₀ : (formalPullbackMap I β₁).app 0 = (formalPullbackMap I β₂).app 0 :=
    formalPullbackMap_app_zero_eq_of_pullback_eq I
      (map_eq_of_eq (pullback (Scheme.formalCompletion.toScheme X I 0)) hg₁ hg₂ hg)
  have ha : formalPullbackMap I β₁ = formalPullbackMap I β₂ :=
    AdicThickeningSystem.hom_ext_of_formallyUnramified (formalPullbackToBase I ℬ)
      ((formalPullbackMap_comp_toBase I β₁).trans (formalPullbackMap_comp_toBase I β₂).symm) ha₀
  have hbn (n : ℕ) :
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).map β₁ =
        (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).map β₂ :=
    relativeSpecMap_injective <| (cancel_mono (levelSpecIsoFormalPullback I ℬ n).hom).mp <|
      (levelSpecIso_hom_formalPullbackMap_app I β₁ n).symm.trans <|
        (congrArg (fun k ↦ (levelSpecIsoFormalPullback I 𝒜 n).hom ≫ k.app n) ha).trans
          (levelSpecIso_hom_formalPullbackMap_app I β₂ n)
  have hβ : β₁ = β₂ := algebraHom_eq_of_forall_level I h𝒜 hℬ hbn
  exact hg₁.trans ((congrArg homOfAlgebraHom hβ).trans hg₂.symm)

private lemma conj_iso_over_base {C : Type*} [Category* C] {A' A B' B S : C}
    (eA : A' ≅ A) (eB : B' ≅ B) (f : A ⟶ B) (pA : A ⟶ S) (pB : B ⟶ S)
    (pA' : A' ⟶ S) (pB' : B' ⟶ S)
    (hf : f ≫ pB = pA) (heA : eA.hom ≫ pA = pA') (heB : eB.hom ≫ pB = pB') :
    (eA.hom ≫ f ≫ eB.inv) ≫ pB' = pA' := by
  simp [← heB, ← heA, hf]

private lemma conj_iso_comm_sq {C : Type*} [Category* C]
    {A₀' A₀ A₁' A₁ B₀' B₀ B₁' B₁ : C}
    (eA₀ : A₀' ≅ A₀) (eA₁ : A₁' ≅ A₁) (eB₀ : B₀' ≅ B₀) (eB₁ : B₁' ≅ B₁)
    (tA : A₀' ⟶ A₁') (tB : B₀' ⟶ B₁') (ιA : A₀ ⟶ A₁) (ιB : B₀ ⟶ B₁)
    (a₀ : A₀ ⟶ B₀) (a₁ : A₁ ⟶ B₁) (s₀ : A₀' ⟶ B₀') (s₁ : A₁' ⟶ B₁')
    (hs₀ : s₀ = eA₀.hom ≫ a₀ ≫ eB₀.inv) (hs₁ : s₁ = eA₁.hom ≫ a₁ ≫ eB₁.inv)
    (htA : tA ≫ eA₁.hom = eA₀.hom ≫ ιA) (htB : tB ≫ eB₁.hom = eB₀.hom ≫ ιB)
    (ha : ιA ≫ a₁ = a₀ ≫ ιB) :
    tA ≫ s₁ = s₀ ≫ tB := by
  apply (cancel_mono eB₁.hom).mp
  simp [hs₀, hs₁, reassoc_of% htA, htB, reassoc_of% ha]

/-- Translates a morphism `formalPullbackSystem I 𝒜 ⟶ formalPullbackSystem I ℬ` over
`X.formalCompletion I` into a compatible family of levelwise algebra homomorphisms via the
relative-spectrum anti-equivalence at each level. -/
private lemma exists_levelAlgebraHoms_of_formalPullbackHom {𝒜 ℬ : QuasicoherentAlgebra X}
    (a : formalPullbackSystem I 𝒜 ⟶ formalPullbackSystem I ℬ)
    (ha_base : a ≫ formalPullbackToBase I ℬ = formalPullbackToBase I 𝒜) :
    ∃ b : ∀ n, (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj ℬ ⟶
        (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj 𝒜,
      (∀ n, CommMon.relativeSpecMap (b n).hom =
        (levelSpecIsoFormalPullback I 𝒜 n).hom ≫ a.app n ≫
          (levelSpecIsoFormalPullback I ℬ n).inv) ∧
      (∀ n, (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (b (n + 1)) ≫
          (levelAlgTransitionNatIso I n).hom.app 𝒜 =
        (levelAlgTransitionNatIso I n).hom.app ℬ ≫ b n) := by
  have hu_base (n : ℕ) :
      ((levelSpecIsoFormalPullback I 𝒜 n).hom ≫ a.app n ≫
          (levelSpecIsoFormalPullback I ℬ n).inv) ≫
        ((QuasicoherentAlgebra.pullback
          (Scheme.formalCompletion.toScheme X I n)).obj ℬ).obj.relativeSpecToBase =
        ((QuasicoherentAlgebra.pullback
          (Scheme.formalCompletion.toScheme X I n)).obj 𝒜).obj.relativeSpecToBase :=
    conj_iso_over_base
      (levelSpecIsoFormalPullback I 𝒜 n) (levelSpecIsoFormalPullback I ℬ n)
      (a.app n) ((formalPullbackToBase I 𝒜).app n) ((formalPullbackToBase I ℬ).app n) _ _
      (congrArg (fun k ↦ k.app n) ha_base)
      (levelSpecIsoFormalPullback_hom_fst I 𝒜 n) (levelSpecIsoFormalPullback_hom_fst I ℬ n)
  choose b hb_spec using fun n ↦
    exists_relativeSpecMap_eq
      ((QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj 𝒜)
      ((QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj ℬ)
      ((levelSpecIsoFormalPullback I 𝒜 n).hom ≫ a.app n ≫
        (levelSpecIsoFormalPullback I ℬ n).inv)
      (hu_base n)
  refine ⟨b, hb_spec, fun n ↦ (levelSpecTransition_compatible_iff I b n).mp ?_⟩
  exact conj_iso_comm_sq
    (levelSpecIsoFormalPullback I 𝒜 n) (levelSpecIsoFormalPullback I 𝒜 (n + 1))
    (levelSpecIsoFormalPullback I ℬ n) (levelSpecIsoFormalPullback I ℬ (n + 1))
    (levelSpecTransition I 𝒜 n) (levelSpecTransition I ℬ n)
    ((formalPullbackSystem I 𝒜).ι n) ((formalPullbackSystem I ℬ).ι n)
    (a.app n) (a.app (n + 1))
    (CommMon.relativeSpecMap (b n).hom) (CommMon.relativeSpecMap (b (n + 1)).hom)
    (hb_spec n) (hb_spec (n + 1))
    (levelSpecTransition_comp_iso I 𝒜 n) (levelSpecTransition_comp_iso I ℬ n)
    (a.naturality n)

private lemma surjective_pullback_toScheme_zero_specOver {𝒜 ℬ : QuasicoherentAlgebra X}
    [IsFinite 𝒜.obj.relativeSpecToBase] [Etale 𝒜.obj.relativeSpecToBase]
    [IsFinite ℬ.obj.relativeSpecToBase] [Etale ℬ.obj.relativeSpecToBase]
    (h𝒜 : Scheme.Modules.isFiniteLocallyFree X 𝒜.obj.X)
    (hℬ : Scheme.Modules.isFiniteLocallyFree X ℬ.obj.X)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    Function.Surjective (fun g : specOver 𝒜 ⟶ specOver ℬ ↦
      (pullback (Scheme.formalCompletion.toScheme X I 0)).map g) := by
  intro φ₀
  let eA := overPullbackZeroIsoFormalPullback I 𝒜
  let eB := overPullbackZeroIsoFormalPullback I ℬ
  let a₀ : (formalPullbackSystem I 𝒜).X 0 ⟶ (formalPullbackSystem I ℬ).X 0 :=
    eA.hom ≫ φ₀.hom.left ≫ eB.inv
  have ha₀ : a₀ ≫ (formalPullbackToBase I ℬ).app 0 = (formalPullbackToBase I 𝒜).app 0 := by
    calc (eA.hom ≫ φ₀.hom.left ≫ eB.inv) ≫ (formalPullbackToBase I ℬ).app 0
        = eA.hom ≫ (φ₀.hom.left ≫ (eB.inv ≫ (formalPullbackToBase I ℬ).app 0)) := by
          simp only [Category.assoc]
      _ = eA.hom ≫ (φ₀.hom.left ≫
            (((pullback (Scheme.formalCompletion.toScheme X I 0)).obj (specOver ℬ)).obj).hom) := by
          rw [overPullbackZeroIsoFormalPullback_inv_toBase]
      _ = eA.hom ≫
            (((pullback (Scheme.formalCompletion.toScheme X I 0)).obj (specOver 𝒜)).obj).hom := by
          rw [Over.w φ₀.hom]
      _ = (formalPullbackToBase I 𝒜).app 0 :=
          overPullbackZeroIsoFormalPullback_hom_hom I 𝒜
  let a := AdicThickeningSystem.liftOfEtale (formalPullbackToBase I 𝒜)
    (formalPullbackToBase I ℬ) a₀ ha₀
  obtain ⟨b, hb_spec, hb_compat⟩ := exists_levelAlgebraHoms_of_formalPullbackHom I a
    (AdicThickeningSystem.liftOfEtale_comp _ _ a₀ ha₀)
  obtain ⟨β, hβ⟩ := exists_algebraHom_of_levelAlgebraHoms I h𝒜 hℬ b hb_compat
  refine ⟨homOfAlgebraHom β, ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)⟩
  have h0 : (formalPullbackMap I β).app 0 = a₀ := by
    refine (cancel_epi (levelSpecIsoFormalPullback I 𝒜 0).hom).mp ?_
    calc (levelSpecIsoFormalPullback I 𝒜 0).hom ≫ (formalPullbackMap I β).app 0
        = CommMon.relativeSpecMap
              ((QuasicoherentAlgebra.pullback
                (Scheme.formalCompletion.toScheme X I 0)).map β).hom ≫
            (levelSpecIsoFormalPullback I ℬ 0).hom :=
          levelSpecIso_hom_formalPullbackMap_app I β 0
      _ = ((levelSpecIsoFormalPullback I 𝒜 0).hom ≫ a.app 0 ≫
            (levelSpecIsoFormalPullback I ℬ 0).inv) ≫
            (levelSpecIsoFormalPullback I ℬ 0).hom :=
          congrArg (· ≫ _) ((congrArg (fun k ↦ CommMon.relativeSpecMap k.hom) (hβ 0)).trans
            (hb_spec 0))
      _ = (levelSpecIsoFormalPullback I 𝒜 0).hom ≫ a.app 0 := by
          simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = (levelSpecIsoFormalPullback I 𝒜 0).hom ≫ a₀ :=
          congrArg ((levelSpecIsoFormalPullback I 𝒜 0).hom ≫ ·)
            (AdicThickeningSystem.liftOfEtale_app_zero _ _ a₀ ha₀)
  have hsymm := (Iso.cancel_iso_hom_left _ _ _).mp
    ((pullback_zero_homOfAlgebraHom_comm I β).trans h0)
  exact (Iso.cancel_iso_inv_right _ _ _).mp hsymm

end Helpers

/-- **Faithfulness of finite étale pullback from formal completion.** Let `i : Z ⟶ X` be a closed
immersion with ideal sheaf `I`. If the completion functor along `I` is faithful on finite locally
free `𝒪_X`-modules, then base change of finite étale schemes along `i` is faithful. -/
theorem faithful_pullback_of_completion {X Z : Scheme.{u}} {I : X.IdealSheafData} (i : Z ⟶ X)
    [IsClosedImmersion i] (hi : i.ker = I)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback i).Faithful := by
  let i₀ := Scheme.formalCompletion.toScheme X I 0
  have h₀ : (pullback i₀).Faithful := by
    refine ⟨fun {Y₁ Y₂} f₁ f₂ hf ↦ ?_⟩
    obtain ⟨𝒜, _, _, h𝒜, ⟨e₁⟩⟩ := exists_iso_specOver Y₁
    obtain ⟨ℬ, _, _, hℬ, ⟨e₂⟩⟩ := exists_iso_specOver Y₂
    have hinj := injective_pullback_toScheme_zero_specOver I h𝒜 hℬ
    have hconj : e₁.hom ≫ f₁ ≫ e₂.inv = e₁.hom ≫ f₂ ≫ e₂.inv := by
      apply hinj
      simp only [Functor.map_comp]
      rw [reassoc_of% hf]
    simpa only [Iso.cancel_iso_hom_left, Iso.cancel_iso_inv_right] using hconj
  have hker : i₀.ker = i.ker := by
    rw [Scheme.formalCompletion.ker_toScheme, zero_add, pow_one, hi]
  have := IsClosedImmersion.isIso_lift i₀ i hker
  let ζ : Z ≅ (X.formalCompletion I).X 0 := asIso (IsClosedImmersion.lift i₀ i hker.le)
  have hζ : ζ.inv ≫ i = i₀ := by
    rw [Iso.inv_comp_eq]
    exact (IsClosedImmersion.lift_fac i₀ i hker.le).symm
  have : (pullback i ⋙ pullback ζ.inv).Faithful :=
    Functor.Faithful.of_iso (eqToIso (congrArg pullback hζ.symm) ≪≫ pullbackComp ζ.inv i)
  exact Functor.Faithful.of_comp (pullback i) (pullback ζ.inv)

private lemma map_inv_comp_comp_hom {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X₁ X₂ Y₁ Y₂ : C} (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (g : X₁ ⟶ X₂) (φ : F.obj Y₁ ⟶ F.obj Y₂)
    (hg : F.map g = F.map e₁.hom ≫ φ ≫ F.map e₂.inv) :
    F.map (e₁.inv ≫ g ≫ e₂.hom) = φ := by
  simp [hg, ← F.map_comp]

/-- **Fullness of finite étale pullback from formal completion.** Let `i : Z ⟶ X` be a closed
immersion with ideal sheaf `I`. If the completion functor along `I` is full and faithful on finite
locally free `𝒪_X`-modules, then base change of finite étale schemes along `i` is full. -/
theorem full_pullback_of_completion {X Z : Scheme.{u}} {I : X.IdealSheafData} (i : Z ⟶ X)
    [IsClosedImmersion i] (hi : i.ker = I)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback i).Full := by
  let i₀ := Scheme.formalCompletion.toScheme X I 0
  have h₀ : (pullback i₀).Full :=
    { map_surjective := fun {Y₁ Y₂} φ₀ ↦ by
        obtain ⟨𝒜, _, _, h𝒜, ⟨e₁⟩⟩ := exists_iso_specOver Y₁
        obtain ⟨ℬ, _, _, hℬ, ⟨e₂⟩⟩ := exists_iso_specOver Y₂
        obtain ⟨g, hg⟩ := surjective_pullback_toScheme_zero_specOver I h𝒜 hℬ
          ((pullback i₀).map e₁.hom ≫ φ₀ ≫ (pullback i₀).map e₂.inv)
        exact ⟨e₁.inv ≫ g ≫ e₂.hom, map_inv_comp_comp_hom (pullback i₀) e₁ e₂ g φ₀ hg⟩ }
  have hker : i₀.ker = i.ker := by
    rw [Scheme.formalCompletion.ker_toScheme, zero_add, pow_one, hi]
  have := IsClosedImmersion.isIso_lift i₀ i hker
  let ζ : Z ≅ (X.formalCompletion I).X 0 := asIso (IsClosedImmersion.lift i₀ i hker.le)
  have hζ : ζ.hom ≫ i₀ = i := IsClosedImmersion.lift_fac i₀ i hker.le
  have eEquiv : pullback ζ.hom ⋙ pullback ζ.inv ≅ 𝟭 _ :=
    (pullbackComp ζ.inv ζ.hom).symm ≪≫ eqToIso (congrArg pullback ζ.inv_hom_id) ≪≫ pullbackId
  have eEquiv' : pullback ζ.inv ⋙ pullback ζ.hom ≅ 𝟭 _ :=
    (pullbackComp ζ.hom ζ.inv).symm ≪≫ eqToIso (congrArg pullback ζ.hom_inv_id) ≪≫ pullbackId
  have : (pullback ζ.hom).Full :=
    (CategoryTheory.Equivalence.mk (pullback ζ.hom) (pullback ζ.inv)
      eEquiv.symm eEquiv').full_functor
  exact Functor.Full.of_iso ((pullbackComp ζ.hom i₀).symm ≪≫ eqToIso (congrArg pullback hζ))

/-- **Full faithfulness of finite étale pullback from formal completion** (Stacks, Lemma 58.17.1).
Let `i : Z ⟶ X` be a closed immersion with ideal sheaf `I`. If the completion functor along `I` is
full and faithful on finite locally free `𝒪_X`-modules, then base change of finite étale schemes
along `i` is fully faithful. -/
@[stacks 0EL8]
noncomputable def fullyFaithfulPullbackOfCompletion {X Z : Scheme.{u}} {I : X.IdealSheafData}
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : i.ker = I)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback i).FullyFaithful :=
  have := faithful_pullback_of_completion i hi
  have := full_pullback_of_completion i hi
  .ofFullyFaithful _

section Subscheme

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- Base change of finite étale schemes along `I.subschemeι : V(I) ⟶ X` is faithful when formal
completion along `I` is faithful on finite locally free `𝒪_X`-modules. -/
instance faithful_pullback_subschemeι
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Faithful :=
  faithful_pullback_of_completion I.subschemeι (Scheme.IdealSheafData.ker_subschemeι I)

/-- Base change of finite étale schemes along `I.subschemeι : V(I) ⟶ X` is full when formal
completion along `I` is full and faithful on finite locally free `𝒪_X`-modules. -/
instance full_pullback_subschemeι
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Full :=
  full_pullback_of_completion I.subschemeι (Scheme.IdealSheafData.ker_subschemeι I)

/-- **Full faithfulness of finite étale restriction to `V(I)` from formal completion**
(Stacks, Lemma 58.17.1). -/
@[stacks 0EL8]
noncomputable def fullyFaithfulPullbackSubschemeι
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).FullyFaithful :=
  fullyFaithfulPullbackOfCompletion I.subschemeι (Scheme.IdealSheafData.ker_subschemeι I)

/-- Base change of finite étale schemes to the initial level `V(I ^ 1)` of `X.formalCompletion I`
is faithful when formal completion along `I` is faithful on finite locally free `𝒪_X`-modules. -/
instance faithful_pullback_toScheme_zero
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback (Scheme.formalCompletion.toScheme X I 0)).Faithful :=
  faithful_pullback_of_completion (Scheme.formalCompletion.toScheme X I 0)
    (by rw [Scheme.formalCompletion.ker_toScheme, zero_add, pow_one])

/-- Base change of finite étale schemes to the initial level `V(I ^ 1)` of `X.formalCompletion I`
is full when formal completion along `I` is full and faithful on finite locally free
`𝒪_X`-modules. -/
instance full_pullback_toScheme_zero
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback (Scheme.formalCompletion.toScheme X I 0)).Full :=
  full_pullback_of_completion (Scheme.formalCompletion.toScheme X I 0)
    (by rw [Scheme.formalCompletion.ker_toScheme, zero_add, pow_one])

/-- Base change of finite étale schemes to the initial level `V(I ^ 1)` of `X.formalCompletion I`
is fully faithful when formal completion along `I` is full and faithful on finite locally free
`𝒪_X`-modules. -/
noncomputable def fullyFaithfulPullbackToSchemeZero
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback (Scheme.formalCompletion.toScheme X I 0)).FullyFaithful :=
  .ofFullyFaithful _

end Subscheme

end TauCeti.FiniteEtaleScheme
