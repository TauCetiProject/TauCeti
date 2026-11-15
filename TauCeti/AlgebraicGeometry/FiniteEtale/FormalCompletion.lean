/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Basic
public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Etale
import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Pullback
import TauCeti.AlgebraicGeometry.RelativeSpec.BaseChange
import TauCeti.AlgebraicGeometry.RelativeSpec.Equivalence
import TauCeti.AlgebraicGeometry.VectorBundle.Pushforward

/-!
# Full faithfulness of finite étale base change from formal completion

Let `X` be a scheme and `I` an ideal sheaf on `X`, cutting out the closed subscheme
`i : V(I) ⟶ X` (`I.subschemeι`) with formal completion `X.formalCompletion I` = `(V(I ^ (n + 1)))`.
When the completion functor on finite locally free `𝒪_X`-modules
`FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙ Scheme.formalCompletion.completionFunctor X I` is
fully faithful — in particular, when `Scheme.formalCompletion.completionFunctor X I` itself is
fully faithful on all finitely presented `𝒪_X`-modules — base change of finite étale schemes
`TauCeti.FiniteEtaleScheme.pullback I.subschemeι : FiniteEtaleScheme X ⥤ FiniteEtaleScheme V(I)` is
fully faithful (Stacks, Lemma 58.17.1 (0EL8) and Remark 58.17.2 (0EL9)). Moreover, faithfulness of
the completion functor on finite locally free sheaves alone already implies faithfulness of
`pullback I.subschemeι`.

The proof combines three ingredients:

1. **Coordinate algebras as finite locally free sheaves.** Every finite étale scheme `p : V ⟶ X` is
   affine, finite, flat, and locally of finite presentation over `X`, so `V` is canonically
   isomorphic to the relative spectrum `Spec_X (p_* 𝒪_V)` (`Scheme.Hom.relativeSpecFunctionsIso`) of
   its coordinate algebra `p_* 𝒪_V`, whose underlying `𝒪_X`-module is finite locally free
   (`Scheme.Modules.isFiniteLocallyFree_pushforward_unit`).
2. **Infinitesimal lifting on adic thickening systems.** Pulling back the canonical map from
   `X.formalCompletion I` to the constant system `AdicThickeningSystem.ofScheme.obj X` along the
   adic morphism induced by `Spec_X A ⟶ X` produces an adic thickening system `𝔙(A)` over
   `X.formalCompletion I` whose `n`-th level is canonically isomorphic to `Spec_{X_n} (i_n^* A)` via
   base change of relative spectra (`isPullback_relativeSpecPullbackFst`). When `Spec_X B ⟶ X` is
   étale, `𝔙(B) ⟶ X.formalCompletion I` is levelwise étale, so a morphism on level `0` extends
   uniquely to all infinitesimal levels (`AdicThickeningSystem.liftOfEtale`,
   `AdicThickeningSystem.hom_ext_of_formallyUnramified`) and hence by the relative-Spec
   anti-equivalence (`relativeSpecEquiv`) to a compatible system of algebra homomorphisms
   `i_n^* B ⟶ i_n^* A`.
3. **Descent of algebra homomorphisms from finite locally free modules.** On underlying modules, a
   compatible family of algebra homomorphisms `i_n^* B ⟶ i_n^* A` defines a morphism in
   `CoherentFormalModule (X.formalCompletion I)` between the completions of `B` and `A`. Fullness
   lifts this to a module map `φ : B ⟶ A` on `X`, and faithfulness on the finite locally free
   sheaves `𝒪_X` and `B ⊗ B` shows that `φ` respects the unit and multiplication, yielding an
   algebra map `B ⟶ A` whose relative spectrum map induces the given morphism over `V(I)`.

Note that no Noetherian hypothesis on `X` or finite-type hypothesis on `I` is needed once full
faithfulness of the completion functor on finite locally free sheaves is given; those finiteness
hypotheses enter only when establishing that module-level full faithfulness from local cohomology or
Grothendieck's existence theorem.

## Main declarations

* `FiniteEtaleScheme.faithful_pullback_subschemeι_of_toFinitelyPresented_comp_completionFunctor`:
  faithfulness of `pullback I.subschemeι` from faithfulness of formal completion on
  `FiniteLocallyFreeSheaf X`;
* `FiniteEtaleScheme.faithful_pullback_subschemeι_of_completionFunctor`: faithfulness of
  `pullback I.subschemeι` from faithfulness of `Scheme.formalCompletion.completionFunctor X I`;
* `FiniteEtaleScheme.full_pullback_subschemeι_of_toFinitelyPresented_comp_completionFunctor` and
  `FiniteEtaleScheme.fullyFaithfulPullbackSubschemeιOfToFinitelyPresentedCompCompletionFunctor`:
  fullness and bundled full faithfulness from full faithfulness on `FiniteLocallyFreeSheaf X`
  (Stacks Tag 0EL9);
* `FiniteEtaleScheme.full_pullback_subschemeι_of_completionFunctor` and
  `FiniteEtaleScheme.fullyFaithfulPullbackSubschemeιOfCompletionFunctor`: fullness and bundled full
  faithfulness from full faithfulness on `FinitelyPresentedSheaf X` (Stacks Tag 0EL8).

## References

* [The Stacks Project, Lemma 58.17.1](https://stacks.math.columbia.edu/tag/0EL8)
* [The Stacks Project, Remark 58.17.2](https://stacks.math.columbia.edu/tag/0EL9)
* [The Stacks Project, Theorem 59.45.2](https://stacks.math.columbia.edu/tag/04DZ)
* [The Stacks Project, Lemma 29.48.2](https://stacks.math.columbia.edu/tag/02KB)
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Opposite AlgebraicGeometry
open scoped MonObj

universe u

namespace TauCeti.FiniteEtaleScheme

open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.AdicThickeningSystem

/-! ### Level-zero closed immersion comparison -/

/-- Natural isomorphism between finite étale pullback functors along equal morphisms. -/
private def pullbackCongr {S T : Scheme.{u}} {f g : T ⟶ S} (h : f = g) :
    pullback f ≅ pullback g :=
  eqToIso (congrArg pullback h)

/-- Base change of finite étale schemes along an isomorphism is faithful. -/
private lemma faithful_pullback_of_isIso {S T : Scheme.{u}} (g : T ⟶ S) [IsIso g] :
    (pullback g).Faithful :=
  Functor.Faithful.of_comp_iso
    ((pullbackComp (inv g) g).symm ≪≫ pullbackCongr (IsIso.inv_hom_id g) ≪≫ pullbackId)

/-- Base change of finite étale schemes along an isomorphism is full. -/
private lemma full_pullback_of_isIso {S T : Scheme.{u}} (g : T ⟶ S) [IsIso g] :
    (pullback g).Full := by
  have := faithful_pullback_of_isIso (inv g)
  exact Functor.Full.of_comp_faithful_iso
    ((pullbackComp (inv g) g).symm ≪≫ pullbackCongr (IsIso.inv_hom_id g) ≪≫ pullbackId)

/-- The canonical isomorphism `V(I) ≅ V(I ^ 1)` with the `0`-th level of `X.formalCompletion I`. -/
private def subschemeIsoZero (X : Scheme.{u}) (I : X.IdealSheafData) :
    I.subscheme ≅ (X.formalCompletion I).X 0 where
  hom := Scheme.IdealSheafData.inclusion (pow_one I).le
  inv := Scheme.IdealSheafData.inclusion (pow_one I).ge
  hom_inv_id :=
    (Scheme.IdealSheafData.inclusion_comp _ _).trans (Scheme.IdealSheafData.inclusion_id _)
  inv_hom_id :=
    (Scheme.IdealSheafData.inclusion_comp _ _).trans (Scheme.IdealSheafData.inclusion_id _)

private lemma subschemeIsoZero_hom_toScheme (X : Scheme.{u}) (I : X.IdealSheafData) :
    (subschemeIsoZero X I).hom ≫ Scheme.formalCompletion.toScheme X I 0 = I.subschemeι := by
  rw [Scheme.formalCompletion.toScheme_def]
  exact Scheme.IdealSheafData.inclusion_subschemeι (pow_one I).le

/-- Pullback along `I.subschemeι` factors through pullback along level `0` of the formal completion
followed by pullback along the isomorphism `subschemeIsoZero X I`. -/
private def pullbackSubschemeιIso (X : Scheme.{u}) (I : X.IdealSheafData) :
    pullback I.subschemeι ≅
      pullback (Scheme.formalCompletion.toScheme X I 0) ⋙
        pullback (subschemeIsoZero X I).hom :=
  pullbackCongr (subschemeIsoZero_hom_toScheme X I).symm ≪≫
    pullbackComp (subschemeIsoZero X I).hom (Scheme.formalCompletion.toScheme X I 0)

private lemma faithful_pullback_subschemeι_of_zero {X : Scheme.{u}} {I : X.IdealSheafData}
    [(pullback (Scheme.formalCompletion.toScheme X I 0)).Faithful] :
    (pullback I.subschemeι).Faithful := by
  have := faithful_pullback_of_isIso (subschemeIsoZero X I).hom
  exact Functor.Faithful.of_iso (pullbackSubschemeιIso X I).symm

private lemma full_pullback_subschemeι_of_zero {X : Scheme.{u}} {I : X.IdealSheafData}
    [(pullback (Scheme.formalCompletion.toScheme X I 0)).Full] :
    (pullback I.subschemeι).Full := by
  have := full_pullback_of_isIso (subschemeIsoZero X I).hom
  exact Functor.Full.of_iso (pullbackSubschemeιIso X I).symm

/-! ### Module-level `eqToHom` helpers avoiding `QuasicoherentAlgebra` unfolding -/

private lemma modules_conjugate_eq_iff {Y : Scheme.{u}} {P P' Q Q' : Y.Modules}
    (eP : P = P') (eQ : Q = Q') (u v : P' ⟶ Q') :
    eqToHom eP ≫ u ≫ eqToHom eQ.symm = eqToHom eP ≫ v ≫ eqToHom eQ.symm ↔ u = v := by
  subst eP eQ
  simp

private lemma modules_conjugate_cancel {Y : Scheme.{u}} {P P' Q Q' : Y.Modules}
    (eP : P = P') (eQ : Q = Q') (α : P ⟶ Q) :
    eqToHom eP ≫ (eqToHom eP.symm ≫ α ≫ eqToHom eQ) ≫ eqToHom eQ.symm = α := by
  subst eP eQ
  simp

private lemma pullback_one_aux {X Y : Scheme.{u}} (f : Y ⟶ X) {MB MA : X.Modules}
    [MonObj MB] [MonObj MA] {PB PA : Y.Modules}
    (eB : PB = (Scheme.Modules.pullback f).obj MB)
    (eA : PA = (Scheme.Modules.pullback f).obj MA)
    (φ : MB ⟶ MA) (α : PB ⟶ PA)
    (hα : ((Scheme.Modules.pullbackObjUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map η[MB] ≫ eqToHom eB.symm) ≫ α =
      (Scheme.Modules.pullbackObjUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map η[MA] ≫ eqToHom eA.symm)
    (hφ : (Scheme.Modules.pullback f).map φ = eqToHom eB.symm ≫ α ≫ eqToHom eA) :
    (Scheme.Modules.pullback f).map (η[MB] ≫ φ) = (Scheme.Modules.pullback f).map η[MA] := by
  subst eB eA
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp, Category.assoc, cancel_epi] at hα hφ
  rw [Functor.map_comp, hφ, hα]

private lemma pullback_mul_aux {X Y : Scheme.{u}} (f : Y ⟶ X) {MB MA : X.Modules}
    [MonObj MB] [MonObj MA]
    [IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) MB MB)]
    [IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) MA MA)]
    {PB PA : Y.Modules}
    (eB : PB = (Scheme.Modules.pullback f).obj MB)
    (eA : PA = (Scheme.Modules.pullback f).obj MA)
    (φ : MB ⟶ MA) (α : PB ⟶ PA)
    (hα : ((eqToHom eB ⊗ₘ eqToHom eB) ≫
        inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) MB MB) ≫
        (Scheme.Modules.pullback f).map μ[MB] ≫ eqToHom eB.symm) ≫ α =
      (α ⊗ₘ α) ≫ (eqToHom eA ⊗ₘ eqToHom eA) ≫
        inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) MA MA) ≫
        (Scheme.Modules.pullback f).map μ[MA] ≫ eqToHom eA.symm)
    (hφ : (Scheme.Modules.pullback f).map φ = eqToHom eB.symm ≫ α ≫ eqToHom eA) :
    (Scheme.Modules.pullback f).map (μ[MB] ≫ φ) =
      (Scheme.Modules.pullback f).map ((φ ⊗ₘ φ) ≫ μ[MA]) := by
  subst eB eA
  simp only [eqToHom_refl, id_tensorHom_id, Category.id_comp, Category.comp_id,
    Category.assoc] at hα hφ
  rw [← hφ] at hα
  have h := congrArg (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) MB MB ≫ ·) hα
  simpa only [IsIso.hom_inv_id_assoc, Functor.OplaxMonoidal.δ_natural_assoc,
    Functor.map_comp] using h

private lemma coherentFormalModule_naturality_aux {X Y Z : Scheme.{u}}
    (g : Z ⟶ Y) (f : Y ⟶ X) (k : Z ⟶ X) (hk : g ≫ f = k) {MB MA : X.Modules}
    {PB₁ PA₁ : Y.Modules} {PB₀ PA₀ PBG PAG : Z.Modules}
    (eB₁ : PB₁ = (Scheme.Modules.pullback f).obj MB)
    (eA₁ : PA₁ = (Scheme.Modules.pullback f).obj MA)
    (eB₀ : PB₀ = (Scheme.Modules.pullback k).obj MB)
    (eA₀ : PA₀ = (Scheme.Modules.pullback k).obj MA)
    (eBG : PBG = (Scheme.Modules.pullback g).obj PB₁)
    (eAG : PAG = (Scheme.Modules.pullback g).obj PA₁)
    (α₁ : PB₁ ⟶ PA₁) (α₀ : PB₀ ⟶ PA₀)
    (h : (eqToHom eBG ≫ (Scheme.Modules.pullback g).map α₁ ≫ eqToHom eAG.symm) ≫
        (eqToHom (eAG.trans (congrArg _ eA₁)) ≫
          (Scheme.Modules.pullbackComp g f ≪≫ Scheme.Modules.pullbackCongr hk).hom.app MA ≫
          eqToHom eA₀.symm) =
      (eqToHom (eBG.trans (congrArg _ eB₁)) ≫
          (Scheme.Modules.pullbackComp g f ≪≫ Scheme.Modules.pullbackCongr hk).hom.app MB ≫
          eqToHom eB₀.symm) ≫ α₀) :
    (Scheme.Modules.pullback g).map (eqToHom eB₁.symm ≫ α₁ ≫ eqToHom eA₁) ≫
        (Scheme.Modules.pullbackComp g f ≪≫ Scheme.Modules.pullbackCongr hk).hom.app MA =
      (Scheme.Modules.pullbackComp g f ≪≫ Scheme.Modules.pullbackCongr hk).hom.app MB ≫
        eqToHom eB₀.symm ≫ α₀ ≫ eqToHom eA₀ := by
  subst hk eB₁ eA₁ eB₀ eA₀ eBG eAG
  simpa using h

/-! ### Descent of quasicoherent algebra morphisms from formal completion -/

private lemma quasicoherentAlgebra_hom_ext {Y : Scheme.{u}} {P Q : QuasicoherentAlgebra Y}
    {u v : P ⟶ Q} (h : u.hom.hom.hom = v.hom.hom.hom) : u = v :=
  ObjectProperty.hom_ext _ (CommMon.hom_ext _ _ h)

/-- Composition isomorphism `(f^* ⋙ g^*) ≅ k^*` of quasicoherent algebra pullbacks along a
commutative triangle `g ≫ f = k`. -/
private def algebraPullbackCompIso {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X) (k : Z ⟶ X)
    (hk : g ≫ f = k) :
    QuasicoherentAlgebra.pullback f ⋙ QuasicoherentAlgebra.pullback g ≅
      QuasicoherentAlgebra.pullback k :=
  QuasicoherentAlgebra.pullbackComp g f ≪≫ eqToIso (by subst hk; rfl)

/-- On underlying modules, `algebraPullbackCompIso` agrees with the module pullback composition and
congruence isomorphism. -/
private lemma algebraPullbackCompIso_hom_app_hom {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X)
    (k : Z ⟶ X) (hk : g ≫ f = k) (A : QuasicoherentAlgebra X) :
    ((algebraPullbackCompIso g f k hk).hom.app A).hom.hom.hom =
      eqToHom ((QuasicoherentAlgebra.pullback_obj_X g _).trans
          (congrArg _ (QuasicoherentAlgebra.pullback_obj_X f A))) ≫
        (Scheme.Modules.pullbackComp g f ≪≫ Scheme.Modules.pullbackCongr hk).hom.app A.obj.X ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X k A).symm := by
  subst hk
  simp only [algebraPullbackCompIso, eqToIso_refl, Iso.trans_refl,
    QuasicoherentAlgebra.pullbackComp_hom_app_hom_hom_hom, Scheme.Modules.pullbackCongr]
  rfl

/-- Compatibility of `relativeSpecPullbackFst` with a commutative triangle `g ≫ f = k`. -/
private lemma relativeSpecPullbackFst_of_comp_eq {X Y Z : Scheme.{u}}
    (A : QuasicoherentAlgebra X) (g : Z ⟶ Y) (f : Y ⟶ X) (k : Z ⟶ X) (hk : g ≫ f = k) :
    relativeSpecPullbackFst A k =
      CommMon.relativeSpecMap ((algebraPullbackCompIso g f k hk).hom.app A).hom ≫
        relativeSpecPullbackFst ((QuasicoherentAlgebra.pullback f).obj A) g ≫
          relativeSpecPullbackFst A f := by
  subst hk
  simpa [algebraPullbackCompIso] using relativeSpecPullbackFst_comp A f g

/-- If formal completion on finite locally free sheaves is faithful, two morphisms between finite
locally free `𝒪_X`-modules agree whenever their pullbacks to all infinitesimal levels agree. -/
private lemma modules_hom_ext_of_completion {X : Scheme.{u}} {I : X.IdealSheafData}
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful]
    {M N : X.Modules} (hM : Scheme.Modules.isFiniteLocallyFree X M)
    (hN : Scheme.Modules.isFiniteLocallyFree X N) {u v : M ⟶ N}
    (h : ∀ n, (Scheme.Modules.pullback (Scheme.formalCompletion.toScheme X I n)).map u =
      (Scheme.Modules.pullback (Scheme.formalCompletion.toScheme X I n)).map v) :
    u = v := by
  let F := FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
    Scheme.formalCompletion.completionFunctor X I
  let u' : (⟨M, hM⟩ : FiniteLocallyFreeSheaf X) ⟶ ⟨N, hN⟩ := ObjectProperty.homMk u
  let v' : (⟨M, hM⟩ : FiniteLocallyFreeSheaf X) ⟶ ⟨N, hN⟩ := ObjectProperty.homMk v
  have huv : F.map u' = F.map v' := CoherentFormalModule.hom_ext h
  exact congrArg (fun f ↦ f.hom) (F.map_injective huv)

/-- Two algebra morphisms between quasicoherent `𝒪_X`-algebras with finite locally free carriers
agree as soon as their pullbacks to all infinitesimal levels agree, assuming formal completion is
faithful on finite locally free sheaves. -/
private lemma quasicoherentAlgebra_hom_ext_of_completion {X : Scheme.{u}} {I : X.IdealSheafData}
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful]
    {B A : QuasicoherentAlgebra X} (hB : Scheme.Modules.isFiniteLocallyFree X B.obj.X)
    (hA : Scheme.Modules.isFiniteLocallyFree X A.obj.X) {b₁ b₂ : B ⟶ A}
    (hb : ∀ n,
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).map b₁ =
        (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).map b₂) :
    b₁ = b₂ := by
  apply quasicoherentAlgebra_hom_ext
  refine modules_hom_ext_of_completion (I := I) hB hA fun n ↦ ?_
  refine (modules_conjugate_eq_iff (QuasicoherentAlgebra.pullback_obj_X _ B)
    (QuasicoherentAlgebra.pullback_obj_X _ A) _ _).mp ?_
  exact (QuasicoherentAlgebra.pullback_map_hom_hom_hom _ b₁).symm.trans
    ((congrArg (fun k ↦ k.hom.hom.hom) (hb n)).trans
      (QuasicoherentAlgebra.pullback_map_hom_hom_hom _ b₂))

/-- If `f^* φ` underlies an algebra map `f^* B ⟶ f^* A`, then `f^*` equalizes `η_B ≫ φ` and
`η_A`. -/
private lemma pullback_map_one_comp_eq {X Y : Scheme.{u}} (f : Y ⟶ X)
    {B A : QuasicoherentAlgebra X} (φ : B.obj.X ⟶ A.obj.X)
    (α : (QuasicoherentAlgebra.pullback f).obj B ⟶ (QuasicoherentAlgebra.pullback f).obj A)
    (hφ : (Scheme.Modules.pullback f).map φ =
      eqToHom (QuasicoherentAlgebra.pullback_obj_X f B).symm ≫ α.hom.hom.hom ≫
        eqToHom (QuasicoherentAlgebra.pullback_obj_X f A)) :
    (Scheme.Modules.pullback f).map (η[B.obj.X] ≫ φ) =
      (Scheme.Modules.pullback f).map η[A.obj.X] := by
  have hone0 :
      η[((QuasicoherentAlgebra.pullback f).obj B).obj.X] ≫ α.hom.hom.hom =
        η[((QuasicoherentAlgebra.pullback f).obj A).obj.X] :=
    IsMonHom.one_hom α.hom.hom.hom
  refine pullback_one_aux f (QuasicoherentAlgebra.pullback_obj_X f B)
    (QuasicoherentAlgebra.pullback_obj_X f A) φ α.hom.hom.hom ?_ hφ
  exact (congrArg (· ≫ α.hom.hom.hom) (QuasicoherentAlgebra.pullback_obj_one f B).symm).trans
    (hone0.trans (QuasicoherentAlgebra.pullback_obj_one f A))

/-- If `f^* φ` underlies an algebra map `f^* B ⟶ f^* A`, then `f^*` equalizes `μ_B ≫ φ` and
`(φ ⊗ₘ φ) ≫ μ_A`. -/
private lemma pullback_map_mul_comp_eq {X Y : Scheme.{u}} (f : Y ⟶ X)
    {B A : QuasicoherentAlgebra X} (φ : B.obj.X ⟶ A.obj.X)
    (α : (QuasicoherentAlgebra.pullback f).obj B ⟶ (QuasicoherentAlgebra.pullback f).obj A)
    (hφ : (Scheme.Modules.pullback f).map φ =
      eqToHom (QuasicoherentAlgebra.pullback_obj_X f B).symm ≫ α.hom.hom.hom ≫
        eqToHom (QuasicoherentAlgebra.pullback_obj_X f A)) :
    (Scheme.Modules.pullback f).map (μ[B.obj.X] ≫ φ) =
      (Scheme.Modules.pullback f).map ((φ ⊗ₘ φ) ≫ μ[A.obj.X]) := by
  have hmul0 :
      μ[((QuasicoherentAlgebra.pullback f).obj B).obj.X] ≫ α.hom.hom.hom =
        (α.hom.hom.hom ⊗ₘ α.hom.hom.hom) ≫
          μ[((QuasicoherentAlgebra.pullback f).obj A).obj.X] :=
    IsMonHom.mul_hom α.hom.hom.hom
  refine pullback_mul_aux f (QuasicoherentAlgebra.pullback_obj_X f B)
    (QuasicoherentAlgebra.pullback_obj_X f A) φ α.hom.hom.hom ?_ hφ
  exact (congrArg (· ≫ α.hom.hom.hom) (QuasicoherentAlgebra.pullback_obj_mul f B).symm).trans
    (hmul0.trans (congrArg ((α.hom.hom.hom ⊗ₘ α.hom.hom.hom) ≫ ·)
      (QuasicoherentAlgebra.pullback_obj_mul f A)))

/-- Assemble a compatible system of algebra morphisms `i_n^* B ⟶ i_n^* A` into a morphism of
coherent formal modules between the completions of the underlying finite locally free sheaves. -/
private def coherentFormalModuleHomOfAlgebraSystem {X : Scheme.{u}} {I : X.IdealSheafData}
    {B A : QuasicoherentAlgebra X} (hB : Scheme.Modules.isFiniteLocallyFree X B.obj.X)
    (hA : Scheme.Modules.isFiniteLocallyFree X A.obj.X)
    (α : ∀ n, (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj B ⟶
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj A)
    (hα : ∀ n,
      (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (α (n + 1)) ≫
          (algebraPullbackCompIso ((X.formalCompletion I).ι n)
            (Scheme.formalCompletion.toScheme X I (n + 1))
            (Scheme.formalCompletion.toScheme X I n)
            (Scheme.formalCompletion.ι_toScheme X I n)).hom.app A =
        (algebraPullbackCompIso ((X.formalCompletion I).ι n)
            (Scheme.formalCompletion.toScheme X I (n + 1))
            (Scheme.formalCompletion.toScheme X I n)
            (Scheme.formalCompletion.ι_toScheme X I n)).hom.app B ≫ α n) :
    (FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
        Scheme.formalCompletion.completionFunctor X I).obj ⟨B.obj.X, hB⟩ ⟶
      (FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
        Scheme.formalCompletion.completionFunctor X I).obj ⟨A.obj.X, hA⟩ where
  app n :=
    eqToHom (QuasicoherentAlgebra.pullback_obj_X _ B).symm ≫ (α n).hom.hom.hom ≫
      eqToHom (QuasicoherentAlgebra.pullback_obj_X _ A)
  naturality n := by
    refine coherentFormalModule_naturality_aux ((X.formalCompletion I).ι n)
      (Scheme.formalCompletion.toScheme X I (n + 1))
      (Scheme.formalCompletion.toScheme X I n)
      (Scheme.formalCompletion.ι_toScheme X I n)
      (QuasicoherentAlgebra.pullback_obj_X _ B)
      (QuasicoherentAlgebra.pullback_obj_X _ A)
      (QuasicoherentAlgebra.pullback_obj_X _ B)
      (QuasicoherentAlgebra.pullback_obj_X _ A)
      (QuasicoherentAlgebra.pullback_obj_X _ _)
      (QuasicoherentAlgebra.pullback_obj_X _ _)
      (α (n + 1)).hom.hom.hom (α n).hom.hom.hom ?_
    have hn :
        ((QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map
            (α (n + 1))).hom.hom.hom ≫
          ((algebraPullbackCompIso ((X.formalCompletion I).ι n)
            (Scheme.formalCompletion.toScheme X I (n + 1))
            (Scheme.formalCompletion.toScheme X I n)
            (Scheme.formalCompletion.ι_toScheme X I n)).hom.app A).hom.hom.hom =
        ((algebraPullbackCompIso ((X.formalCompletion I).ι n)
            (Scheme.formalCompletion.toScheme X I (n + 1))
            (Scheme.formalCompletion.toScheme X I n)
            (Scheme.formalCompletion.ι_toScheme X I n)).hom.app B).hom.hom.hom ≫
          (α n).hom.hom.hom :=
      congrArg (fun k ↦ k.hom.hom.hom) (hα n)
    exact (congrArg₂ CategoryStruct.comp
        (QuasicoherentAlgebra.pullback_map_hom_hom_hom _ (α (n + 1))).symm
        (algebraPullbackCompIso_hom_app_hom _ _ _ _ A).symm).trans
      (hn.trans (congrArg (· ≫ (α n).hom.hom.hom)
        (algebraPullbackCompIso_hom_app_hom _ _ _ _ B)))

/-- When formal completion on finite locally free sheaves is full and faithful, every compatible
family of algebra morphisms `i_n^* B ⟶ i_n^* A` between quasicoherent algebras with finite locally
free carriers comes from an algebra morphism `B ⟶ A` on `X`. -/
private lemma quasicoherentAlgebra_exists_hom_of_completion {X : Scheme.{u}}
    {I : X.IdealSheafData}
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful]
    {B A : QuasicoherentAlgebra X} (hB : Scheme.Modules.isFiniteLocallyFree X B.obj.X)
    (hA : Scheme.Modules.isFiniteLocallyFree X A.obj.X)
    (α : ∀ n, (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj B ⟶
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj A)
    (hα : ∀ n,
      (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (α (n + 1)) ≫
          (algebraPullbackCompIso ((X.formalCompletion I).ι n)
            (Scheme.formalCompletion.toScheme X I (n + 1))
            (Scheme.formalCompletion.toScheme X I n)
            (Scheme.formalCompletion.ι_toScheme X I n)).hom.app A =
        (algebraPullbackCompIso ((X.formalCompletion I).ι n)
            (Scheme.formalCompletion.toScheme X I (n + 1))
            (Scheme.formalCompletion.toScheme X I n)
            (Scheme.formalCompletion.ι_toScheme X I n)).hom.app B ≫ α n) :
    ∃ b : B ⟶ A, ∀ n,
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).map b = α n := by
  let F := FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
    Scheme.formalCompletion.completionFunctor X I
  obtain ⟨φ₀, hφ₀⟩ := F.map_surjective (coherentFormalModuleHomOfAlgebraSystem hB hA α hα)
  have hφ (n : ℕ) :
      (Scheme.Modules.pullback (Scheme.formalCompletion.toScheme X I n)).map φ₀.hom =
        eqToHom (QuasicoherentAlgebra.pullback_obj_X _ B).symm ≫ (α n).hom.hom.hom ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X _ A) :=
    congrArg (·.app n) hφ₀
  have hone : η[B.obj.X] ≫ φ₀.hom = η[A.obj.X] :=
    modules_hom_ext_of_completion (I := I) (ObjectProperty.prop_unit _) hA fun n ↦
      pullback_map_one_comp_eq _ φ₀.hom (α n) (hφ n)
  have hmul : μ[B.obj.X] ≫ φ₀.hom = (φ₀.hom ⊗ₘ φ₀.hom) ≫ μ[A.obj.X] :=
    modules_hom_ext_of_completion (I := I) (ObjectProperty.prop_tensor hB hB) hA fun n ↦
      pullback_map_mul_comp_eq _ φ₀.hom (α n) (hφ n)
  let b : B ⟶ A := ObjectProperty.homMk
    (CommMon.homMk (Mon.Hom.mk' (M := B.obj.toMon) (N := A.obj.toMon) φ₀.hom hone hmul))
  refine ⟨b, fun n ↦ quasicoherentAlgebra_hom_ext ?_⟩
  exact (QuasicoherentAlgebra.pullback_map_hom_hom_hom _ b).trans
    ((congrArg (fun t ↦ eqToHom (QuasicoherentAlgebra.pullback_obj_X _ B) ≫ t ≫
        eqToHom (QuasicoherentAlgebra.pullback_obj_X _ A).symm) (hφ n)).trans
      (modules_conjugate_cancel (QuasicoherentAlgebra.pullback_obj_X _ B)
        (QuasicoherentAlgebra.pullback_obj_X _ A) (α n).hom.hom.hom))

/-! ### Relative-Spec adic thickening systems over the formal completion -/

private lemma relativeSpec_hom_ext_of_relativeSpecMap {Y : Scheme.{u}}
    {P Q : QuasicoherentAlgebra Y} {u v : Q ⟶ P}
    (h : CommMon.relativeSpecMap u.hom = CommMon.relativeSpecMap v.hom) : u = v := by
  apply Quiver.Hom.op_inj
  apply (relativeSpec Y).map_injective
  apply MorphismProperty.Over.Hom.ext
  exact h

private lemma exists_quasicoherentAlgebra_hom_of_relativeSpec {Y : Scheme.{u}}
    {P Q : QuasicoherentAlgebra Y} (f : P.obj.relativeSpec ⟶ Q.obj.relativeSpec)
    (hf : f ≫ Q.obj.relativeSpecToBase = P.obj.relativeSpecToBase) :
    ∃ b : Q ⟶ P, CommMon.relativeSpecMap b.hom = f := by
  let f' : (relativeSpec Y).obj (op P) ⟶ (relativeSpec Y).obj (op Q) :=
    MorphismProperty.Over.homMk f hf
  refine ⟨((relativeSpec Y).preimage f').unop, ?_⟩
  exact congrArg (fun k : (relativeSpec Y).obj (op P) ⟶ (relativeSpec Y).obj (op Q) ↦ k.left)
    ((relativeSpec Y).map_preimage f')

/-- The canonical morphism `X.formalCompletion I ⟶ AdicThickeningSystem.ofScheme.obj X` given by
the closed immersions `V(I ^ (n + 1)) ⟶ X`. -/
private abbrev toConstSystem (X : Scheme.{u}) (I : X.IdealSheafData) :
    X.formalCompletion I ⟶ AdicThickeningSystem.ofScheme.obj X where
  app := Scheme.formalCompletion.toScheme X I
  naturality n := (Scheme.formalCompletion.ι_toScheme X I n).trans (Category.comp_id _).symm

/-- The adic thickening system of infinitesimal pullbacks of `Spec_X A` over
`X.formalCompletion I`. -/
private abbrev relativeSpecCompletionSystem (X : Scheme.{u}) (I : X.IdealSheafData)
    (A : QuasicoherentAlgebra X) : AdicThickeningSystem.{u} :=
  AdicThickeningSystem.pullback (toConstSystem X I)
    (AdicThickeningSystem.ofScheme.map A.obj.relativeSpecToBase)

/-- The projection `relativeSpecCompletionSystem X I A ⟶ X.formalCompletion I`. -/
private abbrev relativeSpecCompletionFst (X : Scheme.{u}) (I : X.IdealSheafData)
    (A : QuasicoherentAlgebra X) :
    relativeSpecCompletionSystem X I A ⟶ X.formalCompletion I :=
  AdicThickeningSystem.pullback.fst (toConstSystem X I)
    (AdicThickeningSystem.ofScheme.map A.obj.relativeSpecToBase)

/-- Functoriality of `relativeSpecCompletionSystem` in morphisms `b : B ⟶ A` of quasicoherent
algebras. -/
private def relativeSpecCompletionMap {X : Scheme.{u}} {I : X.IdealSheafData}
    {B A : QuasicoherentAlgebra X} (b : B ⟶ A) :
    relativeSpecCompletionSystem X I A ⟶ relativeSpecCompletionSystem X I B :=
  AdicThickeningSystem.pullback.lift
    (relativeSpecCompletionFst X I A)
    (AdicThickeningSystem.pullback.snd _ _ ≫
      AdicThickeningSystem.ofScheme.map (CommMon.relativeSpecMap b.hom))
    (by
      rw [AdicThickeningSystem.pullback.condition, Category.assoc, ← Functor.map_comp,
        CommMon.relativeSpecMap_relativeSpecToBase])

private lemma relativeSpecCompletionSystem_ι_fst (X : Scheme.{u}) (I : X.IdealSheafData)
    (A : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecCompletionSystem X I A).ι n ≫
        Limits.pullback.fst (Scheme.formalCompletion.toScheme X I (n + 1))
          A.obj.relativeSpecToBase =
      Limits.pullback.fst (Scheme.formalCompletion.toScheme X I n) A.obj.relativeSpecToBase ≫
        (X.formalCompletion I).ι n := by
  have h := (relativeSpecCompletionFst X I A).naturality n
  rw [AdicThickeningSystem.pullback.fst_app, AdicThickeningSystem.pullback.fst_app] at h
  exact h

private lemma relativeSpecCompletionSystem_ι_snd (X : Scheme.{u}) (I : X.IdealSheafData)
    (A : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecCompletionSystem X I A).ι n ≫
        Limits.pullback.snd (Scheme.formalCompletion.toScheme X I (n + 1))
          A.obj.relativeSpecToBase =
      Limits.pullback.snd (Scheme.formalCompletion.toScheme X I n) A.obj.relativeSpecToBase := by
  have h := (AdicThickeningSystem.pullback.snd (toConstSystem X I)
    (AdicThickeningSystem.ofScheme.map A.obj.relativeSpecToBase)).naturality n
  rw [AdicThickeningSystem.pullback.snd_app, AdicThickeningSystem.pullback.snd_app,
    AdicThickeningSystem.ofScheme_obj_ι] at h
  exact h.trans (Category.comp_id _)

private lemma relativeSpecCompletionMap_app_fst {X : Scheme.{u}} {I : X.IdealSheafData}
    {B A : QuasicoherentAlgebra X} (b : B ⟶ A) (n : ℕ) :
    (relativeSpecCompletionMap (I := I) b).app n ≫
        Limits.pullback.fst (Scheme.formalCompletion.toScheme X I n) B.obj.relativeSpecToBase =
      Limits.pullback.fst (Scheme.formalCompletion.toScheme X I n) A.obj.relativeSpecToBase := by
  have h : relativeSpecCompletionMap (I := I) b ≫ relativeSpecCompletionFst X I B =
      relativeSpecCompletionFst X I A := by
    simp [relativeSpecCompletionMap]
  have hn := congrArg (·.app n) h
  rw [AdicThickeningSystem.comp_app, AdicThickeningSystem.pullback.fst_app,
    AdicThickeningSystem.pullback.fst_app] at hn
  exact hn

private lemma relativeSpecCompletionMap_app_snd {X : Scheme.{u}} {I : X.IdealSheafData}
    {B A : QuasicoherentAlgebra X} (b : B ⟶ A) (n : ℕ) :
    (relativeSpecCompletionMap (I := I) b).app n ≫
        Limits.pullback.snd (Scheme.formalCompletion.toScheme X I n) B.obj.relativeSpecToBase =
      Limits.pullback.snd (Scheme.formalCompletion.toScheme X I n) A.obj.relativeSpecToBase ≫
        CommMon.relativeSpecMap b.hom := by
  have h : relativeSpecCompletionMap (I := I) b ≫
        AdicThickeningSystem.pullback.snd (toConstSystem X I)
          (AdicThickeningSystem.ofScheme.map B.obj.relativeSpecToBase) =
      AdicThickeningSystem.pullback.snd (toConstSystem X I)
          (AdicThickeningSystem.ofScheme.map A.obj.relativeSpecToBase) ≫
        AdicThickeningSystem.ofScheme.map (CommMon.relativeSpecMap b.hom) := by
    simp [relativeSpecCompletionMap]
  have hn := congrArg (·.app n) h
  rw [AdicThickeningSystem.comp_app, AdicThickeningSystem.comp_app,
    AdicThickeningSystem.pullback.snd_app, AdicThickeningSystem.pullback.snd_app] at hn
  exact hn

/-- Levelwise identification `Spec_{X_n} (i_n^* A) ≅ (relativeSpecCompletionSystem X I A).X n`. -/
private def relativeSpecCompletionLevelIso (X : Scheme.{u}) (I : X.IdealSheafData)
    (A : QuasicoherentAlgebra X) (n : ℕ) :
    ((QuasicoherentAlgebra.pullback
        (Scheme.formalCompletion.toScheme X I n)).obj A).obj.relativeSpec ≅
      (relativeSpecCompletionSystem X I A).X n :=
  (isPullback_relativeSpecPullbackFst A (Scheme.formalCompletion.toScheme X I n)).flip.isoPullback

/-- Geometric transition map `Spec_{X_n} (i_n^* A) ⟶ Spec_{X_{n+1}} (i_{n+1}^* A)` between the
relative spectra of consecutive reductions of `A`. -/
private def relativeSpecReductionTransition (X : Scheme.{u}) (I : X.IdealSheafData)
    (A : QuasicoherentAlgebra X) (n : ℕ) :
    ((QuasicoherentAlgebra.pullback
        (Scheme.formalCompletion.toScheme X I n)).obj A).obj.relativeSpec ⟶
      ((QuasicoherentAlgebra.pullback
        (Scheme.formalCompletion.toScheme X I (n + 1))).obj A).obj.relativeSpec :=
  CommMon.relativeSpecMap
      ((algebraPullbackCompIso ((X.formalCompletion I).ι n)
        (Scheme.formalCompletion.toScheme X I (n + 1))
        (Scheme.formalCompletion.toScheme X I n)
        (Scheme.formalCompletion.ι_toScheme X I n)).hom.app A).hom ≫
    relativeSpecPullbackFst
      ((QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I (n + 1))).obj A)
      ((X.formalCompletion I).ι n)

/-- `relativeSpecCompletionLevelIso` intertwines `relativeSpecReductionTransition` with the
transition maps of `relativeSpecCompletionSystem`. -/
private lemma relativeSpecReductionTransition_comp_levelIso (X : Scheme.{u})
    (I : X.IdealSheafData) (A : QuasicoherentAlgebra X) (n : ℕ) :
    relativeSpecReductionTransition X I A n ≫ (relativeSpecCompletionLevelIso X I A (n + 1)).hom =
      (relativeSpecCompletionLevelIso X I A n).hom ≫ (relativeSpecCompletionSystem X I A).ι n := by
  let i := Scheme.formalCompletion.toScheme X I
  let hA (k : ℕ) := (isPullback_relativeSpecPullbackFst A (i k)).flip
  let c := (algebraPullbackCompIso ((X.formalCompletion I).ι n) (i (n + 1)) (i n)
    (Scheme.formalCompletion.ι_toScheme X I n)).hom.app A
  refine Limits.pullback.hom_ext ?_ ?_
  · calc _ = CommMon.relativeSpecMap c.hom ≫
              relativeSpecPullbackFst ((QuasicoherentAlgebra.pullback (i (n + 1))).obj A)
                ((X.formalCompletion I).ι n) ≫
              (hA (n + 1)).isoPullback.hom ≫
                Limits.pullback.fst (i (n + 1)) A.obj.relativeSpecToBase :=
            (Category.assoc _ _ _).trans (Category.assoc _ _ _)
      _ = CommMon.relativeSpecMap c.hom ≫
            relativeSpecPullbackFst ((QuasicoherentAlgebra.pullback (i (n + 1))).obj A)
              ((X.formalCompletion I).ι n) ≫
            ((QuasicoherentAlgebra.pullback (i (n + 1))).obj A).obj.relativeSpecToBase :=
          congrArg (CommMon.relativeSpecMap c.hom ≫ _ ≫ ·) (hA (n + 1)).isoPullback_hom_fst
      _ = ((QuasicoherentAlgebra.pullback (i n)).obj A).obj.relativeSpecToBase ≫
            (X.formalCompletion I).ι n :=
          (congrArg (CommMon.relativeSpecMap c.hom ≫ ·)
            (relativeSpecPullbackFst_relativeSpecToBase _ _)).trans
            (CommMon.relativeSpecMap_relativeSpecToBase_assoc c.hom _)
      _ = (hA n).isoPullback.hom ≫
            (Limits.pullback.fst (i n) A.obj.relativeSpecToBase ≫ (X.formalCompletion I).ι n) :=
          (IsPullback.isoPullback_hom_fst_assoc (hA n) _).symm
      _ = _ :=
          (congrArg ((hA n).isoPullback.hom ≫ ·)
            (relativeSpecCompletionSystem_ι_fst X I A n).symm).trans (Category.assoc _ _ _).symm
  · calc _ = CommMon.relativeSpecMap c.hom ≫
              relativeSpecPullbackFst ((QuasicoherentAlgebra.pullback (i (n + 1))).obj A)
                ((X.formalCompletion I).ι n) ≫
              (hA (n + 1)).isoPullback.hom ≫
                Limits.pullback.snd (i (n + 1)) A.obj.relativeSpecToBase :=
            (Category.assoc _ _ _).trans (Category.assoc _ _ _)
      _ = relativeSpecPullbackFst A (i n) :=
          (congrArg (CommMon.relativeSpecMap c.hom ≫ _ ≫ ·)
            (hA (n + 1)).isoPullback_hom_snd).trans
            (relativeSpecPullbackFst_of_comp_eq A ((X.formalCompletion I).ι n) (i (n + 1)) (i n)
              (Scheme.formalCompletion.ι_toScheme X I n)).symm
      _ = (hA n).isoPullback.hom ≫ Limits.pullback.snd (i n) A.obj.relativeSpecToBase :=
          (hA n).isoPullback_hom_snd.symm
      _ = _ :=
          (congrArg ((hA n).isoPullback.hom ≫ ·)
            (relativeSpecCompletionSystem_ι_snd X I A n).symm).trans (Category.assoc _ _ _).symm

/-- Conjugating `(relativeSpecCompletionMap b).app n` by `relativeSpecCompletionLevelIso` recovers
the relative-spectrum map of `i_n^* b`. -/
private lemma relativeSpecMap_pullback_comp_levelIso {X : Scheme.{u}} {I : X.IdealSheafData}
    {B A : QuasicoherentAlgebra X} (b : B ⟶ A) (n : ℕ) :
    CommMon.relativeSpecMap
        ((QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).map b).hom ≫
      (relativeSpecCompletionLevelIso X I B n).hom =
    (relativeSpecCompletionLevelIso X I A n).hom ≫ (relativeSpecCompletionMap b).app n := by
  let i := Scheme.formalCompletion.toScheme X I n
  let hA := (isPullback_relativeSpecPullbackFst A i).flip
  let hB := (isPullback_relativeSpecPullbackFst B i).flip
  refine Limits.pullback.hom_ext ?_ ?_
  · calc _ = CommMon.relativeSpecMap
              ((QuasicoherentAlgebra.pullback i).map b).hom ≫
              hB.isoPullback.hom ≫ Limits.pullback.fst i B.obj.relativeSpecToBase :=
            Category.assoc _ _ _
      _ = ((QuasicoherentAlgebra.pullback i).obj A).obj.relativeSpecToBase :=
          (congrArg (_ ≫ ·) hB.isoPullback_hom_fst).trans
            (CommMon.relativeSpecMap_relativeSpecToBase _)
      _ = hA.isoPullback.hom ≫ Limits.pullback.fst i A.obj.relativeSpecToBase :=
          hA.isoPullback_hom_fst.symm
      _ = _ :=
          (congrArg (hA.isoPullback.hom ≫ ·) (relativeSpecCompletionMap_app_fst b n).symm).trans
            (Category.assoc _ _ _).symm
  · calc _ = CommMon.relativeSpecMap
              ((QuasicoherentAlgebra.pullback i).map b).hom ≫
              hB.isoPullback.hom ≫ Limits.pullback.snd i B.obj.relativeSpecToBase :=
            Category.assoc _ _ _
      _ = relativeSpecPullbackFst A i ≫ CommMon.relativeSpecMap b.hom :=
          (congrArg (_ ≫ ·) hB.isoPullback_hom_snd).trans
            (relativeSpecMap_pullback_map_relativeSpecPullbackFst A i b)
      _ = hA.isoPullback.hom ≫
            (Limits.pullback.snd i A.obj.relativeSpecToBase ≫ CommMon.relativeSpecMap b.hom) :=
          (IsPullback.isoPullback_hom_snd_assoc hA _).symm
      _ = _ :=
          (congrArg (hA.isoPullback.hom ≫ ·) (relativeSpecCompletionMap_app_snd b n).symm).trans
            (Category.assoc _ _ _).symm

/-- A morphism `Φ` over `X.formalCompletion I` between `relativeSpecCompletionSystem X I A` and
`relativeSpecCompletionSystem X I B` induces an algebra morphism `i_n^* B ⟶ i_n^* A` at each
level `n` via the relative-Spec anti-equivalence. -/
private lemma exists_algebraHomOfCompletionHom {X : Scheme.{u}} {I : X.IdealSheafData}
    {B A : QuasicoherentAlgebra X}
    (Φ : relativeSpecCompletionSystem X I A ⟶ relativeSpecCompletionSystem X I B)
    (hΦ : Φ ≫ relativeSpecCompletionFst X I B = relativeSpecCompletionFst X I A) (n : ℕ) :
    ∃ α : (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj B ⟶
        (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj A,
      CommMon.relativeSpecMap α.hom =
        (relativeSpecCompletionLevelIso X I A n).hom ≫ Φ.app n ≫
          (relativeSpecCompletionLevelIso X I B n).inv := by
  let i := Scheme.formalCompletion.toScheme X I n
  let hA := (isPullback_relativeSpecPullbackFst A i).flip
  let hB := (isPullback_relativeSpecPullbackFst B i).flip
  have hn : Φ.app n ≫ Limits.pullback.fst i B.obj.relativeSpecToBase =
      Limits.pullback.fst i A.obj.relativeSpecToBase := by
    have h := congrArg (·.app n) hΦ
    rw [AdicThickeningSystem.comp_app, AdicThickeningSystem.pullback.fst_app,
      AdicThickeningSystem.pullback.fst_app] at h
    exact h
  refine exists_quasicoherentAlgebra_hom_of_relativeSpec _ ?_
  calc (hA.isoPullback.hom ≫ Φ.app n ≫ hB.isoPullback.inv) ≫
          ((QuasicoherentAlgebra.pullback i).obj B).obj.relativeSpecToBase
      = hA.isoPullback.hom ≫ Φ.app n ≫
          (hB.isoPullback.inv ≫ ((QuasicoherentAlgebra.pullback i).obj B).obj.relativeSpecToBase) :=
        (Category.assoc _ _ _).trans (congrArg (hA.isoPullback.hom ≫ ·) (Category.assoc _ _ _))
    _ = hA.isoPullback.hom ≫ Φ.app n ≫ Limits.pullback.fst i B.obj.relativeSpecToBase :=
        congrArg (hA.isoPullback.hom ≫ Φ.app n ≫ ·) hB.isoPullback_inv_fst
    _ = hA.isoPullback.hom ≫ Limits.pullback.fst i A.obj.relativeSpecToBase :=
        congrArg (hA.isoPullback.hom ≫ ·) hn
    _ = ((QuasicoherentAlgebra.pullback i).obj A).obj.relativeSpecToBase :=
        hA.isoPullback_hom_fst

private def algebraHomOfCompletionHom {X : Scheme.{u}} {I : X.IdealSheafData}
    {B A : QuasicoherentAlgebra X}
    (Φ : relativeSpecCompletionSystem X I A ⟶ relativeSpecCompletionSystem X I B)
    (hΦ : Φ ≫ relativeSpecCompletionFst X I B = relativeSpecCompletionFst X I A) (n : ℕ) :
    (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj B ⟶
      (QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I n)).obj A :=
  (exists_algebraHomOfCompletionHom Φ hΦ n).choose

private lemma relativeSpecMap_algebraHomOfCompletionHom {X : Scheme.{u}} {I : X.IdealSheafData}
    {B A : QuasicoherentAlgebra X}
    (Φ : relativeSpecCompletionSystem X I A ⟶ relativeSpecCompletionSystem X I B)
    (hΦ : Φ ≫ relativeSpecCompletionFst X I B = relativeSpecCompletionFst X I A) (n : ℕ) :
    CommMon.relativeSpecMap (algebraHomOfCompletionHom Φ hΦ n).hom =
      (relativeSpecCompletionLevelIso X I A n).hom ≫ Φ.app n ≫
        (relativeSpecCompletionLevelIso X I B n).inv :=
  (exists_algebraHomOfCompletionHom Φ hΦ n).choose_spec

private lemma algebraHomOfCompletionHom_naturality_fst {X : Scheme.{u}} {I : X.IdealSheafData}
    {B A : QuasicoherentAlgebra X}
    (Φ : relativeSpecCompletionSystem X I A ⟶ relativeSpecCompletionSystem X I B)
    (hΦ : Φ ≫ relativeSpecCompletionFst X I B = relativeSpecCompletionFst X I A) (n : ℕ) :
    (CommMon.relativeSpecMap ((algebraPullbackCompIso ((X.formalCompletion I).ι n)
            (Scheme.formalCompletion.toScheme X I (n + 1))
            (Scheme.formalCompletion.toScheme X I n)
            (Scheme.formalCompletion.ι_toScheme X I n)).hom.app A).hom ≫
        CommMon.relativeSpecMap ((QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map
          (algebraHomOfCompletionHom Φ hΦ (n + 1))).hom) ≫
      relativeSpecPullbackFst
        ((QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I (n + 1))).obj B)
        ((X.formalCompletion I).ι n) =
    (CommMon.relativeSpecMap (algebraHomOfCompletionHom Φ hΦ n).hom ≫
        CommMon.relativeSpecMap ((algebraPullbackCompIso ((X.formalCompletion I).ι n)
            (Scheme.formalCompletion.toScheme X I (n + 1))
            (Scheme.formalCompletion.toScheme X I n)
            (Scheme.formalCompletion.ι_toScheme X I n)).hom.app B).hom) ≫
      relativeSpecPullbackFst
        ((QuasicoherentAlgebra.pullback (Scheme.formalCompletion.toScheme X I (n + 1))).obj B)
        ((X.formalCompletion I).ι n) := by
  let j := (X.formalCompletion I).ι n
  let i := Scheme.formalCompletion.toScheme X I
  let α₁ := algebraHomOfCompletionHom Φ hΦ (n + 1)
  let α₀ := algebraHomOfCompletionHom Φ hΦ n
  let cA := (algebraPullbackCompIso j (i (n + 1)) (i n)
    (Scheme.formalCompletion.ι_toScheme X I n)).hom.app A
  let cB := (algebraPullbackCompIso j (i (n + 1)) (i n)
    (Scheme.formalCompletion.ι_toScheme X I n)).hom.app B
  calc (CommMon.relativeSpecMap cA.hom ≫
          CommMon.relativeSpecMap ((QuasicoherentAlgebra.pullback j).map α₁).hom) ≫
          relativeSpecPullbackFst ((QuasicoherentAlgebra.pullback (i (n + 1))).obj B) j
      = CommMon.relativeSpecMap cA.hom ≫
          (CommMon.relativeSpecMap ((QuasicoherentAlgebra.pullback j).map α₁).hom ≫
            relativeSpecPullbackFst ((QuasicoherentAlgebra.pullback (i (n + 1))).obj B) j) :=
        Category.assoc _ _ _
    _ = CommMon.relativeSpecMap cA.hom ≫
          relativeSpecPullbackFst ((QuasicoherentAlgebra.pullback (i (n + 1))).obj A) j ≫
          CommMon.relativeSpecMap α₁.hom :=
        congrArg (CommMon.relativeSpecMap cA.hom ≫ ·)
          (relativeSpecMap_pullback_map_relativeSpecPullbackFst _ j α₁)
    _ = relativeSpecReductionTransition X I A n ≫
          (relativeSpecCompletionLevelIso X I A (n + 1)).hom ≫
          Φ.app (n + 1) ≫ (relativeSpecCompletionLevelIso X I B (n + 1)).inv :=
        (Category.assoc _ _ _).symm.trans (congrArg (relativeSpecReductionTransition X I A n ≫ ·)
          (relativeSpecMap_algebraHomOfCompletionHom Φ hΦ (n + 1)))
    _ = (relativeSpecCompletionLevelIso X I A n).hom ≫ Φ.app n ≫
          (relativeSpecCompletionSystem X I B).ι n ≫
          (relativeSpecCompletionLevelIso X I B (n + 1)).inv := by
        rw [reassoc_of% relativeSpecReductionTransition_comp_levelIso X I A n, Φ.naturality_assoc n]
    _ = ((relativeSpecCompletionLevelIso X I A n).hom ≫ Φ.app n ≫
          (relativeSpecCompletionLevelIso X I B n).inv) ≫
          relativeSpecReductionTransition X I B n := by
        have hB := relativeSpecReductionTransition_comp_levelIso X I B n
        rw [← Iso.eq_comp_inv] at hB
        simp only [Category.assoc, hB, Iso.inv_hom_id_assoc]
    _ = (CommMon.relativeSpecMap α₀.hom ≫ CommMon.relativeSpecMap cB.hom) ≫
          relativeSpecPullbackFst ((QuasicoherentAlgebra.pullback (i (n + 1))).obj B) j :=
        (congrArg (· ≫ relativeSpecReductionTransition X I B n)
          (relativeSpecMap_algebraHomOfCompletionHom Φ hΦ n).symm).trans
          (Category.assoc _ _ _).symm

/-- The levelwise algebra morphisms `algebraHomOfCompletionHom Φ hΦ n` form a compatible system
across the transitions of `X.formalCompletion I`. -/
private lemma algebraHomOfCompletionHom_naturality {X : Scheme.{u}} {I : X.IdealSheafData}
    {B A : QuasicoherentAlgebra X}
    (Φ : relativeSpecCompletionSystem X I A ⟶ relativeSpecCompletionSystem X I B)
    (hΦ : Φ ≫ relativeSpecCompletionFst X I B = relativeSpecCompletionFst X I A) (n : ℕ) :
    (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map
        (algebraHomOfCompletionHom Φ hΦ (n + 1)) ≫
      (algebraPullbackCompIso ((X.formalCompletion I).ι n)
        (Scheme.formalCompletion.toScheme X I (n + 1))
        (Scheme.formalCompletion.toScheme X I n)
        (Scheme.formalCompletion.ι_toScheme X I n)).hom.app A =
    (algebraPullbackCompIso ((X.formalCompletion I).ι n)
        (Scheme.formalCompletion.toScheme X I (n + 1))
        (Scheme.formalCompletion.toScheme X I n)
        (Scheme.formalCompletion.ι_toScheme X I n)).hom.app B ≫
      algebraHomOfCompletionHom Φ hΦ n := by
  apply relativeSpec_hom_ext_of_relativeSpecMap
  let j := (X.formalCompletion I).ι n
  let i := Scheme.formalCompletion.toScheme X I
  let α₁ := algebraHomOfCompletionHom Φ hΦ (n + 1)
  let α₀ := algebraHomOfCompletionHom Φ hΦ n
  let cA := (algebraPullbackCompIso j (i (n + 1)) (i n)
    (Scheme.formalCompletion.ι_toScheme X I n)).hom.app A
  let cB := (algebraPullbackCompIso j (i (n + 1)) (i n)
    (Scheme.formalCompletion.ι_toScheme X I n)).hom.app B
  refine (CommMon.relativeSpecMap_comp _ cA.hom).trans
    (Eq.trans ?_ (CommMon.relativeSpecMap_comp cB.hom α₀.hom).symm)
  -- Compare the two scheme morphisms into the pullback relative spectrum via its limit property.
  refine (isPullback_relativeSpecPullbackFst
    ((QuasicoherentAlgebra.pullback (i (n + 1))).obj B) j).hom_ext
      (algebraHomOfCompletionHom_naturality_fst Φ hΦ n) ?_
  calc (CommMon.relativeSpecMap cA.hom ≫
          CommMon.relativeSpecMap ((QuasicoherentAlgebra.pullback j).map α₁).hom) ≫
          ((QuasicoherentAlgebra.pullback j).obj
            ((QuasicoherentAlgebra.pullback (i (n + 1))).obj B)).obj.relativeSpecToBase
      = CommMon.relativeSpecMap cA.hom ≫
          (CommMon.relativeSpecMap ((QuasicoherentAlgebra.pullback j).map α₁).hom ≫
            ((QuasicoherentAlgebra.pullback j).obj
              ((QuasicoherentAlgebra.pullback (i (n + 1))).obj B)).obj.relativeSpecToBase) :=
        Category.assoc _ _ _
    _ = ((QuasicoherentAlgebra.pullback (i n)).obj A).obj.relativeSpecToBase :=
        (congrArg (CommMon.relativeSpecMap cA.hom ≫ ·)
          (CommMon.relativeSpecMap_relativeSpecToBase _)).trans
          (CommMon.relativeSpecMap_relativeSpecToBase cA.hom)
    _ = CommMon.relativeSpecMap α₀.hom ≫
          (CommMon.relativeSpecMap cB.hom ≫
            ((QuasicoherentAlgebra.pullback j).obj
              ((QuasicoherentAlgebra.pullback (i (n + 1))).obj B)).obj.relativeSpecToBase) :=
        (CommMon.relativeSpecMap_relativeSpecToBase α₀.hom).symm.trans
          (congrArg (CommMon.relativeSpecMap α₀.hom ≫ ·)
            (CommMon.relativeSpecMap_relativeSpecToBase cB.hom).symm)
    _ = _ := (Category.assoc _ _ _).symm

/-! ### Finite étale schemes presented as relative spectra -/

/-- The finite étale scheme `Spec_X A` over `X` attached to a quasicoherent `𝒪_X`-algebra `A` whose
relative spectrum is finite and étale over `X` (an `abbrev` so `.obj` reduces to
`Over.mk A.obj.relativeSpecToBase` at `reducible` transparency without `eqToIso` transports). -/
private abbrev relativeSpecFiniteEtale {X : Scheme.{u}} (A : QuasicoherentAlgebra X)
    [IsFinite A.obj.relativeSpecToBase] [Etale A.obj.relativeSpecToBase] :
    FiniteEtaleScheme X :=
  ⟨Over.mk A.obj.relativeSpecToBase, (finiteEtaleSchemeProperty_iff _).mpr ⟨‹_›, ‹_›⟩⟩

/-- The morphism `relativeSpecFiniteEtale A ⟶ relativeSpecFiniteEtale B` in `FiniteEtaleScheme X`
induced by an algebra map `b : B ⟶ A`. -/
private def ofRelativeSpecMap {X : Scheme.{u}} {B A : QuasicoherentAlgebra X}
    [IsFinite A.obj.relativeSpecToBase] [Etale A.obj.relativeSpecToBase]
    [IsFinite B.obj.relativeSpecToBase] [Etale B.obj.relativeSpecToBase]
    (b : B ⟶ A) :
    relativeSpecFiniteEtale A ⟶ relativeSpecFiniteEtale B :=
  ObjectProperty.homMk
    (Over.homMk (CommMon.relativeSpecMap b.hom) (CommMon.relativeSpecMap_relativeSpecToBase b.hom))

/-- Every morphism `relativeSpecFiniteEtale A ⟶ relativeSpecFiniteEtale B` comes from an algebra
map `B ⟶ A`. -/
private lemma exists_ofRelativeSpecMap {X : Scheme.{u}} {B A : QuasicoherentAlgebra X}
    [IsFinite A.obj.relativeSpecToBase] [Etale A.obj.relativeSpecToBase]
    [IsFinite B.obj.relativeSpecToBase] [Etale B.obj.relativeSpecToBase]
    (g : relativeSpecFiniteEtale A ⟶ relativeSpecFiniteEtale B) :
    ∃ b : B ⟶ A, ofRelativeSpecMap b = g := by
  obtain ⟨b, hb⟩ := exists_quasicoherentAlgebra_hom_of_relativeSpec g.hom.left (Over.w g.hom)
  exact ⟨b, ObjectProperty.hom_ext _ (Over.OverMorphism.ext hb)⟩

private lemma pullback_map_ofRelativeSpecMap_snd {X Y : Scheme.{u}} (f : Y ⟶ X)
    {B A : QuasicoherentAlgebra X}
    [IsFinite A.obj.relativeSpecToBase] [Etale A.obj.relativeSpecToBase]
    [IsFinite B.obj.relativeSpecToBase] [Etale B.obj.relativeSpecToBase]
    (b : B ⟶ A) :
    ((pullback f).map (ofRelativeSpecMap b)).hom.left ≫
        Limits.pullback.snd B.obj.relativeSpecToBase f =
      Limits.pullback.snd A.obj.relativeSpecToBase f := by
  simp only [ofRelativeSpecMap, pullback_map_hom, ObjectProperty.homMk_hom]
  dsimp [Over.pullback]
  exact Limits.pullback.lift_snd _ _ _

private lemma pullback_map_ofRelativeSpecMap_fst {X Y : Scheme.{u}} (f : Y ⟶ X)
    {B A : QuasicoherentAlgebra X}
    [IsFinite A.obj.relativeSpecToBase] [Etale A.obj.relativeSpecToBase]
    [IsFinite B.obj.relativeSpecToBase] [Etale B.obj.relativeSpecToBase]
    (b : B ⟶ A) :
    ((pullback f).map (ofRelativeSpecMap b)).hom.left ≫
        Limits.pullback.fst B.obj.relativeSpecToBase f =
      Limits.pullback.fst A.obj.relativeSpecToBase f ≫ CommMon.relativeSpecMap b.hom := by
  simp only [ofRelativeSpecMap, pullback_map_hom, ObjectProperty.homMk_hom]
  dsimp [Over.pullback]
  exact Limits.pullback.lift_fst _ _ _

/-- Level `0` of `relativeSpecCompletionMap b` agrees with `FiniteEtaleScheme.pullback` along
`toScheme X I 0` up to `Limits.pullbackSymmetry`. -/
private lemma pullback_toScheme_zero_map_ofRelativeSpecMap {X : Scheme.{u}} {I : X.IdealSheafData}
    {B A : QuasicoherentAlgebra X}
    [IsFinite A.obj.relativeSpecToBase] [Etale A.obj.relativeSpecToBase]
    [IsFinite B.obj.relativeSpecToBase] [Etale B.obj.relativeSpecToBase]
    (b : B ⟶ A) :
    ((pullback (Scheme.formalCompletion.toScheme X I 0)).map (ofRelativeSpecMap b)).hom.left ≫
        (Limits.pullbackSymmetry B.obj.relativeSpecToBase
          (Scheme.formalCompletion.toScheme X I 0)).hom =
      (Limits.pullbackSymmetry A.obj.relativeSpecToBase
          (Scheme.formalCompletion.toScheme X I 0)).hom ≫
        (relativeSpecCompletionMap (I := I) b).app 0 := by
  let i₀ := Scheme.formalCompletion.toScheme X I 0
  refine Limits.pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (Limits.pullbackSymmetry_hom_comp_fst _ _)).trans <|
      (pullback_map_ofRelativeSpecMap_snd i₀ b).trans <|
      (Limits.pullbackSymmetry_hom_comp_fst _ _).symm.trans <|
      (congrArg (_ ≫ ·) (relativeSpecCompletionMap_app_fst b 0).symm).trans
        (Category.assoc _ _ _).symm
  · exact (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (Limits.pullbackSymmetry_hom_comp_snd _ _)).trans <|
      (pullback_map_ofRelativeSpecMap_fst i₀ b).trans <|
      (Limits.pullbackSymmetry_hom_comp_snd_assoc _ _ _).symm.trans <|
      (congrArg (_ ≫ ·) (relativeSpecCompletionMap_app_snd b 0).symm).trans
        (Category.assoc _ _ _).symm

private instance etale_relativeSpecCompletionFst_app {X : Scheme.{u}} {I : X.IdealSheafData}
    (B : QuasicoherentAlgebra X) [Etale B.obj.relativeSpecToBase] (n : ℕ) :
    Etale ((relativeSpecCompletionFst X I B).app n) := by
  rw [AdicThickeningSystem.pullback.fst_app]
  exact MorphismProperty.pullback_fst (P := @Etale)
    (Scheme.formalCompletion.toScheme X I n) B.obj.relativeSpecToBase ‹_›

/-- Injectivity of `(pullback (toScheme X I 0)).map` on finite étale relative spectra whose
coordinate algebras are finite locally free, assuming formal completion is faithful on finite
locally free sheaves. -/
private lemma pullback_toScheme_zero_map_injective_relativeSpec {X : Scheme.{u}}
    {I : X.IdealSheafData}
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful]
    {B A : QuasicoherentAlgebra X} (hB : Scheme.Modules.isFiniteLocallyFree X B.obj.X)
    (hA : Scheme.Modules.isFiniteLocallyFree X A.obj.X)
    [IsFinite A.obj.relativeSpecToBase] [Etale A.obj.relativeSpecToBase]
    [IsFinite B.obj.relativeSpecToBase] [Etale B.obj.relativeSpecToBase] :
    Function.Injective
      ((pullback (Scheme.formalCompletion.toScheme X I 0)).map :
        (relativeSpecFiniteEtale A ⟶ relativeSpecFiniteEtale B) → _) := by
  intro g₁ g₂ hg
  obtain ⟨b₁, rfl⟩ := exists_ofRelativeSpecMap g₁
  obtain ⟨b₂, rfl⟩ := exists_ofRelativeSpecMap g₂
  have hg' :
      ((pullback (Scheme.formalCompletion.toScheme X I 0)).map (ofRelativeSpecMap b₁)).hom.left =
        ((pullback (Scheme.formalCompletion.toScheme X I 0)).map (ofRelativeSpecMap b₂)).hom.left :=
    congrArg (fun k ↦ k.hom.left) hg
  have happ0 : (relativeSpecCompletionMap (I := I) b₁).app 0 =
      (relativeSpecCompletionMap (I := I) b₂).app 0 := by
    refine (cancel_epi (Limits.pullbackSymmetry A.obj.relativeSpecToBase
        (Scheme.formalCompletion.toScheme X I 0)).hom).mp ?_
    exact (pullback_toScheme_zero_map_ofRelativeSpecMap (I := I) b₁).symm.trans
      ((congrArg (· ≫ _) hg').trans (pullback_toScheme_zero_map_ofRelativeSpecMap (I := I) b₂))
  have hΦ : relativeSpecCompletionMap (I := I) b₁ = relativeSpecCompletionMap (I := I) b₂ :=
    AdicThickeningSystem.hom_ext_of_formallyUnramified (relativeSpecCompletionFst X I B)
      (by simp [relativeSpecCompletionMap]) happ0
  congr 1
  refine quasicoherentAlgebra_hom_ext_of_completion (I := I) hB hA fun n ↦ ?_
  apply relativeSpec_hom_ext_of_relativeSpecMap
  have hn : (relativeSpecCompletionMap (I := I) b₁).app n =
      (relativeSpecCompletionMap (I := I) b₂).app n := congrArg (·.app n) hΦ
  refine (cancel_mono (relativeSpecCompletionLevelIso X I B n).hom).mp ?_
  exact (relativeSpecMap_pullback_comp_levelIso b₁ n).trans
    ((congrArg (_ ≫ ·) hn).trans (relativeSpecMap_pullback_comp_levelIso b₂ n).symm)

private lemma pullback_toScheme_zero_comp_fst_zero {X : Scheme.{u}} {I : X.IdealSheafData}
    {B A : QuasicoherentAlgebra X}
    [IsFinite A.obj.relativeSpecToBase] [Etale A.obj.relativeSpecToBase]
    [IsFinite B.obj.relativeSpecToBase] [Etale B.obj.relativeSpecToBase]
    (g₀ : (pullback (Scheme.formalCompletion.toScheme X I 0)).obj (relativeSpecFiniteEtale A) ⟶
      (pullback (Scheme.formalCompletion.toScheme X I 0)).obj (relativeSpecFiniteEtale B)) :
    ((Limits.pullbackSymmetry A.obj.relativeSpecToBase
          (Scheme.formalCompletion.toScheme X I 0)).inv ≫
        g₀.hom.left ≫
          (Limits.pullbackSymmetry B.obj.relativeSpecToBase
            (Scheme.formalCompletion.toScheme X I 0)).hom) ≫
      (relativeSpecCompletionFst X I B).app 0 =
    (relativeSpecCompletionFst X I A).app 0 := by
  let i₀ := Scheme.formalCompletion.toScheme X I 0
  let sA := Limits.pullbackSymmetry A.obj.relativeSpecToBase i₀
  let sB := Limits.pullbackSymmetry B.obj.relativeSpecToBase i₀
  have hw : g₀.hom.left ≫ Limits.pullback.snd B.obj.relativeSpecToBase i₀ =
      Limits.pullback.snd A.obj.relativeSpecToBase i₀ := Over.w g₀.hom
  refine (congrArg (_ ≫ ·) (AdicThickeningSystem.pullback.fst_app (toConstSystem X I)
      (AdicThickeningSystem.ofScheme.map B.obj.relativeSpecToBase) 0)).trans
    (Eq.trans ?_ (AdicThickeningSystem.pullback.fst_app (toConstSystem X I)
      (AdicThickeningSystem.ofScheme.map A.obj.relativeSpecToBase) 0).symm)
  calc (sA.inv ≫ g₀.hom.left ≫ sB.hom) ≫ Limits.pullback.fst i₀ B.obj.relativeSpecToBase
      = sA.inv ≫ g₀.hom.left ≫ (sB.hom ≫ Limits.pullback.fst i₀ B.obj.relativeSpecToBase) :=
        (Category.assoc _ _ _).trans (congrArg (sA.inv ≫ ·) (Category.assoc _ _ _))
    _ = sA.inv ≫ (g₀.hom.left ≫ Limits.pullback.snd B.obj.relativeSpecToBase i₀) :=
        congrArg (sA.inv ≫ g₀.hom.left ≫ ·) (Limits.pullbackSymmetry_hom_comp_fst _ _)
    _ = sA.inv ≫ Limits.pullback.snd A.obj.relativeSpecToBase i₀ :=
        congrArg (sA.inv ≫ ·) hw
    _ = Limits.pullback.fst i₀ A.obj.relativeSpecToBase :=
        Limits.pullbackSymmetry_inv_comp_snd _ _

/-- Surjectivity of `(pullback (toScheme X I 0)).map` on finite étale relative spectra whose
coordinate algebras are finite locally free, assuming formal completion is full and faithful on
finite locally free sheaves. -/
private lemma pullback_toScheme_zero_map_surjective_relativeSpec {X : Scheme.{u}}
    {I : X.IdealSheafData}
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful]
    {B A : QuasicoherentAlgebra X} (hB : Scheme.Modules.isFiniteLocallyFree X B.obj.X)
    (hA : Scheme.Modules.isFiniteLocallyFree X A.obj.X)
    [IsFinite A.obj.relativeSpecToBase] [Etale A.obj.relativeSpecToBase]
    [IsFinite B.obj.relativeSpecToBase] [Etale B.obj.relativeSpecToBase] :
    Function.Surjective
      ((pullback (Scheme.formalCompletion.toScheme X I 0)).map :
        (relativeSpecFiniteEtale A ⟶ relativeSpecFiniteEtale B) → _) := by
  intro g₀
  let i₀ := Scheme.formalCompletion.toScheme X I 0
  let sA := Limits.pullbackSymmetry A.obj.relativeSpecToBase i₀
  let sB := Limits.pullbackSymmetry B.obj.relativeSpecToBase i₀
  let a₀ : (relativeSpecCompletionSystem X I A).X 0 ⟶
      (relativeSpecCompletionSystem X I B).X 0 :=
    sA.inv ≫ g₀.hom.left ≫ sB.hom
  have ha₀ : a₀ ≫ (relativeSpecCompletionFst X I B).app 0 =
      (relativeSpecCompletionFst X I A).app 0 :=
    pullback_toScheme_zero_comp_fst_zero g₀
  let Φ := AdicThickeningSystem.liftOfEtale (relativeSpecCompletionFst X I A)
    (relativeSpecCompletionFst X I B) a₀ ha₀
  have hΦ : Φ ≫ relativeSpecCompletionFst X I B = relativeSpecCompletionFst X I A :=
    AdicThickeningSystem.liftOfEtale_comp _ _ a₀ ha₀
  obtain ⟨b, hb⟩ := quasicoherentAlgebra_exists_hom_of_completion (I := I) hB hA
    (algebraHomOfCompletionHom Φ hΦ) (algebraHomOfCompletionHom_naturality Φ hΦ)
  refine ⟨ofRelativeSpecMap b, ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)⟩
  have hb0 : (relativeSpecCompletionMap (I := I) b).app 0 = a₀ := by
    refine (cancel_epi (relativeSpecCompletionLevelIso X I A 0).hom).mp ?_
    refine (relativeSpecMap_pullback_comp_levelIso b 0).symm.trans ?_
    calc CommMon.relativeSpecMap ((QuasicoherentAlgebra.pullback i₀).map b).hom ≫
            (relativeSpecCompletionLevelIso X I B 0).hom
        = CommMon.relativeSpecMap (algebraHomOfCompletionHom Φ hΦ 0).hom ≫
            (relativeSpecCompletionLevelIso X I B 0).hom :=
          congrArg (fun k ↦ CommMon.relativeSpecMap k.hom ≫ _) (hb 0)
      _ = ((relativeSpecCompletionLevelIso X I A 0).hom ≫ Φ.app 0 ≫
            (relativeSpecCompletionLevelIso X I B 0).inv) ≫
            (relativeSpecCompletionLevelIso X I B 0).hom :=
          congrArg (· ≫ _) (relativeSpecMap_algebraHomOfCompletionHom Φ hΦ 0)
      _ = (relativeSpecCompletionLevelIso X I A 0).hom ≫ a₀ := by
          simp [Φ, AdicThickeningSystem.liftOfEtale_app_zero]
  refine (cancel_mono sB.hom).mp ?_
  exact (pullback_toScheme_zero_map_ofRelativeSpecMap (I := I) b).trans
    ((congrArg (sA.hom ≫ ·) hb0).trans (sA.hom_inv_id_assoc _))

/-- Every finite étale scheme `V` over `X` is isomorphic to `relativeSpecFiniteEtale A` for a
quasicoherent `𝒪_X`-algebra `A` whose underlying module is finite locally free. -/
private lemma exists_iso_relativeSpecFiniteEtale {X : Scheme.{u}} (V : FiniteEtaleScheme X) :
    ∃ (A : QuasicoherentAlgebra X) (_ : Scheme.Modules.isFiniteLocallyFree X A.obj.X)
      (_ : IsFinite A.obj.relativeSpecToBase) (_ : Etale A.obj.relativeSpecToBase),
      Nonempty (relativeSpecFiniteEtale A ≅ V) := by
  let A : QuasicoherentAlgebra X := ⟨V.obj.hom.pushforwardStructureAlgebra, inferInstance⟩
  have hA : Scheme.Modules.isFiniteLocallyFree X A.obj.X :=
    Scheme.Modules.isFiniteLocallyFree_pushforward_unit V.obj.hom
  have hfin : IsFinite A.obj.relativeSpecToBase := by
    rw [← V.obj.hom.relativeSpecFunctionsToScheme_comp]
    infer_instance
  have het : Etale A.obj.relativeSpecToBase := by
    rw [← V.obj.hom.relativeSpecFunctionsToScheme_comp]
    infer_instance
  refine ⟨A, hA, hfin, het,
    ⟨ObjectProperty.isoMk _ (Over.isoMk V.obj.hom.relativeSpecFunctionsIso ?_)⟩⟩
  rw [Scheme.Hom.relativeSpecFunctionsIso_hom]
  exact V.obj.hom.relativeSpecFunctionsToScheme_comp

/-! ### Main theorems -/

/-- If formal completion on finite locally free sheaves is faithful, then base change of finite
étale schemes along the closed immersion `I.subschemeι : V(I) ⟶ X` is faithful
(Stacks, Remark 58.17.2). -/
@[stacks 0EL9]
theorem faithful_pullback_subschemeι_of_toFinitelyPresented_comp_completionFunctor
    (X : Scheme.{u}) (I : X.IdealSheafData)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Faithful := by
  have : (pullback (Scheme.formalCompletion.toScheme X I 0)).Faithful :=
    ⟨fun {V W} u v huv ↦ by
      obtain ⟨A, hA, _, _, ⟨eV⟩⟩ := exists_iso_relativeSpecFiniteEtale V
      obtain ⟨B, hB, _, _, ⟨eW⟩⟩ := exists_iso_relativeSpecFiniteEtale W
      have hinj := pullback_toScheme_zero_map_injective_relativeSpec (I := I) hB hA
      have heq : eV.hom ≫ u ≫ eW.inv = eV.hom ≫ v ≫ eW.inv := by
        apply hinj
        simp only [Functor.map_comp, reassoc_of% huv]
      simpa only [Iso.cancel_iso_hom_left, Iso.cancel_iso_inv_right] using heq⟩
  exact faithful_pullback_subschemeι_of_zero

/-- If the completion functor `Scheme.formalCompletion.completionFunctor X I` on finitely presented
`𝒪_X`-modules is faithful, then base change of finite étale schemes along
`I.subschemeι : V(I) ⟶ X` is faithful (Stacks, Lemma 58.17.1). -/
@[stacks 0EL8]
theorem faithful_pullback_subschemeι_of_completionFunctor
    (X : Scheme.{u}) (I : X.IdealSheafData)
    [(Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Faithful :=
  faithful_pullback_subschemeι_of_toFinitelyPresented_comp_completionFunctor X I

/-- **Fullness of finite étale base change from formal completion on finite locally free sheaves.**
If formal completion on finite locally free `𝒪_X`-modules is full and faithful, then base change of
finite étale schemes along `I.subschemeι : V(I) ⟶ X` is full (Stacks, Remark 58.17.2). -/
@[stacks 0EL9]
theorem full_pullback_subschemeι_of_toFinitelyPresented_comp_completionFunctor
    (X : Scheme.{u}) (I : X.IdealSheafData)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Full := by
  have : (pullback (Scheme.formalCompletion.toScheme X I 0)).Full :=
    ⟨fun {V W} w ↦ by
      obtain ⟨A, hA, _, _, ⟨eV⟩⟩ := exists_iso_relativeSpecFiniteEtale V
      obtain ⟨B, hB, _, _, ⟨eW⟩⟩ := exists_iso_relativeSpecFiniteEtale W
      let G := pullback (Scheme.formalCompletion.toScheme X I 0)
      obtain ⟨u, hu⟩ := pullback_toScheme_zero_map_surjective_relativeSpec (I := I) hB hA
        ((G.mapIso eV).hom ≫ w ≫ (G.mapIso eW).inv)
      refine ⟨eV.inv ≫ u ≫ eW.hom, ?_⟩
      simp [G, hu]⟩
  exact full_pullback_subschemeι_of_zero

/-- **Fullness of finite étale base change from formal completion on finitely presented sheaves.**
If `Scheme.formalCompletion.completionFunctor X I` is full and faithful, then base change of finite
étale schemes along `I.subschemeι : V(I) ⟶ X` is full (Stacks, Lemma 58.17.1). -/
@[stacks 0EL8]
theorem full_pullback_subschemeι_of_completionFunctor
    (X : Scheme.{u}) (I : X.IdealSheafData)
    [(Scheme.formalCompletion.completionFunctor X I).Full]
    [(Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).Full :=
  full_pullback_subschemeι_of_toFinitelyPresented_comp_completionFunctor X I

/-- **Full faithfulness of finite étale base change from formal completion on finite locally free
sheaves** (Stacks, Remark 58.17.2). -/
@[stacks 0EL9]
def fullyFaithfulPullbackSubschemeιOfToFinitelyPresentedCompCompletionFunctor
    (X : Scheme.{u}) (I : X.IdealSheafData)
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙
      Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).FullyFaithful :=
  have := faithful_pullback_subschemeι_of_toFinitelyPresented_comp_completionFunctor X I
  have := full_pullback_subschemeι_of_toFinitelyPresented_comp_completionFunctor X I
  .ofFullyFaithful _

/-- **Full faithfulness of finite étale base change from formal completion on finitely presented
sheaves** (Stacks, Lemma 58.17.1). -/
@[stacks 0EL8]
def fullyFaithfulPullbackSubschemeιOfCompletionFunctor
    (X : Scheme.{u}) (I : X.IdealSheafData)
    [(Scheme.formalCompletion.completionFunctor X I).Full]
    [(Scheme.formalCompletion.completionFunctor X I).Faithful] :
    (pullback I.subschemeι).FullyFaithful :=
  fullyFaithfulPullbackSubschemeιOfToFinitelyPresentedCompCompletionFunctor X I

end TauCeti.FiniteEtaleScheme

end
