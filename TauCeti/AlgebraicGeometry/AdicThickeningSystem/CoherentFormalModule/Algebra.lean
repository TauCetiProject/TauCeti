/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Basic
public import TauCeti.AlgebraicGeometry.RelativeSpec.BaseChange
import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Etale
import TauCeti.AlgebraicGeometry.RelativeSpec.Equivalence

/-!
# Formal completion of quasi-coherent algebras and their relative spectra

Let `X` be a scheme and `I` an ideal sheaf on `X`, with formal completion `X.formalCompletion I`
having `n`-th level `V(I ^ (n + 1))` and closed immersion `toScheme X I n : V(I ^ (n + 1)) ⟶ X`.
For a quasi-coherent commutative `𝒪_X`-algebra `A` with relative spectrum `p_A : Spec_X A ⟶ X`,
each level of the formal completion of `Spec_X A` along `V(I.comap p_A)` is the scheme-theoretic
inverse image of `V(I ^ (n + 1))` (`Scheme.formalCompletion.isPullback_map_app`), while base change
of relative spectra identifies the same fibre product with `Spec_{V(I ^ (n + 1))} (t_n^* A)`
(`isPullback_relativeSpecPullbackFst`). Comparing the two pullback cones produces canonical
levelwise isomorphisms `Scheme.formalCompletion.relativeSpecLevelIso X I A n` compatible with both
morphisms of algebras and the infinitesimal transitions.

When `completionFunctor X I` is faithful (respectively fully faithful) on a monoidal full
subcategory `P` of finitely presented `𝒪_X`-modules containing the underlying modules of `A` and
`B`:

* an `𝒪_X`-linear map `B ⟶ A` is an `𝒪_X`-algebra homomorphism if and only if its reductions to all
  levels `V(I ^ (n + 1))` are algebra homomorphisms (`isMonHom_iff_forall_pullback_toScheme`);
* if `Spec_X B ⟶ X` is formally unramified and `completionFunctor X I` is faithful on `P`,
  algebra homomorphisms `B ⟶ A` are determined by their reduction to the initial level `V(I)`
  (`pullback_toScheme_zero_map_injective`);
* if `Spec_X B ⟶ X` is étale and `completionFunctor X I` is fully faithful on `P`, reduction to
  `V(I)` is bijective on algebra homomorphisms `B ⟶ A` (`pullback_toScheme_zero_map_bijective`):
  any initial algebra map induces a `V(I)`-morphism `Spec_{V(I)} (t_0^* A) ⟶ Spec_{V(I)} (t_0^* B)`,
  which lifts uniquely across the tower of thickenings by `AdicThickeningSystem.liftOfEtale`,
  translates back via `relativeSpecEquiv` to a compatible system of algebra maps on all levels,
  algebraizes as a module morphism by fullness of completion, and is an algebra map by
  faithfulness of completion on `P`.

Working relative to an arbitrary monoidal property `P ≤ isFinitePresentation` allows the theory to
apply both when `completionFunctor X I` is fully faithful on all finitely presented sheaves and
when it is only fully faithful on `FiniteLocallyFreeSheaf X` (as in local purity, Stacks Tags
`0EKP` and `0EKS`).

## Main declarations

* `AlgebraicGeometry.Scheme.formalCompletion.prop_map_app`: stability of base-change-invariant
  morphism properties across the levels of `formalCompletion.map`;
* `AlgebraicGeometry.Scheme.formalCompletion.relativeSpecLevelIso`: canonical isomorphism between
  level `n` of the formal completion of `Spec_X A` and `Spec_{V(I ^ (n + 1))} (t_n^* A)`;
* `TauCeti.AlgebraicGeometry.QuasicoherentAlgebra.isMonHom_pullback_map_iff`: characterization of
  when the pullback of a module morphism between quasi-coherent algebras is a monoid morphism;
* `AlgebraicGeometry.Scheme.formalCompletion.isMonHom_iff_forall_pullback_toScheme`: monoid-morphism
  descent from all infinitesimal levels via faithfulness of completion on a monoidal subcategory;
* `AlgebraicGeometry.Scheme.formalCompletion.pullback_toScheme_zero_map_injective` and
  `AlgebraicGeometry.Scheme.formalCompletion.pullback_toScheme_zero_map_bijective`: faithfulness and
  full faithfulness of reduction to `V(I)` for quasi-coherent algebras with formally unramified or
  étale relative spectrum.

## References

* [The Stacks Project, Lemma 58.17.1 (Tag 0EL8)](https://stacks.math.columbia.edu/tag/0EL8)
-/

public section

open CategoryTheory Limits MonoidalCategory Opposite AlgebraicGeometry
open scoped MonObj
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.AdicThickeningSystem

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry.QuasicoherentAlgebra

/-- A module morphism `φ : B.obj.X ⟶ A.obj.X` between quasi-coherent `𝒪_X`-algebras pulls back to an
algebra homomorphism along `f : Y ⟶ X` if and only if `f^*` identifies `η_B ≫ φ` with `η_A` and
`μ_B ≫ φ` with `(φ ⊗ₘ φ) ≫ μ_A`. -/
theorem isMonHom_pullback_map_iff {X Y : Scheme.{u}} (f : Y ⟶ X)
    {A B : QuasicoherentAlgebra X} (φ : B.obj.X ⟶ A.obj.X) :
    IsMonHom (eqToHom (pullback_obj_X f B) ≫ (Scheme.Modules.pullback f).map φ ≫
        eqToHom (pullback_obj_X f A).symm) ↔
      (Scheme.Modules.pullback f).map (η[B.obj.X] ≫ φ) =
          (Scheme.Modules.pullback f).map η[A.obj.X] ∧
        (Scheme.Modules.pullback f).map (μ[B.obj.X] ≫ φ) =
          (Scheme.Modules.pullback f).map ((φ ⊗ₘ φ) ≫ μ[A.obj.X]) := by
  let ψ : ((pullback f).obj B).obj.X ⟶ ((pullback f).obj A).obj.X :=
    eqToHom (pullback_obj_X f B) ≫ (Scheme.Modules.pullback f).map φ ≫
      eqToHom (pullback_obj_X f A).symm
  have hone : η[((pullback f).obj B).obj.X] ≫ ψ = η[((pullback f).obj A).obj.X] ↔
      (Scheme.Modules.pullback f).map (η[B.obj.X] ≫ φ) =
        (Scheme.Modules.pullback f).map η[A.obj.X] := by
    dsimp only [ψ]
    rw [pullback_obj_one f B, pullback_obj_one f A]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      ← Functor.map_comp_assoc]
    rw [cancel_epi (Scheme.Modules.pullbackObjUnitIso f).inv,
      cancel_mono (eqToHom (pullback_obj_X f A).symm)]
  have hδA : IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) A.obj.X A.obj.X) :=
    Scheme.Modules.isIso_pullback_δ_of_isQuasicoherent f A.obj.X A.obj.X
  have hδB : IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) B.obj.X B.obj.X) :=
    Scheme.Modules.isIso_pullback_δ_of_isQuasicoherent f B.obj.X B.obj.X
  have hδnat : ((Scheme.Modules.pullback f).map φ ⊗ₘ (Scheme.Modules.pullback f).map φ) ≫
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) A.obj.X A.obj.X) =
      inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) B.obj.X B.obj.X) ≫
        (Scheme.Modules.pullback f).map (φ ⊗ₘ φ) := by
    rw [IsIso.comp_inv_eq, Category.assoc, ← Functor.OplaxMonoidal.δ_natural,
      IsIso.inv_hom_id_assoc]
  have hmul : μ[((pullback f).obj B).obj.X] ≫ ψ = (ψ ⊗ₘ ψ) ≫ μ[((pullback f).obj A).obj.X] ↔
      (Scheme.Modules.pullback f).map (μ[B.obj.X] ≫ φ) =
        (Scheme.Modules.pullback f).map ((φ ⊗ₘ φ) ≫ μ[A.obj.X]) := by
    have hψtensor : (ψ ⊗ₘ ψ) ≫
        (eqToHom (pullback_obj_X f A) ⊗ₘ eqToHom (pullback_obj_X f A)) =
        (eqToHom (pullback_obj_X f B) ⊗ₘ eqToHom (pullback_obj_X f B)) ≫
          ((Scheme.Modules.pullback f).map φ ⊗ₘ (Scheme.Modules.pullback f).map φ) := by
      dsimp only [ψ]
      rw [← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom]
      simp
    rw [pullback_obj_mul f B, pullback_obj_mul f A]
    calc
      ((eqToHom (pullback_obj_X f B) ⊗ₘ eqToHom (pullback_obj_X f B)) ≫
          inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) B.obj.X B.obj.X) ≫
            (Scheme.Modules.pullback f).map μ[B.obj.X] ≫ eqToHom (pullback_obj_X f B).symm) ≫ ψ =
        (ψ ⊗ₘ ψ) ≫ (eqToHom (pullback_obj_X f A) ⊗ₘ eqToHom (pullback_obj_X f A)) ≫
          inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) A.obj.X A.obj.X) ≫
            (Scheme.Modules.pullback f).map μ[A.obj.X] ≫ eqToHom (pullback_obj_X f A).symm ↔
        (eqToHom (pullback_obj_X f B) ⊗ₘ eqToHom (pullback_obj_X f B)) ≫
          inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) B.obj.X B.obj.X) ≫
            (Scheme.Modules.pullback f).map (μ[B.obj.X] ≫ φ) ≫
              eqToHom (pullback_obj_X f A).symm =
        (eqToHom (pullback_obj_X f B) ⊗ₘ eqToHom (pullback_obj_X f B)) ≫
          inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) B.obj.X B.obj.X) ≫
            (Scheme.Modules.pullback f).map ((φ ⊗ₘ φ) ≫ μ[A.obj.X]) ≫
              eqToHom (pullback_obj_X f A).symm := by
          have hlhs :
              ((eqToHom (pullback_obj_X f B) ⊗ₘ eqToHom (pullback_obj_X f B)) ≫
                inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) B.obj.X B.obj.X) ≫
                  (Scheme.Modules.pullback f).map μ[B.obj.X] ≫
                    eqToHom (pullback_obj_X f B).symm) ≫ ψ =
              (eqToHom (pullback_obj_X f B) ⊗ₘ eqToHom (pullback_obj_X f B)) ≫
                inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) B.obj.X B.obj.X) ≫
                  (Scheme.Modules.pullback f).map (μ[B.obj.X] ≫ φ) ≫
                    eqToHom (pullback_obj_X f A).symm := by
            dsimp only [ψ]
            simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
              Functor.map_comp]
          have hrhs :
              (ψ ⊗ₘ ψ) ≫ (eqToHom (pullback_obj_X f A) ⊗ₘ eqToHom (pullback_obj_X f A)) ≫
                inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) A.obj.X A.obj.X) ≫
                  (Scheme.Modules.pullback f).map μ[A.obj.X] ≫
                    eqToHom (pullback_obj_X f A).symm =
              (eqToHom (pullback_obj_X f B) ⊗ₘ eqToHom (pullback_obj_X f B)) ≫
                inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) B.obj.X B.obj.X) ≫
                  (Scheme.Modules.pullback f).map ((φ ⊗ₘ φ) ≫ μ[A.obj.X]) ≫
                    eqToHom (pullback_obj_X f A).symm := by
            rw [← Category.assoc (ψ ⊗ₘ ψ), hψtensor, Category.assoc, ← Category.assoc
              ((Scheme.Modules.pullback f).map φ ⊗ₘ (Scheme.Modules.pullback f).map φ),
              hδnat, Category.assoc, ← Functor.map_comp_assoc]
          rw [hlhs, hrhs]
      _ ↔ _ := by
          rw [cancel_epi (eqToHom (pullback_obj_X f B) ⊗ₘ eqToHom (pullback_obj_X f B)),
            cancel_epi (inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) B.obj.X B.obj.X)),
            cancel_mono (eqToHom (pullback_obj_X f A).symm)]
  exact ⟨fun h ↦ ⟨hone.mp h.one_hom, hmul.mp h.mul_hom⟩, fun h ↦ ⟨hone.mpr h.1, hmul.mpr h.2⟩⟩

end TauCeti.AlgebraicGeometry.QuasicoherentAlgebra

namespace AlgebraicGeometry.Scheme.formalCompletion

section MorphismProperties

variable {X Y : Scheme.{u}} {I : X.IdealSheafData} {J : Y.IdealSheafData}

/-- If `V(I)` is the scheme-theoretic inverse image of `V(J)` under `f : X ⟶ Y`, any morphism
property `P` stable under base change transfers from `f` to every level of
`formalCompletion.map f`. -/
theorem prop_map_app (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (f : X ⟶ Y) (hf : J.comap f = I) (hP : P f) (n : ℕ) :
    P ((map f hf.le).app n) :=
  P.of_isPullback (isPullback_map_app f hf n) hP

/-- The morphism of formal completions induced by a formally unramified morphism `f : X ⟶ Y`, for
the inverse image of an ideal sheaf on `Y`, is formally unramified at every level. -/
instance formallyUnramified_map_app (f : X ⟶ Y) [FormallyUnramified f] (n : ℕ) :
    FormallyUnramified ((map (I := J.comap f) f le_rfl).app n) :=
  prop_map_app (@FormallyUnramified) f rfl ‹_› n

/-- The morphism of formal completions induced by an étale morphism `f : X ⟶ Y`, for the inverse
image of an ideal sheaf on `Y`, is étale at every level. -/
instance etale_map_app (f : X ⟶ Y) [Etale f] (n : ℕ) :
    Etale ((map (I := J.comap f) f le_rfl).app n) :=
  prop_map_app (@Etale) f rfl ‹_› n

end MorphismProperties

section RelativeSpec

variable (X : Scheme.{u}) (I : X.IdealSheafData)

/-- Level `n` of the formal completion of `Spec_X A` along the preimage of `I` is canonically
isomorphic to the relative spectrum over `V(I ^ (n + 1))` of the pulled-back algebra `t_n^* A`:
both schemes are fibre products of `Spec_X A` and `V(I ^ (n + 1))` over `X`. -/
def relativeSpecLevelIso (A : QuasicoherentAlgebra X) (n : ℕ) :
    (A.obj.relativeSpec.formalCompletion (I.comap A.obj.relativeSpecToBase)).X n ≅
      ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A).obj.relativeSpec :=
  (isPullback_map_app A.obj.relativeSpecToBase rfl n).isoIsPullback _ _
    (isPullback_relativeSpecPullbackFst A (toScheme X I n))

/-- The forward comparison `relativeSpecLevelIso` commutes with the projections to `Spec_X A`. -/
@[reassoc (attr := simp)]
theorem relativeSpecLevelIso_hom_relativeSpecPullbackFst (A : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecLevelIso X I A n).hom ≫ relativeSpecPullbackFst A (toScheme X I n) =
      toScheme A.obj.relativeSpec (I.comap A.obj.relativeSpecToBase) n :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The forward comparison `relativeSpecLevelIso` commutes with the projections to
`V(I ^ (n + 1))`. -/
@[reassoc (attr := simp)]
theorem relativeSpecLevelIso_hom_relativeSpecToBase (A : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecLevelIso X I A n).hom ≫
        ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A).obj.relativeSpecToBase =
      (map (I := I.comap A.obj.relativeSpecToBase) A.obj.relativeSpecToBase le_rfl).app n :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The inverse comparison `relativeSpecLevelIso` commutes with the projections to `Spec_X A`. -/
@[reassoc (attr := simp)]
theorem relativeSpecLevelIso_inv_toScheme (A : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecLevelIso X I A n).inv ≫
        toScheme A.obj.relativeSpec (I.comap A.obj.relativeSpecToBase) n =
      relativeSpecPullbackFst A (toScheme X I n) :=
  IsPullback.isoIsPullback_inv_fst _ _ _ _

/-- The inverse comparison `relativeSpecLevelIso` commutes with the projections to
`V(I ^ (n + 1))`. -/
@[reassoc (attr := simp)]
theorem relativeSpecLevelIso_inv_map_app (A : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecLevelIso X I A n).inv ≫
        (map (I := I.comap A.obj.relativeSpecToBase) A.obj.relativeSpecToBase le_rfl).app n =
      ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A).obj.relativeSpecToBase :=
  IsPullback.isoIsPullback_inv_snd _ _ _ _

variable {X I}

/-- Under `relativeSpecLevelIso`, the morphism of formal completions induced by `Spec_X ψ` at level
`n` corresponds to `Spec_{V(I ^ (n + 1))} (t_n^* ψ)`. -/
theorem relativeSpecLevelIso_inv_map_app_hom {A B : QuasicoherentAlgebra X} (ψ : B ⟶ A)
    (hcomap : (I.comap B.obj.relativeSpecToBase).comap (CommMon.relativeSpecMap ψ.hom) ≤
      I.comap A.obj.relativeSpecToBase) (n : ℕ) :
    (relativeSpecLevelIso X I A n).inv ≫
        (map (CommMon.relativeSpecMap ψ.hom) hcomap).app n ≫
          (relativeSpecLevelIso X I B n).hom =
      CommMon.relativeSpecMap ((QuasicoherentAlgebra.pullback (toScheme X I n)).map ψ).hom := by
  refine (isPullback_relativeSpecPullbackFst B (toScheme X I n)).hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, relativeSpecLevelIso_hom_relativeSpecPullbackFst,
      map_app_toScheme, relativeSpecLevelIso_inv_toScheme_assoc,
      relativeSpecMap_pullback_map_relativeSpecPullbackFst]
  · have hcomp :
        (map (CommMon.relativeSpecMap ψ.hom) hcomap).app n ≫
            (map (I := I.comap B.obj.relativeSpecToBase) B.obj.relativeSpecToBase le_rfl).app n =
          (map (I := I.comap A.obj.relativeSpecToBase) A.obj.relativeSpecToBase le_rfl).app n := by
      rw [← cancel_mono (toScheme X I n), Category.assoc, map_app_toScheme, map_app_toScheme_assoc,
        CommMon.relativeSpecMap_relativeSpecToBase, map_app_toScheme]
    rw [Category.assoc, Category.assoc, relativeSpecLevelIso_hom_relativeSpecToBase, hcomp,
      relativeSpecLevelIso_inv_map_app, CommMon.relativeSpecMap_relativeSpecToBase]

private def pullbackCongrAlgebra {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (hf : f = g) :
    QuasicoherentAlgebra.pullback f ≅ QuasicoherentAlgebra.pullback g :=
  eqToIso (hf ▸ rfl)

private lemma eqToHom_conj_comp {𝒞 : Type*} [Category 𝒞] {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : 𝒞}
    (e₁ : X₁ = X₂) (e₂ : Y₁ = Y₂) (e₃ : Z₁ = Z₂) (u : X₂ ⟶ Y₂) (v : Y₂ ⟶ Z₂) :
    (eqToHom e₁ ≫ u ≫ eqToHom e₂.symm) ≫ (eqToHom e₂ ≫ v ≫ eqToHom e₃.symm) =
      eqToHom e₁ ≫ (u ≫ v) ≫ eqToHom e₃.symm := by
  subst e₁ e₂ e₃
  simp

private lemma cancel_eqToHom_conj {𝒞 : Type*} [Category 𝒞] {X₁ X₂ Y₁ Y₂ : 𝒞}
    (e₁ : X₁ = X₂) (e₂ : Y₁ = Y₂) {u v : X₂ ⟶ Y₂}
    (h : eqToHom e₁ ≫ u ≫ eqToHom e₂.symm = eqToHom e₁ ≫ v ≫ eqToHom e₂.symm) :
    u = v := by
  subst e₁ e₂
  simpa using h

private lemma eqToHom_eqToHom_symm_conj {𝒞 : Type*} [Category 𝒞] {X₁ X₂ Y₁ Y₂ : 𝒞}
    (e₁ : X₁ = X₂) (e₂ : Y₁ = Y₂) (v : X₁ ⟶ Y₁) :
    eqToHom e₁ ≫ (eqToHom e₁.symm ≫ v ≫ eqToHom e₂) ≫ eqToHom e₂.symm = v := by
  subst e₁ e₂
  simp

private lemma eq_of_relativeSpecMap_eq {S : Scheme.{u}} {A B : QuasicoherentAlgebra S}
    {ψ₁ ψ₂ : B ⟶ A} (h : CommMon.relativeSpecMap ψ₁.hom = CommMon.relativeSpecMap ψ₂.hom) :
    ψ₁ = ψ₂ :=
  Quiver.Hom.op_inj <| (relativeSpec S).map_injective <|
    MorphismProperty.Over.Hom.ext ((relativeSpec_map_left ψ₁.op).trans
      (h.trans (relativeSpec_map_left ψ₂.op).symm))

private lemma pullbackCongrAlgebra_hom_app_hom_hom_hom {Y Z : Scheme.{u}} {f g : Y ⟶ Z}
    (hf : f = g) (A : QuasicoherentAlgebra Z) :
    ((pullbackCongrAlgebra hf).hom.app A).hom.hom.hom =
      eqToHom (QuasicoherentAlgebra.pullback_obj_X f A) ≫
        (Scheme.Modules.pullbackCongr hf).hom.app A.obj.X ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X g A).symm := by
  subst hf
  simp only [pullbackCongrAlgebra, Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, ObjectProperty.FullSubcategory.id_hom, CommMon.id_hom, Category.id_comp]
  exact ((eqToHom_trans (C := Y.Modules) _ _).trans (eqToHom_refl _ _)).symm

private lemma relativeSpecMap_pullbackCongrAlgebra_hom_app_relativeSpecPullbackFst
    {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (hf : f = g) (A : QuasicoherentAlgebra Z) :
    CommMon.relativeSpecMap ((pullbackCongrAlgebra hf).hom.app A).hom ≫
        relativeSpecPullbackFst A f =
      relativeSpecPullbackFst A g := by
  subst hf
  simp [pullbackCongrAlgebra]

/-- The algebra reduction isomorphism `(ι n)^* (t_{n + 1}^* A) ≅ t_n^* A` along a transition of
`X.formalCompletion I`. -/
private def algebraTransitionIso (A : QuasicoherentAlgebra X) (n : ℕ) :
    (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).obj
        ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj A) ≅
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A :=
  (QuasicoherentAlgebra.pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1)) ≪≫
    pullbackCongrAlgebra (ι_toScheme X I n)).app A

private lemma relativeSpecLevelIso_inv_ι_hom (A : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecLevelIso X I A n).inv ≫
        (A.obj.relativeSpec.formalCompletion (I.comap A.obj.relativeSpecToBase)).ι n ≫
          (relativeSpecLevelIso X I A (n + 1)).hom =
      CommMon.relativeSpecMap (algebraTransitionIso (I := I) A n).hom.hom ≫
        relativeSpecPullbackFst ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj A)
          ((X.formalCompletion I).ι n) := by
  refine (isPullback_relativeSpecPullbackFst A (toScheme X I (n + 1))).hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, relativeSpecLevelIso_hom_relativeSpecPullbackFst,
      ι_toScheme, relativeSpecLevelIso_inv_toScheme]
    dsimp only [algebraTransitionIso, Iso.trans_hom, Iso.app_hom, NatTrans.comp_app,
      ObjectProperty.FullSubcategory.comp_hom]
    rw [CommMon.relativeSpecMap_comp, Category.assoc, Category.assoc,
      ← relativeSpecPullbackFst_comp,
      relativeSpecMap_pullbackCongrAlgebra_hom_app_relativeSpecPullbackFst]
  · rw [Category.assoc, Category.assoc, relativeSpecLevelIso_hom_relativeSpecToBase,
      (map (I := I.comap A.obj.relativeSpecToBase) A.obj.relativeSpecToBase le_rfl).naturality,
      relativeSpecLevelIso_inv_map_app_assoc, Category.assoc,
      relativeSpecPullbackFst_relativeSpecToBase,
      CommMon.relativeSpecMap_relativeSpecToBase_assoc]

private lemma algebraTransitionIso_hom_hom_hom_hom (A : QuasicoherentAlgebra X)
    (hA : A.obj.X.IsFinitePresentation) (n : ℕ) :
    (algebraTransitionIso (I := I) A n).hom.hom.hom.hom =
      eqToHom ((QuasicoherentAlgebra.pullback_obj_X ((X.formalCompletion I).ι n) _).trans
          (congrArg (Scheme.Modules.pullback ((X.formalCompletion I).ι n)).obj
            (QuasicoherentAlgebra.pullback_obj_X (toScheme X I (n + 1)) A))) ≫
        (((completionFunctor X I).obj ⟨A.obj.X, hA⟩).transitionIso n).hom ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A).symm := by
  dsimp only [algebraTransitionIso, Iso.trans_hom, Iso.app_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, CommMon.comp_hom, completionFunctor_obj_transitionIso]
  rw [QuasicoherentAlgebra.pullbackComp_hom_app_hom_hom_hom,
    pullbackCongrAlgebra_hom_app_hom_hom_hom]
  exact eqToHom_conj_comp (𝒞 := ((X.formalCompletion I).X n).Modules) _ _
    (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A) _ _

private lemma conjugate_eqToHom_naturality {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒟 ⥤ 𝒞)
    {B₁' B₁ A₁' A₁ : 𝒟} {B₀' B₀ A₀' A₀ B₀₁' A₀₁' : 𝒞}
    (eB₁ : B₁' = B₁) (eA₁ : A₁' = A₁) (eB₀ : B₀' = B₀) (eA₀ : A₀' = A₀)
    (eB₀₁ : B₀₁' = F.obj B₁') (eA₀₁ : A₀₁' = F.obj A₁')
    {u : B₁' ⟶ A₁'} {v : B₀' ⟶ A₀'} {tA : F.obj A₁ ⟶ A₀} {tB : F.obj B₁ ⟶ B₀}
    (h : (eqToHom eB₀₁ ≫ F.map u ≫ eqToHom eA₀₁.symm) ≫
        (eqToHom (eA₀₁.trans (congrArg F.obj eA₁)) ≫ tA ≫ eqToHom eA₀.symm) =
      (eqToHom (eB₀₁.trans (congrArg F.obj eB₁)) ≫ tB ≫ eqToHom eB₀.symm) ≫ v) :
    F.map (eqToHom eB₁.symm ≫ u ≫ eqToHom eA₁) ≫ tA =
      tB ≫ (eqToHom eB₀.symm ≫ v ≫ eqToHom eA₀) := by
  subst eB₁ eA₁ eB₀ eA₀ eB₀₁ eA₀₁
  simpa using h

/-- If `completionFunctor X I` is faithful on a monoidal full subcategory `P` of finitely presented
`𝒪_X`-modules containing `A` and `B`, then an `𝒪_X`-linear map `φ : B.obj.X ⟶ A.obj.X` is an
algebra homomorphism if and only if its reductions to all levels of `X.formalCompletion I` are
algebra homomorphisms. -/
theorem isMonHom_iff_forall_pullback_toScheme {P : ObjectProperty X.Modules} [P.IsMonoidal]
    (hP : ∀ M, P M → M.IsFinitePresentation)
    (hfaith : ∀ ⦃M N : FinitelyPresentedSheaf X⦄, P M.obj → P N.obj →
      Function.Injective (fun f : M ⟶ N ↦ (completionFunctor X I).map f))
    {A B : QuasicoherentAlgebra X} (hA : P A.obj.X) (hB : P B.obj.X)
    (φ : B.obj.X ⟶ A.obj.X) :
    IsMonHom φ ↔ ∀ n, IsMonHom
      (eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B) ≫
        (Scheme.Modules.pullback (toScheme X I n)).map φ ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A).symm) := by
  refine ⟨fun h n ↦ ?_, fun h ↦ ?_⟩
  · refine (QuasicoherentAlgebra.isMonHom_pullback_map_iff (toScheme X I n) φ).mpr ?_
    rw [h.one_hom, h.mul_hom]
    exact ⟨rfl, rfl⟩
  · have h' := fun n ↦ (QuasicoherentAlgebra.isMonHom_pullback_map_iff (toScheme X I n) φ).mp (h n)
    have hone : η[B.obj.X] ≫ φ = η[A.obj.X] :=
      congrArg (·.hom) <|
        hfaith (M := ⟨𝟙_ X.Modules, hP _ P.prop_unit⟩) (N := ⟨A.obj.X, hP _ hA⟩) P.prop_unit hA
          (a₁ := ObjectProperty.homMk (η[B.obj.X] ≫ φ))
          (a₂ := ObjectProperty.homMk η[A.obj.X])
          (CoherentFormalModule.hom_ext fun n ↦ (h' n).1)
    have hmul : μ[B.obj.X] ≫ φ = (φ ⊗ₘ φ) ≫ μ[A.obj.X] :=
      congrArg (·.hom) <|
        hfaith (M := ⟨B.obj.X ⊗ B.obj.X, hP _ (P.prop_tensor hB hB)⟩)
          (N := ⟨A.obj.X, hP _ hA⟩) (P.prop_tensor hB hB) hA
          (a₁ := ObjectProperty.homMk (μ[B.obj.X] ≫ φ))
          (a₂ := ObjectProperty.homMk ((φ ⊗ₘ φ) ≫ μ[A.obj.X]))
          (CoherentFormalModule.hom_ext fun n ↦ (h' n).2)
    exact ⟨hone, hmul⟩

/-- **Faithfulness of reduction to `V(I)` for formally unramified quasi-coherent algebras.** If
`completionFunctor X I` is faithful on a full subcategory `P` of finitely presented `𝒪_X`-modules
containing `A` and `B`, and `Spec_X B ⟶ X` is formally unramified, then algebra homomorphisms
`B ⟶ A` are uniquely determined by their pullback to `V(I)`. -/
@[stacks 0EL8]
theorem pullback_toScheme_zero_map_injective
    {P : ObjectProperty X.Modules}
    (hP : ∀ M, P M → M.IsFinitePresentation)
    (hfaith : ∀ ⦃M N : FinitelyPresentedSheaf X⦄, P M.obj → P N.obj →
      Function.Injective (fun f : M ⟶ N ↦ (completionFunctor X I).map f))
    {A B : QuasicoherentAlgebra X} (hA : P A.obj.X) (hB : P B.obj.X)
    [FormallyUnramified B.obj.relativeSpecToBase] :
    Function.Injective
      (fun ψ : B ⟶ A ↦ (QuasicoherentAlgebra.pullback (toScheme X I 0)).map ψ) := by
  intro ψ₁ ψ₂ h₀
  dsimp only at h₀
  have hc₁ : (I.comap B.obj.relativeSpecToBase).comap (CommMon.relativeSpecMap ψ₁.hom) ≤
      I.comap A.obj.relativeSpecToBase := by
    rw [← Scheme.IdealSheafData.comap_comp, CommMon.relativeSpecMap_relativeSpecToBase]
  have hc₂ : (I.comap B.obj.relativeSpecToBase).comap (CommMon.relativeSpecMap ψ₂.hom) ≤
      I.comap A.obj.relativeSpecToBase := by
    rw [← Scheme.IdealSheafData.comap_comp, CommMon.relativeSpecMap_relativeSpecToBase]
  let πB := map (I := I.comap B.obj.relativeSpecToBase) B.obj.relativeSpecToBase le_rfl
  let f₁ := map (CommMon.relativeSpecMap ψ₁.hom) hc₁
  let f₂ := map (CommMon.relativeSpecMap ψ₂.hom) hc₂
  have hf_over : f₁ ≫ πB = f₂ ≫ πB := by
    rw [map_comp, map_comp]
    ext n
    rw [← cancel_mono (toScheme X I n), map_app_toScheme, map_app_toScheme,
      CommMon.relativeSpecMap_relativeSpecToBase, CommMon.relativeSpecMap_relativeSpecToBase]
  have hf₀ : f₁.app 0 = f₂.app 0 := by
    rw [← cancel_epi (relativeSpecLevelIso X I A 0).inv,
      ← cancel_mono (relativeSpecLevelIso X I B 0).hom]
    exact (relativeSpecLevelIso_inv_map_app_hom ψ₁ hc₁ 0).trans <|
      (congrArg (fun ψ ↦ CommMon.relativeSpecMap ψ.hom) h₀).trans
        (relativeSpecLevelIso_inv_map_app_hom ψ₂ hc₂ 0).symm
  have hf_eq : f₁ = f₂ := AdicThickeningSystem.hom_ext_of_formallyUnramified πB hf_over hf₀
  have hψ_all (n : ℕ) :
      (QuasicoherentAlgebra.pullback (toScheme X I n)).map ψ₁ =
        (QuasicoherentAlgebra.pullback (toScheme X I n)).map ψ₂ := by
    apply eq_of_relativeSpecMap_eq
    have hfn : (map (CommMon.relativeSpecMap ψ₁.hom) hc₁).app n =
        (map (CommMon.relativeSpecMap ψ₂.hom) hc₂).app n :=
      congrArg (fun f ↦ f.app n) hf_eq
    exact (relativeSpecLevelIso_inv_map_app_hom ψ₁ hc₁ n).symm.trans <|
      (congrArg (fun u ↦ (relativeSpecLevelIso X I A n).inv ≫ u ≫
        (relativeSpecLevelIso X I B n).hom) hfn).trans
          (relativeSpecLevelIso_inv_map_app_hom ψ₂ hc₂ n)
  have hmod_all (n : ℕ) :
      (Scheme.Modules.pullback (toScheme X I n)).map ψ₁.hom.hom.hom =
        (Scheme.Modules.pullback (toScheme X I n)).map ψ₂.hom.hom.hom := by
    have hn := congrArg (fun g ↦ g.hom.hom.hom) (hψ_all n)
    simp only [QuasicoherentAlgebra.pullback_map_hom_hom_hom] at hn
    exact cancel_eqToHom_conj (𝒞 := ((X.formalCompletion I).X n).Modules)
      (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B)
      (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A) hn
  have hmod : ψ₁.hom.hom.hom = ψ₂.hom.hom.hom :=
    congrArg (·.hom) <|
      hfaith (M := ⟨B.obj.X, hP _ hB⟩) (N := ⟨A.obj.X, hP _ hA⟩) hB hA
        (a₁ := ObjectProperty.homMk ψ₁.hom.hom.hom)
        (a₂ := ObjectProperty.homMk ψ₂.hom.hom.hom) (CoherentFormalModule.hom_ext hmod_all)
  exact ObjectProperty.hom_ext _ (CommMon.hom_ext _ _ hmod)

private lemma pullback_map_conjugate_transition {A B : QuasicoherentAlgebra X}
    (hA : A.obj.X.IsFinitePresentation) (hB : B.obj.X.IsFinitePresentation) (n : ℕ)
    (ψn : (QuasicoherentAlgebra.pullback (toScheme X I n)).obj B ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A)
    (ψsucc : (QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj B ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj A)
    (hnat : (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map ψsucc ≫
      (algebraTransitionIso (I := I) A n).hom =
        (algebraTransitionIso (I := I) B n).hom ≫ ψn) :
    (Scheme.Modules.pullback ((X.formalCompletion I).ι n)).map
        (eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I (n + 1)) B).symm ≫
          ψsucc.hom.hom.hom ≫
            eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I (n + 1)) A)) ≫
      (((completionFunctor X I).obj ⟨A.obj.X, hA⟩).transitionIso n).hom =
    (((completionFunctor X I).obj ⟨B.obj.X, hB⟩).transitionIso n).hom ≫
      (eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B).symm ≫
        ψn.hom.hom.hom ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A)) := by
  have h := congrArg (fun g ↦ g.hom.hom.hom) hnat
  simp only [ObjectProperty.FullSubcategory.comp_hom, CommMon.comp_hom,
    QuasicoherentAlgebra.pullback_map_hom_hom_hom, algebraTransitionIso_hom_hom_hom_hom A hA n,
    algebraTransitionIso_hom_hom_hom_hom B hB n] at h
  exact conjugate_eqToHom_naturality
    (Scheme.Modules.pullback ((X.formalCompletion I).ι n))
    (QuasicoherentAlgebra.pullback_obj_X (toScheme X I (n + 1)) B)
    (QuasicoherentAlgebra.pullback_obj_X (toScheme X I (n + 1)) A)
    (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B)
    (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A)
    (QuasicoherentAlgebra.pullback_obj_X ((X.formalCompletion I).ι n) _)
    (QuasicoherentAlgebra.pullback_obj_X ((X.formalCompletion I).ι n) _) h

/-- **Surjectivity of reduction to `V(I)` for étale quasi-coherent algebras.** If
`completionFunctor X I` is fully faithful on a monoidal full subcategory `P` of finitely presented
`𝒪_X`-modules containing `A` and `B`, and `Spec_X B ⟶ X` is étale, then every algebra homomorphism
`t_0^* B ⟶ t_0^* A` over `V(I)` lifts to an algebra homomorphism `B ⟶ A` over `X`. -/
@[stacks 0EL8]
theorem pullback_toScheme_zero_map_surjective
    {P : ObjectProperty X.Modules} [P.IsMonoidal]
    (hP : ∀ M, P M → M.IsFinitePresentation)
    (hfull : ∀ ⦃M N : FinitelyPresentedSheaf X⦄, P M.obj → P N.obj →
      Function.Surjective (fun f : M ⟶ N ↦ (completionFunctor X I).map f))
    (hfaith : ∀ ⦃M N : FinitelyPresentedSheaf X⦄, P M.obj → P N.obj →
      Function.Injective (fun f : M ⟶ N ↦ (completionFunctor X I).map f))
    {A B : QuasicoherentAlgebra X} (hA : P A.obj.X) (hB : P B.obj.X)
    [Etale B.obj.relativeSpecToBase] :
    Function.Surjective
      (fun ψ : B ⟶ A ↦ (QuasicoherentAlgebra.pullback (toScheme X I 0)).map ψ) := by
  intro ψ₀
  have ha₀ :
      ((relativeSpecLevelIso X I A 0).hom ≫ CommMon.relativeSpecMap ψ₀.hom ≫
          (relativeSpecLevelIso X I B 0).inv) ≫
        (map (I := I.comap B.obj.relativeSpecToBase) B.obj.relativeSpecToBase le_rfl).app 0 =
      (map (I := I.comap A.obj.relativeSpecToBase) A.obj.relativeSpecToBase le_rfl).app 0 := by
    rw [Category.assoc, Category.assoc, relativeSpecLevelIso_inv_map_app,
      CommMon.relativeSpecMap_relativeSpecToBase, relativeSpecLevelIso_hom_relativeSpecToBase]
  obtain ⟨aLift, haLift_app_comp, haLift_zero⟩ :
      ∃ aLift : A.obj.relativeSpec.formalCompletion (I.comap A.obj.relativeSpecToBase) ⟶
          B.obj.relativeSpec.formalCompletion (I.comap B.obj.relativeSpecToBase),
        (∀ n, aLift.app n ≫
            (map (I := I.comap B.obj.relativeSpecToBase) B.obj.relativeSpecToBase le_rfl).app n =
          (map (I := I.comap A.obj.relativeSpecToBase) A.obj.relativeSpecToBase le_rfl).app n) ∧
        aLift.app 0 = (relativeSpecLevelIso X I A 0).hom ≫ CommMon.relativeSpecMap ψ₀.hom ≫
          (relativeSpecLevelIso X I B 0).inv :=
    ⟨AdicThickeningSystem.liftOfEtale _ _ _ ha₀,
      fun n ↦ AdicThickeningSystem.liftOfEtale_app_comp _ _ _ ha₀ n,
      AdicThickeningSystem.liftOfEtale_app_zero _ _ _ ha₀⟩
  have hg (n : ℕ) :
      ((relativeSpecLevelIso X I A n).inv ≫ aLift.app n ≫ (relativeSpecLevelIso X I B n).hom) ≫
          ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj B).obj.relativeSpecToBase =
        ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A).obj.relativeSpecToBase := by
    rw [Category.assoc, Category.assoc, relativeSpecLevelIso_hom_relativeSpecToBase,
      haLift_app_comp n, relativeSpecLevelIso_inv_map_app]
  obtain ⟨ψ, hψ_spec⟩ :
      ∃ ψ : ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).obj B ⟶
          (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A,
        ∀ n, CommMon.relativeSpecMap (ψ n).hom =
          (relativeSpecLevelIso X I A n).inv ≫ aLift.app n ≫ (relativeSpecLevelIso X I B n).hom :=
    ⟨fun n ↦ ((relativeSpec ((X.formalCompletion I).X n)).preimage
        (MorphismProperty.Over.homMk _ (hg n))).unop,
      fun n ↦ congrArg (fun m ↦ m.left) ((relativeSpec ((X.formalCompletion I).X n)).map_preimage
        (MorphismProperty.Over.homMk _ (hg n)))⟩
  have hψ₀ : ψ 0 = ψ₀ := by
    apply eq_of_relativeSpecMap_eq
    refine (hψ_spec 0).trans <| (congrArg (fun x ↦ (relativeSpecLevelIso X I A 0).inv ≫ x ≫
      (relativeSpecLevelIso X I B 0).hom) haLift_zero).trans ?_
    exact (Iso.inv_hom_id_assoc (relativeSpecLevelIso X I A 0) _).trans <|
      (Category.assoc _ _ _).trans <|
        (congrArg (CommMon.relativeSpecMap ψ₀.hom ≫ ·)
          (Iso.inv_hom_id (relativeSpecLevelIso X I B 0))).trans
          (Category.comp_id (CommMon.relativeSpecMap ψ₀.hom))
  have hψ_nat (n : ℕ) :
      (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1)) ≫
          (algebraTransitionIso (I := I) A n).hom =
        (algebraTransitionIso (I := I) B n).hom ≫ ψ n := by
    apply eq_of_relativeSpecMap_eq
    refine (isPullback_relativeSpecPullbackFst
      ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj B)
      ((X.formalCompletion I).ι n)).hom_ext ?_ ?_
    · calc
        CommMon.relativeSpecMap
            ((QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1)) ≫
              (algebraTransitionIso (I := I) A n).hom).hom ≫
          relativeSpecPullbackFst ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj B)
            ((X.formalCompletion I).ι n)
        _ = (CommMon.relativeSpecMap (algebraTransitionIso (I := I) A n).hom.hom ≫
              CommMon.relativeSpecMap
                ((QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map
                  (ψ (n + 1))).hom) ≫
            relativeSpecPullbackFst ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj B)
              ((X.formalCompletion I).ι n) :=
          congrArg (· ≫ _) (CommMon.relativeSpecMap_comp _ _)
        _ = CommMon.relativeSpecMap (algebraTransitionIso (I := I) A n).hom.hom ≫
              relativeSpecPullbackFst ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj A)
                ((X.formalCompletion I).ι n) ≫
              CommMon.relativeSpecMap (ψ (n + 1)).hom :=
          (Category.assoc _ _ _).trans <|
            congrArg (_ ≫ ·) (relativeSpecMap_pullback_map_relativeSpecPullbackFst _ _ (ψ (n + 1)))
        _ = ((relativeSpecLevelIso X I A n).inv ≫
              (A.obj.relativeSpec.formalCompletion (I.comap A.obj.relativeSpecToBase)).ι n ≫
                (relativeSpecLevelIso X I A (n + 1)).hom) ≫
              ((relativeSpecLevelIso X I A (n + 1)).inv ≫ aLift.app (n + 1) ≫
                (relativeSpecLevelIso X I B (n + 1)).hom) := by
          rw [← Category.assoc, ← relativeSpecLevelIso_inv_ι_hom (I := I) A n, hψ_spec (n + 1)]
        _ = ((relativeSpecLevelIso X I A n).inv ≫ aLift.app n ≫
              (relativeSpecLevelIso X I B n).hom) ≫
              ((relativeSpecLevelIso X I B n).inv ≫
                (B.obj.relativeSpec.formalCompletion (I.comap B.obj.relativeSpecToBase)).ι n ≫
                  (relativeSpecLevelIso X I B (n + 1)).hom) := by
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
          rw [← Category.assoc ((A.obj.relativeSpec.formalCompletion
              (I.comap A.obj.relativeSpecToBase)).ι n),
            aLift.naturality n, Category.assoc]
        _ = CommMon.relativeSpecMap (ψ n).hom ≫
              CommMon.relativeSpecMap (algebraTransitionIso (I := I) B n).hom.hom ≫
              relativeSpecPullbackFst ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj B)
                ((X.formalCompletion I).ι n) := by
          rw [← hψ_spec n]
          exact congrArg (CommMon.relativeSpecMap (ψ n).hom ≫ ·)
            (relativeSpecLevelIso_inv_ι_hom (I := I) B n)
        _ = CommMon.relativeSpecMap ((algebraTransitionIso (I := I) B n).hom ≫ ψ n).hom ≫
              relativeSpecPullbackFst ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj B)
                ((X.formalCompletion I).ι n) :=
          (Category.assoc _ _ _).symm.trans <|
            congrArg (· ≫ _) (CommMon.relativeSpecMap_comp
              (algebraTransitionIso (I := I) B n).hom.hom (ψ n).hom).symm
    · exact (CommMon.relativeSpecMap_relativeSpecToBase _).trans
        (CommMon.relativeSpecMap_relativeSpecToBase _).symm
  have hAfp : A.obj.X.IsFinitePresentation := hP A.obj.X hA
  have hBfp : B.obj.X.IsFinitePresentation := hP B.obj.X hB
  let Φ : (completionFunctor X I).obj ⟨B.obj.X, hBfp⟩ ⟶
      (completionFunctor X I).obj ⟨A.obj.X, hAfp⟩ :=
    { app n := eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B).symm ≫
        (ψ n).hom.hom.hom ≫ eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A)
      naturality n := pullback_map_conjugate_transition hAfp hBfp n (ψ n) (ψ (n + 1)) (hψ_nat n) }
  obtain ⟨φmod, hφmod⟩ := hfull (M := ⟨B.obj.X, hBfp⟩) (N := ⟨A.obj.X, hAfp⟩) hB hA Φ
  let φ : B.obj.X ⟶ A.obj.X := φmod.hom
  have hφmod_app (n : ℕ) :
      eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B) ≫
        (Scheme.Modules.pullback (toScheme X I n)).map φ ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A).symm =
      (ψ n).hom.hom.hom := by
    have hn : (Scheme.Modules.pullback (toScheme X I n)).map φ = Φ.app n :=
      congrArg (fun m ↦ m.app n) hφmod
    rw [hn]
    exact eqToHom_eqToHom_symm_conj (𝒞 := ((X.formalCompletion I).X n).Modules)
      (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B)
      (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A) _
  have hMon : IsMonHom φ :=
    (isMonHom_iff_forall_pullback_toScheme hP hfaith hA hB φ).mpr fun n ↦ by
      rw [hφmod_app n]
      exact (ψ n).hom.hom.isMonHom_hom
  let ψglobal : B ⟶ A := ObjectProperty.homMk (CommMon.homMk (@Mon.Hom.mk _ _ _ _ _ φ hMon))
  refine ⟨ψglobal, ?_⟩
  rw [← hψ₀]
  apply ObjectProperty.hom_ext
  apply CommMon.hom_ext
  dsimp only
  rw [QuasicoherentAlgebra.pullback_map_hom_hom_hom]
  exact hφmod_app 0

/-- **Bijectivity of reduction to `V(I)` for étale quasi-coherent algebras.** Under full
faithfulness of `completionFunctor X I` on a monoidal full subcategory `P` of finitely presented
`𝒪_X`-modules containing `A` and `B`, and étaleness of `Spec_X B ⟶ X`, pulling back algebra
homomorphisms `B ⟶ A` to `V(I)` is bijective. -/
@[stacks 0EL8]
theorem pullback_toScheme_zero_map_bijective
    {P : ObjectProperty X.Modules} [P.IsMonoidal]
    (hP : ∀ M, P M → M.IsFinitePresentation)
    (hfull : ∀ ⦃M N : FinitelyPresentedSheaf X⦄, P M.obj → P N.obj →
      Function.Surjective (fun f : M ⟶ N ↦ (completionFunctor X I).map f))
    (hfaith : ∀ ⦃M N : FinitelyPresentedSheaf X⦄, P M.obj → P N.obj →
      Function.Injective (fun f : M ⟶ N ↦ (completionFunctor X I).map f))
    {A B : QuasicoherentAlgebra X} (hA : P A.obj.X) (hB : P B.obj.X)
    [Etale B.obj.relativeSpecToBase] :
    Function.Bijective
      (fun ψ : B ⟶ A ↦ (QuasicoherentAlgebra.pullback (toScheme X I 0)).map ψ) :=
  ⟨pullback_toScheme_zero_map_injective hP hfaith hA hB,
    pullback_toScheme_zero_map_surjective hP hfull hfaith hA hB⟩

end RelativeSpec

end AlgebraicGeometry.Scheme.formalCompletion

end
