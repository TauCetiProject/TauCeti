/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule
public import TauCeti.AlgebraicGeometry.RelativeSpec.PullbackAlgebra
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
import TauCeti.AlgebraicGeometry.RelativeSpec.BaseChange
import TauCeti.AlgebraicGeometry.RelativeSpec.Equivalence
import TauCeti.AlgebraicGeometry.VectorBundle.Pushforward

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
(`Scheme.Hom.isFiniteLocallyFree_pushforwardStructureAlgebra`).

## Main definitions

* `AlgebraicGeometry.Scheme.formalCompletion.finiteLocallyFreeCompletionFunctor`: the restriction
  of `completionFunctor X I` to `FiniteLocallyFreeSheaf X`.
* `AlgebraicGeometry.Scheme.formalCompletion.algebraPullbackTransitionIso`: the canonical
  isomorphism identifying the pullback along `V(I ^ (n + 1)) ⟶ V(I ^ (n + 2))` of the `(n + 1)`-st
  reduction of a quasi-coherent `𝒪_X`-algebra with its `n`-th reduction.

## Main results

* `AlgebraicGeometry.Scheme.formalCompletion.hom_ext_of_finiteLocallyFree`: under faithfulness of
  `finiteLocallyFreeCompletionFunctor X I`, morphisms of finite locally free `𝒪_X`-modules are
  determined by their pullbacks to all levels of `X.formalCompletion I`.
* `AlgebraicGeometry.Scheme.formalCompletion.hom_ext_quasicoherentAlgebra_of_isFiniteLocallyFree`
  and `exists_hom_quasicoherentAlgebra_of_isFiniteLocallyFree`: uniqueness and existence of
  algebraized morphisms in `QuasicoherentAlgebra X` between finite locally free algebras.
* `AlgebraicGeometry.Scheme.formalCompletion.hom_ext_of_finite_of_flat`,
  `AlgebraicGeometry.Scheme.formalCompletion.exists_hom_of_finite_of_flat`: uniqueness and
  existence of algebraized scheme morphisms over `X` between schemes that are finite, flat, and
  locally of finite presentation over `X`.

## References

* [The Stacks Project, Tag 0EL8](https://stacks.math.columbia.edu/tag/0EL8)
* [The Stacks Project, Tag 0EKS](https://stacks.math.columbia.edu/tag/0EKS)
-/

public section

open CategoryTheory Limits MonoidalCategory Opposite
open scoped MonObj

universe u

namespace AlgebraicGeometry.Scheme.formalCompletion

open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.AdicThickeningSystem

section CompletionFunctor

variable (X : Scheme.{u}) (I : X.IdealSheafData)

/-- The restriction of `completionFunctor X I` to finite locally free sheaves on `X`, sending `E`
to the coherent formal module `(E / I ^ (n + 1) E)ₙ` on `X.formalCompletion I`. Because this is an
abbreviation for `FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙ completionFunctor X I`, `Full`
and `Faithful` instances on `completionFunctor X I` restrict automatically to
`finiteLocallyFreeCompletionFunctor X I`. -/
noncomputable abbrev finiteLocallyFreeCompletionFunctor :
    FiniteLocallyFreeSheaf X ⥤ CoherentFormalModule (X.formalCompletion I) :=
  FiniteLocallyFreeSheaf.toFinitelyPresented X ⋙ completionFunctor X I

/-- At level `n`, `finiteLocallyFreeCompletionFunctor X I` pulls `E` back along `toScheme X I n`. -/
theorem finiteLocallyFreeCompletionFunctor_obj_obj (E : FiniteLocallyFreeSheaf X) (n : ℕ) :
    ((finiteLocallyFreeCompletionFunctor X I).obj E).obj n =
      (Modules.pullback (toScheme X I n)).obj E.obj :=
  (rfl)

/-- The `n`-th transition isomorphism of `(finiteLocallyFreeCompletionFunctor X I).obj E` is the
pullback composition isomorphism along `ι_toScheme X I n`. -/
theorem finiteLocallyFreeCompletionFunctor_obj_transitionIso
    (E : FiniteLocallyFreeSheaf X) (n : ℕ) :
    ((finiteLocallyFreeCompletionFunctor X I).obj E).transitionIso n =
      (Modules.pullbackComp _ _ ≪≫ Modules.pullbackCongr (ι_toScheme X I n)).app E.obj :=
  (rfl)

/-- At level `n`, `finiteLocallyFreeCompletionFunctor X I` acts on morphisms by pullback along
`toScheme X I n`. -/
theorem finiteLocallyFreeCompletionFunctor_map_app
    {E F : FiniteLocallyFreeSheaf X} (φ : E ⟶ F) (n : ℕ) :
    ((finiteLocallyFreeCompletionFunctor X I).map φ).app n =
      (Modules.pullback (toScheme X I n)).map φ.hom :=
  (rfl)

variable {X}

/-- If `finiteLocallyFreeCompletionFunctor X I` is faithful, two morphisms between finite locally
free `𝒪_X`-modules are equal as soon as their pullbacks to all levels `V(I ^ (n + 1))` of the
formal completion agree. -/
theorem hom_ext_of_finiteLocallyFree (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletionFunctor X I).Faithful]
    {M N : X.Modules} (hM : Modules.isFiniteLocallyFree X M)
    (hN : Modules.isFiniteLocallyFree X N) {f g : M ⟶ N}
    (h : ∀ n, (Modules.pullback (toScheme X I n)).map f =
      (Modules.pullback (toScheme X I n)).map g) :
    f = g := by
  let E : FiniteLocallyFreeSheaf X := ⟨M, hM⟩
  let F : FiniteLocallyFreeSheaf X := ⟨N, hN⟩
  let fE : E ⟶ F := ObjectProperty.homMk f
  let gE : E ⟶ F := ObjectProperty.homMk g
  have hfg : (finiteLocallyFreeCompletionFunctor X I).map fE =
      (finiteLocallyFreeCompletionFunctor X I).map gE :=
    CoherentFormalModule.hom_ext h
  exact congrArg (·.hom) ((finiteLocallyFreeCompletionFunctor X I).map_injective hfg)

end CompletionFunctor

/-! ### Algebraization for finite locally free quasi-coherent algebras -/

section Algebra

/-- Auxiliary cancellation of conjugate `eqToHom`s in a category `C`, isolated from unfolded
`QuasicoherentAlgebra` instances in tactic contexts. -/
private lemma eqToHom_conj_cancel {C : Type*} [Category C] {X₁ X₂ Y₁ Y₂ : C}
    (h₁ : X₁ = X₂) (h₂ : Y₁ = Y₂) (u : X₁ ⟶ Y₁) :
    eqToHom h₁ ≫ (eqToHom h₁.symm ≫ u ≫ eqToHom h₂) ≫ eqToHom h₂.symm = u := by
  subst h₁ h₂
  simp

private lemma eq_of_eqToHom_conj {C : Type*} [Category C] {X₁ X₂ Y₁ Y₂ : C}
    (h₁ : X₁ = X₂) (h₂ : Y₁ = Y₂) {u v : X₂ ⟶ Y₂}
    (h : eqToHom h₁ ≫ u ≫ eqToHom h₂.symm = eqToHom h₁ ≫ v ≫ eqToHom h₂.symm) :
    u = v := by
  subst h₁ h₂
  simpa using h

/-- Auxiliary naturality transport across `eqToHom`s in arbitrary categories `C` and `D`. -/
private lemma map_eqToHom_naturality {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A₁ A₂ B₁ B₂ : C} {P₁ P₂ R₁ R₂ Q₁ Q₂ : D}
    (hA : A₁ = A₂) (hB : B₁ = B₂)
    (hP : P₁ = F.obj A₁) (hQ : Q₁ = F.obj B₁)
    (hP' : P₁ = F.obj A₂) (hQ' : Q₁ = F.obj B₂)
    (hR : R₁ = P₂) (hS : R₂ = Q₂)
    {u : A₁ ⟶ B₁} {tA : F.obj A₂ ⟶ P₂} {tB : F.obj B₂ ⟶ Q₂} {v : R₁ ⟶ R₂}
    (h : (eqToHom hP ≫ F.map u ≫ eqToHom hQ.symm) ≫ (eqToHom hQ' ≫ tB ≫ eqToHom hS.symm) =
      (eqToHom hP' ≫ tA ≫ eqToHom hR.symm) ≫ v) :
    F.map (eqToHom hA.symm ≫ u ≫ eqToHom hB) ≫ tB =
      tA ≫ eqToHom hR.symm ≫ v ≫ eqToHom hS := by
  subst hA hB hP hQ hR hS
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc] using h

/-- Pure monoidal-category transport showing that a functor `F` with an epimorphism
`u : 𝟙_ D ⟶ F.obj (𝟙_ C)` reflects the unit equation from a `MonObj` conjugate by `eqToHom`s. -/
private lemma map_one_hom_of_conj {C D : Type*} [Category C] [MonoidalCategory C]
    [Category D] [MonoidalCategory D] (F : C ⥤ D)
    {B A : C} [MonObj B] [MonObj A] {B' A' : D} (hB : B' = F.obj B) (hA : A' = F.obj A)
    {u : 𝟙_ D ⟶ F.obj (𝟙_ C)} [IsIso u]
    {f : B ⟶ A} {ηB : 𝟙_ D ⟶ B'} {ηA : 𝟙_ D ⟶ A'} {ψ : B' ⟶ A'}
    (hηB : ηB = u ≫ F.map η[B] ≫ eqToHom hB.symm)
    (hηA : ηA = u ≫ F.map η[A] ≫ eqToHom hA.symm)
    (hψ : ψ = eqToHom hB ≫ F.map f ≫ eqToHom hA.symm)
    (hone : ηB ≫ ψ = ηA) :
    F.map (η[B] ≫ f) = F.map η[A] := by
  subst hB hA
  rw [hηB, hηA, hψ] at hone
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp, Category.assoc,
    ← Functor.map_comp] at hone
  exact (cancel_epi u).mp hone

/-- Pure monoidal-category transport showing that an oplax monoidal functor `F` with invertible `δ`
reflects the multiplication equation from a `MonObj` conjugate by `eqToHom`s. -/
private lemma map_mul_hom_of_conj {C D : Type*} [Category C] [MonoidalCategory C]
    [Category D] [MonoidalCategory D] (F : C ⥤ D) [F.OplaxMonoidal]
    {B A : C} [MonObj B] [MonObj A]
    [IsIso (Functor.OplaxMonoidal.δ F B B)] [IsIso (Functor.OplaxMonoidal.δ F A A)]
    {B' A' : D} (hB : B' = F.obj B) (hA : A' = F.obj A)
    {f : B ⟶ A} {μB : B' ⊗ B' ⟶ B'} {μA : A' ⊗ A' ⟶ A'} {ψ : B' ⟶ A'}
    (hμB : μB = (eqToHom hB ⊗ₘ eqToHom hB) ≫ inv (Functor.OplaxMonoidal.δ F B B) ≫
      F.map μ[B] ≫ eqToHom hB.symm)
    (hμA : μA = (eqToHom hA ⊗ₘ eqToHom hA) ≫ inv (Functor.OplaxMonoidal.δ F A A) ≫
      F.map μ[A] ≫ eqToHom hA.symm)
    (hψ : ψ = eqToHom hB ≫ F.map f ≫ eqToHom hA.symm)
    (hmul : μB ≫ ψ = (ψ ⊗ₘ ψ) ≫ μA) :
    F.map (μ[B] ≫ f) = F.map ((f ⊗ₘ f) ≫ μ[A]) := by
  subst hB hA
  rw [hμB, hμA, hψ] at hmul
  simp only [eqToHom_refl, id_tensorHom_id, Category.id_comp, Category.comp_id,
    Category.assoc] at hmul
  rw [← Functor.map_comp] at hmul
  have hδ : (F.map f ⊗ₘ F.map f) ≫ inv (Functor.OplaxMonoidal.δ F A A) =
      inv (Functor.OplaxMonoidal.δ F B B) ≫ F.map (f ⊗ₘ f) := by
    rw [IsIso.comp_inv_eq, Category.assoc, ← Functor.OplaxMonoidal.δ_natural,
      IsIso.inv_hom_id_assoc]
  rw [reassoc_of% hδ, ← Functor.map_comp] at hmul
  exact (cancel_epi (inv (Functor.OplaxMonoidal.δ F B B))).mp hmul

/-- Auxiliary comparison expressing the composition isomorphism of `QuasicoherentAlgebra.pullback`
followed by `eqToIso` along `u ≫ v = w` on underlying modules. -/
private lemma pullbackComp_eqToIso_hom_hom_hom_hom {Y Z W : Scheme.{u}}
    (u : Y ⟶ Z) (v : Z ⟶ W) {w : Y ⟶ W} (hw : u ≫ v = w) (C : QuasicoherentAlgebra W) :
    (((QuasicoherentAlgebra.pullbackComp u v).app C ≪≫
        eqToIso (congrArg (fun g ↦ (QuasicoherentAlgebra.pullback g).obj C) hw)).hom).hom.hom.hom =
      eqToHom ((QuasicoherentAlgebra.pullback_obj_X u _).trans
        (congrArg (Modules.pullback u).obj (QuasicoherentAlgebra.pullback_obj_X v C))) ≫
        ((Modules.pullbackComp u v ≪≫ Modules.pullbackCongr hw).app C.obj.X).hom ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X w C).symm := by
  subst hw
  simp only [eqToIso_refl, Iso.trans_refl, Iso.app_hom,
    QuasicoherentAlgebra.pullbackComp_hom_app_hom_hom_hom, Modules.pullbackCongr]
  rfl

/-- For a quasi-coherent commutative `𝒪_X`-algebra `C`, pulling back its `(n + 1)`-st formal
reduction along the transition `V(I ^ (n + 1)) ⟶ V(I ^ (n + 2))` recovers its `n`-th formal
reduction. -/
noncomputable def algebraPullbackTransitionIso (X : Scheme.{u}) (I : X.IdealSheafData)
    (C : QuasicoherentAlgebra X) (n : ℕ) :
    (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).obj
        ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj C) ≅
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj C :=
  (QuasicoherentAlgebra.pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1))).app C ≪≫
    eqToIso (congrArg (fun g ↦ (QuasicoherentAlgebra.pullback g).obj C) (ι_toScheme X I n))

/-- On underlying `𝒪`-modules, `(algebraPullbackTransitionIso X I C n).hom` is the module pullback
composition isomorphism along `ι_toScheme X I n`, conjugated by
`QuasicoherentAlgebra.pullback_obj_X`. -/
@[simp]
theorem algebraPullbackTransitionIso_hom_hom_hom_hom (X : Scheme.{u}) (I : X.IdealSheafData)
    (C : QuasicoherentAlgebra X) (n : ℕ) :
    (algebraPullbackTransitionIso X I C n).hom.hom.hom.hom =
      eqToHom ((QuasicoherentAlgebra.pullback_obj_X ((X.formalCompletion I).ι n) _).trans
        (congrArg (Modules.pullback ((X.formalCompletion I).ι n)).obj
          (QuasicoherentAlgebra.pullback_obj_X (toScheme X I (n + 1)) C))) ≫
        ((Modules.pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1)) ≪≫
            Modules.pullbackCongr (ι_toScheme X I n)).app C.obj.X).hom ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) C).symm :=
  pullbackComp_eqToIso_hom_hom_hom_hom _ _ (ι_toScheme X I n) C

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
  refine hom_ext_of_finiteLocallyFree I hB hA fun n ↦ ?_
  have hn := congrArg (fun k ↦ k.hom.hom.hom) (h n)
  exact eq_of_eqToHom_conj
    (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B)
    (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A)
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
    hom_ext_of_finiteLocallyFree I
      (ObjectProperty.prop_unit (Modules.isFiniteLocallyFree X)) hA fun n ↦
        map_one_hom_of_conj (Modules.pullback (toScheme X I n))
          (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B)
          (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A)
          (QuasicoherentAlgebra.pullback_obj_one (toScheme X I n) B)
          (QuasicoherentAlgebra.pullback_obj_one (toScheme X I n) A)
          (hf n) (IsMonHom.one_hom (ψ n).hom.hom.hom)
  mul_hom :=
    hom_ext_of_finiteLocallyFree I (ObjectProperty.prop_tensor hB hB) hA fun n ↦
      map_mul_hom_of_conj (Modules.pullback (toScheme X I n))
        (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B)
        (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A)
        (QuasicoherentAlgebra.pullback_obj_mul (toScheme X I n) B)
        (QuasicoherentAlgebra.pullback_obj_mul (toScheme X I n) A)
        (hf n) (IsMonHom.mul_hom (ψ n).hom.hom.hom)

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
          (algebraPullbackTransitionIso X I A n).hom =
        (algebraPullbackTransitionIso X I B n).hom ≫ ψ n) :
    ∃ f : B ⟶ A, ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).map f = ψ n := by
  let EB : FiniteLocallyFreeSheaf X := ⟨B.obj.X, hB⟩
  let EA : FiniteLocallyFreeSheaf X := ⟨A.obj.X, hA⟩
  let φ : (finiteLocallyFreeCompletionFunctor X I).obj EB ⟶
      (finiteLocallyFreeCompletionFunctor X I).obj EA :=
    { app n := eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B).symm ≫
        (ψ n).hom.hom.hom ≫ eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A)
      naturality n := by
        have hn :
            ((QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map
                (ψ (n + 1))).hom.hom.hom ≫
              (algebraPullbackTransitionIso X I A n).hom.hom.hom.hom =
            (algebraPullbackTransitionIso X I B n).hom.hom.hom.hom ≫ (ψ n).hom.hom.hom :=
          congrArg (fun k ↦ k.hom.hom.hom) (hψ n)
        have hn' :=
          (congrArg₂ CategoryStruct.comp
            (QuasicoherentAlgebra.pullback_map_hom_hom_hom ((X.formalCompletion I).ι n) (ψ (n + 1)))
            (algebraPullbackTransitionIso_hom_hom_hom_hom X I A n)).symm.trans
            (hn.trans
              (congrArg (· ≫ (ψ n).hom.hom.hom)
                (algebraPullbackTransitionIso_hom_hom_hom_hom X I B n)))
        exact map_eqToHom_naturality (Modules.pullback ((X.formalCompletion I).ι n))
          (QuasicoherentAlgebra.pullback_obj_X (toScheme X I (n + 1)) B)
          (QuasicoherentAlgebra.pullback_obj_X (toScheme X I (n + 1)) A)
          (QuasicoherentAlgebra.pullback_obj_X ((X.formalCompletion I).ι n) _)
          (QuasicoherentAlgebra.pullback_obj_X ((X.formalCompletion I).ι n) _)
          ((QuasicoherentAlgebra.pullback_obj_X ((X.formalCompletion I).ι n) _).trans
            (congrArg (Modules.pullback ((X.formalCompletion I).ι n)).obj
              (QuasicoherentAlgebra.pullback_obj_X (toScheme X I (n + 1)) B)))
          ((QuasicoherentAlgebra.pullback_obj_X ((X.formalCompletion I).ι n) _).trans
            (congrArg (Modules.pullback ((X.formalCompletion I).ι n)).obj
              (QuasicoherentAlgebra.pullback_obj_X (toScheme X I (n + 1)) A)))
          (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B)
          (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A) hn' }
  let f₀ : EB ⟶ EA := (finiteLocallyFreeCompletionFunctor X I).preimage φ
  have hf₀ (n : ℕ) : (ψ n).hom.hom.hom =
      eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B) ≫
        (Modules.pullback (toScheme X I n)).map f₀.hom ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A).symm := by
    have hmap := congrArg (fun k ↦ k.app n)
      ((finiteLocallyFreeCompletionFunctor X I).map_preimage φ)
    simp only [finiteLocallyFreeCompletionFunctor_map_app, φ] at hmap
    exact (eqToHom_conj_cancel
      (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B)
      (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A) (ψ n).hom.hom.hom).symm.trans
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

@[reassoc]
private lemma relativeSpecLevelIso_hom_fst (C : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecLevelIso (I := I) C n).hom ≫
        relativeSpecPullbackFst C (toScheme X I n) =
      toScheme C.obj.relativeSpec (I.comap C.obj.relativeSpecToBase) n :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

@[reassoc]
private lemma relativeSpecLevelIso_hom_snd (C : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecLevelIso (I := I) C n).hom ≫
        ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj C).obj.relativeSpecToBase =
      (map (I := I.comap C.obj.relativeSpecToBase) C.obj.relativeSpecToBase le_rfl).app n :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

@[reassoc]
private lemma relativeSpecLevelIso_inv_fst (C : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecLevelIso (I := I) C n).inv ≫
        toScheme C.obj.relativeSpec (I.comap C.obj.relativeSpecToBase) n =
      relativeSpecPullbackFst C (toScheme X I n) :=
  IsPullback.isoIsPullback_inv_fst _ _ _ _

@[reassoc]
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
  · calc ((relativeSpecLevelIso (I := I) A n).inv ≫
            (map (CommMon.relativeSpecMap f.hom) hf).app n ≫
              (relativeSpecLevelIso (I := I) B n).hom) ≫
            relativeSpecPullbackFst B (toScheme X I n)
        _ = (relativeSpecLevelIso (I := I) A n).inv ≫
              (map (CommMon.relativeSpecMap f.hom) hf).app n ≫
                toScheme B.obj.relativeSpec (I.comap B.obj.relativeSpecToBase) n :=
          (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
            ((Category.assoc _ _ _).trans
              (congrArg (_ ≫ ·) (relativeSpecLevelIso_hom_fst (I := I) B n))))
        _ = (relativeSpecLevelIso (I := I) A n).inv ≫
              toScheme A.obj.relativeSpec (I.comap A.obj.relativeSpecToBase) n ≫
                CommMon.relativeSpecMap f.hom :=
          congrArg (_ ≫ ·) (map_app_toScheme _ hf n)
        _ = relativeSpecPullbackFst A (toScheme X I n) ≫ CommMon.relativeSpecMap f.hom :=
          relativeSpecLevelIso_inv_fst_assoc (I := I) A n _
        _ = _ := (relativeSpecMap_pullback_map_relativeSpecPullbackFst A (toScheme X I n) f).symm
  · have hcomp : (map (CommMon.relativeSpecMap f.hom) hf).app n ≫
        (map (I := I.comap B.obj.relativeSpecToBase) B.obj.relativeSpecToBase le_rfl).app n =
        (map (I := I.comap A.obj.relativeSpecToBase) A.obj.relativeSpecToBase le_rfl).app n := by
      rw [← AdicThickeningSystem.comp_app, map_comp]
      congr 2
      exact CommMon.relativeSpecMap_relativeSpecToBase f.hom
    calc ((relativeSpecLevelIso (I := I) A n).inv ≫
            (map (CommMon.relativeSpecMap f.hom) hf).app n ≫
              (relativeSpecLevelIso (I := I) B n).hom) ≫
            ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj B).obj.relativeSpecToBase
        _ = (relativeSpecLevelIso (I := I) A n).inv ≫
              ((map (CommMon.relativeSpecMap f.hom) hf).app n ≫
                (map (I := I.comap B.obj.relativeSpecToBase)
                  B.obj.relativeSpecToBase le_rfl).app n) :=
          (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
            ((Category.assoc _ _ _).trans
              (congrArg (_ ≫ ·) (relativeSpecLevelIso_hom_snd (I := I) B n))))
        _ = ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A).obj.relativeSpecToBase :=
          (congrArg (_ ≫ ·) hcomp).trans (relativeSpecLevelIso_inv_snd (I := I) A n)
        _ = _ := (CommMon.relativeSpecMap_relativeSpecToBase _).symm

/-- Auxiliary composition compatibility for `relativeSpecPullbackFst` along `u ≫ v = w`. -/
private lemma relativeSpecMap_pullbackComp_eqToIso_fst {Y Z W : Scheme.{u}}
    (u : Y ⟶ Z) (v : Z ⟶ W) {w : Y ⟶ W} (hw : u ≫ v = w) (C : QuasicoherentAlgebra W) :
    CommMon.relativeSpecMap
        (((QuasicoherentAlgebra.pullbackComp u v).app C ≪≫
          eqToIso (congrArg (fun g ↦ (QuasicoherentAlgebra.pullback g).obj C) hw)).hom).hom ≫
      relativeSpecPullbackFst ((QuasicoherentAlgebra.pullback v).obj C) u ≫
        relativeSpecPullbackFst C v =
      relativeSpecPullbackFst C w := by
  subst hw
  simp only [eqToIso_refl, Iso.trans_refl, Iso.app_hom]
  exact (relativeSpecPullbackFst_comp C v u).symm

/-- Under `relativeSpecLevelIso`, the transition morphism `ι n` of the formal completion of
`Spec_X(C)` corresponds to `algebraPullbackTransitionIso` composed with `relativeSpecPullbackFst`
along `(X.formalCompletion I).ι n`. -/
private lemma relativeSpecLevelIso_inv_ι_hom (C : QuasicoherentAlgebra X) (n : ℕ) :
    (relativeSpecLevelIso (I := I) C n).inv ≫
        (C.obj.relativeSpec.formalCompletion (I.comap C.obj.relativeSpecToBase)).ι n ≫
          (relativeSpecLevelIso (I := I) C (n + 1)).hom =
      CommMon.relativeSpecMap (algebraPullbackTransitionIso X I C n).hom.hom ≫
        relativeSpecPullbackFst
          ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj C)
          ((X.formalCompletion I).ι n) := by
  refine (isPullback_relativeSpecPullbackFst C (toScheme X I (n + 1))).hom_ext ?_ ?_
  · calc ((relativeSpecLevelIso (I := I) C n).inv ≫
            (C.obj.relativeSpec.formalCompletion (I.comap C.obj.relativeSpecToBase)).ι n ≫
              (relativeSpecLevelIso (I := I) C (n + 1)).hom) ≫
            relativeSpecPullbackFst C (toScheme X I (n + 1))
        _ = (relativeSpecLevelIso (I := I) C n).inv ≫
              ((C.obj.relativeSpec.formalCompletion (I.comap C.obj.relativeSpecToBase)).ι n ≫
                toScheme C.obj.relativeSpec (I.comap C.obj.relativeSpecToBase) (n + 1)) :=
          (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
            ((Category.assoc _ _ _).trans
              (congrArg (_ ≫ ·) (relativeSpecLevelIso_hom_fst (I := I) C (n + 1)))))
        _ = relativeSpecPullbackFst C (toScheme X I n) :=
          (congrArg (_ ≫ ·) (ι_toScheme _ _ n)).trans (relativeSpecLevelIso_inv_fst (I := I) C n)
        _ = CommMon.relativeSpecMap (algebraPullbackTransitionIso X I C n).hom.hom ≫
              relativeSpecPullbackFst
                ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj C)
                ((X.formalCompletion I).ι n) ≫
              relativeSpecPullbackFst C (toScheme X I (n + 1)) :=
          (relativeSpecMap_pullbackComp_eqToIso_fst _ _ (ι_toScheme X I n) C).symm
        _ = _ := (Category.assoc _ _ _).symm
  · calc ((relativeSpecLevelIso (I := I) C n).inv ≫
            (C.obj.relativeSpec.formalCompletion (I.comap C.obj.relativeSpecToBase)).ι n ≫
              (relativeSpecLevelIso (I := I) C (n + 1)).hom) ≫
            ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj C).obj.relativeSpecToBase
        _ = (relativeSpecLevelIso (I := I) C n).inv ≫
              ((C.obj.relativeSpec.formalCompletion (I.comap C.obj.relativeSpecToBase)).ι n ≫
                (map (I := I.comap C.obj.relativeSpecToBase)
                  C.obj.relativeSpecToBase le_rfl).app (n + 1)) :=
          (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
            ((Category.assoc _ _ _).trans
              (congrArg (_ ≫ ·) (relativeSpecLevelIso_hom_snd (I := I) C (n + 1)))))
        _ = (relativeSpecLevelIso (I := I) C n).inv ≫
              ((map (I := I.comap C.obj.relativeSpecToBase)
                C.obj.relativeSpecToBase le_rfl).app n ≫
                (X.formalCompletion I).ι n) :=
          congrArg (_ ≫ ·)
            ((map (I := I.comap C.obj.relativeSpecToBase)
              C.obj.relativeSpecToBase le_rfl).naturality n)
        _ = ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj C).obj.relativeSpecToBase ≫
              (X.formalCompletion I).ι n :=
          relativeSpecLevelIso_inv_snd_assoc (I := I) C n _
        _ = CommMon.relativeSpecMap (algebraPullbackTransitionIso X I C n).hom.hom ≫
              (relativeSpecPullbackFst
                ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj C)
                ((X.formalCompletion I).ι n) ≫
                ((QuasicoherentAlgebra.pullback
                  (toScheme X I (n + 1))).obj C).obj.relativeSpecToBase) :=
          ((CommMon.relativeSpecMap_relativeSpecToBase_assoc
            (algebraPullbackTransitionIso X I C n).hom.hom
            ((X.formalCompletion I).ι n)).symm.trans
            (congrArg (_ ≫ ·)
              (relativeSpecPullbackFst_relativeSpecToBase _ ((X.formalCompletion I).ι n)).symm))
        _ = _ := (Category.assoc _ _ _).symm

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
  refine hom_ext_quasicoherentAlgebra_of_isFiniteLocallyFree I hB hA fun n ↦ ?_
  let F := relativeSpec ((X.formalCompletion I).X n)
  have hn : CommMon.relativeSpecMap
      ((QuasicoherentAlgebra.pullback (toScheme X I n)).map f₁).hom =
      CommMon.relativeSpecMap
        ((QuasicoherentAlgebra.pullback (toScheme X I n)).map f₂).hom := by
    rw [← relativeSpecLevelIso_inv_map_app_hom (I := I) f₁ hf₁ n,
      ← relativeSpecLevelIso_inv_map_app_hom (I := I) f₂ hf₂ n, h]
  apply Quiver.Hom.op_inj
  refine F.map_injective ?_
  apply MorphismProperty.Over.Hom.ext
  exact hn

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
    CommMon.relativeSpecMap (algebraPullbackTransitionIso X I A n).hom.hom ≫
        CommMon.relativeSpecMap
          ((QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1))).hom =
      CommMon.relativeSpecMap (ψ n).hom ≫
        CommMon.relativeSpecMap (algebraPullbackTransitionIso X I B n).hom.hom := by
  let g (k : ℕ) :=
    (relativeSpecLevelIso (I := I) A k).inv ≫ a.app k ≫ (relativeSpecLevelIso (I := I) B k).hom
  refine (isPullback_relativeSpecPullbackFst
    ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj B)
    ((X.formalCompletion I).ι n)).hom_ext ?_ ?_
  · calc (CommMon.relativeSpecMap (algebraPullbackTransitionIso X I A n).hom.hom ≫
            CommMon.relativeSpecMap
              ((QuasicoherentAlgebra.pullback
                ((X.formalCompletion I).ι n)).map (ψ (n + 1))).hom) ≫
            relativeSpecPullbackFst
              ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj B)
              ((X.formalCompletion I).ι n)
        _ = CommMon.relativeSpecMap (algebraPullbackTransitionIso X I A n).hom.hom ≫
              (relativeSpecPullbackFst
                ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj A)
                ((X.formalCompletion I).ι n) ≫
                CommMon.relativeSpecMap (ψ (n + 1)).hom) :=
          (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
            (relativeSpecMap_pullback_map_relativeSpecPullbackFst _ _ (ψ (n + 1))))
        _ = ((relativeSpecLevelIso (I := I) A n).inv ≫
              (A.obj.relativeSpec.formalCompletion (I.comap A.obj.relativeSpecToBase)).ι n ≫
                (relativeSpecLevelIso (I := I) A (n + 1)).hom) ≫ g (n + 1) :=
          (Category.assoc _ _ _).symm.trans (congrArg₂ CategoryStruct.comp
            (relativeSpecLevelIso_inv_ι_hom (I := I) A n).symm (hψ_spec (n + 1)))
        _ = (relativeSpecLevelIso (I := I) A n).inv ≫
              ((A.obj.relativeSpec.formalCompletion (I.comap A.obj.relativeSpecToBase)).ι n ≫
                a.app (n + 1)) ≫
              (relativeSpecLevelIso (I := I) B (n + 1)).hom := by
          dsimp only [g]
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
        _ = (relativeSpecLevelIso (I := I) A n).inv ≫
              (a.app n ≫
                (B.obj.relativeSpec.formalCompletion (I.comap B.obj.relativeSpecToBase)).ι n) ≫
              (relativeSpecLevelIso (I := I) B (n + 1)).hom :=
          congrArg (_ ≫ ·) (congrArg (· ≫ _) (a.naturality n))
        _ = g n ≫
              ((relativeSpecLevelIso (I := I) B n).inv ≫
                (B.obj.relativeSpec.formalCompletion (I.comap B.obj.relativeSpecToBase)).ι n ≫
                  (relativeSpecLevelIso (I := I) B (n + 1)).hom) := by
          dsimp only [g]
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
        _ = _ :=
          (congrArg₂ CategoryStruct.comp (hψ_spec n).symm
            (relativeSpecLevelIso_inv_ι_hom (I := I) B n)).trans (Category.assoc _ _ _).symm
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (CommMon.relativeSpecMap_relativeSpecToBase _)).trans
      ((CommMon.relativeSpecMap_relativeSpecToBase _).trans
        ((CommMon.relativeSpecMap_relativeSpecToBase _).symm.trans
          ((congrArg (_ ≫ ·)
            (CommMon.relativeSpecMap_relativeSpecToBase _).symm).trans
            (Category.assoc _ _ _).symm))))

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
    calc ((relativeSpecLevelIso (I := I) A n).inv ≫ a.app n ≫
            (relativeSpecLevelIso (I := I) B n).hom) ≫
            ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj B).obj.relativeSpecToBase
        _ = (relativeSpecLevelIso (I := I) A n).inv ≫
              (a.app n ≫ (map B.obj.relativeSpecToBase le_rfl).app n) :=
          (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
            ((Category.assoc _ _ _).trans
              (congrArg (_ ≫ ·) (relativeSpecLevelIso_hom_snd (I := I) B n))))
        _ = (relativeSpecLevelIso (I := I) A n).inv ≫
              (map A.obj.relativeSpecToBase le_rfl).app n :=
          congrArg (_ ≫ ·) (congrArg (·.app n) ha)
        _ = _ := relativeSpecLevelIso_inv_snd (I := I) A n
  let G (n : ℕ) :
      (relativeSpec ((X.formalCompletion I).X n)).obj
          (op ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj A)) ⟶
        (relativeSpec ((X.formalCompletion I).X n)).obj
          (op ((QuasicoherentAlgebra.pullback (toScheme X I n)).obj B)) :=
    MorphismProperty.Over.homMk (g n) (hg n)
  let ψ (n : ℕ) : (QuasicoherentAlgebra.pullback (toScheme X I n)).obj B ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A :=
    ((relativeSpec ((X.formalCompletion I).X n)).preimage (G n)).unop
  have hψ_spec (n : ℕ) : CommMon.relativeSpecMap (ψ n).hom = g n :=
    congrArg (·.left) ((relativeSpec ((X.formalCompletion I).X n)).map_preimage (G n))
  obtain ⟨f, hf⟩ := exists_hom_quasicoherentAlgebra_of_isFiniteLocallyFree (I := I) hB hA ψ
    fun n ↦ by
      apply Quiver.Hom.op_inj
      refine (relativeSpec ((X.formalCompletion I).X n)).map_injective ?_
      apply MorphismProperty.Over.Hom.ext
      exact (CommMon.relativeSpecMap_comp
        (((QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1))).hom)
        (algebraPullbackTransitionIso X I A n).hom.hom).trans
        ((relativeSpecMap_pullback_ι_eq (I := I) a ψ hψ_spec n).trans
          (CommMon.relativeSpecMap_comp
            (algebraPullbackTransitionIso X I B n).hom.hom (ψ n).hom).symm)
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

/-- Two morphisms of formal completions are equal if they agree after composing with the closed
immersions `toScheme` at every level. -/
private lemma formalCompletion_hom_ext {Y Z : Scheme.{u}} {J : Y.IdealSheafData}
    {K : Z.IdealSheafData} {a b : Y.formalCompletion J ⟶ Z.formalCompletion K}
    (h : ∀ n, a.app n ≫ toScheme Z K n = b.app n ≫ toScheme Z K n) : a = b := by
  ext n
  exact (cancel_mono (toScheme Z K n)).mp (h n)

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
  have hu_le : (I.comap p).comap u ≤ I.comap p' := by rw [← IdealSheafData.comap_comp, hu]
  have hu_inv : (I.comap p').comap (inv u) ≤ I.comap p := by
    rw [← IdealSheafData.comap_comp, ← hu, IsIso.inv_hom_id_assoc]
  have hv_inv : (I.comap q').comap (inv v) ≤ I.comap q := by
    rw [← IdealSheafData.comap_comp, ← hv, IsIso.inv_hom_id_assoc]
  let a' : V'.formalCompletion (I.comap p') ⟶ W'.formalCompletion (I.comap q') :=
    map u hu_le ≫ a ≫ map (inv v) hv_inv
  have ha' : a' ≫ map q' le_rfl = map p' le_rfl := by
    refine formalCompletion_hom_ext fun n ↦ ?_
    simp only [a', AdicThickeningSystem.comp_app, Category.assoc]
    rw [map_app_toScheme, map_app_toScheme, map_app_toScheme_assoc]
    have hv_eq : inv v ≫ q' = q := by rw [← hv, IsIso.inv_hom_id_assoc]
    have ha_n := congrArg (fun m ↦ m.app n ≫ toScheme X I n) ha
    simp only [AdicThickeningSystem.comp_app, Category.assoc, map_app_toScheme] at ha_n
    rw [hv_eq, ha_n, map_app_toScheme_assoc, hu]
  obtain ⟨s, hs, hs_map⟩ := h_lift a' ha'
  have hg : (inv u ≫ s ≫ v) ≫ q = p := by
    rw [Category.assoc, Category.assoc, hv, hs, ← hu, IsIso.inv_hom_id_assoc]
  refine ⟨inv u ≫ s ≫ v, hg, formalCompletion_hom_ext fun n ↦ ?_⟩
  have hs_n := congrArg (fun m ↦ m.app n ≫ toScheme W' (I.comap q') n) hs_map
  simp only [a', AdicThickeningSystem.comp_app, Category.assoc, map_app_toScheme] at hs_n
  rw [map_app_toScheme, ← Category.assoc (toScheme V (I.comap p) n),
    ← map_app_toScheme (inv u) hu_inv n, Category.assoc, ← Category.assoc _ s, hs_n]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hu_id : (map (inv u) hu_inv).app n ≫ (map u hu_le).app n = 𝟙 _ := by
    rw [← cancel_mono (toScheme V (I.comap p) n), Category.assoc, map_app_toScheme,
      map_app_toScheme_assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
  rw [reassoc_of% hu_id]

variable {X V W : Scheme.{u}} {I : X.IdealSheafData}
  {I_V : V.IdealSheafData} {I_W : W.IdealSheafData}

/-- **Uniqueness in formal algebraization for finite locally free morphisms.** Let `p : V ⟶ X` and
`q : W ⟶ X` be finite, flat, locally finitely presented morphisms of schemes, and assume that
`finiteLocallyFreeCompletionFunctor X I` is faithful. Then two morphisms `g₁, g₂ : V ⟶ W` over `X`
are equal as soon as they induce the same morphism on formal completions along the preimages of
`I`. -/
theorem hom_ext_of_finite_of_flat
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
  have hmap :
      map (I := I.comap p.pushforwardStructureAlgebra.relativeSpecToBase)
        (J := I.comap q.pushforwardStructureAlgebra.relativeSpecToBase)
        (CommMon.relativeSpecMap m₁)
        (by rw [← IdealSheafData.comap_comp, CommMon.relativeSpecMap_relativeSpecToBase]) =
      map (CommMon.relativeSpecMap m₂)
        (by rw [← IdealSheafData.comap_comp, CommMon.relativeSpecMap_relativeSpecToBase]) := by
    refine formalCompletion_hom_ext fun n ↦ (cancel_mono q.relativeSpecFunctionsToScheme).mp ?_
    rw [Category.assoc, Category.assoc, map_app_toScheme_assoc, map_app_toScheme_assoc,
      Scheme.Hom.relativeSpecFunctionsToScheme_naturality g₁ hg₁,
      Scheme.Hom.relativeSpecFunctionsToScheme_naturality g₂ hg₂]
    have hn := congrArg (fun m ↦ m.app n ≫ toScheme W (I.comap q) n) h
    rw [map_app_toScheme, map_app_toScheme] at hn
    rw [← Category.assoc, ← Category.assoc,
      ← map_app_toScheme p.relativeSpecFunctionsToScheme
        (by rw [← IdealSheafData.comap_comp, p.relativeSpecFunctionsToScheme_comp]) n,
      Category.assoc, Category.assoc, hn]
  have hf : (ObjectProperty.homMk m₁ :
      (⟨q.pushforwardStructureAlgebra, inferInstance⟩ : QuasicoherentAlgebra X) ⟶
        ⟨p.pushforwardStructureAlgebra, inferInstance⟩) =
      ObjectProperty.homMk m₂ :=
    hom_ext_relativeSpec_of_isFiniteLocallyFree I
      q.isFiniteLocallyFree_pushforwardStructureAlgebra
      p.isFiniteLocallyFree_pushforwardStructureAlgebra _ _ hmap
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
theorem exists_hom_of_finite_of_flat
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
    q.isFiniteLocallyFree_pushforwardStructureAlgebra
    p.isFiniteLocallyFree_pushforwardStructureAlgebra a' ha'
  exact ⟨CommMon.relativeSpecMap f.hom, CommMon.relativeSpecMap_relativeSpecToBase f.hom, hf⟩

end FiniteFlat

end AlgebraicGeometry.Scheme.formalCompletion
