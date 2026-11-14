/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Basic
public import TauCeti.AlgebraicGeometry.RelativeSpec.PullbackAlgebra
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree

/-!
# Descent of algebra morphisms from formal completions

Let `X` be a scheme and `I` an ideal sheaf on `X`. The closed immersions
`toScheme X I n : V(I ^ (n + 1)) ⟶ X` assemble into a morphism of adic thickening systems
`Scheme.formalCompletion.toOfScheme X I` from `X.formalCompletion I` to the constant system
`AdicThickeningSystem.ofScheme.obj X`.

For any quasi-coherent commutative `𝒪_X`-algebra `A`, its restrictions `A_n` to the infinitesimal
neighbourhoods `V(I ^ (n + 1))` come with canonical reduction isomorphisms
`QuasicoherentAlgebra.formalCompletionTransitionIso X I A n` identifying the pullback of `A_{n + 1}`
along `V(I ^ (n + 1)) ⟶ V(I ^ (n + 2))` with `A_n`, whose underlying module maps are the reduction
isomorphisms of `Scheme.formalCompletion.completionFunctor X I`.

Consequently, when completion is faithful (respectively, fully faithful) on a monoidal full
subcategory `P` of finitely presented `𝒪_X`-modules — in particular on all finitely presented
modules or on finite locally free sheaves (`FiniteLocallyFreeSheaf.completionFunctor X I`) —
morphisms of quasi-coherent `𝒪_X`-algebras whose underlying modules belong to `P` are uniquely
determined by (respectively, in bijection with compatible families of) their restrictions to the
infinitesimal neighbourhoods `V(I ^ (n + 1))`. Closure of `P` under the monoidal unit and tensor
product ensures that the module morphism recovered by full faithfulness respects the unit and
multiplication, since those identities live in hom-sets between objects of `P` where completion is
faithful.

## Main definitions

* `AlgebraicGeometry.Scheme.formalCompletion.toOfScheme`: the canonical morphism
  `X.formalCompletion I ⟶ AdicThickeningSystem.ofScheme.obj X` with components `toScheme X I n`;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.completionFunctor`: the completion functor
  restricted to finite locally free sheaves;
* `TauCeti.AlgebraicGeometry.QuasicoherentAlgebra.formalCompletionTransitionIso`: the reduction
  isomorphism of a pulled-back quasi-coherent algebra along a transition of `X.formalCompletion I`.

## Main results

* `TauCeti.AlgebraicGeometry.QuasicoherentAlgebra.hom_ext_of_formalCompletion_of_prop`:
  faithfulness of completion on `P` implies uniqueness of algebra morphisms from their
  infinitesimal restrictions, with specializations `hom_ext_of_formalCompletion` and
  `hom_ext_of_formalCompletion_of_isFiniteLocallyFree`;
* `TauCeti.AlgebraicGeometry.QuasicoherentAlgebra.existsUnique_hom_of_formalCompletion_of_prop`:
  full faithfulness of completion on a monoidal property `P` descends compatible families of
  infinitesimal algebra morphisms to a unique algebra morphism on `X`, with specializations
  `existsUnique_hom_of_formalCompletion` and
  `existsUnique_hom_of_formalCompletion_of_isFiniteLocallyFree`.

## References

* [The Stacks Project, Section 30.23](https://stacks.math.columbia.edu/tag/087W)
* [The Stacks Project, Lemma 58.17.1](https://stacks.math.columbia.edu/tag/0EL8)
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open scoped MonObj

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.formalCompletion

open TauCeti.AlgebraicGeometry

/-- The canonical morphism from the formal completion `X/V(I)` to the constant adic thickening
system on `X`, whose level-`n` component is the closed immersion
`toScheme X I n : V(I ^ (n + 1)) ⟶ X`. -/
-- `@[expose]` is forced by dependent typing of `AdicThickeningSystem.pullback`: without
-- `(toOfScheme X I).app n` reducing definitionally to `toScheme X I n`, the level-`n` component of
-- `AdicThickeningSystem.pullback (toOfScheme X I) _` does not unify with `Limits.pullback`.
@[expose]
def toOfScheme (X : Scheme.{u}) (I : X.IdealSheafData) :
    X.formalCompletion I ⟶ AdicThickeningSystem.ofScheme.obj X where
  app n := toScheme X I n
  naturality n := (ι_toScheme X I n).trans (Category.comp_id _).symm

/-- At level `n`, `toOfScheme X I` is the closed immersion `toScheme X I n`. -/
@[simp]
theorem toOfScheme_app (X : Scheme.{u}) (I : X.IdealSheafData) (n : ℕ) :
    (toOfScheme X I).app n = toScheme X I n :=
  (rfl)

end AlgebraicGeometry.Scheme.formalCompletion

namespace TauCeti.AlgebraicGeometry

namespace FiniteLocallyFreeSheaf

/-- The completion functor restricted to finite locally free sheaves on `X`, sending `E` to the
system of its restrictions to the infinitesimal neighbourhoods `V(I ^ (n + 1))`. -/
abbrev completionFunctor (X : Scheme.{u}) (I : X.IdealSheafData) :
    FiniteLocallyFreeSheaf X ⥤ AdicThickeningSystem.CoherentFormalModule (X.formalCompletion I) :=
  toFinitelyPresented X ⋙ Scheme.formalCompletion.completionFunctor X I

end FiniteLocallyFreeSheaf

namespace QuasicoherentAlgebra

open AdicThickeningSystem Scheme.formalCompletion

variable {X : Scheme.{u}}

private lemma conj_comp_conj {Z : Scheme.{u}} {M₁ M₁' M₂ M₂' M₃ M₃' : Z.Modules}
    (p₁ : M₁ = M₁') (p₂ : M₂' = M₂) (p₃ : M₃' = M₃)
    (u : M₁' ⟶ M₂') (v : M₂' ⟶ M₃') :
    (eqToHom p₁ ≫ u ≫ eqToHom p₂) ≫ eqToHom p₂.symm ≫ v ≫ eqToHom p₃ =
      eqToHom p₁ ≫ (u ≫ v) ≫ eqToHom p₃ := by
  subst p₁ p₂ p₃
  simp

private lemma eq_of_conj_eq {Z : Scheme.{u}} {M M' N N' : Z.Modules}
    (p : M' = M) (q : N' = N) {u v : M ⟶ N}
    (h : eqToHom p ≫ u ≫ eqToHom q.symm = eqToHom p ≫ v ≫ eqToHom q.symm) :
    u = v := by
  subst p q
  simpa using h

private lemma conj_conj_symm {Z : Scheme.{u}} {M M' N N' : Z.Modules}
    (p : M' = M) (q : N' = N) (u : M' ⟶ N') :
    eqToHom p ≫ (eqToHom p.symm ≫ u ≫ eqToHom q) ≫ eqToHom q.symm = u := by
  subst p q
  simp

private lemma naturality_of_conj {Z W : Scheme.{u}} (G : W.Modules ⥤ Z.Modules)
    {MB MA MB' MA' : W.Modules} {NB NA NB' NA' KB KA : Z.Modules}
    (pB' : MB' = MB) (pA' : MA' = MA)
    (qB : NB' = G.obj MB') (qA : NA' = G.obj MA')
    (pB : KB = NB) (pA : KA = NA)
    (u₁ : MB' ⟶ MA') (u₀ : KB ⟶ KA) (τA : G.obj MA ⟶ NA) (τB : G.obj MB ⟶ NB)
    (h : (eqToHom qB ≫ G.map u₁ ≫ eqToHom qA.symm) ≫
        (eqToHom (qA.trans (congrArg G.obj pA')) ≫ τA ≫ eqToHom pA.symm) =
      (eqToHom (qB.trans (congrArg G.obj pB')) ≫ τB ≫ eqToHom pB.symm) ≫ u₀) :
    G.map (eqToHom pB'.symm ≫ u₁ ≫ eqToHom pA') ≫ τA =
      τB ≫ eqToHom pB.symm ≫ u₀ ≫ eqToHom pA := by
  subst pB' pA' qB qA pB pA
  simpa using h

private lemma map_one_comp_of_conj {Z : Scheme.{u}} {U MB MB' MA MA' : Z.Modules}
    (e : U ≅ 𝟙_ Z.Modules) (pB : MB' = MB) (pA : MA' = MA)
    (ηB : U ⟶ MB) (ηA : U ⟶ MA) (u : MB' ⟶ MA')
    (h : (e.inv ≫ ηB ≫ eqToHom pB.symm) ≫ u = e.inv ≫ ηA ≫ eqToHom pA.symm) :
    ηB ≫ eqToHom pB.symm ≫ u ≫ eqToHom pA = ηA := by
  subst pB pA
  simpa [Category.assoc] using h

private lemma map_mul_comp_of_conj {Y : Scheme.{u}} (f : Y ⟶ X)
    {B₀ A₀ : X.Modules}
    [IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) B₀ B₀)]
    [IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) A₀ A₀)]
    {MB' MA' : Y.Modules}
    (pB : MB' = (Scheme.Modules.pullback f).obj B₀)
    (pA : MA' = (Scheme.Modules.pullback f).obj A₀)
    (μB : B₀ ⊗ B₀ ⟶ B₀) (μA : A₀ ⊗ A₀ ⟶ A₀) (Φ : B₀ ⟶ A₀) (u : MB' ⟶ MA')
    (hΦ : (Scheme.Modules.pullback f).map Φ = eqToHom pB.symm ≫ u ≫ eqToHom pA)
    (hmul : ((eqToHom pB ⊗ₘ eqToHom pB) ≫
        inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) B₀ B₀) ≫
          (Scheme.Modules.pullback f).map μB ≫ eqToHom pB.symm) ≫ u =
      (u ⊗ₘ u) ≫
        ((eqToHom pA ⊗ₘ eqToHom pA) ≫
          inv (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) A₀ A₀) ≫
            (Scheme.Modules.pullback f).map μA ≫ eqToHom pA.symm)) :
    (Scheme.Modules.pullback f).map (μB ≫ Φ) =
      (Scheme.Modules.pullback f).map ((Φ ⊗ₘ Φ) ≫ μA) := by
  subst pB pA
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, id_tensorHom_id] at hΦ hmul
  subst u
  rw [Category.assoc, IsIso.inv_comp_eq] at hmul
  rw [Functor.map_comp, Functor.map_comp, hmul,
    Functor.OplaxMonoidal.δ_natural_assoc (Scheme.Modules.pullback f) Φ Φ,
    IsIso.hom_inv_id_assoc]

/-- On underlying modules, an `eqToHom` between pullbacks of a quasi-coherent algebra along equal
scheme morphisms is `Scheme.Modules.pullbackCongr` conjugated by the carrier identifications. -/
theorem eqToHom_pullback_obj_hom_hom_hom {Y : Scheme.{u}} {f g : Y ⟶ X} (h : f = g)
    (A : QuasicoherentAlgebra X) :
    (eqToHom (congrArg (fun k ↦ (pullback k).obj A) h)).hom.hom.hom =
      eqToHom (pullback_obj_X f A) ≫ (Scheme.Modules.pullbackCongr h).hom.app A.obj.X ≫
        eqToHom (pullback_obj_X g A).symm := by
  subst h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, eqToHom_trans, eqToHom_refl]
  rfl

variable (X) (I : X.IdealSheafData)

/-- The canonical reduction isomorphism identifying the pullback along
`V(I ^ (n + 1)) ⟶ V(I ^ (n + 2))` of the `(n + 1)`-st infinitesimal restriction of a
quasi-coherent algebra `A` with its `n`-th infinitesimal restriction. -/
def formalCompletionTransitionIso (A : QuasicoherentAlgebra X) (n : ℕ) :
    (pullback ((X.formalCompletion I).ι n)).obj ((pullback (toScheme X I (n + 1))).obj A) ≅
      (pullback (toScheme X I n)).obj A :=
  (pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1))).app A ≪≫
    eqToIso (congrArg (fun f ↦ (pullback f).obj A) (ι_toScheme X I n))

/-- Underlying `CommMon` morphism of `(formalCompletionTransitionIso X I A n).hom`. -/
@[simp]
theorem formalCompletionTransitionIso_hom_hom (A : QuasicoherentAlgebra X) (n : ℕ) :
    (formalCompletionTransitionIso X I A n).hom.hom =
      ((pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1))).hom.app A).hom ≫
        (eqToHom (congrArg (fun f ↦ (pullback f).obj A) (ι_toScheme X I n))).hom :=
  (rfl)

/-- On underlying modules, `formalCompletionTransitionIso` is the reduction isomorphism of
`Scheme.formalCompletion.completionFunctor`, conjugated by `pullback_obj_X`. -/
theorem formalCompletionTransitionIso_hom_hom_hom_hom (A : QuasicoherentAlgebra X) (n : ℕ) :
    (formalCompletionTransitionIso X I A n).hom.hom.hom.hom =
      eqToHom ((pullback_obj_X ((X.formalCompletion I).ι n) _).trans
          (congrArg _ (pullback_obj_X (toScheme X I (n + 1)) A))) ≫
        ((Scheme.Modules.pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1)) ≪≫
            Scheme.Modules.pullbackCongr (ι_toScheme X I n)).app A.obj.X).hom ≫
          eqToHom (pullback_obj_X (toScheme X I n) A).symm :=
  (congrArg₂ (· ≫ ·)
    (pullbackComp_hom_app_hom_hom_hom ((X.formalCompletion I).ι n) (toScheme X I (n + 1)) A)
    (eqToHom_pullback_obj_hom_hom_hom (ι_toScheme X I n) A)).trans
    (conj_comp_conj _ _ _ _ _)

/-- Naturality of `formalCompletionTransitionIso` with respect to algebra morphisms on `X`. -/
@[reassoc]
theorem map_formalCompletionTransitionIso_hom {A B : QuasicoherentAlgebra X} (Ψ : B ⟶ A) (n : ℕ) :
    (pullback ((X.formalCompletion I).ι n)).map ((pullback (toScheme X I (n + 1))).map Ψ) ≫
        (formalCompletionTransitionIso X I A n).hom =
      (formalCompletionTransitionIso X I B n).hom ≫ (pullback (toScheme X I n)).map Ψ := by
  have hA : (formalCompletionTransitionIso X I A n).hom =
      (pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1))).hom.app A ≫
        eqToHom (congrArg (fun f ↦ (pullback f).obj A) (ι_toScheme X I n)) := rfl
  have hB : (formalCompletionTransitionIso X I B n).hom =
      (pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1))).hom.app B ≫
        eqToHom (congrArg (fun f ↦ (pullback f).obj B) (ι_toScheme X I n)) := rfl
  rw [hA, hB, ← Category.assoc, ← Functor.comp_map,
    (pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1))).hom.naturality Ψ,
    Category.assoc, Category.assoc]
  exact congrArg (_ ≫ ·) (eqToHom_naturality (fun f ↦ (pullback f).map Ψ) (ι_toScheme X I n))

variable {X I}

/-- Fully faithful inclusion of the full subcategory of `X.Modules` cut out by `P` into
`FinitelyPresentedSheaf X` when every object satisfying `P` is finitely presented. -/
-- `@[expose]` ensures that `((propCompletionFunctor I hP).obj M).obj n` reduces definitionally to
-- `(Scheme.Modules.pullback (toScheme X I n)).obj M.obj`, matching `@[expose]` on
-- `Scheme.formalCompletion.completionFunctor`.
@[expose]
def toFinitelyPresentedOfLE {P : ObjectProperty X.Modules}
    (hP : ∀ M, P M → M.IsFinitePresentation) :
    P.FullSubcategory ⥤ FinitelyPresentedSheaf.{u} X where
  obj M := ⟨M.obj, hP M.obj M.property⟩
  map f := ObjectProperty.homMk f.hom

/-- On morphisms, `toFinitelyPresentedOfLE hP` preserves the underlying module morphism. -/
@[simp]
theorem toFinitelyPresentedOfLE_map_hom {P : ObjectProperty X.Modules}
    (hP : ∀ M, P M → M.IsFinitePresentation) {M N : P.FullSubcategory} (f : M ⟶ N) :
    ((toFinitelyPresentedOfLE hP).map f).hom = f.hom :=
  (rfl)

/-- `toFinitelyPresentedOfLE hP` is fully faithful. -/
def fullyFaithfulToFinitelyPresentedOfLE {P : ObjectProperty X.Modules}
    (hP : ∀ M, P M → M.IsFinitePresentation) :
    (toFinitelyPresentedOfLE hP).FullyFaithful where
  preimage f := ObjectProperty.homMk f.hom

instance full_toFinitelyPresentedOfLE {P : ObjectProperty X.Modules}
    (hP : ∀ M, P M → M.IsFinitePresentation) :
    (toFinitelyPresentedOfLE hP).Full :=
  (fullyFaithfulToFinitelyPresentedOfLE hP).full

instance faithful_toFinitelyPresentedOfLE {P : ObjectProperty X.Modules}
    (hP : ∀ M, P M → M.IsFinitePresentation) :
    (toFinitelyPresentedOfLE hP).Faithful :=
  (fullyFaithfulToFinitelyPresentedOfLE hP).faithful

/-- The completion functor restricted to the full subcategory of `X.Modules` cut out by an object
property `P` implying finite presentation. -/
abbrev propCompletionFunctor (I : X.IdealSheafData) {P : ObjectProperty X.Modules}
    (hP : ∀ M, P M → M.IsFinitePresentation) :
    P.FullSubcategory ⥤ CoherentFormalModule (X.formalCompletion I) :=
  toFinitelyPresentedOfLE hP ⋙ completionFunctor X I

/-- At level `n`, `propCompletionFunctor I hP` acts on morphisms via `Scheme.Modules.pullback`. -/
theorem propCompletionFunctor_map_app {P : ObjectProperty X.Modules}
    (hP : ∀ M, P M → M.IsFinitePresentation) {M N : P.FullSubcategory} (f : M ⟶ N) (n : ℕ) :
    ((propCompletionFunctor I hP).map f).app n =
      (Scheme.Modules.pullback (toScheme X I n)).map f.hom :=
  (rfl)

section Descent

variable {P : ObjectProperty X.Modules} (hP : ∀ M, P M → M.IsFinitePresentation)

/-- **Uniqueness of algebra morphisms from formal completions.** Let `P` be a full subcategory of
finitely presented `𝒪_X`-modules on which `completionFunctor X I` is faithful. Two morphisms
`Ψ₁, Ψ₂ : B ⟶ A` of quasi-coherent `𝒪_X`-algebras whose underlying modules satisfy `P` are equal as
soon as their restrictions to `V(I ^ (n + 1))` agree for every `n`. -/
theorem hom_ext_of_formalCompletion_of_prop [(propCompletionFunctor I hP).Faithful]
    {A B : QuasicoherentAlgebra X} (hA : P A.obj.X) (hB : P B.obj.X) {Ψ₁ Ψ₂ : B ⟶ A}
    (h : ∀ n, (pullback (toScheme X I n)).map Ψ₁ = (pullback (toScheme X I n)).map Ψ₂) :
    Ψ₁ = Ψ₂ := by
  let F := propCompletionFunctor I hP
  have hmod : (ObjectProperty.homMk Ψ₁.hom.hom.hom :
        (⟨B.obj.X, hB⟩ : P.FullSubcategory) ⟶ ⟨A.obj.X, hA⟩) =
      ObjectProperty.homMk Ψ₂.hom.hom.hom := by
    refine F.map_injective (CoherentFormalModule.hom_ext fun n ↦ ?_)
    exact eq_of_conj_eq (pullback_obj_X (toScheme X I n) B) (pullback_obj_X (toScheme X I n) A)
      ((pullback_map_hom_hom_hom (toScheme X I n) Ψ₁).symm.trans
        ((congrArg (fun g ↦ g.hom.hom.hom) (h n)).trans
          (pullback_map_hom_hom_hom (toScheme X I n) Ψ₂)))
  exact ObjectProperty.hom_ext _ (CommMon.hom_ext _ _ (congrArg (fun g ↦ g.hom) hmod))

/-- The underlying module components of a compatible family of infinitesimal algebra morphisms form
a morphism of coherent formal modules on `X.formalCompletion I`. -/
private def formalModuleHomOfCompatible {A B : QuasicoherentAlgebra X} (hA : P A.obj.X)
    (hB : P B.obj.X)
    (ψ : ∀ n, (pullback (toScheme X I n)).obj B ⟶ (pullback (toScheme X I n)).obj A)
    (hψ : ∀ n, (pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1)) ≫
      (formalCompletionTransitionIso X I A n).hom =
        (formalCompletionTransitionIso X I B n).hom ≫ ψ n) :
    (propCompletionFunctor I hP).obj ⟨B.obj.X, hB⟩ ⟶
      (propCompletionFunctor I hP).obj ⟨A.obj.X, hA⟩ where
  app n := eqToHom (pullback_obj_X (toScheme X I n) B).symm ≫ (ψ n).hom.hom.hom ≫
    eqToHom (pullback_obj_X (toScheme X I n) A)
  naturality n :=
    naturality_of_conj (Scheme.Modules.pullback ((X.formalCompletion I).ι n))
      (pullback_obj_X (toScheme X I (n + 1)) B) (pullback_obj_X (toScheme X I (n + 1)) A)
      (pullback_obj_X ((X.formalCompletion I).ι n) _)
      (pullback_obj_X ((X.formalCompletion I).ι n) _)
      (pullback_obj_X (toScheme X I n) B) (pullback_obj_X (toScheme X I n) A)
      (ψ (n + 1)).hom.hom.hom (ψ n).hom.hom.hom _ _
      ((congrArg₂ (· ≫ ·) (pullback_map_hom_hom_hom _ (ψ (n + 1)))
        (formalCompletionTransitionIso_hom_hom_hom_hom X I A n)).symm.trans
        ((congrArg (fun g ↦ g.hom.hom.hom) (hψ n)).trans
          (congrArg (· ≫ (ψ n).hom.hom.hom)
            (formalCompletionTransitionIso_hom_hom_hom_hom X I B n))))

/-- If `Φ : B.obj.X ⟶ A.obj.X` pulls back at every level `n` to the underlying map of an algebra
morphism `ψ n`, and completion is faithful on a monoidal property `P` satisfied by `A` and `B`, then
`Φ` preserves the unit. -/
private lemma one_hom_of_formalCompletion [P.IsMonoidal] [(propCompletionFunctor I hP).Faithful]
    {A B : QuasicoherentAlgebra X} (hA : P A.obj.X)
    (ψ : ∀ n, (pullback (toScheme X I n)).obj B ⟶ (pullback (toScheme X I n)).obj A)
    (Φ : B.obj.X ⟶ A.obj.X)
    (hΦ : ∀ n, (Scheme.Modules.pullback (toScheme X I n)).map Φ =
      eqToHom (pullback_obj_X (toScheme X I n) B).symm ≫ (ψ n).hom.hom.hom ≫
        eqToHom (pullback_obj_X (toScheme X I n) A)) :
    η[B.obj.X] ≫ Φ = η[A.obj.X] := by
  let F := propCompletionFunctor I hP
  have hhom : (ObjectProperty.homMk (η[B.obj.X] ≫ Φ) :
        (⟨𝟙_ X.Modules, ObjectProperty.prop_unit P⟩ : P.FullSubcategory) ⟶ ⟨A.obj.X, hA⟩) =
      ObjectProperty.homMk η[A.obj.X] := by
    refine F.map_injective (CoherentFormalModule.hom_ext fun n ↦ ?_)
    rw [propCompletionFunctor_map_app, propCompletionFunctor_map_app, ObjectProperty.homMk_hom,
      ObjectProperty.homMk_hom, Functor.map_comp, hΦ n]
    exact map_one_comp_of_conj (Scheme.Modules.pullbackObjUnitIso (toScheme X I n))
      (pullback_obj_X (toScheme X I n) B) (pullback_obj_X (toScheme X I n) A) _ _ _
      ((congrArg (· ≫ (ψ n).hom.hom.hom) (pullback_obj_one (toScheme X I n) B)).symm.trans
        ((IsMonHom.one_hom (ψ n).hom.hom.hom).trans (pullback_obj_one (toScheme X I n) A)))
  exact congrArg (fun g ↦ g.hom) hhom

/-- If `Φ : B.obj.X ⟶ A.obj.X` pulls back at every level `n` to the underlying map of an algebra
morphism `ψ n`, and completion is faithful on a monoidal property `P` satisfied by `A` and `B`, then
`Φ` preserves multiplication. -/
private lemma mul_hom_of_formalCompletion [P.IsMonoidal] [(propCompletionFunctor I hP).Faithful]
    {A B : QuasicoherentAlgebra X} (hA : P A.obj.X) (hB : P B.obj.X)
    (ψ : ∀ n, (pullback (toScheme X I n)).obj B ⟶ (pullback (toScheme X I n)).obj A)
    (Φ : B.obj.X ⟶ A.obj.X)
    (hΦ : ∀ n, (Scheme.Modules.pullback (toScheme X I n)).map Φ =
      eqToHom (pullback_obj_X (toScheme X I n) B).symm ≫ (ψ n).hom.hom.hom ≫
        eqToHom (pullback_obj_X (toScheme X I n) A)) :
    μ[B.obj.X] ≫ Φ = (Φ ⊗ₘ Φ) ≫ μ[A.obj.X] := by
  let F := propCompletionFunctor I hP
  have hhom : (ObjectProperty.homMk (μ[B.obj.X] ≫ Φ) :
        (⟨B.obj.X ⊗ B.obj.X, ObjectProperty.prop_tensor hB hB⟩ : P.FullSubcategory) ⟶
          ⟨A.obj.X, hA⟩) =
      ObjectProperty.homMk ((Φ ⊗ₘ Φ) ≫ μ[A.obj.X]) := by
    refine F.map_injective (CoherentFormalModule.hom_ext fun n ↦ ?_)
    rw [propCompletionFunctor_map_app, propCompletionFunctor_map_app, ObjectProperty.homMk_hom,
      ObjectProperty.homMk_hom]
    exact map_mul_comp_of_conj (toScheme X I n)
      (pullback_obj_X (toScheme X I n) B) (pullback_obj_X (toScheme X I n) A)
      μ[B.obj.X] μ[A.obj.X] Φ (ψ n).hom.hom.hom (hΦ n)
      ((congrArg (· ≫ (ψ n).hom.hom.hom) (pullback_obj_mul (toScheme X I n) B)).symm.trans
        ((IsMonHom.mul_hom (ψ n).hom.hom.hom).trans
          (congrArg (_ ≫ ·) (pullback_obj_mul (toScheme X I n) A))))
  exact congrArg (fun g ↦ g.hom) hhom

/-- **Existence and uniqueness of algebra morphisms from formal completions.** Let `P` be a
monoidal full subcategory of finitely presented `𝒪_X`-modules on which `completionFunctor X I` is
fully faithful, and let `A, B` be quasi-coherent `𝒪_X`-algebras with underlying modules in `P`.
Every family of algebra morphisms `ψ n` on the infinitesimal neighbourhoods `V(I ^ (n + 1))`
compatible with `formalCompletionTransitionIso` is the restriction of a unique algebra morphism
`Ψ : B ⟶ A`. -/
theorem existsUnique_hom_of_formalCompletion_of_prop [P.IsMonoidal]
    [(propCompletionFunctor I hP).Full] [(propCompletionFunctor I hP).Faithful]
    {A B : QuasicoherentAlgebra X} (hA : P A.obj.X) (hB : P B.obj.X)
    (ψ : ∀ n, (pullback (toScheme X I n)).obj B ⟶ (pullback (toScheme X I n)).obj A)
    (hψ : ∀ n, (pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1)) ≫
      (formalCompletionTransitionIso X I A n).hom =
        (formalCompletionTransitionIso X I B n).hom ≫ ψ n) :
    ∃! Ψ : B ⟶ A, ∀ n, (pullback (toScheme X I n)).map Ψ = ψ n := by
  let F := propCompletionFunctor I hP
  let φ := formalModuleHomOfCompatible hP hA hB ψ hψ
  let Φ : B.obj.X ⟶ A.obj.X := (F.preimage φ).hom
  have hΦ (n : ℕ) : (Scheme.Modules.pullback (toScheme X I n)).map Φ =
      eqToHom (pullback_obj_X (toScheme X I n) B).symm ≫ (ψ n).hom.hom.hom ≫
        eqToHom (pullback_obj_X (toScheme X I n) A) :=
    congrArg (fun g ↦ g.app n) (F.map_preimage φ)
  have hmon : IsMonHom Φ :=
    { one_hom := one_hom_of_formalCompletion hP hA ψ Φ hΦ
      mul_hom := mul_hom_of_formalCompletion hP hA hB ψ Φ hΦ }
  let Ψ : B ⟶ A := ObjectProperty.homMk (CommMon.homMk (@Mon.Hom.mk _ _ _ _ _ Φ hmon))
  have hΨ (n : ℕ) : (pullback (toScheme X I n)).map Ψ = ψ n := by
    refine ObjectProperty.hom_ext _ (CommMon.hom_ext _ _ ?_)
    exact (pullback_map_hom_hom_hom (toScheme X I n) Ψ).trans
      ((congrArg (fun m ↦ eqToHom _ ≫ m ≫ eqToHom _) (hΦ n)).trans (conj_conj_symm _ _ _))
  exact ⟨Ψ, hΨ, fun Ψ' hΨ' ↦ hom_ext_of_formalCompletion_of_prop hP hA hB fun n ↦
    (hΨ' n).trans (hΨ n).symm⟩

end Descent

section Specializations

/-- Finite presentation viewed as a monoidal object property on `X.Modules`. -/
private abbrev isFPModules (X : Scheme.{u}) : ObjectProperty X.Modules :=
  _root_.SheafOfModules.isFinitePresentation X.ringCatSheaf

private local instance : (isFPModules X).IsMonoidal :=
  SheafOfModules.isMonoidal_isFinitePresentation (R := X.sheaf)

/-- `FiniteLocallyFreeSheaf.completionFunctor X I` agrees with `propCompletionFunctor` for
`Scheme.Modules.isFiniteLocallyFree X`. -/
def finiteLocallyFreeCompletionIso (X : Scheme.{u}) (I : X.IdealSheafData) :
    FiniteLocallyFreeSheaf.completionFunctor X I ≅
      propCompletionFunctor I (P := Scheme.Modules.isFiniteLocallyFree X) (fun _ hE ↦ hE.2) :=
  Functor.isoWhiskerRight
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦
      (Category.comp_id _).trans (Category.id_comp _).symm)
    (completionFunctor X I)

instance faithful_propCompletionFunctor_isFiniteLocallyFree
    [(FiniteLocallyFreeSheaf.completionFunctor X I).Faithful] :
    (propCompletionFunctor I (P := Scheme.Modules.isFiniteLocallyFree X)
      (fun _ hE ↦ hE.2)).Faithful :=
  Functor.Faithful.of_iso (finiteLocallyFreeCompletionIso X I)

instance full_propCompletionFunctor_isFiniteLocallyFree
    [(FiniteLocallyFreeSheaf.completionFunctor X I).Full] :
    (propCompletionFunctor I (P := Scheme.Modules.isFiniteLocallyFree X)
      (fun _ hE ↦ hE.2)).Full :=
  Functor.Full.of_iso (finiteLocallyFreeCompletionIso X I)

/-- Two morphisms between finitely presented commutative `𝒪_X`-algebras agree if their restrictions
to every infinitesimal neighbourhood `V(I ^ (n + 1))` agree, provided `completionFunctor X I` is
faithful. -/
theorem hom_ext_of_formalCompletion [(completionFunctor X I).Faithful]
    {A B : QuasicoherentAlgebra X} [A.obj.X.IsFinitePresentation] [B.obj.X.IsFinitePresentation]
    {Ψ₁ Ψ₂ : B ⟶ A}
    (h : ∀ n, (pullback (toScheme X I n)).map Ψ₁ = (pullback (toScheme X I n)).map Ψ₂) :
    Ψ₁ = Ψ₂ := by
  have : (propCompletionFunctor I (P := isFPModules X) (fun _ hM ↦ hM)).Faithful :=
    Functor.Faithful.comp (toFinitelyPresentedOfLE (P := isFPModules X) fun _ hM ↦ hM)
      (completionFunctor X I)
  exact hom_ext_of_formalCompletion_of_prop (P := isFPModules X) (fun _ hM ↦ hM) ‹_› ‹_› h

/-- Every compatible family of algebra morphisms on `V(I ^ (n + 1))` between finitely presented
commutative `𝒪_X`-algebras descends to a unique algebra morphism on `X`, provided
`completionFunctor X I` is fully faithful. -/
theorem existsUnique_hom_of_formalCompletion [(completionFunctor X I).Full]
    [(completionFunctor X I).Faithful] {A B : QuasicoherentAlgebra X}
    [A.obj.X.IsFinitePresentation] [B.obj.X.IsFinitePresentation]
    (ψ : ∀ n, (pullback (toScheme X I n)).obj B ⟶ (pullback (toScheme X I n)).obj A)
    (hψ : ∀ n, (pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1)) ≫
      (formalCompletionTransitionIso X I A n).hom =
        (formalCompletionTransitionIso X I B n).hom ≫ ψ n) :
    ∃! Ψ : B ⟶ A, ∀ n, (pullback (toScheme X I n)).map Ψ = ψ n := by
  have : (propCompletionFunctor I (P := isFPModules X) (fun _ hM ↦ hM)).Faithful :=
    Functor.Faithful.comp (toFinitelyPresentedOfLE (P := isFPModules X) fun _ hM ↦ hM)
      (completionFunctor X I)
  have : (propCompletionFunctor I (P := isFPModules X) (fun _ hM ↦ hM)).Full :=
    Functor.Full.comp (toFinitelyPresentedOfLE (P := isFPModules X) fun _ hM ↦ hM)
      (completionFunctor X I)
  exact existsUnique_hom_of_formalCompletion_of_prop (P := isFPModules X) (fun _ hM ↦ hM)
    ‹_› ‹_› ψ hψ

/-- Two morphisms between finite locally free commutative `𝒪_X`-algebras agree if their
restrictions to every infinitesimal neighbourhood `V(I ^ (n + 1))` agree, provided
`FiniteLocallyFreeSheaf.completionFunctor X I` is faithful. -/
theorem hom_ext_of_formalCompletion_of_isFiniteLocallyFree
    [(FiniteLocallyFreeSheaf.completionFunctor X I).Faithful]
    {A B : QuasicoherentAlgebra X} (hA : Scheme.Modules.isFiniteLocallyFree X A.obj.X)
    (hB : Scheme.Modules.isFiniteLocallyFree X B.obj.X) {Ψ₁ Ψ₂ : B ⟶ A}
    (h : ∀ n, (pullback (toScheme X I n)).map Ψ₁ = (pullback (toScheme X I n)).map Ψ₂) :
    Ψ₁ = Ψ₂ :=
  hom_ext_of_formalCompletion_of_prop (fun _ hE ↦ hE.2) hA hB h

/-- Every compatible family of algebra morphisms on `V(I ^ (n + 1))` between finite locally free
commutative `𝒪_X`-algebras descends to a unique algebra morphism on `X`, provided
`FiniteLocallyFreeSheaf.completionFunctor X I` is fully faithful. -/
theorem existsUnique_hom_of_formalCompletion_of_isFiniteLocallyFree
    [(FiniteLocallyFreeSheaf.completionFunctor X I).Full]
    [(FiniteLocallyFreeSheaf.completionFunctor X I).Faithful]
    {A B : QuasicoherentAlgebra X} (hA : Scheme.Modules.isFiniteLocallyFree X A.obj.X)
    (hB : Scheme.Modules.isFiniteLocallyFree X B.obj.X)
    (ψ : ∀ n, (pullback (toScheme X I n)).obj B ⟶ (pullback (toScheme X I n)).obj A)
    (hψ : ∀ n, (pullback ((X.formalCompletion I).ι n)).map (ψ (n + 1)) ≫
      (formalCompletionTransitionIso X I A n).hom =
        (formalCompletionTransitionIso X I B n).hom ≫ ψ n) :
    ∃! Ψ : B ⟶ A, ∀ n, (pullback (toScheme X I n)).map Ψ = ψ n :=
  existsUnique_hom_of_formalCompletion_of_prop (fun _ hE ↦ hE.2) hA hB ψ hψ

end Specializations

end QuasicoherentAlgebra

end TauCeti.AlgebraicGeometry

end
