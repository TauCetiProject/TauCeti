/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.StableTranslate
public import TauCeti.Algebra.Module.AuslanderReiten.Equivalence
public import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.Stable.Equivalence
public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.MatlisDualTranspose

/-!
# The Auslander–Reiten translate as a stable equivalence

Let `A` be an Artin algebra over a commutative Artinian ring `R`, and `E` an injective `R`-module
such that `Hom_R(R ⧸ 𝔪, E)` has length one for every maximal ideal `𝔪` of `R`. The
Auslander–Reiten translate `τ = D Tr` is an equivalence

`τ : (mod A) / 𝒫 ≌ (mod A) / ℐ`

from finitely presented (equivalently, finitely generated) modules modulo maps through projectives
to finitely generated modules modulo maps through injectives. It is the composite of the
Auslander–Bridger duality `Tr` (`TauCeti.stableTransposeEquivalence`, over any ring) and the stable
Matlis duality `D` (`TauCeti.finiteStableMatlisDualEquivalence`). Its chosen quasi-inverse is the
inverse of the stable Matlis duality followed by the inverse transpose; mathematically it is the
inverse translate `τ⁻ = Tr D`, and `TauCeti.stableTranslateEquivalenceInverseObjIso` identifies it
with the inverse transpose of `D N`, naturally in `N`.

For computations, the translate of `X` is compared with the class of the bundled module `D Tr X`
for the presentation chosen by `TauCeti.stableTranspose`
(`TauCeti.stableTranslateObjIsoMatlisDualTranspose`), and `τ τ⁻ N ≅ N` is read through these
presentations (`TauCeti.matlisDualTransposeInverseIso`).

## Main definitions

* `TauCeti.finiteStableTranslate`: the translate `τ = D Tr` with values in finitely generated
  modules modulo injectives; it is `TauCeti.stableTranslate` up to the inclusion
  (`TauCeti.finiteStableTranslateCompιIso`).
* `TauCeti.stableTranslateEquivalence`: **the translate is an equivalence**
  `(mod A) / 𝒫 ≌ (mod A) / ℐ`.
* `TauCeti.stableTranslateEquivalenceInverseObjIso`: its chosen quasi-inverse is `Tr D`.
* `TauCeti.stableTranslateObjIsoMatlisDualTranspose` and `TauCeti.matlisDualTransposeInverseIso`:
  the translate is the class of `D Tr X`, and `τ τ⁻ N ≅ N` modulo injectives.

## Main results

* `TauCeti.stableTranslateEquivalenceInverseObjIso_naturality`,
  `TauCeti.stableTranslateObjIsoMatlisDualTranspose_naturality` and
  `TauCeti.matlisDualTransposeInverseIso_naturality`: naturality of these comparisons.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Proposition IV.1.9.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory Opposite

universe u v

section Translate

variable (R : Type*) [CommRing R] (A : Type u) [Ring A] [Algebra R A] (E : Type v)
  [AddCommGroup E] [Module R E] [Module.Injective R E] [Small.{v} R]
  [IsNoetherianRing R] [Module.Finite R A] [Module.Finite R E]

/-- **The Auslander–Reiten translate on finitely generated modules**: `τ = D Tr`, from finitely
presented modules modulo projectives to finitely generated modules modulo injectives. -/
def finiteStableTranslate :
    FinitelyPresentedStableModule.{u, max u v} A ⥤
      FinitelyGeneratedInjectiveStableModule.{u, max u v} A :=
  stableTranspose.{u, v} A ⋙ finiteStableMatlisDualOp R A E

instance : (finiteStableTranslate R A E).Additive := by
  unfold finiteStableTranslate
  infer_instance

/-- The translate on finitely generated modules is the translate `TauCeti.stableTranslate`, up to
the inclusion of finitely generated modules modulo injectives. -/
def finiteStableTranslateCompιIso :
    finiteStableTranslate R A E ⋙ ObjectProperty.ι _ ≅ stableTranslate R A E :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (finiteStableMatlisDualOpCompιIso R E) ≪≫
    eqToIso (by rw [stableTranslate_def, stableTranslateFunctor_def, ← stableTranspose_def])

variable {R E} [IsArtinianRing R]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)

omit [IsNoetherianRing R] [Module.Finite R E] in
variable (R E) in
/-- **The Auslander–Reiten translate is a stable equivalence.** Over an Artin algebra, `τ = D Tr`
is an equivalence from finitely presented modules modulo projectives to finitely generated modules
modulo injectives. Its chosen quasi-inverse is the stable Matlis dual followed by the inverse
transpose (`TauCeti.stableTranslateEquivalence_inverse`); mathematically it is the inverse
translate `τ⁻ = Tr D` (`TauCeti.stableTranslateEquivalenceInverseObjIso`). -/
def stableTranslateEquivalence :
    FinitelyPresentedStableModule.{u, max u v} A ≌
      FinitelyGeneratedInjectiveStableModule.{u, max u v} A :=
  (stableTransposeEquivalence FinitelyPresentedStableModule.presentation
    FinitelyPresentedStableModule.presentation).trans (finiteStableMatlisDualEquivalence R A E hE)

/-- The functor of the stable equivalence is the translate. -/
@[simp]
theorem stableTranslateEquivalence_functor :
    (stableTranslateEquivalence R A E hE).functor = finiteStableTranslate R A E := by
  rw [stableTranslateEquivalence, Equivalence.trans_functor, stableTransposeEquivalence_functor,
    finiteStableMatlisDualEquivalence_functor, finiteStableTranslate, stableTranspose_def]

omit [Module.Finite R E] in
/-- The chosen quasi-inverse of the translate is the inverse of the stable Matlis duality followed
by the inverse transpose. -/
theorem stableTranslateEquivalence_inverse :
    (stableTranslateEquivalence R A E hE).inverse =
      (finiteStableMatlisDualEquivalence R A E hE).inverse ⋙
        stableTransposeInverse FinitelyPresentedStableModule.presentation
          FinitelyPresentedStableModule.presentation := by
  rw [stableTranslateEquivalence, Equivalence.trans_inverse, stableTransposeEquivalence_inverse]

variable {A}

/-- **The inverse translate is `Tr D`.** The chosen quasi-inverse of the translate sends `N` to the
inverse transpose of the dual `D N`, the cokernel of the dual of the chosen presentation of `D N`
(`TauCeti.stableTransposeInverse_obj`). -/
noncomputable def stableTranslateEquivalenceInverseObjIso
    (N : FinitelyGeneratedInjectiveStableModule.{u, max u v} A) :
    (stableTranslateEquivalence R A E hE).inverse.obj N ≅
      (stableTransposeInverse FinitelyPresentedStableModule.presentation
        FinitelyPresentedStableModule.presentation).obj (op (matlisDualStableObj R E N)) :=
  eqToIso (by rw [stableTranslateEquivalence_inverse, Functor.comp_obj]) ≪≫
    (stableTransposeInverse FinitelyPresentedStableModule.presentation
      FinitelyPresentedStableModule.presentation).mapIso
        (finiteStableMatlisDualEquivalenceInverseObjIso hE N)

/-- **Naturality of `τ⁻ N ≅ Tr D N`.** For a representative `g₀` of `g : N ⟶ N'`, the inverse
translate of `g` is the inverse transpose of the class of `D g₀`. -/
theorem stableTranslateEquivalenceInverseObjIso_naturality
    {N N' : FinitelyGeneratedInjectiveStableModule.{u, max u v} A} (g : N ⟶ N')
    (g₀ : N.obj.as ⟶ N'.obj.as)
    (hg : (ExactStructure.abelian _).injectiveStableFunctor.map g₀ = g.hom) :
    (stableTranslateEquivalence R A E hE).inverse.map g ≫
        (stableTranslateEquivalenceInverseObjIso hE N').hom =
      (stableTranslateEquivalenceInverseObjIso hE N).hom ≫
        (stableTransposeInverse FinitelyPresentedStableModule.presentation
          FinitelyPresentedStableModule.presentation).map
            (ObjectProperty.homMk ((ExactStructure.abelian _).projectiveStableFunctor.map
              ((ModuleCat.matlisDual R E).map g₀.op)) :
                matlisDualStableObj R E N' ⟶ matlisDualStableObj R E N).op := by
  rw [Functor.congr_hom (stableTranslateEquivalence_inverse A hE) g]
  simp only [stableTranslateEquivalenceInverseObjIso, Iso.trans_hom, eqToIso.hom,
    Functor.mapIso_hom, Functor.comp_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [← Functor.map_comp, finiteStableMatlisDualEquivalenceInverseObjIso_naturality hE g g₀ hg,
    Functor.map_comp]

include hE in
/-- **`τ τ⁻ N ≅ N`**: the counit of the translate equivalence, read through
`TauCeti.finiteStableTranslate`. -/
noncomputable def finiteStableTranslateInverseIso
    (N : FinitelyGeneratedInjectiveStableModule.{u, max u v} A) :
    (finiteStableTranslate R A E).obj ((stableTranslateEquivalence R A E hE).inverse.obj N) ≅ N :=
  eqToIso (by rw [← Functor.comp_obj, stableTranslateEquivalence_functor]) ≪≫
    (stableTranslateEquivalence R A E hE).counitIso.app N

/-- **Naturality of `τ τ⁻ N ≅ N`.** -/
theorem finiteStableTranslateInverseIso_naturality
    {N N' : FinitelyGeneratedInjectiveStableModule.{u, max u v} A} (g : N ⟶ N') :
    (finiteStableTranslate R A E).map ((stableTranslateEquivalence R A E hE).inverse.map g) ≫
        (finiteStableTranslateInverseIso hE N').hom =
      (finiteStableTranslateInverseIso hE N).hom ≫ g := by
  have hc := (stableTranslateEquivalence R A E hE).counitIso.hom.naturality g
  simp only [Functor.comp_map, Functor.id_map] at hc
  rw [Functor.congr_hom (stableTranslateEquivalence_functor A hE)] at hc
  simp only [finiteStableTranslateInverseIso, Iso.trans_hom, eqToIso.hom, Iso.app_hom,
    Category.assoc, ← hc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end Translate

/-! ### The translate and its inverse through `D Tr` of chosen presentations -/

section Comparison

open scoped ModuleCat.Algebra

variable {R : Type v} [CommRing R] {A : Type u} [Ring A] [Algebra R A] {E : Type v}
  [AddCommGroup E] [Module R E] [Module.Injective R E]
  [IsArtinianRing R] [Module.Finite R A]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)

omit [IsArtinianRing R] [Module.Finite R A] in
/-- The translate of a finitely presented module, as the class of `D Tr X` for the presentation
chosen by `TauCeti.stableTranspose`. -/
noncomputable def stableTranslateObjIsoMatlisDualTranspose
    (X : FinitelyPresentedStableModule.{u, max u v} A) :
    (stableTranslate R A E).obj X ≅
      (ExactStructure.abelian _).injectiveStableFunctor.obj
        (ModuleCat.matlisDualTranspose R E
          (FinitelyPresentedStableModule.presentation X)) :=
  let P := FinitelyPresentedStableModule.presentation X
  eqToIso (by rw [stableTranslate_def]) ≪≫
    stableTranslateFunctorObjIso R E FinitelyPresentedStableModule.presentation X ≪≫
    (ExactStructure.abelian _).injectiveStableFunctor.mapIso
      (ModuleCat.matlisDualOpTransposeIso R E P)

omit [IsArtinianRing R] [Module.Finite R A] in
/-- **Naturality of `τX ≅ D Tr X` modulo injectives.** For a map `t : X → X'` lifted by
`(t₀, t₁)` to the presentations chosen by `TauCeti.stableTranspose`, the translate of the stable
class of `t` is the class of `D Tr(t)`. -/
theorem stableTranslateObjIsoMatlisDualTranspose_naturality
    {X X' : FinitelyPresentedStableModule.{u, max u v} A} (t : X.obj.as ⟶ X'.obj.as)
    {t₀ : (FinitelyPresentedStableModule.presentation X).P₀ →ₗ[A]
      (FinitelyPresentedStableModule.presentation X').P₀}
    {t₁ : (FinitelyPresentedStableModule.presentation X).P₁ →ₗ[A]
      (FinitelyPresentedStableModule.presentation X').P₁}
    (ht₀ : (FinitelyPresentedStableModule.presentation X').π ∘ₗ t₀ =
      t.hom ∘ₗ (FinitelyPresentedStableModule.presentation X).π)
    (ht₁ : t₀ ∘ₗ (FinitelyPresentedStableModule.presentation X).p =
      (FinitelyPresentedStableModule.presentation X').p ∘ₗ t₁) :
    (stableTranslate R A E).map
        (ObjectProperty.homMk ((ExactStructure.abelian _).projectiveStableFunctor.map t)) ≫
      (stableTranslateObjIsoMatlisDualTranspose X').hom =
    (stableTranslateObjIsoMatlisDualTranspose X).hom ≫
      (ExactStructure.abelian _).injectiveStableFunctor.map
        (ModuleCat.matlisDualTransposeMap R E _ _ ht₁) := by
  have hT := (AuslanderReitenTranspose.stableMap_quotient_map
    (FinitelyPresentedStableModule.presentation X).exact.linearMap_comp_eq_zero
    (FinitelyPresentedStableModule.presentation X').exact
    (FinitelyPresentedStableModule.presentation X').surjective t.hom t₀ t₁ ht₀ ht₁).symm
  -- The component squares: `stableTranslate = stableTranslateFunctor`, its computation on maps,
  -- and `D Tr(t)` through the bundled dual of `Tr X`.
  have key := congrArg (ExactStructure.abelian _).injectiveStableFunctor.map
    (ModuleCat.matlisDualOp_map_comp_matlisDualOpTransposeIso_hom R E _ _ ht₁)
  rw [Functor.map_comp, Functor.map_comp] at key
  rw [Functor.congr_hom (stableTranslate_def (R := R) (A := A) (E := E)),
    stableTranslateFunctor_map _
      (ObjectProperty.homMk ((ExactStructure.abelian _).projectiveStableFunctor.map t)) _ hT]
  simp only [stableTranslateObjIsoMatlisDualTranspose, Iso.trans_hom, eqToIso.hom,
    Functor.mapIso_hom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Iso.inv_hom_id_assoc, key]

include hE in
/-- **`τ τ⁻ N ≅ N`** modulo injectives, with `τ` computed as `D Tr` of the presentation chosen by
`TauCeti.stableTranspose`. -/
noncomputable def matlisDualTransposeInverseIso
    (N : FinitelyGeneratedInjectiveStableModule.{u, max u v} A) :
    (ExactStructure.abelian _).injectiveStableFunctor.obj
        (ModuleCat.matlisDualTranspose R E (FinitelyPresentedStableModule.presentation
          ((stableTranslateEquivalence R A E hE).inverse.obj N))) ≅
      (ExactStructure.abelian _).injectiveStableFunctor.obj N.obj.as :=
  haveI := finite_of_forall_isMaximal hE
  (stableTranslateObjIsoMatlisDualTranspose _).symm ≪≫
    ((finiteStableTranslateCompιIso R A E).app _).symm ≪≫
    (ObjectProperty.ι _).mapIso (finiteStableTranslateInverseIso hE N)

include hE in
/-- **Naturality of `τ τ⁻ N ≅ N` modulo injectives.** For a map `g : N ⟶ N'` and a lift
`(t₀, t₁)` of a representative `t` of `τ⁻ g` to the chosen presentations, `D Tr(t)` corresponds to
`g`. -/
theorem matlisDualTransposeInverseIso_naturality
    {N N' : FinitelyGeneratedInjectiveStableModule.{u, max u v} A} (g : N ⟶ N')
    (t : ((stableTranslateEquivalence R A E hE).inverse.obj N).obj.as ⟶
      ((stableTranslateEquivalence R A E hE).inverse.obj N').obj.as)
    (ht : (ExactStructure.abelian _).projectiveStableFunctor.map t =
      ((stableTranslateEquivalence R A E hE).inverse.map g).hom)
    {t₀ : (FinitelyPresentedStableModule.presentation
        ((stableTranslateEquivalence R A E hE).inverse.obj N)).P₀ →ₗ[A]
      (FinitelyPresentedStableModule.presentation
        ((stableTranslateEquivalence R A E hE).inverse.obj N')).P₀}
    {t₁ : (FinitelyPresentedStableModule.presentation
        ((stableTranslateEquivalence R A E hE).inverse.obj N)).P₁ →ₗ[A]
      (FinitelyPresentedStableModule.presentation
        ((stableTranslateEquivalence R A E hE).inverse.obj N')).P₁}
    (ht₀ : (FinitelyPresentedStableModule.presentation
        ((stableTranslateEquivalence R A E hE).inverse.obj N')).π ∘ₗ t₀ =
      t.hom ∘ₗ (FinitelyPresentedStableModule.presentation
        ((stableTranslateEquivalence R A E hE).inverse.obj N)).π)
    (ht₁ : t₀ ∘ₗ (FinitelyPresentedStableModule.presentation
        ((stableTranslateEquivalence R A E hE).inverse.obj N)).p =
      (FinitelyPresentedStableModule.presentation
        ((stableTranslateEquivalence R A E hE).inverse.obj N')).p ∘ₗ t₁) :
    (ExactStructure.abelian _).injectiveStableFunctor.map
        (ModuleCat.matlisDualTransposeMap R E _ _ ht₁) ≫
      (matlisDualTransposeInverseIso hE N').hom =
    (matlisDualTransposeInverseIso hE N).hom ≫ g.hom := by
  have := finite_of_forall_isMaximal hE
  have hs : ObjectProperty.homMk ((ExactStructure.abelian _).projectiveStableFunctor.map t) =
      (stableTranslateEquivalence R A E hE).inverse.map g :=
    ObjectProperty.hom_ext _ ht
  -- The three component squares: `τ ≅ D Tr`, `τ ≅ finiteStableTranslate`, and the counit.
  have h₁ := stableTranslateObjIsoMatlisDualTranspose_naturality (R := R) (E := E) t ht₀ ht₁
  rw [hs, ← Iso.inv_comp_eq] at h₁
  have h₃ := congrArg (ObjectProperty.ι _).map (finiteStableTranslateInverseIso_naturality hE g)
  rw [Functor.map_comp, Functor.map_comp, ObjectProperty.ι_map (f := g)] at h₃
  simp only [matlisDualTransposeInverseIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_inv, ← h₁, Category.assoc, Iso.hom_inv_id_assoc]
  rw [(finiteStableTranslateCompιIso R A E).inv.naturality_assoc, Functor.comp_map, h₃]

end Comparison

end TauCeti
