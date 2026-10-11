/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.CocyclePairing
public import TauCeti.CategoryTheory.Exact.Stable.Injective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# The injectively trivial part of the Auslander–Reiten pairing

A morphism `N → D Tr(f)` factors through an injective object exactly when its
Nakayama Hom functional belongs to the image of dual restriction to `ker f`.
This identifies the subspace killed on the Hom side of Auslander–Reiten duality.
The cocycle pairing kills exactly the same morphisms as the injective stable quotient.
It therefore identifies injective stable Hom into the translate with the scalar dual
of Hom cocycles modulo coboundaries, naturally in the coefficient module.

The statement uses the existing injective stable category of modules and
does not depend on a choice of injective envelope. It applies to arbitrary algebras
over a field and maps between finite projectives, without minimality or exactness.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.2.
-/

public section

namespace LinearMap

open TauCeti CategoryTheory
open scoped ModuleCat.Algebra

universe u v w

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]
  {P₀ P₁ : Type max u v w}
  [AddCommGroup P₀] [Module A P₀] [Module.Finite A P₀] [Module.Projective A P₀]
  [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁] [Module.Projective A P₁]

/-- Maps into `D Tr(f)` factoring through injective objects correspond exactly to
the image of dual restriction to the kernel of `f` under the Nakayama Hom pairing. -/
theorem auslanderReitenTranslate_injectiveStableFunctor_map_eq_zero_iff
    (f : P₁ →ₗ[A] P₀) (N : ModuleCat.{max u v w} A)
    (g : N →ₗ[A] AuslanderReitenTranslate k f) :
    (ExactStructure.abelian (ModuleCat.{max u v w} A)).injectiveStableFunctor.map
        (ModuleCat.ofHom g) = 0 ↔
      (nakayamaHomEquiv k A P₁ N).symm ((auslanderReitenTranslateToNakayama f).comp g) ∈
        range (((ker f).subtype.lcomp k N).dualMap) := by
  let I := Injective.under N
  let j := Injective.ι N
  let : Module.Injective A I :=
    (Module.injective_iff_injective_object A I).mpr (inferInstance : Injective I)
  rw [← auslanderReitenTranslate_exists_extension_iff f j.hom
    ((ModuleCat.mono_iff_injective j).mp inferInstance) g]
  rw [ExactStructure.injectiveStableFunctor_map_eq_zero_iff,
    ExactStructure.factorsThrough_injective_iff_exists_extension
      (ExactStructure.abelian (ModuleCat.{max u v w} A)) j
      ((ExactStructure.abelian_isInflation_iff j).mpr inferInstance)
      ((ExactStructure.abelian_isInjective_iff I).mpr inferInstance)]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h.hom, congrArg ModuleCat.Hom.hom hh⟩
  · rintro ⟨h, hh⟩
    exact ⟨ModuleCat.ofHom h, ModuleCat.hom_ext hh⟩

/-- The cocycle pairing kills exactly the morphisms killed by the injective stable
quotient functor. -/
theorem auslanderReitenCocyclePairing_eq_zero_iff_injectiveStableFunctor_map_eq_zero
    (f : P₁ →ₗ[A] P₀) (N : ModuleCat.{max u v w} A)
    (g : N →ₗ[A] AuslanderReitenTranslate k f) :
    auslanderReitenCocyclePairing f g = 0 ↔
      (ExactStructure.abelian (ModuleCat.{max u v w} A)).injectiveStableFunctor.map
        (ModuleCat.ofHom g) = 0 := by
  rw [auslanderReitenCocyclePairing_eq_zero_iff,
    auslanderReitenTranslate_injectiveStableFunctor_map_eq_zero_iff]

/-- Injective stable Hom into `D Tr(f)` is the scalar dual of Hom cocycles modulo
coboundaries. This comparison does not choose an injective embedding. -/
noncomputable def auslanderReitenStableHomEquiv
    (f : P₁ →ₗ[A] P₀) (N : ModuleCat.{max u v w} A) :
    ((ExactStructure.abelian (ModuleCat.{max u v w} A)).injectiveStableFunctor.obj N ⟶
      (ExactStructure.abelian (ModuleCat.{max u v w} A)).injectiveStableFunctor.obj
        (ModuleCat.of A (AuslanderReitenTranslate k f))) ≃ₗ[k]
      Module.Dual k (HomCocycleQuotient (k := k) f N) := by
  let F := (ExactStructure.abelian (ModuleCat.{max u v w} A)).injectiveStableFunctor
  letI : Module k (N ⟶ ModuleCat.of A (AuslanderReitenTranslate k f)) :=
    Linear.homModule (R := k) N (ModuleCat.of A (AuslanderReitenTranslate k f))
  let q := F.mapLinearMap k (X := N) (Y := ModuleCat.of A (AuslanderReitenTranslate k f))
  let p : (N ⟶ ModuleCat.of A (AuslanderReitenTranslate k f)) →ₗ[k]
      Module.Dual k (HomCocycleQuotient (k := k) f N) :=
    { toFun := fun g ↦ auslanderReitenCocyclePairing f g.hom
      map_add' := by intros; simp
      map_smul' := by
        intro c g
        rw [← map_smul]
        congr 1
        apply LinearMap.ext
        intro x
        -- The categorical scalar action restricts the algebra action on the translate.
        exact IsScalarTower.algebraMap_smul A c (g.hom x) }
  have hker : ker q = ker p := by
    ext g
    exact (auslanderReitenCocyclePairing_eq_zero_iff_injectiveStableFunctor_map_eq_zero
      f N g.hom).symm
  have hp : Function.Surjective p := by
    intro χ
    obtain ⟨g, hg⟩ := auslanderReitenCocyclePairing_surjective f χ
    exact ⟨ModuleCat.ofHom g, hg⟩
  exact (q.quotKerEquivOfSurjective F.map_surjective).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (p.quotKerEquivOfSurjective hp))

/-- The stable Hom comparison sends the stable class of a map to its cocycle pairing. -/
@[simp]
theorem auslanderReitenStableHomEquiv_map
    (f : P₁ →ₗ[A] P₀) (N : ModuleCat.{max u v w} A)
    (g : N ⟶ ModuleCat.of A (AuslanderReitenTranslate k f)) :
    auslanderReitenStableHomEquiv f N
      ((ExactStructure.abelian (ModuleCat.{max u v w} A)).injectiveStableFunctor.map g) =
      auslanderReitenCocyclePairing f g.hom := by
  let : Module k (N ⟶ ModuleCat.of A (AuslanderReitenTranslate k f)) :=
    Linear.homModule (R := k) N (ModuleCat.of A (AuslanderReitenTranslate k f))
  dsimp only [auslanderReitenStableHomEquiv, LinearEquiv.trans_apply]
  -- `mapLinearMap` has the functor map as its underlying function.
  erw [quotKerEquivOfSurjective_symm_apply]
  rw [Submodule.quotEquivOfEq_mk]
  erw [quotKerEquivOfSurjective_apply_mk]

/-- The inverse comparison sends a cocycle pairing to the stable class of its map. -/
@[simp]
theorem auslanderReitenStableHomEquiv_symm_pairing
    (f : P₁ →ₗ[A] P₀) (N : ModuleCat.{max u v w} A)
    (g : N ⟶ ModuleCat.of A (AuslanderReitenTranslate k f)) :
    (auslanderReitenStableHomEquiv f N).symm (auslanderReitenCocyclePairing f g.hom) =
      (ExactStructure.abelian (ModuleCat.{max u v w} A)).injectiveStableFunctor.map g := by
  apply (auslanderReitenStableHomEquiv f N).injective
  simp

/-- Precomposition in the injective stable category corresponds to the dual of
postcomposition on Hom cocycle classes. -/
theorem auslanderReitenStableHomEquiv_naturality
    (f : P₁ →ₗ[A] P₀) {N N' : ModuleCat.{max u v w} A} (g : N ⟶ N')
    (h : (ExactStructure.abelian (ModuleCat.{max u v w} A)).injectiveStableFunctor.obj N' ⟶
      (ExactStructure.abelian (ModuleCat.{max u v w} A)).injectiveStableFunctor.obj
        (ModuleCat.of A (AuslanderReitenTranslate k f))) :
    auslanderReitenStableHomEquiv f N
        ((ExactStructure.abelian (ModuleCat.{max u v w} A)).injectiveStableFunctor.map g ≫ h) =
      (homCocycleQuotientMap (k := k) f g.hom).dualMap
        (auslanderReitenStableHomEquiv f N' h) := by
  obtain ⟨h, rfl⟩ :=
    (ExactStructure.abelian (ModuleCat.{max u v w} A)).injectiveStableFunctor.map_surjective h
  rw [← Functor.map_comp, auslanderReitenStableHomEquiv_map,
    auslanderReitenStableHomEquiv_map]
  exact (auslanderReitenCocyclePairing_naturality f g.hom h.hom).symm

end LinearMap
