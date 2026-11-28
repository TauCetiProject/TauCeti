/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Equivalence
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.ScalarChange

/-!
# Basic split `K₀` theory of finitely generated projective modules

For a possibly noncommutative ring `R`, this file develops the basic theory of `SplitK0` of
`(finiteProjectiveModules R).FullSubcategory`:

* additivity on products (`TauCeti.SplitK0.of_eq_add_of_linearEquiv_prod`), finite products
  (`TauCeti.SplitK0.of_eq_sum_of_linearEquiv_pi`), and finite-free classes
  (`TauCeti.SplitK0.of_eq_nsmul_of_linearEquiv_fin`, `TauCeti.SplitK0.of_finFreeObj`),
* normal form `[P] - n • [R]`
  (`TauCeti.FiniteProjectiveModules.exists_of_sub_nsmul_of_finiteProjectiveModulesRegular_eq`),
* Morita invariance (`CategoryTheory.Equivalence.finiteProjectiveModulesSplitK0Equiv`),
* agreement of extension of scalars along a ring isomorphism with restriction of scalars along its
  inverse (`RingEquiv.splitK0Map_finiteProjectiveModulesExtendScalars_eq_restrictScalars`).

## References

* C. A. Weibel, *The K-book*, Chapter II, §2, Lemma 2.1, p. 5.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u u'

namespace TauCeti.SplitK0

variable {R : Type u} [Ring R]

/-- **Additivity on products.** The class of a finitely generated projective module isomorphic to
a product `P × Q` is the sum of the classes of `P` and `Q`. -/
theorem of_eq_add_of_linearEquiv_prod {X P Q : (finiteProjectiveModules R).FullSubcategory}
    (e : X.obj ≃ₗ[R] (P.obj × Q.obj)) : of.{u} X = of.{u} P + of.{u} Q := by
  rw [← of_biprod]
  exact of_congr ((finiteProjectiveModules R).fullyFaithfulι.preimageIso
    (e.trans (FiniteProjectiveModules.biprodLinearEquiv P Q).symm).toModuleIso)

/-- **Additivity on finite products.** The class of a finitely generated projective module
isomorphic to a finite product is the sum of the classes of the factors. -/
theorem of_eq_sum_of_linearEquiv_pi {ι : Type} [Fintype ι]
    {X : (finiteProjectiveModules R).FullSubcategory}
    (P : ι → (finiteProjectiveModules R).FullSubcategory)
    (e : X.obj ≃ₗ[R] (i : ι) → (P i).obj) : of.{u} X = ∑ i, of.{u} (P i) := by
  have := PreservesFiniteProducts.of_preserves_binary_and_terminal (finiteProjectiveModules R).ι
  have : PreservesBiproduct P (finiteProjectiveModules R).ι :=
    preservesBiproduct_of_preservesProduct _
  rw [← of_biproduct.{u} P]
  exact of_congr ((finiteProjectiveModules R).fullyFaithfulι.preimageIso
    (e.toModuleIso ≪≫ (ModuleCat.biproductIsoPi fun i ↦ (P i).obj).symm ≪≫
      ((finiteProjectiveModules R).ι.mapBiproduct P).symm))

/-- The class of a finitely generated projective module isomorphic to `Rⁿ` is `n` times the class
of `R`. -/
theorem of_eq_nsmul_of_linearEquiv_fin {X R' : (finiteProjectiveModules R).FullSubcategory}
    {n : ℕ} (e : X.obj ≃ₗ[R] (Fin n → R)) (e' : R'.obj ≃ₗ[R] R) : of.{u} X = n • of.{u} R' := by
  rw [of_eq_sum_of_linearEquiv_pi (fun _ : Fin n ↦ R')
      (e.trans (LinearEquiv.piCongrRight fun _ ↦ e'.symm)),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- The class of `Fin n → R` in `SplitK0` is `n` times `[R]`. -/
@[simp] theorem of_finFreeObj (n : ℕ) :
    SplitK0.of.{u} (FiniteProjectiveModules.finFreeObj R n) =
      n • SplitK0.of.{u} (finiteProjectiveModulesRegular R) :=
  of_eq_nsmul_of_linearEquiv_fin (X := FiniteProjectiveModules.finFreeObj R n)
    (R' := finiteProjectiveModulesRegular R) (.refl _ _) (.refl _ _)

end TauCeti.SplitK0

namespace TauCeti.FiniteProjectiveModules

/-- **Normal form in projective `K₀`.** Every class in the split `K₀` of finitely generated
projective `A`-modules is `[P] - n[A]` for a finitely generated projective `A`-module `P` and a
natural number `n` (Weibel, *The K-book*, Lemma II.2.1). -/
theorem exists_of_sub_nsmul_of_finiteProjectiveModulesRegular_eq (A : Type u) [Ring A]
    (x : SplitK0.{u} (finiteProjectiveModules A).FullSubcategory) :
    ∃ (P : (finiteProjectiveModules A).FullSubcategory) (n : ℕ),
      SplitK0.of.{u} P - n • SplitK0.of.{u} (finiteProjectiveModulesRegular A) = x := by
  obtain ⟨P₁, P₂, rfl⟩ := SplitK0.exists_eq_sub.{u} x
  obtain ⟨Q, n, ⟨e⟩⟩ := exists_biprod_iso_fin P₂
  refine ⟨P₁ ⊞ Q, n, ?_⟩
  rw [SplitK0.of_biprod.{u}, ← SplitK0.of_finFreeObj, ← SplitK0.of_congr.{u} e,
    SplitK0.of_biprod.{u}]
  abel

end TauCeti.FiniteProjectiveModules

namespace CategoryTheory.Equivalence

open TauCeti

variable {A : Type u} [Ring A] {B : Type u'} [Ring B] (e : ModuleCat.{u} A ≌ ModuleCat.{u'} B)

/-- **Morita invariance of `SplitK0` of finitely generated projective modules.** -/
noncomputable def finiteProjectiveModulesSplitK0Equiv :
    SplitK0.{u} (finiteProjectiveModules A).FullSubcategory ≃+
      SplitK0.{u'} (finiteProjectiveModules B).FullSubcategory :=
  SplitK0.mapEquiv.{u, u'} e.finiteProjectiveModulesEquivalence

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_of (P) :
    e.finiteProjectiveModulesSplitK0Equiv (SplitK0.of.{u} P) =
      SplitK0.of.{u'} (e.finiteProjectiveModulesEquivalence.functor.obj P) :=
  SplitK0.mapEquiv_of.{u, u'} _ P

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_symm_of (Q) :
    e.finiteProjectiveModulesSplitK0Equiv.symm (SplitK0.of.{u'} Q) =
      SplitK0.of.{u} (e.finiteProjectiveModulesEquivalence.inverse.obj Q) :=
  SplitK0.mapEquiv_symm_of.{u, u'} _ Q

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_toAddMonoidHom :
    (e.finiteProjectiveModulesSplitK0Equiv :
        SplitK0.{u} (finiteProjectiveModules A).FullSubcategory →+
          SplitK0.{u'} (finiteProjectiveModules B).FullSubcategory) =
      SplitK0.map.{u, u'} e.finiteProjectiveModulesEquivalence.functor :=
  SplitK0.mapEquiv_toAddMonoidHom.{u, u'} _

end CategoryTheory.Equivalence

namespace RingEquiv

open TauCeti

variable {R S : Type u} [Ring R] [Ring S]

/-- On `SplitK0`, extension of scalars along a ring isomorphism `e : R ≃+* S` agrees with
restriction of scalars along `e.symm`. -/
theorem splitK0Map_finiteProjectiveModulesExtendScalars_eq_restrictScalars (e : R ≃+* S) :
    SplitK0.map.{u, u} e.toRingHom.finiteProjectiveModulesExtendScalars =
      ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.finiteProjectiveModulesSplitK0Equiv
        : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory →+
          SplitK0.{u} (finiteProjectiveModules S).FullSubcategory) :=
  SplitK0.hom_ext fun P ↦ by
    simpa using SplitK0.of_congr.{u} <| ObjectProperty.isoMk _ <|
      eqToIso (e.toRingHom.finiteProjectiveModulesExtendScalars_obj_obj P) ≪≫
        (BalancedExtension.functorRingEquivIso.{u, u, u} e).app P.obj ≪≫
        eqToIso ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
          e).symm.finiteProjectiveModulesEquivalence_functor_obj_obj P).symm

end RingEquiv
