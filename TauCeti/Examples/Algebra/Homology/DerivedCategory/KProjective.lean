/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import TauCeti.Algebra.Homology.DerivedCategory.KProjective

/-!
# Examples: K-projective and contractible complexes in the derived category

These examples exercise `TauCeti.Algebra.Homology.DerivedCategory.KProjective`:

* for any K-projective cochain complex `K` in an `A`-linear abelian category over a commutative
  ring `A`, `CochainComplex.IsKProjective.homotopyToDerivedEndEquivQ` provides an `A`-algebra
  equivalence between homotopy endomorphisms of `K` and derived endomorphisms of `Q.obj K`, and
  for any chain-level action `α : H →ₐ[A] End K` the descended action images compare via
  `TauCeti.quotientActionRangeMap`, `TauCeti.derivedActionRangeMap`, and
  `CochainComplex.IsKProjective.homotopyToDerivedActionRangeEquivQ`;
* the mapping cone of `𝟙 K` on a single complex `K = ℤ[0]` is nonzero at the chain level
  (`𝟙 (mappingCone (𝟙 K)) ≠ 0`), yet its identity vanishes in both the homotopy category and the
  derived category, illustrating why `Q.mapEndAlgHom` is surjective rather than injective on chain
  endomorphisms.
-/

open CategoryTheory Limits DerivedCategory CochainComplex.IsKProjective

universe t' t w v u

example {A : Type u} [CommRing A] {C : Type v} [Category.{w} C] [Abelian C] [Linear A C]
    [HasDerivedCategory.{t} C] (K : CochainComplex C ℤ) [K.IsKProjective] :
    Nonempty (End ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ≃ₐ[A] End (Q.obj K)) :=
  ⟨homotopyToDerivedEndEquivQ A K⟩

example {A : Type u} [CommRing A] {C : Type v} [Category.{w} C] [Abelian C] [Linear A C]
    [HasDerivedCategory.{t} C] {H : Type t'} [Semiring H] [Algebra A H]
    (K : CochainComplex C ℤ) [K.IsKProjective] (α : H →ₐ[A] End K) (h : H) :
    Function.Surjective (TauCeti.quotientActionRangeMap A K α) ∧
    Function.Surjective (TauCeti.derivedActionRangeMap A K α) ∧
    homotopyToDerivedActionRangeEquivQ A K α
      (TauCeti.quotientActionRangeMap A K α (α.rangeRestrict h)) =
      TauCeti.derivedActionRangeMap A K α (α.rangeRestrict h) :=
  ⟨TauCeti.quotientActionRangeMap_surjective A K α,
    TauCeti.derivedActionRangeMap_surjective A K α,
    homotopyToDerivedActionRangeEquivQ_apply_quotientActionRangeMap A K α (α.rangeRestrict h)⟩

attribute [local instance] HasDerivedCategory.standard

example :
    let K := (HomologicalComplex.single (ModuleCat.{0} ℤ) (.up ℤ) 0).obj (ModuleCat.of ℤ ℤ)
    let C := CochainComplex.mappingCone (𝟙 K)
    (𝟙 C ≠ 0) ∧
    (HomotopyCategory.quotient (ModuleCat.{0} ℤ) (.up ℤ)).map (𝟙 C) = 0 ∧
    Q.map (𝟙 C) = 0 := by
  intro K C
  have hne : 𝟙 C ≠ 0 := by
    intro h
    have hX0 : IsZero (C.X 0) :=
      (IsZero.iff_id_eq_zero _).mpr (by simpa using congrArg (fun f : C ⟶ C ↦ f.f 0) h)
    have hK0 : IsZero (K.X 0) := ((CochainComplex.mappingCone.isZero_X_iff (𝟙 K) 0).mp hX0).2
    have hZ : IsZero (ModuleCat.of ℤ ℤ) :=
      hK0.of_iso (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of ℤ ℤ)).symm
    have hsub : Subsingleton (ModuleCat.of ℤ ℤ) := ModuleCat.isZero_iff_subsingleton.mp hZ
    exact one_ne_zero (Subsingleton.elim (1 : ℤ) 0)
  have hK : (HomotopyCategory.quotient (ModuleCat.{0} ℤ) (.up ℤ)).map (𝟙 C) = 0 := by
    rw [← Functor.map_zero (HomotopyCategory.quotient _ _)]
    exact HomotopyCategory.eq_of_homotopy _ _ (CochainComplex.mappingCone.homotopyToZeroOfId K)
  have hD : Q.map (𝟙 C) = 0 := by
    rw [← cancel_epi ((quotientCompQhIso (ModuleCat.{0} ℤ)).hom.app C),
      ← quotientCompQhIso_hom_naturality, hK]
    simp
  exact ⟨hne, hK, hD⟩
