/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.Finiteness.Cardinality
import TauCeti.Algebra.Homology.DerivedCategory.FiniteHom

/-!
# Examples: finiteness of derived Hom modules over Noetherian rings

These examples exercise `TauCeti.Algebra.Homology.DerivedCategory.FiniteHom` and its
cohomological boundedness and finiteness hypotheses:

* an object of `DerivedCategory (ModuleCat ℤ)` concentrated in both degrees `≥ 1` and `≤ 0` is
  zero and has finite cohomology in every degree;
* a single complex in degree `0` satisfies `IsGE 0`, `IsLE 0`, `IsGE (-1)`, and `IsLE 3`, but
  not `IsGE 1`;
* the degreewise finite cohomology hypothesis holds for `ℤ` concentrated in degree `0` and fails
  for `ℕ →₀ ℤ` concentrated in degree `0`;
* `DerivedCategory.moduleFinite_hom_of_isLE_of_isGE`,
  `DerivedCategory.moduleFinite_end_of_isGE_of_isLE`, and
  `DerivedCategory.moduleFinite_algHom_range_of_isGE_of_isLE` yield finiteness of `X ⟶ X`,
  `End X`, and `α.range` for a finitely generated module concentrated in degree `0` over a
  commutative Noetherian ring `A`.
-/

open CategoryTheory Limits DerivedCategory Triangulated

universe t w v u

example [HasDerivedCategory.{w} (ModuleCat.{v} ℤ)]
    (X : DerivedCategory (ModuleCat.{v} ℤ)) [X.IsGE 1] [X.IsLE 0] :
    IsZero X ∧ ∀ i : ℤ, Module.Finite ℤ ((homologyFunctor (ModuleCat.{v} ℤ) i).obj X) := by
  have hX : IsZero X := TStructure.t.isZero X 0 1 (by omega)
  refine ⟨hX, fun i ↦ ?_⟩
  have hHi : IsZero ((homologyFunctor (ModuleCat.{v} ℤ) i).obj X) :=
    (homologyFunctor (ModuleCat.{v} ℤ) i).map_isZero hX
  have : Subsingleton ((homologyFunctor (ModuleCat.{v} ℤ) i).obj X) :=
    ModuleCat.isZero_iff_subsingleton.mp hHi
  infer_instance

attribute [local instance] HasDerivedCategory.standard

example :
    let X := (singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ℤ × ℤ))
    (X.IsGE 0 ∧ X.IsLE 0) ∧ (X.IsGE (-1) ∧ X.IsLE 3) ∧ ¬ X.IsGE 1 := by
  intro X
  refine ⟨⟨inferInstance, inferInstance⟩,
    ⟨TStructure.t.isGE_of_ge X (-1) 0 (by omega), TStructure.t.isLE_of_le X 0 3 (by omega)⟩, ?_⟩
  intro hge
  have hz : IsZero ((homologyFunctor (ModuleCat.{0} ℤ) 0).obj X) :=
    isZero_of_isGE X 1 0 (by omega)
  have hz' : IsZero (ModuleCat.of ℤ (ℤ × ℤ)) :=
    hz.of_iso ((singleFunctorCompHomologyFunctorIso (ModuleCat.{0} ℤ) 0).app _).symm
  have h01 : (1, 0) = ((0, 0) : ℤ × ℤ) := by
    have hsub := ModuleCat.isZero_iff_subsingleton.mp hz'
    exact Subsingleton.elim _ _
  exact one_ne_zero (congrArg Prod.fst h01)

example :
    (∀ i : ℤ, Module.Finite ℤ
      ((homologyFunctor (ModuleCat.{0} ℤ) i).obj
        ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ)))) ∧
    ¬ (∀ i : ℤ, Module.Finite ℤ
      ((homologyFunctor (ModuleCat.{0} ℤ) i).obj
        ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ℕ →₀ ℤ))))) := by
  constructor
  · intro i
    by_cases hi : i = 0
    · subst hi
      have e : ModuleCat.of ℤ ℤ ≅ (homologyFunctor (ModuleCat.{0} ℤ) 0).obj
          ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ)) :=
        ((singleFunctorCompHomologyFunctorIso (ModuleCat.{0} ℤ) 0).app (ModuleCat.of ℤ ℤ)).symm
      exact Module.Finite.equiv e.toLinearEquiv
    · have hHi : IsZero ((homologyFunctor (ModuleCat.{0} ℤ) i).obj
          ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ))) := by
        rcases lt_or_gt_of_ne hi with hlt | hgt
        · exact isZero_of_isGE _ 0 i hlt
        · exact isZero_of_isLE _ 0 i hgt
      have : Subsingleton _ := ModuleCat.isZero_iff_subsingleton.mp hHi
      infer_instance
  · intro h
    have : Module.Finite ℤ ((homologyFunctor (ModuleCat.{0} ℤ) 0).obj
        ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ℕ →₀ ℤ)))) := h 0
    have e : (homologyFunctor (ModuleCat.{0} ℤ) 0).obj
        ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ℕ →₀ ℤ))) ≅
        ModuleCat.of ℤ (ℕ →₀ ℤ) :=
      (singleFunctorCompHomologyFunctorIso (ModuleCat.{0} ℤ) 0).app (ModuleCat.of ℤ (ℕ →₀ ℤ))
    have h0 : Module.Finite ℤ (ℕ →₀ ℤ) := Module.Finite.equiv e.toLinearEquiv
    have : Finite ℕ :=
      Module.Finite.finite_basis (Finsupp.basisSingleOne : Module.Basis ℕ ℤ (ℕ →₀ ℤ))
    exact not_finite ℕ

example {A : Type u} [CommRing A] [IsNoetherianRing A] {H : Type t} [Semiring H] [Algebra A H] :
    let X := (singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
    Module.Finite A (X ⟶ X) ∧ Module.Finite A (End X) ∧
      ∀ α : H →ₐ[A] End X, Module.Finite A α.range := by
  intro X
  have hfin : ∀ i : ℤ, 0 ≤ i → i ≤ 0 →
      Module.Finite A ((homologyFunctor (ModuleCat.{u} A) i).obj X) := by
    intro i h0 h1
    have hi : i = 0 := by omega
    subst hi
    have e : ModuleCat.of A A ≅ (homologyFunctor (ModuleCat.{u} A) 0).obj X :=
      ((singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0).app (ModuleCat.of A A)).symm
    exact Module.Finite.equiv e.toLinearEquiv
  exact ⟨X.moduleFinite_hom_of_isLE_of_isGE X 0 0 hfin hfin,
    X.moduleFinite_end_of_isGE_of_isLE 0 0 hfin,
    fun α ↦ X.moduleFinite_algHom_range_of_isGE_of_isLE 0 0 hfin α⟩
