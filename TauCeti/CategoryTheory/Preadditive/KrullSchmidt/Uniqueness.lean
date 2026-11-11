/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Logic.Equiv.Option
import TauCeti.CategoryTheory.Limits.Shapes.Biproduct
import TauCeti.CategoryTheory.Preadditive.Indecomposable
import TauCeti.RingTheory.LocalRing.Basic

/-!
# Uniqueness of decompositions into objects with local endomorphism rings

In a preadditive category with finite biproducts, two decompositions `⨁ i, X i ≅ ⨁ j, Y j` of the
same object into objects with local endomorphism rings agree up to a bijection of the summands:
there is `σ : ι ≃ κ` with `X i ≅ Y (σ i)` for every `i`. This is the Krull-Remak-Schmidt-Azumaya
theorem in its categorical form. It needs no hypothesis on the category beyond finite biproducts;
in a Krull-Schmidt category it gives the uniqueness of the decomposition of every object.

The proof is the exchange argument. Write `⨁ X = X i₀ ⊞ X'` (`TauCeti.biproductSubtypeNeIso`).
The identity of `X i₀` is the sum over `j` of its composites through `Y j`, and `End (X i₀)` is
local, so one composite is invertible; then `X i₀` is a retract of `Y j`, and since `End (Y j)` is
local and so has no nontrivial idempotents, `X i₀ ≅ Y j` (`TauCeti.isIso_of_isIso_comp`). Writing
`⨁ Y = Y j ⊞ Y'`, the isomorphism `X i₀ ⊞ X' ≅ Y j ⊞ Y'` has an invertible upper-left entry, so
Gaussian elimination gives `X' ≅ Y'` (`CategoryTheory.Biprod.isoElim`), and induction on the number
of summands finishes the proof.

## Main results

* `TauCeti.exists_equiv_iso_of_biproduct_iso_of_isLocalRing`: uniqueness of decompositions into
  objects with local endomorphism rings.

For finite-length modules the same statement, with indecomposable summands, is
`TauCeti.exists_equiv_iso_of_biproduct_iso` (and `TauCeti.exists_equiv_iso_of_iso_biproduct`),
proved there through external direct sums; indecomposable modules of finite length have local
endomorphism rings by Fitting's lemma.

## References

* Henning Krause, *Krull-Schmidt categories and projective covers*, Expo. Math. 33 (2015),
  535–549, Theorem 4.2 and Corollary 4.3.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe w w' v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- **The exchange step.** If `A ⊞ A' ≅ ⨁ Y` with `End A` and all `End (Y j)` local, then
`A ≅ Y j` for some `j`, and `A'` is isomorphic to the biproduct of the other summands. -/
private theorem exchange {κ : Type w} [Finite κ] (Y : κ → C)
    (hY : ∀ j, IsLocalRing (End (Y j))) {A A' : C} [IsLocalRing (End A)] (g : A ⊞ A' ≅ ⨁ Y) :
    ∃ j, Nonempty (A ≅ Y j) ∧ Nonempty (A' ≅ ⨁ Subtype.restrict (· ≠ j) Y) := by
  classical
  have := Fintype.ofFinite κ
  -- The identity of `A` is the sum of its composites through the `Y j`; one is invertible.
  have hsum : ∑ j, End.of (biprod.inl ≫ g.hom ≫ biproduct.π Y j ≫ biproduct.ι Y j ≫ g.inv ≫
      biprod.fst) = 1 := by
    ext
    have h : ∑ j, biproduct.π Y j ≫ biproduct.ι Y j ≫ g.inv ≫ biprod.fst = g.inv ≫ biprod.fst := by
      simp only [← Category.assoc, ← Preadditive.sum_comp, biproduct.total, Category.id_comp]
    simp only [End.sum_asHom, End.one_asHom, ← Preadditive.comp_sum, h, Iso.hom_inv_id_assoc,
      biprod.inl_fst]
  obtain ⟨j, -, hj⟩ := IsLocalRing.exists_of_isUnit_sum (hsum ▸ isUnit_one : IsUnit (∑ j, _))
  have := hY j
  -- `A` is a retract of `Y j`, whose idempotents are trivial, so `A ≅ Y j`.
  have : IsIso (biprod.inl ≫ g.hom ≫ biproduct.π Y j) :=
    isIso_of_isIso_comp
      (fun h ↦ indecomposable_of_isLocalRing_end.1 ((IsZero.iff_id_eq_zero A).2 h))
      (fun e he ↦ (IsIdempotentElem.eq_zero_or_eq_one_of_isLocalRing
        (a := End.of e) (End.ext he)).imp (congrArg End.asHom) (congrArg End.asHom))
      _ (biproduct.ι Y j ≫ g.inv ≫ biprod.fst)
      (by simpa only [Category.assoc] using (isUnit_iff_isIso _).1 hj)
  refine ⟨j, ⟨asIso (biprod.inl ≫ g.hom ≫ biproduct.π Y j)⟩, ⟨?_⟩⟩
  -- The complements of `A` and of `Y j` in the two decompositions are isomorphic.
  let f := g ≪≫ biproductSubtypeNeIso Y j
  have hf : biprod.inl ≫ f.hom ≫ biprod.fst = biprod.inl ≫ g.hom ≫ biproduct.π Y j := by
    simp [f]
  have : IsIso (biprod.inl ≫ f.hom ≫ biprod.fst) := by
    rw [hf]
    infer_instance
  exact Biprod.isoElim f

private theorem exists_equiv_iso_aux (n : ℕ) : ∀ {ι : Type w} {κ : Type w'} [Fintype ι]
    [Finite κ] (X : ι → C) (Y : κ → C), Fintype.card ι = n → (∀ i, IsLocalRing (End (X i))) →
    (∀ j, IsLocalRing (End (Y j))) → (⨁ X ≅ ⨁ Y) → ∃ σ : ι ≃ κ, ∀ i, Nonempty (X i ≅ Y (σ i)) := by
  classical
  induction n with
  | zero =>
    intro ι κ _ _ X Y hn _ hY e
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hn
    -- Every `Y j` is a retract of the zero object `⨁ X`, and is nonzero.
    have : IsEmpty κ := ⟨fun j ↦ by
      have := hY j
      have hz := (isZero_biproduct_of_isEmpty X).of_iso e.symm
      have h : 𝟙 (Y j) = 0 := by
        rw [← biproduct.ι_π_self Y j, hz.eq_of_tgt (biproduct.ι Y j) 0, zero_comp]
      exact zero_ne_one (α := End (Y j)) (End.ext h.symm)⟩
    exact ⟨Equiv.equivOfIsEmpty ι κ, fun i ↦ isEmptyElim i⟩
  | succ n ih =>
    intro ι κ _ _ X Y hn hX hY e
    obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by lia)
    have := hX i₀
    obtain ⟨j₀, ⟨φ₀⟩, ⟨φ'⟩⟩ := exchange Y hY ((biproductSubtypeNeIso X i₀).symm ≪≫ e)
    obtain ⟨σ', hσ'⟩ := ih (Subtype.restrict (· ≠ i₀) X) (Subtype.restrict (· ≠ j₀) Y)
      (by simp [Fintype.card_subtype_compl, hn]) (fun i ↦ hX i.1) (fun j ↦ hY j.1) φ'
    refine ⟨(Equiv.optionSubtypeNe i₀).symm.trans ((Equiv.optionCongr σ').trans
      (Equiv.optionSubtypeNe j₀)), fun i ↦ ?_⟩
    by_cases hi : i = i₀
    · subst hi
      simpa [Equiv.optionSubtypeNe_symm_self] using ⟨φ₀⟩
    · simpa [Equiv.optionSubtypeNe_symm_of_ne hi] using hσ' ⟨i, hi⟩

/-- **Uniqueness of decompositions into objects with local endomorphism rings**: two
decompositions `⨁ X ≅ ⨁ Y` of the same object into objects with local endomorphism rings match up
to a bijection of the summands. No hypothesis on the category beyond finite biproducts is needed;
in a Krull-Schmidt category this is the uniqueness of the decomposition of every object. -/
theorem exists_equiv_iso_of_biproduct_iso_of_isLocalRing {ι : Type w} {κ : Type w'} [Finite ι]
    [Finite κ]
    (X : ι → C) (Y : κ → C) (hX : ∀ i, IsLocalRing (End (X i)))
    (hY : ∀ j, IsLocalRing (End (Y j))) (e : ⨁ X ≅ ⨁ Y) :
    ∃ σ : ι ≃ κ, ∀ i, Nonempty (X i ≅ Y (σ i)) := by
  have := Fintype.ofFinite ι
  exact exists_equiv_iso_aux _ X Y rfl hX hY e

end TauCeti
