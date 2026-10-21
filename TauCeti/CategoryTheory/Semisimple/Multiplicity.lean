/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct
public import TauCeti.CategoryTheory.Semisimple.Basic
public import TauCeti.CategoryTheory.Simple.Classes
public import Mathlib.Data.Finsupp.Basic

/-!
# Multiplicities in finite simple decompositions

The simple multiplicities of an object in a finite semisimple abelian category form a finitely
supported function on `SimpleClasses C`. They count summands up to isomorphism, independently of
the chosen decomposition. No coefficient field, splitness, or finiteness of the endomorphism
division rings is required. Equal multiplicities characterize isomorphic objects, and the
multiplicities are additive on binary biproducts and vanish exactly on zero objects.

Uniqueness uses Mathlib's `HomOrthogonal.equiv_of_iso`: Schur's lemma makes the chosen simple
representatives hom orthogonal and their endomorphism rings division rings.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace TauCeti

universe v u

section Uniqueness

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasKernels C]
  [HasFiniteBiproducts C]

/-- Two finite decompositions into simple objects have the same summands, up to a bijection
of indices and isomorphisms of the corresponding objects. -/
theorem exists_equiv_of_iso_biproduct_simples {ι κ : Type} [Finite ι] [Finite κ]
    (f : ι → C) (g : κ → C) [∀ i, Simple (f i)] [∀ j, Simple (g j)]
    (e : (⨁ f) ≅ ⨁ g) : ∃ a : ι ≃ κ, ∀ i, Nonempty (f i ≅ g (a i)) := by
  let ef := biproduct.mapIso fun i ↦ (SimpleClasses.classOfReprIso (f i)).symm
  let eg := biproduct.mapIso fun j ↦ (SimpleClasses.classOfReprIso (g j)).symm
  obtain ⟨a, ha⟩ := SimpleClasses.homOrthogonal_repr.equiv_of_iso (ef.symm ≪≫ e ≪≫ eg)
  refine ⟨a, fun i ↦ ?_⟩
  exact (SimpleClasses.classOf_eq_iff_nonempty_iso _ _).1 (ha i).symm

/-- Counting the simple classes in a decomposition is invariant under isomorphism of its
biproduct. -/
theorem sum_simpleClasses_eq_of_iso_biproduct {ι κ : Type} [Fintype ι] [Fintype κ]
    (f : ι → C) (g : κ → C) [∀ i, Simple (f i)] [∀ j, Simple (g j)]
    (e : (⨁ f) ≅ ⨁ g) :
    (∑ i, Finsupp.single (SimpleClasses.classOf (f i)) 1 : SimpleClasses C →₀ ℕ) =
      ∑ j, Finsupp.single (SimpleClasses.classOf (g j)) 1 := by
  obtain ⟨a, ha⟩ := exists_equiv_of_iso_biproduct_simples f g e
  apply Fintype.sum_equiv a
  intro i
  congr 1
  exact (SimpleClasses.classOf_eq_iff_nonempty_iso _ _).2 (ha i)

end Uniqueness

variable {C : Type u} [Category.{v} C] [Abelian C] [IsFiniteSemisimpleCategory C]

attribute [local instance] Abelian.hasFiniteBiproducts

private theorem exists_simpleMultiplicities (X : C) :
    ∃ m : SimpleClasses C →₀ ℕ, ∀ (ι : Type) [Fintype ι] (f : ι → C)
      [∀ i, Simple (f i)] (_e : X ≅ ⨁ f),
      m = ∑ i, Finsupp.single (SimpleClasses.classOf (f i)) 1 := by
  obtain ⟨ι, hι, f, hf, hbf, ⟨e⟩⟩ :=
    IsFiniteSemisimpleCategory.exists_biproduct_simples X
  let := hι
  let := hf
  let := hbf
  refine ⟨∑ i, Finsupp.single (SimpleClasses.classOf (f i)) 1, ?_⟩
  intro κ hκ g hg d
  exact sum_simpleClasses_eq_of_iso_biproduct f g (e.symm ≪≫ d)

/-- The finitely supported function counting the copies of each simple isomorphism class in an
object. These are decomposition multiplicities, not dimensions over a coefficient field. -/
def simpleMultiplicities (X : C) : SimpleClasses C →₀ ℕ :=
  (exists_simpleMultiplicities X).choose

/-- Any finite decomposition into simple objects computes the simple multiplicities. -/
theorem simpleMultiplicities_eq_of_iso_biproduct {ι : Type} [Fintype ι]
    (f : ι → C) [hf : ∀ i, Simple (f i)] {X : C} (e : X ≅ ⨁ f) :
    simpleMultiplicities X = ∑ i, Finsupp.single (SimpleClasses.classOf (f i)) 1 :=
  (exists_simpleMultiplicities X).choose_spec ι f e

/-- Isomorphic objects have the same simple multiplicities. -/
theorem simpleMultiplicities_eq_of_iso {X Y : C} (e : X ≅ Y) :
    simpleMultiplicities X = simpleMultiplicities Y := by
  obtain ⟨ι, hι, f, hf, hbf, ⟨d⟩⟩ :=
    IsFiniteSemisimpleCategory.exists_biproduct_simples Y
  let := hι
  let := hf
  let := hbf
  rw [simpleMultiplicities_eq_of_iso_biproduct f (e ≪≫ d),
    simpleMultiplicities_eq_of_iso_biproduct f d]

/-- A simple object has one copy of its own class and no copies of any other class. -/
@[simp]
theorem simpleMultiplicities_simple (X : C) [Simple X] :
    simpleMultiplicities X = Finsupp.single (SimpleClasses.classOf X) 1 := by
  rw [simpleMultiplicities_eq_of_iso_biproduct (fun _ : Unit ↦ X)
    (biproductUniqueIso (fun _ : Unit ↦ X)).symm]
  simp

/-- The zero object has no simple summands. -/
@[simp]
theorem simpleMultiplicities_zero : simpleMultiplicities (0 : C) = 0 := by
  let f : Fin 0 → C := fun i ↦ Fin.elim0 i
  let : ∀ i, Simple (f i) := fun i ↦ Fin.elim0 i
  have hz : IsZero (⨁ f) := (IsZero.iff_id_eq_zero _).2 (by ext i; exact Fin.elim0 i)
  rw [simpleMultiplicities_eq_of_iso_biproduct f ((isZero_zero C).iso hz)]
  simp

/-- The multiplicity of a class is the number of summands of that class in any simple
decomposition. In particular, the formula is valid over nonsplit endomorphism division rings. -/
theorem simpleMultiplicities_apply_eq_card {ι : Type} [Finite ι] (f : ι → C)
    [∀ i, Simple (f i)] {X : C} (e : X ≅ ⨁ f) (S : SimpleClasses C) :
    simpleMultiplicities X S = Nat.card {i // SimpleClasses.classOf (f i) = S} := by
  classical
  let := Fintype.ofFinite ι
  rw [simpleMultiplicities_eq_of_iso_biproduct f e]
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]

open scoped Classical in
/-- The multiplicity of a simple object is the sum of the indicators that it is isomorphic to
each summand in any simple decomposition. -/
theorem simpleMultiplicities_apply_classOf_eq_sum {ι : Type} [Fintype ι] (f : ι → C)
    [∀ i, Simple (f i)] {X : C} (e : X ≅ ⨁ f) (S : C) [Simple S] :
    simpleMultiplicities X (SimpleClasses.classOf S) =
      ∑ i, if Nonempty (S ≅ f i) then 1 else 0 := by
  rw [simpleMultiplicities_apply_eq_card f e]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_eq_sum_ones,
    Finset.sum_filter, SimpleClasses.classOf_eq_iff_nonempty_iso, Iso.nonempty_iso_symm]

/-- Simple multiplicities classify objects of a finite semisimple category up to isomorphism. -/
theorem nonempty_iso_iff_simpleMultiplicities_eq (X Y : C) :
    Nonempty (X ≅ Y) ↔ simpleMultiplicities X = simpleMultiplicities Y := by
  classical
  refine ⟨fun ⟨e⟩ ↦ simpleMultiplicities_eq_of_iso e, fun h ↦ ?_⟩
  obtain ⟨ι, hι, f, hf, hbf, ⟨e⟩⟩ :=
    IsFiniteSemisimpleCategory.exists_biproduct_simples X
  obtain ⟨κ, hκ, g, hg, hbg, ⟨d⟩⟩ :=
    IsFiniteSemisimpleCategory.exists_biproduct_simples Y
  let := hι
  let := hκ
  let := hf
  let := hg
  let := hbf
  let := hbg
  have hc (S : SimpleClasses C) :
      Nat.card {i // SimpleClasses.classOf (f i) = S} =
        Nat.card {j // SimpleClasses.classOf (g j) = S} := by
    rw [← simpleMultiplicities_apply_eq_card f e, ← simpleMultiplicities_apply_eq_card g d, h]
  let es (S : SimpleClasses C) :
      (fun i ↦ SimpleClasses.classOf (f i)) ⁻¹' {S} ≃
        (fun j ↦ SimpleClasses.classOf (g j)) ⁻¹' {S} :=
    Fintype.equivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact hc S)
  let a := Equiv.ofPreimageEquiv es
  have ha (i : ι) : SimpleClasses.classOf (g (a i)) = SimpleClasses.classOf (f i) :=
    Equiv.ofPreimageEquiv_map es i
  let ei (i : ι) : f i ≅ g (a i) :=
    ((SimpleClasses.classOf_eq_iff_nonempty_iso _ _).1 (ha i).symm).some
  exact ⟨e ≪≫ biproduct.mapIso ei ≪≫ biproduct.reindex a g ≪≫ d.symm⟩

/-- Simple multiplicities are additive on binary biproducts. -/
@[simp]
theorem simpleMultiplicities_biprod (X Y : C) :
    simpleMultiplicities (X ⊞ Y) = simpleMultiplicities X + simpleMultiplicities Y := by
  classical
  obtain ⟨ι, hι, f, hf, hbf, ⟨e⟩⟩ :=
    IsFiniteSemisimpleCategory.exists_biproduct_simples X
  obtain ⟨κ, hκ, g, hg, hbg, ⟨d⟩⟩ :=
    IsFiniteSemisimpleCategory.exists_biproduct_simples Y
  let := hι
  let := hκ
  let := hf
  let := hg
  let := hbf
  let := hbg
  let s : ι ⊕ κ → C := Sum.elim f g
  let : ∀ i, Simple (s i) := fun
    | .inl i => hf i
    | .inr j => hg j
  calc
    simpleMultiplicities (X ⊞ Y) =
        ∑ i : ι ⊕ κ, (Finsupp.single (SimpleClasses.classOf (s i)) 1 :
          SimpleClasses C →₀ ℕ) :=
      simpleMultiplicities_eq_of_iso_biproduct s
        (biprod.mapIso e d ≪≫ (biproductSumIso f g).symm)
    _ = simpleMultiplicities X + simpleMultiplicities Y := by
      rw [simpleMultiplicities_eq_of_iso_biproduct f e,
        simpleMultiplicities_eq_of_iso_biproduct g d, Fintype.sum_sum_type]
      simp only [s, Sum.elim_inl, Sum.elim_inr]

/-- An object has no simple summands exactly when it is a zero object. -/
@[simp]
theorem simpleMultiplicities_eq_zero_iff (X : C) :
    simpleMultiplicities X = 0 ↔ IsZero X := by
  rw [← simpleMultiplicities_zero (C := C), ← nonempty_iso_iff_simpleMultiplicities_eq]
  exact ⟨fun ⟨e⟩ ↦ (isZero_zero C).of_iso e, fun h ↦ ⟨h.isoZero⟩⟩

end TauCeti
