/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Degree

/-!
# Polynomials with full symmetric Galois group

`TauCeti.Polynomial.HasFullSymmetricGaloisGroup f` requires separability and surjectivity of
the Galois action on the roots in the splitting field. Separability ensures that this is the
symmetric group on `f.natDegree` points, rather than on a smaller set of distinct roots.
With `open TauCeti`, the predicate is also available as `f.HasFullSymmetricGaloisGroup`.

The property can be checked in any field where `f` splits, or by checking that the Galois
group has order `f.natDegree!`. A numbering of the roots gives an explicit group isomorphism
with the permutations of `Fin f.natDegree`. These interfaces connect reduction criteria
for Galois groups with realizations of symmetric groups over the rational numbers.
-/

public section

open Polynomial

namespace TauCeti.Polynomial

variable {F : Type*} [Field F] {f : F[X]}

local instance (f : F[X]) : Fact ((f.map (algebraMap F f.SplittingField)).Splits) :=
  ⟨IsSplittingField.splits f.SplittingField f⟩

/-- A polynomial has full symmetric Galois group if it is separable and every permutation
of its roots in the splitting field is induced by a Galois automorphism. -/
def HasFullSymmetricGaloisGroup (f : F[X]) : Prop :=
  f.Separable ∧ Function.Surjective (Gal.galActionHom f f.SplittingField)

/-- Separability and surjectivity of the action on splitting-field roots give full symmetric
Galois group. -/
theorem HasFullSymmetricGaloisGroup.mk (hsep : f.Separable)
    (hsurj : Function.Surjective (Gal.galActionHom f f.SplittingField)) :
    HasFullSymmetricGaloisGroup f :=
  ⟨hsep, hsurj⟩

/-- A polynomial with full symmetric Galois group is separable. -/
theorem HasFullSymmetricGaloisGroup.separable (hf : HasFullSymmetricGaloisGroup f) :
    f.Separable :=
  hf.1

/-- Every permutation of the splitting-field roots of a polynomial with full symmetric
Galois group is induced by a Galois automorphism. -/
theorem HasFullSymmetricGaloisGroup.surjective_galActionHom
    (hf : HasFullSymmetricGaloisGroup f) :
    Function.Surjective (Gal.galActionHom f f.SplittingField) :=
  hf.2

/-- Among separable polynomials, full symmetric Galois group is equivalent to the Galois
group having order equal to the factorial of the degree. -/
theorem hasFullSymmetricGaloisGroup_iff_natCard_gal_eq_factorial_natDegree (hsep : f.Separable) :
    HasFullSymmetricGaloisGroup f ↔ Nat.card f.Gal = f.natDegree.factorial := by
  have hcard : Nat.card (Equiv.Perm (f.rootSet f.SplittingField)) =
      f.natDegree.factorial := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card,
      card_rootSet_eq_natDegree hsep (IsSplittingField.splits f.SplittingField f)]
  rw [HasFullSymmetricGaloisGroup, and_iff_right hsep, ← hcard]
  exact ⟨fun h ↦ Nat.card_eq_of_bijective _ ⟨Gal.galActionHom_injective f _, h⟩,
    fun h ↦ ((Gal.galActionHom_injective f _).bijective_of_nat_card_le h.ge).2⟩

/-- Full symmetric Galois group can be checked on the roots in any splitting extension. -/
theorem hasFullSymmetricGaloisGroup_iff_separable_and_surjective_galActionHom
    (E : Type*) [Field E] [Algebra F E]
    [hsplit : Fact ((f.map (algebraMap F E)).Splits)] :
    HasFullSymmetricGaloisGroup f ↔
      f.Separable ∧ Function.Surjective (Gal.galActionHom f E) := by
  by_cases hsep : f.Separable
  · rw [hasFullSymmetricGaloisGroup_iff_natCard_gal_eq_factorial_natDegree hsep,
      and_iff_right hsep]
    have hcard : Nat.card (Equiv.Perm (f.rootSet E)) = f.natDegree.factorial := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, card_rootSet_eq_natDegree hsep hsplit.out]
    rw [← hcard]
    exact ⟨fun h ↦ ((Gal.galActionHom_injective f E).bijective_of_nat_card_le h.ge).2,
      fun h ↦ Nat.card_eq_of_bijective _ ⟨Gal.galActionHom_injective f E, h⟩⟩
  · simp [HasFullSymmetricGaloisGroup, hsep]

/-- A polynomial with full symmetric Galois group realizes the symmetric group on as many
points as its degree. No numbering of its roots is fixed globally. -/
theorem HasFullSymmetricGaloisGroup.nonempty_mulEquiv (hf : HasFullSymmetricGaloisGroup f) :
    Nonempty (f.Gal ≃* Equiv.Perm (Fin f.natDegree)) := by
  obtain ⟨e⟩ := nonempty_rootSet_splittingField_equiv_fin f hf.separable
  exact ⟨(MulEquiv.ofBijective (Gal.galActionHom f f.SplittingField)
    ⟨Gal.galActionHom_injective f _, hf.surjective_galActionHom⟩).trans (Equiv.permCongrHom e)⟩

/-- A power of a nonunit polynomial with exponent at least two cannot have full symmetric
Galois group. -/
theorem not_hasFullSymmetricGaloisGroup_pow_of_not_isUnit
    (hf : ¬ IsUnit f) (n : ℕ) (hn : 2 ≤ n) :
    ¬ HasFullSymmetricGaloisGroup (f ^ n) := by
  intro h
  have := h.separable.squarefree.eq_zero_or_one_of_pow_of_not_isUnit hf
  omega

/-- Repeated roots rule out full symmetric Galois group, even when the action on the
distinct roots is surjective: in particular `X ^ n` is excluded for `2 ≤ n`. -/
@[simp]
theorem not_hasFullSymmetricGaloisGroup_X_pow (n : ℕ) (hn : 2 ≤ n) :
    ¬ HasFullSymmetricGaloisGroup (X ^ n : F[X]) :=
  not_hasFullSymmetricGaloisGroup_pow_of_not_isUnit not_isUnit_X n hn

end TauCeti.Polynomial
