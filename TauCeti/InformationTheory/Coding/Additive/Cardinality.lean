/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Puncture

/-!
# Cardinalities under additive coordinate deletion

Restriction of an additive code to a retained coordinate set is a surjective homomorphism
onto its puncture. Its kernel consists of the codewords supported on the complementary set,
and restriction identifies that kernel with the complementary shortening. Consequently
`#shorten(C,s) * #puncture(C,sᶜ) = #C`. This is the cardinality analogue of rank–nullity,
applicable to additive alphabets without a field structure.

Both shortened and punctured codes have cardinality dividing the original code's cardinality.
For a finite code, neither operation increases cardinality. Deleting finitely many coordinates
over a finite alphabet decreases cardinality by at most a factor equal to the number of possible
words on those coordinates.

## References

* W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, §§1.5–1.6,
  for puncturing and shortening, and Chapter 9 for additive codes.
-/

public section

namespace TauCeti.AdditiveCode

variable {A ι : Type*} [AddCommGroup A]

/-- Restriction of codewords to the retained coordinates, with codomain the punctured code. -/
def punctureHom (C : AdditiveCode A ι) (s : Set ι) : C →+ puncture C s :=
  ((AddMonoidHom.pi fun i : s ↦ Pi.evalAddMonoidHom (fun _ : ι ↦ A) i).domRestrict C)
    |>.codRestrict (puncture C s) fun x ↦ mem_puncture.mpr ⟨x.1, x.2, fun _ ↦ rfl⟩

/-- Restriction computes by evaluating the original word at the retained coordinate. -/
@[simp]
theorem punctureHom_apply (C : AdditiveCode A ι) (s : Set ι) (x : C) (i : s) :
    (punctureHom C s x : s → A) i = x.1 i := (rfl)

/-- Every punctured word is the restriction of a codeword. -/
theorem punctureHom_surjective (C : AdditiveCode A ι) (s : Set ι) :
    Function.Surjective (punctureHom C s) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := mem_puncture.mp y.2
  exact ⟨⟨x, hx⟩, Subtype.ext (funext hxy)⟩

/-- Restriction is zero exactly when the word is zero on the retained coordinates. -/
@[simp]
theorem punctureHom_eq_zero (C : AdditiveCode A ι) (s : Set ι) (x : C) :
    punctureHom C s x = 0 ↔ ∀ i : s, x.1 i = 0 := by
  simp only [Subtype.ext_iff, funext_iff,
    punctureHom_apply, ZeroMemClass.coe_zero, Pi.zero_apply]

/-- Restricting the kernel of puncturing on `sᶜ` to `s` identifies it with shortening on `s`.
The inverse extends the shortened word by zero. -/
noncomputable def kerPunctureEquivShorten (C : AdditiveCode A ι) (s : Set ι) :
    (punctureHom C sᶜ).ker ≃+ shorten C s where
  toFun x := ⟨fun i ↦ x.1.1 i, mem_shorten.mpr
    ⟨x.1.1, x.1.2, fun i hi ↦
      (punctureHom_eq_zero C sᶜ x.1).mp (AddMonoidHom.mem_ker.mp x.2) ⟨i, hi⟩,
      fun _ ↦ rfl⟩⟩
  invFun y := ⟨⟨Subtype.val.extend y.1 0, mem_shorten_iff_extend_mem.mp y.2⟩,
    AddMonoidHom.mem_ker.mpr ((punctureHom_eq_zero C sᶜ _).mpr fun i ↦
      (Function.extend_val_apply' i.2).trans (Pi.zero_apply _))⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · exact Subtype.val_injective.extend_apply (fun j : s ↦ x.1.1 j) (0 : ι → A) ⟨i, hi⟩
    · exact (Function.extend_val_apply' hi).trans
        (((punctureHom_eq_zero C sᶜ x.1).mp (AddMonoidHom.mem_ker.mp x.2) ⟨i, hi⟩).symm)
  right_inv y := by
    apply Subtype.ext
    funext i
    exact Subtype.val_injective.extend_apply y.1 (0 : ι → A) i
  map_add' _ _ := by
    apply Subtype.ext
    rfl

/-- The kernel equivalence restricts a word to the shortening's retained coordinates. -/
@[simp]
theorem kerPunctureEquivShorten_apply (C : AdditiveCode A ι) (s : Set ι)
    (x : (punctureHom C sᶜ).ker) (i : s) :
    (kerPunctureEquivShorten C s x : s → A) i = x.1.1 i := (rfl)

/-- The inverse kernel equivalence extends the shortened word by zero. -/
@[simp]
theorem coe_kerPunctureEquivShorten_symm_apply (C : AdditiveCode A ι) (s : Set ι)
    (y : shorten C s) :
    ((kerPunctureEquivShorten C s).symm y).1.1 = Subtype.val.extend y.1 0 := (rfl)

/-- The cardinalities of shortening on `s` and puncturing on `sᶜ` multiply to that of the code.
The coordinates in each set are retained. No finiteness assumption is needed for `Nat.card`. -/
theorem natCard_shorten_mul_natCard_puncture_compl (C : AdditiveCode A ι) (s : Set ι) :
    Nat.card (shorten C s) * Nat.card (puncture C sᶜ) = Nat.card C := by
  -- The kernel identification uses extension by zero; the counting argument uses Mathlib's
  -- `AddSubgroup.card_ker_mul_card_of_surjective` rather than a separate coset calculation.
  rw [← Nat.card_congr (kerPunctureEquivShorten C s).toEquiv]
  exact AddSubgroup.card_ker_mul_card_of_surjective (punctureHom_surjective C sᶜ)

/-- Puncturing on `s` and shortening on its complement give the complementary counting formula. -/
theorem natCard_puncture_mul_natCard_shorten_compl (C : AdditiveCode A ι) (s : Set ι) :
    Nat.card (puncture C s) * Nat.card (shorten C sᶜ) = Nat.card C := by
  have h := natCard_shorten_mul_natCard_puncture_compl C sᶜ
  rw [compl_compl] at h
  exact (Nat.mul_comm _ _).trans h

/-- The cardinality of a punctured additive code divides the original cardinality. -/
theorem natCard_puncture_dvd (C : AdditiveCode A ι) (s : Set ι) :
    Nat.card (puncture C s) ∣ Nat.card C :=
  AddSubgroup.card_dvd_of_surjective (punctureHom_surjective C s)

/-- The cardinality of a shortened additive code divides the original cardinality. -/
theorem natCard_shorten_dvd (C : AdditiveCode A ι) (s : Set ι) :
    Nat.card (shorten C s) ∣ Nat.card C :=
  ⟨_, (natCard_shorten_mul_natCard_puncture_compl C s).symm⟩

/-- Puncturing does not increase the cardinality of a finite code. The alphabet may be infinite. -/
theorem natCard_puncture_le (C : AdditiveCode A ι) [Finite C] (s : Set ι) :
    Nat.card (puncture C s) ≤ Nat.card C :=
  Nat.card_le_card_of_surjective _ (punctureHom_surjective C s)

/-- Shortening does not increase the cardinality of a finite code. The alphabet may be infinite. -/
theorem natCard_shorten_le (C : AdditiveCode A ι) [Finite C] (s : Set ι) :
    Nat.card (shorten C s) ≤ Nat.card C := by
  rw [← Nat.card_congr (kerPunctureEquivShorten C s).toEquiv]
  exact Nat.card_le_card_of_injective _ Subtype.val_injective

/-- Puncturing decreases cardinality by at most the number of words on the deleted coordinates
as a multiplicative factor. -/
theorem natCard_le_natCard_puncture_mul_pow (C : AdditiveCode A ι)
    [Finite A] (s : Set ι) [Finite ↥sᶜ] :
    Nat.card C ≤ Nat.card (puncture C s) * Nat.card A ^ Nat.card ↥sᶜ := by
  rw [← natCard_puncture_mul_natCard_shorten_compl C s]
  apply Nat.mul_le_mul_left
  exact (Nat.card_le_card_of_injective (fun x : shorten C sᶜ ↦ x.1)
    Subtype.val_injective).trans_eq Nat.card_fun

/-- Shortening decreases cardinality by at most the number of words on the deleted coordinates
as a multiplicative factor. -/
theorem natCard_le_natCard_shorten_mul_pow (C : AdditiveCode A ι)
    [Finite A] (s : Set ι) [Finite ↥sᶜ] :
    Nat.card C ≤ Nat.card (shorten C s) * Nat.card A ^ Nat.card ↥sᶜ := by
  rw [← natCard_shorten_mul_natCard_puncture_compl C s]
  apply Nat.mul_le_mul_left
  exact (Nat.card_le_card_of_injective (fun x : puncture C sᶜ ↦ x.1)
    Subtype.val_injective).trans_eq Nat.card_fun

end TauCeti.AdditiveCode
