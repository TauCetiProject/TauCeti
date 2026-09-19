/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Elementary.Basic
public import TauCeti.InformationTheory.Coding.Puncture
public import Mathlib.Logic.Equiv.Option

/-!
# Parity extension and recovery of punctured codes

Parity extension adds one coordinate, the negative sum of the original coordinates, so that
every extended word has coordinate sum zero. The original coordinates are indexed by `some`
and the new coordinate by `none`. The extension preserves dimension and cardinality.

A code with zero coordinate sums can be recovered after puncturing any coordinate by parity
extension, with the original coordinate order restored by `Equiv.optionSubtypeNe`. The binary
evenness specializations are in `TauCeti.InformationTheory.Coding.Binary.ParityExtension`.

## References

W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
Press (2003), §1.5.
-/

public section

namespace TauCeti

variable {F ι κ : Type*} [Fintype ι]

section Ring

variable [Ring F]

/-- Add the negative coordinate sum as a new parity coordinate at `none`. -/
def parityExtend : (ι → F) →ₗ[F] (Option ι → F) where
  toFun x := fun j ↦ j.elim (-∑ i, x i) x
  map_add' x y := by
    ext j
    cases j <;> simp [Finset.sum_add_distrib, add_comm]
  map_smul' a x := by
    ext j
    cases j <;> simp [Finset.mul_sum]

@[simp]
theorem parityExtend_none (x : ι → F) : parityExtend x none = -∑ i, x i := (rfl)

@[simp]
theorem parityExtend_some (x : ι → F) (i : ι) : parityExtend x (some i) = x i := (rfl)

/-- Parity extension is injective, since the original coordinates are retained. -/
theorem parityExtend_injective : Function.Injective (parityExtend : (ι → F) → Option ι → F) := by
  intro x y h
  exact funext fun i ↦ by simpa using congrFun h (some i)

/-- A parity-extended word has coordinate sum zero. -/
theorem sum_parityExtend (x : ι → F) : ∑ j, parityExtend x j = 0 := by
  simp [Fintype.sum_option]

/-- A word of coordinate sum zero is uniquely recovered from its original coordinates. -/
theorem parityExtend_comp_some {x : Option ι → F} (hx : ∑ j, x j = 0) :
    parityExtend (x ∘ some) = x := by
  ext j
  cases j with
  | none =>
    simpa [Fintype.sum_option, Function.comp_def, neg_eq_iff_add_eq_zero, add_comm] using hx
  | some i => simp

/-- The parity extension of a linear code, with the new coordinate indexed by `none`. -/
def parityExtension (C : Submodule F (ι → F)) : Submodule F (Option ι → F) :=
  C.map parityExtend

/-- Parity extension is the image of the code under the parity-extension linear map. -/
theorem parityExtension_def (C : Submodule F (ι → F)) :
    parityExtension C = C.map parityExtend := (rfl)

/-- Parity extension is monotone in the code. -/
theorem parityExtension_mono : Monotone (parityExtension :
    Submodule F (ι → F) → Submodule F (Option ι → F)) :=
  fun _ _ h ↦ Submodule.map_mono h

/-- Parity extension preserves and reflects inclusion of codes. -/
@[simp]
theorem parityExtension_le_parityExtension_iff {C D : Submodule F (ι → F)} :
    parityExtension C ≤ parityExtension D ↔ C ≤ D :=
  Submodule.map_le_map_iff_of_injective parityExtend_injective C D

/-- The parity extension of the zero code is zero. -/
@[simp]
theorem parityExtension_bot : parityExtension (⊥ : Submodule F (ι → F)) = ⊥ :=
  Submodule.map_bot parityExtend

/-- Parity extension preserves sums of codes. -/
@[simp]
theorem parityExtension_sup (C D : Submodule F (ι → F)) :
    parityExtension (C ⊔ D) = parityExtension C ⊔ parityExtension D :=
  Submodule.map_sup C D parityExtend

/-- Parity extension preserves intersections of codes. -/
@[simp]
theorem parityExtension_inf (C D : Submodule F (ι → F)) :
    parityExtension (C ⊓ D) = parityExtension C ⊓ parityExtension D :=
  Submodule.map_inf parityExtend parityExtend_injective

/-- Membership in the extended code is membership of the old coordinates together with the
zero-sum parity condition. -/
@[simp]
theorem mem_parityExtension {C : Submodule F (ι → F)} {x : Option ι → F} :
    x ∈ parityExtension C ↔ x ∘ some ∈ C ∧ ∑ j, x j = 0 := by
  rw [parityExtension_def, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨by simpa only [Function.comp_def, parityExtend_some] using hy, sum_parityExtend y⟩
  · rintro ⟨hxC, hx⟩
    exact ⟨x ∘ some, hxC, parityExtend_comp_some hx⟩

/-- Extending the whole word space gives the single-parity-check code. -/
@[simp]
theorem parityExtension_top : parityExtension (⊤ : Submodule F (ι → F)) =
    singleParityCheckCode F (Option ι) := by
  ext x
  simp only [mem_parityExtension, Submodule.mem_top, true_and, mem_singleParityCheckCode]

/-- Every parity extension is a subcode of the single-parity-check code. -/
theorem parityExtension_le_singleParityCheckCode (C : Submodule F (ι → F)) :
    parityExtension C ≤ singleParityCheckCode F (Option ι) := by
  intro x hx
  exact (mem_singleParityCheckCode _ _).mpr (mem_parityExtension.mp hx).2

/-- Restricting an extended code to the original coordinates recovers the original code. -/
@[simp]
theorem map_some_parityExtension (C : Submodule F (ι → F)) :
    (parityExtension C).map (LinearMap.funLeft F F some) = C := by
  have h : (LinearMap.funLeft F F some).comp
      (parityExtend : (ι → F) →ₗ[F] (Option ι → F)) = LinearMap.id := by
    ext x i
    simp
  rw [parityExtension_def, ← Submodule.map_comp, h, Submodule.map_id]

/-- Encoding by parity extension gives a linear equivalence of codeword spaces. -/
noncomputable def parityExtensionEquiv (C : Submodule F (ι → F)) : C ≃ₗ[F] parityExtension C :=
  Submodule.equivMapOfInjective parityExtend parityExtend_injective C

@[simp]
theorem coe_parityExtensionEquiv_apply (C : Submodule F (ι → F)) (x : C) :
    (parityExtensionEquiv C x : Option ι → F) = parityExtend (x : ι → F) :=
  Submodule.coe_equivMapOfInjective_apply parityExtend parityExtend_injective C x

@[simp]
theorem coe_parityExtensionEquiv_symm_apply (C : Submodule F (ι → F))
    (x : parityExtension C) :
    ((parityExtensionEquiv C).symm x : ι → F) = (x : Option ι → F) ∘ some := by
  have h := congrArg (fun y : parityExtension C ↦ (y : Option ι → F))
    ((parityExtensionEquiv C).apply_symm_apply x)
  exact funext fun i ↦ by
    simpa only [coe_parityExtensionEquiv_apply, parityExtend_some, Function.comp_apply]
      using congrFun h (some i)

/-- Adding a parity coordinate preserves dimension. -/
@[simp]
theorem finrank_parityExtension (C : Submodule F (ι → F)) :
    Module.finrank F (parityExtension C) = Module.finrank F C :=
  (parityExtensionEquiv C).finrank_eq.symm

/-- Adding a parity coordinate preserves the number of codewords. -/
@[simp↓]
theorem natCard_parityExtension (C : Submodule F (ι → F)) :
    Nat.card (parityExtension C) = Nat.card C :=
  Nat.card_congr (parityExtensionEquiv C).symm.toEquiv

end Ring

variable [Field F]

/-- Deleting a coordinate of a zero-sum code and adding a parity coordinate recovers the code,
with `none` placed at the deleted coordinate by the displayed equivalence. -/
theorem parityExtension_punctureAt [DecidableEq ι] (C : LinearCode F ι) (i : ι)
    (hC : C ≤ singleParityCheckCode F ι) :
    parityExtension (punctureAt C i) = reindex C (Equiv.optionSubtypeNe i) := by
  rw [punctureAt_def]
  -- Normalize the singleton-complement subtype to the predicate used by `optionSubtypeNe`.
  change parityExtension (puncture C {j | j ≠ i}) = reindex C (Equiv.optionSubtypeNe i)
  ext x
  rw [mem_parityExtension, mem_puncture, mem_reindex]
  constructor
  · rintro ⟨⟨y, hy, hyx⟩, hx⟩
    refine ⟨y, hy, ?_⟩
    have hsum : ∑ j, y (Equiv.optionSubtypeNe i j) = 0 := by
      rw [Equiv.sum_comp]
      exact (mem_singleParityCheckCode _ _).mp (hC hy)
    have hwords : (fun j ↦ y (Equiv.optionSubtypeNe i j)) = x := by
      rw [← parityExtend_comp_some hsum, ← parityExtend_comp_some hx]
      congr 1
      funext j
      exact hyx j
    exact congrFun hwords
  · rintro ⟨y, hy, hyx⟩
    refine ⟨⟨y, hy, fun j ↦ hyx (some j)⟩, ?_⟩
    have hsum := (mem_singleParityCheckCode _ _).mp (hC hy)
    rw [← Equiv.sum_comp (Equiv.optionSubtypeNe i) y] at hsum
    simp only [hyx] at hsum
    exact hsum

/-- Parity extension commutes with relabelling the original coordinates. -/
@[simp]
theorem parityExtension_reindex [Fintype κ] (C : LinearCode F ι) (e : κ ≃ ι) :
    parityExtension (reindex C e) = reindex (parityExtension C) (e.optionCongr) := by
  ext x
  simp only [mem_parityExtension, mem_reindex]
  constructor
  · rintro ⟨⟨y, hy, hyx⟩, hx⟩
    refine ⟨parityExtend y, ⟨by simpa only [Function.comp_def, parityExtend_some]
      using hy, sum_parityExtend y⟩, ?_⟩
    intro j
    cases j with
    | none =>
      have hs : ∑ k, y (e k) = ∑ k, x (some k) := Finset.sum_congr rfl fun k _ ↦ hyx k
      rw [Equiv.sum_comp] at hs
      simpa [Fintype.sum_option, hs, neg_eq_iff_add_eq_zero, add_comm] using hx
    | some k => simpa using hyx k
  · rintro ⟨y, ⟨hy, hys⟩, hyx⟩
    refine ⟨⟨y ∘ some, hy, fun k ↦ hyx (some k)⟩, ?_⟩
    rw [← Equiv.sum_comp e.optionCongr y] at hys
    simpa only [hyx] using hys

end TauCeti
