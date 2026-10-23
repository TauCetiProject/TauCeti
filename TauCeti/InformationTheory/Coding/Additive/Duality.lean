/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Additive.DirectSum
public import TauCeti.InformationTheory.Coding.Puncture.Basic
public import TauCeti.LinearAlgebra.FiniteBilinearModule.CoordinatePower

/-!
# Puncturing, shortening, direct sums, and duality for additive codes

An additive code over a finite bilinear alphabet has a dual given by the orthogonal complement
for the summed coordinate pairing. For a set `s` of retained coordinates,
`(puncture C s)ᗮ = shorten Cᗮ s`. If the alphabet pairing is nondegenerate, also
`(shorten C s)ᗮ = puncture Cᗮ s`.

These identities apply to arbitrary additive subgroups, including codes over discriminant
alphabets without a field structure. The first identity holds even for degenerate pairings;
the second uses nondegeneracy. The coordinate sets may be empty and the code may be zero.

The summed pairing on a disjoint union of coordinate types has no cross terms between the two
coordinate blocks, so `(C ⊕ D)ᗮ = Cᗮ ⊕ Dᗮ`, again with no nondegeneracy assumption. Hence
bilinear isotropy and the Lagrangian condition hold for a direct sum exactly when they hold for
both summands. For a finite quadratic alphabet the quadratic value of a word is also summed
blockwise, so quadratic isotropy and the quadratic Lagrangian condition are likewise
componentwise. These are the code-level counterparts of the orthogonal-direct-sum laws
`TauCeti.FiniteBilinearModule.orthogonalComplement_prod` and
`TauCeti.FiniteQuadraticModule.isLagrangian_prod_iff`.

## References

* W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, §§1.4–1.5 and
  Chapter 9, for duality, coordinate deletion, and direct sums of linear and additive codes.
-/

public section

namespace TauCeti.FiniteBilinearModule

universe u v w

variable (A : FiniteBilinearModule.{u}) {ι : Type v} [Fintype ι]
variable (C : AdditiveCode A ι) (s : Set ι) [Fintype s]

/-- The orthogonal complement of a punctured additive code is the shortened orthogonal
complement, retaining the same coordinates. No nondegeneracy assumption is needed. -/
@[simp]
theorem orthogonalComplement_puncture :
    (A.coordinatePower s).orthogonalComplement (AdditiveCode.puncture C s) =
      AdditiveCode.shorten ((A.coordinatePower ι).orthogonalComplement C) s := by
  ext y
  rw [AdditiveCode.mem_shorten_iff_extend_mem,
    mem_orthogonalComplement_iff, mem_orthogonalComplement_iff]
  simp_rw [A.coordinatePower_pairing_extend_zero_left
      (f := (Subtype.val : s → ι)) Subtype.val_injective]
  constructor
  · intro h x hx
    exact h _ (AdditiveCode.mem_puncture.mpr ⟨x, hx, fun _ ↦ rfl⟩)
  · intro h z hz
    obtain ⟨x, hx, hxz⟩ := AdditiveCode.mem_puncture.mp hz
    have heq : x ∘ (Subtype.val : s → ι) = z := funext hxz
    simpa only [heq] using h x hx

/-- For a nondegenerate finite bilinear alphabet, the orthogonal complement of a shortened
additive code is the punctured orthogonal complement, retaining the same coordinates. -/
@[simp]
theorem IsNondegenerate.orthogonalComplement_shorten (hA : A.IsNondegenerate) :
    (A.coordinatePower s).orthogonalComplement (AdditiveCode.shorten C s) =
      AdditiveCode.puncture ((A.coordinatePower ι).orthogonalComplement C) s := by
  have hι := hA.coordinatePower ι
  have hs := hA.coordinatePower s
  rw [← IsNondegenerate.orthogonalComplement_orthogonalComplement
    (A.coordinatePower s) hs
    (AdditiveCode.puncture ((A.coordinatePower ι).orthogonalComplement C) s),
    A.orthogonalComplement_puncture,
    IsNondegenerate.orthogonalComplement_orthogonalComplement (A.coordinatePower ι) hι]

section DirectSum

variable {κ : Type w} [Fintype κ] (C : AdditiveCode A ι) (D : AdditiveCode A κ)

/-- The orthogonal complement of a direct sum of additive codes is the direct sum of their
orthogonal complements. No nondegeneracy assumption is needed. -/
@[simp]
theorem orthogonalComplement_directSum :
    (A.coordinatePower (ι ⊕ κ)).orthogonalComplement (C.directSum D) =
      ((A.coordinatePower ι).orthogonalComplement C).directSum
        ((A.coordinatePower κ).orthogonalComplement D) := by
  have hsplit (y x : ι ⊕ κ → A) : (A.coordinatePower (ι ⊕ κ)).pairing y x =
      (A.coordinatePower ι).pairing (y ∘ Sum.inl) (x ∘ Sum.inl) +
        (A.coordinatePower κ).pairing (y ∘ Sum.inr) (x ∘ Sum.inr) := by
    rw [coordinatePower_pairing, coordinatePower_pairing, coordinatePower_pairing]
    exact Fintype.sum_sum_type _
  ext y
  rw [AddSubgroup.mem_directSum_iff, mem_orthogonalComplement_iff, mem_orthogonalComplement_iff,
    mem_orthogonalComplement_iff]
  constructor
  · intro h
    refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · have hx' := h _ (AddSubgroup.sumElim_zero_right_mem_directSum D hx)
      rwa [hsplit, Sum.elim_comp_inl, Sum.elim_comp_inr, pairing_zero_right, add_zero] at hx'
    · have hx' := h _ (AddSubgroup.sumElim_zero_left_mem_directSum C hx)
      rwa [hsplit, Sum.elim_comp_inl, Sum.elim_comp_inr, pairing_zero_right, zero_add] at hx'
  · rintro ⟨hC, hD⟩ x hx
    rw [AddSubgroup.mem_directSum_iff] at hx
    simp only [hsplit, Function.comp_def, hC _ hx.1, hD _ hx.2, add_zero]

/-- A direct sum of additive codes is isotropic for the summed pairing exactly when both
summands are. -/
@[simp]
theorem isIsotropic_directSum_iff :
    (A.coordinatePower (ι ⊕ κ)).IsIsotropic (C.directSum D) ↔
      (A.coordinatePower ι).IsIsotropic C ∧ (A.coordinatePower κ).IsIsotropic D := by
  simp only [isIsotropic_iff_le_orthogonalComplement, orthogonalComplement_directSum,
    AddSubgroup.directSum_le_directSum_iff]

/-- A direct sum of additive codes is Lagrangian for the summed pairing exactly when both
summands are. -/
@[simp]
theorem isLagrangian_directSum_iff :
    (A.coordinatePower (ι ⊕ κ)).IsLagrangian (C.directSum D) ↔
      (A.coordinatePower ι).IsLagrangian C ∧ (A.coordinatePower κ).IsLagrangian D := by
  simp only [isLagrangian_def, orthogonalComplement_directSum, AddSubgroup.directSum_inj]

end DirectSum

end TauCeti.FiniteBilinearModule

namespace TauCeti.FiniteQuadraticModule

universe u v w

variable (A : FiniteQuadraticModule.{u}) {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
variable (C : AdditiveCode A ι) (D : AdditiveCode A κ)

/-- A direct sum of additive codes over a finite quadratic alphabet is quadratically isotropic
exactly when both summands are. -/
theorem isIsotropic_directSum_iff :
    (A.coordinatePower (ι ⊕ κ)).IsIsotropic (C.directSum D) ↔
      (A.coordinatePower ι).IsIsotropic C ∧ (A.coordinatePower κ).IsIsotropic D := by
  simp only [isIsotropic_coordinatePower_iff, AddSubgroup.mem_directSum_iff,
    Fintype.sum_sum_type]
  constructor
  · intro h
    refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · simpa using h (Sum.elim x 0) (AddSubgroup.mem_directSum_iff.mp
        (AddSubgroup.sumElim_zero_right_mem_directSum D hx))
    · simpa using h (Sum.elim 0 x) (AddSubgroup.mem_directSum_iff.mp
        (AddSubgroup.sumElim_zero_left_mem_directSum C hx))
  · rintro ⟨hC, hD⟩ x hx
    rw [hC _ hx.1, hD _ hx.2, add_zero]

/-- A direct sum of additive codes over a finite quadratic alphabet is a quadratic Lagrangian
exactly when both summands are. -/
@[simp]
theorem isLagrangian_directSum_iff :
    (A.coordinatePower (ι ⊕ κ)).IsLagrangian (C.directSum D) ↔
      (A.coordinatePower ι).IsLagrangian C ∧ (A.coordinatePower κ).IsLagrangian D := by
  simp only [isLagrangian_def, isIsotropic_directSum_iff,
    FiniteBilinearModule.isLagrangian_directSum_iff]
  tauto

end TauCeti.FiniteQuadraticModule
