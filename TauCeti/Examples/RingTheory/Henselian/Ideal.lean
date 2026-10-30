/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselian.Ideal

/-!
# Tests for henselian pairs and nested ideals

The proper nonzero ideals `(4) ≤ (2)` of `ℤ/16ℤ` exercise restriction of the
henselian ideal, quotient descent and two-stage lifting. A simple root modulo `(4)`
lifts to an actual nonzero root in `(4)`, not just to an element of `(2)`.
The zero and unit ideals test the boundary cases of the nested-ideal criterion.
-/

public section

open Ideal Polynomial

namespace TauCeti.Examples.HenselianIdeal

-- Nilpotent ideals are contained in the nilradical, which is henselian by radical permanence.
private instance : HenselianRing (ZMod 16) (Ideal.span {2}) := by
  have h : (Ideal.span {2} : Ideal (ZMod 16)) ≤ (⊥ : Ideal (ZMod 16)).radical := by
    rw [span_singleton_le_iff_mem]
    exact ⟨4, by rw [Ideal.mem_bot]; decide⟩
  exact henselianRing_of_le h

private theorem four_le_two : (Ideal.span {4} : Ideal (ZMod 16)) ≤ Ideal.span {2} := by
  rw [span_singleton_le_iff_mem, mem_span_singleton]
  exact ⟨2, by decide⟩

-- The smaller ideal is genuinely nonzero and different from the larger one.
example : (4 : ZMod 16) ≠ 0 ∧ (2 : ZMod 16) ∉ Ideal.span {(4 : ZMod 16)} := by
  constructor
  · decide
  · rw [mem_span_singleton, dvd_def]
    decide

-- Henselianity restricts to a strictly smaller ideal, without radical equality being assumed.
example : HenselianRing (ZMod 16) (Ideal.span {4}) :=
  henselianRing_of_le four_le_two

-- The quotient keeps its nonzero henselian ideal; this is not merely the residue field.
example : HenselianRing ((ZMod 16) ⧸ Ideal.span {(4 : ZMod 16)})
    ((Ideal.span {2}).map (Ideal.Quotient.mk (Ideal.span {4}))) :=
  inferInstance

/-- The simple root zero modulo `(4)` lifts to a nonzero root in `(4)` over `ℤ/16ℤ`. -/
theorem exists_nonzero_root : ∃ a : ZMod 16,
    a ^ 2 + a - 4 = 0 ∧ a ∈ Ideal.span {4} ∧ a ≠ 0 := by
  have : HenselianRing (ZMod 16) (Ideal.span {4}) := henselianRing_of_le four_le_two
  obtain ⟨a, ha₀, ha⟩ := TauCeti.HenselianRing.exists_sq_add_eq_of_mem
    (J := Ideal.span {(4 : ZMod 16)}) (c := 4) (Ideal.subset_span (by simp))
  have hroot : a ^ 2 + a - 4 = 0 := sub_eq_zero.mpr ha
  refine ⟨a, hroot, ha₀, ?_⟩
  rintro rfl
  exact (by decide : (0 : ZMod 16) ^ 2 + 0 - 4 ≠ 0) hroot

-- Reconstruct the original pair from the two successive henselian pairs.
example : HenselianRing (ZMod 16) (Ideal.span {2}) := by
  have : HenselianRing (ZMod 16) (Ideal.span {4}) := henselianRing_of_le four_le_two
  have : HenselianRing ((ZMod 16) ⧸ Ideal.span {(4 : ZMod 16)})
      ((Ideal.span {2}).map (Ideal.Quotient.mk (Ideal.span {4}))) := inferInstance
  exact henselianRing_of_quotient four_le_two

-- Equality is allowed in the nesting, and the upper quotient ideal is then zero.
example (R : Type*) [CommRing R] (I : Ideal R) [HenselianRing R I] :
    HenselianRing (R ⧸ I) ⊥ := by
  simpa using (inferInstance : HenselianRing (R ⧸ I) (I.map (Ideal.Quotient.mk I)))

-- The criterion retains the zero ring and its unit ideal.
example : HenselianRing (ZMod 1) ⊤ ↔
    HenselianRing (ZMod 1) ⊥ ∧
      HenselianRing ((ZMod 1) ⧸ (⊥ : Ideal (ZMod 1)))
        ((⊤ : Ideal (ZMod 1)).map (Ideal.Quotient.mk ⊥)) :=
  henselianRing_iff_quotient bot_le

-- Henselianity of the smaller pair alone does not imply henselianity of the larger pair.
example : HenselianRing ℚ ⊥ ∧ ¬ HenselianRing ℚ ⊤ := by
  refine ⟨inferInstance, fun h ↦ ?_⟩
  have hunit := mem_jacobson_bot.1 (h.jac (x := 1) trivial) (-1)
  norm_num at hunit

end TauCeti.Examples.HenselianIdeal
