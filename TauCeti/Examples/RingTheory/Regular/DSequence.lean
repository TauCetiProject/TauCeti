/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Regular.DSequence

/-!
# d-sequences that are not regular, and the role of the order

Over `ℤ`, the list `[2, 0]` is a d-sequence: `2` is injective on `(2, 0) ℤ = 2 ℤ`, and the second
condition only concerns elements of `(2, 0) ℤ`, which already lie in `2 ℤ`. It is not weakly
regular, because `0` is not regular on `ℤ ⧸ 2 ℤ`. The reversed list `[0, 2]` is not a d-sequence:
multiplication by `0` is not injective on `(0, 2) ℤ = 2 ℤ`. So the order of a d-sequence matters.

## References

* K. Česnavičius, *Macaulayfication of Noetherian schemes*, arXiv:1810.04493v2, Definition 3.8.
-/

public section

open scoped Pointwise

namespace TauCeti.IsDSequence

/-- `[2, 0]` is a d-sequence on `ℤ`. -/
example : IsDSequence ℤ [(2 : ℤ), 0] := by
  rw [isDSequence_iff_forall_mem_of_smul_mem]
  intro i hi x hx hrx
  have h20 : Ideal.ofList [(2 : ℤ), 0] = Ideal.ofList [2] := by
    simp [Ideal.ofList_cons]
  match i, hi with
  | 0, _ =>
    simpa using hrx
  | 1, _ => simpa [h20] using hx

/-- `[2, 0]` is not weakly regular on `ℤ`: `0` is not regular on `ℤ ⧸ 2 ℤ`. -/
example : ¬ RingTheory.Sequence.IsWeaklyRegular ℤ [(2 : ℤ), 0] := by
  intro h
  have h1 := h.regular_mod_prev 1 (by simp)
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem] at h1
  have h11 := h1 1 (by simp)
  simp [Ideal.mem_span_singleton] at h11

/-- `[0, 2]` is not a d-sequence on `ℤ`: `0` kills the nonzero element `2` of `(0, 2) ℤ`. -/
example : ¬ IsDSequence ℤ [(0 : ℤ), 2] := by
  intro h
  have hx : (2 : ℤ) • (1 : ℤ) ∈ (Ideal.ofList [(0 : ℤ), 2] • ⊤ : Submodule ℤ ℤ) :=
    Submodule.smul_mem_smul (Ideal.subset_span (by simp)) Submodule.mem_top
  have h2 := h.mem_of_smul_mem (i := 0) (by simp) hx (by simp)
  simp at h2

end TauCeti.IsDSequence
