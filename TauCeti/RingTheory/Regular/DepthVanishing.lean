/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Regular.RegularSequence

import Mathlib.RingTheory.Ideal.Span
import TauCeti.RingTheory.MvPolynomial.RegularSequence

/-!
# Depth vanishing along a weakly regular sequence

For a commutative ring `A` and a family of functors `H : ℕ → ModuleCat A → ModuleCat A` whose
values are `I`-power torsion and satisfy the inductive regularity criterion along `M`-regular
elements, `H n M` vanishes whenever `I` contains a weakly `M`-regular sequence of length greater
than `n`. We also record the special case that the first `d` indeterminates of
`MvPolynomial (Fin (d + e)) R` form a weakly regular sequence.

## Main results

* `TauCeti.depth_vanishing`: if every element of `H n M` is annihilated by a power of each element
  of `I`, and an `M`-regular element `r` is regular on `H n M` whenever `H m (M / rM) = 0` for all
  `m < n`, then `Subsingleton (H n M)` for any weakly `M`-regular sequence `l` in `I` with
  `n < l.length`.
* `TauCeti.isWeaklyRegular_X_castAdd`: the first `d` variables
  `List.ofFn (MvPolynomial.X ∘ Fin.castAdd e)` form a weakly regular sequence in
  `MvPolynomial (Fin (d + e)) R`.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean at commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`, file
  `src/Lib/Cohomology/Hodge/DepthVanishing.lean` (declarations `New.Variety.depth_vanishing`,
  `New.Variety.isWeaklyRegular_X_castAdd`); Apache 2.0, Copyright 2026 Anthropic, PBC.
-/

public section

namespace TauCeti

/-- Abstract depth vanishing along a weakly regular sequence. Let
`H : ℕ → ModuleCat A → ModuleCat A` be a family of module-valued assignments such that every
element of `H n M` is killed by a power of each element of `I`, and such that an `M`-regular
element `r : A` is regular on `H n M` whenever `H m (M / rM)` is subsingleton for all `m < n`.
If `l : List A` is a weakly `M`-regular sequence contained in `I` with `n < l.length`, then
`H n M` is subsingleton. -/
theorem depth_vanishing {A : Type*} [CommRing A] (H : ℕ → ModuleCat A → ModuleCat A)
    {I : Ideal A} {l : List A}
    (h_torsion : ∀ (n : ℕ) (M : ModuleCat A) (x : H n M), ∀ r ∈ I, ∃ j : ℕ, r ^ j • x = 0)
    (h_regular : ∀ (n : ℕ) (M : ModuleCat A) (r : A), IsSMulRegular M r →
      (∀ m < n, Subsingleton (H m (ModuleCat.of A (QuotSMulTop r M)))) →
      IsSMulRegular (H n M) r)
    (h_le : Ideal.ofList l ≤ I) {n : ℕ} (hn : n < l.length) (M : ModuleCat A)
    (h_weak : RingTheory.Sequence.IsWeaklyRegular M l) :
    Subsingleton (H n M) := by
  induction l generalizing M n with
  | nil => simp at hn
  | cons r l ih =>
    obtain ⟨hr_mem, hl_le⟩ : r ∈ I ∧ Ideal.ofList l ≤ I := by
      simpa [Ideal.span_singleton_le_iff_mem] using h_le
    obtain ⟨hr_reg, hl_reg⟩ := (RingTheory.Sequence.isWeaklyRegular_cons_iff M r l).mp h_weak
    have h_quot : ∀ m < n, Subsingleton (H m (ModuleCat.of A (QuotSMulTop r M))) :=
      fun m hm ↦ ih hl_le (Nat.lt_of_lt_of_le hm (Nat.lt_succ_iff.mp hn)) _ hl_reg
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨j, hj⟩ := h_torsion n M x r hr_mem
    exact ((h_regular n M r hr_reg h_quot).pow j).right_eq_zero_of_smul hj

/-- The first `d` indeterminates of `MvPolynomial (Fin (d + e)) R` form a weakly regular
sequence. -/
theorem isWeaklyRegular_X_castAdd (R : Type*) [CommRing R] (d e : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin (d + e)) R)
      (List.ofFn (MvPolynomial.X (R := R) ∘ Fin.castAdd (n := d) e)) := by
  rw [← List.map_ofFn]
  exact MvPolynomial.isWeaklyRegular_map_X _ (List.nodup_ofFn.mpr (Fin.castAdd_injective d e))

end TauCeti
