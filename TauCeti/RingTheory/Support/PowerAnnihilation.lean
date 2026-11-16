/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Support and annihilation by an ideal power

For a finite module `M` and a finitely generated ideal `I`, support in `V(I)` in the
prime spectrum is equivalent to annihilation by a single positive power of `I`.
The ideal need not be an ideal of definition and the ring need not be noetherian.

This is the affine algebraic support condition used for coherent modules on formal
spectra. It refers to the support in `Spec R`, not to the possibly much smaller space
of open primes of an adic ring. In particular, full topological support on a one-point
formal spectrum does not imply annihilation by a power of its maximal ideal.

## References

* The Stacks Project, Tag 00L6 (finite modules and closed support).
-/

public section

namespace Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A finite module has support in `V(I)` exactly when a positive power of the finitely
generated ideal `I` annihilates it. -/
theorem support_subset_zeroLocus_iff_exists_pow_le_annihilator [Module.Finite R M]
    {I : Ideal R} (hI : I.FG) :
    support R M ⊆ PrimeSpectrum.zeroLocus I ↔
      ∃ n : ℕ, 0 < n ∧ I ^ n ≤ annihilator R M := by
  rw [support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h hI
    exact ⟨n + 1, Nat.succ_pos n, (Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn⟩
  · rintro ⟨n, -, h⟩ r hr
    exact ⟨n, h (Ideal.pow_mem_pow hr n)⟩

end Module
