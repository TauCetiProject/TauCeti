/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.IrreducibleBasis.Basic

/-!
# Root multiplicities reconstructed from an irreducible basis

Each member of an irreducible basis decomposition is a constant times a product
of fixed powers of basis members. After any specialization into a domain that
does not nullify the input, its root multiplicity is the corresponding weighted
sum of the basis multiplicities. The exponents are independent of both the
specialization and the root. Distinct basis members may acquire common roots,
and their contributions then add.

The same reconstruction holds for any zero-preserving multiplicative map
that sends constant polynomials to constant polynomials; additivity is not needed.

Consequently, two specializations with the same nullification status for the
input and equal basis multiplicities have equal input multiplicities. This
transfers multiplicity invariance on common root sections from the basis to the
original polynomial family. Nullified inputs have multiplicity zero, following
the convention of `Polynomial.rootMultiplicity`.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic
decomposition*, Springer (1998), 242–268, Sections 2–3 (basis preprocessing).
-/

public section

open Polynomial

namespace Finset.IsIrreducibleBasis

variable {R A : Type*} [CommRing R] [CommRing A] [IsDomain A]
  {F B : Finset R[X]} {f : R[X]}

/-- One fixed exponent vector reconstructs root multiplicities under every
zero-preserving multiplicative map that sends constants to constants and does
not nullify the input. Additivity and preservation of degrees are not required. -/
theorem exists_rootMultiplicity_eq_sum (hB : F.IsIrreducibleBasis B) (hf : f ∈ F) :
    ∃ e : R[X] → ℕ, ∀ (φ : R[X] →*₀ A[X]),
      (∀ c : R, ∃ a : A, φ (C c) = C a) → φ f ≠ 0 → ∀ t : A,
      (φ f).rootMultiplicity t = ∑ b ∈ B, e b * (φ b).rootMultiplicity t := by
  classical
  obtain ⟨c, e, hfe⟩ := hB.exists_eq_C_mul_prod f hf
  refine ⟨e, fun φ hC hφ t ↦ ?_⟩
  obtain ⟨a, ha⟩ := hC c
  have hmap : φ f = C a * ∏ b ∈ B, (φ b) ^ e b := by
    rw [hfe, map_mul, ha, map_prod]
    simp only [map_pow]
  have hc : a ≠ 0 := by
    intro hc
    simp [hmap, hc] at hφ
  have hprod : (∏ b ∈ B, (φ b) ^ e b) ≠ 0 :=
    right_ne_zero_of_mul (hmap ▸ hφ)
  rw [← count_roots, hmap, roots_C_mul _ hc, roots_prod _ _ hprod]
  simp only [Multiset.count_bind, roots_pow, Multiset.count_nsmul, count_roots]
  rfl

/-- One fixed exponent vector reconstructs root multiplicities after every
specialization that does not nullify the input. Neither injectivity of the
coefficient map nor preservation of degrees or coprimality is required. -/
theorem exists_rootMultiplicity_map_eq_sum (hB : F.IsIrreducibleBasis B) (hf : f ∈ F) :
    ∃ e : R[X] → ℕ, ∀ (φ : R →+* A), f.map φ ≠ 0 → ∀ t : A,
      (f.map φ).rootMultiplicity t =
        ∑ b ∈ B, e b * (b.map φ).rootMultiplicity t := by
  obtain ⟨e, he⟩ := hB.exists_rootMultiplicity_eq_sum (A := A) hf
  exact ⟨e, fun φ ↦ he (Polynomial.mapRingHom φ) (fun c ↦ ⟨φ c, map_C φ⟩)⟩

/-- Equal basis multiplicities at two specialized points give equal input
multiplicities, provided the input is nullified by both maps or by neither.
The two root values need not be equal, so this applies along moving sections. -/
theorem rootMultiplicity_map_eq (hB : F.IsIrreducibleBasis B) (hf : f ∈ F)
    (φ ψ : R →+* A) (s t : A) (hzero : f.map φ = 0 ↔ f.map ψ = 0)
    (hm : ∀ b ∈ B, (b.map φ).rootMultiplicity s = (b.map ψ).rootMultiplicity t) :
    (f.map φ).rootMultiplicity s = (f.map ψ).rootMultiplicity t := by
  by_cases hφ : f.map φ = 0
  · simp [hφ, hzero.mp hφ]
  · obtain ⟨e, he⟩ := hB.exists_rootMultiplicity_map_eq_sum (A := A) hf
    rw [he φ hφ s, he ψ (hzero.not.mp hφ) t]
    exact Finset.sum_congr rfl fun b hb ↦ congrArg (e b * ·) (hm b hb)

end Finset.IsIrreducibleBasis
