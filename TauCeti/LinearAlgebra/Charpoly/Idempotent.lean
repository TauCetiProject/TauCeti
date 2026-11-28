/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Charpoly.Newton
import TauCeti.LinearAlgebra.Trace.Idempotent

/-!
# Comparing characteristic polynomials on images of idempotents

An operator preserving the image of an idempotent has trace on that image equal to the
ambient trace after multiplication by the idempotent. Comparing these ambient traces for
all powers, including the zeroth power to recover the ranks, compares the characteristic
polynomials on the images. The ambient formulation is linear in the projector, so it also
applies when trace comparisons are available separately for the terms of a sum of projectors.

This is the linear algebra of the comparison on the good forms in
`New.Data.charpoly_heckeOnGood_eq` in `New/Spanning/Multiplicities/EqualMultiplicities.lean`
of [lsernau/grh-lean](https://github.com/lsernau/grh-lean) (revision `72fead1`).
-/

public section

open Module

namespace LinearMap

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The characteristic polynomials of two operators restricted to invariant images of
idempotents agree exactly when the ambient traces of all powers multiplied by their respective
idempotents agree. The zeroth power compares the dimensions of the images. -/
theorem charpoly_restrict_range_eq_iff_trace_mul_pow_eq [CharZero K]
    {e f : End K V} {d g : End K W} (he : IsIdempotentElem e) (hd : IsIdempotentElem d)
    (hf : ∀ x ∈ range e, f x ∈ range e) (hg : ∀ x ∈ range d, g x ∈ range d) :
    (f.restrict hf).charpoly = (g.restrict hg).charpoly ↔
      ∀ n : ℕ, trace K V (e * f ^ n) = trace K W (d * g ^ n) := by
  have htrace (n : ℕ) : trace K V (e * f ^ n) = trace K (range e) ((f.restrict hf) ^ n) := by
    rw [End.pow_restrict n hf]
    exact trace_mul_eq_trace_restrict_range he _
  have htrace' (n : ℕ) : trace K W (d * g ^ n) = trace K (range d) ((g.restrict hg) ^ n) := by
    rw [End.pow_restrict n hg]
    exact trace_mul_eq_trace_restrict_range hd _
  simp only [htrace, htrace']
  refine ⟨fun h n ↦ trace_pow_eq_of_charpoly_eq h n, fun h ↦ ?_⟩
  apply charpoly_eq_of_trace_pow_eq
  · simpa only [pow_zero, trace_one, Nat.cast_inj] using h 0
  · exact fun n _ _ ↦ h n

end LinearMap

namespace MonoidHom

variable {K A V W : Type*} [Field K] [Monoid A]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

open LinearMap

/-- Two monoid representations have identical characteristic polynomials on invariant
projector images if and only if their ambient traces with the projectors inserted agree on
the whole monoid. -/
theorem charpoly_restrict_range_eq_iff_trace_mul_eq [CharZero K]
    (ρ : A →* End K V) (σ : A →* End K W) {e : End K V} {d : End K W}
    (he : IsIdempotentElem e) (hd : IsIdempotentElem d)
    (hρ : ∀ a, ∀ x ∈ e.range, ρ a x ∈ e.range)
    (hσ : ∀ a, ∀ x ∈ d.range, σ a x ∈ d.range) :
    (∀ a, ((ρ a).restrict (hρ a)).charpoly = ((σ a).restrict (hσ a)).charpoly) ↔
      ∀ a, trace K V (e * ρ a) = trace K W (d * σ a) := by
  simp only [charpoly_restrict_range_eq_iff_trace_mul_pow_eq he hd]
  refine ⟨fun h a ↦ by simpa only [pow_one] using h a 1, fun h a n ↦ ?_⟩
  simpa only [map_pow] using h (a ^ n)

/-- To compare the characteristic polynomials on the images of two idempotent sums, it is
sufficient to compare the inserted traces separately for each corresponding summand. The
individual summands need not preserve the two invariant images. -/
theorem charpoly_restrict_range_eq_of_sum_trace_mul_eq [CharZero K]
    (ρ : A →* End K V) (σ : A →* End K W) {ι : Type*} (s : Finset ι)
    (e : ι → End K V) (d : ι → End K W)
    (he : IsIdempotentElem (∑ i ∈ s, e i)) (hd : IsIdempotentElem (∑ i ∈ s, d i))
    (hρ : ∀ a, ∀ x ∈ LinearMap.range (∑ i ∈ s, e i),
      ρ a x ∈ LinearMap.range (∑ i ∈ s, e i))
    (hσ : ∀ a, ∀ x ∈ LinearMap.range (∑ i ∈ s, d i),
      σ a x ∈ LinearMap.range (∑ i ∈ s, d i))
    (h : ∀ a i, i ∈ s → trace K V (e i * ρ a) = trace K W (d i * σ a)) (a : A) :
    ((ρ a).restrict (hρ a)).charpoly = ((σ a).restrict (hσ a)).charpoly := by
  apply (ρ.charpoly_restrict_range_eq_iff_trace_mul_eq σ he hd hρ hσ).mpr _ a
  intro b
  simp only [Finset.sum_mul, map_sum]
  exact Finset.sum_congr rfl (fun i hi ↦ h b i hi)

end MonoidHom
