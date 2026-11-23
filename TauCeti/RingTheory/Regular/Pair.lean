/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Powers of weakly regular pairs

For a weakly regular pair `(a, b)` on a module `M`, powers `bʲ` remain regular on
`M ⧸ aⁿ M`, and powers `aʲ` remain regular on `M ⧸ bⁿ M`, even when `b` itself is not
regular on `M`. Their powered scalar images intersect in `(aʳ bˢ)M`, without a flatness
assumption. For `M = R`, this gives the corresponding powered principal-ideal intersection.
These results supply torsion-freeness of principal-adic completions, patching over
`D(a) ∪ D(b)`, and powered principal intersections.

## References

* The Stacks Project, [Regular sequences](https://stacks.math.columbia.edu/tag/0AUH).
-/

public section

universe u v

open RingTheory.Sequence Module Pointwise

section Pow

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- An element `b` is regular on `M ⧸ a M` exactly when `a c = b m` forces `m ∈ a M`. -/
theorem TauCeti.isSMulRegular_quotSMulTop_iff {a b : R} :
    IsSMulRegular (QuotSMulTop a M) b ↔
      ∀ m c : M, a • c = b • m → m ∈ a • (⊤ : Submodule R M) :=
  (isSMulRegular_quotient_iff_mem_of_smul_mem _ b).trans <| forall_congr' fun m ↦ by
    simp [Submodule.mem_smul_pointwise_iff_exists (b • m)]

/-- If `a, b` is a weakly `M`-regular sequence, then `bʲ` is regular on `M ⧸ aⁿ M`. -/
theorem RingTheory.Sequence.IsWeaklyRegular.isSMulRegular_quotSMulTop_pow {a b : R}
    (h : IsWeaklyRegular M [a, b]) (n j : ℕ) : IsSMulRegular (QuotSMulTop (a ^ n) M) (b ^ j) := by
  obtain ⟨ha, hb⟩ := (isWeaklyRegular_cons_iff M a [b]).1 h
  rw [isWeaklyRegular_singleton_iff] at hb
  refine isSMulRegular_iff_right_eq_zero_of_smul.2 fun q hq ↦ ?_
  induction q using Submodule.Quotient.induction_on with | H x => ?_
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
  rw [Submodule.Quotient.mk_eq_zero]
  -- Show by induction on `n` that `bʲ x ∈ aⁿ M` implies `x ∈ aⁿ M`.
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hq
    -- First `x ∈ a M`, since `b` is regular on `M ⧸ a M`.
    have hxa : x ∈ a • (⊤ : Submodule R M) := by
      refine (Submodule.Quotient.mk_eq_zero _).1 ((hb.pow j).right_eq_zero_of_smul ?_)
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← hy, pow_succ',
        mul_smul]
      exact Submodule.smul_mem_pointwise_smul _ a ⊤ trivial
    obtain ⟨x', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hxa
    -- Then cancel `a`, which is `M`-regular, and apply the induction hypothesis.
    have hx' : b ^ j • x' = a ^ n • y := ha <| by
      simp only [smul_comm a (b ^ j), ← mul_smul, ← pow_succ', hy]
    obtain ⟨c, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1
      (ih x' (hx' ▸ Submodule.smul_mem_pointwise_smul _ _ ⊤ trivial))
    rw [smul_smul, ← pow_succ']
    exact Submodule.smul_mem_pointwise_smul _ _ ⊤ trivial

/-- If `a, b` is a weakly `M`-regular sequence, then `aʲ` is regular on `M ⧸ bⁿ M`. Here `b` need
not be regular on `M`. -/
theorem RingTheory.Sequence.IsWeaklyRegular.isSMulRegular_quotSMulTop_pow_swap {a b : R}
    (h : IsWeaklyRegular M [a, b]) (n j : ℕ) : IsSMulRegular (QuotSMulTop (b ^ n) M) (a ^ j) := by
  have ha : IsSMulRegular M (a ^ j) := ((isWeaklyRegular_cons_iff M a [b]).1 h).1.pow j
  refine TauCeti.isSMulRegular_quotSMulTop_iff.2 fun m c hc ↦ ?_
  -- From `bⁿ c = aʲ m`, first `c ∈ aʲ M`, since `bⁿ` is regular on `M ⧸ aʲ M`.
  obtain ⟨d, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1
    (TauCeti.isSMulRegular_quotSMulTop_iff.1 (h.isSMulRegular_quotSMulTop_pow j n) c m hc.symm)
  -- Then cancel `aʲ`, which is `M`-regular, from `aʲ (bⁿ d) = aʲ m`.
  obtain rfl : b ^ n • d = m := ha <| by simp only [← hc, smul_comm (a ^ j)]
  exact Submodule.smul_mem_pointwise_smul _ _ ⊤ trivial

/-- For a weakly regular pair `(a, b)` on `M`, the element `a` is regular on `M ⧸ bⁿ M` for
every `n`. -/
theorem RingTheory.Sequence.IsWeaklyRegular.isSMulRegular_quotient_pow_smul_top {a b : R}
    (h : IsWeaklyRegular M [a, b]) (n : ℕ) :
    IsSMulRegular (M ⧸ (Ideal.span {b} ^ n • ⊤ : Submodule R M)) a := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
  simpa only [pow_one] using h.isSMulRegular_quotSMulTop_pow_swap n 1

namespace RingTheory.Sequence.IsWeaklyRegular

/-- On a module with weakly regular pair `(a, b)`, the images of powers of `a` and `b`
intersect in the image of their product. Neither flatness nor regularity of `b` on `M` is needed. -/
theorem pow_smul_top_inf_pow_smul_top_eq_mul_smul_top
    {a b : R} (h : IsWeaklyRegular M [a, b]) (r s : ℕ) :
    a ^ r • (⊤ : Submodule R M) ⊓ b ^ s • ⊤ = (a ^ r * b ^ s) • ⊤ := by
  apply le_antisymm
  · simpa only [smul_smul, inf_comm, mul_comm] using
      smul_top_inf_eq_smul_of_isSMulRegular_on_quot (h.isSMulRegular_quotSMulTop_pow r s)
  · rw [mul_smul]
    apply le_inf
    · exact smul_mono_right _ le_top
    · rw [smul_comm]
      exact smul_mono_right _ le_top

/-- For a weakly regular pair in a commutative ring, the principal ideals generated by any
powers intersect in the ideal generated by their product. No domain assumption is needed. -/
theorem span_singleton_pow_inf_span_singleton_pow_eq_span_singleton_mul
    {a b : R} (h : IsWeaklyRegular R [a, b]) (r s : ℕ) :
    Ideal.span {a ^ r} ⊓ Ideal.span {b ^ s} = Ideal.span {a ^ r * b ^ s} := by
  simpa only [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top,
    Ideal.span_singleton_mul_span_singleton] using
      h.pow_smul_top_inf_pow_smul_top_eq_mul_smul_top r s

end RingTheory.Sequence.IsWeaklyRegular

end Pow
