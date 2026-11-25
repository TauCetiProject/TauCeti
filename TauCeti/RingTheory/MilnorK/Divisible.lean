/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import TauCeti.LinearAlgebra.TensorProduct.Basic

/-!
# Root factorization divides the Steinberg tensors

Let `R` be a commutative ring and write the unit group additively, `U = Additive Rˣ`. The
degree-two relations of Milnor K-theory are the *Steinberg tensors* `a ⊗ b ∈ U ⊗[ℤ] U` for units
`a, b` with `a + b = 1`. This file proves that if `Xⁿ - a` splits into linear factors over `R`,
the Steinberg tensor `a ⊗ b` is `n` times a sum of Steinberg tensors.

The argument is the root factorization of `Xⁿ - a`. Write `Xⁿ - a = ∏ (X - cᵢ)`, with roots
counted with multiplicity. Evaluating at `1` gives `b = 1 - a = ∏ (1 - cᵢ)`. Each root is a unit
with `cᵢⁿ = a`, and each `1 - cᵢ` divides the unit `b`, so it is a unit with
`cᵢ + (1 - cᵢ) = 1`. Hence

`a ⊗ b = ∑ᵢ a ⊗ (1 - cᵢ) = ∑ᵢ cᵢⁿ ⊗ (1 - cᵢ) = n • ∑ᵢ cᵢ ⊗ (1 - cᵢ)`.

It follows that the submodule spanned by the Steinberg tensors is `n`-divisible whenever every
`Xⁿ - a` splits, for instance for every `n ≠ 0` over an algebraically closed field. Together with
the divisibility statements for tensor products in
`TauCeti.LinearAlgebra.TensorProduct.Divisible` and
`TauCeti.LinearAlgebra.PiTensorProduct.Divisible`, and for quotients in
`TauCeti.RingTheory.Regular.IsSMulRegular`, this is the input for the unique divisibility of the
Milnor K-groups `TauCeti.MilnorK` of an algebraically closed field in degrees at least two. Over
a field of characteristic `p` the roots of `Xᵖ - a` all coincide, and the argument uses them with
their multiplicity.

## Main results

* `TauCeti.exists_ofMul_tmul_ofMul_eq_nsmul_sum`: if `a + b = 1` and `Xⁿ - a` splits, then
  `a ⊗ b = n • ∑ᵢ cᵢ ⊗ dᵢ` for finitely many unit pairs with `cᵢ + dᵢ = 1` and `cᵢⁿ = a`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Proposition 6.4.1 and Exercise 7.3.
-/

public section

open Polynomial
open scoped TensorProduct

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- **Root factorization of a Steinberg tensor.** Let `a, b` be units of a commutative ring
with `a + b = 1`, and suppose `Xⁿ - a` splits for some `n ≠ 0`. Then in
`Additive Rˣ ⊗[ℤ] Additive Rˣ` the Steinberg tensor `a ⊗ b` is `n` times a finite sum of Steinberg
tensors `c ⊗ d` of unit pairs with `c + d = 1` and `cⁿ = a`. -/
theorem exists_ofMul_tmul_ofMul_eq_nsmul_sum {n : ℕ} (hn : n ≠ 0) {a b : Rˣ}
    (hab : (a : R) + b = 1) (hsplit : (X ^ n - C (a : R)).Splits) :
    ∃ s : Multiset (Rˣ × Rˣ), (∀ x ∈ s, (x.1 : R) + x.2 = 1 ∧ x.1 ^ n = a) ∧
      Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b =
        n • (s.map fun x ↦ Additive.ofMul x.1 ⊗ₜ[ℤ] Additive.ofMul x.2).sum := by
  classical
  -- A factorization `Xⁿ - a = ∏ (X - c)`, with the roots `c` counted with multiplicity.
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset.1 hsplit
  rw [(monic_X_pow_sub_C (a : R) hn).leadingCoeff, C_1, one_mul] at hm
  have heval (x : R) : x ^ n - a = (m.map (x - ·)).prod := by
    simpa [eval_multiset_prod, Multiset.map_map, Function.comp_def] using congrArg (eval x) hm
  have hpow (c : R) (hc : c ∈ m) : c ^ n = a := by
    rw [← sub_eq_zero, heval]
    exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨c, hc, sub_self c⟩)
  -- Evaluating the factorization at `1` gives `b = ∏ (1 - c)`.
  have hprod : (m.map (1 - ·)).prod = (b : R) := by
    rw [← heval, one_pow, ← hab, add_sub_cancel_left]
  -- Every root is a unit, since its `n`th power is the unit `a`.
  lift m to Multiset Rˣ using fun c hc ↦ (isUnit_pow_iff hn).1 (hpow c hc ▸ a.isUnit)
  simp only [Multiset.map_map, Function.comp_def] at hprod
  replace hpow (c : Rˣ) (hc : c ∈ m) : c ^ n = a :=
    Units.ext (by simpa using hpow c (Multiset.mem_map_of_mem _ hc))
  -- Every `1 - c` divides the unit `b`, so it is a unit `d c`.
  have hunit (c : Rˣ) (hc : c ∈ m) : ∃ d : Rˣ, (d : R) = 1 - c :=
    isUnit_of_dvd_unit (Multiset.dvd_prod (Multiset.mem_map_of_mem (fun c : Rˣ ↦ 1 - (c : R)) hc))
      (hprod ▸ b.isUnit)
  choose! d hd using hunit
  have hb : b = (m.map d).prod := Units.ext <| by
    rw [← hprod, ← Units.coeHom_apply, map_multiset_prod, Multiset.map_map]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun c hc ↦ (hd c hc).symm)
  refine ⟨m.map fun c ↦ (c, d c), ?_, ?_⟩
  · simp only [Multiset.mem_map]
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨by simp [hd c hc], hpow c hc⟩
  · simp only [hb, ofMul_multiset_prod, TensorProduct.tmul_multiset_sum, Multiset.map_map,
      Function.comp_def, ← Multiset.sum_map_nsmul]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun c hc ↦ ?_)
    rw [← hpow c hc, ofMul_pow, TensorProduct.smul_tmul']

end TauCeti
