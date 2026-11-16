/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.LinearAlgebra.TensorProduct.Basic

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
the divisibility statements for tensor products and their quotients in
`TauCeti.LinearAlgebra.TensorProduct.Divisible` and
`TauCeti.LinearAlgebra.PiTensorProduct.Divisible`, this is the input for the unique divisibility
of the Milnor K-groups of an algebraically closed field in degrees at least two. In
characteristic `p` the roots of `Xᵖ - a` all coincide, and the argument uses them with their
multiplicity.

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
tensors `c ⊗ d`, with `c + d = 1` and `cⁿ = a`: the pairs are the roots `c` of a factorization
`Xⁿ - a = ∏ (X - c)`, counted with multiplicity, together with `d = 1 - c`. -/
theorem exists_ofMul_tmul_ofMul_eq_nsmul_sum {n : ℕ} (hn : n ≠ 0) {a b : Rˣ}
    (hab : (a : R) + b = 1) (hsplit : (X ^ n - C (a : R)).Splits) :
    ∃ s : Multiset (Rˣ × Rˣ), (∀ x ∈ s, (x.1 : R) + x.2 = 1 ∧ x.1 ^ n = a) ∧
      Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b =
        n • (s.map fun x ↦ Additive.ofMul x.1 ⊗ₜ[ℤ] Additive.ofMul x.2).sum := by
  classical
  -- A factorization `f = ∏ (X - c)`, with the roots `c` counted with multiplicity.
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset.1 hsplit
  rw [(monic_X_pow_sub_C (a : R) hn).leadingCoeff, C_1, one_mul] at hm
  have heval (x : R) : x ^ n - a = (m.map (x - ·)).prod := by
    simpa [eval_multiset_prod, Multiset.map_map, Function.comp_def] using congrArg (eval x) hm
  have hpow : ∀ c ∈ m, c ^ n = a := fun c hc ↦ by
    rw [← sub_eq_zero, heval]
    exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨c, hc, sub_self c⟩)
  -- Evaluating the factorization at `1` gives `b = ∏ (1 - c)`.
  have hprod : (m.map (1 - ·)).prod = (b : R) := by
    rw [← heval, one_pow, ← hab, add_sub_cancel_left]
  -- Every root is a unit, since its `n`th power is the unit `a`.
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : Multiset Rˣ, s₀.map (↑) = m :=
    CanLift.prf (β := Multiset Rˣ) m fun c hc ↦
      (isUnit_pow_iff hn).1 (hpow c hc ▸ a.isUnit)
  -- Every `1 - c` divides the unit `b`, so it is a unit.
  have hunit : ∀ c ∈ s₀, IsUnit (1 - (c : R)) := fun c hc ↦ by
    refine isUnit_of_dvd_unit (Multiset.dvd_prod ?_) (hprod ▸ b.isUnit)
    rw [← hs₀, Multiset.map_map]
    exact Multiset.mem_map_of_mem _ hc
  let u : R → Rˣ := fun x ↦ if h : IsUnit (1 - x) then h.unit else 1
  have hu : ∀ c ∈ s₀, (u c : R) = 1 - c := fun c hc ↦ by simp [u, hunit c hc]
  have hb : b = (s₀.map fun c : Rˣ ↦ u c).prod := by
    have h := map_multiset_prod (Units.coeHom R) (s₀.map fun c : Rˣ ↦ u c)
    simp only [Units.coeHom_apply, Multiset.map_map] at h
    rw [Units.ext_iff, h, ← hprod, ← hs₀, Multiset.map_map]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun c hc ↦ (hu c hc).symm)
  have hpow' : ∀ c ∈ s₀, c ^ n = a := fun c hc ↦
    Units.ext (by exact_mod_cast hpow c (hs₀ ▸ Multiset.mem_map_of_mem _ hc))
  refine ⟨s₀.map fun c : Rˣ ↦ (c, u c), ?_, ?_⟩
  · simp only [Multiset.mem_map]
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨by simp [hu c hc], hpow' c hc⟩
  · have h := map_multiset_sum (TensorProduct.mk ℤ (Additive Rˣ) (Additive Rˣ) (Additive.ofMul a))
      (s₀.map fun c : Rˣ ↦ Additive.ofMul (u c))
    rw [hb, ofMul_multiset_prod, Multiset.map_map, Multiset.map_map, ← Multiset.sum_map_nsmul]
    simp only [TensorProduct.mk_apply, Multiset.map_map, Function.comp_def] at h ⊢
    rw [h]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun c hc ↦ ?_)
    simp [← hpow' c hc, ofMul_pow, TensorProduct.smul_tmul']

end TauCeti
