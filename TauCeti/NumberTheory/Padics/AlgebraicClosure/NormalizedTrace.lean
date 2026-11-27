/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.NormalizedTrace
public import Mathlib.NumberTheory.Padics.Complex
public import TauCeti.NumberTheory.Cyclotomic.Tower

import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.NumberTheory.Cyclotomic.Irreducible
import TauCeti.NumberTheory.Padics.NormedAlgebra
import TauCeti.RingTheory.Polynomial.Cyclotomic.PrimePow
import TauCeti.RingTheory.RootsOfUnity.Ultrametric

/-!
# Tate's bound for the normalized trace on `ℚ_p(μ_{p^∞})`

Let `T = Algebra.normalizedTrace ℚ_[p] (PadicAlgCl p)` be the normalized trace from the algebraic
closure of `ℚ_p` to `ℚ_p`: on a finite extension `L` of `ℚ_p` it is `[L : ℚ_p]⁻¹ Tr_{L/ℚ_p}`.
On the full cyclotomic extension `ℚ_p(μ_{p^∞}) = TauCeti.cyclotomicTower p ℚ_[p] (PadicAlgCl p)`
it is bounded: `‖T z‖ ≤ p ‖z‖`. This is the first case of Tate's normalized traces `R_n`, the
retraction `R_0` of the cyclotomic tower of `ℚ_p` onto its base. It is the analytic input of
Tate's theorem that `ℂ_p` has no nonzero invariants in a nonzero Tate twist.

The proof is elementary. The normalized trace of a root of unity of `p`-power order has norm at
most one: it is `1` for `ζ = 1`, `-(p - 1)⁻¹` in order `p`, and `0` in higher order, read off
from the cyclotomic polynomial, which is the minimal polynomial over `ℚ_p`. An element `z` of
`ℚ_p(μ_{p^{n+1}})` is a `ℚ_p`-combination `∑ aᵢ πⁱ` of the powers below `e = φ(p^{n+1})` of the
uniformizer `π = ζ - 1`. Since `‖π‖ ^ e = ‖p‖`, the nonzero terms have distinct norms, so each is
at most `‖z‖`, and `‖aᵢ‖ ≤ p ‖aᵢ πⁱ‖ ≤ p ‖z‖`. Expanding `πⁱ` binomially, `‖T πⁱ‖ ≤ 1`.

## Main results

* `PadicAlgCl.norm_normalizedTrace_le_one_of_pow_eq_one`: the normalized trace of a root of unity
  of `p`-power order has norm at most one.
* `PadicAlgCl.norm_normalizedTrace_le`: Tate's bound `‖T z‖ ≤ p ‖z‖` on `ℚ_p(μ_{p^∞})`.

## References

* J. Tate, *p-divisible groups*, Proceedings of a Conference on Local Fields (Driebergen, 1966),
  Springer, 1967, §3.1.
* O. Brinon and B. Conrad, *CMI summer school notes on p-adic Hodge theory* (2009), §14.1.
* J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois representations*, §1.4 and §4.3.

The bound and its proof through the expansion in powers of `ζ - 1` are adapted from
`New.Period.exists_norm_normalizedTrace_le` in `src/Lib/PadicHodge/TateSen.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), which proves
the bound with an inexplicit constant.
-/

public section

open Polynomial Algebra IntermediateField

namespace PadicAlgCl

variable {p : ℕ} [hp : Fact p.Prime]

/-- The normalized trace to `ℚ_p` of a root of unity of `p`-power order has norm at most one: it
is `1` at `1`, `-(p - 1)⁻¹` on a root of order `p`, and `0` on a root of higher order. -/
theorem norm_normalizedTrace_le_one_of_pow_eq_one {ζ : PadicAlgCl p} {n : ℕ}
    (hζ : ζ ^ p ^ n = 1) : ‖normalizedTrace ℚ_[p] (PadicAlgCl p) ζ‖ ≤ 1 := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hζ)
  have hprim : IsPrimitiveRoot ζ (p ^ k) := hk ▸ IsPrimitiveRoot.orderOf ζ
  rcases k with _ | m
  · rw [pow_zero, IsPrimitiveRoot.one_right_iff] at hprim
    subst hprim
    have h1 : normalizedTrace ℚ_[p] (PadicAlgCl p) 1 = 1 := by
      simpa using normalizedTrace_algebraMap_apply ℚ_[p] ℚ_[p] (PadicAlgCl p) 1
    simp [h1]
  rw [normalizedTrace_minpoly, ← hprim.minpoly_eq_cyclotomic_of_irreducible
    (TauCeti.irreducible_cyclotomic_prime_pow_ratPadic p _), nextCoeff_cyclotomic_prime_pow p,
    natDegree_cyclotomic, Nat.totient_prime_pow_succ hp.out]
  split_ifs with hm
  · subst hm
    have hcop : p.Coprime (p - 1) :=
      (Nat.coprime_self_sub_right hp.out.one_le).mpr (Nat.coprime_one_right _)
    simp [Padic.norm_natCast_eq_one_iff.mpr hcop]
  · simp

/-- The normalized traces of the powers of `ζ - 1`, for a root of unity `ζ` of `p`-power order,
have norm at most one: by the binomial theorem, `(ζ - 1) ^ i` is an integral combination of powers
of `ζ`. -/
theorem norm_normalizedTrace_sub_one_pow_le_one {ζ : PadicAlgCl p} {n : ℕ} (hζ : ζ ^ p ^ n = 1)
    (i : ℕ) : ‖normalizedTrace ℚ_[p] (PadicAlgCl p) ((ζ - 1) ^ i)‖ ≤ 1 := by
  rw [sub_pow, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ ↦ ?_
  have hj : (ζ ^ j) ^ p ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have h_eq : (-1) ^ (j + i) * ζ ^ j * 1 ^ (i - j) * (i.choose j : PadicAlgCl p) =
      ((((-1) ^ (j + i) * i.choose j : ℤ) : ℚ_[p]) • ζ ^ j) := by
    rw [Algebra.smul_def]; push_cast; ring
  rw [h_eq, map_smul, norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ _)).trans
    (norm_normalizedTrace_le_one_of_pow_eq_one hj)

/-- An element of `ℚ_p(μ_{p^{n+1}})` is a `ℚ_p`-combination of the powers `(ζ - 1) ^ i` with `i`
below `φ(p ^ (n + 1))`, for a primitive root `ζ` of order `p ^ (n + 1)`: the monic polynomial
`Φ(X + 1)` of that degree kills `ζ - 1`, and `ζ - 1` generates the field. -/
private theorem exists_sum_smul_sub_one_pow_eq {n : ℕ} {ζ z : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ (p ^ (n + 1)))
    (hz : z ∈ IntermediateField.adjoin ℚ_[p] {y : PadicAlgCl p | y ^ p ^ (n + 1) = 1}) :
    ∃ a : ℕ → ℚ_[p], ∑ i ∈ Finset.range (p ^ (n + 1)).totient, a i • (ζ - 1) ^ i = z := by
  classical
  have hζmem : ζ ∈ ℚ_[p]⟮ζ - 1⟯ := by
    simpa using add_mem (mem_adjoin_simple_self ℚ_[p] (ζ - 1)) (one_mem ℚ_[p]⟮ζ - 1⟯)
  have h_mem : z ∈ ℚ_[p]⟮ζ - 1⟯ := by
    refine (IntermediateField.adjoin_le_iff.mpr ?_) hz
    intro y (hy : y ^ p ^ (n + 1) = 1)
    obtain ⟨k, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hy
    exact pow_mem hζmem k
  have hf : ((cyclotomic (p ^ (n + 1)) ℚ_[p]).comp (X + C 1)).Monic :=
    (cyclotomic.monic _ ℚ_[p]).comp_X_add_C 1
  have hroot : aeval (ζ - 1) ((cyclotomic (p ^ (n + 1)) ℚ_[p]).comp (X + C 1)) = 0 := by
    rw [aeval_comp, hζ.minpoly_eq_cyclotomic_of_irreducible
      (TauCeti.irreducible_cyclotomic_prime_pow_ratPadic p _)]
    simp
  have h_span := Submodule.span_range_natDegree_eq_adjoin hf hroot
  rw [natDegree_comp, natDegree_X_add_C, mul_one, natDegree_cyclotomic] at h_span
  rw [← Submodule.mem_span_image_finset_iff_exists_fun', ← Finset.coe_image, h_span,
    Subalgebra.mem_toSubmodule, ← adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic _)]
  exact h_mem

/-- **Tate's bound for the normalized trace.** On the full cyclotomic extension `ℚ_p(μ_{p^∞})`,
the normalized trace to `ℚ_p` satisfies `‖T z‖ ≤ p ‖z‖`. -/
theorem norm_normalizedTrace_le {z : PadicAlgCl p}
    (hz : z ∈ TauCeti.cyclotomicTower p ℚ_[p] (PadicAlgCl p)) :
    ‖normalizedTrace ℚ_[p] (PadicAlgCl p) z‖ ≤ p * ‖z‖ := by
  classical
  obtain ⟨n, hn⟩ := TauCeti.mem_cyclotomicTower_iff.mp hz
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (PadicAlgCl p) (p ^ (n + 1))
  obtain ⟨a, rfl⟩ := exists_sum_smul_sub_one_pow_eq hζ
    (TauCeti.monotone_adjoin_pow_eq_one p ℚ_[p] (PadicAlgCl p) n.le_succ hn)
  set e := (p ^ (n + 1)).totient
  -- `π = ζ - 1` has `‖π‖ ^ e = p⁻¹`.
  have hπe : ‖ζ - 1‖ ^ e = (p : ℝ)⁻¹ := by
    rw [hζ.norm'_sub_one_pow_totient_prime_pow, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)),
      PadicAlgCl.norm_extends, Padic.norm_p]
  have hπ1 : ‖ζ - 1‖ < 1 := by
    by_contra! h
    have := one_le_pow₀ (n := e) h
    rw [hπe] at this
    exact absurd this (not_le.mpr (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)))
  rw [← Finset.sum_filter_ne_zero, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi ↦ ?_
  have hie : i ≤ e := (Finset.mem_range.mp (Finset.mem_filter.mp hi).1).le
  calc ‖normalizedTrace ℚ_[p] (PadicAlgCl p) (a i • (ζ - 1) ^ i)‖ ≤ ‖a i‖ := by
        rw [map_smul, norm_smul]
        exact mul_le_of_le_one_right (norm_nonneg _)
          (norm_normalizedTrace_sub_one_pow_le_one hζ.pow_eq_one i)
    _ = p * (‖a i‖ * ‖ζ - 1‖ ^ e) := by
        rw [hπe, mul_left_comm, mul_inv_cancel₀ (by exact_mod_cast hp.out.ne_zero), mul_one]
    _ ≤ p * ‖a i • (ζ - 1) ^ i‖ := by
        rw [norm_smul, norm_pow]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (norm_nonneg _) hπ1.le hie) (norm_nonneg _)) (by positivity)
    _ ≤ p * ‖∑ j ∈ Finset.range e with a j • (ζ - 1) ^ j ≠ 0, a j • (ζ - 1) ^ j‖ := by
        gcongr
        rw [IsUltrametricDist.norm_sum_eq_sup'_of_pairwise_ne ⟨i, hi⟩
          (TauCeti.pairwise_norm_smul_pow_ne hπe fun j hj ↦ ?_)]
        · exact Finset.le_sup' (fun j ↦ ‖a j • (ζ - 1) ^ j‖) hi
        obtain ⟨hj, hj0⟩ := Finset.mem_filter.mp hj
        exact ⟨Finset.mem_range.mp hj, fun h0 ↦ hj0 (by simp [h0])⟩

end PadicAlgCl
