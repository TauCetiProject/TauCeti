/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Separating one variable of a multivariate polynomial

Over a field `K`, every polynomial `P ∈ K[X_σ]` can be written, for a chosen variable `Xᵢ`, as

`P = ∑_{k < m} fₖ · gₖ(Xᵢ)`

where the `fₖ` do not involve `Xᵢ`, the `gₖ` are one-variable polynomials, both families are
linearly independent over `K`, and `m ≤ deg_{Xᵢ} P + 1`. Moreover the `fₖ` have partial degrees
at most those of `P` and the `gₖ` have degree at most `deg_{Xᵢ} P`.

This is the separation of variables in the proof of Roth's lemma: for rows `D k` that do not
differentiate in `Xᵢ`, the determinant of the Hasse derivatives `∂^(D k + l eᵢ) P` factors as the
generalized Wronskian of the `fₖ` times the one-variable Wronskian of the `gₖ`
(`MvPolynomial.det_hasseDeriv_sum_mul_toMvPolynomial`). Over a field of characteristic zero, the
linear independence of the `fₖ` gives admissible rows `D` with `W_D(f) ≠ 0`, and the linear
independence of the `gₖ` makes their Hasse Wronskian nonzero.

## Main results

* `MvPolynomial.exists_eq_sum_mul_X_pow`: the expansion `P = ∑_{j ≤ deg_{Xᵢ} P} Qⱼ · Xᵢ ^ j` with
  coefficients `Qⱼ` free of `Xᵢ`, over any commutative semiring.
* `MvPolynomial.exists_sum_mul_linearIndependent`: the separated expression of `P` in the
  variable `Xᵢ`, with both families linearly independent.

## Implementation notes

Write `P = ∑_{j ≤ N} Qⱼ Xᵢ ^ j` with `Qⱼ` free of `Xᵢ`, where `N = deg_{Xᵢ} P`. The `fₖ` are a basis
of the span of the `Qⱼ`, and `gₖ = ∑ⱼ cⱼₖ X ^ j` (built with `Polynomial.ofFn`) where `cⱼₖ` is the
`k`-th coordinate of `Qⱼ`. A
linear relation among the `gₖ` gives a linear form on the span vanishing on every `Qⱼ`, hence
identically, which forces the relation to be trivial.

## References

* L. Pottmeyer, *Diophantine Approximation*, lecture notes (version of 17 January 2022), §3.3,
  Lemma 3.3.8.
-/

public section

namespace MvPolynomial

open Finset Module

variable {R K σ : Type*} [CommSemiring R] [Field K]

/-- Expansion of `P` in powers of the variable `Xᵢ`: `P = ∑_{j ≤ deg_{Xᵢ} P} Qⱼ · Xᵢ ^ j`, where
the coefficients `Qⱼ` do not involve `Xᵢ` and have partial degrees at most those of `P`. -/
theorem exists_eq_sum_mul_X_pow (P : MvPolynomial σ R) (i : σ) :
    ∃ Q : ℕ → MvPolynomial σ R, (∀ j, i ∉ (Q j).vars ∧ ∀ k, (Q j).degreeOf k ≤ P.degreeOf k) ∧
      P = ∑ j ∈ range (P.degreeOf i + 1), Q j * X i ^ j := by
  classical
  -- `Qⱼ` collects the monomials of `P` of degree `j` in `Xᵢ`, with `Xᵢ` removed.
  set Q : ℕ → MvPolynomial σ R := fun j ↦
    ∑ x ∈ P.support with x i = j, monomial (x.erase i) (P.coeff x)
  have hQ (j : ℕ) {d : σ →₀ ℕ} (hd : d ∈ (Q j).support) : d i = 0 ∧ ∀ k, d k ≤ P.degreeOf k := by
    obtain ⟨x, hx, hd⟩ := mem_biUnion.1 (support_sum hd)
    rw [mem_singleton.1 (support_monomial_subset hd)]
    refine ⟨Finsupp.erase_same, fun k ↦ (Finsupp.erase_apply ..).trans_le ?_⟩
    split_ifs
    · exact Nat.zero_le _
    · exact monomial_le_degreeOf k (mem_filter.1 hx).1
  refine ⟨Q, fun j ↦ ⟨fun hi ↦ ?_, fun k ↦ degreeOf_le_iff.2 fun d hd ↦ (hQ j hd).2 k⟩, ?_⟩
  · obtain ⟨d, hd, hid⟩ := (mem_vars_iff_mem_support i).1 hi
    exact Finsupp.mem_support_iff.1 hid (hQ j hd).1
  · conv_lhs => rw [P.as_sum,
      ← sum_fiberwise_of_maps_to (g := fun x ↦ x i) (t := range (P.degreeOf i + 1))
        fun x hx ↦ mem_range_succ_iff.2 (monomial_le_degreeOf i hx)]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [sum_mul]
    refine sum_congr rfl fun x hx ↦ ?_
    rw [← (mem_filter.1 hx).2, X_pow_eq_monomial, monomial_mul_monomial, mul_one,
      Finsupp.erase_add_single]

/-- **Separation of one variable** (Pottmeyer, Lemma 3.3.8). Over a field, a polynomial `P` is a
sum `∑_{k < m} fₖ · gₖ(Xᵢ)` of `m ≤ deg_{Xᵢ} P + 1` products, where the `fₖ` are linearly
independent and do not involve `Xᵢ`, and the `gₖ` are linearly independent one-variable
polynomials. The `fₖ` have partial degrees at most those of `P`, and the `gₖ` have degree at most
`deg_{Xᵢ} P`. -/
theorem exists_sum_mul_linearIndependent (P : MvPolynomial σ K) (i : σ) :
    ∃ m ≤ P.degreeOf i + 1, ∃ (f : Fin m → MvPolynomial σ K) (g : Fin m → Polynomial K),
      LinearIndependent K f ∧ LinearIndependent K g ∧ (∀ k, i ∉ (f k).vars) ∧
        (∀ k j, (f k).degreeOf j ≤ P.degreeOf j) ∧ (∀ k, (g k).natDegree ≤ P.degreeOf i) ∧
          P = ∑ k, f k * (g k).toMvPolynomial i := by
  classical
  set N := P.degreeOf i
  obtain ⟨Q, hQ, hPQ⟩ := exists_eq_sum_mul_X_pow P i
  rw [← Fin.sum_univ_eq_sum_range (fun j ↦ Q j * X i ^ j)] at hPQ
  -- Every `Qⱼ` is supported on exponents with no `Xᵢ` and partial degrees bounded by `P`.
  set S : Set (σ →₀ ℕ) := {x | x i = 0 ∧ ∀ j, x j ≤ P.degreeOf j}
  have hQS (j : ℕ) : Q j ∈ restrictSupport K S :=
    (mem_restrictSupport_iff K).2 fun x hx ↦ ⟨mem_support_notMem_vars_zero hx (hQ j).1,
      fun k ↦ (monomial_le_degreeOf k hx).trans ((hQ j).2 k)⟩
  set V := Submodule.span K (Set.range fun j : Fin (N + 1) ↦ Q j)
  have hVS : V ≤ restrictSupport K S := Submodule.span_le.2 (Set.range_subset_iff.2 fun j ↦ hQS j)
  have : Module.Finite K V := Module.Finite.span_of_finite K (Set.finite_range _)
  set b := Module.finBasis K V
  -- The coordinates `cⱼₖ` of `Qⱼ` in the basis `b`, and the one-variable polynomials `gₖ`.
  set c : Fin (N + 1) → Fin (finrank K V) → K := fun j ↦
    b.repr ⟨Q j, Submodule.subset_span (Set.mem_range_self j)⟩
  set g : Fin (finrank K V) → Polynomial K := fun k ↦ Polynomial.ofFn (N + 1) fun j ↦ c j k
    with hg_def
  have hQb (j : Fin (N + 1)) : Q j = ∑ k, c j k • (b k : MvPolynomial σ K) := by
    have := congr_arg Subtype.val (b.sum_repr ⟨Q j, Submodule.subset_span (Set.mem_range_self j)⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  have hbS (k : Fin (finrank K V)) {x : σ →₀ ℕ} (hx : x ∈ (b k : MvPolynomial σ K).support) :
      x ∈ S :=
    (mem_restrictSupport_iff K).1 (hVS (b k).2) hx
  refine ⟨finrank K V, (finrank_range_le_card _).trans (by simp [N]), fun k ↦ b k, g,
    b.linearIndependent.map' V.subtype V.ker_subtype, ?_, fun k hk ↦ ?_, fun k j ↦ ?_,
    fun k ↦ ?_, ?_⟩
  · -- A relation `∑ₖ aₖ gₖ = 0` gives the linear form `∑ₖ aₖ cₖ` vanishing on each `Qⱼ`.
    refine Fintype.linearIndependent_iff.2 fun a ha k ↦ ?_
    set φ : V →ₗ[K] K := ∑ k, a k • b.coord k
    have hφQ (j : Fin (N + 1)) : ∑ k, a k * c j k = 0 := by
      have hac : ∑ k, a k • (fun j ↦ c j k) = 0 :=
        Polynomial.injective_ofFn (N + 1) (by simpa [hg_def, map_sum] using ha)
      simpa using congr_fun hac j
    have hφ (x : MvPolynomial σ K) (hx : x ∈ V) : φ ⟨x, hx⟩ = 0 := by
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        simpa [φ, c, mul_comm] using hφQ j
      | zero => exact map_zero φ
      | add x y hx hy hφx hφy =>
        exact (map_add φ ⟨x, hx⟩ ⟨y, hy⟩).trans (by rw [hφx, hφy, add_zero])
      | smul r x hx hφx => exact (map_smul φ r ⟨x, hx⟩).trans (by rw [hφx, smul_zero])
    simpa [φ, Finsupp.single_apply] using hφ _ (b k).2
  · obtain ⟨x, hx, hix⟩ := (mem_vars_iff_mem_support i).1 hk
    exact Finsupp.mem_support_iff.1 hix (hbS k hx).1
  · exact degreeOf_le_iff.2 fun x hx ↦ (hbS k hx).2 j
  · exact Nat.lt_succ_iff.1 (Polynomial.ofFn_natDegree_lt N.succ_pos _)
  · rw [hPQ]
    simp only [hQb, hg_def, Polynomial.ofFn_eq_sum_monomial, ← Polynomial.C_mul_X_pow_eq_monomial,
      map_sum, map_mul, map_pow, Polynomial.toMvPolynomial_C, Polynomial.toMvPolynomial_X, sum_mul,
      mul_sum, smul_eq_C_mul]
    rw [sum_comm]
    refine sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ ?_
    ring

end MvPolynomial
