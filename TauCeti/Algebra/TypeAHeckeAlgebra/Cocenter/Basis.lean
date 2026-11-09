/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Cocenter.Basic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Block
import TauCeti.RingTheory.MvPolynomial.Ideal
import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary

/-!
# The cycle-block words form a basis of the cocenter of a Hecke stage

Let `Hₙ` be the stage of the first `n` strands of the infinite type-A Hecke algebra over a
commutative ring `K`, with parameter `q` and `Q = q ^ 2`. The elements `ζ_λ`
(`TauCeti.InfiniteTypeAHeckeAlgebra.cycleBlock`), for `λ` a partition of `n`, span the cocenter
`Hₙ / [Hₙ, Hₙ]` (`TauCeti.InfiniteTypeAHeckeAlgebra.span_cycleBlock_sup_commutatorSubmodule`).
This file proves that their classes are linearly independent when `K` is an infinite integral
domain, `Q ≠ 1`, and the product `∏_{d=1}^{n} [d]_Q` of the `Q`-integers
`[d]_Q = 1 + Q + ⋯ + Q ^ (d - 1)` is nonzero
(`TauCeti.InfiniteTypeAHeckeAlgebra.linearIndependent_mkQ_cycleBlock`). So the classes of the
`ζ_λ` form a basis of the cocenter (`TauCeti.InfiniteTypeAHeckeAlgebra.cycleBlockCocenterBasis`),
and the cocenter has dimension the number of partitions of `n`. This applies for instance over
`ℂ` at every positive real `Q ≠ 1`, where every `[d]_Q` is positive.

The classes are separated by the atomic traces on alphabets of `n` negative letters. Such a trace,
with weights `p₁, …, pₙ`, is a trace on `Hₙ`; it is multiplicative on disjoint blocks of strands,
so its value on `ζ_λ` is the product of its values on the cycle words `ζ_(λᵢ)`. By the cycle-trace
generating identity, its value on `ζₘ`, for `m > 0`, is a universal polynomial `γₘ` evaluated at
the elementary symmetric functions `e₁, …, eₙ` of the weights. Namely `γₘ` is the polynomial in
variables `X 1, X 2, …` given by the recursion

`γₘ = [m]_Q * X m - ∑ (0 < i < m), γᵢ * X (m - i)`,

which records that `1 + (Q - 1) * ∑ (m > 0), γₘ * x ^ m` is `E (Q x) / E x` for
`E x = 1 + ∑ (k > 0), X k * x ^ k`; dividing by `Q - 1` needs `Q ≠ 1`.

So the lowest-degree part of `γₘ` is `[m]_Q * X m`, and the lowest-degree part of the product
`γ_λ = ∏ᵢ γ_(λᵢ)` is the monomial `∏ᵢ [λᵢ]_Q * X λᵢ`, of total degree the number of parts of
`λ`. Distinct partitions give distinct monomials, so the `γ_λ` are linearly independent as soon
as the `Q`-integers `[d]_Q`, `d ≤ n`, are nonzero
(`MvPolynomial.linearIndependent_of_sub_monomial_mem_pow_idealOfVars`). Finally, the elementary
symmetric functions of `n` variables are algebraically independent, and a polynomial over an
infinite domain is determined by its values, so a linear relation among the classes of the `ζ_λ`
gives the same relation among the `γ_λ`.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.linearIndependent_mkQ_cycleBlock`: the classes of the `ζ_λ`
  in the cocenter of `Hₙ` are linearly independent.
* `TauCeti.InfiniteTypeAHeckeAlgebra.cycleBlockCocenterBasis`: the basis of the cocenter of `Hₙ`
  formed by the classes of the `ζ_λ`.

## References

* M. Geck and G. Pfeiffer, *Characters of Finite Coxeter Groups and Iwahori-Hecke Algebras*,
  OUP (2000), Sections 8.2 and 8.4, for the basis of the cocenter given by the classes of the
  elements `T_w` of minimal length in the conjugacy classes.
* A. Ram, *A Frobenius formula for the characters of the Hecke algebras*, Invent. Math. 106
  (1991), 461–488, for the cycle-block words `ζ_λ`.
* Yu. A. Neretin, *Some remarks on traces on the infinite-dimensional Iwahori–Hecke algebra*,
  arXiv:2101.02133, §§1.6–1.7 and §3.1, for the product model and its cycle-trace generating
  function.
-/

public section

open Finset

namespace TauCeti

namespace TypeAHeckeAlgebra

/-! ### The universal cycle values -/

section CycleValue

variable {S : Type*} [CommRing S]

/-- The universal value of an atomic trace on the cycle word `ζₘ`, in terms of the parameter `Q`
and the coefficients `y k` of the generating polynomial of the weights:
`cycleValue Q y m = [m]_Q * y m - ∑ (i < m), cycleValue Q y i * y (m - i)`. -/
private def cycleValue (Q : S) (y : ℕ → S) (m : ℕ) : S :=
  (∑ i ∈ range m, Q ^ i) * y m - ∑ i : Fin m, cycleValue Q y i * y (m - i)
termination_by m
decreasing_by exact i.isLt

private theorem cycleValue_eq (Q : S) (y : ℕ → S) (m : ℕ) :
    cycleValue Q y m =
      (∑ i ∈ range m, Q ^ i) * y m - ∑ i ∈ range m, cycleValue Q y i * y (m - i) := by
  rw [cycleValue]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i ↦ cycleValue Q y i * y (m - i)) m

private theorem cycleValue_zero (Q : S) (y : ℕ → S) : cycleValue Q y 0 = 0 := by
  rw [cycleValue_eq]
  simp

private theorem map_cycleValue {S' : Type*} [CommRing S'] (f : S →+* S') (Q : S) (y : ℕ → S)
    (m : ℕ) : f (cycleValue Q y m) = cycleValue (f Q) (fun k ↦ f (y k)) m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [cycleValue_eq, cycleValue_eq]
    simp only [map_sub, map_mul, map_sum, map_pow]
    congr 1
    exact sum_congr rfl fun i hi ↦ by rw [ih i (mem_range.mp hi)]

/-- If a sequence `F` with `F 0 = 1` satisfies `∑ (i ≤ m), F i * y (m - i) = Q ^ m * y m` for every
`m`, where `y 0 = 1`, then `F m = (Q - 1) * cycleValue Q y m` for every `m > 0`. In terms of
generating series: if `F x * E x = E (Q x)`, then `F` is `1 + (Q - 1) * ∑ (m > 0), γₘ * x ^ m`. -/
private theorem eq_sub_one_mul_cycleValue {Q : S} {y F : ℕ → S} (hy : y 0 = 1) (hF : F 0 = 1)
    (h : ∀ m, ∑ i ∈ range (m + 1), F i * y (m - i) = Q ^ m * y m) (m : ℕ) :
    F m = (Q - 1) * cycleValue Q y m + if m = 0 then 1 else 0 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hF, cycleValue_zero]
    -- Below `m`, the terms of the sum are known.
    have hsum : ∑ i ∈ range m, F i * y (m - i) =
        ∑ i ∈ range m, ((Q - 1) * (cycleValue Q y i * y (m - i)) + if i = 0 then y m else 0) :=
      sum_congr rfl fun i hi ↦ by
        rw [ih i (mem_range.mp hi)]
        split_ifs with h0
        · subst h0
          simp [cycleValue_zero]
        · ring
    have hm' := h m
    rw [sum_range_succ, hsum, Nat.sub_self, hy, mul_one] at hm'
    simp only [sum_add_distrib, ← mul_sum, sum_ite_eq', mem_range, hm, ↓reduceIte] at hm'
    rw [cycleValue_eq]
    simp only [hm.ne', ↓reduceIte, add_zero]
    linear_combination hm' - y m * geom_sum_mul Q m

end CycleValue

/-! ### Atomic traces on negative letters -/

section Atomic

variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι] [Fintype ι]

open PowerSeries in
/-- On an alphabet of negative letters only, the atomic trace of the cycle word `ζₘ`, `m > 0`, is
the universal cycle value at the elementary symmetric functions of the weights. -/
private theorem atomicTrace_cycleWord_eq_cycleValue (q : Rˣ)
    (hq : IsLeftRegular ((q : R) ^ 2 - 1)) (p : ι → R) {m : ℕ} (hm : 0 < m) :
    atomicTrace (fun _ ↦ False) q p m (cycleWord q m) =
      cycleValue ((q : R) ^ 2) (fun k ↦ (univ.val.map p).esymm k) m := by
  have hgen := atomicTrace_cycleWord_generating_function (fun _ : ι ↦ False) q p
  simp only [↓reduceIte] at hgen
  -- Scaling the weights by `q ^ 2` scales the `k`-th elementary symmetric function by `q ^ (2 k)`.
  have hscale (k : ℕ) : (univ.val.map fun a ↦ (q : R) ^ 2 * p a).esymm k =
      ((q : R) ^ 2) ^ k * (univ.val.map p).esymm k := by
    rw [← smul_eq_mul, Multiset.pow_smul_esymm, Multiset.map_map]
    simp only [Function.comp_def, smul_eq_mul]
  have h := eq_sub_one_mul_cycleValue (Q := (q : R) ^ 2) (y := fun k ↦ (univ.val.map p).esymm k)
    (F := fun i ↦ if i = 0 then 1 else ((q : R) ^ 2 - 1) * atomicTrace (fun _ ↦ False) q p i
      (cycleWord q i)) (by simp) (by simp) (fun m ↦ ?_) m
  · simp only [hm.ne', ↓reduceIte, add_zero] at h
    exact hq h
  · have hcoeff := congrArg (coeff m) hgen
    rw [← mk_multiset_esymm_eq_prod_one_add_X p,
      ← mk_multiset_esymm_eq_prod_one_add_X fun a ↦ (q : R) ^ 2 * p a, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff_mk, hscale] at hcoeff
    simpa only [coeff_mk] using hcoeff

end Atomic

/-! ### The universal cycle values are linearly independent -/

section Polynomial

open MvPolynomial

variable {K : Type*} [CommRing K]

/-- The universal cycle values have no constant term. -/
private theorem cycleValue_C_X_mem_idealOfVars (Q : K) (m : ℕ) :
    cycleValue (C Q) X m ∈ idealOfVars ℕ K := by
  rw [cycleValue_eq]
  exact sub_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨m, rfl⟩))
    (sum_mem fun i _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩))

/-- The lowest-degree part of the universal cycle value `γₘ` is `[m]_Q * X m`. -/
private theorem cycleValue_C_X_sub_mem (Q : K) (m : ℕ) :
    cycleValue (C Q) X m - C (∑ i ∈ range m, Q ^ i) * X m ∈ idealOfVars ℕ K ^ 2 := by
  rw [cycleValue_eq, show (∑ i ∈ range m, C Q ^ i : MvPolynomial ℕ K) =
      C (∑ i ∈ range m, Q ^ i) by simp [map_sum], sub_sub_cancel_left, pow_two]
  exact neg_mem (sum_mem fun i _ ↦
    Ideal.mul_mem_mul (cycleValue_C_X_mem_idealOfVars Q i) (Ideal.subset_span ⟨_, rfl⟩))

/-- The lowest-degree part of a product `γ_λ = ∏ᵢ γ_(λᵢ)` of universal cycle values is
`∏ᵢ [λᵢ]_Q * X λᵢ`, of total degree the number of factors. -/
private theorem prod_cycleValue_C_X_mem (Q : K) (l : Multiset ℕ) :
    (l.map (cycleValue (C Q) X)).prod ∈ idealOfVars ℕ K ^ Multiset.card l ∧
      (l.map (cycleValue (C Q) X)).prod -
          C (l.map fun m ↦ ∑ i ∈ range m, Q ^ i).prod * (l.map X).prod ∈
        idealOfVars ℕ K ^ (Multiset.card l + 1) := by
  induction l using Multiset.induction_on with
  | empty => simp
  | cons a l ih =>
    obtain ⟨h₁, h₂⟩ := ih
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, map_mul]
    set Γ := (l.map (cycleValue (C Q) X)).prod
    set Y := (l.map (X (R := K))).prod
    set κ := C (l.map fun m ↦ ∑ i ∈ range m, Q ^ i).prod
    refine ⟨by rw [pow_succ']; exact Ideal.mul_mem_mul (cycleValue_C_X_mem_idealOfVars Q a) h₁, ?_⟩
    have hA : (cycleValue (C Q) X a - C (∑ i ∈ range a, Q ^ i) * X a) * Γ ∈
        idealOfVars ℕ K ^ (Multiset.card l + 1 + 1) := by
      rw [show Multiset.card l + 1 + 1 = 2 + Multiset.card l by omega, pow_add]
      exact Ideal.mul_mem_mul (cycleValue_C_X_sub_mem Q a) h₁
    have hB : C (∑ i ∈ range a, Q ^ i) * X a * (Γ - κ * Y) ∈
        idealOfVars ℕ K ^ (Multiset.card l + 1 + 1) := by
      rw [pow_succ']
      exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨a, rfl⟩)) h₂
    convert add_mem hA hB using 1
    ring

/-- The products `γ_λ = ∏ᵢ γ_(λᵢ)` of universal cycle values over the partitions `λ` of `n` are
linearly independent as soon as the `Q`-integers `[d]_Q`, `1 ≤ d ≤ n`, are nonzero. -/
private theorem linearIndependent_prod_cycleValue [IsDomain K] {Q : K} {n : ℕ}
    (hprod : ∏ d ∈ Icc 1 n, ∑ i ∈ range d, Q ^ i ≠ 0) :
    LinearIndependent K fun μ : n.Partition ↦ (μ.parts.map (cycleValue (C Q) X)).prod := by
  -- The product of the variables in a multiset `l` is the monomial `Multiset.toFinsupp l`, whose
  -- total degree is the cardinality of `l`.
  have hX (l : Multiset ℕ) :
      (l.map X).prod = (monomial (Multiset.toFinsupp l) 1 : MvPolynomial ℕ K) := by
    induction l using Multiset.induction_on with
    | empty => simp
    | cons a l ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, ih, ← Multiset.singleton_add,
        Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, monomial_single_add, pow_one]
  have hdeg (l : Multiset ℕ) : (Multiset.toFinsupp l).degree = Multiset.card l := by
    induction l using Multiset.induction_on with
    | empty => simp
    | cons a l ih =>
      rw [← Multiset.singleton_add, Multiset.toFinsupp_add, map_add, Multiset.toFinsupp_singleton,
        Finsupp.degree_single, ih, Multiset.card_add, Multiset.card_singleton, add_comm]
  refine linearIndependent_of_sub_monomial_mem_pow_idealOfVars
    (s := fun μ : n.Partition ↦ Multiset.toFinsupp μ.parts)
    (c := fun μ ↦ (μ.parts.map fun m ↦ ∑ i ∈ range m, Q ^ i).prod)
    (fun μ ν h ↦ Nat.Partition.ext (Multiset.toFinsupp.injective h)) (fun μ ↦ ?_) (fun μ ↦ ?_)
  · refine Multiset.prod_ne_zero fun h0 ↦ ?_
    obtain ⟨m, hm, hm0⟩ := Multiset.mem_map.mp h0
    exact prod_ne_zero_iff.mp hprod m (mem_Icc.mpr ⟨μ.parts_pos hm, μ.le_of_mem_parts hm⟩) hm0
  · have hmono : monomial (Multiset.toFinsupp μ.parts)
        (μ.parts.map fun m ↦ ∑ i ∈ range m, Q ^ i).prod =
          C (μ.parts.map fun m ↦ ∑ i ∈ range m, Q ^ i).prod * (μ.parts.map (X (R := K))).prod := by
      rw [hX, C_mul_monomial, mul_one]
    rw [hdeg, hmono]
    exact (prod_cycleValue_C_X_mem Q μ.parts).2

/-- The universal cycle values `γₘ`, `m ≤ n`, only involve the variables `X 1, …, X n`. -/
private theorem cycleValue_C_X_mem_supported [Nontrivial K] (Q : K) {n : ℕ} :
    ∀ m ≤ n, cycleValue (C Q) X m ∈ supported K (Set.Icc 1 n) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [cycleValue_zero]
      exact zero_mem _
    rw [cycleValue_eq]
    refine sub_mem (mul_mem (sum_mem fun i _ ↦ pow_mem ?_ _) (X_mem_supported.mpr ⟨hm, hmn⟩))
      (sum_mem fun i hi ↦ mul_mem (ih i (mem_range.mp hi) (by grind)) ?_)
    · simpa [MvPolynomial.algebraMap_eq] using (supported K (Set.Icc 1 n)).algebraMap_mem Q
    · exact X_mem_supported.mpr ⟨by grind, by omega⟩

/-- A polynomial in the variables `X 1, …, X n` over an infinite domain vanishes as soon as it
vanishes after substituting, for every `p : Fin n → K`, the elementary symmetric functions of the
`p i` for the variables. -/
private theorem eq_zero_of_aeval_esymm_eq_zero [IsDomain K] [Infinite K] {n : ℕ}
    {P : MvPolynomial ℕ K} (hP : P ∈ supported K (Set.Icc 1 n))
    (h : ∀ p : Fin n → K, aeval (fun k ↦ (univ.val.map p).esymm k) P = 0) : P = 0 := by
  obtain ⟨P', rfl⟩ := exists_rename_eq_of_vars_subset_range P (fun i : Fin n ↦ (i : ℕ) + 1)
    (fun i j hij ↦ Fin.ext (by simpa using hij)) fun k hk ↦ by
      obtain ⟨hk₁, hk₂⟩ := mem_supported.mp hP hk
      exact ⟨⟨k - 1, by omega⟩, by simp only; omega⟩
  -- Substituting the elementary symmetric polynomials gives the zero polynomial.
  have hzero : (esymmAlgHom (Fin n) K n P' : MvPolynomial (Fin n) K) = 0 := by
    rw [esymmAlgHom_apply]
    refine MvPolynomial.funext fun p ↦ ?_
    rw [map_zero, ← h p, aeval_rename, ← aeval_eq_eval, ← AlgHom.comp_apply, comp_aeval]
    simp [Function.comp_def, aeval_esymm_eq_multiset_esymm]
  rw [esymmAlgHom_fin_injective K le_rfl
    (show esymmAlgHom (Fin n) K n P' = esymmAlgHom (Fin n) K n 0 by
      rw [map_zero]
      exact Subtype.ext hzero), map_zero]

end Polynomial

end TypeAHeckeAlgebra

namespace InfiniteTypeAHeckeAlgebra

open TypeAHeckeAlgebra MvPolynomial

variable {K : Type*} [CommRing K] [IsDomain K] [Infinite K] {q : Kˣ} {n : ℕ}

/-- **The classes of the elements `ζ_λ` in the cocenter are linearly independent.** Over an
infinite integral domain, if `Q = q ^ 2` is not `1` and the product `∏_{d=1}^{n} [d]_Q` of the
`Q`-integers `[d]_Q = 1 + Q + ⋯ + Q ^ (d - 1)` is nonzero, then the classes of the elements
`ζ_λ`, for `λ` a partition of `n`, in the cocenter of the stage of the first `n` strands are
linearly independent. -/
theorem linearIndependent_mkQ_cycleBlock (hQ : (q : K) ^ 2 ≠ 1)
    (hprod : ∏ d ∈ Icc 1 n, ∑ i ∈ range d, ((q : K) ^ 2) ^ i ≠ 0) :
    LinearIndependent K fun μ : n.Partition ↦
      (commutatorSubmodule K (stage K q n)).mkQ ⟨cycleBlock q μ, cycleBlock_mem_stage μ⟩ := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hmem : ∑ μ, g μ • (⟨cycleBlock q μ, cycleBlock_mem_stage μ⟩ : stage K q n) ∈
      commutatorSubmodule K (stage K q n) := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum]
    simpa only [map_smul] using hg
  have hreg : IsLeftRegular ((q : K) ^ 2 - 1) := fun _ _ h ↦ mul_left_cancel₀ (sub_ne_zero.mpr hQ) h
  -- Every atomic trace on `n` negative letters kills the combination of the `ζ_λ`, which
  -- evaluates the same combination of the universal cycle values.
  have heval (p : Fin n → K) : aeval (fun k ↦ (univ.val.map p).esymm k)
      (∑ μ, g μ • (μ.parts.map (cycleValue (C ((q : K) ^ 2)) X)).prod) = 0 := by
    let ψ : stage K q n →ₗ[K] K :=
      atomicTrace (fun _ : Fin n ↦ False) q p n ∘ₗ (stageEquiv K q n).symm.toLinearMap
    have hψ := (commutatorSubmodule_le_ker_iff ψ).mpr
      (fun x y ↦ by simp [ψ, atomicTrace_mul_comm]) hmem
    rw [LinearMap.mem_ker, map_sum] at hψ
    rw [← hψ, map_sum]
    refine sum_congr rfl fun μ _ ↦ ?_
    simp only [map_smul, ψ, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      apply_stageEquiv_symm_cycleBlock (fun _ _ ↦ atomicTrace_castAdd_mul_natAdd _ q p),
      atomicTrace_one, pow_zero, one_mul, map_multiset_prod, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun m hm ↦ ?_
    have := map_cycleValue (aeval fun k ↦ (univ.val.map p).esymm k).toRingHom (C ((q : K) ^ 2))
      X m
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, aeval_X,
      Algebra.algebraMap_self, RingHom.id_apply] at this
    rw [Function.comp_apply, this, atomicTrace_cycleWord_eq_cycleValue q hreg p (μ.parts_pos hm)]
  have hpoly := eq_zero_of_aeval_esymm_eq_zero (n := n)
    (sum_mem fun μ _ ↦ Subalgebra.smul_mem _ (Subalgebra.multiset_prod_mem _ fun x hx ↦ by
      obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.mp hx
      exact cycleValue_C_X_mem_supported _ m (μ.le_of_mem_parts hm)) _) heval
  exact Fintype.linearIndependent_iff.mp (linearIndependent_prod_cycleValue hprod) g hpoly

/-- **The cycle-block basis of the cocenter.** Over an infinite integral domain, if `Q = q ^ 2` is
not `1` and `∏_{d=1}^{n} [d]_Q` is nonzero, the classes of the elements `ζ_λ`, for `λ` a partition
of `n`, form a basis of the cocenter `Hₙ / [Hₙ, Hₙ]` of the stage of the first `n` strands. -/
noncomputable def cycleBlockCocenterBasis (hQ : (q : K) ^ 2 ≠ 1)
    (hprod : ∏ d ∈ Icc 1 n, ∑ i ∈ range d, ((q : K) ^ 2) ^ i ≠ 0) :
    Module.Basis n.Partition K (cyclicQuotient K (stage K q n)) :=
  .mk (linearIndependent_mkQ_cycleBlock hQ hprod) <| by
    have h := span_cycleBlock_sup_commutatorSubmodule (R := K) (q := q) n
    rw [sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp] at h
    exact h.ge

/-- The basis vector of `cycleBlockCocenterBasis` at `λ` is the class of `ζ_λ`. -/
@[simp]
theorem cycleBlockCocenterBasis_apply (hQ : (q : K) ^ 2 ≠ 1)
    (hprod : ∏ d ∈ Icc 1 n, ∑ i ∈ range d, ((q : K) ^ 2) ^ i ≠ 0) (μ : n.Partition) :
    cycleBlockCocenterBasis hQ hprod μ =
      (commutatorSubmodule K (stage K q n)).mkQ ⟨cycleBlock q μ, cycleBlock_mem_stage μ⟩ :=
  Module.Basis.mk_apply _ _ _

end InfiniteTypeAHeckeAlgebra

end TauCeti
