/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.WeilNumber.Basic
public import TauCeti.NumberTheory.WeilNumber.IotaWeight

import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# Weil numbers and the complex embeddings of a coefficient field

A Weil `q`-number of weight `n` is sent to a complex number of absolute value `q ^ (n / 2)` by
every field embedding into `ℂ`, so it is `ι`-pure of weight `n` for every `ι`. This file compares
that all-embeddings condition with the conditions one can test on a polynomial over a coefficient
field.

Let `E` be a field algebraic over `ℚ`, such as a number field, and `P ∈ E[X]`; think of
`P` as the characteristic polynomial of a Frobenius element, or as the Hecke polynomial of an
eigenform over its coefficient field. Every root of `P` in an algebraically closed field is a Weil
`q`-number of weight `n` if and only if, for every field embedding `σ : E → ℂ`, every complex root
of `σ(P)` has absolute value `q ^ (n / 2)`. This is the form in which purity of a Frobenius
polynomial over a coefficient field is usually verified and used: one embedding at a time, with
roots counted in `ℂ`. When `P` has rational coefficients there is only one embedding of `ℚ`, and
it is enough to test all complex roots of `P` itself.

Testing a single root under a single embedding is a weaker condition. The polynomial
`X⁴ - X³ - X² - X + 1` is irreducible over `ℚ`, and its complex roots are a pair of conjugates on
the unit circle and a pair of reciprocal positive reals, one of them greater than `1`; it is the
product of `X² - tX + 1` over the two roots `t` of `t² - t - 3`. A root on
the unit circle is `ι`-pure of weight `0` for the identity embedding of `ℂ`, but it is not a Weil
number of any weight. In `ℚ[X] / (X⁴ - X³ - X² - X + 1)`, the class of `X` is `ι`-pure of weight
`0` for the embedding sending it to the unit circle and not for the one sending it to the real
root greater than `1`. These checks close the file.

## Main results

* `TauCeti.IsWeilNumber.isIotaPure`: a Weil `q`-number of weight `n` is `ι`-pure of weight `n`
  for every field embedding `ι` into `ℂ`.
* `TauCeti.isWeilNumber_iff_forall_mem_roots_map_minpoly`: an element integral over a field `E`
  algebraic over `ℚ` is a Weil `q`-number of weight `n` if and only if `1 < q` and, for every
  embedding `σ : E → ℂ`, every complex root of `σ` applied to its minimal polynomial over `E` has
  absolute value `q ^ (n / 2)`.
* `TauCeti.IsWeilNumber.of_aeval_eq_zero_of_forall_roots_map`: a root of a nonzero polynomial over
  `E` whose images under all embeddings `σ : E → ℂ` have all their roots of absolute value
  `q ^ (n / 2)` is a Weil `q`-number of weight `n`.
* `TauCeti.forall_isWeilNumber_mem_aroots_iff`: every root of `P ∈ E[X]` in an
  algebraically closed field is a Weil `q`-number of weight `n` if and only if, for every
  `σ : E → ℂ`, every complex root of `σ(P)` has absolute value `q ^ (n / 2)`.
* `TauCeti.forall_isWeilNumber_mem_aroots_iff_of_rat`: for a rational polynomial it
  suffices to test its complex roots.
* `TauCeti.irreducible_X_pow_four_sub_X_pow_three_sub_X_sq_sub_X_add_one` and
  `TauCeti.not_isWeilNumber_of_aeval_X_pow_four_sub_X_pow_three_sub_X_sq_sub_X_add_one_eq_zero`:
  the quartic above is irreducible over `ℚ`, and none of its roots, in any field, is a Weil number.

## References

* P. Deligne, *La conjecture de Weil. II*, Publ. Math. IHÉS 52 (1980), §1.2, (1.2.6).
-/

public section

open Polynomial

namespace TauCeti

variable {K : Type*} [Field K] [Algebra ℚ K] {q : ℝ} {n : ℤ}

/-- A Weil `q`-number of weight `n` is `ι`-pure of weight `n` for every field embedding `ι` into
`ℂ`. -/
theorem IsWeilNumber.isIotaPure {α : K} (h : IsWeilNumber q n α) (ι : K →+* ℂ) :
    IsIotaPure ι q n α :=
  (isIotaPure_iff_norm_apply_eq h.pos h.one_lt.ne').mpr (h.norm_apply_eq ι)

/-! ### Embeddings of a coefficient field -/

section CoefficientField

variable {E L : Type*} [Field E] [Algebra ℚ E] [Algebra.IsAlgebraic ℚ E]
  [Field L] [Algebra ℚ L] [Algebra E L]

/-- Let `E` be a field algebraic over `ℚ`. An element `α` integral over `E` is a Weil `q`-number
of weight `n` if and only if `1 < q` and, for every field embedding `σ : E → ℂ`, every complex root
of the image under `σ` of the minimal polynomial of `α` over `E` has absolute value
`q ^ (n / 2)`. For `E = ℚ` this is the definition of a Weil number. -/
theorem isWeilNumber_iff_forall_mem_roots_map_minpoly {α : L} (hα : IsIntegral E α) :
    IsWeilNumber q n α ↔ 1 < q ∧
      ∀ σ : E →+* ℂ, ∀ z ∈ ((minpoly E α).map σ).roots, ‖z‖ = q ^ ((n : ℝ) / 2) := by
  have : Fact (Irreducible (minpoly E α)) := ⟨minpoly.irreducible hα⟩
  have : Module.Finite E (AdjoinRoot (minpoly E α)) := (minpoly.monic hα).finite_adjoinRoot
  have : Algebra.IsAlgebraic ℚ (AdjoinRoot (minpoly E α)) := Algebra.IsAlgebraic.trans ℚ E _
  -- Transport the question to `AdjoinRoot (minpoly E α)`, which is algebraic over `ℚ`: its
  -- embeddings into `ℂ` are the pairs of an embedding `σ` of `E` and a root of `σ (minpoly E α)`.
  have hα' : (minpoly E α).eval₂ (algebraMap E L) α = 0 := by
    rw [← aeval_def, minpoly.aeval]
  have hroot' : IsWeilNumber q n α ↔ IsWeilNumber q n (AdjoinRoot.root (minpoly E α)) := by
    rw [← isWeilNumber_map_iff (AdjoinRoot.lift (algebraMap E L) α hα'), AdjoinRoot.lift_root]
  rw [hroot', isWeilNumber_iff_forall_norm_apply_eq]
  refine and_congr_right fun _ ↦ ⟨fun h σ z hz ↦ ?_, fun h τ ↦ h (τ.comp (algebraMap E _)) _ ?_⟩
  · have hz' : (minpoly E α).eval₂ σ z = 0 := by
      rw [eval₂_eq_eval_map]
      exact (mem_roots (Polynomial.map_ne_zero (minpoly.ne_zero hα))).mp hz
    simpa using h (AdjoinRoot.lift σ z hz')
  · rw [mem_roots (Polynomial.map_ne_zero (minpoly.ne_zero hα)), IsRoot, ← eval₂_eq_eval_map,
      ← hom_eval₂, ← aeval_def, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]

/-- Let `E` be a field algebraic over `ℚ` and `P ∈ E[X]` nonzero. If, for every field embedding
`σ : E → ℂ`, every complex root of `σ(P)` has absolute value `q ^ (n / 2)`, then every root of `P`
in a field over `E` is a Weil `q`-number of weight `n`. The polynomial need not be irreducible. -/
theorem IsWeilNumber.of_aeval_eq_zero_of_forall_roots_map {P : E[X]} (hq : 1 < q) (hP : P ≠ 0)
    {α : L} (hα : aeval α P = 0)
    (hroots : ∀ σ : E →+* ℂ, ∀ z ∈ (P.map σ).roots, ‖z‖ = q ^ ((n : ℝ) / 2)) :
    IsWeilNumber q n α := by
  have hint : IsIntegral E α := (isAlgebraic_iff_isIntegral).mp ⟨P, hP, hα⟩
  refine (isWeilNumber_iff_forall_mem_roots_map_minpoly hint).mpr ⟨hq, fun σ z hz ↦ hroots σ z ?_⟩
  exact Multiset.mem_of_le (roots.le_of_dvd (Polynomial.map_ne_zero hP)
    (Polynomial.map_dvd σ (minpoly.dvd E α hα))) hz

/-- Let `E` be a field algebraic over `ℚ`, `P ∈ E[X]` and `L` an algebraically closed field over
`E`. Every root of `P` in `L` is a Weil `q`-number of weight `n` if and only if, for
every field embedding `σ : E → ℂ`, every complex root of `σ(P)` has absolute value
`q ^ (n / 2)`. -/
theorem forall_isWeilNumber_mem_aroots_iff [IsAlgClosed L] (hq : 1 < q) (P : E[X]) :
    (∀ α ∈ P.aroots L, IsWeilNumber q n α) ↔
      ∀ σ : E →+* ℂ, ∀ z ∈ (P.map σ).roots, ‖z‖ = q ^ ((n : ℝ) / 2) := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  refine ⟨fun h σ z hz ↦ ?_, fun h α hα ↦
    IsWeilNumber.of_aeval_eq_zero_of_forall_roots_map hq hP (mem_aroots.mp hα).2 h⟩
  -- Make `ℂ` an `E`-algebra through `σ`, and pick a root `α` in `L` of the minimal polynomial of
  -- `z` over `E`; it is a root of `P` with the same minimal polynomial as `z`.
  let _ : Algebra E ℂ := σ.toAlgebra
  have hzP : aeval z P = 0 := by
    rw [aeval_def, RingHom.algebraMap_toAlgebra, eval₂_eq_eval_map]
    exact (mem_roots (Polynomial.map_ne_zero hP)).mp hz
  have hzint : IsIntegral E z := (isAlgebraic_iff_isIntegral).mp ⟨P, hP, hzP⟩
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero L (minpoly E z)
    (minpoly.degree_pos hzint).ne'
  have hmin : minpoly E z = minpoly E α :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hzint) hα (minpoly.monic hzint)
  have hαP : α ∈ P.aroots L :=
    mem_aroots.mpr ⟨hP, aeval_eq_zero_of_dvd_aeval_eq_zero (minpoly.dvd E z hzP) hα⟩
  have hαint : IsIntegral E α := (isAlgebraic_iff_isIntegral).mp ⟨P, hP, (mem_aroots.mp hαP).2⟩
  refine ((isWeilNumber_iff_forall_mem_roots_map_minpoly hαint).mp (h α hαP)).2 σ z ?_
  rw [← hmin, mem_roots (Polynomial.map_ne_zero (minpoly.ne_zero hzint)), IsRoot,
    ← eval₂_eq_eval_map, ← RingHom.algebraMap_toAlgebra σ, ← aeval_def, minpoly.aeval]

/-- Every root of a rational polynomial `P` in an algebraically closed field of
characteristic zero is a Weil `q`-number of weight `n` if and only if every complex root of `P`
has absolute value `q ^ (n / 2)`: for a rational polynomial, testing one embedding suffices. -/
theorem forall_isWeilNumber_mem_aroots_iff_of_rat [IsAlgClosed K] (hq : 1 < q) (P : ℚ[X]) :
    (∀ α ∈ P.aroots K, IsWeilNumber q n α) ↔ ∀ z ∈ P.aroots ℂ, ‖z‖ = q ^ ((n : ℝ) / 2) := by
  rw [forall_isWeilNumber_mem_aroots_iff hq P]
  exact ⟨fun h ↦ h _, fun h σ ↦ Subsingleton.elim σ (algebraMap ℚ ℂ) ▸ h⟩

end CoefficientField

/-! ### A root on the unit circle need not be a Weil number -/

/-- `X⁴ - X³ - X² - X + 1` is irreducible over `ℚ`: modulo `2` it is the fifth cyclotomic
polynomial, which is irreducible over `ZMod 2` because `2` has order `4` modulo `5`. -/
theorem irreducible_X_pow_four_sub_X_pow_three_sub_X_sq_sub_X_add_one :
    Irreducible (X ^ 4 - X ^ 3 - X ^ 2 - X + 1 : ℚ[X]) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hmonic : (X ^ 4 - X ^ 3 - X ^ 2 - X + 1 : ℤ[X]).Monic := by monicity!
  have hmod : (X ^ 4 - X ^ 3 - X ^ 2 - X + 1 : ℤ[X]).map (Int.castRingHom (ZMod 2)) =
      cyclotomic 5 (ZMod 2) := by
    rw [cyclotomic_prime, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one]
    have h2 : (2 : (ZMod 2)[X]) = 0 := by
      rw [← C_ofNat, show (2 : ZMod 2) = 0 from rfl, C_0]
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, map_X,
      Polynomial.map_one]
    linear_combination (-X - X ^ 2 - X ^ 3) * h2
  have hirr : Irreducible (cyclotomic 5 (ZMod 2)) :=
    ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (by norm_num) dvd_rfl <| by
      rw [natDegree_cyclotomic, Nat.totient_prime this.out, eq_comm,
        orderOf_eq_iff (by norm_num)]
      refine ⟨by decide, fun m hm hm0 ↦ ?_⟩
      interval_cases m <;> decide
  have := (hmonic.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp
    (Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 2)) _ hmonic (hmod ▸ hirr))
  simpa using this

/-- The quartic `X⁴ - X³ - X² - X + 1` has a complex root on the unit circle: if
`4c² - 2c - 3 = 0` with `-1 < c < 0`, then `c + i √(1 - c²)` is a root of `X² - 2cX + 1`, which
divides the quartic. -/
private theorem exists_root_norm_eq_one :
    ∃ z : ℂ, z ^ 4 - z ^ 3 - z ^ 2 - z + 1 = 0 ∧ ‖z‖ = 1 := by
  have hcont : ContinuousOn (fun c : ℝ ↦ 4 * c ^ 2 - 2 * c - 3) (Set.Icc (-1) (-1 / 2)) := by
    fun_prop
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo' (by norm_num) hcont
    (show (0 : ℝ) ∈ Set.Ioo _ _ by norm_num)
  have hc2 : 0 ≤ 1 - c ^ 2 := by nlinarith [hc.1, hc.2]
  set s := √(1 - c ^ 2)
  have hs : (s : ℂ) ^ 2 = 1 - (c : ℂ) ^ 2 := by
    exact_mod_cast Real.sq_sqrt hc2
  have hc0' : 4 * (c : ℂ) ^ 2 - 2 * c - 3 = 0 := by exact_mod_cast hc0
  set z : ℂ := c + s * Complex.I
  have hz : z ^ 2 - 2 * c * z + 1 = 0 := by
    linear_combination (s : ℂ) ^ 2 * Complex.I_sq - hs
  refine ⟨z, ?_, ?_⟩
  · linear_combination (z ^ 2 - (1 - 2 * c) * z + 1) * hz + z ^ 2 * hc0'
  · rw [Complex.norm_add_mul_I, Real.sq_sqrt hc2, add_sub_cancel, Real.sqrt_one]

/-- The quartic `X⁴ - X³ - X² - X + 1` has a real root greater than `1`, since it is negative at
`1` and positive at `2`. -/
private theorem exists_root_one_lt :
    ∃ r : ℝ, 1 < r ∧ r ^ 4 - r ^ 3 - r ^ 2 - r + 1 = 0 := by
  have hcont : ContinuousOn (fun r : ℝ ↦ r ^ 4 - r ^ 3 - r ^ 2 - r + 1) (Set.Icc 1 2) := by
    fun_prop
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo (by norm_num) hcont
    (show (0 : ℝ) ∈ Set.Ioo _ _ by norm_num)
  exact ⟨r, hr.1, hr0⟩

/-- No root of the irreducible quartic `X⁴ - X³ - X² - X + 1`, in any field of characteristic
zero, is a Weil number: among its complex conjugates are a number of absolute value `1` and a
real number greater than `1`. -/
theorem not_isWeilNumber_of_aeval_X_pow_four_sub_X_pow_three_sub_X_sq_sub_X_add_one_eq_zero
    {α : K} (hα : aeval α (X ^ 4 - X ^ 3 - X ^ 2 - X + 1 : ℚ[X]) = 0) : ¬IsWeilNumber q n α := by
  intro h
  have hmin : X ^ 4 - X ^ 3 - X ^ 2 - X + 1 = minpoly ℚ α :=
    minpoly.eq_of_irreducible_of_monic
      irreducible_X_pow_four_sub_X_pow_three_sub_X_sq_sub_X_add_one hα (by monicity!)
  have hmem : ∀ z : ℂ, z ^ 4 - z ^ 3 - z ^ 2 - z + 1 = 0 → z ∈ (minpoly ℚ α).aroots ℂ :=
    fun z hz ↦ mem_aroots.mpr ⟨minpoly.ne_zero h.isIntegral, by simp [← hmin, hz]⟩
  obtain ⟨z, hz, hz1⟩ := exists_root_norm_eq_one
  obtain ⟨r, hr1, hr⟩ := exists_root_one_lt
  have h1 := h.norm_eq_of_mem_aroots (hmem z hz)
  have h2 := h.norm_eq_of_mem_aroots (hmem r (by exact_mod_cast hr))
  rw [Complex.norm_real, Real.norm_of_nonneg (by linarith), ← h1, hz1] at h2
  exact hr1.ne' h2

/- A root `α` of `X⁴ - X³ - X² - X + 1` on the unit circle is `ι`-pure of weight `0` for the
identity embedding of `ℂ` and every admissible `q`, but it is not a Weil number of any weight:
testing a single root under a single embedding does not give purity. -/
example : ∃ α : ℂ, α ^ 4 - α ^ 3 - α ^ 2 - α + 1 = 0 ∧
    (∀ q : ℝ, 0 < q → q ≠ 1 → IsIotaPure (RingHom.id ℂ) q 0 α) ∧
    ∀ (q : ℝ) (n : ℤ), ¬IsWeilNumber q n α := by
  obtain ⟨α, hα, hα1⟩ := exists_root_norm_eq_one
  refine ⟨α, hα, fun q hq₀ hq₁ ↦ ?_, fun q n ↦
    not_isWeilNumber_of_aeval_X_pow_four_sub_X_pow_three_sub_X_sq_sub_X_add_one_eq_zero
      (by simp [hα])⟩
  rw [isIotaPure_iff_norm_apply_eq hq₀ hq₁]
  simp [hα1]

/- In `ℚ[X] / (X⁴ - X³ - X² - X + 1)`, the class of `X` is `ι`-pure of weight `0` for an
embedding sending it to the unit circle, and not for an embedding sending it to the real root
greater than `1`. -/
example (hq : 1 < q) :
    letI : Fact (Irreducible (X ^ 4 - X ^ 3 - X ^ 2 - X + 1 : ℚ[X])) :=
      ⟨irreducible_X_pow_four_sub_X_pow_three_sub_X_sq_sub_X_add_one⟩
    ∃ ι₁ ι₂ : AdjoinRoot (X ^ 4 - X ^ 3 - X ^ 2 - X + 1 : ℚ[X]) →+* ℂ,
      IsIotaPure ι₁ q 0 (AdjoinRoot.root (X ^ 4 - X ^ 3 - X ^ 2 - X + 1 : ℚ[X])) ∧
        ¬IsIotaPure ι₂ q 0 (AdjoinRoot.root (X ^ 4 - X ^ 3 - X ^ 2 - X + 1 : ℚ[X])) := by
  have : Fact (Irreducible (X ^ 4 - X ^ 3 - X ^ 2 - X + 1 : ℚ[X])) :=
    ⟨irreducible_X_pow_four_sub_X_pow_three_sub_X_sq_sub_X_add_one⟩
  obtain ⟨z, hz, hz1⟩ := exists_root_norm_eq_one
  obtain ⟨r, hr1, hr⟩ := exists_root_one_lt
  have hq₀ : 0 < q := zero_lt_one.trans hq
  refine ⟨AdjoinRoot.lift (algebraMap ℚ ℂ) z (by simp [hz]),
    AdjoinRoot.lift (algebraMap ℚ ℂ) r (by simpa using congrArg ((↑) : ℝ → ℂ) hr), ?_, ?_⟩ <;>
    rw [isIotaPure_iff_norm_apply_eq hq₀ hq.ne', AdjoinRoot.lift_root]
  · simp [hz1]
  · rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    simpa using hr1.ne'

end TauCeti
