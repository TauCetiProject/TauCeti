/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.TemperleyLieb.Positivity
import TauCeti.Algebra.TemperleyLieb.Trace.Radical
import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Regression examples: Temperley–Lieb trace positivity and boundary regimes

These examples exercise `TauCeti.TemperleyLieb.jonesLoopParameters`, bounded-depth trace
positivity, and trace radicals across the boundary parameter regimes:

* at `δ = 1 / 2` (`0 < δ < 1`), the first bad level is `2` and the two-strand Jones–Wenzl
  idempotent `1 - 2 • e 0` has trace `-3 / 4 < 0`;
* at `δ = 0`, every complex Markov trace is positive semidefinite even though `0` is not in
  `jonesLoopParameters`, whereas negative real parameters fail positivity on one strand and `-1`
  witnesses why `0 < δ` is needed in the normalized pullback criterion;
* in the open gap `1 < δ < √2`, positivity holds on `0`, `1`, and `2` strands and fails from `3`
  strands onward;
* at `δ = √2` (`2 cos (π / 4)`), every level is positive semidefinite while the nonzero
  three-strand Jones–Wenzl projection lies in the trace radical;
* at `δ = 1` (`2 cos (π / 3)`), the two-strand Jones–Wenzl projection `1 - e 0` lies in the trace
  radical but not in the Jacobson radical;
* on two strands over any commutative ring, `1 - δ • e 0` is idempotent iff `δ ^ 3 = δ`, in
  contrast to Wenzl's `1 - δ⁻¹ • e 0`.
-/

namespace TauCeti.TemperleyLiebPositivityExamples

open Real TauCeti TauCeti.TemperleyLieb
open scoped ComplexOrder

/-! ### Inadmissible parameter `δ = 1 / 2`: first bad level `2` -/

-- `1 / 2` lies below `1 = 2 cos (π / 3)` and has first bad level `2`.
example : (1 / 2 : ℝ) ∉ jonesLoopParameters ∧ ⌊π / arccos ((1 / 2 : ℝ) / 2)⌋₊ = 2 :=
  ⟨notMem_jonesLoopParameters_of_lt_one (by norm_num),
    floor_pi_div_arccos_eq (by omega)
      (by rw [Nat.cast_ofNat, cos_pi_div_two]; norm_num)
      (by norm_num [cos_pi_div_three])⟩

-- At `δ = 1 / 2`, a Markov trace is positive semidefinite on `n` strands iff `n < 2`.
example [Fact (IsSelfAdjoint ((1 / 2 : ℝ) : ℂ))]
    {tr : ∀ n : ℕ, TemperleyLieb ℂ ((1 / 2 : ℝ) : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ ((1 / 2 : ℝ) : ℂ) tr) (n : ℕ) :
    (∀ x : TemperleyLieb ℂ ((1 / 2 : ℝ) : ℂ) n, 0 ≤ tr n (star x * x)) ↔ n < 2 := by
  have hJ : (1 / 2 : ℝ) ∉ jonesLoopParameters :=
    notMem_jonesLoopParameters_of_lt_one (by norm_num)
  have hfl : ⌊π / arccos ((1 / 2 : ℝ) / 2)⌋₊ = 2 :=
    floor_pi_div_arccos_eq (by omega)
      (by rw [Nat.cast_ofNat, cos_pi_div_two]; norm_num)
      (by norm_num [cos_pi_div_three])
  rw [htr.forall_map_star_mul_self_nonneg_iff_lt_floor (by norm_num) hJ, hfl]

-- At `δ = 1 / 2`, `f₂ = 1 - 2 • e 0` has negative trace `-3 / 4`.
example [Fact (IsSelfAdjoint ((1 / 2 : ℝ) : ℂ))]
    {tr : ∀ n : ℕ, TemperleyLieb ℂ ((1 / 2 : ℝ) : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ ((1 / 2 : ℝ) : ℂ) tr) :
    jonesWenzl ((1 / 2 : ℝ) : ℂ) 2 = 1 - (2 : ℂ) • e ((1 / 2 : ℝ) : ℂ) 0 ∧
      tr 2 (star (jonesWenzl ((1 / 2 : ℝ) : ℂ) 2) * jonesWenzl ((1 / 2 : ℝ) : ℂ) 2) =
        (-3 / 4 : ℂ) := by
  have hinv : Ring.inverse ((1 / 2 : ℝ) : ℂ) = 2 := by
    push_cast
    rw [Ring.inverse_eq_inv]
    norm_num
  have hunit : ∀ k ∈ Finset.Icc 1 2, IsUnit (qInt ℂ ((1 / 2 : ℝ) : ℂ) k) := by
    intro k hk
    rcases Finset.mem_Icc.1 hk with ⟨hk1, hk2⟩
    interval_cases k
    · simp
    · simp only [qInt_two]
      exact Ne.isUnit (by norm_num)
  refine ⟨by rw [jonesWenzl_two, hinv], ?_⟩
  rw [htr.map_star_jonesWenzl_mul_jonesWenzl hunit, qInt_add_two, qInt_two, qInt_one]
  push_cast
  norm_num

/-! ### Degenerate and negative parameters: `δ = 0` and `δ = -1` -/

-- At `δ = 0` (`q = i`), the spin-model trace is positive semidefinite on all strands despite
-- `0 ∉ jonesLoopParameters`.
example :
    let _ : Fact (IsSelfAdjoint ((0 : ℝ) : ℂ)) := ⟨Complex.conj_ofReal 0⟩
    (0 : ℝ) ∉ jonesLoopParameters ∧
      ∀ (n : ℕ) (x : TemperleyLieb ℂ ((0 : ℝ) : ℂ) n),
        0 ≤ markovTrace (Units.mk0 Complex.I Complex.I_ne_zero) (by simp) (star x * x) := by
  intro _
  let qI : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero
  exact ⟨zero_notMem_jonesLoopParameters, fun n x ↦
    (isMarkovTrace_markovTrace qI (by simp [qI])).map_star_mul_self_nonneg_of_eq_zero
      Complex.ofReal_zero n x⟩

-- At `δ = -1`, the unital star characters sending every generator to `-1` pull back the positive
-- identity state on `ℂ` to the normalized Markov trace `(-1)⁻ⁿ tr n`, showing that `0 < δ` cannot
-- be omitted from the normalized pullback admissibility criterion.
example :
    let _ : Fact (IsSelfAdjoint ((-1 : ℝ) : ℂ)) := ⟨Complex.conj_ofReal (-1)⟩
    ∃ (ρ : ∀ n : ℕ, TemperleyLieb ℂ ((-1 : ℝ) : ℂ) n →⋆ₐ[ℂ] ℂ)
      (φ : StarPositiveFunctional ℂ)
      (tr : ∀ n : ℕ, TemperleyLieb ℂ ((-1 : ℝ) : ℂ) n →ₗ[ℂ] ℂ),
      IsMarkovTrace ℂ ((-1 : ℝ) : ℂ) tr ∧
      (∀ n x, φ (ρ n x) = ((-1 : ℝ) : ℂ)⁻¹ ^ n * tr n x) ∧
      (-1 : ℝ) ∉ jonesLoopParameters := by
  intro _
  obtain ⟨ρAlg, hρAlg⟩ :
      ∃ f : ∀ n : ℕ, TemperleyLieb ℂ ((-1 : ℝ) : ℂ) n →ₐ[ℂ] ℂ,
        ∀ (n : ℕ) (i : Fin (n - 1)), f n (e ((-1 : ℝ) : ℂ) i) = -1 :=
    ⟨fun n ↦ TemperleyLieb.lift (fun _ ↦ (-1 : ℂ))
      (fun _ ↦ by push_cast; norm_num) (fun _ ↦ by norm_num) (fun _ ↦ Commute.refl _),
      fun n i ↦ TemperleyLieb.lift_e _ _ _ _ i⟩
  let ρ (n : ℕ) : TemperleyLieb ℂ ((-1 : ℝ) : ℂ) n →⋆ₐ[ℂ] ℂ :=
    { ρAlg n with
      map_star' := map_star_iff.2 fun i ↦ by simp [hρAlg, IsSelfAdjoint] }
  let φ : StarPositiveFunctional ℂ :=
    { toLinearMap := LinearMap.id
      square_nonneg := star_mul_self_nonneg }
  let tr (n : ℕ) : TemperleyLieb ℂ ((-1 : ℝ) : ℂ) n →ₗ[ℂ] ℂ :=
    ((-1 : ℂ) ^ n) • (ρAlg n).toLinearMap
  have hstrand (n : ℕ) (x : TemperleyLieb ℂ ((-1 : ℝ) : ℂ) (n + 1)) :
      ρAlg (n + 2) (strandIncl x) = ρAlg (n + 1) x := by
    have hcomp : (ρAlg (n + 2)).comp strandIncl = ρAlg (n + 1) :=
      TemperleyLieb.hom_ext fun i ↦ by simp [hρAlg]
    exact AlgHom.congr_fun hcomp x
  have htr : IsMarkovTrace ℂ ((-1 : ℝ) : ℂ) tr :=
    { map_one := fun n ↦ by simp [tr]
      map_mul_comm := fun n x y ↦ by simp [tr, mul_comm]
      map_strandIncl := fun n x ↦ by
        simp only [tr, LinearMap.smul_apply, AlgHom.toLinearMap_apply, hstrand, smul_eq_mul]
        push_cast
        ring
      map_strandIncl_mul_e_last := fun n x ↦ by
        simp only [tr, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_mul, hstrand,
          smul_eq_mul, hρAlg]
        ring }
  refine ⟨ρ, φ, tr, htr, fun n x ↦ ?_, notMem_jonesLoopParameters_of_lt_one (by norm_num)⟩
  have hρ (x : TemperleyLieb ℂ ((-1 : ℝ) : ℂ) n) : ρ n x = ρAlg n x := rfl
  have hφ (z : ℂ) : φ z = z := rfl
  rw [hφ, hρ]
  simp only [tr, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_mul]
  push_cast
  rw [← mul_assoc, ← mul_pow]
  norm_num

/-! ### Open gap `1 < δ < √2`: first bad level `3` -/

-- Throughout `1 < δ < √2`, positivity holds on `0`, `1`, and `2` strands and fails from `3` on.
example {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] (h1 : 1 < δ) (h2 : δ < √2)
    {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (n : ℕ) :
    δ ∉ jonesLoopParameters ∧
      ((∀ x : TemperleyLieb ℂ (δ : ℂ) n, 0 ≤ tr n (star x * x)) ↔ n < 3) := by
  have hlo : 2 * cos (π / (3 : ℕ)) < δ := by norm_num [cos_pi_div_three]; linarith
  have hhi : δ < 2 * cos (π / (4 : ℕ)) := by
    rw [Nat.cast_ofNat, cos_pi_div_four]
    linarith
  have hJ : δ ∉ jonesLoopParameters :=
    notMem_jonesLoopParameters_of_two_mul_cos_lt (by omega) hlo hhi
  have hfl : ⌊π / arccos (δ / 2)⌋₊ = 3 :=
    floor_pi_div_arccos_eq (by omega) hlo hhi
  refine ⟨hJ, ?_⟩
  rw [htr.forall_map_star_mul_self_nonneg_iff_lt_floor (by linarith) hJ, hfl]

-- In `1 < δ < √2`, `tr 2 f₂ = δ² - 1 > 0` whereas `tr 3 f₃ = δ³ - 2 δ < 0`.
example {δ : ℝ} (h1 : 1 < δ) (h2 : δ < √2)
    {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) :
    0 < tr 2 (jonesWenzl (δ : ℂ) 2) ∧ tr 3 (jonesWenzl (δ : ℂ) 3) < 0 := by
  have hδ2 : δ ^ 2 < 2 := by
    have hsq : √2 ^ 2 = 2 := sq_sqrt zero_le_two
    nlinarith [sq_nonneg δ]
  have hq (j : ℕ) : qInt ℂ (δ : ℂ) j = (qInt ℝ δ j : ℂ) :=
    (Complex.ofRealHom.map_qInt δ j).symm
  have hq3 : qInt ℝ δ 3 = δ ^ 2 - 1 := by
    rw [qInt_add_two, qInt_two, qInt_one]
    ring
  have hq4 : qInt ℝ δ 4 = δ * (δ ^ 2 - 2) := by
    rw [qInt_add_two, hq3, qInt_two]
    ring
  have hunit3 : ∀ k ∈ Finset.Icc 1 3, IsUnit (qInt ℂ (δ : ℂ) k) := by
    intro k hk
    rcases Finset.mem_Icc.1 hk with ⟨hk1, hk3⟩
    rw [hq]
    apply (Complex.ofReal_ne_zero.2 ?_).isUnit
    interval_cases k
    · simp
    · simp; linarith
    · rw [hq3]; nlinarith
  have hunit2 : ∀ k ∈ Finset.Icc 1 2, IsUnit (qInt ℂ (δ : ℂ) k) :=
    fun k hk ↦ hunit3 k (Finset.Icc_subset_Icc_right (by omega) hk)
  refine ⟨?_, ?_⟩
  · rw [htr.map_jonesWenzl 2 hunit2, hq, hq3]
    exact_mod_cast (show 0 < δ ^ 2 - 1 by nlinarith)
  · rw [htr.map_jonesWenzl 3 hunit3, hq, hq4]
    exact_mod_cast mul_neg_of_pos_of_neg (by linarith) (by linarith)

/-! ### Discrete admissible boundaries: `δ = √2` and `δ = 1` -/

-- At `δ = √2` (`m = 4`), all levels are positive semidefinite and `f₃` is a nonzero element of the
-- three-strand trace radical.
example [Fact (IsSelfAdjoint (√2 : ℂ))]
    {tr : ∀ n : ℕ, TemperleyLieb ℂ (√2 : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ (√2 : ℂ) tr) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (√2 : ℂ) n), 0 ≤ tr n (star x * x)) ∧
      jonesWenzl (√2 : ℂ) 3 ≠ 0 ∧
      jonesWenzl (√2 : ℂ) 3 ∈ (tr 3).traceRadical (htr.map_mul_comm 3) := by
  have hsq : (√2 : ℝ) ^ 2 = 2 := sq_sqrt zero_le_two
  have hq (j : ℕ) : qInt ℂ (√2 : ℂ) j = (qInt ℝ √2 j : ℂ) :=
    (Complex.ofRealHom.map_qInt √2 j).symm
  have hq3 : qInt ℝ √2 3 = 1 := by
    rw [qInt_add_two, qInt_two, qInt_one]
    linear_combination hsq
  have hq4 : qInt ℝ √2 4 = 0 := by
    rw [qInt_add_two, hq3, qInt_two]
    ring
  have hunit : ∀ k ∈ Finset.Icc 1 3, IsUnit (qInt ℂ (√2 : ℂ) k) := by
    intro k hk
    rcases Finset.mem_Icc.1 hk with ⟨hk1, hk3⟩
    rw [hq]
    apply (Complex.ofReal_ne_zero.2 ?_).isUnit
    interval_cases k
    · simp
    · simp [sqrt_ne_zero'.2 zero_lt_two]
    · simp [hq3]
  refine ⟨htr.map_star_mul_self_nonneg_of_mem_jonesLoopParameters sqrt_two_mem_jonesLoopParameters,
    fun h0 ↦ zero_ne_one (α := ℂ) (by simpa [h0] using aug_jonesWenzl (δ := (√2 : ℂ)) 3), ?_⟩
  rw [htr.jonesWenzl_mem_traceRadical_iff hunit, hq, hq4, Complex.ofReal_zero]

-- At `δ = 1` (`m = 3`), `f₂ = 1 - e 0` belongs to the trace radical on two strands, whereas it does
-- not belong to the Jacobson radical because `1 - f₂ = e 0` is killed by the augmentation.
example {tr : ∀ n : ℕ, TemperleyLieb ℂ ((1 : ℝ) : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ ((1 : ℝ) : ℂ) tr) :
    jonesWenzl ((1 : ℝ) : ℂ) 2 ∈ (tr 2).traceRadical (htr.map_mul_comm 2) ∧
      jonesWenzl ((1 : ℝ) : ℂ) 2 ∉ Ring.jacobson (TemperleyLieb ℂ ((1 : ℝ) : ℂ) 2) ∧
      (tr 2).traceRadical (htr.map_mul_comm 2) ≠
        Ring.jacobson (TemperleyLieb ℂ ((1 : ℝ) : ℂ) 2) := by
  have hunit : ∀ k ∈ Finset.Icc 1 2, IsUnit (qInt ℂ ((1 : ℝ) : ℂ) k) := by
    intro k hk
    rcases Finset.mem_Icc.1 hk with ⟨hk1, hk2⟩
    interval_cases k <;> simp
  have hmem : jonesWenzl ((1 : ℝ) : ℂ) 2 ∈ (tr 2).traceRadical (htr.map_mul_comm 2) := by
    rw [htr.jonesWenzl_mem_traceRadical_iff hunit, qInt_add_two, qInt_two, qInt_one]
    norm_num
  have hnotjac :
      jonesWenzl ((1 : ℝ) : ℂ) 2 ∉ Ring.jacobson (TemperleyLieb ℂ ((1 : ℝ) : ℂ) 2) := by
    intro hjac
    rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff] at hjac
    obtain ⟨z, hz⟩ := hjac (-1)
    have haug :=
      congrArg (aug (R := ℂ) (δ := ((1 : ℝ) : ℂ)) (n := 2)) ((Submodule.mem_bot _).1 hz)
    simp at haug
  exact ⟨hmem, hnotjac, fun heq ↦ hnotjac (heq ▸ hmem)⟩

/-! ### Two-strand Wenzl coefficient check -/

-- Over any commutative ring `R`, the element `1 - δ • e 0` on two strands is idempotent iff
-- `δ ^ 3 = δ`, so replacing `δ⁻¹` by `δ` in `jonesWenzl δ 2 = 1 - δ⁻¹ • e 0` fails whenever
-- `δ ^ 3 ≠ δ`.
example {R : Type*} [CommRing R] (δ : R) :
    IsIdempotentElem (1 - δ • e (R := R) (n := 2) δ 0) ↔ δ ^ 3 = δ := by
  rw [IsIdempotentElem]
  have hsq :
      (1 - δ • e (R := R) (n := 2) δ 0) * (1 - δ • e δ 0) =
        1 - (2 * δ - δ ^ 3) • e δ 0 := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, e_mul_self,
      smul_smul]
    module
  rw [hsq, sub_right_inj, (smul_left_injective_e_two (0 : Fin (2 - 1))).eq_iff]
  exact ⟨fun h ↦ by linear_combination -h, fun h ↦ by linear_combination -h⟩

end TauCeti.TemperleyLiebPositivityExamples
