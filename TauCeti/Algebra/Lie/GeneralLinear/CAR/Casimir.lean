/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Casimir
public import TauCeti.Algebra.Lie.GeneralLinear.Fock

import TauCeti.Algebra.Lie.GeneralLinear.CAR.HighestWeight
import TauCeti.Algebra.Lie.GeneralLinear.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Basic

/-!
# The trace-form Casimir on the CAR module

Let `Fᵢⱼ` be the normal-ordered quadratic lift of the matrix unit `Eᵢⱼ` to the Clifford
algebra of the trace form. The trace-form Casimir acts on the left-regular CAR module by left
multiplication with `∑ i, j, Fᵢⱼ Fⱼᵢ`. This file proves that this Clifford element is the scalar

`N (2 N² - 1) / 4`.

This scalar is the Casimir invariant used with the CAR occupation spectrum to constrain the
highest weights of irreducible constituents. It is therefore an input to the constituent-weight
comparison and the resulting isotypic decomposition of the left-regular CAR module.

## Main results

* `TauCeti.representation_glCasimir_car_apply`: the Casimir acts on every CAR vector by the
  scalar `N (2 N² - 1) / 4`.

## References

* D. Panyushev, *The exterior algebra and "spin" of an orthogonal g-module*,
  Transformation Groups 6 (2001), 371–396, Proposition 2.4 and Example 2.5(1).
* B. Kostant, *Clifford algebra analogue of the Hopf--Koszul--Samelson theorem*,
  Advances in Mathematics 125 (1997), 275–350.
-/

public section

namespace TauCeti

open CliffordAlgebra Finset
open scoped TauCeti

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]
variable {N : ℕ}

section CliffordCalculation

attribute [local instance 2000] Classical.decEq

private noncomputable abbrev carD (i j : Fin N) :
    CliffordAlgebra (traceQuadraticForm K (Fin N)) :=
  ι (traceQuadraticForm K (Fin N)) (Matrix.single i j 1)

private noncomputable abbrev carF (i j : Fin N) :
    CliffordAlgebra (traceQuadraticForm K (Fin N)) :=
  glCliffordHom (K := K) (n := Fin N) (Matrix.single i j 1)

private noncomputable def carCasimirElement :
    CliffordAlgebra (traceQuadraticForm K (Fin N)) :=
  ∑ i : Fin N, ∑ j : Fin N,
    carF (K := K) i j * carF j i

omit [Invertible (2 : K)] in
private theorem sum_carD_cycle (a b : Fin N) :
    (∑ i : Fin N, ∑ k : Fin N, carD (K := K) k i * carD i b * carD a k) =
      ∑ i : Fin N, ∑ k : Fin N, carD (K := K) i b * carD a k * carD k i := by
  have hcycle (i k : Fin N) :
      carD (K := K) k i * carD i b * carD a k =
        carD i b * carD a k * carD k i -
          (if i = a then (2 : K) • carD i b else 0) +
            if k = b then (2 : K) • carD a k else 0 := by
    have hib := traceQuadraticForm_ι_single_mul_ι_single_add_swap
      (R := K) k i i b 1 1
    have hak := traceQuadraticForm_ι_single_mul_ι_single_add_swap
      (R := K) k i a k 1 1
    have hib' : carD (K := K) k i * carD i b =
        algebraMap K _ (if i = i ∧ b = k then 2 * (1 * 1) else 0) -
          carD i b * carD k i :=
      eq_sub_iff_add_eq.mpr hib
    have hak' : carD (K := K) k i * carD a k =
        algebraMap K _ (if i = a ∧ k = k then 2 * (1 * 1) else 0) -
          carD a k * carD k i :=
      eq_sub_iff_add_eq.mpr hak
    rw [hib', sub_mul, mul_assoc (carD (K := K) i b), hak', mul_sub]
    have hcentral (x : CliffordAlgebra (traceQuadraticForm K (Fin N))) :
        algebraMap K _ (2 : K) * x = x * algebraMap K _ (2 : K) :=
      Algebra.commutes (2 : K) x
    by_cases hia : i = a <;> by_cases hbk : b = k
    all_goals try have hkb : k ≠ b := Ne.symm hbk
    all_goals simp_all only [true_and, mul_one, and_true, ite_true, ite_false, map_zero,
      zero_mul, Algebra.smul_def, map_ofNat]
    all_goals noncomm_ring
  simp_rw [hcycle]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp

private theorem commute_carCasimirElement_carD (a b : Fin N) :
    Commute (carCasimirElement (K := K) (N := N)) (carD (K := K) a b) := by
  rw [commute_iff_lie_eq, carCasimirElement, sum_lie]
  simp_rw [sum_lie]
  have hleib (x y z : CliffordAlgebra (traceQuadraticForm K (Fin N))) :
      ⁅x * y, z⁆ = x * ⁅y, z⁆ + ⁅x, z⁆ * y := by
    simp only [Ring.lie_def]
    noncomm_ring
  have hFD (i j : Fin N) : ⁅carF (K := K) i j, carD (K := K) a b⁆ =
      (if j = a then carD (K := K) i b else 0) -
        if b = i then carD (K := K) a j else 0 := by
    rw [glCliffordHom_lie_ι, lie_single_single]
    simp only [map_sub, apply_ite, map_zero, one_mul, carD]
    split_ifs <;> rfl
  have hF (i j : Fin N) :
      carF (K := K) i j =
        (2 : K)⁻¹ • ∑ k : Fin N, carD (K := K) i k * carD k j := by
    exact glCliffordHom_single (K := K) (n := Fin N) i j
  have hA : (∑ i : Fin N, ∑ j : Fin N,
      carF (K := K) i j * (if i = a then carD j b else 0)) =
        ∑ j : Fin N, carF (K := K) a j * carD j b := by
    simp [mul_ite]
  have hB : (∑ i : Fin N, ∑ j : Fin N,
      carF (K := K) i j * (if b = j then carD a i else 0)) =
        ∑ i : Fin N, carF (K := K) i b * carD a i := by
    simp [mul_ite]
  have hC : (∑ i : Fin N, ∑ j : Fin N,
      (if j = a then carD i b else 0) * carF j i) =
        ∑ i : Fin N, carD (K := K) i b * carF a i := by
    simp [ite_mul]
  have hD : (∑ i : Fin N, ∑ j : Fin N,
      (if b = i then carD a j else 0) * carF j i) =
        ∑ j : Fin N, carD (K := K) a j * carF j b := by
    simp [ite_mul]
  -- The Leibniz rule leaves four sums. The two outer sums agree after expanding `F`, while the
  -- cyclic CAR identity identifies the two inner sums; both pairs therefore cancel.
  calc
    ∑ i : Fin N, ∑ j : Fin N, ⁅carF (K := K) i j * carF j i, carD a b⁆ =
        (∑ j : Fin N, carF (K := K) a j * carD j b) -
          (∑ i : Fin N, carF (K := K) i b * carD a i) +
          (∑ i : Fin N, carD (K := K) i b * carF a i) -
          ∑ j : Fin N, carD (K := K) a j * carF j b := by
      simp_rw [hleib, hFD, mul_sub, sub_mul, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      rw [hA, hB, hC, hD]
      abel
    _ = 0 := by
      have hAD : (∑ j : Fin N, carF (K := K) a j * carD j b) =
          ∑ j : Fin N, carD (K := K) a j * carF j b := by
        simp_rw [hF, smul_mul_assoc, mul_smul_comm,
          Finset.sum_mul, Finset.mul_sum, Finset.smul_sum]
        rw [Finset.sum_comm]
        simp only [mul_assoc]
      have hBC : (∑ i : Fin N, carF (K := K) i b * carD a i) =
          ∑ i : Fin N, carD (K := K) i b * carF a i := by
        simp_rw [hF, smul_mul_assoc, mul_smul_comm,
          Finset.sum_mul, Finset.mul_sum, Finset.smul_sum]
        rw [Finset.sum_comm]
        simpa only [← Finset.smul_sum, mul_assoc] using
          congrArg ((2 : K)⁻¹ • ·) (sum_carD_cycle (K := K) a b)
      rw [hAD, hBC]
      abel

private theorem carCasimirElement_mem_even :
    carCasimirElement (K := K) (N := N) ∈ even (traceQuadraticForm K (Fin N)) := by
  have hF_even (i j : Fin N) :
      carF (K := K) i j ∈ evenOdd (traceQuadraticForm K (Fin N)) 0 := by
    rw [carF, glCliffordHom_single]
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro k _
    exact ι_mul_ι_mem_evenOdd_zero _ _ _
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  simpa only [zero_add] using
    SetLike.mul_mem_graded (hF_even i j) (hF_even j i)

private theorem carCasimirElement_eq_algebraMap :
    ∃ r : K, carCasimirElement (K := K) (N := N) =
      algebraMap K (CliffordAlgebra (traceQuadraticForm K (Fin N))) r := by
  apply exists_eq_algebraMap_of_mem_even_of_commute
    (traceQuadraticForm K (Fin N)) (traceQuadraticForm_nondegenerate K (Fin N))
      (carCasimirElement (K := K) (N := N)) carCasimirElement_mem_even
  intro X
  rw [Matrix.matrix_eq_sum_single X, map_sum]
  apply Commute.sum_right
  intro i _
  rw [map_sum]
  apply Commute.sum_right
  intro j _
  have hsingle : Matrix.single i j (X i j) =
      X i j • Matrix.single i j (1 : K) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hsingle, map_smul]
  exact (commute_carCasimirElement_carD (K := K) i j).smul_right (X i j)

end CliffordCalculation

private theorem representation_glCasimir_eq_carCasimirElement_mul
    (c : CliffordAlgebra (traceQuadraticForm K (Fin N))) :
    UniversalEnvelopingAlgebra.representation K (Matrix (Fin N) (Fin N) K)
        (CliffordAlgebra (traceQuadraticForm K (Fin N))) (glCasimir K (Fin N)) c =
      carCasimirElement (K := K) (N := N) * c := by
  have hunit (i j : Fin N) :
      glCliffordHom (K := K) (n := Fin N) (Matrix.single i j 1) =
        carF (K := K) i j := by
    congr 1
    ext a b
    simp only [Matrix.single_apply]
    split_ifs <;> rfl
  calc
    _ = ∑ i : Fin N, ∑ j : Fin N,
        ⁅Matrix.single i j (1 : K), ⁅Matrix.single j i (1 : K), c⁆⁆ :=
      representation_glCasimir_apply K (Fin N) c
    (∑ i : Fin N, ∑ j : Fin N,
      ⁅Matrix.single i j (1 : K), ⁅Matrix.single j i (1 : K), c⁆⁆) =
        ∑ i : Fin N, ∑ j : Fin N, carF (K := K) i j * (carF j i * c) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [car_lie_def, car_lie_def, hunit, hunit]
    _ = carCasimirElement * c := by
      rw [carCasimirElement, Finset.sum_mul]
      simp_rw [Finset.sum_mul, mul_assoc]

private def carCasimirWeight (N : ℕ) (i : Fin N) : K :=
  (2 : K)⁻¹ * (1 + 2 * ((Finset.univ.filter fun k : Fin N => i < k).card : K))

private theorem carCasimirWeight_eq (i : Fin N) :
    carCasimirWeight (K := K) N i = (N : K) - 1 / 2 - (i : K) := by
  rw [carCasimirWeight, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  have hi : (i : ℕ) + 1 ≤ N := by omega
  have hsub : N - 1 - (i : ℕ) = N - ((i : ℕ) + 1) := by omega
  rw [hsub, Nat.cast_sub hi]
  push_cast
  field_simp
  ring

private theorem sum_carCasimirWeight (N : ℕ) :
    (∑ i : Fin N, carCasimirWeight (K := K) N i) = (N : K) ^ 2 / 2 := by
  simp_rw [carCasimirWeight_eq]
  obtain _ | N := N
  · simp
  have hsum : (∑ i ∈ Finset.range (N + 1), (i : K)) * 2 =
      ((N + 1 : ℕ) : K) * (N : K) := by
    have h := congrArg (fun m : ℕ => (m : K)) (Finset.sum_range_id_mul_two (N + 1))
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum, Nat.add_sub_cancel] using h
  have hsum' : (∑ i ∈ Finset.range (N + 1), (i : K)) =
      ((N + 1 : ℕ) : K) * (N : K) / 2 := by
    exact (eq_div_iff (Invertible.ne_zero (2 : K))).2 hsum
  calc
    (∑ i : Fin (N + 1), (((N + 1 : ℕ) : K) - 1 / 2 - (i : K))) =
        ∑ i ∈ Finset.range (N + 1), (((N + 1 : ℕ) : K) - 1 / 2 - (i : K)) :=
      Fin.sum_univ_eq_sum_range
        (fun i : ℕ => ((N + 1 : ℕ) : K) - 1 / 2 - (i : K)) (N + 1)
    _ = ((N + 1 : ℕ) : K) ^ 2 / 2 := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [hsum']
      push_cast
      field_simp [Invertible.ne_zero (2 : K)]
      ring

private theorem carCasimir_eigenvalue (N : ℕ) :
    (∑ i : Fin N, carCasimirWeight (K := K) N i *
      (carCasimirWeight (K := K) N i + (N : K) - 1 - 2 * (i : K))) =
        (N : K) * (2 * (N : K) ^ 2 - 1) / 4 := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hsucc (i : Fin N) :
          carCasimirWeight (K := K) (N + 1) i.succ =
            carCasimirWeight (K := K) N i := by
        rw [carCasimirWeight_eq, carCasimirWeight_eq]
        norm_num [Fin.val_succ]
        ring
      have htail (i : Fin N) :
          carCasimirWeight (K := K) (N + 1) i.succ *
              (carCasimirWeight (K := K) (N + 1) i.succ + (N + 1 : K) - 1 -
                2 * (i.succ : K)) =
            carCasimirWeight (K := K) N i *
                (carCasimirWeight (K := K) N i + (N : K) - 1 - 2 * (i : K)) -
              carCasimirWeight (K := K) N i := by
        rw [hsucc]
        norm_num [Fin.val_succ]
        ring
      rw [Fin.sum_univ_succ]
      push_cast
      simp_rw [htail]
      rw [Finset.sum_sub_distrib, ih, sum_carCasimirWeight, carCasimirWeight_eq]
      push_cast
      norm_num
      have h4 : (4 : K) ≠ 0 := by
        rw [show (4 : K) = 2 * 2 by norm_num]
        exact mul_ne_zero (Invertible.ne_zero (2 : K)) (Invertible.ne_zero (2 : K))
      field_simp [h4]
      ring

private theorem carCasimirElement_eq_scalar :
    carCasimirElement (K := K) (N := N) =
      algebraMap K (CliffordAlgebra (traceQuadraticForm K (Fin N)))
        ((N : K) * (2 * (N : K) ^ 2 - 1) / 4) := by
  obtain ⟨r, hr⟩ := carCasimirElement_eq_algebraMap (K := K) (N := N)
  have hhighest :
      IsGlHighestWeightVector (carCasimirWeight (K := K) N)
        (carHighestWeightVector K (Fin N)) :=
    isGlHighestWeightVector_carHighestWeightVector (K := K) (n := Fin N)
  have hcasimir := glCasimir_smul_of_isGlHighestWeightVector (K := K)
    hhighest
  rw [representation_glCasimir_eq_carCasimirElement_mul, hr,
    carCasimir_eigenvalue] at hcasimir
  have hscalar : r • carHighestWeightVector K (Fin N) =
      ((N : K) * (2 * (N : K) ^ 2 - 1) / 4) • carHighestWeightVector K (Fin N) := by
    simpa only [Algebra.smul_def] using hcasimir
  have hr' : r = (N : K) * (2 * (N : K) ^ 2 - 1) / 4 :=
    smul_left_injective K (carHighestWeightVector_ne_zero (K := K) (n := Fin N)) hscalar
  rwa [hr'] at hr

/-- The trace-form Casimir acts on the left-regular CAR module by the scalar
`N (2 N² - 1) / 4`. -/
@[simp]
theorem representation_glCasimir_car_apply (F : Type u) [Field F] [Invertible (2 : F)] (N : ℕ)
    (c : CliffordAlgebra (traceQuadraticForm F (Fin N))) :
    UniversalEnvelopingAlgebra.representation F (Matrix (Fin N) (Fin N) F)
        (CliffordAlgebra (traceQuadraticForm F (Fin N))) (glCasimir F (Fin N)) c =
      ((N : F) * (2 * (N : F) ^ 2 - 1) / 4) • c := by
  rw [representation_glCasimir_eq_carCasimirElement_mul, carCasimirElement_eq_scalar,
    Algebra.smul_def]

end

end TauCeti
