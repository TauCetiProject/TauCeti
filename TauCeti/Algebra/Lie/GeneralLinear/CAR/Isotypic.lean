/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.CAR.WeightSpectrum
public import TauCeti.Algebra.Lie.GeneralLinear.Isotypic
import TauCeti.Algebra.Lie.GeneralLinear.CAR.Casimir
import TauCeti.Algebra.Lie.GeneralLinear.CAR.WeightUniqueness
import TauCeti.Algebra.Lie.GeneralLinear.Existence
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension

/-!
# Isotypy of the left-regular CAR module

Over an algebraically closed field of characteristic zero, the left-regular Clifford algebra of
the trace form is an isotypic `gl_N`-module. Its simple type has the half-shifted staircase highest
weight

`(N - 1/2, N - 3/2, ..., 1/2)`.

To identify the weight, write its coordinates as natural occupation counts shifted by `1/2`.
Highest-weight dominance makes the counts antitone, while the CAR cut identities bound their
proper prefix sums and fix their total. The trace-form Casimir scalar supplies the remaining
quadratic equality. The staircase majorization criterion then identifies every coordinate.

## Main results

* `TauCeti.IsGlHighestWeightVector.eq_glHalfStaircase`: every CAR highest-weight vector has the
  half-shifted staircase weight.
* `TauCeti.isIsotypicOfType_glIrreducible_car`: the left-regular CAR module is isotypic of the
  simple module with that highest weight.

## References

* D. Panyushev, *The exterior algebra and "spin" of an orthogonal g-module*, Transformation Groups
  6 (2001), 371–396, Proposition 2.4 and Example 2.5(1).
* D. Shlyakhtenko, *Failure of Strong Convergence of Matrices with Fermionic Entries*,
  arXiv:2606.28648, Section 2.3.
-/

public section

open scoped BigOperators TauCeti

namespace TauCeti

noncomputable section

attribute [local instance] Classical.decEq
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem sum_range_rev (N k : ℕ) (hk : k ≤ N) :
    Finset.sum (Finset.range k) (fun x => N - (x + 1)) =
      k.choose 2 + k * (N - k) := by
  calc
    Finset.sum (Finset.range k) (fun x => N - (x + 1)) =
        Finset.sum (Finset.range k) (fun x => (N - k) + (k - 1 - x)) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxk := Finset.mem_range.mp hx
      omega
    _ = k * (N - k) + Finset.sum (Finset.range k) (fun x => k - 1 - x) := by
      rw [Finset.sum_add_distrib]
      simp
    _ = k * (N - k) + Finset.sum (Finset.range k) (fun x => x) := by
      rw [Finset.sum_range_reflect (fun x => x) k]
    _ = k.choose 2 + k * (N - k) := by
      rw [Finset.sum_range_id, Nat.choose_two_right]
      omega

private theorem sum_fin_rev_castLE (N k : ℕ) (hk : k ≤ N) :
    (∑ i : Fin k, (Fin.rev (Fin.castLE hk i) : ℕ)) =
      k.choose 2 + k * (N - k) := by
  rw [Finset.sum_fin_eq_sum_range]
  simp only [Fin.rev, Fin.castLE]
  calc
    Finset.sum (Finset.range k)
        (fun x => if h : x < k then N - (x + 1) else 0) =
        Finset.sum (Finset.range k) (fun x => N - (x + 1)) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [Finset.mem_range.mp hx]
    _ = _ := sum_range_rev N k hk

namespace IsGlHighestWeightVector

variable {K : Type*} [Field K] [CharZero K] {N : ℕ}

/-- Every highest-weight vector in the left-regular CAR module has the half-shifted staircase
weight `(N - 1/2, N - 3/2, ..., 1/2)`.

The result is uniform in the rank, including ranks zero and one. -/
theorem eq_glHalfStaircase {μ : Fin N → K}
    {v : CliffordAlgebra (traceQuadraticForm K (Fin N))}
    (hv : IsGlHighestWeightVector μ v) : μ = glHalfStaircase K N := by
  let a : Fin N → ℕ := fun i => (hv.exists_weight_apply_eq_natCast_add_inv_two i).choose
  have hμ (i : Fin N) : μ i = (a i : K) + (2 : K)⁻¹ :=
    (hv.exists_weight_apply_eq_natCast_add_inv_two i).choose_spec.2
  have ha : Antitone a :=
    hv.isGlDominantIntegral.antitone_of_eq_natCast_add_const (funext hμ)
  have hmajor (k : ℕ) (hk : k < N) :
      (∑ i : Fin k, (a (Fin.castLE hk.le i) : ℤ)) ≤
        ∑ i : Fin k, ((Fin.rev (Fin.castLE hk.le i) : ℕ) : ℤ) := by
    let s : Finset (Fin N) := Finset.univ.map (Fin.castLEEmb hk.le)
    have hbound := sum_le_choose_two_add_card_mul_sub_of_lie_single_self_eq_smul
      (K := K) (n := Fin N) (μ := μ) (a := a) (v := v) s hv.ne_zero
      (fun i _ => hv.lie_single_self_eq_smul i) (fun i _ => hμ i)
    have hnat : (∑ i : Fin k, a (Fin.castLE hk.le i)) ≤
        ∑ i : Fin k, (Fin.rev (Fin.castLE hk.le i) : ℕ) := by
      rw [sum_fin_rev_castLE N k hk.le]
      simpa [s] using hbound
    exact_mod_cast hnat
  have hsum : (∑ i : Fin N, (a i : ℤ)) =
      ∑ i : Fin N, ((Fin.rev i : ℕ) : ℤ) := by
    have hsum' := sum_univ_eq_choose_two_of_lie_single_self_eq_smul
      (K := K) (n := Fin N) (μ := μ) (a := a) (v := v) hv.ne_zero
      hv.lie_single_self_eq_smul hμ
    have hnat : (∑ i : Fin N, a i) = ∑ i : Fin N, (Fin.rev i : ℕ) := by
      rw [hsum']
      simpa using (sum_fin_rev_castLE N N le_rfl).symm
    exact_mod_cast hnat
  have hfield :
      (∑ i : Fin N, μ i * (μ i + (N : K) - 1 - 2 * (i : K))) =
        ∑ i : Fin N, glHalfStaircase K N i *
          (glHalfStaircase K N i + (N : K) - 1 - 2 * (i : K)) := by
    have hcar := glCasimir_smul_of_isGlHighestWeightVector (K := K) hv
    rw [representation_glCasimir_car_apply] at hcar
    have hscalar := smul_left_injective K hv.ne_zero hcar
    rw [glCasimir_eigenvalue_glHalfStaircase]
    exact hscalar.symm
  have hcasimir :
      (∑ i : Fin N, (a i : ℤ) * ((a i : ℤ) + (N : ℤ) - 2 * (i : ℕ))) =
        ∑ i : Fin N, ((Fin.rev i : ℕ) : ℤ) *
          (((Fin.rev i : ℕ) : ℤ) + (N : ℤ) - 2 * (i : ℕ)) := by
    apply Int.cast_injective (α := K)
    push_cast
    let c : Fin N → K := fun i => (N : K) / 2 - 1 / 4 - (i : K)
    have hshift (b : Fin N → ℕ) :
        (∑ i : Fin N, ((b i : K) + (2 : K)⁻¹) *
          ((b i : K) + (2 : K)⁻¹ + (N : K) - 1 - 2 * (i : K))) =
          (∑ i : Fin N, (b i : K) * ((b i : K) + (N : K) - 2 * (i : K))) +
            ∑ i : Fin N, c i := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [c, one_div]
      ring
    have hleft :
        (∑ i : Fin N, μ i * (μ i + (N : K) - 1 - 2 * (i : K))) =
          (∑ i : Fin N, (a i : K) * ((a i : K) + (N : K) - 2 * (i : K))) +
            ∑ i : Fin N, c i := by
      calc
        _ = ∑ i : Fin N, ((a i : K) + (2 : K)⁻¹) *
            ((a i : K) + (2 : K)⁻¹ + (N : K) - 1 - 2 * (i : K)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hμ i]
        _ = _ := hshift a
    have hrev (i : Fin N) :
        glHalfStaircase K N i = ((Fin.rev i : ℕ) : K) + (2 : K)⁻¹ := by
      simpa only [one_div] using
        (Fin.natCast_rev_add_one_div_two_eq_glHalfStaircase (F := K) i).symm
    have hright :
        (∑ i : Fin N, glHalfStaircase K N i *
          (glHalfStaircase K N i + (N : K) - 1 - 2 * (i : K))) =
          (∑ i : Fin N, ((Fin.rev i : ℕ) : K) *
            (((Fin.rev i : ℕ) : K) + (N : K) - 2 * (i : K))) +
            ∑ i : Fin N, c i := by
      calc
        _ = ∑ i : Fin N, (((Fin.rev i : ℕ) : K) + (2 : K)⁻¹) *
            (((Fin.rev i : ℕ) : K) + (2 : K)⁻¹ + (N : K) - 1 - 2 * (i : K)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hrev i]
        _ = _ := hshift fun i => (Fin.rev i : ℕ)
    rw [hleft, hright] at hfield
    exact add_right_cancel hfield
  have haeq := eq_finRev_of_antitone_of_prefix_sum_le_of_sum_eq_of_casimir_eq
    a ha hmajor hsum hcasimir
  funext i
  rw [hμ i, congrFun haeq i]
  simpa only [one_div] using
    (Fin.natCast_rev_add_one_div_two_eq_glHalfStaircase (F := K) i)

end IsGlHighestWeightVector

/-- Over an algebraically closed field of characteristic zero, the left-regular CAR module is
isotypic of the simple `gl_N`-module with half-shifted staircase highest weight. -/
theorem isIsotypicOfType_glIrreducible_car
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] (N : ℕ) :
    _root_.LieModule.IsIsotypicOfType K (Matrix (Fin N) (Fin N) K)
      (CliffordAlgebra (traceQuadraticForm K (Fin N)))
      (glIrreducible N (glHalfStaircase K N)) := by
  apply isIsotypicOfType_glIrreducible_of_forall_isGlHighestWeightVector
  intro μ v hv
  exact hv.eq_glHalfStaircase

end

end TauCeti
