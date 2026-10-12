/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Jimbo.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

/-!
# Turaev's enhancement of the Jimbo R-matrix

The diagonal operator with eigenvalues `q ^ (N - 1 - 2 * a)` on colours `a : Fin N`
enhances the Jimbo R-matrix. On words its tensor powers commute with every crossing.
The weighted partial trace over the second colour of a positive crossing is `q ^ N`
times the identity; for a negative crossing it is `q ^ (-N)` times the identity.
These are the local identities used to normalize a weighted braid trace under Markov
stabilization. The partial traces are stated as matrix-coefficient sums in the canonical
word basis, so they apply over any commutative ring and require no choice of basis.

## References

* M. Jimbo, *A q-analogue of U(gl(N+1)), Hecke algebra, and the Yang-Baxter equation*,
  Lett. Math. Phys. 11 (1986), 247-252.
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math.
  92 (1988), 527-553.
* G. Massuyeau, F. F. Nichita, *Yang-Baxter operators arising from algebra structures
  and the Alexander polynomial of knots*, Comm. Algebra 33 (2005), 2375-2385,
  Definition 3.1 (the enhancement conditions).

The R-matrix and its inverse are `jimboGenerator` and `jimboUnit` from the companion module.
-/

public section

open Finsupp Function
open scoped BigOperators

namespace TauCeti.KnotTheory

variable {R : Type*} [CommRing R] {N n : ℕ}

/-- The diagonal eigenvalue of Turaev's enhancement on the colour `a`. The exponent is
an integer, and the parameter is a unit, so this is defined over any commutative ring. -/
def jimboWeight (q : Rˣ) (a : Fin N) : R :=
  ↑(q ^ ((N : ℤ) - 1 - 2 * (a : ℕ)))

/-- The defining equation of the enhancement weight. -/
theorem jimboWeight_def (q : Rˣ) (a : Fin N) :
    jimboWeight q a = ↑(q ^ ((N : ℤ) - 1 - 2 * (a : ℕ))) := (rfl)

/-- The enhancement at `q = 1` assigns weight one to every colour. -/
@[simp]
theorem jimboWeight_one (a : Fin N) : jimboWeight (1 : Rˣ) a = 1 := by
  simp [jimboWeight_def]

/-- Replacing `q` by its inverse gives the inverse enhancement weight. -/
@[simp]
theorem jimboWeight_mul_inv (q : Rˣ) (a : Fin N) :
    jimboWeight q a * jimboWeight q⁻¹ a = 1 := by
  simp only [jimboWeight_def, ← Units.val_mul, ← mul_zpow, mul_inv_cancel, one_zpow,
    Units.val_one]

/-- The tensor power of the diagonal enhancement: a basis word is multiplied by the
product of the weights of its colours. -/
noncomputable def jimboEnhancement (q : Rˣ) : Module.End R ((Fin n → Fin N) →₀ R) :=
  linearCombination R fun w ↦ (∏ i, jimboWeight q (w i)) • single w 1

/-- The enhancement acts diagonally in the canonical word basis. -/
@[simp]
theorem jimboEnhancement_single_one (q : Rˣ) (w : Fin n → Fin N) :
    jimboEnhancement q (single w 1) = (∏ i, jimboWeight q (w i)) • single w 1 := by
  simp [jimboEnhancement]

/-- At `q = 1` the enhancement is the identity. -/
@[simp]
theorem jimboEnhancement_one : jimboEnhancement (N := N) (n := n) (1 : Rˣ) = 1 := by
  ext w : 2
  simp

/-- The tensor-power enhancement is inverted by replacing the parameter with its inverse. -/
@[simp]
theorem jimboEnhancement_mul_inv (q : Rˣ) :
    jimboEnhancement (N := N) (n := n) q * jimboEnhancement q⁻¹ = 1 := by
  ext w : 2
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
    Module.End.mul_apply, jimboEnhancement_single_one, map_smul, Module.End.one_apply,
    smul_smul]
  rw [mul_comm, ← Finset.prod_mul_distrib]
  simp

/-- The enhancement is an invertible operator. -/
theorem isUnit_jimboEnhancement (q : Rˣ) :
    IsUnit (jimboEnhancement (N := N) (n := n) q) := by
  refine ⟨⟨jimboEnhancement q, jimboEnhancement q⁻¹,
    jimboEnhancement_mul_inv q, ?_⟩, rfl⟩
  simpa only [inv_inv] using jimboEnhancement_mul_inv (N := N) (n := n) q⁻¹

/-- The tensor-power enhancement commutes with the Jimbo crossing on any pair of strands. -/
theorem jimboEnhancement_commute_generator (q : Rˣ) (j k : Fin n) :
    Commute (jimboEnhancement (N := N) q) (jimboGenerator q j k) := by
  have hw (w : Fin n → Fin N) :
      (∏ i, jimboWeight q ((w ∘ Equiv.swap j k) i)) = ∏ i, jimboWeight q (w i) :=
    Equiv.prod_comp (Equiv.swap j k) (fun i ↦ jimboWeight q (w i))
  unfold Commute SemiconjBy
  ext w : 2
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
    Module.End.mul_apply, jimboGenerator_single_one, jimboEnhancement_single_one]
  split_ifs <;>
    simp_all only [map_smul, map_add, jimboEnhancement_single_one, jimboGenerator_single_one,
      ↓reduceIte] <;> module

/-- The tensor-power enhancement commutes with every braid in the Jimbo representation. -/
theorem jimboEnhancement_commute (q : Rˣ) (b : BraidGroup n) :
    Commute (jimboEnhancement (N := N) q)
      (jimbo (Fin N) q b : Module.End R ((Fin n → Fin N) →₀ R)) := by
  induction b using BraidGroup.sigma_induction_on with
  | sigma i =>
    simpa only [jimbo_sigma, jimboUnit_val] using
      jimboEnhancement_commute_generator (N := N) q
        (BraidGroup.strand i) (BraidGroup.strandSucc i)
  | one => simp
  | mul b c hb hc => simpa only [map_mul, Units.val_mul] using hb.mul_right hc
  | inv b hb => simpa only [map_inv] using hb.units_inv_right

private theorem weight_step (q : Rˣ) (a : ℕ) :
    ((q : R) - ↑(q⁻¹)) * ↑(q ^ ((N : ℤ) - 1 - 2 * a)) =
      (↑(q ^ ((N : ℤ) - 2 * a)) : R) - ↑(q ^ ((N : ℤ) - 2 * (a + 1))) := by
  rw [sub_mul, ← Units.val_mul, ← Units.val_mul]
  have h₁ : q * q ^ ((N : ℤ) - 1 - 2 * a) = q ^ ((N : ℤ) - 2 * a) := by
    rw [← zpow_one_add]; congr 1; omega
  have h₂ : q⁻¹ * q ^ ((N : ℤ) - 1 - 2 * a) = q ^ ((N : ℤ) - 2 * (a + 1)) := by
    rw [← zpow_neg_one, ← zpow_add]; congr 1; ring
  rw [h₁, h₂]

private theorem weight_prefix (q : Rˣ) (m : ℕ) :
    ((q : R) - ↑(q⁻¹)) * (∑ a ∈ Finset.range m, (↑(q ^ ((N : ℤ) - 1 - 2 * a)) : R)) =
      ↑(q ^ (N : ℤ)) - ↑(q ^ ((N : ℤ) - 2 * m)) := by
  rw [Finset.mul_sum]
  simp_rw [weight_step (N := N)]
  simpa using Finset.sum_range_sub' (fun a ↦ (↑(q ^ ((N : ℤ) - 2 * a)) : R)) m

/-- Summing the enhancement weights below a colour gives the positive stabilization factor.
This formula involves no division by `q - q⁻¹`, so it also holds at `q = ±1`. -/
theorem jimboWeight_sum_lt (q : Rˣ) (a : Fin N) :
    (q : R) * jimboWeight q a + ((q : R) - ↑(q⁻¹)) *
      (∑ c : Fin N, if c < a then jimboWeight q c else 0) = ↑(q ^ N) := by
  have hs : (∑ c : Fin N, if c < a then jimboWeight q c else 0) =
      ∑ c ∈ Finset.range a.val, (↑(q ^ ((N : ℤ) - 1 - 2 * c)) : R) := by
    simp only [jimboWeight_def, Fin.lt_def]
    rw [Fin.sum_univ_eq_sum_range
      (fun c ↦ if c < a.val then (↑(q ^ ((N : ℤ) - 1 - 2 * (c : ℤ))) : R) else 0)]
    rw [← Finset.sum_subset (Finset.range_mono (Nat.le_of_lt a.isLt))
      (by intro i _ hi; simp_all)]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  rw [hs, weight_prefix (N := N), jimboWeight_def, ← Units.val_mul, ← zpow_one_add]
  have he : 1 + ((N : ℤ) - 1 - 2 * a.val) = (N : ℤ) - 2 * a.val := by omega
  rw [he]
  simp

/-- The difference of the positive and negative stabilization factors is the quantum dimension
multiplied by the Hecke parameter. -/
theorem jimboWeight_sum (q : Rˣ) :
    ((q : R) - ↑(q⁻¹)) * (∑ c : Fin N, jimboWeight q c) =
      ↑(q ^ N) - ↑((q⁻¹) ^ N) := by
  simp only [jimboWeight_def]
  rw [Fin.sum_univ_eq_sum_range (fun c ↦ (↑(q ^ ((N : ℤ) - 1 - 2 * (c : ℤ))) : R))]
  rw [weight_prefix (N := N)]
  congr 2
  have he : (N : ℤ) - 2 * N = -(N : ℤ) := by omega
  rw [he, zpow_neg, zpow_natCast, inv_pow]

/-- The weighted partial trace of a positive Jimbo crossing over its second colour. -/
theorem sum_jimboGenerator_coeff_mul_weight (q : Rˣ) (a b : Fin N) :
    (∑ c : Fin N,
      (jimboGenerator q (0 : Fin 2) 1 (single ![b, c] 1)) ![a, c] * jimboWeight q c) =
      if a = b then ↑(q ^ N) else 0 := by
  classical
  have hswap (b c : Fin N) : (![b, c] : Fin 2 → Fin N) ∘ Equiv.swap 0 1 = ![c, b] := by
    ext i; fin_cases i <;> simp
  have heq (a b c d : Fin N) : (![a, b] : Fin 2 → Fin N) = ![c, d] ↔ a = c ∧ b = d := by
    simp [funext_iff, Fin.forall_fin_two]
  by_cases hab : a = b
  · subst b
    have hc (c : Fin N) :
        (jimboGenerator q (0 : Fin 2) 1 (single ![a, c] 1)) ![a, c] * jimboWeight q c =
          (if c = a then (q : R) * jimboWeight q a else 0) +
          (if c < a then ((q : R) - ↑(q⁻¹)) * jimboWeight q c else 0) := by
      rw [jimboGenerator_single_one]
      rcases lt_trichotomy a c with h | h | h <;> subst_vars <;>
        simp [ne_of_lt, ne_of_gt, lt_asymm, *]
    simp_rw [hc]
    rw [Finset.sum_add_distrib]
    simpa only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.mul_sum,
      mul_ite, mul_zero] using jimboWeight_sum_lt q a
  · rw [ite_eq_right hab]
    apply Finset.sum_eq_zero
    intro c _
    rw [jimboGenerator_single_one]
    split_ifs <;> simp [hswap, heq, Finsupp.single_apply, hab] <;> grind

/-- The weighted partial trace of a negative Jimbo crossing over its second colour. -/
theorem sum_jimboUnit_inv_coeff_mul_weight (q : Rˣ) (a b : Fin N) :
    (∑ c : Fin N,
      (((jimboUnit q (0 : Fin (2 - 1)))⁻¹ :
        (Module.End R ((Fin 2 → Fin N) →₀ R))ˣ) : Module.End R ((Fin 2 → Fin N) →₀ R))
          (single ![b, c] 1) ![a, c] * jimboWeight q c) =
      if a = b then ↑((q⁻¹) ^ N) else 0 := by
  classical
  rw [jimboUnit_inv_val]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, add_mul]
  rw [Finset.sum_add_distrib]
  have hstrand : BraidGroup.strand (0 : Fin (2 - 1)) = 0 := by ext; simp
  have hsucc : BraidGroup.strandSucc (0 : Fin (2 - 1)) = 1 := by ext; simp
  rw [hstrand, hsucc, sum_jimboGenerator_coeff_mul_weight]
  have heq (c : Fin N) : (![b, c] : Fin 2 → Fin N) = ![a, c] ↔ b = a := by
    simp [funext_iff, Fin.forall_fin_two]
  simp only [Finsupp.single_apply, heq]
  by_cases h : a = b
  · subst b
    simp only [↓reduceIte, mul_one]
    rw [← Finset.mul_sum]
    have hs := jimboWeight_sum (N := N) q
    linear_combination -hs
  · simp [h, Ne.symm h]

end TauCeti.KnotTheory
