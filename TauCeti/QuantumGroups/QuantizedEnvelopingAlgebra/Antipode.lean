/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantizedEnvelopingAlgebra.Basic
import Mathlib.Tactic.Ring

/-!
# The antipode of the Drinfeld-Jimbo quantized enveloping algebra

This file constructs the antipode of `TauCeti.QuantizedEnvelopingAlgebra D q` unconditionally for
every Cartan datum `D` and every parameter `q` in a field `K`, proves that it is an algebra
isomorphism onto the opposite algebra by identifying its square with a diagonal rescaling
automorphism, computes its inverse on the generators, and establishes its action on quantum divided
powers and its compatibility with morphisms of Cartan data.

## Main definitions and results

* `TauCeti.QuantizedEnvelopingAlgebra.antipodeOp`: the antipode as a `K`-algebra homomorphism
  `U_q(D) →ₐ[K] U_q(D)ᵐᵒᵖ` sending `Eᵢ ↦ op(-(Kᵢ⁻¹ Eᵢ))`, `Fᵢ ↦ op(-(Fᵢ Kᵢ))`, and
  `K_y ↦ op(K_(-y))`.
* `TauCeti.QuantizedEnvelopingAlgebra.antipodeSqEquiv`: the square `S²` as a `K`-algebra
  automorphism of `U_q(D)`, rescaling `Eᵢ` by `qᵢ⁻²` and `Fᵢ` by `qᵢ²` and fixing every `K_y`.
* `TauCeti.QuantizedEnvelopingAlgebra.antipodeEquiv` and `antipodeLinearEquiv`: the antipode as an
  algebra isomorphism `U_q(D) ≃ₐ[K] U_q(D)ᵐᵒᵖ` and as a `K`-linear equivalence
  `U_q(D) ≃ₗ[K] U_q(D)`, together with its inverse values on generators.
* `TauCeti.QuantizedEnvelopingAlgebra.antipodeLinearEquiv_quantumDividedPower_e` and
  `antipodeLinearEquiv_quantumDividedPower_f`: the action of `S` on `Eᵢ^(n)` and `Fᵢ^(n)`.
* `TauCeti.QuantizedEnvelopingAlgebra.map_antipodeLinearEquiv`: naturality of the antipode with
  respect to `CartanDatum.Hom`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  Section 3.3.
* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, AMS, 1996,
  Chapter 4.
-/

public section

open Finset

namespace TauCeti

namespace QuantizedEnvelopingAlgebra

section Antipode

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
  (D : CartanDatum ι X Y) (q : K)

/-- Quantum divided power of `-(Kᵢ⁻¹ Eᵢ)`:
`(-(Kᵢ⁻¹ Eᵢ))^(n) = ((-1)^n qᵢ^(n(n - 1))) • (Kᵢ^(-n) Eᵢ^(n))`. -/
theorem quantumDividedPower_neg_simpleKInv_mul_e (i : ι) (n : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (-(simpleKInv D q i * e D q i)) n =
      ((-1 : K) ^ n * (q ^ D.symmetrizer i) ^ (n * (n - 1))) •
        (simpleKInv D q i ^ n * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) := by
  have hcomm : e D q i * simpleKInv D q i =
      (q ^ D.symmetrizer i) ^ 2 • (simpleKInv D q i * e D q i) := by
    rw [e_mul_simpleKInv, D.cartan_apply_self, zpow_two, ← pow_two]
  rw [← neg_one_smul K (simpleKInv D q i * e D q i), quantumDividedPower_smul,
    quantumDividedPower_mul_of_mul_eq_sq_smul_mul _ hcomm, smul_smul]

/-- Quantum divided power of `-(Fᵢ Kᵢ)`:
`(-(Fᵢ Kᵢ))^(n) = ((-1)^n qᵢ^(-n(n - 1))) • (Fᵢ^(n) Kᵢ^n)`. -/
theorem quantumDividedPower_neg_f_mul_simpleK (i : ι) (n : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (-(f D q i * simpleK D q i)) n =
      ((-1 : K) ^ n * ((q ^ D.symmetrizer i)⁻¹) ^ (n * (n - 1))) •
        (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n * simpleK D q i ^ n) := by
  have hcomm : simpleK D q i * f D q i =
      ((q ^ D.symmetrizer i)⁻¹) ^ 2 • (f D q i * simpleK D q i) := by
    rw [simpleK_mul_f, D.cartan_apply_self, zpow_neg, zpow_two, ← pow_two, inv_pow]
  rw [← neg_one_smul K (f D q i * simpleK D q i), quantumDividedPower_smul,
    quantumDividedPower_mul_of_mul_eq_sq_smul_mul' _ hcomm, smul_smul]

private theorem antipode_commutator_self (i : ι) :
    MulOpposite.op (-(simpleKInv D q i * e D q i)) *
        MulOpposite.op (-(f D q i * simpleK D q i)) -
      MulOpposite.op (-(f D q i * simpleK D q i)) *
        MulOpposite.op (-(simpleKInv D q i * e D q i)) =
    (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
      (MulOpposite.op (k D q (-D.simpleTorus i)) -
        MulOpposite.op (k D q (- -D.simpleTorus i))) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp [zero_pow (D.symmetrizer_pos i).ne']
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_sub, MulOpposite.unop_mul, MulOpposite.unop_op,
    MulOpposite.unop_smul, neg_mul_neg, neg_neg, ← simpleK_def, ← simpleKInv_def]
  have hqᵢ : q ^ D.symmetrizer i ≠ 0 := pow_ne_zero _ hq
  have hconj : simpleKInv D q i * e D q i * (f D q i * simpleK D q i) = e D q i * f D q i := by
    rw [simpleKInv_mul_e, smul_mul_assoc, mul_assoc, ← mul_assoc (simpleKInv D q i),
      simpleKInv_mul_f, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc (f D q i),
      simpleKInv_mul_simpleK, mul_one, ← zpow_add₀ hqᵢ, neg_add_cancel, zpow_zero, one_smul]
  have hmid : f D q i * simpleK D q i * (simpleKInv D q i * e D q i) = f D q i * e D q i := by
    rw [mul_assoc (f D q i), simpleK_mul_simpleKInv_assoc]
  rw [hmid, hconj, ← neg_sub (e D q i * f D q i), e_mul_f_sub_f_mul_e_self, ← smul_neg, neg_sub]

private theorem antipode_commutator_ne {i j : ι} (hij : i ≠ j) :
    MulOpposite.op (-(simpleKInv D q i * e D q i)) *
        MulOpposite.op (-(f D q j * simpleK D q j)) -
      MulOpposite.op (-(f D q j * simpleK D q j)) *
        MulOpposite.op (-(simpleKInv D q i * e D q i)) = 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_sub, MulOpposite.unop_mul, MulOpposite.unop_op,
    MulOpposite.unop_zero, neg_mul_neg]
  have hqᵢ : q ^ D.symmetrizer i ≠ 0 := pow_ne_zero _ hq
  have hkj_ei : simpleK D q j * e D q i =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (e D q i * simpleK D q j) := by
    rw [simpleK_mul_e, ← zpow_natCast q, ← zpow_mul, D.symmetrizer_mul_cartan j i, zpow_mul,
      zpow_natCast]
  calc f D q j * simpleK D q j * (simpleKInv D q i * e D q i) -
        simpleKInv D q i * e D q i * (f D q j * simpleK D q j)
      = (f D q j * simpleKInv D q i) * (simpleK D q j * e D q i) -
          simpleKInv D q i * (e D q i * f D q j) * simpleK D q j := by
        rw [mul_assoc (f D q j), ← mul_assoc (simpleK D q j),
          (commute_simpleK_simpleKInv D q j i).eq, mul_assoc (simpleKInv D q i),
          ← mul_assoc (f D q j), mul_assoc (simpleKInv D q i) (e D q i), ← mul_assoc (e D q i),
          ← mul_assoc (simpleKInv D q i)]
    _ = 0 := by
        rw [f_mul_simpleKInv, hkj_ei, smul_mul_smul_comm, ← zpow_add₀ hqᵢ, neg_add_cancel,
          zpow_zero, one_smul, mul_assoc (simpleKInv D q i), ← mul_assoc (f D q j),
          ← mul_assoc (simpleKInv D q i), (commute_e_f D q hij).eq, sub_self]

private theorem antipode_serre_e_word (i j : ι) (r s : ℕ) :
    (simpleKInv D q i ^ s * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) s) *
        (simpleKInv D q j * e D q j) *
        (simpleKInv D q i ^ r * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r) =
      ((q ^ D.symmetrizer i) ^ ((s : ℤ) * D.cartan i j) *
        (q ^ D.symmetrizer i) ^ ((r : ℤ) * D.cartan i j) *
        (q ^ D.symmetrizer i) ^ (2 * (s : ℤ) * (r : ℤ))) •
        (simpleKInv D q j * simpleKInv D q i ^ (s + r) *
          (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) s * e D q j *
            quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r)) := by
  have hedps_kj :
      quantumDividedPower (q ^ D.symmetrizer i) (e D q i) s * simpleKInv D q j =
        (q ^ D.symmetrizer i) ^ ((s : ℤ) * D.cartan i j) •
          (simpleKInv D q j * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) s) := by
    have h1 : e D q i * simpleKInv D q j =
        (q ^ D.symmetrizer i) ^ D.cartan i j • (simpleKInv D q j * e D q i) := by
      rw [e_mul_simpleKInv, ← zpow_natCast q, ← zpow_mul, D.symmetrizer_mul_cartan j i, zpow_mul,
        zpow_natCast]
    rw [quantumDividedPower_mul_of_mul_eq_smul_mul _ h1 s, ← zpow_natCast _ s, ← zpow_mul,
      mul_comm _ (s : ℤ)]
  have hedps_kir :
      quantumDividedPower (q ^ D.symmetrizer i) (e D q i) s * simpleKInv D q i ^ r =
        (q ^ D.symmetrizer i) ^ (2 * (s : ℤ) * (r : ℤ)) •
          (simpleKInv D q i ^ r * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) s) := by
    simpa only [D.cartan_apply_self, mul_comm ((s : ℤ) * (r : ℤ)) 2, ← mul_assoc] using
      quantumDividedPower_e_mul_simpleKInv_pow D q (q ^ D.symmetrizer i) i i s r
  calc (simpleKInv D q i ^ s * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) s) *
          (simpleKInv D q j * e D q j) *
          (simpleKInv D q i ^ r * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r)
      = (q ^ D.symmetrizer i) ^ ((s : ℤ) * D.cartan i j) •
          ((simpleKInv D q i ^ s * simpleKInv D q j) *
            quantumDividedPower (q ^ D.symmetrizer i) (e D q i) s *
            (e D q j * simpleKInv D q i ^ r) *
            quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r) := by
        simp only [mul_assoc]
        rw [← mul_assoc (quantumDividedPower _ (e D q i) s) (simpleKInv D q j), hedps_kj]
        simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
    _ = ((q ^ D.symmetrizer i) ^ ((s : ℤ) * D.cartan i j) *
          (q ^ D.symmetrizer i) ^ ((r : ℤ) * D.cartan i j)) •
          (simpleKInv D q j * simpleKInv D q i ^ s *
            (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) s * simpleKInv D q i ^ r) *
            e D q j * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r) := by
        rw [((commute_simpleKInv_simpleKInv D q i j).pow_left s).eq, e_mul_simpleKInv_pow]
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
    _ = _ := by
        rw [hedps_kir]
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc]
        rw [mul_assoc (simpleKInv D q j), ← pow_add,
          mul_assoc (simpleKInv D q j * simpleKInv D q i ^ (s + r)),
          mul_assoc (simpleKInv D q j * simpleKInv D q i ^ (s + r))]

private theorem antipode_serre_e_scalar {i j : ι} (hij : i ≠ j) (hq : q ≠ 0) {r : ℕ}
    (hr : r ≤ D.serreLength i j) :
    -((-1 : K) ^ r *
        (((-1 : K) ^ (D.serreLength i j - r) *
            (q ^ D.symmetrizer i) ^ ((D.serreLength i j - r) * (D.serreLength i j - r - 1))) *
          ((-1 : K) ^ r * (q ^ D.symmetrizer i) ^ (r * (r - 1))) *
          ((q ^ D.symmetrizer i) ^ (((D.serreLength i j - r : ℕ) : ℤ) * D.cartan i j) *
            (q ^ D.symmetrizer i) ^ ((r : ℤ) * D.cartan i j) *
            (q ^ D.symmetrizer i) ^ (2 * ((D.serreLength i j - r : ℕ) : ℤ) * (r : ℤ))))) =
      -(((-1 : K) ^ (D.serreLength i j - r))) := by
  set m := D.serreLength i j
  set s := m - r
  set qᵢ := q ^ D.symmetrizer i
  have hqᵢ : qᵢ ≠ 0 := pow_ne_zero _ hq
  have hr2 : (-1 : K) ^ r * (-1 : K) ^ r = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hexp : qᵢ ^ (s * (s - 1)) * qᵢ ^ (r * (r - 1)) * qᵢ ^ ((s : ℤ) * D.cartan i j) *
      qᵢ ^ ((r : ℤ) * D.cartan i j) * qᵢ ^ (2 * (s : ℤ) * (r : ℤ)) = 1 := by
    have hcart : D.cartan i j = 1 - (m : ℤ) := by have := D.natCast_serreLength hij; omega
    have hs_sub : ((s * (s - 1) : ℕ) : ℤ) = (s : ℤ) * ((s : ℤ) - 1) := by
      rcases s with _ | s <;> simp
    have hr_sub : ((r * (r - 1) : ℕ) : ℤ) = (r : ℤ) * ((r : ℤ) - 1) := by
      rcases r with _ | r <;> simp
    have hrs : (r : ℤ) + (s : ℤ) = (m : ℤ) := by exact_mod_cast Nat.add_sub_of_le hr
    rw [← zpow_natCast qᵢ (s * (s - 1)), ← zpow_natCast qᵢ (r * (r - 1)), hs_sub, hr_sub,
      ← zpow_add₀ hqᵢ, ← zpow_add₀ hqᵢ, ← zpow_add₀ hqᵢ, ← zpow_add₀ hqᵢ, hcart, ← hrs]
    convert zpow_zero qᵢ using 2
    ring
  calc _ = -(((-1 : K) ^ r * (-1 : K) ^ r) * (-1 : K) ^ s *
            (qᵢ ^ (s * (s - 1)) * qᵢ ^ (r * (r - 1)) * qᵢ ^ ((s : ℤ) * D.cartan i j) *
              qᵢ ^ ((r : ℤ) * D.cartan i j) * qᵢ ^ (2 * (s : ℤ) * (r : ℤ)))) := by ring
    _ = -((-1 : K) ^ s) := by rw [hr2, hexp, one_mul, mul_one]

private theorem antipode_serre_e_term {i j : ι} (hij : i ≠ j) (hq : q ≠ 0) {r : ℕ}
    (hr : r ≤ D.serreLength i j) :
    MulOpposite.unop
      ((-1 : K) ^ r •
        (quantumDividedPower (q ^ D.symmetrizer i)
            (MulOpposite.op (-(simpleKInv D q i * e D q i))) r *
          MulOpposite.op (-(simpleKInv D q j * e D q j)) *
          quantumDividedPower (q ^ D.symmetrizer i)
            (MulOpposite.op (-(simpleKInv D q i * e D q i))) (D.serreLength i j - r))) =
      -(simpleKInv D q j * simpleKInv D q i ^ D.serreLength i j *
        ((-1 : K) ^ (D.serreLength i j - r) •
          (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (D.serreLength i j - r) *
            e D q j * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r))) := by
  simp only [MulOpposite.unop_smul, MulOpposite.unop_mul, unop_quantumDividedPower,
    MulOpposite.unop_op]
  rw [quantumDividedPower_neg_simpleKInv_mul_e D q i (D.serreLength i j - r),
    quantumDividedPower_neg_simpleKInv_mul_e D q i r, neg_mul, mul_neg, smul_neg, ← neg_smul]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [← mul_assoc (simpleKInv D q i ^ _ * _), antipode_serre_e_word D q i j r,
    Nat.sub_add_cancel hr, smul_smul, ← neg_smul]
  congr 1
  exact (by ring : _ = _).trans (antipode_serre_e_scalar D q hij hq hr)

private theorem antipode_serre_e {i j : ι} (hij : i ≠ j) :
    serreSum D q (fun l => MulOpposite.op (-(simpleKInv D q l * e D q l))) i j = 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp [serreSum_def]
  apply MulOpposite.opAddEquiv.symm.injective
  rw [serreSum_def, map_sum, map_zero]
  have hcongr : ∑ r ∈ range (D.serreLength i j + 1),
      (MulOpposite.opAddEquiv.symm) ((-1 : K) ^ r •
        (quantumDividedPower (q ^ D.symmetrizer i)
            (MulOpposite.op (-(simpleKInv D q i * e D q i))) r *
          MulOpposite.op (-(simpleKInv D q j * e D q j)) *
          quantumDividedPower (q ^ D.symmetrizer i)
            (MulOpposite.op (-(simpleKInv D q i * e D q i))) (D.serreLength i j - r))) =
      -(simpleKInv D q j * simpleKInv D q i ^ D.serreLength i j *
        ∑ r ∈ range (D.serreLength i j + 1),
          (-1 : K) ^ (D.serreLength i j - r) •
            (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (D.serreLength i j - r) *
              e D q j * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r)) := by
    rw [mul_sum, ← sum_neg_distrib]
    exact sum_congr rfl fun r hr =>
      antipode_serre_e_term D q hij hq (Nat.lt_succ_iff.mp (mem_range.mp hr))
  rw [hcongr, ← sum_range_reflect]
  have hrefl : ∑ x ∈ range (D.serreLength i j + 1),
      (-1 : K) ^ (D.serreLength i j - (D.serreLength i j + 1 - 1 - x)) •
        (quantumDividedPower (q ^ D.symmetrizer i) (e D q i)
            (D.serreLength i j - (D.serreLength i j + 1 - 1 - x)) * e D q j *
          quantumDividedPower (q ^ D.symmetrizer i) (e D q i)
            (D.serreLength i j + 1 - 1 - x)) =
      serreSum D q (e D q) i j := by
    rw [serreSum_def]
    refine sum_congr rfl fun x hx => ?_
    have hxm : x ≤ D.serreLength i j := Nat.lt_succ_iff.mp (mem_range.mp hx)
    simp only [Nat.add_succ_sub_one, add_zero, Nat.sub_sub_self hxm]
  rw [hrefl, serreE_eq_zero D q hij, mul_zero, neg_zero]

private theorem antipode_serre_f {i j : ι} (hij : i ≠ j) :
    serreSum D q (fun l => MulOpposite.op (-(f D q l * simpleK D q l))) i j = 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp [serreSum_def]
  let ωop : (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ ≃ₐ[K] (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ :=
    AlgEquiv.op (chevalleyInvolution D q)
  have hrel : (fun l => MulOpposite.op (-(f D q l * simpleK D q l))) =
      fun l => (q ^ D.symmetrizer l) ^ (2 : ℤ) •
        ωop (MulOpposite.op (-(simpleKInv D q l * e D q l))) := by
    ext l
    have hql : q ^ D.symmetrizer l ≠ 0 := pow_ne_zero _ hq
    apply MulOpposite.unop_injective
    simp only [ωop, AlgEquiv.op_apply_apply, MulOpposite.unop_smul, MulOpposite.unop_op, map_neg,
      map_mul, simpleKInv_def, chevalleyInvolution_k, neg_neg, chevalleyInvolution_e, ← simpleK_def,
      simpleK_mul_f, D.cartan_apply_self, smul_neg, smul_smul, ← zpow_add₀ hql, add_neg_cancel,
      zpow_zero, one_smul]
  rw [hrel, serreSum_smul, ← map_serreSum ωop D q, antipode_serre_e D q hij, map_zero, smul_zero]

private noncomputable def antipodeTuple :
    GeneratorTuple D q (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ where
  e i := MulOpposite.op (-(simpleKInv D q i * e D q i))
  f i := MulOpposite.op (-(f D q i * simpleK D q i))
  k y := MulOpposite.op (k D q (-y))
  k_zero := by simp
  k_mul_k y z := by
    apply MulOpposite.unop_injective
    rw [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_op, MulOpposite.unop_op,
      k_mul_k, neg_add_rev]
  conjugate_e y i := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul, neg_neg,
      mul_neg, neg_mul, simpleKInv_def, mul_assoc]
    rw [← mul_assoc (k D q y), (commute_k_k D q y (-D.simpleTorus i)).eq,
      mul_assoc (k D q (-D.simpleTorus i)), ← mul_assoc (k D q y), k_mul_e_mul_k_neg,
      mul_smul_comm, smul_neg]
  conjugate_f y i := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul, neg_neg,
      mul_neg, neg_mul, simpleK_def, mul_assoc]
    rw [(commute_k_k D q (D.simpleTorus i) (-y)).eq, ← mul_assoc (f D q i),
      ← mul_assoc (k D q y), ← mul_assoc (k D q y), k_mul_f_mul_k_neg, smul_mul_assoc, smul_neg]
  commutator_self := antipode_commutator_self D q
  commutator_ne := antipode_commutator_ne D q
  serre_e := antipode_serre_e D q
  serre_f := antipode_serre_f D q

/-- The antipode `S : U_q(D) →ₐ[K] U_q(D)ᵐᵒᵖ` as an algebra homomorphism into the opposite
algebra, defined unconditionally for every parameter `q : K`. -/
noncomputable def antipodeOp :
    QuantizedEnvelopingAlgebra D q →ₐ[K] (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ :=
  lift (antipodeTuple D q)

/-- `S(Eᵢ) = op(-(Kᵢ⁻¹ Eᵢ))`. -/
@[simp]
theorem antipodeOp_e (i : ι) :
    antipodeOp D q (e D q i) = MulOpposite.op (-(simpleKInv D q i * e D q i)) := by
  simp [antipodeOp, antipodeTuple]

/-- `S(Fᵢ) = op(-(Fᵢ Kᵢ))`. -/
@[simp]
theorem antipodeOp_f (i : ι) :
    antipodeOp D q (f D q i) = MulOpposite.op (-(f D q i * simpleK D q i)) := by
  simp [antipodeOp, antipodeTuple]

/-- `S(K_y) = op(K_(-y))`. -/
@[simp]
theorem antipodeOp_k (y : Y) :
    antipodeOp D q (k D q y) = MulOpposite.op (k D q (-y)) := by
  simp [antipodeOp, antipodeTuple]

/-- `S(Kᵢ) = op(Kᵢ⁻¹)`. -/
@[simp]
theorem antipodeOp_simpleK (i : ι) :
    antipodeOp D q (simpleK D q i) = MulOpposite.op (simpleKInv D q i) := by
  simp [simpleK_def, simpleKInv_def]

/-- `S(Kᵢ⁻¹) = op(Kᵢ)`. -/
@[simp]
theorem antipodeOp_simpleKInv (i : ι) :
    antipodeOp D q (simpleKInv D q i) = MulOpposite.op (simpleK D q i) := by
  simp [simpleK_def, simpleKInv_def]

open Classical in
private noncomputable def antipodeSqUnit (D : CartanDatum ι X Y) (q : K) (i : ι) : Kˣ :=
  if hq : q = 0 then 1 else (Units.mk0 (q ^ D.symmetrizer i) (pow_ne_zero _ hq))⁻¹ ^ 2

/-- The square `S²` of the antipode as an algebra automorphism of `U_q(D)`, rescaling `Eᵢ` by
`qᵢ⁻²` and `Fᵢ` by `qᵢ²` and fixing `K_y`. -/
noncomputable def antipodeSqEquiv :
    QuantizedEnvelopingAlgebra D q ≃ₐ[K] QuantizedEnvelopingAlgebra D q :=
  rescale D q (antipodeSqUnit D q)

/-- `S²(Eᵢ) = qᵢ⁻² • Eᵢ` for every `q : K`. -/
@[simp]
theorem antipodeSqEquiv_e (i : ι) :
    antipodeSqEquiv D q (e D q i) = ((q ^ D.symmetrizer i)⁻¹ ^ 2) • e D q i := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · simp [antipodeSqEquiv, antipodeSqUnit, hq]

/-- `S²(Fᵢ) = qᵢ² • Fᵢ` for every `q : K`. -/
@[simp]
theorem antipodeSqEquiv_f (i : ι) :
    antipodeSqEquiv D q (f D q i) = (q ^ D.symmetrizer i) ^ 2 • f D q i := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · simp [antipodeSqEquiv, antipodeSqUnit, hq, inv_pow]

/-- `S²(K_y) = K_y`. -/
@[simp]
theorem antipodeSqEquiv_k (y : Y) :
    antipodeSqEquiv D q (k D q y) = k D q y := by
  simp [antipodeSqEquiv]

private theorem opComm_antipodeOp_comp_antipodeOp :
    (AlgHom.opComm (antipodeOp D q)).comp (antipodeOp D q) = (antipodeSqEquiv D q).toAlgHom := by
  apply hom_ext
  · intro i
    simp only [AlgHom.coe_comp, Function.comp_apply, antipodeOp_e, MulOpposite.op_neg,
      MulOpposite.op_mul, AlgHom.opComm_apply_apply, MulOpposite.unop_neg, MulOpposite.unop_mul,
      MulOpposite.unop_op, map_neg, map_mul, antipodeOp_simpleKInv, neg_mul, neg_neg]
    rw [simpleKInv_mul_e, D.cartan_apply_self, zpow_neg, zpow_two, ← pow_two, smul_mul_assoc,
      mul_assoc, simpleKInv_mul_simpleK, mul_one]
    simp [inv_pow]
  · intro i
    simp only [AlgHom.coe_comp, Function.comp_apply, antipodeOp_f, MulOpposite.op_neg,
      MulOpposite.op_mul, AlgHom.opComm_apply_apply, MulOpposite.unop_neg, MulOpposite.unop_mul,
      MulOpposite.unop_op, map_neg, map_mul, antipodeOp_simpleK, mul_neg, neg_neg]
    rw [← mul_assoc, simpleKInv_mul_f, D.cartan_apply_self, zpow_two, ← pow_two, smul_mul_assoc,
      mul_assoc, simpleKInv_mul_simpleK, mul_one]
    simp
  · intro y
    simp

private theorem antipodeOp_bijective : Function.Bijective (antipodeOp D q) := by
  have hcomp : Function.Bijective
      ((AlgHom.opComm (antipodeOp D q)) ∘ (antipodeOp D q)) := by
    simpa only [← AlgHom.coe_comp, opComm_antipodeOp_comp_antipodeOp, AlgEquiv.coe_toAlgHom] using
      (antipodeSqEquiv D q).bijective
  refine ⟨hcomp.1.of_comp, fun y => ?_⟩
  obtain ⟨z, hz⟩ := hcomp.2.of_comp y.unop
  refine ⟨z.unop, MulOpposite.unop_injective ?_⟩
  simpa using hz

/-- The antipode as an algebra equivalence `U_q(D) ≃ₐ[K] U_q(D)ᵐᵒᵖ` onto the opposite algebra. -/
noncomputable def antipodeEquiv :
    QuantizedEnvelopingAlgebra D q ≃ₐ[K] (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ :=
  AlgEquiv.ofBijective (antipodeOp D q) (antipodeOp_bijective D q)

/-- The underlying algebra homomorphism of `antipodeEquiv` is `antipodeOp`. -/
@[simp]
theorem antipodeEquiv_toAlgHom : (antipodeEquiv D q).toAlgHom = antipodeOp D q := (rfl)

/-- `antipodeEquiv` agrees pointwise with `antipodeOp`. -/
@[simp]
theorem antipodeEquiv_apply (x : QuantizedEnvelopingAlgebra D q) :
    antipodeEquiv D q x = antipodeOp D q x := (rfl)

/-- The antipode as a `K`-linear equivalence `U_q(D) ≃ₗ[K] U_q(D)`. -/
noncomputable def antipodeLinearEquiv :
    QuantizedEnvelopingAlgebra D q ≃ₗ[K] QuantizedEnvelopingAlgebra D q :=
  (antipodeEquiv D q).toLinearEquiv.trans (MulOpposite.opLinearEquiv K).symm

/-- `antipodeLinearEquiv` unwraps the `MulOpposite` value of `antipodeOp`. -/
theorem antipodeLinearEquiv_apply (x : QuantizedEnvelopingAlgebra D q) :
    antipodeLinearEquiv D q x = (antipodeOp D q x).unop := (rfl)

/-- `S(1) = 1`. -/
@[simp]
theorem antipodeLinearEquiv_one : antipodeLinearEquiv D q 1 = 1 := by
  simp [antipodeLinearEquiv_apply]

/-- The antipode reverses multiplication: `S(x * y) = S(y) * S(x)`. -/
theorem antipodeLinearEquiv_mul (x y : QuantizedEnvelopingAlgebra D q) :
    antipodeLinearEquiv D q (x * y) =
      antipodeLinearEquiv D q y * antipodeLinearEquiv D q x := by
  simp [antipodeLinearEquiv_apply]

/-- `S(Eᵢ) = -(Kᵢ⁻¹ Eᵢ)`. -/
@[simp]
theorem antipodeLinearEquiv_e (i : ι) :
    antipodeLinearEquiv D q (e D q i) = -(simpleKInv D q i * e D q i) := by
  simp [antipodeLinearEquiv_apply]

/-- `S(Fᵢ) = -(Fᵢ Kᵢ)`. -/
@[simp]
theorem antipodeLinearEquiv_f (i : ι) :
    antipodeLinearEquiv D q (f D q i) = -(f D q i * simpleK D q i) := by
  simp [antipodeLinearEquiv_apply]

/-- `S(K_y) = K_(-y)`. -/
@[simp]
theorem antipodeLinearEquiv_k (y : Y) :
    antipodeLinearEquiv D q (k D q y) = k D q (-y) := by
  simp [antipodeLinearEquiv_apply]

/-- `S(Kᵢ) = Kᵢ⁻¹`. -/
@[simp]
theorem antipodeLinearEquiv_simpleK (i : ι) :
    antipodeLinearEquiv D q (simpleK D q i) = simpleKInv D q i := by
  simp [simpleK_def, simpleKInv_def]

/-- `S(Kᵢ⁻¹) = Kᵢ`. -/
@[simp]
theorem antipodeLinearEquiv_simpleKInv (i : ι) :
    antipodeLinearEquiv D q (simpleKInv D q i) = simpleK D q i := by
  simp [simpleK_def, simpleKInv_def]

/-- Applying `antipodeLinearEquiv` twice agrees with `antipodeSqEquiv`. -/
theorem antipodeLinearEquiv_antipodeLinearEquiv (x : QuantizedEnvelopingAlgebra D q) :
    antipodeLinearEquiv D q (antipodeLinearEquiv D q x) = antipodeSqEquiv D q x := by
  simpa [antipodeLinearEquiv_apply] using
    AlgHom.congr_fun (opComm_antipodeOp_comp_antipodeOp D q) x

/-- `S²(Eᵢ) = qᵢ⁻² • Eᵢ` for every `q : K`. -/
theorem antipodeLinearEquiv_antipodeLinearEquiv_e (i : ι) :
    antipodeLinearEquiv D q (antipodeLinearEquiv D q (e D q i)) =
      ((q ^ D.symmetrizer i)⁻¹ ^ 2) • e D q i := by
  rw [antipodeLinearEquiv_antipodeLinearEquiv, antipodeSqEquiv_e]

/-- `S²(Fᵢ) = qᵢ² • Fᵢ` for every `q : K`. -/
theorem antipodeLinearEquiv_antipodeLinearEquiv_f (i : ι) :
    antipodeLinearEquiv D q (antipodeLinearEquiv D q (f D q i)) =
      (q ^ D.symmetrizer i) ^ 2 • f D q i := by
  rw [antipodeLinearEquiv_antipodeLinearEquiv, antipodeSqEquiv_f]

/-- `S²(K_y) = K_y`. -/
theorem antipodeLinearEquiv_antipodeLinearEquiv_k (y : Y) :
    antipodeLinearEquiv D q (antipodeLinearEquiv D q (k D q y)) = k D q y := by
  rw [antipodeLinearEquiv_antipodeLinearEquiv, antipodeSqEquiv_k]

/-- `S⁻¹(Eᵢ) = -(Eᵢ Kᵢ⁻¹)`. -/
@[simp]
theorem antipodeLinearEquiv_symm_e (i : ι) :
    (antipodeLinearEquiv D q).symm (e D q i) = -(e D q i * simpleKInv D q i) := by
  rw [LinearEquiv.symm_apply_eq, map_neg, antipodeLinearEquiv_mul, antipodeLinearEquiv_e,
    antipodeLinearEquiv_simpleKInv, mul_neg, neg_neg, simpleK_mul_simpleKInv_assoc]

/-- `S⁻¹(Fᵢ) = -(Kᵢ Fᵢ)`. -/
@[simp]
theorem antipodeLinearEquiv_symm_f (i : ι) :
    (antipodeLinearEquiv D q).symm (f D q i) = -(simpleK D q i * f D q i) := by
  rw [LinearEquiv.symm_apply_eq, map_neg, antipodeLinearEquiv_mul, antipodeLinearEquiv_f,
    antipodeLinearEquiv_simpleK, neg_mul, neg_neg, mul_assoc, simpleK_mul_simpleKInv, mul_one]

/-- `S⁻¹(K_y) = K_(-y)`. -/
@[simp]
theorem antipodeLinearEquiv_symm_k (y : Y) :
    (antipodeLinearEquiv D q).symm (k D q y) = k D q (-y) := by
  rw [LinearEquiv.symm_apply_eq, antipodeLinearEquiv_k, neg_neg]

/-- `S⁻¹(Kᵢ) = Kᵢ⁻¹`. -/
@[simp]
theorem antipodeLinearEquiv_symm_simpleK (i : ι) :
    (antipodeLinearEquiv D q).symm (simpleK D q i) = simpleKInv D q i := by
  simp [simpleK_def, simpleKInv_def]

/-- `S⁻¹(Kᵢ⁻¹) = Kᵢ`. -/
@[simp]
theorem antipodeLinearEquiv_symm_simpleKInv (i : ι) :
    (antipodeLinearEquiv D q).symm (simpleKInv D q i) = simpleK D q i := by
  simp [simpleK_def, simpleKInv_def]

/-- `S⁻¹(op Eᵢ) = -(Eᵢ Kᵢ⁻¹)`. -/
@[simp]
theorem antipodeEquiv_symm_op_e (i : ι) :
    (antipodeEquiv D q).symm (MulOpposite.op (e D q i)) = -(e D q i * simpleKInv D q i) :=
  antipodeLinearEquiv_symm_e D q i

/-- `S⁻¹(op Fᵢ) = -(Kᵢ Fᵢ)`. -/
@[simp]
theorem antipodeEquiv_symm_op_f (i : ι) :
    (antipodeEquiv D q).symm (MulOpposite.op (f D q i)) = -(simpleK D q i * f D q i) :=
  antipodeLinearEquiv_symm_f D q i

/-- `S⁻¹(op K_y) = K_(-y)`. -/
@[simp]
theorem antipodeEquiv_symm_op_k (y : Y) :
    (antipodeEquiv D q).symm (MulOpposite.op (k D q y)) = k D q (-y) :=
  antipodeLinearEquiv_symm_k D q y

/-- **Antipode of raising divided powers**:
`S(Eᵢ^(n)) = ((-1)^n qᵢ^(n(n - 1))) • (Kᵢ^(-n) Eᵢ^(n))` for every `n : ℕ`. -/
theorem antipodeLinearEquiv_quantumDividedPower_e (i : ι) (n : ℕ) :
    antipodeLinearEquiv D q (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) =
      ((-1 : K) ^ n * (q ^ D.symmetrizer i) ^ (n * (n - 1))) •
        (simpleKInv D q i ^ n * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) := by
  rw [antipodeLinearEquiv_apply, map_quantumDividedPower, antipodeOp_e, unop_quantumDividedPower,
    MulOpposite.unop_op, quantumDividedPower_neg_simpleKInv_mul_e]

/-- **Antipode of lowering divided powers**:
`S(Fᵢ^(n)) = ((-1)^n qᵢ^(-n(n - 1))) • (Fᵢ^(n) Kᵢ^n)` for every `n : ℕ`. -/
theorem antipodeLinearEquiv_quantumDividedPower_f (i : ι) (n : ℕ) :
    antipodeLinearEquiv D q (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n) =
      ((-1 : K) ^ n * ((q ^ D.symmetrizer i)⁻¹) ^ (n * (n - 1))) •
        (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n * simpleK D q i ^ n) := by
  rw [antipodeLinearEquiv_apply, map_quantumDividedPower, antipodeOp_f, unop_quantumDividedPower,
    MulOpposite.unop_op, quantumDividedPower_neg_f_mul_simpleK]

end Antipode

section Functoriality

variable {ι X Y X' Y' K : Type*} [AddCommGroup X] [AddCommGroup Y]
  [AddCommGroup X'] [AddCommGroup Y'] [Field K]
  {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'}

/-- `map φ q` intertwines the antipode: `map φ q (S x) = S (map φ q x)`. -/
@[simp]
theorem map_antipodeLinearEquiv (φ : CartanDatum.Hom D D') (q : K)
    (x : QuantizedEnvelopingAlgebra D q) :
    map φ q (antipodeLinearEquiv D q x) = antipodeLinearEquiv D' q (map φ q x) := by
  have hop : (AlgHom.op (map φ q)).comp (antipodeOp D q) =
      (antipodeOp D' q).comp (map φ q) := by
    apply hom_ext <;> intro a <;> simp
  simpa [antipodeLinearEquiv_apply] using
    congrArg MulOpposite.unop (AlgHom.congr_fun hop x)

end Functoriality

end QuantizedEnvelopingAlgebra

end TauCeti
