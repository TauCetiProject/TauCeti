/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantizedEnvelopingAlgebra.Basic
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Algebra.Basic
import TauCeti.QuantumGroups.QuantizedEnvelopingAlgebra.Rescale

/-!
# The antipode of the Drinfeld–Jimbo quantized enveloping algebra

This file constructs the antipode of `TauCeti.QuantizedEnvelopingAlgebra D q` unconditionally for
every Cartan datum `D` and parameter `q` in a field `K`, identifies `S²` with a diagonal rescaling
automorphism to prove bijectivity, computes `S⁻¹` on generators, and establishes the action of `S`
on quantum divided powers and its naturality under `CartanDatum.Hom`.

## Main definitions and results

* `TauCeti.QuantizedEnvelopingAlgebra.antipodeOp`: the antipode `U_q(D) →ₐ[K] U_q(D)ᵐᵒᵖ` sending
  `Eᵢ ↦ op(-(Kᵢ⁻¹ Eᵢ))`, `Fᵢ ↦ op(-(Fᵢ Kᵢ))`, and `K_y ↦ op(K_(-y))`.
* `TauCeti.QuantizedEnvelopingAlgebra.antipodeSqEquiv`, `antipodeEquiv`, `antipodeLinearEquiv`:
  `S²` as an algebra automorphism, `S` as `U_q(D) ≃ₐ[K] U_q(D)ᵐᵒᵖ` and `U_q(D) ≃ₗ[K] U_q(D)`, and
  `S⁻¹` on generators.
* `TauCeti.QuantizedEnvelopingAlgebra.antipodeLinearEquiv_quantumDividedPower_e`,
  `antipodeLinearEquiv_quantumDividedPower_f`, `map_antipodeLinearEquiv`: divided-power formulas
  and naturality under `CartanDatum.Hom`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993, §3.3.
* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, AMS, 1996, Ch. 4.
-/

public section

open Finset

namespace TauCeti

namespace QuantizedEnvelopingAlgebra

section Antipode

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
  (D : CartanDatum ι X Y) (q : K)

/-- `(-(Kᵢ⁻¹ Eᵢ))^(n) = ((-1)^n qᵢ^(n(n - 1))) • (Kᵢ^(-n) Eᵢ^(n))`. -/
theorem quantumDividedPower_neg_simpleKInv_mul_e (i : ι) (n : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (-(simpleKInv D q i * e D q i)) n =
      ((-1 : K) ^ n * (q ^ D.symmetrizer i) ^ (n * (n - 1))) •
        (simpleKInv D q i ^ n * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) := by
  have hcomm : e D q i * simpleKInv D q i =
      (q ^ D.symmetrizer i) ^ 2 • (simpleKInv D q i * e D q i) := by
    rw [e_mul_simpleKInv, D.cartan_apply_self, zpow_two, ← pow_two]
  rw [← neg_one_smul K (simpleKInv D q i * e D q i), quantumDividedPower_smul,
    quantumDividedPower_mul_of_mul_eq_sq_smul_mul _ hcomm, smul_smul]

/-- `(-(Fᵢ Kᵢ))^(n) = ((-1)^n qᵢ^(-n(n - 1))) • (Fᵢ^(n) Kᵢ^n)`. -/
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
  have hleft : f D q i * simpleK D q i * (simpleKInv D q i * e D q i) = f D q i * e D q i := by
    simp [mul_assoc]
  have hconj : simpleKInv D q i * e D q i * (f D q i * simpleK D q i) = e D q i * f D q i := by
    have hkf : simpleKInv D q i * (f D q i * simpleK D q i) =
        (q ^ D.symmetrizer i) ^ D.cartan i i • f D q i := by
      rw [← mul_assoc, simpleKInv_mul_f]; simp [mul_assoc]
    calc simpleKInv D q i * e D q i * (f D q i * simpleK D q i)
        = (q ^ D.symmetrizer i) ^ (-D.cartan i i) •
            (e D q i * (simpleKInv D q i * (f D q i * simpleK D q i))) := by
          rw [simpleKInv_mul_e]; simp [mul_assoc]
      _ = e D q i * f D q i := by
          rw [hkf]; simp [smul_smul, hq]
  rw [hleft, hconj, ← neg_sub (e D q i * f D q i), e_mul_f_sub_f_mul_e_self, ← smul_neg, neg_sub]

private theorem antipode_commutator_ne {i j : ι} (hij : i ≠ j) :
    MulOpposite.op (-(simpleKInv D q i * e D q i)) *
        MulOpposite.op (-(f D q j * simpleK D q j)) -
      MulOpposite.op (-(f D q j * simpleK D q j)) *
        MulOpposite.op (-(simpleKInv D q i * e D q i)) = 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_sub, MulOpposite.unop_mul, MulOpposite.unop_op,
    MulOpposite.unop_zero, neg_mul_neg, sub_eq_zero]
  have hkj_ei : simpleK D q j * e D q i =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (e D q i * simpleK D q j) := by
    rw [simpleK_mul_e, zpow_symmetrizer_cartan_comm]
  have hkk : simpleK D q j * (simpleKInv D q i * e D q i) =
      simpleKInv D q i * (simpleK D q j * e D q i) := by
    rw [← mul_assoc, (commute_simpleK_simpleKInv D q j i).eq, mul_assoc]
  calc f D q j * simpleK D q j * (simpleKInv D q i * e D q i)
      = (f D q j * simpleKInv D q i) * (simpleK D q j * e D q i) := by
        rw [mul_assoc, hkk, ← mul_assoc]
    _ = simpleKInv D q i * (f D q j * e D q i) * simpleK D q j := by
        rw [f_mul_simpleKInv, hkj_ei]
        simp [smul_smul, mul_inv_cancel₀ (zpow_ne_zero _ (pow_ne_zero _ hq)), mul_assoc]
    _ = simpleKInv D q i * e D q i * (f D q j * simpleK D q j) := by
        rw [← (commute_e_f D q hij).eq]; simp only [mul_assoc]

private theorem serreNormalizedE_term {i j : ι} (hij : i ≠ j) (hq : q ≠ 0) {r : ℕ}
    (hrm : r ≤ D.serreLength i j) :
    quantumDividedPower (q ^ D.symmetrizer i) (normalizedE D q i) r * normalizedE D q j *
        quantumDividedPower (q ^ D.symmetrizer i) (normalizedE D q i) (D.serreLength i j - r) =
      simpleKInv D q j * simpleKInv D q i ^ D.serreLength i j *
        (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r * e D q j *
          quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (D.serreLength i j - r)) := by
  set m := D.serreLength i j; set s := m - r; set qᵢ := q ^ D.symmetrizer i
  have hqᵢ : qᵢ ≠ 0 := pow_ne_zero _ hq
  have hnorm (n : ℕ) : quantumDividedPower qᵢ (normalizedE D q i) n =
      qᵢ ^ ((n : ℤ) * ((n : ℤ) - 1)) •
        (simpleKInv D q i ^ n * quantumDividedPower qᵢ (e D q i) n) := by
    have hc : e D q i * simpleKInv D q i = qᵢ ^ 2 • (simpleKInv D q i * e D q i) := by
      rw [e_mul_simpleKInv, D.cartan_apply_self, zpow_two, ← pow_two]
    have hn : ((n * (n - 1) : ℕ) : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by rcases n with _ | n <;> simp
    rw [normalizedE_def, quantumDividedPower_mul_of_mul_eq_sq_smul_mul qᵢ hc n,
      ← zpow_natCast qᵢ, hn]
  have hedp_kj : quantumDividedPower qᵢ (e D q i) r * simpleKInv D q j =
      qᵢ ^ (D.cartan i j * (r : ℤ)) • (simpleKInv D q j * quantumDividedPower qᵢ (e D q i) r) := by
    have h1 : e D q i * simpleKInv D q j = qᵢ ^ D.cartan i j • (simpleKInv D q j * e D q i) := by
      rw [e_mul_simpleKInv, zpow_symmetrizer_cartan_comm]
    rw [quantumDividedPower_mul_of_mul_eq_smul_mul qᵢ h1 r, ← zpow_natCast _ r, ← zpow_mul]
  have hej_kis : e D q j * simpleKInv D q i ^ s =
      qᵢ ^ (D.cartan i j * (s : ℤ)) • (simpleKInv D q i ^ s * e D q j) := by
    rw [mul_pow_of_mul_eq_smul_mul (e_mul_simpleKInv D q i j) s, ← zpow_natCast _ s, ← zpow_mul]
  have hedp_kis : quantumDividedPower qᵢ (e D q i) r * simpleKInv D q i ^ s =
      qᵢ ^ (2 * (s : ℤ) * (r : ℤ)) •
        (simpleKInv D q i ^ s * quantumDividedPower qᵢ (e D q i) r) := by
    have h1 := mul_pow_of_mul_eq_smul_mul (e_mul_simpleKInv D q i i) s
    rw [D.cartan_apply_self, ← zpow_natCast _ s, ← zpow_mul] at h1
    rw [quantumDividedPower_mul_of_mul_eq_smul_mul qᵢ h1 r, ← zpow_natCast _ r, ← zpow_mul]
  rw [hnorm r, hnorm s, normalizedE_def]
  simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
  rw [← mul_assoc (quantumDividedPower qᵢ (e D q i) r) (simpleKInv D q j), hedp_kj]
  simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
  rw [← mul_assoc (e D q j) (simpleKInv D q i ^ s), hej_kis]
  simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
  rw [← mul_assoc (quantumDividedPower qᵢ (e D q i) r) (simpleKInv D q i ^ s), hedp_kis]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← zpow_add₀ hqᵢ, ← mul_assoc]
  rw [((commute_simpleKInv_simpleKInv D q i j).pow_left r).eq, mul_assoc (simpleKInv D q j),
    ← pow_add, Nat.add_sub_of_le hrm]
  have hcart : D.cartan i j = 1 - (m : ℤ) := by have := D.natCast_serreLength hij; omega
  have hrs : (m : ℤ) = (r : ℤ) + (s : ℤ) := by omega
  have hexp : (s : ℤ) * ((s : ℤ) - 1) + ((r : ℤ) * ((r : ℤ) - 1) + (D.cartan i j * (r : ℤ) +
      (D.cartan i j * (s : ℤ) + 2 * (s : ℤ) * (r : ℤ)))) = 0 := by rw [hcart, hrs]; ring
  rw [hexp, zpow_zero, one_smul]

/-- The normalized raising operators `eᵢ = Kᵢ⁻¹ Eᵢ` satisfy the quantum Serre relations. -/
theorem serreNormalizedE_eq_zero {i j : ι} (hij : i ≠ j) :
    serreSum D q (normalizedE D q) i j = 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp [serreSum_def, normalizedE_def]
  have hcongr : serreSum D q (normalizedE D q) i j =
      simpleKInv D q j * simpleKInv D q i ^ D.serreLength i j * serreSum D q (e D q) i j := by
    rw [serreSum_def, serreSum_def, mul_sum]
    refine sum_congr rfl fun r hr => ?_
    rw [serreNormalizedE_term D q hij hq (Nat.lt_succ_iff.mp (mem_range.mp hr)), mul_smul_comm]
  rw [hcongr, serreE_eq_zero D q hij, mul_zero]

private theorem antipode_serre_e {i j : ι} (hij : i ≠ j) :
    serreSum D q (fun l => MulOpposite.op (-(simpleKInv D q l * e D q l))) i j = 0 := by
  apply MulOpposite.unop_injective
  have hneg : (fun l => -(simpleKInv D q l * e D q l)) =
      fun l => (-1 : K) • normalizedE D q l := by ext l; simp [normalizedE_def]
  rw [unop_serreSum, hneg, serreSum_smul, serreNormalizedE_eq_zero D q hij,
    smul_zero, smul_zero, MulOpposite.unop_zero]

private theorem antipode_serre_f {i j : ι} (hij : i ≠ j) :
    serreSum D q (fun l => MulOpposite.op (-(f D q l * simpleK D q l))) i j = 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp [serreSum_def]
  let ωop := AlgEquiv.op (chevalleyInvolution D q)
  have hrel : (fun l => MulOpposite.op (-(f D q l * simpleK D q l))) =
      fun l => (q ^ D.symmetrizer l) ^ (2 : ℤ) •
        ωop (MulOpposite.op (-(simpleKInv D q l * e D q l))) := by
    ext l; apply MulOpposite.unop_injective
    simp only [ωop, AlgEquiv.op_apply_apply, MulOpposite.unop_smul, MulOpposite.unop_op, map_neg,
      map_mul, simpleKInv_def, chevalleyInvolution_k, neg_neg, chevalleyInvolution_e, ← simpleK_def,
      simpleK_mul_f, D.cartan_apply_self, smul_neg, smul_smul, ← zpow_add₀ (pow_ne_zero _ hq),
      add_neg_cancel, zpow_zero, one_smul]
  rw [hrel, serreSum_smul, ← map_serreSum ωop D q, antipode_serre_e D q hij, map_zero, smul_zero]

private noncomputable def antipodeTuple :
    GeneratorTuple D q (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ where
  e i := MulOpposite.op (-(simpleKInv D q i * e D q i))
  f i := MulOpposite.op (-(f D q i * simpleK D q i))
  k y := MulOpposite.op (k D q (-y))
  k_zero := by simp
  k_mul_k y z := MulOpposite.unop_injective <| by simp [neg_add_rev]
  conjugate_e y i := MulOpposite.unop_injective <| by
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul, neg_neg,
      mul_neg, neg_mul, simpleKInv_def, mul_assoc]
    rw [← mul_assoc (k D q y), (commute_k_k D q y (-D.simpleTorus i)).eq,
      mul_assoc (k D q (-D.simpleTorus i)), ← mul_assoc (k D q y), k_mul_e_mul_k_neg,
      mul_smul_comm, smul_neg]
  conjugate_f y i := MulOpposite.unop_injective <| by
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

@[simp] theorem antipodeOp_e (i : ι) :
    antipodeOp D q (e D q i) = MulOpposite.op (-(simpleKInv D q i * e D q i)) :=
  lift_e (antipodeTuple D q) i
@[simp] theorem antipodeOp_f (i : ι) :
    antipodeOp D q (f D q i) = MulOpposite.op (-(f D q i * simpleK D q i)) :=
  lift_f (antipodeTuple D q) i
@[simp] theorem antipodeOp_k (y : Y) : antipodeOp D q (k D q y) = MulOpposite.op (k D q (-y)) :=
  lift_k (antipodeTuple D q) y
@[simp] theorem antipodeOp_simpleK (i : ι) :
    antipodeOp D q (simpleK D q i) = MulOpposite.op (simpleKInv D q i) := by
  simp [simpleK_def, simpleKInv_def]
@[simp] theorem antipodeOp_simpleKInv (i : ι) :
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

@[simp] theorem antipodeSqEquiv_e (i : ι) :
    antipodeSqEquiv D q (e D q i) = ((q ^ D.symmetrizer i)⁻¹ ^ 2) • e D q i := by
  rcases eq_or_ne q 0 with rfl | hq <;> simp [antipodeSqEquiv, antipodeSqUnit, *]
@[simp] theorem antipodeSqEquiv_f (i : ι) :
    antipodeSqEquiv D q (f D q i) = (q ^ D.symmetrizer i) ^ 2 • f D q i := by
  rcases eq_or_ne q 0 with rfl | hq <;> simp [antipodeSqEquiv, antipodeSqUnit, inv_pow, *]
@[simp] theorem antipodeSqEquiv_k (y : Y) : antipodeSqEquiv D q (k D q y) = k D q y := by
  simp [antipodeSqEquiv]

private theorem opComm_antipodeOp_comp_antipodeOp :
    (AlgHom.opComm (antipodeOp D q)).comp (antipodeOp D q) = (antipodeSqEquiv D q).toAlgHom := by
  apply hom_ext <;> intro x <;>
    simp only [AlgHom.coe_comp, Function.comp_apply, antipodeOp_e, antipodeOp_f, antipodeOp_k,
      MulOpposite.op_neg, MulOpposite.op_mul, AlgHom.opComm_apply_apply, MulOpposite.unop_neg,
      MulOpposite.unop_mul, MulOpposite.unop_op, map_neg, map_mul, antipodeOp_simpleKInv,
      antipodeOp_simpleK, neg_mul, mul_neg, neg_neg, AlgEquiv.coe_toAlgHom, antipodeSqEquiv_k]
  · rw [simpleKInv_mul_e, D.cartan_apply_self, zpow_neg, zpow_two, ← pow_two, smul_mul_assoc,
      mul_assoc, simpleKInv_mul_simpleK, mul_one]
    simp [inv_pow]
  · rw [← mul_assoc, simpleKInv_mul_f, D.cartan_apply_self, zpow_two, ← pow_two, smul_mul_assoc,
      mul_assoc, simpleKInv_mul_simpleK, mul_one]
    simp

private theorem antipodeOp_bijective : Function.Bijective (antipodeOp D q) := by
  have hcomp : Function.Bijective ((AlgHom.opComm (antipodeOp D q)) ∘ (antipodeOp D q)) := by
    simpa only [← AlgHom.coe_comp, opComm_antipodeOp_comp_antipodeOp, AlgEquiv.coe_toAlgHom] using
      (antipodeSqEquiv D q).bijective
  refine ⟨hcomp.1.of_comp, fun y => ?_⟩
  obtain ⟨z, hz⟩ := hcomp.2.of_comp y.unop
  exact ⟨z.unop, MulOpposite.unop_injective (by simpa using hz)⟩

/-- The antipode as an algebra equivalence `U_q(D) ≃ₐ[K] U_q(D)ᵐᵒᵖ` onto the opposite algebra. -/
noncomputable def antipodeEquiv :
    QuantizedEnvelopingAlgebra D q ≃ₐ[K] (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ :=
  AlgEquiv.ofBijective (antipodeOp D q) (antipodeOp_bijective D q)

@[simp] theorem antipodeEquiv_toAlgHom : (antipodeEquiv D q).toAlgHom = antipodeOp D q := (rfl)
@[simp] theorem antipodeEquiv_apply (x : QuantizedEnvelopingAlgebra D q) :
    antipodeEquiv D q x = antipodeOp D q x := (rfl)

/-- The antipode as a `K`-linear equivalence `U_q(D) ≃ₗ[K] U_q(D)`. -/
noncomputable def antipodeLinearEquiv :
    QuantizedEnvelopingAlgebra D q ≃ₗ[K] QuantizedEnvelopingAlgebra D q :=
  (antipodeEquiv D q).toLinearEquiv.trans (MulOpposite.opLinearEquiv K).symm

theorem antipodeLinearEquiv_apply (x : QuantizedEnvelopingAlgebra D q) :
    antipodeLinearEquiv D q x = (antipodeOp D q x).unop := (rfl)
@[simp] theorem antipodeEquiv_symm_op (x : QuantizedEnvelopingAlgebra D q) :
    (antipodeEquiv D q).symm (MulOpposite.op x) = (antipodeLinearEquiv D q).symm x := (rfl)
@[simp] theorem antipodeLinearEquiv_one : antipodeLinearEquiv D q 1 = 1 := by
  simp [antipodeLinearEquiv_apply]
/-- The antipode is anti-multiplicative: `S (x * y) = S y * S x`. -/
@[simp] theorem antipodeLinearEquiv_mul (x y : QuantizedEnvelopingAlgebra D q) :
    antipodeLinearEquiv D q (x * y) = antipodeLinearEquiv D q y * antipodeLinearEquiv D q x := by
  simp [antipodeLinearEquiv_apply]
@[simp] theorem antipodeLinearEquiv_e (i : ι) :
    antipodeLinearEquiv D q (e D q i) = -(simpleKInv D q i * e D q i) := by
  simp [antipodeLinearEquiv_apply]
@[simp] theorem antipodeLinearEquiv_f (i : ι) :
    antipodeLinearEquiv D q (f D q i) = -(f D q i * simpleK D q i) := by
  simp [antipodeLinearEquiv_apply]
@[simp] theorem antipodeLinearEquiv_k (y : Y) :
    antipodeLinearEquiv D q (k D q y) = k D q (-y) := by simp [antipodeLinearEquiv_apply]
@[simp] theorem antipodeLinearEquiv_simpleK (i : ι) :
    antipodeLinearEquiv D q (simpleK D q i) = simpleKInv D q i := by
  simp [simpleK_def, simpleKInv_def]
@[simp] theorem antipodeLinearEquiv_simpleKInv (i : ι) :
    antipodeLinearEquiv D q (simpleKInv D q i) = simpleK D q i := by
  simp [simpleK_def, simpleKInv_def]
theorem antipodeLinearEquiv_e_eq_neg_normalizedE (i : ι) :
    antipodeLinearEquiv D q (e D q i) = -normalizedE D q i := by
  rw [antipodeLinearEquiv_e, normalizedE_def]
theorem antipodeLinearEquiv_f_eq_neg_normalizedF (i : ι) :
    antipodeLinearEquiv D q (f D q i) = -normalizedF D q i := by
  rw [antipodeLinearEquiv_f, normalizedF_def]

/-- Applying `antipodeLinearEquiv` twice agrees with `antipodeSqEquiv`. -/
theorem antipodeLinearEquiv_antipodeLinearEquiv (x : QuantizedEnvelopingAlgebra D q) :
    antipodeLinearEquiv D q (antipodeLinearEquiv D q x) = antipodeSqEquiv D q x := by
  simpa [antipodeLinearEquiv_apply] using
    AlgHom.congr_fun (opComm_antipodeOp_comp_antipodeOp D q) x
theorem antipodeLinearEquiv_antipodeLinearEquiv_e (i : ι) :
    antipodeLinearEquiv D q (antipodeLinearEquiv D q (e D q i)) =
      ((q ^ D.symmetrizer i)⁻¹ ^ 2) • e D q i := by
  rw [antipodeLinearEquiv_antipodeLinearEquiv, antipodeSqEquiv_e]
theorem antipodeLinearEquiv_antipodeLinearEquiv_f (i : ι) :
    antipodeLinearEquiv D q (antipodeLinearEquiv D q (f D q i)) =
      (q ^ D.symmetrizer i) ^ 2 • f D q i := by
  rw [antipodeLinearEquiv_antipodeLinearEquiv, antipodeSqEquiv_f]
theorem antipodeLinearEquiv_antipodeLinearEquiv_k (y : Y) :
    antipodeLinearEquiv D q (antipodeLinearEquiv D q (k D q y)) = k D q y := by
  rw [antipodeLinearEquiv_antipodeLinearEquiv, antipodeSqEquiv_k]

/-- When `⟨αᵢ, y⟩ = 2 dᵢ` for all `i`, `S²` is conjugation by `K_(-y)`. -/
theorem antipodeLinearEquiv_antipodeLinearEquiv_of_pairing_root {y : Y}
    (hρ : ∀ i : ι, D.pairing (D.root i) y = 2 * D.symmetrizer i)
    (x : QuantizedEnvelopingAlgebra D q) :
    antipodeLinearEquiv D q (antipodeLinearEquiv D q x) = k D q (-y) * x * k D q y := by
  rw [antipodeLinearEquiv_antipodeLinearEquiv]
  rcases eq_or_ne q 0 with rfl | hq
  · have hid : antipodeSqEquiv D (0 : K) = AlgEquiv.refl := by
      apply AlgEquiv.coe_toAlgHom_injective; apply hom_ext <;> intro a <;> simp
    rw [hid]
    have hcomm : Commute x (k D (0 : K) (-y)) :=
      commute_of_commute_generators D 0 (by simp) (by simp) (fun z => commute_k_k D 0 z (-y)) x
    simpa only [AlgEquiv.coe_refl, id_eq] using
      (by rw [← hcomm.eq, mul_assoc, k_neg_mul_k, mul_one] :
        x = k D (0 : K) (-y) * x * k D (0 : K) y)
  · have hc : antipodeSqUnit D q = fun i => Units.mk0 q hq ^ D.pairing (D.root i) (-y) := by
      ext i
      simp only [antipodeSqUnit, hq, ↓reduceDIte, map_neg, hρ i, Units.val_pow_eq_pow_val,
        Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, Units.val_mk0]
      rw [zpow_neg, mul_comm (2 : ℤ), zpow_mul, zpow_natCast, zpow_two, ← sq, inv_pow]
    rw [antipodeSqEquiv, hc, ← toAlgEquiv_conjAct_kUnitsHom hq (-y)]
    simp [ConjAct.units_smul_def, mul_assoc]

/-- `S(ω(S x)) = ω x`, equivalently `ω ∘ S = S⁻¹ ∘ ω`. -/
theorem antipodeLinearEquiv_chevalleyInvolution_antipodeLinearEquiv
    (x : QuantizedEnvelopingAlgebra D q) :
    antipodeLinearEquiv D q (chevalleyInvolution D q (antipodeLinearEquiv D q x)) =
      chevalleyInvolution D q x := by
  have h : (AlgHom.opComm (antipodeOp D q)).comp
      ((AlgEquiv.op (chevalleyInvolution D q)).toAlgHom.comp (antipodeOp D q)) =
      (chevalleyInvolution D q).toAlgHom := by
    apply hom_ext <;> intro a <;> simp [mul_assoc]
  simpa only [AlgHom.comp_apply, AlgHom.opComm_apply_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.op_apply_apply, MulOpposite.unop_op, antipodeLinearEquiv_apply] using
    AlgHom.congr_fun h x

@[simp] theorem antipodeLinearEquiv_symm_e (i : ι) :
    (antipodeLinearEquiv D q).symm (e D q i) = -(e D q i * simpleKInv D q i) := by
  simp [LinearEquiv.symm_apply_eq]
@[simp] theorem antipodeLinearEquiv_symm_f (i : ι) :
    (antipodeLinearEquiv D q).symm (f D q i) = -(simpleK D q i * f D q i) := by
  simp [LinearEquiv.symm_apply_eq, mul_assoc]
@[simp] theorem antipodeLinearEquiv_symm_k (y : Y) :
    (antipodeLinearEquiv D q).symm (k D q y) = k D q (-y) := by
  rw [LinearEquiv.symm_apply_eq, antipodeLinearEquiv_k, neg_neg]
@[simp] theorem antipodeLinearEquiv_symm_simpleK (i : ι) :
    (antipodeLinearEquiv D q).symm (simpleK D q i) = simpleKInv D q i := by
  simp [simpleK_def, simpleKInv_def]
@[simp] theorem antipodeLinearEquiv_symm_simpleKInv (i : ι) :
    (antipodeLinearEquiv D q).symm (simpleKInv D q i) = simpleK D q i := by
  simp [simpleK_def, simpleKInv_def]

/-- **Antipode of raising divided powers**:
`S(Eᵢ^(n)) = ((-1)^n qᵢ^(n(n - 1))) • (Kᵢ^(-n) Eᵢ^(n))`. -/
theorem antipodeLinearEquiv_quantumDividedPower_e (i : ι) (n : ℕ) :
    antipodeLinearEquiv D q (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) =
      ((-1 : K) ^ n * (q ^ D.symmetrizer i) ^ (n * (n - 1))) •
        (simpleKInv D q i ^ n * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) := by
  rw [antipodeLinearEquiv_apply, map_quantumDividedPower, antipodeOp_e, unop_quantumDividedPower,
    MulOpposite.unop_op, quantumDividedPower_neg_simpleKInv_mul_e]

/-- **Antipode of lowering divided powers**:
`S(Fᵢ^(n)) = ((-1)^n qᵢ^(-n(n - 1))) • (Fᵢ^(n) Kᵢ^n)`. -/
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
@[simp] theorem map_antipodeLinearEquiv (φ : CartanDatum.Hom D D') (q : K)
    (x : QuantizedEnvelopingAlgebra D q) :
    map φ q (antipodeLinearEquiv D q x) = antipodeLinearEquiv D' q (map φ q x) := by
  have hop : (AlgHom.op (map φ q)).comp (antipodeOp D q) =
      (antipodeOp D' q).comp (map φ q) := by apply hom_ext <;> intro a <;> simp
  simpa [antipodeLinearEquiv_apply] using congrArg MulOpposite.unop (AlgHom.congr_fun hop x)

end Functoriality

end QuantizedEnvelopingAlgebra

end TauCeti
