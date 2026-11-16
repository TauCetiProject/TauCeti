/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import TauCeti.Algebra.HopfAlgebra.Basic
public import TauCeti.Algebra.HopfAlgebra.InverseAntipode
public import TauCeti.QuantumGroups.QuantizedEnvelopingAlgebra.Bialgebra
public import TauCeti.QuantumGroups.QuantizedEnvelopingAlgebra.Rescale
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Hopf algebra structure and antipode of a quantized enveloping algebra

This file constructs the antipode of `TauCeti.QuantizedEnvelopingAlgebra D q`:

* `S(Eᵢ) = -(Kᵢ⁻¹ Eᵢ)`, `S(Fᵢ) = -(Fᵢ Kᵢ)`, `S(K_y) = K_(-y)`.

The opposite-valued homomorphism `antipodeOp : U →ₐ[K] Uᵐᵒᵖ` descends through the divided-power
presentation unconditionally for every `q : K` and is always a `K`-algebra isomorphism
(`antipodeEquiv`). Pairing it with `bialgebra` under the additional hypothesis
`[1 - aᵢⱼ]_(qᵢ)! ≠ 0` (`i ≠ j`) yields `hopfAlgebra` and the generic instance `instHopfAlgebra`.
We prove that for `q ≠ 0`, `S²` is the diagonal rescaling `Eᵢ ↦ qᵢ⁻² • Eᵢ`, `Fᵢ ↦ qᵢ² • Fᵢ`,
`K_y ↦ K_y` (specializing to conjugation by `K_(-y)` for any coweight `y : Y` with
`⟨αᵢ, y⟩ = 2 dᵢ`, the symmetrized counterpart `∑_{α > 0} d_α α∨` of `2ρ` under `αᵢ ↦ dᵢ hᵢ`,
which agrees with `2ρ∨` only when all `dᵢ = 1`), and establish the divided-power antipode and
`S⁻¹` formulas.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993, §3.1.
* J. C. Jantzen, *Lectures on Quantum Groups*, GSM 6, AMS, 1996, §§4.8–4.11.
* The `antipodeTuple`, `HopfAlgebra.ofAntipodeOfAdjoin`, `S²`, and `antipodeEquiv` constructions
  adapt `TauCeti.QuantumGroups.UqSl2.Hopf` and `TauCeti.QuantumGroups.UqSl2.Antipode`.
-/

public section

open Finset

namespace TauCeti.QuantizedEnvelopingAlgebra

variable {K ι X Y : Type*} [Field K] [AddCommGroup X] [AddCommGroup Y]

/-! ### Unconditional opposite-valued antipode -/

section AntipodeOp

variable (D : CartanDatum ι X Y) {q : K}

private lemma quantumDividedPower_neg_kiInv_mul_e (i : ι) (n : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (-(kiInv D q i * e D q i)) n =
      ((-1 : K) ^ n * (q ^ D.symmetrizer i) ^ (n * (n - 1))) •
        (kiInv D q i ^ n * eDividedPower D q i n) := by
  have hcomm : e D q i * kiInv D q i = (q ^ D.symmetrizer i) ^ 2 • (kiInv D q i * e D q i) := by
    rw [e_mul_kiInv, D.cartan_apply_self, zpow_two, ← sq]
  rw [← neg_one_smul K (kiInv D q i * e D q i), quantumDividedPower_smul,
    quantumDividedPower_mul_of_mul_eq_smul_mul _ hcomm, ← pow_mul,
    Nat.mul_div_cancel' (Nat.two_dvd_mul_sub_one n), smul_smul, eDividedPower]

private lemma quantumDividedPower_neg_f_mul_ki (i : ι) (n : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (-(f D q i * ki D q i)) n =
      ((-1 : K) ^ n * (q ^ D.symmetrizer i)⁻¹ ^ (n * (n - 1))) •
        (fDividedPower D q i n * ki D q i ^ n) := by
  have hcomm : ki D q i * f D q i = (q ^ D.symmetrizer i)⁻¹ ^ 2 • (f D q i * ki D q i) := by
    rw [ki_mul_f, D.cartan_apply_self, zpow_neg, zpow_two, ← sq, inv_pow]
  rw [← neg_one_smul K (f D q i * ki D q i), quantumDividedPower_smul,
    quantumDividedPower_mul_right_of_mul_eq_smul_mul _ hcomm, ← pow_mul,
    Nat.mul_div_cancel' (Nat.two_dvd_mul_sub_one n), smul_smul, fDividedPower]

private lemma antipode_serre_exp {m r : ℕ} (hr : r ≤ m) {a : ℤ} (ha : a = 1 - m) :
    (((m - r) * (m - r - 1) : ℕ) : ℤ) + ((r * (r - 1) : ℕ) : ℤ) +
      ((m - r : ℕ) : ℤ) * a + (r : ℤ) * a + 2 * ((m - r : ℕ) : ℤ) * (r : ℤ) = 0 := by
  have hcast_n (k : ℕ) : ((k * (k - 1) : ℕ) : ℤ) = (k : ℤ) * ((k : ℤ) - 1) := by
    rcases k with _ | k <;> simp
  rw [hcast_n, hcast_n, ha, Nat.cast_sub hr]; ring

private lemma eDividedPower_mul_kiInv (i j : ι) (s : ℕ) :
    eDividedPower D q i s * kiInv D q j =
      (q ^ D.symmetrizer i) ^ ((s : ℤ) * D.cartan i j) • (kiInv D q j * eDividedPower D q i s) := by
  rw [kiInv, eDividedPower_mul_k, map_neg, mul_neg, neg_mul, neg_neg, D.pairing_root_simpleTorus,
    show (s : ℤ) * (D.symmetrizer i * D.cartan i j) =
      D.symmetrizer i * ((s : ℤ) * D.cartan i j) by ring, zpow_mul, zpow_natCast]

private lemma e_mul_kiInv_pow (i j : ι) (r : ℕ) :
    e D q j * kiInv D q i ^ r =
      (q ^ D.symmetrizer i) ^ ((r : ℤ) * D.cartan i j) • (kiInv D q i ^ r * e D q j) := by
  rw [kiInv, k_pow, e_mul_k, smul_neg, map_neg, neg_neg, map_nsmul, D.pairing_root_simpleTorus,
    nsmul_eq_mul,
    show (r : ℤ) * (D.symmetrizer j * D.cartan j i) = D.symmetrizer i * ((r : ℤ) * D.cartan i j) by
      linear_combination (r : ℤ) * D.symmetrizer_mul_cartan j i, zpow_mul, zpow_natCast]

private lemma eDividedPower_mul_kiInv_pow (i : ι) (s r : ℕ) :
    eDividedPower D q i s * kiInv D q i ^ r =
      (q ^ D.symmetrizer i) ^ (2 * (s : ℤ) * (r : ℤ)) •
        (kiInv D q i ^ r * eDividedPower D q i s) := by
  rw [kiInv, k_pow, eDividedPower_mul_k, smul_neg, map_neg, mul_neg, neg_mul, neg_neg,
    map_nsmul, D.pairing_root_simpleTorus_self, nsmul_eq_mul,
    show (s : ℤ) * ((r : ℤ) * (2 * D.symmetrizer i)) =
      D.symmetrizer i * (2 * (s : ℤ) * (r : ℤ)) by ring, zpow_mul, zpow_natCast]

/-- Each summand of the unopped antipode image of the `E`-Serre relation factors out
`-(Kⱼ⁻¹ Kᵢ^(-m))` on the left with all `qᵢ`-powers cancelling. -/
private lemma antipode_serre_e_term (hq : q ≠ 0) {i j : ι} (hij : i ≠ j) {r : ℕ}
    (hr : r ≤ serreLength D i j) :
    (-1 : K) ^ r •
        (quantumDividedPower (q ^ D.symmetrizer i) (-(kiInv D q i * e D q i))
            (serreLength D i j - r) *
          (-(kiInv D q j * e D q j)) *
          quantumDividedPower (q ^ D.symmetrizer i) (-(kiInv D q i * e D q i)) r) =
      -(kiInv D q j * kiInv D q i ^ serreLength D i j * ((-1 : K) ^ (serreLength D i j - r) •
        (eDividedPower D q i (serreLength D i j - r) * e D q j * eDividedPower D q i r))) := by
  set m := serreLength D i j; set qi := q ^ D.symmetrizer i with hqi_def
  have hqi : qi ≠ 0 := pow_ne_zero _ hq
  rw [quantumDividedPower_neg_kiInv_mul_e, quantumDividedPower_neg_kiInv_mul_e,
    mul_neg, neg_mul, smul_neg, neg_inj, smul_mul_assoc, smul_mul_smul_comm, smul_smul,
    mul_smul_comm]
  -- Move every toral factor `Kᵢ⁻¹` and `Kⱼ⁻¹` to the left past `Eᵢ^(m - r)` and `Eⱼ`.
  simp only [mul_assoc]
  rw [← mul_assoc (eDividedPower D q i (m - r)), eDividedPower_mul_kiInv]
  simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
  rw [← mul_assoc (e D q j), e_mul_kiInv_pow]
  simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
  rw [← mul_assoc (eDividedPower D q i (m - r)), eDividedPower_mul_kiInv_pow]
  simp only [mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, ← hqi_def]
  rw [← mul_assoc (kiInv D q i ^ (m - r)),
    ((commute_k_k (-D.simpleTorus i) (-D.simpleTorus j)).pow_left (m - r)).eq,
    mul_assoc (kiInv D q j), ← mul_assoc (kiInv D q i ^ (m - r)), ← pow_add, Nat.sub_add_cancel hr]
  refine congrArg (· • _) ?_
  -- Cancel `(-1)^r * (-1)^r = 1` and the combined `qᵢ`-exponent `= 0`.
  have hsign : (-1 : K) ^ r * (-1 : K) ^ r = 1 := by rw [← mul_pow, neg_mul_neg, one_mul, one_pow]
  set c : K := qi ^ ((m - r) * (m - r - 1)) * qi ^ (r * (r - 1)) *
    (qi ^ (((m - r : ℕ) : ℤ) * D.cartan i j) * qi ^ ((r : ℤ) * D.cartan i j) *
      qi ^ (2 * (((m - r : ℕ) : ℤ) * (r : ℤ))))
  have hpow : c = 1 := by
    have hexp : (((m - r) * (m - r - 1) : ℕ) : ℤ) + ((r * (r - 1) : ℕ) : ℤ) +
        (((m - r : ℕ) : ℤ) * D.cartan i j + (r : ℤ) * D.cartan i j +
          2 * (((m - r : ℕ) : ℤ) * (r : ℤ))) = 0 := by
      linear_combination antipode_serre_exp hr (cartan_eq_one_sub_serreLength D hij)
    simp only [c, ← zpow_natCast, ← zpow_add₀ hqi]; rw [hexp, zpow_zero]
  calc _ = (-1 : K) ^ (m - r) * ((-1 : K) ^ r * (-1 : K) ^ r) * c := by dsimp only [c]; ring
    _ = (-1 : K) ^ (m - r) := by rw [hsign, hpow, mul_one, mul_one]

private lemma antipode_serre_e {i j : ι} (hij : i ≠ j) :
    ∑ r ∈ range (serreLength D i j + 1), (-1 : K) ^ r •
      (quantumDividedPower (q ^ D.symmetrizer i) (MulOpposite.op (-(kiInv D q i * e D q i))) r *
        MulOpposite.op (-(kiInv D q j * e D q j)) *
        quantumDividedPower (q ^ D.symmetrizer i) (MulOpposite.op (-(kiInv D q i * e D q i)))
          (serreLength D i j - r)) = 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · apply MulOpposite.unop_injective
    simp only [unop_sum, MulOpposite.unop_smul, MulOpposite.unop_mul,
      MulOpposite.unop_op, MulOpposite.unop_zero, unop_quantumDividedPower, ← mul_assoc]
    rw [sum_congr rfl fun r hr ↦
        antipode_serre_e_term D hq hij (Nat.lt_succ_iff.mp (mem_range.mp hr)),
      sum_neg_distrib, ← mul_sum, ← sum_range_reflect]
    rw [sum_congr rfl fun r hr ↦ by
        rw [Nat.add_one_sub_one, Nat.sub_sub_self (Nat.lt_succ_iff.mp (mem_range.mp hr))],
      serre_e hij, mul_zero, neg_zero]

private noncomputable def antipodeTuple :
    GeneratorTuple D q (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ where
  e i := MulOpposite.op (-(kiInv D q i * e D q i))
  f i := MulOpposite.op (-(f D q i * ki D q i))
  k y := MulOpposite.op (k D q (-y))
  k_zero := by simp
  k_mul_k y z := MulOpposite.unop_injective (by simp [k_mul_k, add_comm])
  k_mul_e y i := MulOpposite.unop_injective <| by
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul,
      neg_mul, mul_neg, smul_neg, neg_inj]
    rw [mul_assoc, e_mul_k, map_neg, neg_neg, mul_smul_comm, ← mul_assoc (kiInv D q i),
      kiInv, (commute_k_k (-D.simpleTorus i) (-y)).eq, mul_assoc]
  k_mul_f y i := MulOpposite.unop_injective <| by
    rcases eq_or_ne q 0 with rfl | hq
    · simp
    · simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul,
        neg_mul, mul_neg, smul_neg, neg_inj]
      rw [← mul_assoc (k D q (-y)), k_mul_f]
      simp [inv_smul_smul₀ (zpow_ne_zero _ hq), mul_assoc, ki,
        (commute_k_k (D.simpleTorus i) (-y)).eq]
  e_mul_f_sub_f_mul_e_self i := MulOpposite.unop_injective <| by
    rcases eq_or_ne q 0 with rfl | hq
    · simp [(D.symmetrizer_pos i).ne']
    · simp only [MulOpposite.unop_sub, MulOpposite.unop_mul, MulOpposite.unop_op,
        MulOpposite.unop_smul, neg_mul_neg]
      have h1 : f D q i * ki D q i * (kiInv D q i * e D q i) = f D q i * e D q i := by
        simp [mul_assoc, ki, kiInv]
      have h2 : kiInv D q i * e D q i * (f D q i * ki D q i) = e D q i * f D q i := by
        have hqi : q ^ D.symmetrizer i ≠ 0 := pow_ne_zero _ hq
        rw [kiInv_mul_e, smul_mul_assoc, mul_assoc (e D q i), ← mul_assoc (kiInv D q i),
          kiInv_mul_f]
        simp [inv_smul_smul₀ (pow_ne_zero 2 hqi), mul_assoc, ki, kiInv]
      rw [h1, h2, ← neg_sub (e D q i * f D q i), e_mul_f_sub_f_mul_e_self, ← smul_neg,
        neg_sub, ki, kiInv, neg_neg]
  e_mul_f_sub_f_mul_e_of_ne {i j} hij := MulOpposite.unop_injective <| by
    rcases eq_or_ne q 0 with rfl | hq
    · simp
    · simp only [MulOpposite.unop_sub, MulOpposite.unop_mul, MulOpposite.unop_op,
        MulOpposite.unop_zero, neg_mul_neg, sub_eq_zero]
      calc f D q j * ki D q j * (kiInv D q i * e D q i)
          = (f D q j * k D q (-D.simpleTorus i)) * (k D q (D.simpleTorus j) * e D q i) := by
            rw [ki, kiInv, mul_assoc (f D q j), ← mul_assoc (k D q (D.simpleTorus j)),
              (commute_k_k (D.simpleTorus j) (-D.simpleTorus i)).eq]; simp only [mul_assoc]
        _ = (q ^ (-(D.symmetrizer j * D.cartan j i)) * q ^ (D.symmetrizer i * D.cartan i j)) •
              (k D q (-D.simpleTorus i) * (f D q j * e D q i) * k D q (D.simpleTorus j)) := by
            rw [f_mul_k, k_mul_e, map_neg, D.pairing_root_simpleTorus, D.pairing_root_simpleTorus,
              smul_mul_smul_comm]; simp only [mul_assoc]
        _ = kiInv D q i * e D q i * (f D q j * ki D q j) := by
            rw [← zpow_add₀ hq, D.symmetrizer_mul_cartan j i, neg_add_cancel, zpow_zero, one_smul,
              ← e_mul_f_of_ne hij, ki, kiInv]; simp only [mul_assoc]
  serre_e hij := antipode_serre_e D hij
  serre_f {i j} hij := by
    -- Follows from `antipode_serre_e` via `chevalleyInvolution` and `serre_smul`.
    let φ := (AlgEquiv.op (chevalleyInvolution D q)).toAlgHom
    have hφ (m : ι) : φ (MulOpposite.op (-(kiInv D q m * e D q m))) =
        MulOpposite.op (-(ki D q m * f D q m)) := by simp [φ]
    have hsc (m : ι) : MulOpposite.op (-(f D q m * ki D q m)) =
        (q ^ D.symmetrizer m) ^ D.cartan m m • MulOpposite.op (-(ki D q m * f D q m)) := by
      rw [f_mul_ki, ← smul_neg, MulOpposite.op_smul]
    have h0 := congrArg φ (antipode_serre_e D hij)
    simp only [map_sum, map_smul, map_mul, map_quantumDividedPower, hφ, map_zero] at h0
    simp only [hsc, serre_smul, h0, smul_zero]

/-- The antipode as a `K`-algebra homomorphism `U →ₐ[K] Uᵐᵒᵖ`, defined for every `q : K`. -/
noncomputable def antipodeOp (D : CartanDatum ι X Y) (q : K) :
    QuantizedEnvelopingAlgebra D q →ₐ[K] (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ :=
  lift (antipodeTuple D)

variable {D}

@[simp] theorem antipodeOp_e (i : ι) :
    antipodeOp D q (e D q i) = MulOpposite.op (-(kiInv D q i * e D q i)) := lift_e _ i
@[simp] theorem antipodeOp_f (i : ι) :
    antipodeOp D q (f D q i) = MulOpposite.op (-(f D q i * ki D q i)) := lift_f _ i
@[simp] theorem antipodeOp_k (y : Y) :
    antipodeOp D q (k D q y) = MulOpposite.op (k D q (-y)) := lift_k _ y
theorem antipodeOp_ki (i : ι) : antipodeOp D q (ki D q i) = MulOpposite.op (kiInv D q i) :=
  antipodeOp_k (D.simpleTorus i)
theorem antipodeOp_kiInv (i : ι) : antipodeOp D q (kiInv D q i) = MulOpposite.op (ki D q i) := by
  rw [kiInv, antipodeOp_k, neg_neg, ki]

theorem unop_antipodeOp_eDividedPower (i : ι) (n : ℕ) :
    MulOpposite.unop (antipodeOp D q (eDividedPower D q i n)) =
      ((-1 : K) ^ n * (q ^ D.symmetrizer i) ^ (n * (n - 1))) •
        (kiInv D q i ^ n * eDividedPower D q i n) := by
  rw [eDividedPower, map_quantumDividedPower, antipodeOp_e, unop_quantumDividedPower,
    MulOpposite.unop_op, ← eDividedPower, quantumDividedPower_neg_kiInv_mul_e]

theorem unop_antipodeOp_fDividedPower (i : ι) (n : ℕ) :
    MulOpposite.unop (antipodeOp D q (fDividedPower D q i n)) =
      ((-1 : K) ^ n * (q ^ D.symmetrizer i)⁻¹ ^ (n * (n - 1))) •
        (fDividedPower D q i n * ki D q i ^ n) := by
  rw [fDividedPower, map_quantumDividedPower, antipodeOp_f, unop_quantumDividedPower,
    MulOpposite.unop_op, ← fDividedPower, quantumDividedPower_neg_f_mul_ki]

/-- For `q ≠ 0`, `S²` equals the diagonal rescaling `Eᵢ ↦ qᵢ⁻² • Eᵢ`, `Fᵢ ↦ qᵢ² • Fᵢ`, `K_y ↦ K_y`.
-/
theorem opComm_antipodeOp_comp_antipodeOp (hq : q ≠ 0) :
    (AlgHom.opComm (antipodeOp D q)).comp (antipodeOp D q) =
      (rescale D q (fun i ↦
        (Units.mk0 (q ^ D.symmetrizer i) (pow_ne_zero _ hq))⁻¹ ^ 2)).toAlgHom := by
  ext i
  · simp only [AlgHom.comp_apply, AlgHom.opComm_apply_apply, AlgEquiv.coe_toAlgHom,
      antipodeOp_e, MulOpposite.unop_op, map_neg, map_mul, antipodeOp_kiInv,
      MulOpposite.unop_neg, MulOpposite.unop_mul, neg_mul, neg_neg, rescale_e,
      Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [kiInv_mul_e, D.cartan_apply_self, zpow_neg, zpow_two, ← sq, inv_pow,
      smul_mul_assoc, mul_assoc, kiInv, ki, k_neg_mul_k, mul_one]
  · simp only [AlgHom.comp_apply, AlgHom.opComm_apply_apply, AlgEquiv.coe_toAlgHom,
      antipodeOp_f, MulOpposite.unop_op, map_neg, map_mul, antipodeOp_ki,
      MulOpposite.unop_neg, MulOpposite.unop_mul, mul_neg, neg_neg, rescale_f,
      Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, inv_inv]
    rw [← mul_assoc, kiInv_mul_f, D.cartan_apply_self, zpow_two, ← sq,
      smul_mul_assoc, mul_assoc, kiInv, ki, k_neg_mul_k, mul_one]
  · simp

private lemma opComm_antipodeOp_comp_antipodeOp_zero :
    (AlgHom.opComm (antipodeOp D (0 : K))).comp (antipodeOp D 0) =
      AlgHom.id K (QuantizedEnvelopingAlgebra D 0) := by ext <;> simp

/-- When `⟨αᵢ, y⟩ = 2 dᵢ` for all `i`, `S²` is conjugation by `K_(-y)`. -/
theorem unop_antipodeOp_unop_antipodeOp_of_pairing_root {y : Y}
    (hρ : ∀ i : ι, D.pairing (D.root i) y = 2 * D.symmetrizer i)
    (x : QuantizedEnvelopingAlgebra D q) :
    MulOpposite.unop (antipodeOp D q (MulOpposite.unop (antipodeOp D q x))) =
      k D q (-y) * x * k D q y := by
  rcases eq_or_ne q 0 with rfl | hq
  · have hcomm : Commute x (k D (0 : K) (-y)) :=
      commute_of_commute_generators (by simp) (by simp) (fun z ↦ commute_k_k z (-y)) x
    have hx := AlgHom.congr_fun (opComm_antipodeOp_comp_antipodeOp_zero (D := D) (K := K)) x
    simp only [AlgHom.comp_apply, AlgHom.opComm_apply_apply, AlgHom.id_apply] at hx
    rw [hx, ← hcomm.eq, mul_assoc, k_neg_mul_k, mul_one]
  · have hc : (fun i ↦ (Units.mk0 (q ^ D.symmetrizer i) (pow_ne_zero _ hq))⁻¹ ^ 2) =
        fun i ↦ Units.mk0 q hq ^ D.pairing (D.root i) (-y) := by
      ext i
      simp only [map_neg, hρ i, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
        Units.val_zpow_eq_zpow_val, Units.val_mk0]
      rw [zpow_neg, mul_comm (2 : ℤ), zpow_mul, zpow_natCast, zpow_two, ← sq, inv_pow]
    have hx := AlgHom.congr_fun (opComm_antipodeOp_comp_antipodeOp (D := D) hq) x
    simp only [AlgHom.comp_apply, AlgHom.opComm_apply_apply, AlgEquiv.coe_toAlgHom] at hx
    rw [hx, hc, ← toAlgEquiv_conjAct_kUnit hq (-y)]
    simp [ConjAct.units_smul_def, mul_assoc]

variable (D q) in
/-- The opposite-valued antipode `U →ₐ[K] Uᵐᵒᵖ` is bijective for every `q : K`. -/
theorem antipodeOp_bijective : Function.Bijective (antipodeOp D q) := by
  let g : QuantizedEnvelopingAlgebra D q → QuantizedEnvelopingAlgebra D q :=
    MulOpposite.unop ∘ antipodeOp D q
  have hsq : Function.Bijective (g ∘ g) := by
    have hcomp : (g ∘ g : _ → _) = (AlgHom.opComm (antipodeOp D q)).comp (antipodeOp D q) := rfl
    rw [hcomp]
    rcases eq_or_ne q 0 with rfl | hq
    · rw [opComm_antipodeOp_comp_antipodeOp_zero]; exact Function.bijective_id
    · rw [opComm_antipodeOp_comp_antipodeOp hq]; exact (rescale D q _).bijective
  exact MulOpposite.opEquiv.bijective.comp ⟨.of_comp hsq.1, .of_comp hsq.2⟩

variable (D q) in
/-- The antipode as a `K`-algebra isomorphism `U ≃ₐ[K] Uᵐᵒᵖ`, defined for every `q : K`. -/
noncomputable def antipodeEquiv :
    QuantizedEnvelopingAlgebra D q ≃ₐ[K] (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ :=
  AlgEquiv.ofBijective (antipodeOp D q) (antipodeOp_bijective D q)

@[simp] theorem antipodeEquiv_toAlgHom : (antipodeEquiv D q).toAlgHom = antipodeOp D q :=
  AlgEquiv.toAlgHom_ofBijective _ _
@[simp] theorem antipodeEquiv_apply (x : QuantizedEnvelopingAlgebra D q) :
    antipodeEquiv D q x = antipodeOp D q x := AlgEquiv.ofBijective_apply _ _ x
@[simp] theorem antipodeEquiv_symm_op_e (i : ι) :
    (antipodeEquiv D q).symm (MulOpposite.op (e D q i)) = -(e D q i * kiInv D q i) :=
  (antipodeEquiv D q).injective <| by simp [← MulOpposite.op_mul, kiInv]
@[simp] theorem antipodeEquiv_symm_op_f (i : ι) :
    (antipodeEquiv D q).symm (MulOpposite.op (f D q i)) = -(ki D q i * f D q i) :=
  (antipodeEquiv D q).injective <| by simp [← MulOpposite.op_mul, ki, mul_assoc]
@[simp] theorem antipodeEquiv_symm_op_k (y : Y) :
    (antipodeEquiv D q).symm (MulOpposite.op (k D q y)) = k D q (-y) :=
  (antipodeEquiv D q).injective <| by simp
theorem antipodeEquiv_symm_op_ki (i : ι) :
    (antipodeEquiv D q).symm (MulOpposite.op (ki D q i)) = kiInv D q i :=
  antipodeEquiv_symm_op_k (D.simpleTorus i)
theorem antipodeEquiv_symm_op_kiInv (i : ι) :
    (antipodeEquiv D q).symm (MulOpposite.op (kiInv D q i)) = ki D q i := by
  rw [kiInv, antipodeEquiv_symm_op_k, neg_neg, ki]

/-- `S(ω(S x)) = ω x`, equivalently `ω ∘ S = S⁻¹ ∘ ω`. -/
theorem unop_antipodeOp_chevalleyInvolution_unop_antipodeOp (x : QuantizedEnvelopingAlgebra D q) :
    MulOpposite.unop (antipodeOp D q (chevalleyInvolution D q (MulOpposite.unop
        (antipodeOp D q x)))) = chevalleyInvolution D q x := by
  have h : (AlgHom.opComm (antipodeOp D q)).comp
      ((AlgEquiv.op (chevalleyInvolution D q)).toAlgHom.comp (antipodeOp D q)) =
      (chevalleyInvolution D q).toAlgHom := by
    ext i
    · simp [ki, kiInv, mul_assoc]
    · simp [ki, kiInv, ← mul_assoc]
    · simp
  simpa only [AlgHom.comp_apply, AlgHom.opComm_apply_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.op_apply_apply, MulOpposite.unop_op] using AlgHom.congr_fun h x

theorem map_unop_antipodeOp {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D' : CartanDatum ι X' Y'} (φ : CartanDatum.Hom D D') (x : QuantizedEnvelopingAlgebra D q) :
    map φ (MulOpposite.unop (antipodeOp D q x)) = MulOpposite.unop (antipodeOp D' q (map φ x)) := by
  have h : (AlgHom.op (map φ)).comp (antipodeOp D q) = (antipodeOp D' q).comp (map φ) := by
    ext <;> simp [ki, kiInv]
  simpa only [AlgHom.comp_apply, AlgHom.op_apply_apply, MulOpposite.unop_op] using
    congrArg MulOpposite.unop (AlgHom.congr_fun h x)

end AntipodeOp

/-! ### Hopf algebra structure, square, bijectivity, and inverse -/

section Hopf

variable (D : CartanDatum ι X Y) {q : K}

section Explicit

variable (hserre : ∀ {i j : ι}, i ≠ j →
  quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0)

/-- Explicit-hypothesis `HopfAlgebra` structure on `QuantizedEnvelopingAlgebra D q`, assuming
`[1 - aᵢⱼ]_(qᵢ)! ≠ 0` for all `i ≠ j` (needed for the bialgebra structure `bialgebra`). -/
@[expose, instance_reducible]
noncomputable def hopfAlgebra : HopfAlgebra K (QuantizedEnvelopingAlgebra D q) :=
  @HopfAlgebra.ofAntipodeOfAdjoin K (QuantizedEnvelopingAlgebra D q) _ _
    (bialgebra D hserre) _ (antipodeOp D q) (adjoin_range_generator D q)
    (by rintro _ ⟨g, rfl⟩; cases g <;>
      simp [bialgebra_comul, bialgebra_counit, mul_assoc, ki, kiInv])
    (by rintro _ ⟨g, rfl⟩; cases g <;>
      simp [bialgebra_comul, bialgebra_counit, ← mul_assoc (ki D q _), ki, kiInv])

theorem hopfAlgebra_toBialgebra : (hopfAlgebra D hserre).toBialgebra = bialgebra D hserre := (rfl)
theorem hopfAlgebra_comul (x : QuantizedEnvelopingAlgebra D q) :
    letI := hopfAlgebra D hserre; Coalgebra.comul (R := K) x = comulAlgHom D hserre x := (rfl)
theorem hopfAlgebra_counit (x : QuantizedEnvelopingAlgebra D q) :
    letI := hopfAlgebra D hserre; Coalgebra.counit (R := K) x = counit D q x := (rfl)
theorem hopfAlgebra_antipode (x : QuantizedEnvelopingAlgebra D q) :
    letI := hopfAlgebra D hserre
    HopfAlgebra.antipode K x = MulOpposite.unop (antipodeOp D q x) := (rfl)

end Explicit

section Generic

variable (q : K) [Fact (IsGenericQuantumParameter q)]

/-- The canonical `K`-Hopf algebra structure on `QuantizedEnvelopingAlgebra D q` at generic `q`. -/
noncomputable instance instHopfAlgebra : HopfAlgebra K (QuantizedEnvelopingAlgebra D q) :=
  hopfAlgebra D fun {i j} _ ↦
    quantumFactorial_ne_zero
      ((Fact.out : IsGenericQuantumParameter q).pow (D.symmetrizer_pos i)) (serreLength D i j)

variable {D q}

@[simp] theorem antipode_e (i : ι) :
    HopfAlgebra.antipode K (e D q i) = -(kiInv D q i * e D q i) :=
  congrArg MulOpposite.unop (antipodeOp_e i)
@[simp] theorem antipode_f (i : ι) :
    HopfAlgebra.antipode K (f D q i) = -(f D q i * ki D q i) :=
  congrArg MulOpposite.unop (antipodeOp_f i)
@[simp] theorem antipode_k (y : Y) : HopfAlgebra.antipode K (k D q y) = k D q (-y) :=
  congrArg MulOpposite.unop (antipodeOp_k y)
theorem antipode_ki (i : ι) : HopfAlgebra.antipode K (ki D q i) = kiInv D q i :=
  antipode_k (D.simpleTorus i)
theorem antipode_kiInv (i : ι) : HopfAlgebra.antipode K (kiInv D q i) = ki D q i := by
  rw [kiInv, antipode_k, neg_neg, ki]
@[simp] theorem antipodeOp_apply (x : QuantizedEnvelopingAlgebra D q) :
    antipodeOp D q x = MulOpposite.op (HopfAlgebra.antipode K x) := (rfl)
theorem antipode_e_eq_neg_normalizedE (i : ι) :
    HopfAlgebra.antipode K (e D q i) = -normalizedE D q i := by rw [antipode_e, normalizedE_def]
theorem antipode_f_eq_neg_normalizedF (i : ι) :
    HopfAlgebra.antipode K (f D q i) = -normalizedF D q i := by rw [antipode_f, normalizedF_def]

/-- `S(Eᵢ^(n)) = (-1)^n qᵢ^(n(n - 1)) Kᵢ^(-n) Eᵢ^(n)`. -/
theorem antipode_eDividedPower (i : ι) (n : ℕ) :
    HopfAlgebra.antipode K (eDividedPower D q i n) =
      ((-1 : K) ^ n * (q ^ D.symmetrizer i) ^ (n * (n - 1))) •
        (kiInv D q i ^ n * eDividedPower D q i n) := unop_antipodeOp_eDividedPower i n
/-- `S(Fᵢ^(n)) = (-1)^n qᵢ^(-n(n - 1)) Fᵢ^(n) Kᵢ^n`. -/
theorem antipode_fDividedPower (i : ι) (n : ℕ) :
    HopfAlgebra.antipode K (fDividedPower D q i n) =
      ((-1 : K) ^ n * (q ^ D.symmetrizer i)⁻¹ ^ (n * (n - 1))) •
        (fDividedPower D q i n * ki D q i ^ n) := unop_antipodeOp_fDividedPower i n

/-- On every Cartan datum, `S²` equals the diagonal rescaling `Eᵢ ↦ qᵢ⁻² • Eᵢ`, `Fᵢ ↦ qᵢ² • Fᵢ`. -/
theorem antipode_antipode_eq_rescale (x : QuantizedEnvelopingAlgebra D q) :
    HopfAlgebra.antipode K (HopfAlgebra.antipode K x) =
      rescale D q (fun i ↦ (Units.mk0 (q ^ D.symmetrizer i)
        (pow_ne_zero _ (Fact.out : IsGenericQuantumParameter q).ne_zero))⁻¹ ^ 2) x := by
  have h := opComm_antipodeOp_comp_antipodeOp (D := D)
    (Fact.out : IsGenericQuantumParameter q).ne_zero
  simpa only [AlgHom.comp_apply, AlgHom.opComm_apply_apply, AlgEquiv.coe_toAlgHom,
    antipodeOp_apply, MulOpposite.unop_op] using AlgHom.congr_fun h x

/-- When `⟨αᵢ, y⟩ = 2 dᵢ` for all `i`, `S²` is conjugation by `K_(-y)`. -/
theorem antipode_antipode_of_pairing_root {y : Y}
    (hρ : ∀ i : ι, D.pairing (D.root i) y = 2 * D.symmetrizer i)
    (x : QuantizedEnvelopingAlgebra D q) :
    HopfAlgebra.antipode K (HopfAlgebra.antipode K x) = k D q (-y) * x * k D q y :=
  unop_antipodeOp_unop_antipodeOp_of_pairing_root hρ x
theorem antipode_antipode_e (i : ι) :
    HopfAlgebra.antipode K (HopfAlgebra.antipode K (e D q i)) =
      (q ^ D.symmetrizer i)⁻¹ ^ 2 • e D q i := by rw [antipode_antipode_eq_rescale]; simp
theorem antipode_antipode_f (i : ι) :
    HopfAlgebra.antipode K (HopfAlgebra.antipode K (f D q i)) =
      (q ^ D.symmetrizer i) ^ 2 • f D q i := by rw [antipode_antipode_eq_rescale]; simp [inv_pow]
theorem antipode_antipode_k (y : Y) :
    HopfAlgebra.antipode K (HopfAlgebra.antipode K (k D q y)) = k D q y := by simp

variable (D q) in
/-- The antipode of `QuantizedEnvelopingAlgebra D q` is bijective on every Cartan datum. -/
theorem antipode_bijective :
    Function.Bijective (HopfAlgebra.antipode K (A := QuantizedEnvelopingAlgebra D q)) :=
  MulOpposite.opEquiv.symm.bijective.comp (antipodeOp_bijective D q)

@[simp] theorem antipodeEquiv_symm_apply (x : (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ) :
    (antipodeEquiv D q).symm x =
      TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) x.unop :=
  (antipodeEquiv D q).injective <| by simp [TauCeti.HopfAlgebra.antipode_inverseAntipode]
@[simp] theorem inverseAntipode_e (i : ι) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (e D q i) =
      -(e D q i * kiInv D q i) := by
  simpa only [antipodeEquiv_symm_op_e, MulOpposite.unop_op] using
    (antipodeEquiv_symm_apply (MulOpposite.op (e D q i))).symm
@[simp] theorem inverseAntipode_f (i : ι) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (f D q i) =
      -(ki D q i * f D q i) := by
  simpa only [antipodeEquiv_symm_op_f, MulOpposite.unop_op] using
    (antipodeEquiv_symm_apply (MulOpposite.op (f D q i))).symm
@[simp] theorem inverseAntipode_k (y : Y) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (k D q y) = k D q (-y) := by
  simpa only [antipodeEquiv_symm_op_k, MulOpposite.unop_op] using
    (antipodeEquiv_symm_apply (MulOpposite.op (k D q y))).symm
theorem inverseAntipode_ki (i : ι) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (ki D q i) = kiInv D q i :=
  inverseAntipode_k (D.simpleTorus i)
theorem inverseAntipode_kiInv (i : ι) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (kiInv D q i) = ki D q i := by
  rw [kiInv, inverseAntipode_k, neg_neg, ki]

/-- `S(ω(S x)) = ω x`, equivalently `ω ∘ S = S⁻¹ ∘ ω`. -/
theorem antipode_chevalleyInvolution_antipode (x : QuantizedEnvelopingAlgebra D q) :
    HopfAlgebra.antipode K (chevalleyInvolution D q (HopfAlgebra.antipode K x)) =
      chevalleyInvolution D q x := unop_antipodeOp_chevalleyInvolution_unop_antipodeOp x

@[simp] theorem map_antipode {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D' : CartanDatum ι X' Y'} (φ : CartanDatum.Hom D D') (x : QuantizedEnvelopingAlgebra D q) :
    map φ (HopfAlgebra.antipode K x) = HopfAlgebra.antipode K (map φ x) := map_unop_antipodeOp φ x

end Generic

end Hopf

end TauCeti.QuantizedEnvelopingAlgebra
