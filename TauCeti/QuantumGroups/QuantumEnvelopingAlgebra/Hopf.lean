/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumEnvelopingAlgebra.Bialgebra
public import TauCeti.QuantumGroups.QuantumEnvelopingAlgebra.Grading
public import TauCeti.Algebra.HopfAlgebra.Basic
public import TauCeti.Algebra.HopfAlgebra.InverseAntipode

/-!
# The antipode and Hopf algebra structure on `QuantumEnvelopingAlgebra`

For a symmetrizable Cartan datum `D` and **any** `q` in a field `K`, we define
`normE D q i = Kᵢ⁻¹ Eᵢ` and `normF D q i = Fᵢ Kᵢ`, construct the opposite-valued antipode
equivalence `antipodeOpEquiv : U ≃ₐ[K] Uᵐᵒᵖ`, and establish the unconditional `HopfAlgebra`
instance, divided-power antipodes, `antipode_bijective`, and `S²(x) = K_(-c) x K_c` for `2ρ^\vee`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993, §3.1.
* S. Lentner, *Quantum groups and Nichols algebras acting on conformal field theories*, Adv. Math.
  278 (2015), Theorem 3.3.
-/

public noncomputable section

open scoped TensorProduct

namespace TauCeti.QuantumEnvelopingAlgebra

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]

section Norm
variable (D : CartanDatum ι X Y) (q : K)
/-- The normalized raising operator `eᵢ = Kᵢ⁻¹ * Eᵢ`. -/
def normE (i : ι) : QuantumEnvelopingAlgebra D q := simpleKInv D q i * e D q i
/-- The normalized lowering operator `fᵢ = Fᵢ * Kᵢ`. -/
def normF (i : ι) : QuantumEnvelopingAlgebra D q := f D q i * simpleK D q i
theorem normE_def (i : ι) : normE D q i = simpleKInv D q i * e D q i := (rfl)
theorem normF_def (i : ι) : normF D q i = f D q i * simpleK D q i := (rfl)
end Norm
@[simp] theorem normE_zero {D : CartanDatum ι X Y} (i : ι) : normE D (0 : K) i = 0 := by
  simp [normE_def]
@[simp] theorem normF_zero {D : CartanDatum ι X Y} (i : ι) : normF D (0 : K) i = 0 := by
  simp [normF_def]

private theorem two_mul_choose_two_eq (r : ℕ) :
    ((2 * r.choose 2 : ℕ) : ℤ) = (r : ℤ) * ((r : ℤ) - 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, mul_add, Nat.cast_add, ih]; push_cast; ring

private theorem normE_pow {D : CartanDatum ι X Y} {q : K} (i : ι) (r : ℕ) :
    normE D q i ^ r = (q ^ D.symmetrizer i) ^ ((r : ℤ) * ((r : ℤ) - 1)) •
      (simpleKInv D q i ^ r * e D q i ^ r) := by
  rw [normE_def, mul_pow_of_mul_eq_smul_mul (e_mul_simpleKInv_self i), ← pow_mul, ← zpow_natCast,
    two_mul_choose_two_eq]
private theorem normF_pow {D : CartanDatum ι X Y} {q : K} (i : ι) (r : ℕ) :
    normF D q i ^ r = (q ^ D.symmetrizer i) ^ (-((r : ℤ) * ((r : ℤ) - 1))) •
      (f D q i ^ r * simpleK D q i ^ r) := by
  rw [normF_def, mul_pow_of_mul_eq_smul_mul (simpleK_mul_f_self i), ← pow_mul, inv_pow,
    ← zpow_natCast, ← zpow_neg, two_mul_choose_two_eq]

/-- Quantum divided power of `-Kᵢ⁻¹ Eᵢ`, valid for every `q : K` and `r : ℕ`. -/
theorem quantumDividedPower_neg_normE {D : CartanDatum ι X Y} {q : K} (i : ι) (r : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (-normE D q i) r =
      (-1 : K) ^ r • (q ^ D.symmetrizer i) ^ ((r : ℤ) * ((r : ℤ) - 1)) •
        (simpleKInv D q i ^ r * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r) := by
  rw [← neg_one_smul K (normE D q i), quantumDividedPower_smul, quantumDividedPower_def,
    normE_pow, smul_comm (quantumFactorial _ r)⁻¹, ← mul_smul_comm, ← quantumDividedPower_def]
/-- Quantum divided power of `-Fᵢ Kᵢ`, valid for every `q : K` and `r : ℕ`. -/
theorem quantumDividedPower_neg_normF {D : CartanDatum ι X Y} {q : K} (i : ι) (r : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (-normF D q i) r =
      (-1 : K) ^ r • (q ^ D.symmetrizer i) ^ (-((r : ℤ) * ((r : ℤ) - 1))) •
        (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) r * simpleK D q i ^ r) := by
  rw [← neg_one_smul K (normF D q i), quantumDividedPower_smul, quantumDividedPower_def,
    normF_pow, smul_comm (quantumFactorial _ r)⁻¹, ← smul_mul_assoc, ← quantumDividedPower_def]

section Unconditional
open MulOpposite
variable (D : CartanDatum ι X Y) (q : K)

private theorem normE_pow_mul_normE_mul_normE_pow {q' : K} (hq : q' ≠ 0) {i j : ι} (hij : i ≠ j)
    {r s : ℕ} (hrs : r + s = serreLength D i j) :
    normE D q' i ^ r * normE D q' j * normE D q' i ^ s =
      (simpleKInv D q' j * simpleKInv D q' i ^ serreLength D i j) *
        (e D q' i ^ r * e D q' j * e D q' i ^ s) := by
  set qᵢ : K := q' ^ D.symmetrizer i; have hqᵢ : qᵢ ≠ 0 := pow_ne_zero _ hq
  have hcomm₁ : e D q' i ^ r * simpleKInv D q' j =
      qᵢ ^ ((r : ℤ) * D.cartan i j) • (simpleKInv D q' j * e D q' i ^ r) := by
    rw [e_pow_mul_k, map_neg, D.pairing_root_simpleTorus, mul_neg, neg_neg,
      ← mul_assoc, mul_comm (r : ℤ), mul_assoc, zpow_mul, zpow_natCast]
  have hcomm₂ : (e D q' i ^ r * e D q' j) * simpleKInv D q' i ^ s =
      qᵢ ^ ((s : ℤ) * D.cartan i j + 2 * (r : ℤ) * s) •
        (simpleKInv D q' i ^ s * (e D q' i ^ r * e D q' j)) := by
    have hexp : (s : ℤ) * ((D.symmetrizer i : ℤ) * D.cartan i j) +
        (r : ℤ) * ((s : ℤ) * (2 * (D.symmetrizer i : ℤ))) =
        (D.symmetrizer i : ℤ) * ((s : ℤ) * D.cartan i j + 2 * (r : ℤ) * s) := by ring
    rw [k_pow, smul_neg, mul_assoc, e_mul_k_neg, map_nsmul, D.pairing_root_simpleTorus,
      ← D.symmetrizer_mul_cartan, nsmul_eq_mul, mul_smul_comm, ← mul_assoc (e D q' i ^ r),
      e_pow_mul_k, map_neg, map_nsmul, D.pairing_root_simpleTorus_self, nsmul_eq_mul, mul_neg,
      neg_neg, smul_mul_assoc, smul_smul, ← zpow_add₀ hq, mul_assoc]
    simp only [← smul_neg, ← k_pow, hexp, zpow_mul, zpow_natCast]; rfl
  rw [normE_pow, normE_pow, normE_def]; simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_assoc (simpleKInv D q' i ^ r), ← mul_assoc (e D q' i ^ r), hcomm₁]
  simp only [mul_smul_comm, smul_mul_assoc, ← mul_assoc (simpleKInv D q' i ^ r),
    ((commute_k _ _).pow_left r).eq]
  rw [mul_assoc (simpleKInv D q' j * _), mul_assoc (simpleKInv D q' j * _),
    ← mul_assoc (e D q' i ^ r * e D q' j), hcomm₂]
  simp only [mul_smul_comm, smul_mul_assoc, smul_smul]
  rw [← mul_assoc (simpleKInv D q' j * _), mul_assoc (simpleKInv D q' j),
    ← mul_assoc (k D q' (-D.simpleTorus i) ^ r), ← pow_add, hrs, ← mul_assoc (simpleKInv D q' j),
    mul_assoc (simpleKInv D q' j * _)]
  dsimp only [qᵢ]; rw [← zpow_add₀ hqᵢ, ← zpow_add₀ hqᵢ, ← zpow_add₀ hqᵢ]
  convert one_smul K _; rw [← zpow_zero (q' ^ D.symmetrizer i)]; congr 1
  rw [cartan_eq_one_sub_serreLength D hij, ← hrs]; push_cast; ring

private theorem antipode_serreE {i j : ι} (hij : i ≠ j) :
    serreElement (q ^ D.symmetrizer i) (serreLength D i j)
      (op (-normE D q i)) (op (-normE D q j)) = 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · set qᵢ : K := q ^ D.symmetrizer i; apply unop_injective
    rw [unop_zero, serreElement_def, Finset.unop_sum, ← Finset.Nat.sum_antidiagonal_swap]
    dsimp only [Prod.swap]
    trans ∑ p ∈ Finset.antidiagonal (serreLength D i j),
        -((simpleKInv D q j * simpleKInv D q i ^ serreLength D i j) *
          (((-1 : K) ^ p.1 * quantumBinomial qᵢ (serreLength D i j) p.1) •
            (e D q i ^ p.1 * e D q j * e D q i ^ p.2)))
    · refine Finset.sum_congr rfl fun p hp ↦ ?_
      have hrs := Finset.mem_antidiagonal.mp hp
      have hsym : quantumBinomial qᵢ (serreLength D i j) p.2 =
          quantumBinomial qᵢ (serreLength D i j) p.1 := by
        simpa [← hrs, Nat.add_sub_cancel_left] using
          quantumBinomial_symm qᵢ (by omega : p.1 ≤ serreLength D i j)
      simp only [unop_smul, unop_mul, unop_pow, unop_op]
      rw [← neg_one_smul K (normE D q i), smul_pow, smul_pow, neg_mul, mul_neg, smul_neg]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hsym]
      rw [← mul_assoc (normE D q i ^ p.1), normE_pow_mul_normE_mul_normE_pow D hq hij hrs]; congr 2
      have hsq : (-1 : K) ^ p.2 * (-1 : K) ^ p.2 = 1 := by rw [← mul_pow]; simp
      linear_combination ((-1 : K) ^ p.1 * quantumBinomial qᵢ (serreLength D i j) p.1) * hsq
    · rw [Finset.sum_neg_distrib, ← Finset.mul_sum, ← serreElement_def, serre_e hij, mul_zero,
        neg_zero]

private theorem antipode_serreF {i j : ι} (hij : i ≠ j) :
    serreElement (q ^ D.symmetrizer i) (serreLength D i j)
      (op (-normF D q i)) (op (-normF D q j)) = 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · have hscale : ∀ m : ι, op (-normF D q m) = (q ^ D.symmetrizer m) ^ 2 •
        (AlgHom.op (chevalleyEquiv D q).toAlgHom) (op (-normE D q m)) := fun m ↦
      unop_injective <| by
        simp [normE_def, normF_def, simpleK_mul_f_self, smul_smul, inv_pow,
          mul_inv_cancel₀ (pow_ne_zero 2 (pow_ne_zero _ hq))]
    have h := congrArg (AlgHom.op (chevalleyEquiv D q).toAlgHom) (antipode_serreE D q hij)
    rw [map_serreElement, map_zero] at h
    rw [hscale i, hscale j, serreElement_smul, h, smul_zero]

/-- The unconditional opposite-valued antipode `S : U →ₐ[K] Uᵐᵒᵖ`. -/
def antipodeOp : QuantumEnvelopingAlgebra D q →ₐ[K] (QuantumEnvelopingAlgebra D q)ᵐᵒᵖ :=
  lift
    { e i := op (-normE D q i), f i := op (-normF D q i), k y := op (k D q (-y))
      k_zero := by simp
      k_mul_k y₁ y₂ := unop_injective (by simp [k_mul_k, add_comm])
      k_mul_e y i := unop_injective <| by
        simp only [unop_mul, unop_op, unop_smul, normE_def, neg_mul, mul_neg, mul_assoc, smul_neg]
        rw [e_mul_k_neg, mul_smul_comm, ← mul_assoc, (commute_k _ _).eq, mul_assoc]
      k_mul_f y i := unop_injective <| by
        simp only [unop_mul, unop_op, unop_smul, normF_def, neg_mul, mul_neg, mul_assoc, smul_neg]
        rw [← (commute_k _ _).eq, ← mul_assoc, f_mul_k_neg, smul_mul_assoc, mul_assoc]
      e_mul_f_sub_f_mul_e_self i := unop_injective <| by
        simp only [unop_sub, unop_mul, unop_op, unop_smul, normE_def, normF_def, neg_mul_neg,
          neg_neg]
        have hef0 : e D q i * f D q i ∈ grade D q 0 := by
          simpa using SetLike.mul_mem_graded (e_mem_grade (D := D) (q := q) i) (f_mem_grade i)
        have hconj : simpleKInv D q i * e D q i * (f D q i * simpleK D q i) =
            e D q i * f D q i := by
          simpa [mul_assoc] using k_mul_mul_k_neg_of_mem_grade hef0 (-D.simpleTorus i)
        have hcancel : f D q i * simpleK D q i * (simpleKInv D q i * e D q i) =
            f D q i * e D q i := by simp [mul_assoc, ← mul_assoc (simpleK D q i)]
        rw [hcancel, hconj, ← neg_sub (e D q i * f D q i), e_mul_f_sub_f_mul_e_self,
          ← smul_neg, neg_sub]
      e_mul_f_of_ne {i j} hij := by
        rcases eq_or_ne q 0 with rfl | hq
        · simp
        · apply unop_injective
          simp only [unop_mul, unop_op, normE_def, normF_def, neg_mul_neg]
          rw [mul_assoc (f D q j), ← mul_assoc (simpleK D q j), (commute_k _ _).eq,
            mul_assoc (simpleKInv D q i), simpleK_mul_e, mul_smul_comm, mul_smul_comm,
            ← mul_assoc (f D q j), f_mul_simpleKInv, smul_mul_assoc, smul_smul,
            pow_symmetrizer_zpow_cartan_mul_neg hq i j, one_smul, mul_assoc (simpleKInv D q i),
            ← mul_assoc (f D q j), ← e_mul_f_of_ne hij]; simp [mul_assoc]
      serre_e hij := antipode_serreE D q hij, serre_f hij := antipode_serreF D q hij }

theorem antipodeOp_e (i : ι) :
    antipodeOp D q (e D q i) = op (-(simpleKInv D q i * e D q i)) := by simp [antipodeOp, normE_def]
theorem antipodeOp_f (i : ι) :
    antipodeOp D q (f D q i) = op (-(f D q i * simpleK D q i)) := by simp [antipodeOp, normF_def]
theorem antipodeOp_k (y : Y) :
    antipodeOp D q (k D q y) = op (k D q (-y)) := by simp [antipodeOp]
/-- The unconditional opposite-valued inverse antipode `S⁻¹ : U →ₐ[K] Uᵐᵒᵖ`. -/
def antipodeInvOp : QuantumEnvelopingAlgebra D q →ₐ[K] (QuantumEnvelopingAlgebra D q)ᵐᵒᵖ :=
  (AlgHom.op (chevalleyEquiv D q).toAlgHom).comp
    ((antipodeOp D q).comp (chevalleyEquiv D q).toAlgHom)
@[simp] theorem antipodeInvOp_e (i : ι) :
    antipodeInvOp D q (e D q i) = op (-(e D q i * simpleKInv D q i)) := by
  simp [antipodeInvOp, antipodeOp_f]
@[simp] theorem antipodeInvOp_f (i : ι) :
    antipodeInvOp D q (f D q i) = op (-(simpleK D q i * f D q i)) := by
  simp [antipodeInvOp, antipodeOp_e]
@[simp] theorem antipodeInvOp_k (y : Y) :
    antipodeInvOp D q (k D q y) = op (k D q (-y)) := by simp [antipodeInvOp, antipodeOp_k]
/-- Unconditional algebra equivalence `U ≃ₐ[K] Uᵐᵒᵖ` given by `antipodeOp` and `antipodeInvOp`. -/
def antipodeOpEquiv : QuantumEnvelopingAlgebra D q ≃ₐ[K] (QuantumEnvelopingAlgebra D q)ᵐᵒᵖ :=
  AlgEquiv.ofAlgHom (antipodeOp D q) (AlgHom.opComm (antipodeInvOp D q))
    (AlgHom.opComm.symm.injective <| by
      ext i <;> exact unop_injective (unop_injective
        (by simp [antipodeOp_e, antipodeOp_f, antipodeOp_k, op_neg, op_mul, mul_assoc])))
    (by ext i <;> simp [antipodeOp_e, antipodeOp_f, antipodeOp_k, op_neg, op_mul, mul_assoc])
@[simp] theorem antipodeOpEquiv_toAlgHom : (antipodeOpEquiv D q).toAlgHom = antipodeOp D q := (rfl)
@[simp] theorem antipodeOpEquiv_apply (x : QuantumEnvelopingAlgebra D q) :
    antipodeOpEquiv D q x = antipodeOp D q x := (rfl)
@[simp] theorem antipodeOpEquiv_symm_op (x : QuantumEnvelopingAlgebra D q) :
    (antipodeOpEquiv D q).symm (op x) = (antipodeInvOp D q x).unop := (rfl)
end Unconditional

section Hopf
open MulOpposite
open _root_.HopfAlgebra (antipode antipode_mul_antidistrib)
variable (D : CartanDatum ι X Y) (q : K)

instance instHopfAlgebra : HopfAlgebra K (QuantumEnvelopingAlgebra D q) :=
  HopfAlgebra.ofAntipodeOfAdjoin (antipodeOp D q) (adjoin_range_generator D q)
    (by
      rintro _ ⟨g, rfl⟩
      cases g <;> simp [antipodeOp_e, antipodeOp_f, antipodeOp_k, mul_assoc])
    (by
      rintro _ ⟨g, rfl⟩
      cases g <;> simp [antipodeOp_e, antipodeOp_f, antipodeOp_k, ← mul_assoc (simpleK D q _)])
@[simp] theorem antipode_e (i : ι) :
    antipode K (e D q i) = -(simpleKInv D q i * e D q i) := by simp [antipode, antipodeOp_e]
@[simp] theorem antipode_f (i : ι) :
    antipode K (f D q i) = -(f D q i * simpleK D q i) := by simp [antipode, antipodeOp_f]
@[simp] theorem antipode_k (y : Y) :
    antipode K (k D q y) = k D q (-y) := by simp [antipode, antipodeOp_k]
@[simp] theorem antipodeOp_apply (x : QuantumEnvelopingAlgebra D q) :
    antipodeOp D q x = op (antipode K x) := (rfl)

theorem antipode_quantumDividedPower_e {D : CartanDatum ι X Y} {q : K} (i : ι) (r : ℕ) :
    antipode K (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r) =
      (-1 : K) ^ r • (q ^ D.symmetrizer i) ^ ((r : ℤ) * ((r : ℤ) - 1)) •
        (simpleKInv D q i ^ r * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r) :=
  op_injective <| by
    rw [← antipodeOp_apply, map_quantumDividedPower, antipodeOp_e, ← normE_def,
      ← op_quantumDividedPower, quantumDividedPower_neg_normE]
theorem antipode_quantumDividedPower_f {D : CartanDatum ι X Y} {q : K} (i : ι) (r : ℕ) :
    antipode K (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) r) =
      (-1 : K) ^ r • (q ^ D.symmetrizer i) ^ (-((r : ℤ) * ((r : ℤ) - 1))) •
        (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) r * simpleK D q i ^ r) :=
  op_injective <| by
    rw [← antipodeOp_apply, map_quantumDividedPower, antipodeOp_f, ← normF_def,
      ← op_quantumDividedPower, quantumDividedPower_neg_normF]
theorem antipode_bijective :
    Function.Bijective (antipode K : QuantumEnvelopingAlgebra D q →ₗ[K] _) :=
  ⟨fun _ _ hab ↦ (antipodeOpEquiv D q).injective (congrArg op hab), fun b ↦
    ⟨(antipodeOpEquiv D q).symm (op b),
      op_injective ((antipodeOpEquiv D q).apply_symm_apply (op b))⟩⟩

@[simp] theorem inverseAntipode_e (i : ι) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (e D q i) =
      -(e D q i * simpleKInv D q i) :=
  (antipode_bijective D q).injective <| by simp [antipode_mul_antidistrib]
@[simp] theorem inverseAntipode_f (i : ι) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (f D q i) =
      -(simpleK D q i * f D q i) :=
  (antipode_bijective D q).injective <| by simp [antipode_mul_antidistrib, mul_assoc]
@[simp] theorem inverseAntipode_k (y : Y) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (k D q y) = k D q (-y) :=
  (antipode_bijective D q).injective <| by simp

theorem antipode_antipode_e (i : ι) :
    antipode K (antipode K (e D q i)) = (q ^ D.symmetrizer i)⁻¹ ^ 2 • e D q i := by
  rw [antipode_e, map_neg, antipode_mul_antidistrib, antipode_e, antipode_k, neg_neg, neg_mul,
    neg_neg, mul_assoc, e_mul_k, D.pairing_root_simpleTorus_self, mul_smul_comm, ← mul_assoc,
    k_mul_k, neg_add_cancel, k_zero, one_mul, mul_comm (2 : ℤ), ← mul_neg, zpow_mul, zpow_natCast,
    zpow_neg, zpow_ofNat, inv_pow]
theorem antipode_antipode_f (i : ι) :
    antipode K (antipode K (f D q i)) = (q ^ D.symmetrizer i) ^ 2 • f D q i := by
  rw [antipode_f, map_neg, antipode_mul_antidistrib, antipode_k, antipode_f, mul_neg, neg_neg,
    ← mul_assoc, k_mul_f, map_neg, neg_neg, D.pairing_root_simpleTorus_self, smul_mul_assoc,
    mul_assoc, k_mul_k, neg_add_cancel, k_zero, mul_one, mul_comm (2 : ℤ), zpow_mul, zpow_natCast,
    zpow_ofNat]
theorem antipode_antipode_k (y : Y) : antipode K (antipode K (k D q y)) = k D q y := by simp

theorem antipode_antipode_of_forall_pairing_root_eq {D : CartanDatum ι X Y} {q : K} {c : Y}
    (hc : ∀ i, D.pairing (D.root i) c = 2 * (D.symmetrizer i : ℤ))
    (x : QuantumEnvelopingAlgebra D q) :
    antipode K (antipode K x) = k D q (-c) * x * k D q c := by
  let sq : QuantumEnvelopingAlgebra D q →ₐ[K] QuantumEnvelopingAlgebra D q :=
    (AlgHom.opComm (antipodeOp D q)).comp (antipodeOp D q)
  have hsq : ∀ a, sq a = antipode K (antipode K a) := fun _ ↦ rfl
  let cj : QuantumEnvelopingAlgebra D q →ₐ[K] QuantumEnvelopingAlgebra D q :=
    { toFun a := k D q (-c) * a * k D q c, map_one' := by simp, map_mul' _ _ := by simp [mul_assoc],
      map_zero' := by simp, map_add' _ _ := by simp [mul_add, add_mul],
      commutes' _ := by simp [Algebra.algebraMap_eq_smul_one] }
  have h : sq = cj := by
    ext i
    · have he := k_mul_mul_k_neg_of_mem_grade (e_mem_grade (D := D) (q := q) i) (-c)
      rw [neg_neg, map_neg, hc i, mul_comm (2 : ℤ), ← mul_neg, zpow_mul, zpow_natCast,
        zpow_neg, zpow_ofNat, ← inv_pow] at he
      exact (hsq _).trans ((antipode_antipode_e D q i).trans he.symm)
    · have hf := k_mul_mul_k_neg_of_mem_grade (f_mem_grade (D := D) (q := q) i) (-c)
      rw [neg_neg, map_neg, map_neg, LinearMap.neg_apply, neg_neg, hc i, mul_comm (2 : ℤ), zpow_mul,
        zpow_natCast, zpow_ofNat] at hf
      exact (hsq _).trans ((antipode_antipode_f D q i).trans hf.symm)
    · rw [hsq, antipode_antipode_k]; simp [cj, k_mul_k, neg_add_cancel_comm]
  exact AlgHom.congr_fun h x
end Hopf
end TauCeti.QuantumEnvelopingAlgebra
