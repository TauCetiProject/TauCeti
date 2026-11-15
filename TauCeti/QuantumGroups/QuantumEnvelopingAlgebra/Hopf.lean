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

For a symmetrizable Cartan datum `D` on a full lattice pair `(X, Y)` and a parameter `q` in a
field `K`, this file establishes:

* unconditionally for every `q : K`: the normalized root operators `normE D q i = Kᵢ⁻¹ Eᵢ` and
  `normF D q i = Fᵢ Kᵢ`, and the algebra anti-automorphism `antipodeOpEquiv : U ≃ₐ[K] Uᵐᵒᵖ`
  (`Eᵢ ↦ -Kᵢ⁻¹ Eᵢ`, `Fᵢ ↦ -Fᵢ Kᵢ`, `K_y ↦ K_(-y)`) with inverse built by Chevalley conjugacy
  without assuming any coweight `2ρ^\vee` in `Y`;
* under `[IsSerreRegular D q]`: the `HopfAlgebra K (QuantumEnvelopingAlgebra D q)` instance, the
  coproducts of the normalized root operators, the antipodes of all quantum divided powers,
  bijectivity of the Hopf antipode, the action of `inverseAntipode` on the generators, and the
  inner-automorphism formula `S²(x) = K_(-c) x K_c` whenever a quantum `2ρ^\vee` coweight `c ∈ Y`
  exists (`⟨αᵢ, c⟩ = 2 dᵢ` for all `i`).

## Main definitions

* `TauCeti.QuantumEnvelopingAlgebra.normE`, `TauCeti.QuantumEnvelopingAlgebra.normF`:
  normalized root operators `Kᵢ⁻¹ Eᵢ` and `Fᵢ Kᵢ`.
* `TauCeti.QuantumEnvelopingAlgebra.antipodeOp`, `TauCeti.QuantumEnvelopingAlgebra.antipodeOpEquiv`:
  unconditional opposite-valued antipode and its algebra isomorphism with `Uᵐᵒᵖ`.
* `TauCeti.QuantumEnvelopingAlgebra.instHopfAlgebra`:
  `HopfAlgebra K (QuantumEnvelopingAlgebra D q)`.
* `TauCeti.QuantumEnvelopingAlgebra.antipodeEquiv`: the Hopf antipode as `U ≃ₐ[K] Uᵐᵒᵖ`.
* `TauCeti.QuantumEnvelopingAlgebra.antipode_bijective`: bijectivity of the Hopf antipode.
* `TauCeti.QuantumEnvelopingAlgebra.antipode_antipode_of_forall_pairing_root_eq`: inner
  automorphism formula for `S²`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §3.1.
* S. Lentner, *Quantum groups and Nichols algebras acting on conformal field theories*, Adv. Math.
  268 (2015), Theorem 3.3.
* A. Virelizier, *Quantum groups*, Graduate Studies in Mathematics, §2.3.
-/

public noncomputable section

open scoped TensorProduct

namespace TauCeti.QuantumEnvelopingAlgebra

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]

/-! ### Normalized root operators and their divided powers -/

/-- The normalized raising operator `eᵢ = Kᵢ⁻¹ * Eᵢ`. -/
def normE (D : CartanDatum ι X Y) (q : K) (i : ι) : QuantumEnvelopingAlgebra D q :=
  simpleKInv D q i * e D q i

/-- The normalized lowering operator `fᵢ = Fᵢ * Kᵢ`. -/
def normF (D : CartanDatum ι X Y) (q : K) (i : ι) : QuantumEnvelopingAlgebra D q :=
  f D q i * simpleK D q i

theorem normE_def (D : CartanDatum ι X Y) (q : K) (i : ι) :
    normE D q i = simpleKInv D q i * e D q i := (rfl)

theorem normF_def (D : CartanDatum ι X Y) (q : K) (i : ι) :
    normF D q i = f D q i * simpleK D q i := (rfl)

@[simp]
theorem normE_zero {D : CartanDatum ι X Y} (i : ι) : normE D (0 : K) i = 0 := by
  simp [normE_def]

@[simp]
theorem normF_zero {D : CartanDatum ι X Y} (i : ι) : normF D (0 : K) i = 0 := by
  simp [normF_def]

private theorem normE_pow {D : CartanDatum ι X Y} {q : K} (hq : q ≠ 0) (i : ι) (r : ℕ) :
    normE D q i ^ r =
      (q ^ D.symmetrizer i) ^ ((r : ℤ) * ((r : ℤ) - 1)) • (simpleKInv D q i ^ r * e D q i ^ r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hcomm : e D q i ^ r * simpleKInv D q i =
        (q ^ D.symmetrizer i) ^ (2 * (r : ℤ)) • (simpleKInv D q i * e D q i ^ r) := by
      calc e D q i ^ r * simpleKInv D q i
          = simpleKInv D q i * (simpleK D q i * e D q i ^ r) * simpleKInv D q i := by simp
        _ = (q ^ D.symmetrizer i) ^ (2 * (r : ℤ)) • (simpleKInv D q i * e D q i ^ r) := by
          rw [k_mul_e_pow, D.pairing_root_simpleTorus_self]
          have hexp : (r : ℤ) * (2 * (D.symmetrizer i : ℤ)) =
              (D.symmetrizer i : ℤ) * (2 * (r : ℤ)) := by ring
          rw [hexp, zpow_mul, zpow_natCast]
          simp [mul_assoc]
    rw [pow_succ, ih, normE_def, smul_mul_assoc, mul_assoc (simpleKInv D q i ^ r),
      ← mul_assoc (e D q i ^ r), hcomm]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc]
    rw [← zpow_add₀ (pow_ne_zero _ hq), ← pow_succ, mul_assoc, ← pow_succ]
    congr 2
    push_cast
    ring

private theorem normF_pow {D : CartanDatum ι X Y} {q : K} (hq : q ≠ 0) (i : ι) (r : ℕ) :
    normF D q i ^ r =
      (q ^ D.symmetrizer i) ^ (-((r : ℤ) * ((r : ℤ) - 1))) • (f D q i ^ r * simpleK D q i ^ r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hcomm : simpleK D q i ^ r * f D q i =
        (q ^ D.symmetrizer i) ^ (-(2 * (r : ℤ))) • (f D q i * simpleK D q i ^ r) := by
      rw [k_pow, k_mul_f, map_nsmul, D.pairing_root_simpleTorus_self, nsmul_eq_mul, ← k_pow]
      have hexp : -((r : ℤ) * (2 * (D.symmetrizer i : ℤ))) =
          (D.symmetrizer i : ℤ) * (-(2 * (r : ℤ))) := by ring
      rw [hexp, zpow_mul, zpow_natCast]
    rw [pow_succ, ih, normF_def, smul_mul_assoc, mul_assoc (f D q i ^ r),
      ← mul_assoc (simpleK D q i ^ r), hcomm]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc]
    rw [← zpow_add₀ (pow_ne_zero _ hq), ← pow_succ, mul_assoc, ← pow_succ]
    congr 2
    push_cast
    ring

/-- Quantum divided power of `-Kᵢ⁻¹ Eᵢ`, valid for every `q : K` and `r : ℕ`. -/
theorem quantumDividedPower_neg_normE {D : CartanDatum ι X Y} {q : K} (i : ι) (r : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (-normE D q i) r =
      (-1 : K) ^ r • (q ^ D.symmetrizer i) ^ ((r : ℤ) * ((r : ℤ) - 1)) •
        (simpleKInv D q i ^ r * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r) := by
  rcases eq_or_ne q 0 with rfl | hq
  · rcases r with _ | r
    · simp
    · simp [quantumDividedPower_zero_elem _ r.succ_ne_zero]
  · rw [← neg_one_smul K (normE D q i),
      quantumDividedPower_smul, quantumDividedPower_def, normE_pow hq,
      smul_comm ((quantumFactorial _ r)⁻¹), ← mul_smul_comm, ← quantumDividedPower_def]

/-- Quantum divided power of `-Fᵢ Kᵢ`, valid for every `q : K` and `r : ℕ`. -/
theorem quantumDividedPower_neg_normF {D : CartanDatum ι X Y} {q : K} (i : ι) (r : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (-normF D q i) r =
      (-1 : K) ^ r • (q ^ D.symmetrizer i) ^ (-((r : ℤ) * ((r : ℤ) - 1))) •
        (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) r * simpleK D q i ^ r) := by
  rcases eq_or_ne q 0 with rfl | hq
  · rcases r with _ | r
    · simp
    · simp [quantumDividedPower_zero_elem _ r.succ_ne_zero]
  · rw [← neg_one_smul K (normF D q i),
      quantumDividedPower_smul, quantumDividedPower_def, normF_pow hq,
      smul_comm ((quantumFactorial _ r)⁻¹), ← smul_mul_assoc, ← quantumDividedPower_def]

/-! ### Unconditional opposite-valued antipode -/

section Unconditional

variable (D : CartanDatum ι X Y) (q : K)

private theorem antipode_serreE_word {q' : K} (hq : q' ≠ 0) (i j : ι) {r s : ℕ}
    (hrs : r + s = serreLength D i j) :
    (simpleKInv D q' i ^ r * quantumDividedPower (q' ^ D.symmetrizer i) (e D q' i) r) *
        (simpleKInv D q' j * e D q' j) *
        (simpleKInv D q' i ^ s * quantumDividedPower (q' ^ D.symmetrizer i) (e D q' i) s) =
      ((q' ^ D.symmetrizer i) ^ ((r : ℤ) * D.cartan i j) *
          (q' ^ D.symmetrizer i) ^ ((s : ℤ) * D.cartan i j + 2 * (r : ℤ) * s)) •
        ((simpleKInv D q' j * simpleKInv D q' i ^ serreLength D i j) *
          (quantumDividedPower (q' ^ D.symmetrizer i) (e D q' i) r * e D q' j *
            quantumDividedPower (q' ^ D.symmetrizer i) (e D q' i) s)) := by
  have hcomm₁ : quantumDividedPower (q' ^ D.symmetrizer i) (e D q' i) r * simpleKInv D q' j =
      (q' ^ D.symmetrizer i) ^ ((r : ℤ) * D.cartan i j) •
        (simpleKInv D q' j * quantumDividedPower (q' ^ D.symmetrizer i) (e D q' i) r) := by
    rw [quantumDividedPower_e_mul_k, map_neg, D.pairing_root_simpleTorus, mul_neg, neg_neg,
      ← mul_assoc, mul_comm (r : ℤ), mul_assoc, zpow_mul, zpow_natCast]
  have hcomm₂ :
      (quantumDividedPower (q' ^ D.symmetrizer i) (e D q' i) r * e D q' j) *
        simpleKInv D q' i ^ s =
      (q' ^ D.symmetrizer i) ^ ((s : ℤ) * D.cartan i j + 2 * (r : ℤ) * s) •
        (simpleKInv D q' i ^ s *
          (quantumDividedPower (q' ^ D.symmetrizer i) (e D q' i) r * e D q' j)) := by
    rw [k_pow, smul_neg, mul_assoc, e_mul_k_neg, map_nsmul, D.pairing_root_simpleTorus,
      ← D.symmetrizer_mul_cartan, nsmul_eq_mul, mul_smul_comm,
      ← mul_assoc (quantumDividedPower _ _ _), quantumDividedPower_e_mul_k, map_neg, map_nsmul,
      D.pairing_root_simpleTorus_self, nsmul_eq_mul, mul_neg, neg_neg, smul_mul_assoc, smul_smul,
      ← zpow_add₀ hq, mul_assoc]
    simp only [← smul_neg, ← k_pow]
    have hexp : (s : ℤ) * ((D.symmetrizer i : ℤ) * D.cartan i j) +
        (r : ℤ) * ((s : ℤ) * (2 * (D.symmetrizer i : ℤ))) =
        (D.symmetrizer i : ℤ) * ((s : ℤ) * D.cartan i j + 2 * (r : ℤ) * s) := by ring
    rw [hexp, zpow_mul, zpow_natCast]
  calc (simpleKInv D q' i ^ r * quantumDividedPower (q' ^ D.symmetrizer i) (e D q' i) r) *
          (simpleKInv D q' j * e D q' j) *
          (simpleKInv D q' i ^ s * quantumDividedPower (q' ^ D.symmetrizer i) (e D q' i) s)
      = simpleKInv D q' i ^ r *
          (quantumDividedPower (q' ^ D.symmetrizer i) (e D q' i) r * simpleKInv D q' j) *
          e D q' j * simpleKInv D q' i ^ s *
          quantumDividedPower (q' ^ D.symmetrizer i) (e D q' i) s := by
        simp only [mul_assoc]
    _ = (q' ^ D.symmetrizer i) ^ ((r : ℤ) * D.cartan i j) •
          ((simpleKInv D q' i ^ r * simpleKInv D q' j) *
            ((quantumDividedPower (q' ^ D.symmetrizer i) (e D q' i) r * e D q' j) *
              simpleKInv D q' i ^ s) *
            quantumDividedPower (q' ^ D.symmetrizer i) (e D q' i) s) := by
        rw [hcomm₁]
        simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = _ := by
        rw [(commute_k _ _).pow_left r |>.eq, hcomm₂]
        simp only [mul_smul_comm, smul_mul_assoc, smul_smul]
        congr 1
        rw [mul_assoc (simpleKInv D q' j), ← mul_assoc (simpleKInv D q' i ^ r), ← pow_add, hrs]
        simp only [mul_assoc]

private theorem antipode_serreE_term {q' : K} (hq : q' ≠ 0) {i j : ι} (hij : i ≠ j)
    {r s : ℕ} (hrs : r + s = serreLength D i j) :
    (-1 : K) ^ s •
        (quantumDividedPower (q' ^ D.symmetrizer i) (-normE D q' i) r * (-normE D q' j) *
          quantumDividedPower (q' ^ D.symmetrizer i) (-normE D q' i) s) =
      -((simpleKInv D q' j * simpleKInv D q' i ^ serreLength D i j) *
        ((-1 : K) ^ r •
          (quantumDividedPower (q' ^ D.symmetrizer i) (e D q' i) r * e D q' j *
            quantumDividedPower (q' ^ D.symmetrizer i) (e D q' i) s))) := by
  set qᵢ : K := q' ^ D.symmetrizer i
  have hqᵢ : qᵢ ≠ 0 := pow_ne_zero _ hq
  rw [quantumDividedPower_neg_normE, quantumDividedPower_neg_normE, normE_def, mul_neg, neg_mul,
    smul_neg, ← neg_smul]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [antipode_serreE_word D hq i j hrs, smul_smul, ← neg_smul]
  congr 1
  have hqpow :
      qᵢ ^ ((s : ℤ) * ((s : ℤ) - 1)) * qᵢ ^ ((r : ℤ) * ((r : ℤ) - 1)) *
        qᵢ ^ ((r : ℤ) * D.cartan i j) * qᵢ ^ ((s : ℤ) * D.cartan i j + 2 * (r : ℤ) * s) = 1 := by
    rw [← zpow_add₀ hqᵢ, ← zpow_add₀ hqᵢ, ← zpow_add₀ hqᵢ, ← zpow_zero qᵢ]
    congr 1
    rw [cartan_eq_one_sub_serreLength D hij, ← hrs]
    push_cast
    ring
  have hsign : (-1 : K) ^ s * (-1 : K) ^ s = 1 := by
    rw [← mul_pow]
    simp
  calc _ = -((-1 : K) ^ s * (-1 : K) ^ s) * (-1 : K) ^ r *
          (qᵢ ^ ((s : ℤ) * ((s : ℤ) - 1)) * qᵢ ^ ((r : ℤ) * ((r : ℤ) - 1)) *
            qᵢ ^ ((r : ℤ) * D.cartan i j) *
            qᵢ ^ ((s : ℤ) * D.cartan i j + 2 * (r : ℤ) * s)) := by ring
    _ = _ := by
      rw [hqpow, hsign]
      ring

private theorem antipode_serreE {i j : ι} (hij : i ≠ j) :
    serreElement (q ^ D.symmetrizer i) (serreLength D i j)
      (MulOpposite.op (-normE D q i)) (MulOpposite.op (-normE D q j)) = 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · apply MulOpposite.unop_injective
    rw [MulOpposite.unop_zero, serreElement_def, Finset.unop_sum]
    have hunop : ∀ p : ℕ × ℕ,
        ((-1 : K) ^ p.1 •
          (quantumDividedPower (q ^ D.symmetrizer i) (MulOpposite.op (-normE D q i)) p.1 *
            MulOpposite.op (-normE D q j) *
            quantumDividedPower (q ^ D.symmetrizer i) (MulOpposite.op (-normE D q i)) p.2)).unop =
        (-1 : K) ^ p.1 •
          (quantumDividedPower (q ^ D.symmetrizer i) (-normE D q i) p.2 * (-normE D q j) *
            quantumDividedPower (q ^ D.symmetrizer i) (-normE D q i) p.1) := by
      intro p
      rw [← op_quantumDividedPower, ← op_quantumDividedPower]
      simp only [MulOpposite.unop_smul, MulOpposite.unop_mul, MulOpposite.unop_op, mul_assoc]
    rw [Finset.sum_congr rfl fun p _ ↦ hunop p, ← Finset.Nat.sum_antidiagonal_swap]
    dsimp only [Prod.swap]
    have hterm : ∀ p ∈ Finset.antidiagonal (serreLength D i j),
        (-1 : K) ^ p.2 •
          (quantumDividedPower (q ^ D.symmetrizer i) (-normE D q i) p.1 * (-normE D q j) *
            quantumDividedPower (q ^ D.symmetrizer i) (-normE D q i) p.2) =
        -((simpleKInv D q j * simpleKInv D q i ^ serreLength D i j) *
          ((-1 : K) ^ p.1 •
            (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) p.1 * e D q j *
              quantumDividedPower (q ^ D.symmetrizer i) (e D q i) p.2))) :=
      fun p hp ↦ antipode_serreE_term D hq hij (Finset.mem_antidiagonal.mp hp)
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, ← Finset.mul_sum,
      ← serreElement_def, serre_e hij, mul_zero, neg_zero]

private theorem antipode_serreF {i j : ι} (hij : i ≠ j) :
    serreElement (q ^ D.symmetrizer i) (serreLength D i j)
      (MulOpposite.op (-normF D q i)) (MulOpposite.op (-normF D q j)) = 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · have hscale : ∀ m : ι, MulOpposite.op (-normF D q m) =
        (q ^ D.symmetrizer m) ^ 2 •
          (AlgHom.op (chevalleyEquiv D q).toAlgHom) (MulOpposite.op (-normE D q m)) := by
      intro m
      apply MulOpposite.unop_injective
      simp [normE_def, normF_def, simpleK_mul_f_self, smul_smul, inv_pow,
        mul_inv_cancel₀ (pow_ne_zero 2 (pow_ne_zero _ hq))]
    have h := congrArg (AlgHom.op (chevalleyEquiv D q).toAlgHom) (antipode_serreE D q hij)
    rw [AlgHomClass.map_serreElement, map_zero] at h
    rw [hscale i, hscale j, serreElement_smul, h, smul_zero]

private def antipodeTuple : GeneratorTuple D q (QuantumEnvelopingAlgebra D q)ᵐᵒᵖ where
  e i := MulOpposite.op (-normE D q i)
  f i := MulOpposite.op (-normF D q i)
  k y := MulOpposite.op (k D q (-y))
  k_zero := by simp
  k_mul_k y₁ y₂ := by
    apply MulOpposite.unop_injective
    simp [k_mul_k, add_comm]
  k_mul_e y i := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul, normE_def,
      neg_mul, mul_neg, mul_assoc, smul_neg]
    rw [e_mul_k_neg, mul_smul_comm, ← mul_assoc, commute_k _ _ |>.eq, mul_assoc]
  k_mul_f y i := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul, normF_def,
      neg_mul, mul_neg, mul_assoc, smul_neg]
    rw [← commute_k _ _ |>.eq, ← mul_assoc, f_mul_k_neg, smul_mul_assoc, mul_assoc]
  e_mul_f_sub_f_mul_e_self i := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_sub, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_smul, normE_def, normF_def, neg_mul_neg, neg_neg]
    have hef0 : e D q i * f D q i ∈ grade D q 0 := by
      simpa using SetLike.mul_mem_graded (e_mem_grade (D := D) (q := q) i) (f_mem_grade i)
    have hconj : simpleKInv D q i * (e D q i * f D q i) * simpleK D q i =
        e D q i * f D q i := by
      simpa using k_mul_mul_k_neg_of_mem_grade hef0 (-D.simpleTorus i)
    have hcancel : f D q i * simpleK D q i * (simpleKInv D q i * e D q i) =
        f D q i * e D q i := by
      simp [mul_assoc, ← mul_assoc (simpleK D q i)]
    have hconj' : simpleKInv D q i * e D q i * (f D q i * simpleK D q i) =
        e D q i * f D q i := by
      simpa [mul_assoc] using hconj
    rw [hcancel, hconj', ← neg_sub (e D q i * f D q i), e_mul_f_sub_f_mul_e_self,
      ← smul_neg, neg_sub]
  e_mul_f_of_ne {i j} hij := by
    rcases eq_or_ne q 0 with rfl | hq
    · simp
    · apply MulOpposite.unop_injective
      simp only [MulOpposite.unop_mul, MulOpposite.unop_op, normE_def, normF_def, neg_mul_neg]
      rw [mul_assoc (f D q j), ← mul_assoc (simpleK D q j), commute_k _ _ |>.eq,
        mul_assoc (simpleKInv D q i), simpleK_mul_e, mul_smul_comm, mul_smul_comm,
        ← mul_assoc (f D q j), f_mul_simpleKInv, smul_mul_assoc, smul_smul,
        pow_symmetrizer_zpow_cartan_mul_neg hq i j, one_smul, mul_assoc (simpleKInv D q i),
        ← mul_assoc (f D q j), ← e_mul_f_of_ne hij]
      simp [mul_assoc]
  serre_e hij := antipode_serreE D q hij
  serre_f hij := antipode_serreF D q hij

/-- The unconditional opposite-valued antipode `S : U →ₐ[K] Uᵐᵒᵖ`, sending `Eᵢ ↦ op (-Kᵢ⁻¹ Eᵢ)`,
`Fᵢ ↦ op (-Fᵢ Kᵢ)`, and `K_y ↦ op (K_(-y))` for every parameter `q : K`. -/
def antipodeOp : QuantumEnvelopingAlgebra D q →ₐ[K] (QuantumEnvelopingAlgebra D q)ᵐᵒᵖ :=
  lift (antipodeTuple D q)

@[simp]
theorem antipodeOp_e (i : ι) :
    antipodeOp D q (e D q i) = MulOpposite.op (-(simpleKInv D q i * e D q i)) := by
  simp [antipodeOp, antipodeTuple, normE_def]

@[simp]
theorem antipodeOp_f (i : ι) :
    antipodeOp D q (f D q i) = MulOpposite.op (-(f D q i * simpleK D q i)) := by
  simp [antipodeOp, antipodeTuple, normF_def]

@[simp]
theorem antipodeOp_k (y : Y) :
    antipodeOp D q (k D q y) = MulOpposite.op (k D q (-y)) := by
  simp [antipodeOp, antipodeTuple]

/-- The unconditional opposite-valued inverse antipode `S⁻¹ : U →ₐ[K] Uᵐᵒᵖ`, constructed by
conjugating `antipodeOp` with `chevalleyEquiv` so that no coweight `2ρ^\vee ∈ Y` is needed. -/
def antipodeInvOp : QuantumEnvelopingAlgebra D q →ₐ[K] (QuantumEnvelopingAlgebra D q)ᵐᵒᵖ :=
  (AlgHom.op (chevalleyEquiv D q).toAlgHom).comp
    ((antipodeOp D q).comp (chevalleyEquiv D q).toAlgHom)

@[simp]
theorem antipodeInvOp_e (i : ι) :
    antipodeInvOp D q (e D q i) = MulOpposite.op (-(e D q i * simpleKInv D q i)) := by
  simp [antipodeInvOp]

@[simp]
theorem antipodeInvOp_f (i : ι) :
    antipodeInvOp D q (f D q i) = MulOpposite.op (-(simpleK D q i * f D q i)) := by
  simp [antipodeInvOp]

@[simp]
theorem antipodeInvOp_k (y : Y) :
    antipodeInvOp D q (k D q y) = MulOpposite.op (k D q (-y)) := by
  simp [antipodeInvOp]

private theorem opComm_antipodeInvOp_comp_antipodeOp :
    (AlgHom.opComm (antipodeInvOp D q)).comp (antipodeOp D q) =
      AlgHom.id K (QuantumEnvelopingAlgebra D q) := by
  ext i
  · have h : MulOpposite.op (-(simpleKInv D q i * e D q i)) =
        -(MulOpposite.op (e D q i) * MulOpposite.op (simpleKInv D q i)) := by
      simp [← MulOpposite.op_mul, ← MulOpposite.op_neg]
    simp [h, mul_assoc]
  · have h : MulOpposite.op (-(f D q i * simpleK D q i)) =
        -(MulOpposite.op (simpleK D q i) * MulOpposite.op (f D q i)) := by
      simp [← MulOpposite.op_mul, ← MulOpposite.op_neg]
    simp [h, ← mul_assoc]
  · simp

private theorem antipodeOp_comp_opComm_antipodeInvOp :
    (antipodeOp D q).comp (AlgHom.opComm (antipodeInvOp D q)) =
      AlgHom.id K (QuantumEnvelopingAlgebra D q)ᵐᵒᵖ := by
  apply AlgHom.opComm.symm.injective
  ext i
  · apply MulOpposite.unop_injective
    apply MulOpposite.unop_injective
    have h : MulOpposite.op (-(e D q i * simpleKInv D q i)) =
        -(MulOpposite.op (simpleKInv D q i) * MulOpposite.op (e D q i)) := by
      simp [← MulOpposite.op_mul, ← MulOpposite.op_neg]
    simp [h]
  · apply MulOpposite.unop_injective
    apply MulOpposite.unop_injective
    have h : MulOpposite.op (-(simpleK D q i * f D q i)) =
        -(MulOpposite.op (f D q i) * MulOpposite.op (simpleK D q i)) := by
      simp [← MulOpposite.op_mul, ← MulOpposite.op_neg]
    simp [h, mul_assoc]
  · simp

/-- The unconditional algebra isomorphism `QuantumEnvelopingAlgebra D q ≃ₐ[K]
(QuantumEnvelopingAlgebra D q)ᵐᵒᵖ` given by `antipodeOp` and `antipodeInvOp`, valid for every
Cartan datum `D` and every field parameter `q : K`. -/
def antipodeOpEquiv :
    QuantumEnvelopingAlgebra D q ≃ₐ[K] (QuantumEnvelopingAlgebra D q)ᵐᵒᵖ :=
  AlgEquiv.ofAlgHom (antipodeOp D q) (AlgHom.opComm (antipodeInvOp D q))
    (antipodeOp_comp_opComm_antipodeInvOp D q)
    (opComm_antipodeInvOp_comp_antipodeOp D q)

@[simp]
theorem antipodeOpEquiv_toAlgHom : (antipodeOpEquiv D q).toAlgHom = antipodeOp D q := (rfl)

@[simp]
theorem antipodeOpEquiv_apply (x : QuantumEnvelopingAlgebra D q) :
    antipodeOpEquiv D q x = antipodeOp D q x := (rfl)

@[simp]
theorem antipodeOpEquiv_symm_op (x : QuantumEnvelopingAlgebra D q) :
    (antipodeOpEquiv D q).symm (MulOpposite.op x) = (antipodeInvOp D q x).unop := (rfl)

end Unconditional

/-! ### The Hopf algebra structure, divided-power antipodes, and `S²` -/

section Hopf

variable (D : CartanDatum ι X Y) (q : K) [IsSerreRegular D q]

/-- The `K`-Hopf algebra structure on `QuantumEnvelopingAlgebra D q`. -/
instance instHopfAlgebra : HopfAlgebra K (QuantumEnvelopingAlgebra D q) :=
  HopfAlgebra.ofAntipodeOfAdjoin (antipodeOp D q) (adjoin_range_generator D q)
    (by
      rintro _ ⟨g, rfl⟩
      cases g <;> simp [mul_assoc])
    (by
      rintro _ ⟨g, rfl⟩
      cases g <;> simp [← mul_assoc (simpleK D q _)])

@[simp]
theorem antipode_e (i : ι) :
    HopfAlgebra.antipode K (e D q i) = -(simpleKInv D q i * e D q i) := by
  simp [HopfAlgebra.antipode]

@[simp]
theorem antipode_f (i : ι) :
    HopfAlgebra.antipode K (f D q i) = -(f D q i * simpleK D q i) := by
  simp [HopfAlgebra.antipode]

@[simp]
theorem antipode_k (y : Y) :
    HopfAlgebra.antipode K (k D q y) = k D q (-y) := by
  simp [HopfAlgebra.antipode]

@[simp]
theorem antipodeOp_apply (x : QuantumEnvelopingAlgebra D q) :
    antipodeOp D q x = MulOpposite.op (HopfAlgebra.antipode K x) := (rfl)

/-- Coproduct of the normalized raising operator `eᵢ = Kᵢ⁻¹ Eᵢ`:
`Δ(eᵢ) = eᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ eᵢ`. -/
@[simp]
theorem comul_normE (i : ι) :
    Coalgebra.comul (R := K) (normE D q i) =
      normE D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] normE D q i := by
  rw [normE_def, ← Bialgebra.comulAlgHom_apply, map_mul, Bialgebra.comulAlgHom_apply,
    Bialgebra.comulAlgHom_apply, comul_k, comul_e]
  simp [mul_add, Algebra.TensorProduct.tmul_mul_tmul]

/-- Coproduct of the normalized lowering operator `fᵢ = Fᵢ Kᵢ`:
`Δ(fᵢ) = fᵢ ⊗ 1 + Kᵢ ⊗ fᵢ`. -/
@[simp]
theorem comul_normF (i : ι) :
    Coalgebra.comul (R := K) (normF D q i) =
      normF D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] normF D q i := by
  rw [normF_def, ← Bialgebra.comulAlgHom_apply, map_mul, Bialgebra.comulAlgHom_apply,
    Bialgebra.comulAlgHom_apply, comul_f, comul_k]
  simp [add_mul, Algebra.TensorProduct.tmul_mul_tmul]

/-- **Antipode of raising quantum divided powers**:
`S(Eᵢ^(r)) = (-1)^r qᵢ^(r(r-1)) • (Kᵢ⁻¹^r * Eᵢ^(r))` for every `r : ℕ`. -/
theorem antipode_quantumDividedPower_e {D : CartanDatum ι X Y} {q : K} [IsSerreRegular D q]
    (i : ι) (r : ℕ) :
    HopfAlgebra.antipode K (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r) =
      (-1 : K) ^ r • (q ^ D.symmetrizer i) ^ ((r : ℤ) * ((r : ℤ) - 1)) •
        (simpleKInv D q i ^ r * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) r) := by
  apply MulOpposite.op_injective
  rw [← antipodeOp_apply, AlgHomClass.map_quantumDividedPower, antipodeOp_e, ← normE_def,
    ← op_quantumDividedPower, quantumDividedPower_neg_normE]

/-- **Antipode of lowering quantum divided powers**:
`S(Fᵢ^(r)) = (-1)^r qᵢ^(-r(r-1)) • (Fᵢ^(r) * Kᵢ^r)` for every `r : ℕ`. -/
theorem antipode_quantumDividedPower_f {D : CartanDatum ι X Y} {q : K} [IsSerreRegular D q]
    (i : ι) (r : ℕ) :
    HopfAlgebra.antipode K (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) r) =
      (-1 : K) ^ r • (q ^ D.symmetrizer i) ^ (-((r : ℤ) * ((r : ℤ) - 1))) •
        (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) r * simpleK D q i ^ r) := by
  apply MulOpposite.op_injective
  rw [← antipodeOp_apply, AlgHomClass.map_quantumDividedPower, antipodeOp_f, ← normF_def,
    ← op_quantumDividedPower, quantumDividedPower_neg_normF]

/-- The Hopf antipode as an algebra isomorphism onto the opposite algebra. -/
def antipodeEquiv :
    QuantumEnvelopingAlgebra D q ≃ₐ[K] (QuantumEnvelopingAlgebra D q)ᵐᵒᵖ :=
  antipodeOpEquiv D q

@[simp]
theorem antipodeEquiv_apply (x : QuantumEnvelopingAlgebra D q) :
    antipodeEquiv D q x = MulOpposite.op (HopfAlgebra.antipode K x) := (rfl)

/-- The Hopf antipode of `QuantumEnvelopingAlgebra D q` is bijective, without requiring any
coweight `2ρ^\vee ∈ Y`. -/
theorem antipode_bijective :
    Function.Bijective
      (HopfAlgebra.antipode K :
        QuantumEnvelopingAlgebra D q →ₗ[K] QuantumEnvelopingAlgebra D q) :=
  ⟨fun _ _ hab ↦ (antipodeEquiv D q).injective (congrArg MulOpposite.op hab), fun b ↦
    ⟨(antipodeEquiv D q).symm (MulOpposite.op b),
      MulOpposite.op_injective ((antipodeEquiv D q).apply_symm_apply (MulOpposite.op b))⟩⟩

@[simp]
theorem inverseAntipode_e (i : ι) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (e D q i) =
      -(e D q i * simpleKInv D q i) := by
  apply (antipode_bijective D q).injective
  simp [HopfAlgebra.antipode_mul_antidistrib]

@[simp]
theorem inverseAntipode_f (i : ι) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (f D q i) =
      -(simpleK D q i * f D q i) := by
  apply (antipode_bijective D q).injective
  simp [HopfAlgebra.antipode_mul_antidistrib, mul_assoc]

@[simp]
theorem inverseAntipode_k (y : Y) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (k D q y) =
      k D q (-y) := by
  apply (antipode_bijective D q).injective
  simp

/-- Action of the squared antipode `S²` on `Eᵢ`: `S(S(Eᵢ)) = qᵢ⁻² • Eᵢ`. -/
theorem antipode_antipode_e (i : ι) :
    HopfAlgebra.antipode K (HopfAlgebra.antipode K (e D q i)) =
      (q ^ D.symmetrizer i)⁻¹ ^ 2 • e D q i := by
  rw [antipode_e, map_neg, HopfAlgebra.antipode_mul_antidistrib, antipode_e, antipode_k,
    neg_neg, neg_mul, neg_neg, mul_assoc, e_mul_k, D.pairing_root_simpleTorus_self,
    mul_smul_comm, ← mul_assoc, k_mul_k, neg_add_cancel, k_zero, one_mul]
  congr 1
  have hexp : -(2 * (D.symmetrizer i : ℤ)) = -(((D.symmetrizer i * 2 : ℕ) : ℤ)) := by
    push_cast
    ring
  rw [hexp, zpow_neg, zpow_natCast, pow_mul, ← inv_pow]

/-- Action of the squared antipode `S²` on `Fᵢ`: `S(S(Fᵢ)) = qᵢ² • Fᵢ`. -/
theorem antipode_antipode_f (i : ι) :
    HopfAlgebra.antipode K (HopfAlgebra.antipode K (f D q i)) =
      (q ^ D.symmetrizer i) ^ 2 • f D q i := by
  rw [antipode_f, map_neg, HopfAlgebra.antipode_mul_antidistrib, antipode_k, antipode_f,
    mul_neg, neg_neg, ← mul_assoc, k_mul_f, map_neg, neg_neg, D.pairing_root_simpleTorus_self,
    smul_mul_assoc, mul_assoc, k_mul_k, neg_add_cancel, k_zero, mul_one]
  congr 1
  have hexp : 2 * (D.symmetrizer i : ℤ) = ((D.symmetrizer i * 2 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hexp, zpow_natCast, pow_mul]

/-- Action of the squared antipode `S²` on `K_y`: `S(S(K_y)) = K_y`. -/
theorem antipode_antipode_k (y : Y) :
    HopfAlgebra.antipode K (HopfAlgebra.antipode K (k D q y)) = k D q y := by
  simp

/-- Whenever `c ∈ Y` satisfies `⟨αᵢ, c⟩ = 2 dᵢ` for all `i` (a quantum `2ρ^\vee` coweight), the
square of the antipode is the inner automorphism `x ↦ K_(-c) x K_c`. -/
theorem antipode_antipode_of_forall_pairing_root_eq {D : CartanDatum ι X Y} {q : K}
    [IsSerreRegular D q] {c : Y}
    (hc : ∀ i, D.pairing (D.root i) c = 2 * (D.symmetrizer i : ℤ))
    (x : QuantumEnvelopingAlgebra D q) :
    HopfAlgebra.antipode K (HopfAlgebra.antipode K x) = k D q (-c) * x * k D q c := by
  let antipodeSq : QuantumEnvelopingAlgebra D q →ₐ[K] QuantumEnvelopingAlgebra D q :=
    { toFun a := HopfAlgebra.antipode K (HopfAlgebra.antipode K a)
      map_one' := by simp
      map_mul' a b := by simp [HopfAlgebra.antipode_mul_antidistrib]
      map_zero' := by simp
      map_add' a b := by simp
      commutes' r := by simp [Algebra.algebraMap_eq_smul_one] }
  let conjAlgHom : QuantumEnvelopingAlgebra D q →ₐ[K] QuantumEnvelopingAlgebra D q :=
    { toFun a := k D q (-c) * a * k D q c
      map_one' := by simp
      map_mul' a b := by simp [mul_assoc]
      map_zero' := by simp
      map_add' a b := by simp [mul_add, add_mul]
      commutes' r := by simp [Algebra.algebraMap_eq_smul_one] }
  have h : antipodeSq = conjAlgHom := by
    ext i
    · simp only [antipodeSq, conjAlgHom, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk]
      rw [antipode_antipode_e, k_mul_e, map_neg, hc i, smul_mul_assoc, mul_assoc, k_mul_k,
        neg_add_cancel, k_zero, mul_one]
      congr 1
      have hexp : -(2 * (D.symmetrizer i : ℤ)) = -(((D.symmetrizer i * 2 : ℕ) : ℤ)) := by
        push_cast
        ring
      rw [hexp, zpow_neg, zpow_natCast, pow_mul, inv_pow]
    · simp only [antipodeSq, conjAlgHom, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk]
      rw [antipode_antipode_f, k_mul_f, map_neg, neg_neg, hc i, smul_mul_assoc, mul_assoc,
        k_mul_k, neg_add_cancel, k_zero, mul_one]
      congr 1
      have hexp : 2 * (D.symmetrizer i : ℤ) = ((D.symmetrizer i * 2 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [hexp, zpow_natCast, pow_mul]
    · simp only [antipodeSq, conjAlgHom, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk]
      rw [antipode_antipode_k, k_mul_k, k_mul_k]
      have hi : -c + i + c = i := by abel
      rw [hi]
  exact AlgHom.congr_fun h x

end Hopf

end TauCeti.QuantumEnvelopingAlgebra
