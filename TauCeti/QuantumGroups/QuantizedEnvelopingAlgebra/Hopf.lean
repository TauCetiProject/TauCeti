/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import TauCeti.Algebra.HopfAlgebra.Antipode
public import TauCeti.Algebra.HopfAlgebra.Basic
public import TauCeti.Algebra.HopfAlgebra.InverseAntipode
public import TauCeti.QuantumGroups.QuantizedEnvelopingAlgebra.Bialgebra
public import TauCeti.QuantumGroups.QuantizedEnvelopingAlgebra.Rescale
import Mathlib.Tactic

/-!
# The Hopf algebra structure and antipode of a quantized enveloping algebra

This file constructs the antipode of the Drinfeld–Jimbo quantized enveloping algebra
`TauCeti.QuantizedEnvelopingAlgebra D q` of a Cartan datum `D : TauCeti.CartanDatum ι X Y` over a
field `K`:

* `S(Eᵢ) = -(Kᵢ⁻¹ Eᵢ)`, `S(Fᵢ) = -(Fᵢ Kᵢ)`, `S(K_y) = K_(-y)`.

The opposite-valued algebra homomorphism `antipodeAlgHom` descends through the divided-power Serre
presentation for **every** nonzero parameter `q ≠ 0`: straightening `(Kᵢ⁻¹ Eᵢ)^(r)` and moving all
toral factors to the outside collects a total `qᵢ`-exponent
`s(s - 1) + r(r - 1) + (r + s) aᵢⱼ + 2 r s = 0` for `r + s = 1 - aᵢⱼ`, after which reversing the
summation order recovers the Serre sum.

Combining `antipodeAlgHom` with `TauCeti.QuantizedEnvelopingAlgebra.bialgebraOfSerre` yields the
explicit-hypothesis `HopfAlgebra` structure `hopfAlgebraOfSerre` under `q ≠ 0` and Serre-degree
factorial nonvanishing, and the canonical `HopfAlgebra` instance at
`[Fact (IsGenericQuantumParameter q)]`.

We also prove that `S²` equals the diagonal rescaling automorphism `Eᵢ ↦ qᵢ⁻² • Eᵢ`,
`Fᵢ ↦ qᵢ² • Fᵢ`, `K_y ↦ K_y` on **every** Cartan datum (Specializing to conjugation by
`K_(-2ρ∨)` whenever a coweight `2ρ∨ ∈ Y` satisfies `⟨αᵢ, 2ρ∨⟩ = 2 dᵢ`), deduce that `S` is
bijective and an algebra isomorphism onto the opposite algebra, and record the formulas for `S` on
divided powers and for `S⁻¹` on generators.

## Main definitions

* `TauCeti.QuantizedEnvelopingAlgebra.antipodeAlgHom`: the opposite-valued antipode `U →ₐ[K] Uᵐᵒᵖ`
  for `q ≠ 0`.
* `TauCeti.QuantizedEnvelopingAlgebra.hopfAlgebraOfSerre` and `instHopfAlgebra`: explicit-hypothesis
  and generic-parameter `HopfAlgebra` structures.
* `TauCeti.QuantizedEnvelopingAlgebra.antipodeEquiv`: the antipode as an algebra isomorphism
  `U ≃ₐ[K] Uᵐᵒᵖ`.

## Main results

* `TauCeti.QuantizedEnvelopingAlgebra.antipode_eDividedPower` and `antipode_fDividedPower`:
  `S(Eᵢ^(n)) = (-1)^n qᵢ^(n(n-1)) Kᵢ^(-n) Eᵢ^(n)` and
  `S(Fᵢ^(n)) = (-1)^n qᵢ^(-n(n-1)) Fᵢ^(n) Kᵢ^n`.
* `TauCeti.QuantizedEnvelopingAlgebra.antipode_antipode_eq_rescale` and
  `antipode_antipode_of_pairing_root`: `S²` as diagonal rescaling and as conjugation by `K_(-2ρ∨)`.
* `TauCeti.QuantizedEnvelopingAlgebra.antipode_bijective`: bijectivity of the antipode on every
  Cartan datum.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §3.1.
* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, American
  Mathematical Society, 1996, §§4.8–4.11.
-/

public section

open Finset

namespace TauCeti.QuantizedEnvelopingAlgebra

variable {K ι X Y : Type*} [Field K] [AddCommGroup X] [AddCommGroup Y]

/-! ### Opposite-valued antipode for `q ≠ 0` -/

section AntipodeOp

variable (D : CartanDatum ι X Y) {q : K}

private lemma unop_sum {α M : Type*} [AddCommMonoid M] (s : Finset α) (g : α → Mᵐᵒᵖ) :
    MulOpposite.unop (∑ x ∈ s, g x) = ∑ x ∈ s, MulOpposite.unop (g x) :=
  map_sum MulOpposite.opAddEquiv.symm g s

private lemma unop_quantumDividedPower {A : Type*} [Ring A] [Algebra K A]
    (qi : K) (x : A) (n : ℕ) :
    MulOpposite.unop (quantumDividedPower qi (MulOpposite.op x) n) =
      quantumDividedPower qi x n := by
  rw [quantumDividedPower_def, MulOpposite.unop_smul, ← MulOpposite.op_pow,
    MulOpposite.unop_op, ← quantumDividedPower_def]

private lemma quantumDividedPower_neg_kiInv_mul_e (i : ι) (n : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (-(kiInv D q i * e D q i)) n =
      ((-1 : K) ^ n * (q ^ D.symmetrizer i) ^ (n * (n - 1))) •
        (kiInv D q i ^ n * eDividedPower D q i n) := by
  have hcomm : e D q i * kiInv D q i =
      (q ^ D.symmetrizer i) ^ 2 • (kiInv D q i * e D q i) := by
    rw [e_mul_kiInv, D.cartan_apply_self, zpow_two, ← sq]
  rw [← neg_one_smul K (kiInv D q i * e D q i), quantumDividedPower_smul,
    quantumDividedPower_mul_of_mul_eq_smul_mul _ hcomm, smul_smul, eDividedPower]

private lemma quantumDividedPower_neg_f_mul_ki (i : ι) (n : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (-(f D q i * ki D q i)) n =
      ((-1 : K) ^ n * (q ^ D.symmetrizer i)⁻¹ ^ (n * (n - 1))) •
        (fDividedPower D q i n * ki D q i ^ n) := by
  have hcomm : ki D q i * f D q i =
      (q ^ D.symmetrizer i)⁻¹ ^ 2 • (f D q i * ki D q i) := by
    rw [ki_mul_f, D.cartan_apply_self, zpow_neg, zpow_two, ← sq, inv_pow]
  rw [← quantumDividedPower_inv, ← neg_one_smul K (f D q i * ki D q i), quantumDividedPower_smul,
    quantumDividedPower_mul_right_of_mul_eq_smul_mul _ hcomm, quantumDividedPower_inv,
    smul_smul, fDividedPower]

private lemma antipode_serre_exp {m r : ℕ} (hr : r ≤ m) {a : ℤ} (ha : a = 1 - m) :
    (((m - r) * (m - r - 1) : ℕ) : ℤ) + ((r * (r - 1) : ℕ) : ℤ) +
      ((m - r : ℕ) : ℤ) * a + (r : ℤ) * a +
      2 * ((m - r : ℕ) : ℤ) * (r : ℤ) = 0 := by
  have hcast_n (k : ℕ) : ((k * (k - 1) : ℕ) : ℤ) = (k : ℤ) * ((k : ℤ) - 1) := by
    rcases k with _ | k <;> simp
  rw [hcast_n, hcast_n, ha, Nat.cast_sub hr]
  ring

private lemma eDividedPower_mul_kiInv (i j : ι) (s : ℕ) :
    eDividedPower D q i s * kiInv D q j =
      (q ^ D.symmetrizer i) ^ ((s : ℤ) * D.cartan i j) •
        (kiInv D q j * eDividedPower D q i s) := by
  rw [kiInv, eDividedPower_mul_k, map_neg, mul_neg, neg_mul, neg_neg, D.pairing_root_simpleTorus]
  have hexp : (s : ℤ) * (D.symmetrizer i * D.cartan i j) =
      D.symmetrizer i * ((s : ℤ) * D.cartan i j) := by ring
  rw [hexp, zpow_mul, zpow_natCast]

private lemma e_mul_kiInv_pow (i j : ι) (r : ℕ) :
    e D q j * kiInv D q i ^ r =
      (q ^ D.symmetrizer i) ^ ((r : ℤ) * D.cartan i j) • (kiInv D q i ^ r * e D q j) := by
  rw [kiInv, k_pow, e_mul_k, smul_neg, map_neg, neg_neg, map_nsmul, D.pairing_root_simpleTorus,
    nsmul_eq_mul]
  have hexp : (r : ℤ) * (D.symmetrizer j * D.cartan j i) =
      D.symmetrizer i * ((r : ℤ) * D.cartan i j) := by
    linear_combination (r : ℤ) * D.symmetrizer_mul_cartan j i
  rw [hexp, zpow_mul, zpow_natCast]

private lemma eDividedPower_mul_kiInv_pow (i : ι) (s r : ℕ) :
    eDividedPower D q i s * kiInv D q i ^ r =
      (q ^ D.symmetrizer i) ^ (2 * (s : ℤ) * (r : ℤ)) •
        (kiInv D q i ^ r * eDividedPower D q i s) := by
  rw [kiInv, k_pow, eDividedPower_mul_k, smul_neg, map_neg, mul_neg, neg_mul, neg_neg,
    map_nsmul, D.pairing_root_simpleTorus_self, nsmul_eq_mul]
  have hexp : (s : ℤ) * ((r : ℤ) * (2 * D.symmetrizer i)) =
      D.symmetrizer i * (2 * (s : ℤ) * (r : ℤ)) := by ring
  rw [hexp, zpow_mul, zpow_natCast]

private lemma ki_pow_mul_f (i j : ι) (s : ℕ) :
    ki D q i ^ s * f D q j =
      (q ^ D.symmetrizer i)⁻¹ ^ ((s : ℤ) * D.cartan i j) • (f D q j * ki D q i ^ s) := by
  rw [ki, k_pow, k_mul_f, map_nsmul, D.pairing_root_simpleTorus, nsmul_eq_mul]
  have hexp : -((s : ℤ) * (D.symmetrizer j * D.cartan j i)) =
      -(D.symmetrizer i * ((s : ℤ) * D.cartan i j)) := by
    linear_combination -(s : ℤ) * D.symmetrizer_mul_cartan j i
  rw [hexp, zpow_neg, zpow_mul, zpow_natCast, ← inv_zpow]

private lemma ki_pow_mul_fDividedPower (i : ι) (s r : ℕ) :
    ki D q i ^ s * fDividedPower D q i r =
      (q ^ D.symmetrizer i)⁻¹ ^ (2 * (s : ℤ) * (r : ℤ)) •
        (fDividedPower D q i r * ki D q i ^ s) := by
  rw [ki, k_pow, k_mul_fDividedPower, map_nsmul, D.pairing_root_simpleTorus_self, nsmul_eq_mul]
  have hexp : -(r : ℤ) * ((s : ℤ) * (2 * D.symmetrizer i)) =
      -(D.symmetrizer i * (2 * (s : ℤ) * (r : ℤ))) := by ring
  rw [hexp, zpow_neg, zpow_mul, zpow_natCast, ← inv_zpow]

private lemma kj_mul_fDividedPower (i j : ι) (r : ℕ) :
    ki D q j * fDividedPower D q i r =
      (q ^ D.symmetrizer i)⁻¹ ^ ((r : ℤ) * D.cartan i j) •
        (fDividedPower D q i r * ki D q j) := by
  rw [ki, k_mul_fDividedPower, D.pairing_root_simpleTorus]
  have hexp : -(r : ℤ) * (D.symmetrizer i * D.cartan i j) =
      -(D.symmetrizer i * ((r : ℤ) * D.cartan i j)) := by ring
  rw [hexp, zpow_neg, zpow_mul, zpow_natCast, ← inv_zpow]

private noncomputable def antipodeTuple (hq : q ≠ 0) :
    GeneratorTuple D q (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ where
  e i := MulOpposite.op (-(kiInv D q i * e D q i))
  f i := MulOpposite.op (-(f D q i * ki D q i))
  k y := MulOpposite.op (k D q (-y))
  k_zero := by simp
  k_mul_k y z := by
    apply MulOpposite.unop_injective
    simp [k_mul_k, add_comm]
  k_mul_e y i := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul,
      neg_mul, mul_neg, smul_neg, neg_inj]
    rw [mul_assoc, e_mul_k, map_neg, neg_neg, mul_smul_comm, ← mul_assoc (kiInv D q i),
      kiInv, (commute_k_k (-D.simpleTorus i) (-y)).eq, mul_assoc]
  k_mul_f y i := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul,
      neg_mul, mul_neg, smul_neg, neg_inj]
    rw [← mul_assoc (k D q (-y)), k_mul_f, map_neg, neg_neg, smul_mul_assoc, smul_smul,
      ← zpow_add₀ hq, neg_add_cancel, zpow_zero, one_smul, mul_assoc, ki,
      (commute_k_k (D.simpleTorus i) (-y)).eq, ← mul_assoc]
  e_mul_f_sub_f_mul_e_self i := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_sub, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_smul, neg_mul_neg]
    have h1 : f D q i * ki D q i * (kiInv D q i * e D q i) = f D q i * e D q i := by
      rw [mul_assoc (f D q i), ← mul_assoc (ki D q i), ki, kiInv, k_mul_k_neg, one_mul]
    have h2 : kiInv D q i * e D q i * (f D q i * ki D q i) = e D q i * f D q i := by
      have hqi : q ^ D.symmetrizer i ≠ 0 := pow_ne_zero _ hq
      rw [kiInv_mul_e, smul_mul_assoc, mul_assoc (e D q i), ← mul_assoc (kiInv D q i),
        kiInv_mul_f, smul_mul_assoc, mul_smul_comm, smul_smul, ← zpow_add₀ hqi,
        neg_add_cancel, zpow_zero, one_smul, mul_assoc (f D q i), kiInv, ki, k_neg_mul_k, mul_one]
    rw [h1, h2, ← neg_sub (e D q i * f D q i), e_mul_f_sub_f_mul_e_self, ← smul_neg,
      neg_sub, ki, kiInv, neg_neg]
  e_mul_f_sub_f_mul_e_of_ne {i j} hij := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_sub, MulOpposite.unop_mul, MulOpposite.unop_op,
      MulOpposite.unop_zero, neg_mul_neg]
    have h1 : f D q j * ki D q j * (kiInv D q i * e D q i) =
        kiInv D q i * e D q i * (f D q j * ki D q j) := by
      calc
        f D q j * ki D q j * (kiInv D q i * e D q i)
          = (f D q j * k D q (-D.simpleTorus i)) * (k D q (D.simpleTorus j) * e D q i) := by
            rw [ki, kiInv, mul_assoc (f D q j), ← mul_assoc (k D q (D.simpleTorus j)),
              (commute_k_k (D.simpleTorus j) (-D.simpleTorus i)).eq]
            simp only [mul_assoc]
        _ = (q ^ (-(D.symmetrizer j * D.cartan j i)) * q ^ (D.symmetrizer i * D.cartan i j)) •
              (k D q (-D.simpleTorus i) * (f D q j * e D q i) * k D q (D.simpleTorus j)) := by
            rw [f_mul_k, k_mul_e, map_neg, D.pairing_root_simpleTorus, D.pairing_root_simpleTorus,
              smul_mul_smul_comm]
            simp only [mul_assoc]
        _ = kiInv D q i * e D q i * (f D q j * ki D q j) := by
            rw [← zpow_add₀ hq, D.symmetrizer_mul_cartan j i, neg_add_cancel, zpow_zero, one_smul,
              ← e_mul_f_of_ne hij, ki, kiInv]
            simp only [mul_assoc]
    rw [h1, sub_self]
  serre_e {i j} hij := by
    apply MulOpposite.unop_injective
    simp only [unop_sum, MulOpposite.unop_smul, MulOpposite.unop_mul,
      MulOpposite.unop_op, MulOpposite.unop_zero, unop_quantumDividedPower, ← mul_assoc]
    let m := serreLength D i j
    let qi := q ^ D.symmetrizer i
    have hqi : qi ≠ 0 := pow_ne_zero _ hq
    have hterm : ∀ r ∈ range (m + 1),
        (-1 : K) ^ r •
          (quantumDividedPower qi (-(kiInv D q i * e D q i)) (m - r) *
            (-(kiInv D q j * e D q j)) *
            quantumDividedPower qi (-(kiInv D q i * e D q i)) r) =
        -(kiInv D q j * kiInv D q i ^ m *
          ((-1 : K) ^ (m - r) •
            (eDividedPower D q i (m - r) * e D q j * eDividedPower D q i r))) := by
      intro r hr
      have hr' : r ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hr)
      rw [quantumDividedPower_neg_kiInv_mul_e, quantumDividedPower_neg_kiInv_mul_e,
        mul_neg, neg_mul, smul_neg, neg_inj, smul_mul_assoc, smul_mul_smul_comm, smul_smul,
        mul_smul_comm]
      have hmove : kiInv D q i ^ (m - r) * eDividedPower D q i (m - r) *
          (kiInv D q j * e D q j) * (kiInv D q i ^ r * eDividedPower D q i r) =
          (qi ^ (((m - r : ℕ) : ℤ) * D.cartan i j) * qi ^ ((r : ℤ) * D.cartan i j) *
              qi ^ (2 * ((m - r : ℕ) : ℤ) * (r : ℤ))) •
            (kiInv D q j * kiInv D q i ^ m *
              (eDividedPower D q i (m - r) * e D q j * eDividedPower D q i r)) := by
        calc
          kiInv D q i ^ (m - r) * eDividedPower D q i (m - r) *
              (kiInv D q j * e D q j) * (kiInv D q i ^ r * eDividedPower D q i r)
            = kiInv D q i ^ (m - r) * (eDividedPower D q i (m - r) * kiInv D q j) *
                (e D q j * kiInv D q i ^ r) * eDividedPower D q i r := by
              simp only [mul_assoc]
          _ = (qi ^ (((m - r : ℕ) : ℤ) * D.cartan i j) * qi ^ ((r : ℤ) * D.cartan i j)) •
                (kiInv D q i ^ (m - r) * kiInv D q j *
                  (eDividedPower D q i (m - r) * kiInv D q i ^ r) *
                  e D q j * eDividedPower D q i r) := by
              rw [eDividedPower_mul_kiInv, e_mul_kiInv_pow]
              simp only [mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]
              exact congrArg (· • _) (mul_comm _ _)
          _ = (qi ^ (((m - r : ℕ) : ℤ) * D.cartan i j) * qi ^ ((r : ℤ) * D.cartan i j) *
                qi ^ (2 * ((m - r : ℕ) : ℤ) * (r : ℤ))) •
                (kiInv D q j * kiInv D q i ^ m *
                  (eDividedPower D q i (m - r) * e D q j * eDividedPower D q i r)) := by
              rw [eDividedPower_mul_kiInv_pow, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
                smul_smul]
              refine congrArg₂ (· • ·) rfl ?_
              have hcomm : kiInv D q i ^ (m - r) * kiInv D q j =
                  kiInv D q j * kiInv D q i ^ (m - r) :=
                ((commute_k_k (-D.simpleTorus i) (-D.simpleTorus j)).pow_left (m - r)).eq
              calc
                kiInv D q i ^ (m - r) * kiInv D q j *
                    (kiInv D q i ^ r * eDividedPower D q i (m - r)) *
                    e D q j * eDividedPower D q i r
                  = kiInv D q j * (kiInv D q i ^ (m - r) * kiInv D q i ^ r) *
                      (eDividedPower D q i (m - r) * e D q j * eDividedPower D q i r) := by
                    rw [hcomm]
                    simp only [mul_assoc]
                _ = kiInv D q j * kiInv D q i ^ m *
                      (eDividedPower D q i (m - r) * e D q j * eDividedPower D q i r) := by
                    rw [← pow_add, Nat.sub_add_cancel hr']
      rw [hmove, smul_smul]
      refine congrArg (· • _) ?_
      have hsign : (-1 : K) ^ r * (-1 : K) ^ r = 1 := by
        rw [← mul_pow]
        norm_num
      have hpow : qi ^ ((m - r) * (m - r - 1)) * qi ^ (r * (r - 1)) *
          (qi ^ (((m - r : ℕ) : ℤ) * D.cartan i j) * qi ^ ((r : ℤ) * D.cartan i j) *
            qi ^ (2 * ((m - r : ℕ) : ℤ) * (r : ℤ))) = 1 := by
        rw [← zpow_natCast qi ((m - r) * _), ← zpow_natCast qi (r * _),
          ← zpow_add₀ hqi, ← zpow_add₀ hqi, ← zpow_add₀ hqi, ← zpow_add₀ hqi]
        convert zpow_zero qi using 2
        linear_combination antipode_serre_exp hr' (cartan_eq_one_sub_serreLength D hij)
      calc
        (-1 : K) ^ r * (((-1 : K) ^ (m - r) * qi ^ ((m - r) * (m - r - 1))) *
            ((-1 : K) ^ r * qi ^ (r * (r - 1)))) *
            (qi ^ (((m - r : ℕ) : ℤ) * D.cartan i j) * qi ^ ((r : ℤ) * D.cartan i j) *
              qi ^ (2 * ((m - r : ℕ) : ℤ) * (r : ℤ)))
          = (-1 : K) ^ (m - r) * ((-1 : K) ^ r * (-1 : K) ^ r) *
              (qi ^ ((m - r) * (m - r - 1)) * qi ^ (r * (r - 1)) *
                (qi ^ (((m - r : ℕ) : ℤ) * D.cartan i j) * qi ^ ((r : ℤ) * D.cartan i j) *
                  qi ^ (2 * ((m - r : ℕ) : ℤ) * (r : ℤ)))) := by ring
        _ = (-1 : K) ^ (m - r) := by rw [hsign, hpow, mul_one, mul_one]
    change ∑ r ∈ range (m + 1), _ = 0
    rw [sum_congr rfl hterm, sum_neg_distrib, ← mul_sum]
    have hrefl : (∑ x ∈ range (m + 1),
        (-1 : K) ^ (m - x) •
          (eDividedPower D q i (m - x) * e D q j * eDividedPower D q i x)) =
        ∑ r ∈ range (m + 1),
          (-1 : K) ^ r • (eDividedPower D q i r * e D q j * eDividedPower D q i (m - r)) := by
      rw [← sum_range_reflect]
      refine sum_congr rfl fun r hr ↦ ?_
      have hr' : r ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hr)
      rw [Nat.add_one_sub_one, Nat.sub_sub_self hr']
    rw [hrefl, serre_e hij, mul_zero, neg_zero]
  serre_f {i j} hij := by
    apply MulOpposite.unop_injective
    simp only [unop_sum, MulOpposite.unop_smul, MulOpposite.unop_mul,
      MulOpposite.unop_op, MulOpposite.unop_zero, unop_quantumDividedPower, ← mul_assoc]
    let m := serreLength D i j
    let qi := q ^ D.symmetrizer i
    have hqi : qi⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hq)
    have hterm : ∀ r ∈ range (m + 1),
        (-1 : K) ^ r •
          (quantumDividedPower qi (-(f D q i * ki D q i)) (m - r) *
            (-(f D q j * ki D q j)) *
            quantumDividedPower qi (-(f D q i * ki D q i)) r) =
        -(((-1 : K) ^ (m - r) •
            (fDividedPower D q i (m - r) * f D q j * fDividedPower D q i r)) *
          (ki D q j * ki D q i ^ m)) := by
      intro r hr
      have hr' : r ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hr)
      rw [quantumDividedPower_neg_f_mul_ki, quantumDividedPower_neg_f_mul_ki,
        mul_neg, neg_mul, smul_neg, neg_inj, smul_mul_assoc, smul_mul_smul_comm, smul_smul,
        smul_mul_assoc]
      have hmove : fDividedPower D q i (m - r) * ki D q i ^ (m - r) *
          (f D q j * ki D q j) * (fDividedPower D q i r * ki D q i ^ r) =
          (qi⁻¹ ^ (((m - r : ℕ) : ℤ) * D.cartan i j) * qi⁻¹ ^ ((r : ℤ) * D.cartan i j) *
              qi⁻¹ ^ (2 * ((m - r : ℕ) : ℤ) * (r : ℤ))) •
            ((fDividedPower D q i (m - r) * f D q j * fDividedPower D q i r) *
              (ki D q j * ki D q i ^ m)) := by
        calc
          fDividedPower D q i (m - r) * ki D q i ^ (m - r) *
              (f D q j * ki D q j) * (fDividedPower D q i r * ki D q i ^ r)
            = fDividedPower D q i (m - r) * (ki D q i ^ (m - r) * f D q j) *
                (ki D q j * fDividedPower D q i r) * ki D q i ^ r := by
              simp only [mul_assoc]
          _ = (qi⁻¹ ^ (((m - r : ℕ) : ℤ) * D.cartan i j) * qi⁻¹ ^ ((r : ℤ) * D.cartan i j)) •
                (fDividedPower D q i (m - r) * f D q j *
                  (ki D q i ^ (m - r) * fDividedPower D q i r) *
                  (ki D q j * ki D q i ^ r)) := by
              rw [ki_pow_mul_f, kj_mul_fDividedPower]
              simp only [mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]
              exact congrArg (· • _) (mul_comm _ _)
          _ = (qi⁻¹ ^ (((m - r : ℕ) : ℤ) * D.cartan i j) * qi⁻¹ ^ ((r : ℤ) * D.cartan i j) *
                qi⁻¹ ^ (2 * ((m - r : ℕ) : ℤ) * (r : ℤ))) •
                ((fDividedPower D q i (m - r) * f D q j * fDividedPower D q i r) *
                  (ki D q j * ki D q i ^ m)) := by
              rw [ki_pow_mul_fDividedPower, mul_smul_comm, smul_mul_assoc, smul_smul]
              refine congrArg₂ (· • ·) rfl ?_
              have hcomm : ki D q i ^ (m - r) * ki D q j = ki D q j * ki D q i ^ (m - r) :=
                ((commute_k_k (D.simpleTorus i) (D.simpleTorus j)).pow_left (m - r)).eq
              calc
                fDividedPower D q i (m - r) * f D q j *
                    (fDividedPower D q i r * ki D q i ^ (m - r)) *
                    (ki D q j * ki D q i ^ r)
                  = (fDividedPower D q i (m - r) * f D q j * fDividedPower D q i r) *
                      (ki D q i ^ (m - r) * ki D q j * ki D q i ^ r) := by
                    simp only [mul_assoc]
                _ = (fDividedPower D q i (m - r) * f D q j * fDividedPower D q i r) *
                      (ki D q j * ki D q i ^ m) := by
                    rw [hcomm, mul_assoc (ki D q j), ← pow_add, Nat.sub_add_cancel hr']
      rw [hmove, smul_smul]
      refine congrArg (· • _) ?_
      have hsign : (-1 : K) ^ r * (-1 : K) ^ r = 1 := by
        rw [← mul_pow]
        norm_num
      have hpow : qi⁻¹ ^ ((m - r) * (m - r - 1)) * qi⁻¹ ^ (r * (r - 1)) *
          (qi⁻¹ ^ (((m - r : ℕ) : ℤ) * D.cartan i j) * qi⁻¹ ^ ((r : ℤ) * D.cartan i j) *
            qi⁻¹ ^ (2 * ((m - r : ℕ) : ℤ) * (r : ℤ))) = 1 := by
        rw [← zpow_natCast qi⁻¹ ((m - r) * _), ← zpow_natCast qi⁻¹ (r * _),
          ← zpow_add₀ hqi, ← zpow_add₀ hqi, ← zpow_add₀ hqi, ← zpow_add₀ hqi]
        convert zpow_zero qi⁻¹ using 2
        linear_combination antipode_serre_exp hr' (cartan_eq_one_sub_serreLength D hij)
      calc
        (-1 : K) ^ r * (((-1 : K) ^ (m - r) * qi⁻¹ ^ ((m - r) * (m - r - 1))) *
            ((-1 : K) ^ r * qi⁻¹ ^ (r * (r - 1)))) *
            (qi⁻¹ ^ (((m - r : ℕ) : ℤ) * D.cartan i j) * qi⁻¹ ^ ((r : ℤ) * D.cartan i j) *
              qi⁻¹ ^ (2 * ((m - r : ℕ) : ℤ) * (r : ℤ)))
          = (-1 : K) ^ (m - r) * ((-1 : K) ^ r * (-1 : K) ^ r) *
              (qi⁻¹ ^ ((m - r) * (m - r - 1)) * qi⁻¹ ^ (r * (r - 1)) *
                (qi⁻¹ ^ (((m - r : ℕ) : ℤ) * D.cartan i j) * qi⁻¹ ^ ((r : ℤ) * D.cartan i j) *
                  qi⁻¹ ^ (2 * ((m - r : ℕ) : ℤ) * (r : ℤ)))) := by ring
        _ = (-1 : K) ^ (m - r) := by rw [hsign, hpow, mul_one, mul_one]
    change ∑ r ∈ range (m + 1), _ = 0
    rw [sum_congr rfl hterm, sum_neg_distrib, ← sum_mul]
    have hrefl : (∑ x ∈ range (m + 1),
        (-1 : K) ^ (m - x) •
          (fDividedPower D q i (m - x) * f D q j * fDividedPower D q i x)) =
        ∑ r ∈ range (m + 1),
          (-1 : K) ^ r • (fDividedPower D q i r * f D q j * fDividedPower D q i (m - r)) := by
      rw [← sum_range_reflect]
      refine sum_congr rfl fun r hr ↦ ?_
      have hr' : r ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hr)
      rw [Nat.add_one_sub_one, Nat.sub_sub_self hr']
    rw [hrefl, serre_f hij, zero_mul, neg_zero]

/-- The antipode of `QuantizedEnvelopingAlgebra D q` as a `K`-algebra homomorphism into the opposite
algebra, defined for every nonzero parameter `q`. -/
noncomputable def antipodeAlgHom (hq : q ≠ 0) :
    QuantizedEnvelopingAlgebra D q →ₐ[K] (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ :=
  lift (antipodeTuple D hq)

variable {D}

@[simp]
theorem antipodeAlgHom_e (hq : q ≠ 0) (i : ι) :
    antipodeAlgHom D hq (e D q i) = MulOpposite.op (-(kiInv D q i * e D q i)) :=
  lift_e _ i

@[simp]
theorem antipodeAlgHom_f (hq : q ≠ 0) (i : ι) :
    antipodeAlgHom D hq (f D q i) = MulOpposite.op (-(f D q i * ki D q i)) :=
  lift_f _ i

@[simp]
theorem antipodeAlgHom_k (hq : q ≠ 0) (y : Y) :
    antipodeAlgHom D hq (k D q y) = MulOpposite.op (k D q (-y)) :=
  lift_k _ y

theorem antipodeAlgHom_ki (hq : q ≠ 0) (i : ι) :
    antipodeAlgHom D hq (ki D q i) = MulOpposite.op (kiInv D q i) :=
  antipodeAlgHom_k hq (D.simpleTorus i)

theorem antipodeAlgHom_kiInv (hq : q ≠ 0) (i : ι) :
    antipodeAlgHom D hq (kiInv D q i) = MulOpposite.op (ki D q i) := by
  rw [kiInv, antipodeAlgHom_k, neg_neg, ki]

theorem unop_antipodeAlgHom_eDividedPower (hq : q ≠ 0) (i : ι) (n : ℕ) :
    MulOpposite.unop (antipodeAlgHom D hq (eDividedPower D q i n)) =
      ((-1 : K) ^ n * (q ^ D.symmetrizer i) ^ (n * (n - 1))) •
        (kiInv D q i ^ n * eDividedPower D q i n) := by
  rw [eDividedPower, map_quantumDividedPower, antipodeAlgHom_e, unop_quantumDividedPower,
    ← eDividedPower, quantumDividedPower_neg_kiInv_mul_e]

theorem unop_antipodeAlgHom_fDividedPower (hq : q ≠ 0) (i : ι) (n : ℕ) :
    MulOpposite.unop (antipodeAlgHom D hq (fDividedPower D q i n)) =
      ((-1 : K) ^ n * (q ^ D.symmetrizer i)⁻¹ ^ (n * (n - 1))) •
        (fDividedPower D q i n * ki D q i ^ n) := by
  rw [fDividedPower, map_quantumDividedPower, antipodeAlgHom_f, unop_quantumDividedPower,
    ← fDividedPower, quantumDividedPower_neg_f_mul_ki]

/-- Applying the opposite-valued antipode twice equals the diagonal rescaling automorphism
`Eᵢ ↦ qᵢ⁻² • Eᵢ`, `Fᵢ ↦ qᵢ² • Fᵢ`, `K_y ↦ K_y` for every `q ≠ 0`. -/
theorem opComm_antipodeAlgHom_comp_antipodeAlgHom (hq : q ≠ 0) :
    (AlgHom.opComm (antipodeAlgHom D hq)).comp (antipodeAlgHom D hq) =
      (rescale D q
        (fun i ↦ (Units.mk0 (q ^ D.symmetrizer i) (pow_ne_zero _ hq))⁻¹ ^ 2)).toAlgHom := by
  ext i
  · change MulOpposite.unop (antipodeAlgHom D hq
        (MulOpposite.unop (antipodeAlgHom D hq (e D q i)))) = rescale D q _ (e D q i)
    simp only [antipodeAlgHom_e, MulOpposite.unop_op, map_neg, map_mul, antipodeAlgHom_kiInv,
      MulOpposite.unop_neg, MulOpposite.unop_mul, neg_mul, neg_neg, rescale_e,
      Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [kiInv_mul_e, D.cartan_apply_self, zpow_neg, zpow_two, ← sq, inv_pow,
      smul_mul_assoc, mul_assoc, kiInv, ki, k_neg_mul_k, mul_one]
  · change MulOpposite.unop (antipodeAlgHom D hq
        (MulOpposite.unop (antipodeAlgHom D hq (f D q i)))) = rescale D q _ (f D q i)
    simp only [antipodeAlgHom_f, MulOpposite.unop_op, map_neg, map_mul, antipodeAlgHom_ki,
      MulOpposite.unop_neg, MulOpposite.unop_mul, mul_neg, neg_neg, rescale_f,
      Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, inv_inv]
    rw [← mul_assoc, kiInv_mul_f, D.cartan_apply_self, zpow_two, ← sq,
      smul_mul_assoc, mul_assoc, kiInv, ki, k_neg_mul_k, mul_one]
  · simp

end AntipodeOp

/-! ### Hopf algebra structure -/

section Hopf

variable (D : CartanDatum ι X Y) {q : K}

/-- Explicit-hypothesis `HopfAlgebra` structure on `QuantizedEnvelopingAlgebra D q` under `q ≠ 0`
and nonvanishing of the Serre-degree quantum factorials `[1 - aᵢⱼ]_(qᵢ)!` (`i ≠ j`). -/
@[expose, instance_reducible]
noncomputable def hopfAlgebraOfSerre (hq : q ≠ 0)
    (hserre : ∀ {i j : ι}, i ≠ j →
      quantumFactorial (q ^ D.symmetrizer i) (serreLength D i j) ≠ 0) :
    HopfAlgebra K (QuantizedEnvelopingAlgebra D q) :=
  @HopfAlgebra.ofAntipodeOfAdjoin K (QuantizedEnvelopingAlgebra D q) _ _
    (bialgebraOfSerre D hq hserre) _ (antipodeAlgHom D hq) (adjoin_range_generator D q)
    (by
      rintro _ ⟨g, rfl⟩
      cases g <;> simp [Coalgebra.comul, Coalgebra.counit, mul_assoc, ki, kiInv])
    (by
      rintro _ ⟨g, rfl⟩
      cases g <;>
        simp [Coalgebra.comul, Coalgebra.counit, ← mul_assoc (ki D q _), ki, kiInv])

section Generic

variable (q : K) [Fact (IsGenericQuantumParameter q)]

/-- The canonical `K`-Hopf algebra structure on `QuantizedEnvelopingAlgebra D q` at a generic
quantum parameter `q`. -/
noncomputable instance instHopfAlgebra : HopfAlgebra K (QuantizedEnvelopingAlgebra D q) :=
  hopfAlgebraOfSerre D (Fact.out : IsGenericQuantumParameter q).ne_zero fun {i j} _ ↦
    quantumFactorial_ne_zero
      ((Fact.out : IsGenericQuantumParameter q).pow (D.symmetrizer_pos i)) (serreLength D i j)

variable {D q}

@[simp]
theorem antipode_e (i : ι) :
    HopfAlgebra.antipode K (e D q i) = -(kiInv D q i * e D q i) :=
  congrArg MulOpposite.unop
    (antipodeAlgHom_e (Fact.out : IsGenericQuantumParameter q).ne_zero i)

@[simp]
theorem antipode_f (i : ι) :
    HopfAlgebra.antipode K (f D q i) = -(f D q i * ki D q i) :=
  congrArg MulOpposite.unop
    (antipodeAlgHom_f (Fact.out : IsGenericQuantumParameter q).ne_zero i)

@[simp]
theorem antipode_k (y : Y) :
    HopfAlgebra.antipode K (k D q y) = k D q (-y) :=
  congrArg MulOpposite.unop
    (antipodeAlgHom_k (Fact.out : IsGenericQuantumParameter q).ne_zero y)

theorem antipode_ki (i : ι) :
    HopfAlgebra.antipode K (ki D q i) = kiInv D q i :=
  antipode_k (D.simpleTorus i)

theorem antipode_kiInv (i : ι) :
    HopfAlgebra.antipode K (kiInv D q i) = ki D q i := by
  rw [kiInv, antipode_k, neg_neg, ki]

@[simp]
theorem antipodeAlgHom_apply (x : QuantizedEnvelopingAlgebra D q) :
    antipodeAlgHom D (Fact.out : IsGenericQuantumParameter q).ne_zero x =
      MulOpposite.op (HopfAlgebra.antipode K x) :=
  (rfl)

theorem antipode_e_eq_neg_normalizedE (i : ι) :
    HopfAlgebra.antipode K (e D q i) = -normalizedE D q i := by
  rw [antipode_e, normalizedE_def]

theorem antipode_f_eq_neg_normalizedF (i : ι) :
    HopfAlgebra.antipode K (f D q i) = -normalizedF D q i := by
  rw [antipode_f, normalizedF_def]

/-- Antipode of the raising divided powers:
`S(Eᵢ^(n)) = (-1)^n qᵢ^(n(n - 1)) Kᵢ^(-n) Eᵢ^(n)`. -/
theorem antipode_eDividedPower (i : ι) (n : ℕ) :
    HopfAlgebra.antipode K (eDividedPower D q i n) =
      ((-1 : K) ^ n * (q ^ D.symmetrizer i) ^ (n * (n - 1))) •
        (kiInv D q i ^ n * eDividedPower D q i n) :=
  unop_antipodeAlgHom_eDividedPower (Fact.out : IsGenericQuantumParameter q).ne_zero i n

/-- Antipode of the lowering divided powers:
`S(Fᵢ^(n)) = (-1)^n qᵢ^(-n(n - 1)) Fᵢ^(n) Kᵢ^n`. -/
theorem antipode_fDividedPower (i : ι) (n : ℕ) :
    HopfAlgebra.antipode K (fDividedPower D q i n) =
      ((-1 : K) ^ n * (q ^ D.symmetrizer i)⁻¹ ^ (n * (n - 1))) •
        (fDividedPower D q i n * ki D q i ^ n) :=
  unop_antipodeAlgHom_fDividedPower (Fact.out : IsGenericQuantumParameter q).ne_zero i n

/-! ### Square, bijectivity, and inverse of the antipode -/

/-- On every Cartan datum, `S²` equals the diagonal rescaling automorphism
`Eᵢ ↦ qᵢ⁻² • Eᵢ`, `Fᵢ ↦ qᵢ² • Fᵢ`, `K_y ↦ K_y`. -/
theorem antipode_antipode_eq_rescale (x : QuantizedEnvelopingAlgebra D q) :
    HopfAlgebra.antipode K (HopfAlgebra.antipode K x) =
      rescale D q
        (fun i ↦
          (Units.mk0 (q ^ D.symmetrizer i)
            (pow_ne_zero _ (Fact.out : IsGenericQuantumParameter q).ne_zero))⁻¹ ^ 2) x := by
  simpa using AlgHom.congr_fun
    (opComm_antipodeAlgHom_comp_antipodeAlgHom
      (D := D) (Fact.out : IsGenericQuantumParameter q).ne_zero) x

/-- When a coweight `twoRhoCheck : Y` satisfies `⟨αᵢ, twoRhoCheck⟩ = 2 dᵢ` for every `i` (such as
the sum of positive coroots in finite type), `S²` is conjugation by `K_(-twoRhoCheck)`:
`S(S x) = K_(-twoRhoCheck) * x * K_(twoRhoCheck)`. -/
theorem antipode_antipode_of_pairing_root {twoRhoCheck : Y}
    (hρ : ∀ i : ι, D.pairing (D.root i) twoRhoCheck = 2 * D.symmetrizer i)
    (x : QuantizedEnvelopingAlgebra D q) :
    HopfAlgebra.antipode K (HopfAlgebra.antipode K x) =
      k D q (-twoRhoCheck) * x * k D q twoRhoCheck := by
  have hq : q ≠ 0 := (Fact.out : IsGenericQuantumParameter q).ne_zero
  have hc : (fun i ↦ (Units.mk0 (q ^ D.symmetrizer i) (pow_ne_zero _ hq))⁻¹ ^ 2) =
      fun i ↦ Units.mk0 q hq ^ D.pairing (D.root i) (-twoRhoCheck) := by
    ext i
    simp only [map_neg, hρ i, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
      Units.val_zpow_eq_zpow_val, Units.val_mk0]
    rw [zpow_neg, mul_comm (2 : ℤ), zpow_mul, zpow_natCast, zpow_two, ← sq, inv_pow]
  rw [antipode_antipode_eq_rescale, hc, ← toAlgEquiv_conjAct_kUnit hq (-twoRhoCheck)]
  simp [ConjAct.units_smul_def, mul_assoc]

theorem antipode_antipode_e (i : ι) :
    HopfAlgebra.antipode K (HopfAlgebra.antipode K (e D q i)) =
      (q ^ D.symmetrizer i)⁻¹ ^ 2 • e D q i := by
  rw [antipode_antipode_eq_rescale]
  simp

theorem antipode_antipode_f (i : ι) :
    HopfAlgebra.antipode K (HopfAlgebra.antipode K (f D q i)) =
      (q ^ D.symmetrizer i) ^ 2 • f D q i := by
  rw [antipode_antipode_eq_rescale]
  simp [inv_pow]

theorem antipode_antipode_k (y : Y) :
    HopfAlgebra.antipode K (HopfAlgebra.antipode K (k D q y)) = k D q y := by
  simp

variable (D q) in
/-- The antipode of `QuantizedEnvelopingAlgebra D q` is bijective on every Cartan datum. -/
theorem antipode_bijective :
    Function.Bijective
      (HopfAlgebra.antipode K :
        QuantizedEnvelopingAlgebra D q →ₗ[K] QuantizedEnvelopingAlgebra D q) := by
  have h : Function.Bijective
      ((HopfAlgebra.antipode K : QuantizedEnvelopingAlgebra D q → QuantizedEnvelopingAlgebra D q) ∘
        HopfAlgebra.antipode K) := by
    simpa only [Function.comp_def, antipode_antipode_eq_rescale] using
      (rescale D q
        (fun i ↦
          (Units.mk0 (q ^ D.symmetrizer i)
            (pow_ne_zero _ (Fact.out : IsGenericQuantumParameter q).ne_zero))⁻¹ ^ 2)).bijective
  exact ⟨.of_comp h.1, .of_comp h.2⟩

variable (D q) in
/-- The antipode of `QuantizedEnvelopingAlgebra D q` as a `K`-algebra isomorphism onto the opposite
algebra. -/
noncomputable def antipodeEquiv :
    QuantizedEnvelopingAlgebra D q ≃ₐ[K] (QuantizedEnvelopingAlgebra D q)ᵐᵒᵖ :=
  AlgEquiv.ofBijective
    (antipodeAlgHom D (Fact.out : IsGenericQuantumParameter q).ne_zero)
    (MulOpposite.opEquiv.bijective.comp (antipode_bijective D q))

@[simp]
theorem antipodeEquiv_toAlgHom :
    (antipodeEquiv D q).toAlgHom =
      antipodeAlgHom D (Fact.out : IsGenericQuantumParameter q).ne_zero :=
  (rfl)

@[simp]
theorem antipodeEquiv_apply (x : QuantizedEnvelopingAlgebra D q) :
    antipodeEquiv D q x = MulOpposite.op (HopfAlgebra.antipode K x) :=
  (rfl)

@[simp]
theorem inverseAntipode_e (i : ι) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (e D q i) =
      -(e D q i * kiInv D q i) := by
  apply (antipode_bijective D q).injective
  rw [TauCeti.HopfAlgebra.antipode_inverseAntipode, map_neg,
    HopfAlgebra.antipode_mul_antidistrib, antipode_kiInv, antipode_e,
    mul_neg, neg_neg, ← mul_assoc, ki, kiInv, k_mul_k_neg, one_mul]

@[simp]
theorem inverseAntipode_f (i : ι) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (f D q i) =
      -(ki D q i * f D q i) := by
  apply (antipode_bijective D q).injective
  rw [TauCeti.HopfAlgebra.antipode_inverseAntipode, map_neg,
    HopfAlgebra.antipode_mul_antidistrib, antipode_f, antipode_ki,
    neg_mul, neg_neg, mul_assoc, ki, kiInv, k_mul_k_neg, mul_one]

@[simp]
theorem inverseAntipode_k (y : Y) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (k D q y) = k D q (-y) := by
  apply (antipode_bijective D q).injective
  rw [TauCeti.HopfAlgebra.antipode_inverseAntipode, antipode_k, neg_neg]

theorem inverseAntipode_ki (i : ι) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (ki D q i) = kiInv D q i :=
  inverseAntipode_k (D.simpleTorus i)

theorem inverseAntipode_kiInv (i : ι) :
    TauCeti.HopfAlgebra.inverseAntipode (antipode_bijective D q) (kiInv D q i) = ki D q i := by
  rw [kiInv, inverseAntipode_k, neg_neg, ki]

/-- The Chevalley involution intertwines the antipode with its inverse (`ω ∘ S = S⁻¹ ∘ ω`),
equivalently `S(ω(S x)) = ω x`. -/
theorem antipode_chevalleyInvolution_antipode (x : QuantizedEnvelopingAlgebra D q) :
    HopfAlgebra.antipode K (chevalleyInvolution D q (HopfAlgebra.antipode K x)) =
      chevalleyInvolution D q x := by
  have h :
      ((AlgHom.opComm (antipodeAlgHom D (Fact.out : IsGenericQuantumParameter q).ne_zero)).comp
          ((AlgEquiv.op (chevalleyInvolution D q)).toAlgHom.comp
            (antipodeAlgHom D (Fact.out : IsGenericQuantumParameter q).ne_zero))) =
        (chevalleyInvolution D q).toAlgHom := by
    ext i
    · simp [HopfAlgebra.antipode_mul_antidistrib, mul_assoc]
    · simp [HopfAlgebra.antipode_mul_antidistrib, ← mul_assoc]
    · simp
  simpa using AlgHom.congr_fun h x

/-- Functoriality of the antipode along a morphism `φ : CartanDatum.Hom D D'` of Cartan data. -/
@[simp]
theorem map_antipode {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
    {D' : CartanDatum ι X' Y'} (φ : CartanDatum.Hom D D')
    (x : QuantizedEnvelopingAlgebra D q) :
    map φ (HopfAlgebra.antipode K x) = HopfAlgebra.antipode K (map φ x) := by
  simpa only [mapBialgHom_apply] using BialgHomClass.map_antipode (R := K) (mapBialgHom φ) x

end Generic

end Hopf

end TauCeti.QuantizedEnvelopingAlgebra
