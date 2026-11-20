/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantizedEnvelopingAlgebra.Antipode
public import TauCeti.Algebra.HopfAlgebra.Antipode
public import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.Tactic.Module

/-!
# The Hopf algebra structure on the Drinfeld–Jimbo quantized enveloping algebra

This file constructs the counit, coproduct, bialgebra structure, and Hopf algebra structure on
`TauCeti.QuantizedEnvelopingAlgebra D q` for a Cartan datum `D` and parameter `q` in a field `K`,
with divided-power coproduct formulas and functoriality along morphisms of Cartan data.

With `qᵢ = q ^ D.symmetrizer i`, `Kᵢ = simpleK D q i`, and `Kᵢ⁻¹ = simpleKInv D q i`:
* `ε(Eᵢ) = 0`, `ε(Fᵢ) = 0`, `ε(K_y) = 1` (unconditional in `q`, proving `Nontrivial`);
* `Δ(Eᵢ) = Eᵢ ⊗ 1 + Kᵢ ⊗ Eᵢ`, `Δ(Fᵢ) = Fᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ Fᵢ`, `Δ(K_y) = K_y ⊗ K_y`, whenever all
  Serre quantum factorials `quantumFactorial qᵢ (D.serreLength i j)` (`i ≠ j`) are nonzero (in
  particular at every generic quantum parameter, `quantumFactorial_serreLength_ne_zero`).

## Main definitions and results

* `TauCeti.QuantizedEnvelopingAlgebra.counitAlgHom`, `comulAlgHom`: counit and coproduct, with
  `comulAlgHom_quantumDividedPower_e` and `comulAlgHom_quantumDividedPower_f`.
* `TauCeti.QuantizedEnvelopingAlgebra.bialgebra`, `hopfAlgebra`: Mathlib `Bialgebra` and
  `HopfAlgebra` structures, `comulAlgHom_antipodeLinearEquiv`, and `exists_antipode`.
* `TauCeti.QuantizedEnvelopingAlgebra.mapBialgHom`: functoriality under `CartanDatum.Hom`.

## References

* G. Lusztig, *Finite dimensional Hopf algebras arising from quantized universal enveloping
  algebras*, J. Amer. Math. Soc. 3 (1990), 257--296, Proposition 4.8.
* G. Lusztig, *Introduction to Quantum Groups*, Progress in Math. 110, Birkhäuser, 1993, Ch. 3.
* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, AMS, 1996, Ch. 4.
* S. Lentner, *Quantum groups and Nichols algebras acting on conformal field theories*, Adv. Math.
  268 (2015), 247--316, Section 3.
-/

public section

open Finset
open scoped TensorProduct

namespace TauCeti

namespace QuantizedEnvelopingAlgebra

section CounitAndCoproduct

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
  (D : CartanDatum ι X Y) (q : K)

private noncomputable def counitTuple : GeneratorTuple D q K where
  e _ := 0
  f _ := 0
  k _ := 1
  k_zero := rfl
  k_mul_k _ _ := mul_one 1
  conjugate_e _ _ := by simp
  conjugate_f _ _ := by simp
  commutator_self _ := by simp
  commutator_ne _ := by simp
  serre_e _ := by simp [serreSum_def]
  serre_f _ := by simp [serreSum_def]

/-- The unconditional counit `ε : U_q(D) →ₐ[K] K`, sending `Eᵢ` and `Fᵢ` to `0` and `K_y` to `1`. -/
noncomputable def counitAlgHom : QuantizedEnvelopingAlgebra D q →ₐ[K] K :=
  lift (counitTuple D q)

@[simp] theorem counitAlgHom_e (i : ι) : counitAlgHom D q (e D q i) = 0 := lift_e _ i
@[simp] theorem counitAlgHom_f (i : ι) : counitAlgHom D q (f D q i) = 0 := lift_f _ i
@[simp] theorem counitAlgHom_k (y : Y) : counitAlgHom D q (k D q y) = 1 := lift_k _ y
@[simp] theorem counitAlgHom_simpleK (i : ι) : counitAlgHom D q (simpleK D q i) = 1 := by
  simp [simpleK_def]
@[simp] theorem counitAlgHom_simpleKInv (i : ι) : counitAlgHom D q (simpleKInv D q i) = 1 := by
  simp [simpleKInv_def]
@[simp] theorem counitAlgHom_normalizedE (i : ι) : counitAlgHom D q (normalizedE D q i) = 0 := by
  simp [normalizedE_def]
@[simp] theorem counitAlgHom_normalizedF (i : ι) : counitAlgHom D q (normalizedF D q i) = 0 := by
  simp [normalizedF_def]

/-- The unconditional counit `counitAlgHom D q : U_q(D) →ₐ[K] K` witnesses nontriviality of
`QuantizedEnvelopingAlgebra D q` for every parameter `q : K`, including degenerate ones. -/
noncomputable instance : Nontrivial (QuantizedEnvelopingAlgebra D q) :=
  (counitAlgHom D q).toRingHom.domain_nontrivial

/-! ### Coproduct and divided-power coproduct formulas -/

/-- At a generic quantum parameter `q`, all Serre quantum factorials are nonzero. -/
theorem quantumFactorial_serreLength_ne_zero {q : K} (hq : IsGenericQuantumParameter q)
    (i j : ι) : quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0 :=
  quantumFactorial_ne_zero (hq.pow (D.symmetrizer_pos i)) _

private noncomputable def comulElemE (i : ι) :
    QuantizedEnvelopingAlgebra D q ⊗[K] QuantizedEnvelopingAlgebra D q :=
  e D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] e D q i

private noncomputable def comulElemF (i : ι) :
    QuantizedEnvelopingAlgebra D q ⊗[K] QuantizedEnvelopingAlgebra D q :=
  f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i

private theorem comulElemE_summand_comm (i : ι) :
    (simpleK D q i ⊗ₜ[K] e D q i) * (e D q i ⊗ₜ[K] 1) =
      (q ^ D.symmetrizer i) ^ 2 • ((e D q i ⊗ₜ[K] 1) * (simpleK D q i ⊗ₜ[K] e D q i)) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
    simpleK_mul_e, D.cartan_apply_self, zpow_two, ← pow_two, TensorProduct.smul_tmul']

private theorem comulElemF_summand_comm (i : ι) :
    (f D q i ⊗ₜ[K] simpleKInv D q i) * (1 ⊗ₜ[K] f D q i) =
      (q ^ D.symmetrizer i) ^ 2 • ((1 ⊗ₜ[K] f D q i) * (f D q i ⊗ₜ[K] simpleKInv D q i)) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
    simpleKInv_mul_f, D.cartan_apply_self, zpow_two, ← pow_two, TensorProduct.tmul_smul]

private theorem quantumDividedPower_comulElemE {i : ι} {n : ℕ}
    (hn : quantumFactorial (q ^ D.symmetrizer i) n ≠ 0) :
    quantumDividedPower (q ^ D.symmetrizer i) (comulElemE D q i) n =
      ∑ a ∈ range (n + 1), (q ^ D.symmetrizer i) ^ (a * (n - a)) •
        ((quantumDividedPower (q ^ D.symmetrizer i) (e D q i) a * simpleK D q i ^ (n - a)) ⊗ₜ[K]
          quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (n - a)) := by
  rw [comulElemE, quantumDividedPower_add (comulElemE_summand_comm D q i) hn]
  refine sum_congr rfl fun a _ => ?_
  rw [quantumDividedPower_tmul_left, one_pow, quantumDividedPower_tmul_right,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

private theorem quantumDividedPower_comulElemF {i : ι} {n : ℕ}
    (hn : quantumFactorial (q ^ D.symmetrizer i) n ≠ 0) :
    quantumDividedPower (q ^ D.symmetrizer i) (comulElemF D q i) n =
      ∑ a ∈ range (n + 1), (q ^ D.symmetrizer i) ^ (a * (n - a)) •
        (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) a ⊗ₜ[K]
          (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) (n - a) *
            simpleKInv D q i ^ a)) := by
  rw [comulElemF, add_comm, quantumDividedPower_add (comulElemF_summand_comm D q i) hn,
    ← sum_range_reflect]
  refine sum_congr rfl fun a ha => ?_
  have han : a ≤ n := Nat.lt_succ_iff.mp (mem_range.mp ha)
  simp only [Nat.add_succ_sub_one, add_zero, Nat.sub_sub_self han]
  rw [Nat.mul_comm (n - a) a, quantumDividedPower_tmul_right, one_pow,
    quantumDividedPower_tmul_left, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

private theorem comul_commutator_self (i : ι) :
    comulElemE D q i * comulElemF D q i - comulElemF D q i * comulElemE D q i =
      (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
        (k D q (D.simpleTorus i) ⊗ₜ[K] k D q (D.simpleTorus i) -
          k D q (-D.simpleTorus i) ⊗ₜ[K] k D q (-D.simpleTorus i)) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp [comulElemE, comulElemF, zero_pow (D.symmetrizer_pos i).ne']
  simp only [comulElemE, comulElemF, mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, mul_one, ← simpleK_def, ← simpleKInv_def]
  have hcross : (simpleK D q i * f D q i) ⊗ₜ[K] (e D q i * simpleKInv D q i) =
      (f D q i * simpleK D q i) ⊗ₜ[K] (simpleKInv D q i * e D q i) := by
    rw [simpleK_mul_f, e_mul_simpleKInv]
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul,
      ← zpow_add₀ (pow_ne_zero _ hq), add_neg_cancel, zpow_zero, one_smul]
  rw [hcross]
  calc _ = (e D q i * f D q i - f D q i * e D q i) ⊗ₜ[K] simpleKInv D q i +
          simpleK D q i ⊗ₜ[K] (e D q i * f D q i - f D q i * e D q i) := by
        simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]; abel
    _ = _ := by
        rw [e_mul_f_sub_f_mul_e_self]
        simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, TensorProduct.sub_tmul,
          TensorProduct.tmul_sub, smul_sub]
        module

private theorem comul_commutator_ne {i j : ι} (hij : i ≠ j) :
    comulElemE D q i * comulElemF D q j - comulElemF D q j * comulElemE D q i = 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp [comulElemE, comulElemF]
  simp only [comulElemE, comulElemF, mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, mul_one]
  have hcross : (simpleK D q i * f D q j) ⊗ₜ[K] (e D q i * simpleKInv D q j) =
      (f D q j * simpleK D q i) ⊗ₜ[K] (simpleKInv D q j * e D q i) := by
    rw [simpleK_mul_f, e_mul_simpleKInv, zpow_symmetrizer_cartan_comm D q j i]
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul,
      ← zpow_add₀ (pow_ne_zero _ hq), add_neg_cancel, zpow_zero, one_smul]
  rw [hcross, (commute_e_f D q hij).eq]; abel

private theorem comul_serre_e {i j : ι} (hij : i ≠ j)
    (hfac : quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    serreSum D q (comulElemE D q) i j = 0 := by
  let U := QuantizedEnvelopingAlgebra D q
  refine serreSum_add D q (x := fun l => e D q l ⊗ₜ[K] (1 : U))
    (y := fun l => simpleK D q l ⊗ₜ[K] e D q l) hij hfac (comulElemE_summand_comm D q i)
    ?_ ?_ ?_ ?_
  · rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
      simpleK_mul_e, TensorProduct.smul_tmul']
  · rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      e_mul_simpleK, zpow_neg, zpow_symmetrizer_cartan_comm, ← zpow_neg, TensorProduct.smul_tmul']
  · simpa only [Algebra.TensorProduct.includeLeft_apply, map_zero] using
      (map_serreSum (Algebra.TensorProduct.includeLeft : U →ₐ[K] U ⊗[K] U)
        D q (e D q) i j).symm.trans (congrArg _ (serreE_eq_zero D q hij))
  · have hterm : serreSum D q (fun l => simpleK D q l ⊗ₜ[K] e D q l) i j =
        (simpleK D q j * simpleK D q i ^ D.serreLength i j) ⊗ₜ[K] serreSum D q (e D q) i j := by
      rw [serreSum_def, serreSum_def, TensorProduct.tmul_sum]
      refine sum_congr rfl fun r hr => ?_
      rw [quantumDividedPower_tmul_right, quantumDividedPower_tmul_right,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        ((commute_simpleK_simpleK D q i j).pow_left r).eq, mul_assoc (simpleK D q j),
        ← pow_add, Nat.add_sub_of_le (Nat.lt_succ_iff.mp (mem_range.mp hr)),
        ← TensorProduct.tmul_smul]
    rw [hterm, serreE_eq_zero D q hij, TensorProduct.tmul_zero]

private theorem comul_serre_f {i j : ι} (hij : i ≠ j)
    (hfac : quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    serreSum D q (comulElemF D q) i j = 0 := by
  let U := QuantizedEnvelopingAlgebra D q
  let Φ : (U ⊗[K] U) →ₐ[K] (U ⊗[K] U) :=
    (Algebra.TensorProduct.map (chevalleyInvolution D q).toAlgHom
      (chevalleyInvolution D q).toAlgHom).comp (Algebra.TensorProduct.comm K U U).toAlgHom
  have hΦ : comulElemF D q = fun l => Φ (comulElemE D q l) := by
    ext l; simp [Φ, comulElemE, comulElemF, simpleK_def, simpleKInv_def, add_comm]
  rw [hΦ, ← map_serreSum Φ D q, comul_serre_e D q hij hfac, map_zero]

private noncomputable def comulTuple
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    GeneratorTuple D q (QuantizedEnvelopingAlgebra D q ⊗[K] QuantizedEnvelopingAlgebra D q) where
  e := comulElemE D q
  f := comulElemF D q
  k y := k D q y ⊗ₜ[K] k D q y
  k_zero := by rw [k_zero, Algebra.TensorProduct.one_def]
  k_mul_k y z := by rw [Algebra.TensorProduct.tmul_mul_tmul, k_mul_k]
  conjugate_e y i := by
    simp only [comulElemE, mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      k_mul_e_mul_k_neg, k_mul_k_neg, simpleK_def]
    rw [(commute_k_k D q y (D.simpleTorus i)).eq, mul_assoc, k_mul_k_neg, mul_one,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul, TensorProduct.tmul_smul, smul_add]
  conjugate_f y i := by
    simp only [comulElemF, mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      k_mul_f_mul_k_neg, k_mul_k_neg, simpleKInv_def]
    rw [(commute_k_k D q y (-D.simpleTorus i)).eq, mul_assoc, k_mul_k_neg, mul_one,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul, TensorProduct.tmul_smul, smul_add]
  commutator_self := comul_commutator_self D q
  commutator_ne := comul_commutator_ne D q
  serre_e hij := comul_serre_e D q hij (hserre _ _ hij)
  serre_f hij := comul_serre_f D q hij (hserre _ _ hij)

/-- The coproduct `Δ : U_q(D) →ₐ[K] U_q(D) ⊗[K] U_q(D)`, defined whenever all Serre quantum
factorials are nonzero. -/
noncomputable def comulAlgHom
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    QuantizedEnvelopingAlgebra D q →ₐ[K]
      QuantizedEnvelopingAlgebra D q ⊗[K] QuantizedEnvelopingAlgebra D q :=
  lift (comulTuple D q hserre)

section WithSerre

variable (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0)

@[simp] theorem comulAlgHom_e (i : ι) :
    comulAlgHom D q hserre (e D q i) = e D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] e D q i :=
  lift_e (comulTuple D q hserre) i
@[simp] theorem comulAlgHom_f (i : ι) :
    comulAlgHom D q hserre (f D q i) = f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i :=
  lift_f (comulTuple D q hserre) i
@[simp] theorem comulAlgHom_k (y : Y) :
    comulAlgHom D q hserre (k D q y) = k D q y ⊗ₜ[K] k D q y :=
  lift_k (comulTuple D q hserre) y
@[simp] theorem comulAlgHom_simpleK (i : ι) :
    comulAlgHom D q hserre (simpleK D q i) = simpleK D q i ⊗ₜ[K] simpleK D q i := by
  simp [simpleK_def]
@[simp] theorem comulAlgHom_simpleKInv (i : ι) :
    comulAlgHom D q hserre (simpleKInv D q i) = simpleKInv D q i ⊗ₜ[K] simpleKInv D q i := by
  simp [simpleKInv_def]

@[simp] theorem comulAlgHom_normalizedE (i : ι) :
    comulAlgHom D q hserre (normalizedE D q i) =
      normalizedE D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] normalizedE D q i := by
  rw [normalizedE_def, map_mul, comulAlgHom_simpleKInv, comulAlgHom_e, mul_add,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    simpleKInv_mul_simpleK, ← normalizedE_def]

@[simp] theorem comulAlgHom_normalizedF (i : ι) :
    comulAlgHom D q hserre (normalizedF D q i) =
      normalizedF D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] normalizedF D q i := by
  rw [normalizedF_def, map_mul, comulAlgHom_f, comulAlgHom_simpleK, add_mul,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    simpleKInv_mul_simpleK, ← normalizedF_def]

/-- **Coproduct of raising divided powers**: when `[n]_(qᵢ)! ≠ 0`,
`Δ(Eᵢ^(n)) = ∑_{a=0}^n qᵢ^(a(n - a)) • ((Eᵢ^(a) Kᵢ^(n - a)) ⊗ Eᵢ^(n - a))`. -/
theorem comulAlgHom_quantumDividedPower_e {i : ι} {n : ℕ}
    (hn : quantumFactorial (q ^ D.symmetrizer i) n ≠ 0) :
    comulAlgHom D q hserre (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) =
      ∑ a ∈ range (n + 1), (q ^ D.symmetrizer i) ^ (a * (n - a)) •
        ((quantumDividedPower (q ^ D.symmetrizer i) (e D q i) a * simpleK D q i ^ (n - a)) ⊗ₜ[K]
          quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (n - a)) := by
  rw [map_quantumDividedPower, comulAlgHom_e, ← comulElemE, quantumDividedPower_comulElemE D q hn]

/-- **Coproduct of lowering divided powers**: when `[n]_(qᵢ)! ≠ 0`,
`Δ(Fᵢ^(n)) = ∑_{a=0}^n qᵢ^(a(n - a)) • (Fᵢ^(a) ⊗ (Fᵢ^(n - a) Kᵢ^(-a)))`. -/
theorem comulAlgHom_quantumDividedPower_f {i : ι} {n : ℕ}
    (hn : quantumFactorial (q ^ D.symmetrizer i) n ≠ 0) :
    comulAlgHom D q hserre (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n) =
      ∑ a ∈ range (n + 1), (q ^ D.symmetrizer i) ^ (a * (n - a)) •
        (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) a ⊗ₜ[K]
          (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) (n - a) *
            simpleKInv D q i ^ a)) := by
  rw [map_quantumDividedPower, comulAlgHom_f, ← comulElemF, quantumDividedPower_comulElemF D q hn]

/-! ### Bialgebra, Hopf algebra, and functoriality -/

/-- Coassociativity of `comulAlgHom`: `(Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ`. -/
theorem comulAlgHom_coassoc :
    (Algebra.TensorProduct.assoc K K K _ _ _).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulAlgHom D q hserre) (.id K _)).comp
        (comulAlgHom D q hserre)) =
      (Algebra.TensorProduct.map (.id K _) (comulAlgHom D q hserre)).comp
        (comulAlgHom D q hserre) := by
  apply hom_ext <;> intro x <;>
    simp [TensorProduct.tmul_add, TensorProduct.add_tmul, add_assoc, Algebra.TensorProduct.one_def]

/-- Left counit identity for `counitAlgHom` and `comulAlgHom`: `(ε ⊗ id) ∘ Δ = lid⁻¹`. -/
theorem counitAlgHom_comulAlgHom_left :
    (Algebra.TensorProduct.map (counitAlgHom D q) (.id K _)).comp (comulAlgHom D q hserre) =
      (Algebra.TensorProduct.lid K (QuantizedEnvelopingAlgebra D q)).symm.toAlgHom := by
  apply hom_ext <;> intro x <;> simp

/-- Right counit identity for `counitAlgHom` and `comulAlgHom`: `(id ⊗ ε) ∘ Δ = rid⁻¹`. -/
theorem counitAlgHom_comulAlgHom_right :
    (Algebra.TensorProduct.map (.id K _) (counitAlgHom D q)).comp (comulAlgHom D q hserre) =
      (Algebra.TensorProduct.rid K K (QuantizedEnvelopingAlgebra D q)).symm.toAlgHom := by
  apply hom_ext <;> intro x <;> simp

/-- The `Bialgebra` structure on `QuantizedEnvelopingAlgebra D q` defined by `comulAlgHom` and
`counitAlgHom`. -/
@[expose, instance_reducible]
noncomputable def bialgebra : Bialgebra K (QuantizedEnvelopingAlgebra D q) :=
  Bialgebra.ofAlgHom (comulAlgHom D q hserre) (counitAlgHom D q)
    (comulAlgHom_coassoc D q hserre) (counitAlgHom_comulAlgHom_left D q hserre)
    (counitAlgHom_comulAlgHom_right D q hserre)

@[simp] theorem bialgebra_comulAlgHom :
    letI := bialgebra D q hserre
    Bialgebra.comulAlgHom K (QuantizedEnvelopingAlgebra D q) = comulAlgHom D q hserre :=
  letI := bialgebra D q hserre; AlgHom.ext fun _ => rfl
@[simp] theorem bialgebra_comul :
    letI := bialgebra D q hserre
    Coalgebra.comul (R := K) (A := QuantizedEnvelopingAlgebra D q) =
      (comulAlgHom D q hserre).toLinearMap := (rfl)
@[simp] theorem bialgebra_counitAlgHom :
    letI := bialgebra D q hserre
    Bialgebra.counitAlgHom K (QuantizedEnvelopingAlgebra D q) = counitAlgHom D q :=
  letI := bialgebra D q hserre; AlgHom.ext fun _ => rfl
@[simp] theorem bialgebra_counit :
    letI := bialgebra D q hserre
    Coalgebra.counit (R := K) (A := QuantizedEnvelopingAlgebra D q) =
      (counitAlgHom D q).toLinearMap := (rfl)

/-- The `HopfAlgebra` structure on `QuantizedEnvelopingAlgebra D q` extending `bialgebra D q hserre`
with antipode `antipodeLinearEquiv D q`. -/
@[expose, instance_reducible]
noncomputable def hopfAlgebra : HopfAlgebra K (QuantizedEnvelopingAlgebra D q) :=
  letI := bialgebra D q hserre
  HopfAlgebra.ofAntipodeOfAdjoin (antipodeOp D q) (adjoin_range_generator D q)
    (by rintro _ ⟨i | i | y, rfl⟩ <;> simp [bialgebra_comul, bialgebra_counit, mul_assoc])
    (by rintro _ ⟨i | i | y, rfl⟩ <;>
      simp [bialgebra_comul, bialgebra_counit, simpleK_mul_simpleKInv_assoc])

/-- Every toral element `K_y` is group-like in `bialgebra D q hserre`. -/
theorem isGroupLikeElem_k (y : Y) :
    letI := bialgebra D q hserre
    IsGroupLikeElem K (k D q y) := by
  let := bialgebra D q hserre
  exact ⟨by simp [bialgebra_counit], by simp [bialgebra_comul]⟩

@[simp] theorem hopfAlgebra_toBialgebra :
    (hopfAlgebra D q hserre).toBialgebra = bialgebra D q hserre := (rfl)
@[simp] theorem hopfAlgebra_antipode :
    letI := hopfAlgebra D q hserre
    HopfAlgebraStruct.antipode K (A := QuantizedEnvelopingAlgebra D q) =
      (antipodeLinearEquiv D q).toLinearMap := by
  let := hopfAlgebra D q hserre; ext x; exact (antipodeLinearEquiv_apply D q x).symm

/-- The antipode of `hopfAlgebra D q hserre` is bijective. -/
theorem antipode_bijective :
    letI := hopfAlgebra D q hserre
    Function.Bijective
      (HopfAlgebraStruct.antipode K :
        QuantizedEnvelopingAlgebra D q →ₗ[K] QuantizedEnvelopingAlgebra D q) := by
  let := hopfAlgebra D q hserre
  rw [hopfAlgebra_antipode D q hserre]; exact (antipodeLinearEquiv D q).bijective

/-- The antipode is a coalgebra anti-automorphism: `Δ(S x) = (S ⊗ S)(swap (Δ x))`. -/
theorem comulAlgHom_antipodeLinearEquiv (x : QuantizedEnvelopingAlgebra D q) :
    comulAlgHom D q hserre (antipodeLinearEquiv D q x) =
      TensorProduct.map (antipodeLinearEquiv D q).toLinearMap
        (antipodeLinearEquiv D q).toLinearMap
        (TensorProduct.comm K _ _ (comulAlgHom D q hserre x)) := by
  let := hopfAlgebra D q hserre
  simpa only [hopfAlgebra_antipode D q hserre, hopfAlgebra_toBialgebra, bialgebra_comul,
    AlgHom.toLinearMap_apply, LinearEquiv.coe_coe] using
    TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply (R := K) x

/-- Existence and characterization of the bijective antipode on `bialgebra D q hserre`. -/
theorem exists_antipode :
    letI := bialgebra D q hserre
    ∃ S : QuantizedEnvelopingAlgebra D q →ₗ[K] QuantizedEnvelopingAlgebra D q,
      LinearMap.mul' K _ ∘ₗ S.rTensor _ ∘ₗ Coalgebra.comul =
          Algebra.linearMap K _ ∘ₗ Coalgebra.counit ∧
        LinearMap.mul' K _ ∘ₗ S.lTensor _ ∘ₗ Coalgebra.comul =
          Algebra.linearMap K _ ∘ₗ Coalgebra.counit ∧
        Function.Bijective S ∧
        (∀ i, S (e D q i) = -(simpleKInv D q i * e D q i)) ∧
        (∀ i, S (f D q i) = -(f D q i * simpleK D q i)) ∧
        ∀ y, S (k D q y) = k D q (-y) := by
  let H := hopfAlgebra D q hserre
  refine ⟨HopfAlgebraStruct.antipode K, H.mul_antipode_rTensor_comul,
    H.mul_antipode_lTensor_comul, antipode_bijective D q hserre, ?_⟩
  rw [hopfAlgebra_antipode D q hserre]
  exact ⟨antipodeLinearEquiv_e D q, antipodeLinearEquiv_f D q, antipodeLinearEquiv_k D q⟩

end WithSerre

end CounitAndCoproduct

section Functoriality

variable {ι X Y X' Y' K : Type*} [AddCommGroup X] [AddCommGroup Y]
  [AddCommGroup X'] [AddCommGroup Y'] [Field K]
  {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'}

/-- A morphism of Cartan data transports nonvanishing of the Serre quantum factorials. -/
theorem serre_ne_zero_of_hom (φ : CartanDatum.Hom D D') {q : K}
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0)
    (i j : ι) (hij : i ≠ j) :
    quantumFactorial (q ^ D'.symmetrizer i) (D'.serreLength i j) ≠ 0 := by
  rw [φ.symmetrizer_eq, φ.serreLength_eq]; exact hserre i j hij

/-- A morphism of Cartan data preserves the counit: `ε' ∘ map φ q = ε`. -/
@[simp] theorem counitAlgHom_comp_map (φ : CartanDatum.Hom D D') (q : K) :
    (counitAlgHom D' q).comp (map φ q) = counitAlgHom D q := by
  apply hom_ext <;> intro x <;> simp

section WithSerre

variable (φ : CartanDatum.Hom D D') (q : K)
  (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0)

/-- A morphism of Cartan data preserves the coproduct:
`(map φ q ⊗ map φ q) ∘ Δ = Δ' ∘ map φ q`. -/
theorem map_comp_comulAlgHom :
    (Algebra.TensorProduct.map (map φ q) (map φ q)).comp (comulAlgHom D q hserre) =
      (comulAlgHom D' q (serre_ne_zero_of_hom φ hserre)).comp (map φ q) := by
  apply hom_ext <;> intro x <;> simp

/-- A morphism of Cartan data induces a bialgebra homomorphism between the corresponding quantized
enveloping algebras. -/
noncomputable def mapBialgHom :
    letI := bialgebra D q hserre
    letI := bialgebra D' q (serre_ne_zero_of_hom φ hserre)
    QuantizedEnvelopingAlgebra D q →ₐc[K] QuantizedEnvelopingAlgebra D' q :=
  letI := bialgebra D q hserre
  letI := bialgebra D' q (serre_ne_zero_of_hom φ hserre)
  BialgHom.ofAlgHom (map φ q)
    (by simpa only [bialgebra_counitAlgHom] using counitAlgHom_comp_map φ q)
    (by simpa only [bialgebra_comulAlgHom] using map_comp_comulAlgHom φ q hserre)

@[simp] theorem mapBialgHom_toAlgHom :
    letI := bialgebra D q hserre
    letI := bialgebra D' q (serre_ne_zero_of_hom φ hserre)
    (mapBialgHom φ q hserre : QuantizedEnvelopingAlgebra D q →ₐ[K]
      QuantizedEnvelopingAlgebra D' q) = map φ q := (rfl)

@[simp] theorem mapBialgHom_apply (x : QuantizedEnvelopingAlgebra D q) :
    letI := bialgebra D q hserre
    letI := bialgebra D' q (serre_ne_zero_of_hom φ hserre)
    mapBialgHom φ q hserre x = map φ q x := (rfl)

end WithSerre

end Functoriality

end QuantizedEnvelopingAlgebra

end TauCeti
