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
import Mathlib.Tactic.Ring

/-!
# The Hopf algebra structure on the Drinfeld-Jimbo quantized enveloping algebra

This file constructs the counit, coproduct, bialgebra structure, and Hopf algebra structure on
`TauCeti.QuantizedEnvelopingAlgebra D q` for a Cartan datum `D` and parameter `q` in a field `K`,
together with the coproduct formulas on quantum divided powers and functoriality along morphisms of
Cartan data.

## Conventions

With `qᵢ = q ^ D.symmetrizer i`, `Kᵢ = simpleK D q i`, and `Kᵢ⁻¹ = simpleKInv D q i`, the
coalgebra maps take the generator values:
* `ε(Eᵢ) = 0`, `ε(Fᵢ) = 0`, `ε(K_y) = 1`;
* `Δ(Eᵢ) = Eᵢ ⊗ 1 + Kᵢ ⊗ Eᵢ`, `Δ(Fᵢ) = Fᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ Fᵢ`, `Δ(K_y) = K_y ⊗ K_y`.

The counit `counitAlgHom` is defined unconditionally for every `q : K` and witnesses that
`QuantizedEnvelopingAlgebra D q` is nontrivial. The coproduct `comulAlgHom`, bialgebra `bialgebra`,
and Hopf algebra `hopfAlgebra` require only the nonvanishing of the Serre quantum factorials
`∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0`, which holds in
particular at every generic quantum parameter (`quantumFactorial_serreLength_ne_zero`).

## Main definitions and results

* `TauCeti.QuantizedEnvelopingAlgebra.counitAlgHom`: the unconditional counit `U_q(D) →ₐ[K] K`, and
  the resulting `Nontrivial` instance on `QuantizedEnvelopingAlgebra D q`.
* `TauCeti.QuantizedEnvelopingAlgebra.comulAlgHom`: the coproduct `U_q(D) →ₐ[K] U_q(D) ⊗[K] U_q(D)`,
  its values on `normalizedE` and `normalizedF`, and the divided-power coproduct formulas
  `comulAlgHom_quantumDividedPower_e` and `comulAlgHom_quantumDividedPower_f`.
* `TauCeti.QuantizedEnvelopingAlgebra.bialgebra` and `hopfAlgebra`: the Mathlib `Bialgebra` and
  `HopfAlgebra` structures on `QuantizedEnvelopingAlgebra D q`, coalgebra anti-multiplicativity of
  the antipode (`comulAlgHom_antipodeLinearEquiv`), and `exists_antipode`.
* `TauCeti.QuantizedEnvelopingAlgebra.mapBialgHom`: functoriality of the bialgebra structure under
  `CartanDatum.Hom`.

## References

* G. Lusztig, *Canonical bases arising from quantized enveloping algebras*, J. Amer. Math. Soc. 3
  (1990), Proposition 4.8.
* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  Chapter 3.
* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, AMS, 1996,
  Chapter 4.
* S. Lentner, *Quantum groups and Nichols algebras acting on conformal field theories*, Adv. Math.
  251 (2014), Section 3.
-/

public section

open Finset
open scoped TensorProduct

namespace TauCeti

namespace QuantizedEnvelopingAlgebra

/-! ### Unconditional counit and nontriviality -/

section Counit

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

/-- `ε(Eᵢ) = 0`. -/
@[simp]
theorem counitAlgHom_e (i : ι) : counitAlgHom D q (e D q i) = 0 := by
  simp [counitAlgHom, counitTuple]

/-- `ε(Fᵢ) = 0`. -/
@[simp]
theorem counitAlgHom_f (i : ι) : counitAlgHom D q (f D q i) = 0 := by
  simp [counitAlgHom, counitTuple]

/-- `ε(K_y) = 1`. -/
@[simp]
theorem counitAlgHom_k (y : Y) : counitAlgHom D q (k D q y) = 1 := by
  simp [counitAlgHom, counitTuple]

/-- `ε(Kᵢ) = 1`. -/
@[simp]
theorem counitAlgHom_simpleK (i : ι) : counitAlgHom D q (simpleK D q i) = 1 := by
  simp [simpleK_def]

/-- `ε(Kᵢ⁻¹) = 1`. -/
@[simp]
theorem counitAlgHom_simpleKInv (i : ι) : counitAlgHom D q (simpleKInv D q i) = 1 := by
  simp [simpleKInv_def]

/-- `ε(eᵢ) = 0` for the normalized raising generator `eᵢ = Kᵢ⁻¹ Eᵢ`. -/
@[simp]
theorem counitAlgHom_normalizedE (i : ι) : counitAlgHom D q (normalizedE D q i) = 0 := by
  simp [normalizedE_def]

/-- `ε(fᵢ) = 0` for the normalized lowering generator `fᵢ = Fᵢ Kᵢ`. -/
@[simp]
theorem counitAlgHom_normalizedF (i : ι) : counitAlgHom D q (normalizedF D q i) = 0 := by
  simp [normalizedF_def]

noncomputable instance : Nontrivial (QuantizedEnvelopingAlgebra D q) :=
  (counitAlgHom D q).toRingHom.domain_nontrivial

end Counit

/-! ### Coproduct and divided-power coproduct formulas -/

section Coproduct

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
  (D : CartanDatum ι X Y) (q : K)

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
    (simpleK D q i ⊗ₜ[K] e D q i) * (e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q)) =
      (q ^ D.symmetrizer i) ^ 2 •
        ((e D q i ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q)) * (simpleK D q i ⊗ₜ[K] e D q i)) := by
  have hke : simpleK D q i * e D q i =
      (q ^ D.symmetrizer i) ^ 2 • (e D q i * simpleK D q i) := by
    rw [simpleK_mul_e, D.cartan_apply_self, zpow_two, ← pow_two]
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
    hke, TensorProduct.smul_tmul']

private theorem comulElemF_summand_comm (i : ι) :
    (f D q i ⊗ₜ[K] simpleKInv D q i) * ((1 : QuantizedEnvelopingAlgebra D q) ⊗ₜ[K] f D q i) =
      (q ^ D.symmetrizer i) ^ 2 •
        (((1 : QuantizedEnvelopingAlgebra D q) ⊗ₜ[K] f D q i) *
          (f D q i ⊗ₜ[K] simpleKInv D q i)) := by
  have hkf : simpleKInv D q i * f D q i =
      (q ^ D.symmetrizer i) ^ 2 • (f D q i * simpleKInv D q i) := by
    rw [simpleKInv_mul_f, D.cartan_apply_self, zpow_two, ← pow_two]
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
    hkf, TensorProduct.tmul_smul]

private theorem quantumDividedPower_tmul_one (q' : K) (x : QuantizedEnvelopingAlgebra D q)
    (n : ℕ) :
    quantumDividedPower q' (x ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q)) n =
      quantumDividedPower q' x n ⊗ₜ[K] 1 := by
  simpa only [Algebra.TensorProduct.includeLeft_apply] using
    (map_quantumDividedPower
      (Algebra.TensorProduct.includeLeft : QuantizedEnvelopingAlgebra D q →ₐ[K]
        QuantizedEnvelopingAlgebra D q ⊗[K] QuantizedEnvelopingAlgebra D q) q' x n).symm

private theorem quantumDividedPower_one_tmul (q' : K) (x : QuantizedEnvelopingAlgebra D q)
    (n : ℕ) :
    quantumDividedPower q' ((1 : QuantizedEnvelopingAlgebra D q) ⊗ₜ[K] x) n =
      1 ⊗ₜ[K] quantumDividedPower q' x n := by
  simpa only [Algebra.TensorProduct.includeRight_apply] using
    (map_quantumDividedPower
      (Algebra.TensorProduct.includeRight : QuantizedEnvelopingAlgebra D q →ₐ[K]
        QuantizedEnvelopingAlgebra D q ⊗[K] QuantizedEnvelopingAlgebra D q) q' x n).symm

private theorem quantumDividedPower_simpleK_tmul_e (q' : K) (i : ι) (n : ℕ) :
    quantumDividedPower q' (simpleK D q i ⊗ₜ[K] e D q i) n =
      (simpleK D q i ^ n) ⊗ₜ[K] quantumDividedPower q' (e D q i) n := by
  let U := QuantizedEnvelopingAlgebra D q
  have hsplit : simpleK D q i ⊗ₜ[K] e D q i =
      (simpleK D q i ⊗ₜ[K] (1 : U)) * ((1 : U) ⊗ₜ[K] e D q i) := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  have hc : Commute (simpleK D q i ⊗ₜ[K] (1 : U)) ((1 : U) ⊗ₜ[K] e D q i) := by
    simp [Commute, SemiconjBy, Algebra.TensorProduct.tmul_mul_tmul]
  have hpow : (simpleK D q i ⊗ₜ[K] (1 : U)) ^ n = (simpleK D q i ^ n) ⊗ₜ[K] 1 := by simp
  rw [hsplit, quantumDividedPower_mul_left_of_commute q' hc, hpow,
    quantumDividedPower_one_tmul D q, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

private theorem quantumDividedPower_f_tmul_simpleKInv (q' : K) (i : ι) (n : ℕ) :
    quantumDividedPower q' (f D q i ⊗ₜ[K] simpleKInv D q i) n =
      quantumDividedPower q' (f D q i) n ⊗ₜ[K] (simpleKInv D q i ^ n) := by
  let U := QuantizedEnvelopingAlgebra D q
  have hsplit : f D q i ⊗ₜ[K] simpleKInv D q i =
      (f D q i ⊗ₜ[K] (1 : U)) * ((1 : U) ⊗ₜ[K] simpleKInv D q i) := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  have hc : Commute (f D q i ⊗ₜ[K] (1 : U)) ((1 : U) ⊗ₜ[K] simpleKInv D q i) := by
    simp [Commute, SemiconjBy, Algebra.TensorProduct.tmul_mul_tmul]
  have hpow : ((1 : U) ⊗ₜ[K] simpleKInv D q i) ^ n = 1 ⊗ₜ[K] (simpleKInv D q i ^ n) := by simp
  rw [hsplit, quantumDividedPower_mul_right_of_commute q' hc,
    quantumDividedPower_tmul_one D q, hpow, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

private theorem quantumDividedPower_comulElemE {i : ι} {n : ℕ}
    (hn : quantumFactorial (q ^ D.symmetrizer i) n ≠ 0) :
    quantumDividedPower (q ^ D.symmetrizer i) (comulElemE D q i) n =
      ∑ a ∈ range (n + 1), (q ^ D.symmetrizer i) ^ (a * (n - a)) •
        ((quantumDividedPower (q ^ D.symmetrizer i) (e D q i) a * simpleK D q i ^ (n - a)) ⊗ₜ[K]
          quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (n - a)) := by
  rw [comulElemE, quantumDividedPower_add (comulElemE_summand_comm D q i) hn]
  refine sum_congr rfl fun a _ => ?_
  rw [quantumDividedPower_tmul_one D q, quantumDividedPower_simpleK_tmul_e D q,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

private theorem quantumDividedPower_comulElemF {i : ι} {n : ℕ}
    (hn : quantumFactorial (q ^ D.symmetrizer i) n ≠ 0) :
    quantumDividedPower (q ^ D.symmetrizer i) (comulElemF D q i) n =
      ∑ a ∈ range (n + 1), (q ^ D.symmetrizer i) ^ (a * (n - a)) •
        (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) a ⊗ₜ[K]
          (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) (n - a) *
            simpleKInv D q i ^ a)) := by
  have hadd : comulElemF D q i =
      (1 ⊗ₜ[K] f D q i) + (f D q i ⊗ₜ[K] simpleKInv D q i) := add_comm _ _
  rw [hadd, quantumDividedPower_add (comulElemF_summand_comm D q i) hn, ← sum_range_reflect]
  refine sum_congr rfl fun a ha => ?_
  have han : a ≤ n := Nat.lt_succ_iff.mp (mem_range.mp ha)
  simp only [Nat.add_succ_sub_one, add_zero, Nat.sub_sub_self han]
  rw [Nat.mul_comm (n - a) a, quantumDividedPower_one_tmul D q,
    quantumDividedPower_f_tmul_simpleKInv D q, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

private theorem comul_commutator_self (i : ι) :
    comulElemE D q i * comulElemF D q i - comulElemF D q i * comulElemE D q i =
      (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
        (k D q (D.simpleTorus i) ⊗ₜ[K] k D q (D.simpleTorus i) -
          k D q (-D.simpleTorus i) ⊗ₜ[K] k D q (-D.simpleTorus i)) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp [comulElemE, comulElemF, zero_pow (D.symmetrizer_pos i).ne']
  have hqᵢ : q ^ D.symmetrizer i ≠ 0 := pow_ne_zero _ hq
  simp only [comulElemE, comulElemF, mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, mul_one, ← simpleK_def, ← simpleKInv_def]
  have hcross : (simpleK D q i * f D q i) ⊗ₜ[K] (e D q i * simpleKInv D q i) =
      (f D q i * simpleK D q i) ⊗ₜ[K] (simpleKInv D q i * e D q i) := by
    rw [simpleK_mul_f, e_mul_simpleKInv]
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul, ← zpow_add₀ hqᵢ,
      add_neg_cancel, zpow_zero, one_smul]
  rw [hcross]
  calc
    _ = (e D q i * f D q i - f D q i * e D q i) ⊗ₜ[K] simpleKInv D q i +
          simpleK D q i ⊗ₜ[K] (e D q i * f D q i - f D q i * e D q i) := by
      simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      abel
    _ = _ := by
      rw [e_mul_f_sub_f_mul_e_self]
      simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, TensorProduct.sub_tmul,
        TensorProduct.tmul_sub, smul_sub]
      module

private theorem comul_commutator_ne {i j : ι} (hij : i ≠ j) :
    comulElemE D q i * comulElemF D q j - comulElemF D q j * comulElemE D q i = 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp [comulElemE, comulElemF]
  have hqᵢ : q ^ D.symmetrizer i ≠ 0 := pow_ne_zero _ hq
  simp only [comulElemE, comulElemF, mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, mul_one]
  have hei_kj : e D q i * simpleKInv D q j =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (simpleKInv D q j * e D q i) := by
    rw [e_mul_simpleKInv, ← zpow_natCast q, ← zpow_mul, D.symmetrizer_mul_cartan j i, zpow_mul,
      zpow_natCast]
  have hcross : (simpleK D q i * f D q j) ⊗ₜ[K] (e D q i * simpleKInv D q j) =
      (f D q j * simpleK D q i) ⊗ₜ[K] (simpleKInv D q j * e D q i) := by
    rw [simpleK_mul_f, hei_kj]
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul, ← zpow_add₀ hqᵢ,
      add_neg_cancel, zpow_zero, one_smul]
  rw [hcross, (commute_e_f D q hij).eq]
  abel

private theorem expand_serre_comulElemE {i : ι} {m : ℕ}
    (hfac : quantumFactorial (q ^ D.symmetrizer i) m ≠ 0)
    (mid : QuantizedEnvelopingAlgebra D q ⊗[K] QuantizedEnvelopingAlgebra D q) :
    ∑ r ∈ range (m + 1), (-1 : K) ^ r •
      (quantumDividedPower (q ^ D.symmetrizer i) (comulElemE D q i) r * mid *
        quantumDividedPower (q ^ D.symmetrizer i) (comulElemE D q i) (m - r)) =
      ∑ r ∈ range (m + 1), ∑ a₁ ∈ range (r + 1), ∑ a₂ ∈ range (m - r + 1),
        (-1 : K) ^ r •
          (((q ^ D.symmetrizer i) ^ (a₁ * (r - a₁)) •
              ((quantumDividedPower (q ^ D.symmetrizer i) (e D q i) a₁ *
                  simpleK D q i ^ (r - a₁)) ⊗ₜ[K]
                quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (r - a₁))) *
            mid *
            ((q ^ D.symmetrizer i) ^ (a₂ * (m - r - a₂)) •
              ((quantumDividedPower (q ^ D.symmetrizer i) (e D q i) a₂ *
                  simpleK D q i ^ (m - r - a₂)) ⊗ₜ[K]
                quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (m - r - a₂)))) := by
  refine sum_congr rfl fun r hr => ?_
  have hrm : r ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hr)
  rw [quantumDividedPower_comulElemE D q (quantumFactorial_ne_zero_of_le hrm hfac),
    quantumDividedPower_comulElemE D q (quantumFactorial_ne_zero_of_le (Nat.sub_le m r) hfac),
    sum_mul, sum_mul, smul_sum]
  exact sum_congr rfl fun _ _ => by rw [mul_sum, smul_sum]

private theorem sum_serre_reindex_left {M : Type*} [AddCommMonoid M] (m : ℕ)
    (F : ℕ → ℕ → ℕ → M) :
    ∑ r ∈ range (m + 1), ∑ a₁ ∈ range (r + 1), ∑ a₂ ∈ range (m - r + 1), F r a₁ a₂ =
      ∑ b ∈ range (m + 1), ∑ a₁ ∈ range (m - b + 1), ∑ b₁ ∈ range (b + 1),
        F (a₁ + b₁) a₁ (m - b - a₁) := by
  simp only [sum_sigma']
  refine Finset.sum_nbij'
    (fun ⟨r, ⟨a₁, a₂⟩⟩ => ⟨(r - a₁) + (m - r - a₂), ⟨a₁, r - a₁⟩⟩)
    (fun ⟨b, ⟨a₁, b₁⟩⟩ => ⟨a₁ + b₁, ⟨a₁, m - b - a₁⟩⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨r, ⟨a₁, a₂⟩⟩ hx; simp only [mem_sigma, mem_range] at hx ⊢; omega
  · rintro ⟨b, ⟨a₁, b₁⟩⟩ hy; simp only [mem_sigma, mem_range] at hy ⊢; omega
  · rintro ⟨r, ⟨a₁, a₂⟩⟩ hx; simp only [mem_sigma, mem_range] at hx
    exact Sigma.ext (by dsimp; omega) (heq_of_eq <| Sigma.ext rfl (heq_of_eq <| by dsimp; omega))
  · rintro ⟨b, ⟨a₁, b₁⟩⟩ hy; simp only [mem_sigma, mem_range] at hy
    exact Sigma.ext (by dsimp; omega) (heq_of_eq <| Sigma.ext rfl (heq_of_eq <| by dsimp; omega))
  · rintro ⟨r, ⟨a₁, a₂⟩⟩ hx; simp only [mem_sigma, mem_range] at hx
    dsimp
    congr 1 <;> omega

private theorem sum_serre_reindex_right {M : Type*} [AddCommMonoid M] (m : ℕ)
    (F : ℕ → ℕ → ℕ → M) :
    ∑ r ∈ range (m + 1), ∑ a₁ ∈ range (r + 1), ∑ a₂ ∈ range (m - r + 1), F r a₁ a₂ =
      ∑ a ∈ range (m + 1), ∑ b₁ ∈ range (m - a + 1), ∑ a₁ ∈ range (a + 1),
        F (a₁ + b₁) a₁ (a - a₁) := by
  simp only [sum_sigma']
  refine Finset.sum_nbij'
    (fun ⟨r, ⟨a₁, a₂⟩⟩ => ⟨a₁ + a₂, ⟨r - a₁, a₁⟩⟩)
    (fun ⟨a, ⟨b₁, a₁⟩⟩ => ⟨a₁ + b₁, ⟨a₁, a - a₁⟩⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨r, ⟨a₁, a₂⟩⟩ hx; simp only [mem_sigma, mem_range] at hx ⊢; omega
  · rintro ⟨a, ⟨b₁, a₁⟩⟩ hy; simp only [mem_sigma, mem_range] at hy ⊢; omega
  · rintro ⟨r, ⟨a₁, a₂⟩⟩ hx; simp only [mem_sigma, mem_range] at hx
    exact Sigma.ext (by dsimp; omega) (heq_of_eq <| Sigma.ext rfl (heq_of_eq <| by dsimp; omega))
  · rintro ⟨a, ⟨b₁, a₁⟩⟩ hy; simp only [mem_sigma, mem_range] at hy
    exact Sigma.ext (by dsimp; omega) (heq_of_eq <| Sigma.ext (by dsimp; omega) (heq_of_eq rfl))
  · rintro ⟨r, ⟨a₁, a₂⟩⟩ hx; simp only [mem_sigma, mem_range] at hx
    dsimp
    congr 1 <;> omega

private theorem comul_serre_e_left_scalar {i j : ι} (hij : i ≠ j)
    (hqᵢ : q ^ D.symmetrizer i ≠ 0) {b a₁ b₁ : ℕ} (hb : b ≤ D.serreLength i j)
    (ha₁ : a₁ ≤ D.serreLength i j - b) (hb₁ : b₁ ≤ b) :
    (-1 : K) ^ (a₁ + b₁) *
        ((q ^ D.symmetrizer i) ^ ((D.serreLength i j - b - a₁) * (b - b₁)) *
          ((q ^ D.symmetrizer i) ^ (a₁ * b₁) *
            (quantumBinomial (q ^ D.symmetrizer i) b b₁ *
              ((q ^ D.symmetrizer i) ^ ((b₁ : ℤ) * D.cartan i j) *
                (q ^ D.symmetrizer i) ^
                  (2 * (b₁ : ℤ) * ((D.serreLength i j - b - a₁ : ℕ) : ℤ)))))) =
      (-1 : K) ^ a₁ * (q ^ D.symmetrizer i) ^ ((D.serreLength i j - b - a₁) * b) *
        ((-1 : K) ^ b₁ * (q ^ D.symmetrizer i) ^ ((b₁ : ℤ) * (1 - (b : ℤ))) *
          quantumBinomial (q ^ D.symmetrizer i) b b₁) := by
  set m := D.serreLength i j
  set a₂ := m - b - a₁
  set b₂ := b - b₁
  set qᵢ := q ^ D.symmetrizer i
  have hcart : D.cartan i j = 1 - (m : ℤ) := by have := D.natCast_serreLength hij; omega
  have hm_eq : (m : ℤ) = (a₁ : ℤ) + (a₂ : ℤ) + (b : ℤ) := by omega
  have hb_eq : (b₂ : ℤ) = (b : ℤ) - (b₁ : ℤ) := by omega
  rw [pow_add (-1 : K), ← zpow_natCast qᵢ (a₁ * b₁), ← zpow_natCast qᵢ (a₂ * b₂),
    ← zpow_natCast qᵢ (a₂ * b)]
  have hexp : qᵢ ^ ((a₁ * b₁ : ℕ) : ℤ) * qᵢ ^ ((a₂ * b₂ : ℕ) : ℤ) *
      qᵢ ^ ((b₁ : ℤ) * D.cartan i j) * qᵢ ^ (2 * (b₁ : ℤ) * (a₂ : ℤ)) =
      qᵢ ^ ((a₂ * b : ℕ) : ℤ) * qᵢ ^ ((b₁ : ℤ) * (1 - (b : ℤ))) := by
    rw [← zpow_add₀ hqᵢ, ← zpow_add₀ hqᵢ, ← zpow_add₀ hqᵢ, ← zpow_add₀ hqᵢ]
    congr 1
    push_cast
    rw [hcart, hm_eq, hb_eq]
    ring
  linear_combination (-1 : K) ^ a₁ * (-1 : K) ^ b₁ * quantumBinomial qᵢ b b₁ * hexp

private theorem comul_serre_e_left_term {i j : ι} (hij : i ≠ j)
    (hqᵢ : q ^ D.symmetrizer i ≠ 0)
    (hfac : quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0)
    {b a₁ b₁ : ℕ} (hb : b ≤ D.serreLength i j) (ha₁ : a₁ ≤ D.serreLength i j - b)
    (hb₁ : b₁ ≤ b) :
    (-1 : K) ^ (a₁ + b₁) •
      (((q ^ D.symmetrizer i) ^ (a₁ * b₁) •
          ((quantumDividedPower (q ^ D.symmetrizer i) (e D q i) a₁ * simpleK D q i ^ b₁) ⊗ₜ[K]
            quantumDividedPower (q ^ D.symmetrizer i) (e D q i) b₁)) *
        (e D q j ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q)) *
        ((q ^ D.symmetrizer i) ^ ((D.serreLength i j - b - a₁) * (b - b₁)) •
          ((quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (D.serreLength i j - b - a₁) *
              simpleK D q i ^ (b - b₁)) ⊗ₜ[K]
            quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (b - b₁)))) =
    ((-1 : K) ^ a₁ * (q ^ D.symmetrizer i) ^ ((D.serreLength i j - b - a₁) * b) *
        ((-1 : K) ^ b₁ * (q ^ D.symmetrizer i) ^ ((b₁ : ℤ) * (1 - (b : ℤ))) *
          quantumBinomial (q ^ D.symmetrizer i) b b₁)) •
      ((quantumDividedPower (q ^ D.symmetrizer i) (e D q i) a₁ * e D q j *
          quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (D.serreLength i j - b - a₁) *
          simpleK D q i ^ b) ⊗ₜ[K]
        quantumDividedPower (q ^ D.symmetrizer i) (e D q i) b) := by
  have hfac_b : quantumFactorial (q ^ D.symmetrizer i) (b₁ + (b - b₁)) ≠ 0 := by
    rw [Nat.add_sub_of_le hb₁]; exact quantumFactorial_ne_zero_of_le hb hfac
  have hk_edp :
      simpleK D q i ^ b₁ *
          quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (D.serreLength i j - b - a₁) =
        (q ^ D.symmetrizer i) ^
            (2 * (b₁ : ℤ) * ((D.serreLength i j - b - a₁ : ℕ) : ℤ)) •
          (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (D.serreLength i j - b - a₁) *
            simpleK D q i ^ b₁) := by
    simpa only [D.cartan_apply_self,
      mul_comm ((b₁ : ℤ) * ((D.serreLength i j - b - a₁ : ℕ) : ℤ)) 2, ← mul_assoc] using
      simpleK_pow_mul_quantumDividedPower_e D q (q ^ D.symmetrizer i) i i b₁
        (D.serreLength i j - b - a₁)
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    quantumDividedPower_mul_quantumDividedPower _ hfac_b, Nat.add_sub_of_le hb₁]
  have hword :
      (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) a₁ * simpleK D q i ^ b₁) * e D q j *
          (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (D.serreLength i j - b - a₁) *
            simpleK D q i ^ (b - b₁)) =
        ((q ^ D.symmetrizer i) ^ ((b₁ : ℤ) * D.cartan i j) *
          (q ^ D.symmetrizer i) ^
            (2 * (b₁ : ℤ) * ((D.serreLength i j - b - a₁ : ℕ) : ℤ))) •
          (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) a₁ * e D q j *
            quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (D.serreLength i j - b - a₁) *
            simpleK D q i ^ b) := by
    calc _ = (q ^ D.symmetrizer i) ^ ((b₁ : ℤ) * D.cartan i j) •
              (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) a₁ * e D q j *
                (simpleK D q i ^ b₁ *
                  quantumDividedPower (q ^ D.symmetrizer i) (e D q i)
                    (D.serreLength i j - b - a₁)) *
                simpleK D q i ^ (b - b₁)) := by
            rw [mul_assoc (quantumDividedPower _ (e D q i) a₁), simpleK_pow_mul_e]
            simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
      _ = _ := by
            rw [hk_edp]
            simp only [mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, ← pow_add,
              Nat.add_sub_of_le hb₁]
  rw [hword]
  simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul]
  rw [comul_serre_e_left_scalar D q hij hqᵢ hb ha₁ hb₁]

private theorem comul_serre_e_left {i j : ι} (hij : i ≠ j)
    (hfac : quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    ∑ r ∈ range (D.serreLength i j + 1), (-1 : K) ^ r •
      (quantumDividedPower (q ^ D.symmetrizer i) (comulElemE D q i) r *
        (e D q j ⊗ₜ[K] (1 : QuantizedEnvelopingAlgebra D q)) *
        quantumDividedPower (q ^ D.symmetrizer i) (comulElemE D q i)
          (D.serreLength i j - r)) = 0 := by
  have hqᵢ : q ^ D.symmetrizer i ≠ 0 := ne_zero_of_sub_inv_ne_zero
    (sub_inv_ne_zero_of_quantumFactorial_ne_zero (D.serreLength_ne_zero hij) hfac)
  rw [expand_serre_comulElemE D q hfac, sum_serre_reindex_left]
  refine sum_eq_zero fun b hb => ?_
  have hbm : b ≤ D.serreLength i j := Nat.lt_succ_iff.mp (mem_range.mp hb)
  rcases eq_or_ne b 0 with rfl | hb₀
  · have hb0 : ∑ a₁ ∈ range (D.serreLength i j + 1),
        (-1 : K) ^ a₁ • ((quantumDividedPower (q ^ D.symmetrizer i) (e D q i) a₁ * e D q j *
          quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (D.serreLength i j - a₁)) ⊗ₜ[K]
            (1 : QuantizedEnvelopingAlgebra D q)) = 0 := by
      simp only [TensorProduct.smul_tmul', ← TensorProduct.sum_tmul, ← serreSum_def,
        serreE_eq_zero D q hij, TensorProduct.zero_tmul]
    refine (sum_congr rfl fun a₁ ha₁ => ?_).trans hb0
    rw [sum_range_one]
    have hterm := comul_serre_e_left_term D q hij hqᵢ hfac (Nat.zero_le _)
      (Nat.lt_succ_iff.mp (mem_range.mp ha₁)) le_rfl
    simpa only [Nat.add_zero, Nat.sub_zero, Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero,
      pow_zero, zpow_zero, mul_one, one_smul, quantumBinomial_zero_right,
      quantumDividedPower_zero] using hterm
  · refine sum_eq_zero fun a₁ ha₁ => ?_
    have ha₁m : a₁ ≤ D.serreLength i j - b := Nat.lt_succ_iff.mp (mem_range.mp ha₁)
    calc _ = ∑ b₁ ∈ range (b + 1),
          ((-1 : K) ^ a₁ * (q ^ D.symmetrizer i) ^ ((D.serreLength i j - b - a₁) * b) *
            ((-1 : K) ^ b₁ * (q ^ D.symmetrizer i) ^ ((b₁ : ℤ) * (1 - (b : ℤ))) *
              quantumBinomial (q ^ D.symmetrizer i) b b₁)) •
            ((quantumDividedPower (q ^ D.symmetrizer i) (e D q i) a₁ * e D q j *
                quantumDividedPower (q ^ D.symmetrizer i) (e D q i)
                  (D.serreLength i j - b - a₁) * simpleK D q i ^ b) ⊗ₜ[K]
              quantumDividedPower (q ^ D.symmetrizer i) (e D q i) b) := by
          refine sum_congr rfl fun b₁ hb₁ => ?_
          have hb₁b : b₁ ≤ b := Nat.lt_succ_iff.mp (mem_range.mp hb₁)
          have hsub :
              D.serreLength i j - (a₁ + b₁) - (D.serreLength i j - b - a₁) = b - b₁ := by omega
          simpa only [Nat.add_sub_cancel_left, hsub] using
            comul_serre_e_left_term D q hij hqᵢ hfac hbm ha₁m hb₁b
      _ = 0 := by
          rw [← sum_smul, ← mul_sum,
            sum_neg_one_pow_mul_zpow_one_sub_mul_quantumBinomial hqᵢ hb₀, mul_zero, zero_smul]

private theorem comul_serre_e_right_scalar {i j : ι} (hij : i ≠ j)
    (hqᵢ : q ^ D.symmetrizer i ≠ 0) {a b₁ a₁ : ℕ} (ha : a ≤ D.serreLength i j)
    (hb₁ : b₁ ≤ D.serreLength i j - a) (ha₁ : a₁ ≤ a) :
    (-1 : K) ^ (a₁ + b₁) *
        ((q ^ D.symmetrizer i) ^ ((a - a₁) * (D.serreLength i j - a - b₁)) *
          ((q ^ D.symmetrizer i) ^ (a₁ * b₁) *
            (((q ^ D.symmetrizer i) ^ (-(a₁ : ℤ) * D.cartan i j) *
                (q ^ D.symmetrizer i) ^ (2 * (b₁ : ℤ) * ((a - a₁ : ℕ) : ℤ)) *
                quantumBinomial (q ^ D.symmetrizer i) a a₁)))) =
      (-1 : K) ^ b₁ * (q ^ D.symmetrizer i) ^ (a * (D.serreLength i j - a - b₁) + 2 * b₁ * a) *
        ((-1 : K) ^ a₁ * (q ^ D.symmetrizer i) ^ ((a₁ : ℤ) * ((a : ℤ) - 1)) *
          quantumBinomial (q ^ D.symmetrizer i) a a₁) := by
  set m := D.serreLength i j
  set a₂ := a - a₁
  set b₂ := m - a - b₁
  set qᵢ := q ^ D.symmetrizer i
  have hcart : D.cartan i j = 1 - (m : ℤ) := by have := D.natCast_serreLength hij; omega
  have hm_eq : (m : ℤ) = (a : ℤ) + (b₁ : ℤ) + (b₂ : ℤ) := by omega
  have ha_eq : (a₂ : ℤ) = (a : ℤ) - (a₁ : ℤ) := by omega
  rw [pow_add (-1 : K), ← zpow_natCast qᵢ (a₁ * b₁), ← zpow_natCast qᵢ (a₂ * b₂),
    ← zpow_natCast qᵢ (a * b₂ + 2 * b₁ * a)]
  have hexp : qᵢ ^ ((a₁ * b₁ : ℕ) : ℤ) * qᵢ ^ ((a₂ * b₂ : ℕ) : ℤ) *
      qᵢ ^ (-(a₁ : ℤ) * D.cartan i j) * qᵢ ^ (2 * (b₁ : ℤ) * (a₂ : ℤ)) =
      qᵢ ^ ((a * b₂ + 2 * b₁ * a : ℕ) : ℤ) * qᵢ ^ ((a₁ : ℤ) * ((a : ℤ) - 1)) := by
    rw [← zpow_add₀ hqᵢ, ← zpow_add₀ hqᵢ, ← zpow_add₀ hqᵢ, ← zpow_add₀ hqᵢ]
    congr 1
    push_cast
    rw [hcart, hm_eq, ha_eq]
    ring
  linear_combination (-1 : K) ^ b₁ * (-1 : K) ^ a₁ * quantumBinomial qᵢ a a₁ * hexp

private theorem quantumDividedPower_e_mul_simpleK (i j : ι) (n : ℕ) :
    quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n * simpleK D q j =
      (q ^ D.symmetrizer i) ^ (-(n : ℤ) * D.cartan i j) •
        (simpleK D q j * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) := by
  have h1 : e D q i * simpleK D q j =
      (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (simpleK D q j * e D q i) := by
    rw [e_mul_simpleK, ← zpow_natCast q, ← zpow_mul, mul_neg, ← D.symmetrizer_mul_cartan,
      ← mul_neg, zpow_mul, zpow_natCast]
  rw [quantumDividedPower_mul_of_mul_eq_smul_mul _ h1 n, ← zpow_natCast _ n, ← zpow_mul]
  congr 2
  ring

private theorem comul_serre_e_right_term {i j : ι} (hij : i ≠ j)
    (hqᵢ : q ^ D.symmetrizer i ≠ 0)
    (hfac : quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0)
    {a b₁ a₁ : ℕ} (ha : a ≤ D.serreLength i j) (hb₁ : b₁ ≤ D.serreLength i j - a)
    (ha₁ : a₁ ≤ a) :
    (-1 : K) ^ (a₁ + b₁) •
      (((q ^ D.symmetrizer i) ^ (a₁ * b₁) •
          ((quantumDividedPower (q ^ D.symmetrizer i) (e D q i) a₁ * simpleK D q i ^ b₁) ⊗ₜ[K]
            quantumDividedPower (q ^ D.symmetrizer i) (e D q i) b₁)) *
        (simpleK D q j ⊗ₜ[K] e D q j) *
        ((q ^ D.symmetrizer i) ^ ((a - a₁) * (D.serreLength i j - a - b₁)) •
          ((quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (a - a₁) *
              simpleK D q i ^ (D.serreLength i j - a - b₁)) ⊗ₜ[K]
            quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (D.serreLength i j - a - b₁)))) =
    ((-1 : K) ^ b₁ * (q ^ D.symmetrizer i) ^ (a * (D.serreLength i j - a - b₁) + 2 * b₁ * a) *
        ((-1 : K) ^ a₁ * (q ^ D.symmetrizer i) ^ ((a₁ : ℤ) * ((a : ℤ) - 1)) *
          quantumBinomial (q ^ D.symmetrizer i) a a₁)) •
      ((simpleK D q j * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) a *
          simpleK D q i ^ (D.serreLength i j - a)) ⊗ₜ[K]
        (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) b₁ * e D q j *
          quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (D.serreLength i j - a - b₁))) := by
  have hfac_a : quantumFactorial (q ^ D.symmetrizer i) (a₁ + (a - a₁)) ≠ 0 := by
    rw [Nat.add_sub_of_le ha₁]; exact quantumFactorial_ne_zero_of_le ha hfac
  have hk_edp :
      simpleK D q i ^ b₁ * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (a - a₁) =
        (q ^ D.symmetrizer i) ^ (2 * (b₁ : ℤ) * ((a - a₁ : ℕ) : ℤ)) •
          (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (a - a₁) * simpleK D q i ^ b₁) := by
    simpa only [D.cartan_apply_self, mul_comm ((b₁ : ℤ) * ((a - a₁ : ℕ) : ℤ)) 2, ← mul_assoc] using
      simpleK_pow_mul_quantumDividedPower_e D q (q ^ D.symmetrizer i) i i b₁ (a - a₁)
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul]
  have hword :
      (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) a₁ * simpleK D q i ^ b₁) *
          simpleK D q j *
          (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (a - a₁) *
            simpleK D q i ^ (D.serreLength i j - a - b₁)) =
        ((q ^ D.symmetrizer i) ^ (-(a₁ : ℤ) * D.cartan i j) *
          (q ^ D.symmetrizer i) ^ (2 * (b₁ : ℤ) * ((a - a₁ : ℕ) : ℤ)) *
          quantumBinomial (q ^ D.symmetrizer i) a a₁) •
          (simpleK D q j * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) a *
            simpleK D q i ^ (D.serreLength i j - a)) := by
    calc _ = (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) a₁ * simpleK D q j) *
              ((simpleK D q i ^ b₁ *
                quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (a - a₁)) *
                simpleK D q i ^ (D.serreLength i j - a - b₁)) := by
            rw [mul_assoc (quantumDividedPower _ (e D q i) a₁),
              ((commute_simpleK_simpleK D q i j).pow_left b₁).eq]
            simp only [mul_assoc]
      _ = _ := by
            rw [quantumDividedPower_e_mul_simpleK, hk_edp]
            simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
            rw [mul_assoc (quantumDividedPower _ (e D q i) (a - a₁)), ← pow_add,
              Nat.add_sub_of_le hb₁, ← mul_assoc (simpleK D q j * _),
              mul_assoc (simpleK D q j), quantumDividedPower_mul_quantumDividedPower _ hfac_a,
              Nat.add_sub_of_le ha₁]
            simp only [mul_smul_comm, smul_mul_assoc, smul_smul]
            congr 1
            ring
  rw [hword]
  simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul]
  rw [comul_serre_e_right_scalar D q hij hqᵢ ha hb₁ ha₁]

private theorem comul_serre_e_right {i j : ι} (hij : i ≠ j)
    (hfac : quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    ∑ r ∈ range (D.serreLength i j + 1), (-1 : K) ^ r •
      (quantumDividedPower (q ^ D.symmetrizer i) (comulElemE D q i) r *
        (simpleK D q j ⊗ₜ[K] e D q j) *
        quantumDividedPower (q ^ D.symmetrizer i) (comulElemE D q i)
          (D.serreLength i j - r)) = 0 := by
  have hqᵢ : q ^ D.symmetrizer i ≠ 0 := ne_zero_of_sub_inv_ne_zero
    (sub_inv_ne_zero_of_quantumFactorial_ne_zero (D.serreLength_ne_zero hij) hfac)
  rw [expand_serre_comulElemE D q hfac, sum_serre_reindex_right]
  refine sum_eq_zero fun a ha => ?_
  have ham : a ≤ D.serreLength i j := Nat.lt_succ_iff.mp (mem_range.mp ha)
  rcases eq_or_ne a 0 with rfl | ha₀
  · have ha0 : ∑ b₁ ∈ range (D.serreLength i j + 1),
        (-1 : K) ^ b₁ • ((simpleK D q j * simpleK D q i ^ D.serreLength i j) ⊗ₜ[K]
          (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) b₁ * e D q j *
            quantumDividedPower (q ^ D.symmetrizer i) (e D q i)
              (D.serreLength i j - b₁))) = 0 := by
      simp only [← TensorProduct.tmul_smul, ← TensorProduct.tmul_sum, ← serreSum_def,
        serreE_eq_zero D q hij, TensorProduct.tmul_zero]
    refine (sum_congr rfl fun b₁ hb₁ => ?_).trans ha0
    rw [sum_range_one]
    have hterm := comul_serre_e_right_term D q hij hqᵢ hfac (Nat.zero_le _)
      (Nat.lt_succ_iff.mp (mem_range.mp hb₁)) le_rfl
    simpa only [zero_add, Nat.sub_zero, Nat.cast_zero, zero_mul, mul_zero, pow_zero, zpow_zero,
      mul_one, one_mul, one_smul, quantumBinomial_zero_right, quantumDividedPower_zero] using hterm
  · refine sum_eq_zero fun b₁ hb₁ => ?_
    have hb₁m : b₁ ≤ D.serreLength i j - a := Nat.lt_succ_iff.mp (mem_range.mp hb₁)
    calc _ = ∑ a₁ ∈ range (a + 1),
          ((-1 : K) ^ b₁ *
              (q ^ D.symmetrizer i) ^ (a * (D.serreLength i j - a - b₁) + 2 * b₁ * a) *
            ((-1 : K) ^ a₁ * (q ^ D.symmetrizer i) ^ ((a₁ : ℤ) * ((a : ℤ) - 1)) *
              quantumBinomial (q ^ D.symmetrizer i) a a₁)) •
            ((simpleK D q j * quantumDividedPower (q ^ D.symmetrizer i) (e D q i) a *
                simpleK D q i ^ (D.serreLength i j - a)) ⊗ₜ[K]
              (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) b₁ * e D q j *
                quantumDividedPower (q ^ D.symmetrizer i) (e D q i)
                  (D.serreLength i j - a - b₁))) := by
          refine sum_congr rfl fun a₁ ha₁ => ?_
          have ha₁a : a₁ ≤ a := Nat.lt_succ_iff.mp (mem_range.mp ha₁)
          have hsub :
              D.serreLength i j - (a₁ + b₁) - (a - a₁) = D.serreLength i j - a - b₁ := by omega
          simpa only [Nat.add_sub_cancel_left, hsub] using
            comul_serre_e_right_term D q hij hqᵢ hfac ham hb₁m ha₁a
      _ = 0 := by
          rw [← sum_smul, ← mul_sum, sum_neg_one_pow_mul_zpow_mul_quantumBinomial hqᵢ ha₀,
            mul_zero, zero_smul]

private theorem comul_serre_e {i j : ι} (hij : i ≠ j)
    (hfac : quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    serreSum D q (comulElemE D q) i j = 0 := by
  have hsplit : serreSum D q (comulElemE D q) i j =
      (∑ r ∈ range (D.serreLength i j + 1), (-1 : K) ^ r •
        (quantumDividedPower (q ^ D.symmetrizer i) (comulElemE D q i) r *
          (e D q j ⊗ₜ[K] 1) *
          quantumDividedPower (q ^ D.symmetrizer i) (comulElemE D q i)
            (D.serreLength i j - r))) +
      (∑ r ∈ range (D.serreLength i j + 1), (-1 : K) ^ r •
        (quantumDividedPower (q ^ D.symmetrizer i) (comulElemE D q i) r *
          (simpleK D q j ⊗ₜ[K] e D q j) *
          quantumDividedPower (q ^ D.symmetrizer i) (comulElemE D q i)
            (D.serreLength i j - r))) := by
    rw [serreSum_def, ← sum_add_distrib]
    refine sum_congr rfl fun r _ => ?_
    simp only [comulElemE, mul_add, add_mul, smul_add]
  rw [hsplit, comul_serre_e_left D q hij hfac, comul_serre_e_right D q hij hfac, add_zero]

private theorem comul_serre_f {i j : ι} (hij : i ≠ j)
    (hfac : quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    serreSum D q (comulElemF D q) i j = 0 := by
  let U := QuantizedEnvelopingAlgebra D q
  let Φ : (U ⊗[K] U) →ₐ[K] (U ⊗[K] U) :=
    (Algebra.TensorProduct.map (chevalleyInvolution D q).toAlgHom
      (chevalleyInvolution D q).toAlgHom).comp (Algebra.TensorProduct.comm K U U).toAlgHom
  have hΦ : comulElemF D q = fun l => Φ (comulElemE D q l) := by
    ext l
    simp [Φ, comulElemE, comulElemF, simpleK_def, simpleKInv_def, add_comm]
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

/-- `Δ(Eᵢ) = Eᵢ ⊗ 1 + Kᵢ ⊗ Eᵢ`. -/
@[simp]
theorem comulAlgHom_e
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0)
    (i : ι) :
    comulAlgHom D q hserre (e D q i) = e D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] e D q i := by
  simp [comulAlgHom, comulTuple, comulElemE]

/-- `Δ(Fᵢ) = Fᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ Fᵢ`. -/
@[simp]
theorem comulAlgHom_f
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0)
    (i : ι) :
    comulAlgHom D q hserre (f D q i) = f D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] f D q i := by
  simp [comulAlgHom, comulTuple, comulElemF]

/-- `Δ(K_y) = K_y ⊗ K_y`. -/
@[simp]
theorem comulAlgHom_k
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0)
    (y : Y) :
    comulAlgHom D q hserre (k D q y) = k D q y ⊗ₜ[K] k D q y := by
  simp [comulAlgHom, comulTuple]

/-- `Δ(Kᵢ) = Kᵢ ⊗ Kᵢ`. -/
@[simp]
theorem comulAlgHom_simpleK
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0)
    (i : ι) :
    comulAlgHom D q hserre (simpleK D q i) = simpleK D q i ⊗ₜ[K] simpleK D q i := by
  simp [simpleK_def]

/-- `Δ(Kᵢ⁻¹) = Kᵢ⁻¹ ⊗ Kᵢ⁻¹`. -/
@[simp]
theorem comulAlgHom_simpleKInv
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0)
    (i : ι) :
    comulAlgHom D q hserre (simpleKInv D q i) = simpleKInv D q i ⊗ₜ[K] simpleKInv D q i := by
  simp [simpleKInv_def]

/-- `Δ(eᵢ) = eᵢ ⊗ Kᵢ⁻¹ + 1 ⊗ eᵢ` for the normalized raising generator `eᵢ = Kᵢ⁻¹ Eᵢ`. -/
@[simp]
theorem comulAlgHom_normalizedE
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0)
    (i : ι) :
    comulAlgHom D q hserre (normalizedE D q i) =
      normalizedE D q i ⊗ₜ[K] simpleKInv D q i + 1 ⊗ₜ[K] normalizedE D q i := by
  rw [normalizedE_def, map_mul, comulAlgHom_simpleKInv, comulAlgHom_e, mul_add,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    simpleKInv_mul_simpleK, ← normalizedE_def]

/-- `Δ(fᵢ) = fᵢ ⊗ 1 + Kᵢ ⊗ fᵢ` for the normalized lowering generator `fᵢ = Fᵢ Kᵢ`. -/
@[simp]
theorem comulAlgHom_normalizedF
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0)
    (i : ι) :
    comulAlgHom D q hserre (normalizedF D q i) =
      normalizedF D q i ⊗ₜ[K] 1 + simpleK D q i ⊗ₜ[K] normalizedF D q i := by
  rw [normalizedF_def, map_mul, comulAlgHom_f, comulAlgHom_simpleK, add_mul,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    simpleKInv_mul_simpleK, ← normalizedF_def]

/-- **Coproduct of raising divided powers**: when `[n]_(qᵢ)! ≠ 0`,
`Δ(Eᵢ^(n)) = ∑_{a=0}^n qᵢ^(a(n - a)) • ((Eᵢ^(a) Kᵢ^(n - a)) ⊗ Eᵢ^(n - a))`. -/
theorem comulAlgHom_quantumDividedPower_e
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0)
    {i : ι} {n : ℕ} (hn : quantumFactorial (q ^ D.symmetrizer i) n ≠ 0) :
    comulAlgHom D q hserre (quantumDividedPower (q ^ D.symmetrizer i) (e D q i) n) =
      ∑ a ∈ range (n + 1), (q ^ D.symmetrizer i) ^ (a * (n - a)) •
        ((quantumDividedPower (q ^ D.symmetrizer i) (e D q i) a * simpleK D q i ^ (n - a)) ⊗ₜ[K]
          quantumDividedPower (q ^ D.symmetrizer i) (e D q i) (n - a)) := by
  rw [map_quantumDividedPower, comulAlgHom_e, ← comulElemE, quantumDividedPower_comulElemE D q hn]

/-- **Coproduct of lowering divided powers**: when `[n]_(qᵢ)! ≠ 0`,
`Δ(Fᵢ^(n)) = ∑_{a=0}^n qᵢ^(a(n - a)) • (Fᵢ^(a) ⊗ (Fᵢ^(n - a) Kᵢ^(-a)))`. -/
theorem comulAlgHom_quantumDividedPower_f
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0)
    {i : ι} {n : ℕ} (hn : quantumFactorial (q ^ D.symmetrizer i) n ≠ 0) :
    comulAlgHom D q hserre (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) n) =
      ∑ a ∈ range (n + 1), (q ^ D.symmetrizer i) ^ (a * (n - a)) •
        (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) a ⊗ₜ[K]
          (quantumDividedPower (q ^ D.symmetrizer i) (f D q i) (n - a) *
            simpleKInv D q i ^ a)) := by
  rw [map_quantumDividedPower, comulAlgHom_f, ← comulElemF, quantumDividedPower_comulElemF D q hn]

end Coproduct

/-! ### Bialgebra, Hopf algebra, and functoriality -/

section BialgebraAndHopf

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
  (D : CartanDatum ι X Y) (q : K)

/-- Coassociativity of `comulAlgHom`: `(Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ`. -/
theorem comulAlgHom_coassoc
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    (Algebra.TensorProduct.assoc K K K
        (QuantizedEnvelopingAlgebra D q) (QuantizedEnvelopingAlgebra D q)
        (QuantizedEnvelopingAlgebra D q)).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulAlgHom D q hserre) (.id K _)).comp
        (comulAlgHom D q hserre)) =
      (Algebra.TensorProduct.map (.id K _) (comulAlgHom D q hserre)).comp
        (comulAlgHom D q hserre) := by
  apply hom_ext <;> intro x <;>
    simp [TensorProduct.tmul_add, TensorProduct.add_tmul, add_assoc,
      Algebra.TensorProduct.one_def]

/-- Left counit law `(ε ⊗ id) ∘ Δ = id`. -/
theorem counitAlgHom_comulAlgHom_left
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    (Algebra.TensorProduct.map (counitAlgHom D q) (.id K _)).comp (comulAlgHom D q hserre) =
      (Algebra.TensorProduct.lid K (QuantizedEnvelopingAlgebra D q)).symm.toAlgHom := by
  apply hom_ext <;> intro x <;> simp

/-- Right counit law `(id ⊗ ε) ∘ Δ = id`. -/
theorem counitAlgHom_comulAlgHom_right
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    (Algebra.TensorProduct.map (.id K _) (counitAlgHom D q)).comp (comulAlgHom D q hserre) =
      (Algebra.TensorProduct.rid K K (QuantizedEnvelopingAlgebra D q)).symm.toAlgHom := by
  apply hom_ext <;> intro x <;> simp

/-- The `Bialgebra` structure on `QuantizedEnvelopingAlgebra D q` defined by `comulAlgHom` and
`counitAlgHom`. -/
@[expose, instance_reducible]
noncomputable def bialgebra
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    Bialgebra K (QuantizedEnvelopingAlgebra D q) :=
  Bialgebra.ofAlgHom (comulAlgHom D q hserre) (counitAlgHom D q)
    (comulAlgHom_coassoc D q hserre) (counitAlgHom_comulAlgHom_left D q hserre)
    (counitAlgHom_comulAlgHom_right D q hserre)

/-- In `bialgebra D q hserre`, `Bialgebra.comulAlgHom` is `comulAlgHom D q hserre`. -/
@[simp]
theorem bialgebra_comulAlgHom
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    letI := bialgebra D q hserre
    Bialgebra.comulAlgHom K (QuantizedEnvelopingAlgebra D q) = comulAlgHom D q hserre :=
  letI := bialgebra D q hserre
  AlgHom.ext fun _ => rfl

/-- In `bialgebra D q hserre`, `Coalgebra.comul` is `(comulAlgHom D q hserre).toLinearMap`. -/
@[simp]
theorem bialgebra_comul
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    letI := bialgebra D q hserre
    Coalgebra.comul (R := K) (A := QuantizedEnvelopingAlgebra D q) =
      (comulAlgHom D q hserre).toLinearMap := (rfl)

/-- In `bialgebra D q hserre`, `Bialgebra.counitAlgHom` is `counitAlgHom D q`. -/
@[simp]
theorem bialgebra_counitAlgHom
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    letI := bialgebra D q hserre
    Bialgebra.counitAlgHom K (QuantizedEnvelopingAlgebra D q) = counitAlgHom D q :=
  letI := bialgebra D q hserre
  AlgHom.ext fun _ => rfl

/-- In `bialgebra D q hserre`, `Coalgebra.counit` is `(counitAlgHom D q).toLinearMap`. -/
@[simp]
theorem bialgebra_counit
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    letI := bialgebra D q hserre
    Coalgebra.counit (R := K) (A := QuantizedEnvelopingAlgebra D q) =
      (counitAlgHom D q).toLinearMap := (rfl)

/-- Every toral element `K_y` is group-like in `bialgebra D q hserre`. -/
theorem isGroupLikeElem_k
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0)
    (y : Y) :
    letI := bialgebra D q hserre
    IsGroupLikeElem K (k D q y) := by
  let := bialgebra D q hserre
  exact ⟨by simp [bialgebra_counit], by simp [bialgebra_comul]⟩

/-- The `HopfAlgebra` structure on `QuantizedEnvelopingAlgebra D q` extending `bialgebra D q hserre`
with antipode `antipodeLinearEquiv D q`. -/
@[expose, instance_reducible]
noncomputable def hopfAlgebra
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    HopfAlgebra K (QuantizedEnvelopingAlgebra D q) :=
  letI := bialgebra D q hserre
  HopfAlgebra.ofAntipodeOfAdjoin (antipodeOp D q) (adjoin_range_generator D q)
    (by
      rintro _ ⟨g, rfl⟩
      cases g with
      | e i => simp [generator_e, bialgebra_comul, bialgebra_counit]
      | f i => simp [generator_f, bialgebra_comul, bialgebra_counit, mul_assoc]
      | k y => simp [generator_k, bialgebra_comul, bialgebra_counit])
    (by
      rintro _ ⟨g, rfl⟩
      cases g with
      | e i =>
        simp [generator_e, bialgebra_comul, bialgebra_counit, simpleK_mul_simpleKInv_assoc]
      | f i => simp [generator_f, bialgebra_comul, bialgebra_counit]
      | k y => simp [generator_k, bialgebra_comul, bialgebra_counit])

/-- The underlying `Bialgebra` of `hopfAlgebra D q hserre` is `bialgebra D q hserre`. -/
@[simp]
theorem hopfAlgebra_toBialgebra
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    (hopfAlgebra D q hserre).toBialgebra = bialgebra D q hserre := (rfl)

/-- The antipode of `hopfAlgebra D q hserre` is `(antipodeLinearEquiv D q).toLinearMap`. -/
@[simp]
theorem hopfAlgebra_antipode
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    letI := hopfAlgebra D q hserre
    HopfAlgebraStruct.antipode K (A := QuantizedEnvelopingAlgebra D q) =
      (antipodeLinearEquiv D q).toLinearMap := by
  let := hopfAlgebra D q hserre
  ext x
  exact (antipodeLinearEquiv_apply D q x).symm

/-- The antipode of `hopfAlgebra D q hserre` is bijective. -/
theorem antipode_bijective
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    letI := hopfAlgebra D q hserre
    Function.Bijective
      (HopfAlgebraStruct.antipode K :
        QuantizedEnvelopingAlgebra D q →ₗ[K] QuantizedEnvelopingAlgebra D q) := by
  let := hopfAlgebra D q hserre
  rw [hopfAlgebra_antipode D q hserre]
  exact (antipodeLinearEquiv D q).bijective

/-- The antipode is a coalgebra anti-automorphism:
`Δ(S x) = (S ⊗ S)(swap (Δ x))`. -/
theorem comulAlgHom_antipodeLinearEquiv
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0)
    (x : QuantizedEnvelopingAlgebra D q) :
    comulAlgHom D q hserre (antipodeLinearEquiv D q x) =
      TensorProduct.map (antipodeLinearEquiv D q).toLinearMap
        (antipodeLinearEquiv D q).toLinearMap
        (TensorProduct.comm K _ _ (comulAlgHom D q hserre x)) := by
  let := hopfAlgebra D q hserre
  simpa only [hopfAlgebra_antipode D q hserre, hopfAlgebra_toBialgebra, bialgebra_comul,
    AlgHom.toLinearMap_apply, LinearEquiv.coe_coe] using
    TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply (R := K) x

/-- Existence and characterization of the bijective antipode on `bialgebra D q hserre`. -/
theorem exists_antipode
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
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

section Functoriality

variable {X' Y' : Type*} [AddCommGroup X'] [AddCommGroup Y']
  {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'}

/-- `map φ q` respects the counit: `ε ∘ map φ q = ε`. -/
@[simp]
theorem counitAlgHom_comp_map (φ : CartanDatum.Hom D D') (q : K) :
    (counitAlgHom D' q).comp (map φ q) = counitAlgHom D q := by
  apply hom_ext <;> intro x <;> simp

/-- `map φ q` respects the coproduct: `(map φ q ⊗ map φ q) ∘ Δ = Δ ∘ map φ q`. -/
theorem map_comp_comulAlgHom (φ : CartanDatum.Hom D D') (q : K)
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    (Algebra.TensorProduct.map (map φ q) (map φ q)).comp (comulAlgHom D q hserre) =
      (comulAlgHom D' q (fun i j hij => by
          simpa only [φ.symmetrizer_eq, φ.serreLength_eq] using hserre i j hij)).comp
        (map φ q) := by
  apply hom_ext <;> intro x <;> simp

/-- A morphism of Cartan data induces a bialgebra homomorphism between the corresponding quantized
enveloping algebras. -/
noncomputable def mapBialgHom (φ : CartanDatum.Hom D D') (q : K)
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    letI := bialgebra D q hserre
    letI := bialgebra D' q (fun i j hij => by
      simpa only [φ.symmetrizer_eq, φ.serreLength_eq] using hserre i j hij)
    QuantizedEnvelopingAlgebra D q →ₐc[K] QuantizedEnvelopingAlgebra D' q :=
  letI := bialgebra D q hserre
  letI := bialgebra D' q (fun i j hij => by
    simpa only [φ.symmetrizer_eq, φ.serreLength_eq] using hserre i j hij)
  BialgHom.ofAlgHom (map φ q)
    (by simpa only [bialgebra_counitAlgHom] using counitAlgHom_comp_map φ q)
    (by simpa only [bialgebra_comulAlgHom] using map_comp_comulAlgHom φ q hserre)

/-- The underlying `AlgHom` of `mapBialgHom φ q hserre` is `map φ q`. -/
@[simp]
theorem mapBialgHom_toAlgHom (φ : CartanDatum.Hom D D') (q : K)
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0) :
    letI := bialgebra D q hserre
    letI := bialgebra D' q (fun i j hij => by
      simpa only [φ.symmetrizer_eq, φ.serreLength_eq] using hserre i j hij)
    (mapBialgHom φ q hserre : QuantizedEnvelopingAlgebra D q →ₐ[K]
      QuantizedEnvelopingAlgebra D' q) = map φ q := (rfl)

/-- `mapBialgHom φ q hserre` agrees pointwise with `map φ q`. -/
@[simp]
theorem mapBialgHom_apply (φ : CartanDatum.Hom D D') (q : K)
    (hserre : ∀ i j, i ≠ j → quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0)
    (x : QuantizedEnvelopingAlgebra D q) :
    letI := bialgebra D q hserre
    letI := bialgebra D' q (fun i j hij => by
      simpa only [φ.symmetrizer_eq, φ.serreLength_eq] using hserre i j hij)
    mapBialgHom φ q hserre x = map φ q x := (rfl)

end Functoriality

end BialgebraAndHopf

end QuantizedEnvelopingAlgebra

end TauCeti
