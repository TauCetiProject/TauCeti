/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.RingQuot
public import TauCeti.LinearAlgebra.Matrix.Cartan.Datum.Hom
public import TauCeti.QuantumGroups.QuantumInteger.Factorial

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Drinfeld–Jimbo quantized enveloping algebra of a Cartan datum

Given a symmetrizable Cartan datum `D : CartanDatum ι X Y` (`TauCeti.CartanDatum`) and `q` in a
field `K`, this file defines `TauCeti.QuantizedEnvelopingAlgebra D q` by generators `Eᵢ`, `Fᵢ`
(`i : ι`) and `K_y` (`y : Y`) subject to:
* `K_0 = 1` and `K_y K_z = K_(y + z)`;
* `K_y Eᵢ K_(-y) = q^⟨αᵢ, y⟩ Eᵢ` and `K_y Fᵢ K_(-y) = q^(-⟨αᵢ, y⟩) Fᵢ`;
* `Eᵢ Fⱼ - Fⱼ Eᵢ = δᵢⱼ (Kᵢ - Kᵢ⁻¹) / (qᵢ - qᵢ⁻¹)` with `qᵢ = q^(dᵢ)` and `Kᵢ = K_(dᵢ hᵢ)`;
* for `i ≠ j`, `∑_{r + s = 1 - aᵢⱼ} (-1)^r Eᵢ^(r) Eⱼ Eᵢ^(s) = 0` and similarly for `F`, in
  `qᵢ`-divided powers.

Including `K_y` for every `y ∈ Y` retains central directions (`⟨αᵢ, c⟩ = 0` for all `i`) and
intermediate lattices, without finiteness, decidability, or freeness assumptions on `ι`, `X`, `Y`.
The quotient is defined for every `q : K` (forcing `Eᵢ = Fᵢ = 0` at `q = 0`).

## Main definitions and results

* `TauCeti.QuantizedEnvelopingAlgebra`, `Generator`, `Rel`: presentation and quotient algebra.
* `TauCeti.QuantizedEnvelopingAlgebra.e`, `f`, `k`, `simpleK`, `simpleKInv`, `normalizedE`,
  `normalizedF`, `kUnitsHom`: generators, normalized root operators, and toral units.
* `TauCeti.QuantizedEnvelopingAlgebra.serreSum`, `serreSum_add`: quantum Serre combinations and
  additivity on `q`-commuting families.
* `TauCeti.QuantizedEnvelopingAlgebra.GeneratorTuple`, `lift`, `liftEquiv`, `hom_ext`, `induction`:
  universal property and generator induction.
* `TauCeti.QuantizedEnvelopingAlgebra.rescale`, `chevalleyInvolution`, `map`: diagonal rescaling,
  Chevalley involution, and functoriality along `CartanDatum.Hom`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993, §3.1.
* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, AMS, 1996, Ch. 4.
* S. Lentner, *Quantum groups and Nichols algebras acting on conformal field theories*, Adv. Math.
  268 (2015), 247--316, Definition 3.2.
-/

public section

open Finset

namespace TauCeti

namespace QuantizedEnvelopingAlgebra

/-- The generator alphabet of a quantized enveloping algebra: raising generators `Eᵢ`, lowering
generators `Fᵢ`, and a toral generator `K_y` for every `y ∈ Y`. -/
inductive Generator (ι Y : Type*)
  | e (i : ι)
  | f (i : ι)
  | k (y : Y)

section SerreSum

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]

/-- Given `x : ι → A` in a `K`-algebra `A`, the quantum Serre combination
`∑_{r = 0}^{1 - aᵢⱼ} (-1)^r xᵢ^(r) xⱼ xᵢ^(1 - aᵢⱼ - r)` formed with `qᵢ`-divided powers. -/
noncomputable def serreSum {A : Type*} [Semiring A] [Algebra K A]
    (D : CartanDatum ι X Y) (q : K) (x : ι → A) (i j : ι) : A :=
  ∑ r ∈ range (D.serreLength i j + 1), (-1 : K) ^ r •
    (quantumDividedPower (q ^ D.symmetrizer i) (x i) r * x j *
      quantumDividedPower (q ^ D.symmetrizer i) (x i) (D.serreLength i j - r))

theorem serreSum_def {A : Type*} [Semiring A] [Algebra K A]
    (D : CartanDatum ι X Y) (q : K) (x : ι → A) (i j : ι) :
    serreSum D q x i j = ∑ r ∈ range (D.serreLength i j + 1), (-1 : K) ^ r •
      (quantumDividedPower (q ^ D.symmetrizer i) (x i) r * x j *
        quantumDividedPower (q ^ D.symmetrizer i) (x i) (D.serreLength i j - r)) := (rfl)

@[simp] theorem map_serreSum {A B F : Type*} [Semiring A] [Algebra K A] [Semiring B] [Algebra K B]
    [FunLike F A B] [AlgHomClass F K A B] (φ : F)
    (D : CartanDatum ι X Y) (q : K) (x : ι → A) (i j : ι) :
    φ (serreSum D q x i j) = serreSum D q (fun l => φ (x l)) i j := by
  simp [serreSum_def]

/-- Scaling the family `x` by `c` scales `serreSum D q x i j` by `cᵢ^(1 - aᵢⱼ) * cⱼ`. -/
theorem serreSum_smul {A : Type*} [Semiring A] [Algebra K A]
    (D : CartanDatum ι X Y) (q : K) (c : ι → K) (x : ι → A) (i j : ι) :
    serreSum D q (fun l => c l • x l) i j =
      (c i ^ D.serreLength i j * c j) • serreSum D q x i j := by
  rw [serreSum_def, serreSum_def, smul_sum]
  refine sum_congr rfl fun r hr => ?_
  have hrm : r ≤ D.serreLength i j := Nat.lt_succ_iff.mp (mem_range.mp hr)
  simp only [quantumDividedPower_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  rw [mul_comm (c j), ← mul_assoc (c i ^ _), ← pow_add, Nat.sub_add_cancel hrm]
  ring

private theorem serreSum_add_left_term {A : Type*} [Ring A] [Algebra K A]
    (D : CartanDatum ι X Y) (q : K) {x y : ι → A} {i j : ι} (hij : i ≠ j)
    (hqᵢ : q ^ D.symmetrizer i ≠ 0)
    (hfac : quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0)
    (hyx : y i * x i = (q ^ D.symmetrizer i) ^ 2 • (x i * y i)) {z : A}
    (hyz : y i * z = (q ^ D.symmetrizer i) ^ D.cartan i j • (z * y i))
    {b a₁ b₁ : ℕ} (hbm : b ≤ D.serreLength i j) (ha₁ : a₁ ≤ D.serreLength i j - b)
    (hb₁ : b₁ ≤ b) :
    (-1 : K) ^ (a₁ + b₁) • (((q ^ D.symmetrizer i) ^ (a₁ * b₁) •
      (quantumDividedPower (q ^ D.symmetrizer i) (x i) a₁ *
        quantumDividedPower (q ^ D.symmetrizer i) (y i) b₁)) * z *
      ((q ^ D.symmetrizer i) ^ ((D.serreLength i j - b - a₁) * (b - b₁)) •
        (quantumDividedPower (q ^ D.symmetrizer i) (x i) (D.serreLength i j - b - a₁) *
          quantumDividedPower (q ^ D.symmetrizer i) (y i) (b - b₁)))) =
    ((-1 : K) ^ a₁ * (q ^ D.symmetrizer i) ^ ((D.serreLength i j - b - a₁) * b) *
      ((-1 : K) ^ b₁ * (q ^ D.symmetrizer i) ^ ((b₁ : ℤ) * (1 - (b : ℤ))) *
        quantumBinomial (q ^ D.symmetrizer i) b b₁)) •
      (quantumDividedPower (q ^ D.symmetrizer i) (x i) a₁ * z *
        quantumDividedPower (q ^ D.symmetrizer i) (x i) (D.serreLength i j - b - a₁) *
        quantumDividedPower (q ^ D.symmetrizer i) (y i) b) := by
  set m := D.serreLength i j; set qᵢ := q ^ D.symmetrizer i; set a₂ := m - b - a₁
  have hfac_b : quantumFactorial qᵢ (b₁ + (b - b₁)) ≠ 0 := by
    rw [Nat.add_sub_of_le hb₁]; exact quantumFactorial_ne_zero_of_le hbm hfac
  -- Commute `yᵢ^(b₁)` past `z` and `xᵢ^(a₂)` and combine divided powers of `yᵢ`.
  have hyx_dp : quantumDividedPower qᵢ (y i) b₁ * quantumDividedPower qᵢ (x i) a₂ =
      (qᵢ ^ (2 * a₂)) ^ b₁ •
        (quantumDividedPower qᵢ (x i) a₂ * quantumDividedPower qᵢ (y i) b₁) := by
    have h1 : y i * quantumDividedPower qᵢ (x i) a₂ =
        qᵢ ^ (2 * a₂) • (quantumDividedPower qᵢ (x i) a₂ * y i) := by
      rw [mul_quantumDividedPower_of_mul_eq_smul_mul qᵢ hyx a₂, pow_mul]
    exact quantumDividedPower_mul_of_mul_eq_smul_mul qᵢ h1 b₁
  have hyz_dp := quantumDividedPower_mul_of_mul_eq_smul_mul qᵢ hyz b₁
  simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
  rw [← mul_assoc (quantumDividedPower qᵢ (y i) b₁) z, hyz_dp]
  simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
  rw [← mul_assoc (quantumDividedPower qᵢ (y i) b₁), hyx_dp]
  simp only [smul_mul_assoc, mul_smul_comm, mul_assoc,
    quantumDividedPower_mul_quantumDividedPower _ hfac_b, Nat.add_sub_of_le hb₁, smul_smul]
  simp only [← mul_assoc]; congr 1
  have hcart : D.cartan i j = 1 - (m : ℤ) := by have := D.natCast_serreLength hij; omega
  have hm_eq : (m : ℤ) = (a₁ : ℤ) + (a₂ : ℤ) + (b : ℤ) := by omega
  have hb_eq : ((b - b₁ : ℕ) : ℤ) = (b : ℤ) - (b₁ : ℤ) := by omega
  have hq_exp : qᵢ ^ (a₁ * b₁) * qᵢ ^ (a₂ * (b - b₁)) * (qᵢ ^ D.cartan i j) ^ b₁ *
      (qᵢ ^ (2 * a₂)) ^ b₁ = qᵢ ^ (a₂ * b) * qᵢ ^ ((b₁ : ℤ) * (1 - (b : ℤ))) := by
    simp only [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hqᵢ]
    congr 1; push_cast; rw [hcart, hm_eq, hb_eq]; ring
  rw [pow_add (-1 : K)]
  linear_combination (-1 : K) ^ a₁ * (-1 : K) ^ b₁ * quantumBinomial qᵢ b b₁ * hq_exp

private theorem serreSum_add_left {A : Type*} [Ring A] [Algebra K A]
    (D : CartanDatum ι X Y) (q : K) {x y : ι → A} {i j : ι} (hij : i ≠ j)
    (hfac : quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0)
    (hyx : y i * x i = (q ^ D.symmetrizer i) ^ 2 • (x i * y i)) {z : A}
    (hyz : y i * z = (q ^ D.symmetrizer i) ^ D.cartan i j • (z * y i))
    (hxz : ∑ r ∈ range (D.serreLength i j + 1), (-1 : K) ^ r •
      (quantumDividedPower (q ^ D.symmetrizer i) (x i) r * z *
        quantumDividedPower (q ^ D.symmetrizer i) (x i) (D.serreLength i j - r)) = 0) :
    ∑ r ∈ range (D.serreLength i j + 1), (-1 : K) ^ r •
      (quantumDividedPower (q ^ D.symmetrizer i) (x i + y i) r * z *
        quantumDividedPower (q ^ D.symmetrizer i) (x i + y i) (D.serreLength i j - r)) = 0 := by
  set m := D.serreLength i j; set qᵢ := q ^ D.symmetrizer i
  have hqᵢ : qᵢ ≠ 0 := ne_zero_of_sub_inv_ne_zero
    (sub_inv_ne_zero_of_quantumFactorial_ne_zero (D.serreLength_ne_zero hij) hfac)
  let F (r a₁ a₂ : ℕ) : A := (-1 : K) ^ r • ((qᵢ ^ (a₁ * (r - a₁)) •
    (quantumDividedPower qᵢ (x i) a₁ * quantumDividedPower qᵢ (y i) (r - a₁))) * z *
    (qᵢ ^ (a₂ * (m - r - a₂)) •
      (quantumDividedPower qᵢ (x i) a₂ * quantumDividedPower qᵢ (y i) (m - r - a₂))))
  have hexp : ∑ r ∈ range (m + 1), (-1 : K) ^ r •
      (quantumDividedPower qᵢ (x i + y i) r * z * quantumDividedPower qᵢ (x i + y i) (m - r)) =
      ∑ b ∈ range (m + 1), ∑ a₁ ∈ range (m - b + 1), ∑ b₁ ∈ range (b + 1),
        F (a₁ + b₁) a₁ (m - b - a₁) := by
    calc _ = ∑ r ∈ range (m + 1), ∑ a₁ ∈ range (r + 1), ∑ a₂ ∈ range (m - r + 1), F r a₁ a₂ :=
          sum_congr rfl fun r hr => by
            have hrm : r ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hr)
            rw [quantumDividedPower_add hyx (quantumFactorial_ne_zero_of_le hrm hfac),
              quantumDividedPower_add hyx (quantumFactorial_ne_zero_of_le (Nat.sub_le m r) hfac),
              sum_mul, sum_mul, smul_sum]
            exact sum_congr rfl fun _ _ => by rw [mul_sum, smul_sum]
      _ = _ := by
        simp only [sum_sigma']
        refine Finset.sum_nbij' (fun ⟨r, a₁, a₂⟩ => ⟨(r - a₁) + (m - r - a₂), a₁, r - a₁⟩)
          (fun ⟨b, a₁, b₁⟩ => ⟨a₁ + b₁, a₁, m - b - a₁⟩) ?_ ?_ ?_ ?_ ?_ <;>
          rintro ⟨_, _, _⟩ h <;> simp only [mem_sigma, mem_range] at h ⊢
        · omega
        · omega
        · exact Sigma.ext (by dsimp; omega) (heq_of_eq <| Sigma.ext rfl (by dsimp; congr 1; omega))
        · exact Sigma.ext (by dsimp; omega) (heq_of_eq <| Sigma.ext rfl (by dsimp; congr 1; omega))
        · congr 1 <;> omega
  rw [hexp]
  refine sum_eq_zero fun b hb => ?_
  have hbm : b ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hb)
  rcases eq_or_ne b 0 with rfl | hb₀
  · exact (sum_congr rfl fun a₁ _ => by simp [F]).trans hxz
  · refine sum_eq_zero fun a₁ ha₁ => ?_
    have ha₁m : a₁ ≤ m - b := Nat.lt_succ_iff.mp (mem_range.mp ha₁)
    have hsum : ∑ b₁ ∈ range (b + 1), F (a₁ + b₁) a₁ (m - b - a₁) =
        ∑ b₁ ∈ range (b + 1), ((-1 : K) ^ a₁ * qᵢ ^ ((m - b - a₁) * b) *
          ((-1 : K) ^ b₁ * qᵢ ^ ((b₁ : ℤ) * (1 - (b : ℤ))) * quantumBinomial qᵢ b b₁)) •
          (quantumDividedPower qᵢ (x i) a₁ * z *
            quantumDividedPower qᵢ (x i) (m - b - a₁) * quantumDividedPower qᵢ (y i) b) :=
      sum_congr rfl fun b₁ hb₁ => by
        have hb₁b : b₁ ≤ b := Nat.lt_succ_iff.mp (mem_range.mp hb₁)
        have hsub : m - (a₁ + b₁) - (m - b - a₁) = b - b₁ := by omega
        simpa only [F, Nat.add_sub_cancel_left, hsub] using
          serreSum_add_left_term D q hij hqᵢ hfac hyx hyz hbm ha₁m hb₁b
    rw [hsum, ← sum_smul, ← mul_sum,
      sum_neg_one_pow_mul_zpow_one_sub_mul_quantumBinomial hqᵢ hb₀, mul_zero, zero_smul]

/-- Evaluating `MulOpposite.unop` on the opposite-algebra quantum Serre combination reverses the
sum and multiplies by the sign factor `(-1)^(D.serreLength i j)` (equal to `(-1)^(1 - aᵢⱼ)` for
`i ≠ j`). -/
theorem unop_serreSum {A : Type*} [Semiring A] [Algebra K A]
    (D : CartanDatum ι X Y) (q : K) (u : ι → A) (i j : ι) :
    MulOpposite.unop (serreSum D q (fun l => MulOpposite.op (u l)) i j) =
      (-1 : K) ^ D.serreLength i j • serreSum D q u i j :=
  unop_sum_neg_one_pow_smul_quantumDividedPower_mul_mul _ _ (u i) (u j)

/-- **Additivity of quantum Serre combinations** on `q`-commuting families: if `yᵢ xᵢ = qᵢ² xᵢ yᵢ`,
`yᵢ xⱼ = qᵢ^(aᵢⱼ) xⱼ yᵢ`, `xᵢ yⱼ = qᵢ^(-aᵢⱼ) yⱼ xᵢ`, and `[1 - aᵢⱼ]_(qᵢ)! ≠ 0`, then
`serreSum D q x i j = 0` and `serreSum D q y i j = 0` imply `serreSum D q (x + y) i j = 0`. -/
theorem serreSum_add {A : Type*} [Ring A] [Algebra K A]
    (D : CartanDatum ι X Y) (q : K) {x y : ι → A} {i j : ι} (hij : i ≠ j)
    (hfac : quantumFactorial (q ^ D.symmetrizer i) (D.serreLength i j) ≠ 0)
    (hyx : y i * x i = (q ^ D.symmetrizer i) ^ 2 • (x i * y i))
    (hyxj : y i * x j = (q ^ D.symmetrizer i) ^ D.cartan i j • (x j * y i))
    (hxyj : x i * y j = (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (y j * x i))
    (hx : serreSum D q x i j = 0) (hy : serreSum D q y i j = 0) :
    serreSum D q (fun l => x l + y l) i j = 0 := by
  have hqᵢ : q ^ D.symmetrizer i ≠ 0 := ne_zero_of_sub_inv_ne_zero
    (sub_inv_ne_zero_of_quantumFactorial_ne_zero (D.serreLength_ne_zero hij) hfac)
  have hleft := serreSum_add_left D q hij hfac hyx hyxj hx
  -- Deduce the `yⱼ` summand by applying `serreSum_add_left` in `Aᵐᵒᵖ`.
  have hop_yx : MulOpposite.op (x i) * MulOpposite.op (y i) =
      (q ^ D.symmetrizer i) ^ 2 • (MulOpposite.op (y i) * MulOpposite.op (x i)) := by
    simpa only [← MulOpposite.op_mul, MulOpposite.op_smul] using congrArg MulOpposite.op hyx
  have hop_yz : MulOpposite.op (x i) * MulOpposite.op (y j) =
      (q ^ D.symmetrizer i) ^ D.cartan i j • (MulOpposite.op (y j) * MulOpposite.op (x i)) := by
    have hyjx : y j * x i = (q ^ D.symmetrizer i) ^ D.cartan i j • (x i * y j) := by
      rw [hxyj, smul_smul, ← zpow_add₀ hqᵢ, add_neg_cancel, zpow_zero, one_smul]
    simpa only [← MulOpposite.op_mul, MulOpposite.op_smul] using congrArg MulOpposite.op hyjx
  have hop_hy : serreSum D q (fun l => MulOpposite.op (y l)) i j = 0 :=
    MulOpposite.unop_injective <| by rw [unop_serreSum, hy, smul_zero, MulOpposite.unop_zero]
  have hop_right := congrArg MulOpposite.unop <| serreSum_add_left D q
    (x := fun l => MulOpposite.op (y l)) (y := fun l => MulOpposite.op (x l))
    hij hfac hop_yx hop_yz hop_hy
  simp only [← MulOpposite.op_add, add_comm (y i) (x i),
    unop_sum_neg_one_pow_smul_quantumDividedPower_mul_mul, MulOpposite.unop_zero] at hop_right
  have hright := (smul_eq_zero.mp hop_right).resolve_left
    (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  rw [serreSum_def]
  simp_rw [mul_add, add_mul, smul_add, sum_add_distrib]
  rw [hleft, hright, add_zero]

/-- When `aᵢⱼ = 0` and `qᵢ - qᵢ⁻¹ ≠ 0`, vanishing of the quantum Serre combination
`serreSum D q x i j` implies that `x i` and `x j` commute. -/
theorem commute_of_serreSum_eq_zero {A : Type*} [Ring A] [Algebra K A]
    (D : CartanDatum ι X Y) (q : K) {x : ι → A} {i j : ι} (hcartan : D.cartan i j = 0)
    (hq : q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹ ≠ 0) (h : serreSum D q x i j = 0) :
    Commute (x i) (x j) := by
  rw [serreSum_def, D.serreLength_of_cartan_eq_zero hcartan, sum_range_succ, sum_range_one] at h
  simp only [pow_zero, pow_one, one_smul, neg_one_smul, Nat.sub_zero, Nat.sub_self,
    quantumDividedPower_zero, quantumDividedPower_one hq, one_mul, mul_one,
    ← sub_eq_add_neg] at h
  exact (sub_eq_zero.mp h).symm

/-- The defining relations of the Drinfeld–Jimbo quantized enveloping algebra on
`FreeAlgebra K (Generator ι Y)`. Splitting diagonal and off-diagonal commutators avoids requiring
`DecidableEq ι`. -/
inductive Rel (D : CartanDatum ι X Y) (q : K) :
    FreeAlgebra K (Generator ι Y) → FreeAlgebra K (Generator ι Y) → Prop
  | k_zero : Rel D q (FreeAlgebra.ι K (.k 0)) 1
  | k_mul_k (y z : Y) :
      Rel D q (FreeAlgebra.ι K (.k y) * FreeAlgebra.ι K (.k z)) (FreeAlgebra.ι K (.k (y + z)))
  | conjugate_e (y : Y) (i : ι) :
      Rel D q (FreeAlgebra.ι K (.k y) * FreeAlgebra.ι K (.e i) * FreeAlgebra.ι K (.k (-y)))
        (q ^ D.pairing (D.root i) y • FreeAlgebra.ι K (.e i))
  | conjugate_f (y : Y) (i : ι) :
      Rel D q (FreeAlgebra.ι K (.k y) * FreeAlgebra.ι K (.f i) * FreeAlgebra.ι K (.k (-y)))
        (q ^ (-D.pairing (D.root i) y) • FreeAlgebra.ι K (.f i))
  | commutator_self (i : ι) :
      Rel D q
        (FreeAlgebra.ι K (.e i) * FreeAlgebra.ι K (.f i) -
          FreeAlgebra.ι K (.f i) * FreeAlgebra.ι K (.e i))
        ((q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
          (FreeAlgebra.ι K (.k (D.simpleTorus i)) - FreeAlgebra.ι K (.k (-D.simpleTorus i))))
  | commutator_ne {i j : ι} (hij : i ≠ j) :
      Rel D q
        (FreeAlgebra.ι K (.e i) * FreeAlgebra.ι K (.f j) -
          FreeAlgebra.ι K (.f j) * FreeAlgebra.ι K (.e i)) 0
  | serre_e {i j : ι} (hij : i ≠ j) :
      Rel D q (serreSum D q (fun l => FreeAlgebra.ι K (.e l)) i j) 0
  | serre_f {i j : ι} (hij : i ≠ j) :
      Rel D q (serreSum D q (fun l => FreeAlgebra.ι K (.f l)) i j) 0

end SerreSum

end QuantizedEnvelopingAlgebra

/-- The Drinfeld–Jimbo quantized enveloping algebra `U_q(D)` associated to a symmetrizable Cartan
datum `D : CartanDatum ι X Y` and parameter `q : K`, defined as `RingQuot` of the free algebra by
`QuantizedEnvelopingAlgebra.Rel D q`. -/
def QuantizedEnvelopingAlgebra {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
    (D : CartanDatum ι X Y) (q : K) : Type _ :=
  RingQuot (QuantizedEnvelopingAlgebra.Rel D q)

namespace QuantizedEnvelopingAlgebra

section Presentation

variable {ι X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [Field K]
  (D : CartanDatum ι X Y) (q : K)

noncomputable instance : Ring (QuantizedEnvelopingAlgebra D q) :=
  inferInstanceAs (Ring (RingQuot (Rel D q)))
noncomputable instance : Algebra K (QuantizedEnvelopingAlgebra D q) :=
  inferInstanceAs (Algebra K (RingQuot (Rel D q)))
noncomputable instance : Inhabited (QuantizedEnvelopingAlgebra D q) := ⟨0⟩

/-- The quotient algebra map from the free algebra onto `QuantizedEnvelopingAlgebra D q`. -/
noncomputable def mkAlgHom : FreeAlgebra K (Generator ι Y) →ₐ[K] QuantizedEnvelopingAlgebra D q :=
  RingQuot.mkAlgHom K (Rel D q)
theorem mkAlgHom_surjective : Function.Surjective (mkAlgHom D q) :=
  RingQuot.mkAlgHom_surjective K (Rel D q)
private theorem mkAlgHom_eq_of_rel {a b : FreeAlgebra K (Generator ι Y)} (h : Rel D q a b) :
    mkAlgHom D q a = mkAlgHom D q b := RingQuot.mkAlgHom_rel K h

/-- The image in `QuantizedEnvelopingAlgebra D q` of a generator in `Generator ι Y`. -/
noncomputable def generator (g : Generator ι Y) : QuantizedEnvelopingAlgebra D q :=
  mkAlgHom D q (FreeAlgebra.ι K g)
@[simp] theorem mkAlgHom_ι (g : Generator ι Y) :
    mkAlgHom D q (FreeAlgebra.ι K g) = generator D q g := (rfl)

/-- The raising generator `Eᵢ` of `QuantizedEnvelopingAlgebra D q`. -/
noncomputable def e (i : ι) : QuantizedEnvelopingAlgebra D q := generator D q (.e i)
/-- The lowering generator `Fᵢ` of `QuantizedEnvelopingAlgebra D q`. -/
noncomputable def f (i : ι) : QuantizedEnvelopingAlgebra D q := generator D q (.f i)
/-- The toral generator `K_y` (`y ∈ Y`) of `QuantizedEnvelopingAlgebra D q`. -/
noncomputable def k (y : Y) : QuantizedEnvelopingAlgebra D q := generator D q (.k y)
/-- The simple toral generator `Kᵢ = K_(dᵢ hᵢ)`. -/
noncomputable def simpleK (i : ι) : QuantizedEnvelopingAlgebra D q := k D q (D.simpleTorus i)
/-- The inverse simple toral generator `Kᵢ⁻¹ = K_(-dᵢ hᵢ)`. -/
noncomputable def simpleKInv (i : ι) : QuantizedEnvelopingAlgebra D q := k D q (-D.simpleTorus i)
/-- The normalized raising operator `eᵢ = Kᵢ⁻¹ Eᵢ`. -/
noncomputable def normalizedE (i : ι) : QuantizedEnvelopingAlgebra D q :=
  simpleKInv D q i * e D q i
/-- The normalized lowering operator `fᵢ = Fᵢ Kᵢ`. -/
noncomputable def normalizedF (i : ι) : QuantizedEnvelopingAlgebra D q :=
  f D q i * simpleK D q i

theorem e_def (i : ι) : e D q i = generator D q (.e i) := (rfl)
theorem f_def (i : ι) : f D q i = generator D q (.f i) := (rfl)
theorem k_def (y : Y) : k D q y = generator D q (.k y) := (rfl)
theorem simpleK_def (i : ι) : simpleK D q i = k D q (D.simpleTorus i) := (rfl)
theorem simpleKInv_def (i : ι) : simpleKInv D q i = k D q (-D.simpleTorus i) := (rfl)
theorem normalizedE_def (i : ι) : normalizedE D q i = simpleKInv D q i * e D q i := (rfl)
theorem normalizedF_def (i : ι) : normalizedF D q i = f D q i * simpleK D q i := (rfl)
@[simp] theorem generator_e (i : ι) : generator D q (.e i) = e D q i := (rfl)
@[simp] theorem generator_f (i : ι) : generator D q (.f i) = f D q i := (rfl)
@[simp] theorem generator_k (y : Y) : generator D q (.k y) = k D q y := (rfl)

/-! ### Toral group structure -/

@[simp] theorem k_zero : k D q 0 = 1 := by simpa using mkAlgHom_eq_of_rel D q Rel.k_zero
@[simp] theorem k_mul_k (y z : Y) : k D q y * k D q z = k D q (y + z) := by
  simpa using mkAlgHom_eq_of_rel D q (Rel.k_mul_k y z)
@[simp] theorem k_mul_k_assoc (y z : Y) (x : QuantizedEnvelopingAlgebra D q) :
    k D q y * (k D q z * x) = k D q (y + z) * x := by rw [← mul_assoc, k_mul_k]
theorem k_add (y z : Y) : k D q (y + z) = k D q y * k D q z := (k_mul_k D q y z).symm
theorem k_mul_k_neg (y : Y) : k D q y * k D q (-y) = 1 := by simp
theorem k_neg_mul_k (y : Y) : k D q (-y) * k D q y = 1 := by simp

/-- Any two toral generators commute. -/
theorem commute_k_k (y z : Y) : Commute (k D q y) (k D q z) := by
  rw [Commute, SemiconjBy, k_mul_k, k_mul_k, add_comm]

@[simp] theorem simpleK_mul_simpleKInv (i : ι) : simpleK D q i * simpleKInv D q i = 1 := by
  simp [simpleK_def, simpleKInv_def]
@[simp] theorem simpleKInv_mul_simpleK (i : ι) : simpleKInv D q i * simpleK D q i = 1 := by
  simp [simpleK_def, simpleKInv_def]
@[simp] theorem simpleK_mul_simpleKInv_assoc (i : ι) (x : QuantizedEnvelopingAlgebra D q) :
    simpleK D q i * (simpleKInv D q i * x) = x := by
  rw [← mul_assoc, simpleK_mul_simpleKInv, one_mul]
@[simp] theorem simpleKInv_mul_simpleK_assoc (i : ι) (x : QuantizedEnvelopingAlgebra D q) :
    simpleKInv D q i * (simpleK D q i * x) = x := by
  rw [← mul_assoc, simpleKInv_mul_simpleK, one_mul]

/-- The group homomorphism `Multiplicative Y →* (QuantizedEnvelopingAlgebra D q)ˣ` sending
`ofAdd y` to the unit `K_y` with inverse `K_(-y)`. -/
noncomputable def kUnitsHom : Multiplicative Y →* (QuantizedEnvelopingAlgebra D q)ˣ where
  toFun y := ⟨k D q y.toAdd, k D q (-y.toAdd), k_mul_k_neg D q y.toAdd, k_neg_mul_k D q y.toAdd⟩
  map_one' := Units.ext (k_zero D q)
  map_mul' y z := Units.ext (k_add D q y.toAdd z.toAdd)

@[simp] theorem val_kUnitsHom (y : Y) :
    ((kUnitsHom D q (.ofAdd y) : (QuantizedEnvelopingAlgebra D q)ˣ) :
      QuantizedEnvelopingAlgebra D q) = k D q y := (rfl)
@[simp] theorem val_inv_kUnitsHom (y : Y) :
    (((kUnitsHom D q (.ofAdd y))⁻¹ : (QuantizedEnvelopingAlgebra D q)ˣ) :
      QuantizedEnvelopingAlgebra D q) = k D q (-y) := (rfl)
theorem isUnit_k (y : Y) : IsUnit (k D q y) := ⟨kUnitsHom D q (.ofAdd y), rfl⟩
@[simp] theorem k_pow (y : Y) (n : ℕ) : k D q y ^ n = k D q (n • y) := by
  have h := congrArg Units.val ((kUnitsHom D q).map_pow (.ofAdd y) n)
  simpa only [Units.val_pow_eq_pow_val, val_kUnitsHom, ← ofAdd_nsmul] using h.symm
theorem simpleK_pow (i : ι) (n : ℕ) : simpleK D q i ^ n = k D q (n • D.simpleTorus i) := by
  rw [simpleK_def, k_pow]
theorem simpleKInv_pow (i : ι) (n : ℕ) :
    simpleKInv D q i ^ n = k D q (-(n • D.simpleTorus i)) := by rw [simpleKInv_def, k_pow, smul_neg]

/-! ### Toral conjugation and commutation -/

theorem k_mul_e_mul_k_neg (y : Y) (i : ι) :
    k D q y * e D q i * k D q (-y) = q ^ D.pairing (D.root i) y • e D q i := by
  simpa using mkAlgHom_eq_of_rel D q (Rel.conjugate_e y i)
theorem k_mul_f_mul_k_neg (y : Y) (i : ι) :
    k D q y * f D q i * k D q (-y) = q ^ (-D.pairing (D.root i) y) • f D q i := by
  simpa using mkAlgHom_eq_of_rel D q (Rel.conjugate_f y i)

/-- At `q = 0`, every raising generator `Eᵢ` and lowering generator `Fᵢ` vanishes. -/
@[simp] theorem e_zero (i : ι) : e D (0 : K) i = 0 := by
  have h := congrArg (fun x => k D (0 : K) (-D.coroot i) * x * k D (0 : K) (D.coroot i))
    (k_mul_e_mul_k_neg D (0 : K) (D.coroot i) i)
  simpa [D.pairing_root_coroot_self, mul_assoc, ← mul_assoc (k D (0 : K) (-D.coroot i))] using h
@[simp] theorem f_zero (i : ι) : f D (0 : K) i = 0 := by
  have h := congrArg (fun x => k D (0 : K) (D.coroot i) * x * k D (0 : K) (-D.coroot i))
    (k_mul_f_mul_k_neg D (0 : K) (-D.coroot i) i)
  simpa [D.pairing_root_coroot_self, mul_assoc, ← mul_assoc (k D (0 : K) (D.coroot i))] using h

theorem k_mul_e (y : Y) (i : ι) :
    k D q y * e D q i = q ^ D.pairing (D.root i) y • (e D q i * k D q y) := by
  rw [← smul_mul_assoc, ← k_mul_e_mul_k_neg, mul_assoc, mul_assoc, k_neg_mul_k, mul_one]
theorem k_mul_f (y : Y) (i : ι) :
    k D q y * f D q i = q ^ (-D.pairing (D.root i) y) • (f D q i * k D q y) := by
  rw [← smul_mul_assoc, ← k_mul_f_mul_k_neg, mul_assoc, mul_assoc, k_neg_mul_k, mul_one]
theorem e_mul_k (y : Y) (i : ι) :
    e D q i * k D q y = q ^ (-D.pairing (D.root i) y) • (k D q y * e D q i) := by
  rw [← mul_smul_comm, ← map_neg (D.pairing (D.root i)), ← k_mul_e_mul_k_neg D q (-y) i, neg_neg,
    ← mul_assoc, ← mul_assoc, k_mul_k_neg, one_mul]
theorem f_mul_k (y : Y) (i : ι) :
    f D q i * k D q y = q ^ D.pairing (D.root i) y • (k D q y * f D q i) := by
  rw [← mul_smul_comm, ← neg_neg (D.pairing (D.root i) y), ← map_neg (D.pairing (D.root i)),
    ← k_mul_f_mul_k_neg D q (-y) i, neg_neg, ← mul_assoc, ← mul_assoc, k_mul_k_neg, one_mul]

/-- Symmetrizability in exponent form: `qᵢ^(aᵢⱼ) = qⱼ^(aⱼᵢ)`. -/
theorem zpow_symmetrizer_cartan_comm (i j : ι) :
    (q ^ D.symmetrizer i) ^ D.cartan i j = (q ^ D.symmetrizer j) ^ D.cartan j i := by
  simp only [← zpow_natCast, ← zpow_mul, D.symmetrizer_mul_cartan]

private theorem zpow_pairing_simpleTorus (i j : ι) :
    q ^ D.pairing (D.root j) (D.simpleTorus i) = (q ^ D.symmetrizer i) ^ D.cartan i j := by
  rw [D.pairing_root_simpleTorus, ← D.symmetrizer_mul_cartan, ← zpow_natCast, ← zpow_mul]
private theorem zpow_neg_pairing_simpleTorus (i j : ι) :
    q ^ (-D.pairing (D.root j) (D.simpleTorus i)) = (q ^ D.symmetrizer i) ^ (-D.cartan i j) := by
  rw [zpow_neg, zpow_pairing_simpleTorus, ← zpow_neg]

theorem simpleK_mul_e (i j : ι) : simpleK D q i * e D q j =
    (q ^ D.symmetrizer i) ^ D.cartan i j • (e D q j * simpleK D q i) := by
  rw [simpleK_def, k_mul_e, zpow_pairing_simpleTorus]
theorem simpleKInv_mul_e (i j : ι) : simpleKInv D q i * e D q j =
    (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (e D q j * simpleKInv D q i) := by
  rw [simpleKInv_def, k_mul_e, map_neg, zpow_neg_pairing_simpleTorus]
theorem e_mul_simpleK (i j : ι) : e D q j * simpleK D q i =
    (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (simpleK D q i * e D q j) := by
  rw [simpleK_def, e_mul_k, zpow_neg_pairing_simpleTorus]
theorem e_mul_simpleKInv (i j : ι) : e D q j * simpleKInv D q i =
    (q ^ D.symmetrizer i) ^ D.cartan i j • (simpleKInv D q i * e D q j) := by
  rw [simpleKInv_def, e_mul_k, map_neg, neg_neg, zpow_pairing_simpleTorus]
theorem simpleK_mul_f (i j : ι) : simpleK D q i * f D q j =
    (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (f D q j * simpleK D q i) := by
  rw [simpleK_def, k_mul_f, zpow_neg_pairing_simpleTorus]
theorem simpleKInv_mul_f (i j : ι) : simpleKInv D q i * f D q j =
    (q ^ D.symmetrizer i) ^ D.cartan i j • (f D q j * simpleKInv D q i) := by
  rw [simpleKInv_def, k_mul_f, map_neg, neg_neg, zpow_pairing_simpleTorus]
theorem f_mul_simpleK (i j : ι) : f D q j * simpleK D q i =
    (q ^ D.symmetrizer i) ^ D.cartan i j • (simpleK D q i * f D q j) := by
  rw [simpleK_def, f_mul_k, zpow_pairing_simpleTorus]
theorem f_mul_simpleKInv (i j : ι) : f D q j * simpleKInv D q i =
    (q ^ D.symmetrizer i) ^ (-D.cartan i j) • (simpleKInv D q i * f D q j) := by
  rw [simpleKInv_def, f_mul_k, map_neg, zpow_neg_pairing_simpleTorus]

theorem k_mul_quantumDividedPower_e (q' : K) (y : Y) (i : ι) (n : ℕ) :
    k D q y * quantumDividedPower q' (e D q i) n =
      (q ^ D.pairing (D.root i) y) ^ n • (quantumDividedPower q' (e D q i) n * k D q y) :=
  mul_quantumDividedPower_of_mul_eq_smul_mul q' (k_mul_e D q y i) n
theorem k_mul_quantumDividedPower_f (q' : K) (y : Y) (i : ι) (n : ℕ) :
    k D q y * quantumDividedPower q' (f D q i) n =
      (q ^ (-D.pairing (D.root i) y)) ^ n • (quantumDividedPower q' (f D q i) n * k D q y) :=
  mul_quantumDividedPower_of_mul_eq_smul_mul q' (k_mul_f D q y i) n

theorem commute_simpleK_simpleK (i j : ι) : Commute (simpleK D q i) (simpleK D q j) :=
  commute_k_k D q (D.simpleTorus i) (D.simpleTorus j)
theorem commute_simpleK_simpleKInv (i j : ι) : Commute (simpleK D q i) (simpleKInv D q j) :=
  commute_k_k D q (D.simpleTorus i) (-D.simpleTorus j)
theorem commute_simpleKInv_simpleKInv (i j : ι) :
    Commute (simpleKInv D q i) (simpleKInv D q j) :=
  commute_k_k D q (-D.simpleTorus i) (-D.simpleTorus j)

/-! ### Commutator and quantum Serre relations -/

/-- The diagonal commutator relation `Eᵢ Fᵢ - Fᵢ Eᵢ = (Kᵢ - Kᵢ⁻¹) / (qᵢ - qᵢ⁻¹)`. -/
theorem e_mul_f_sub_f_mul_e_self (i : ι) :
    e D q i * f D q i - f D q i * e D q i =
      (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
        (simpleK D q i - simpleKInv D q i) := by
  simpa [simpleK_def, simpleKInv_def] using mkAlgHom_eq_of_rel D q (Rel.commutator_self i)

/-- The off-diagonal commutator relation `Eᵢ Fⱼ - Fⱼ Eᵢ = 0` for `i ≠ j`. -/
theorem e_mul_f_sub_f_mul_e_of_ne {i j : ι} (hij : i ≠ j) :
    e D q i * f D q j - f D q j * e D q i = 0 := by
  simpa using mkAlgHom_eq_of_rel D q (Rel.commutator_ne hij)

theorem commute_e_f {i j : ι} (hij : i ≠ j) : Commute (e D q i) (f D q j) :=
  sub_eq_zero.mp (e_mul_f_sub_f_mul_e_of_ne D q hij)

/-- Combined `Eᵢ`--`Fⱼ` commutator formula under `DecidableEq ι`. -/
theorem e_mul_f_sub_f_mul_e [DecidableEq ι] (i j : ι) :
    e D q i * f D q j - f D q j * e D q i =
      if i = j then
        (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
          (simpleK D q i - simpleKInv D q i)
      else 0 := by
  split_ifs with hij
  · exact hij ▸ e_mul_f_sub_f_mul_e_self D q i
  · exact e_mul_f_sub_f_mul_e_of_ne D q hij

/-- The positive quantum Serre relation in `QuantizedEnvelopingAlgebra D q` for `i ≠ j`. -/
theorem serreE_eq_zero {i j : ι} (hij : i ≠ j) : serreSum D q (e D q) i j = 0 := by
  simpa using mkAlgHom_eq_of_rel D q (Rel.serre_e hij)

/-- The negative quantum Serre relation in `QuantizedEnvelopingAlgebra D q` for `i ≠ j`. -/
theorem serreF_eq_zero {i j : ι} (hij : i ≠ j) : serreSum D q (f D q) i j = 0 := by
  simpa using mkAlgHom_eq_of_rel D q (Rel.serre_f hij)

/-- When `aᵢⱼ = 0` and `qᵢ - qᵢ⁻¹ ≠ 0`, `Eᵢ` and `Eⱼ` commute. -/
theorem commute_e_e_of_cartan_eq_zero {i j : ι} (hcartan : D.cartan i j = 0)
    (hq : q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹ ≠ 0) :
    Commute (e D q i) (e D q j) :=
  commute_of_serreSum_eq_zero D q hcartan hq
    (serreE_eq_zero D q (by rintro rfl; simp at hcartan))

/-- When `aᵢⱼ = 0` and `qᵢ - qᵢ⁻¹ ≠ 0`, `Fᵢ` and `Fⱼ` commute. -/
theorem commute_f_f_of_cartan_eq_zero {i j : ι} (hcartan : D.cartan i j = 0)
    (hq : q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹ ≠ 0) :
    Commute (f D q i) (f D q j) :=
  commute_of_serreSum_eq_zero D q hcartan hq
    (serreF_eq_zero D q (by rintro rfl; simp at hcartan))

/-! ### Universal property and generator induction -/

/-- A tuple of elements `(e, f, k)` in a `K`-algebra `A` satisfying the defining relations of
`QuantizedEnvelopingAlgebra D q`. Extensional on `(e, f, k)`. -/
@[ext]
structure GeneratorTuple (A : Type*) [Ring A] [Algebra K A] where
  /-- Proposed images of the raising generators `Eᵢ`. -/
  e : ι → A
  /-- Proposed images of the lowering generators `Fᵢ`. -/
  f : ι → A
  /-- Proposed images of the toral generators `K_y`. -/
  k : Y → A
  /-- `k 0 = 1`. -/
  k_zero : k 0 = 1
  /-- `k y * k z = k (y + z)`. -/
  k_mul_k : ∀ y z : Y, k y * k z = k (y + z)
  /-- `k y * e i * k (-y) = q^⟨αᵢ, y⟩ • e i`. -/
  conjugate_e : ∀ (y : Y) (i : ι), k y * e i * k (-y) = q ^ D.pairing (D.root i) y • e i
  /-- `k y * f i * k (-y) = q^(-⟨αᵢ, y⟩) • f i`. -/
  conjugate_f : ∀ (y : Y) (i : ι), k y * f i * k (-y) = q ^ (-D.pairing (D.root i) y) • f i
  /-- `e i * f i - f i * e i = (k (dᵢ hᵢ) - k (-dᵢ hᵢ)) / (qᵢ - qᵢ⁻¹)`. -/
  commutator_self : ∀ i : ι,
    e i * f i - f i * e i =
      (q ^ D.symmetrizer i - (q ^ D.symmetrizer i)⁻¹)⁻¹ •
        (k (D.simpleTorus i) - k (-D.simpleTorus i))
  /-- `e i * f j - f j * e i = 0` for `i ≠ j`. -/
  commutator_ne : ∀ {i j : ι}, i ≠ j → e i * f j - f j * e i = 0
  /-- Positive quantum Serre relation for `i ≠ j`. -/
  serre_e : ∀ {i j : ι}, i ≠ j → serreSum D q e i j = 0
  /-- Negative quantum Serre relation for `i ≠ j`. -/
  serre_f : ∀ {i j : ι}, i ≠ j → serreSum D q f i j = 0

namespace GeneratorTuple

variable {D q} {A : Type*} [Ring A] [Algebra K A]

/-- The function `Generator ι Y → A` underlying a `GeneratorTuple`. -/
def toFun (T : GeneratorTuple D q A) : Generator ι Y → A
  | .e i => T.e i
  | .f i => T.f i
  | .k y => T.k y

@[simp] theorem toFun_e (T : GeneratorTuple D q A) (i : ι) : T.toFun (.e i) = T.e i := (rfl)
@[simp] theorem toFun_f (T : GeneratorTuple D q A) (i : ι) : T.toFun (.f i) = T.f i := (rfl)
@[simp] theorem toFun_k (T : GeneratorTuple D q A) (y : Y) : T.toFun (.k y) = T.k y := (rfl)

end GeneratorTuple

section Lift

variable {D q} {A : Type*} [Ring A] [Algebra K A]

/-- **Universal property of `QuantizedEnvelopingAlgebra`**: a `GeneratorTuple` in a `K`-algebra `A`
extends uniquely to a `K`-algebra homomorphism `QuantizedEnvelopingAlgebra D q →ₐ[K] A`. -/
noncomputable def lift (T : GeneratorTuple D q A) : QuantizedEnvelopingAlgebra D q →ₐ[K] A :=
  RingQuot.liftAlgHom K ⟨FreeAlgebra.lift K T.toFun, by
    intro a b h
    cases h with
    | k_zero => simpa using T.k_zero
    | k_mul_k y z => simpa using T.k_mul_k y z
    | conjugate_e y i => simpa using T.conjugate_e y i
    | conjugate_f y i => simpa using T.conjugate_f y i
    | commutator_self i => simpa using T.commutator_self i
    | commutator_ne hij => simpa using T.commutator_ne hij
    | serre_e hij => simpa using T.serre_e hij
    | serre_f hij => simpa using T.serre_f hij⟩

@[simp] theorem lift_generator (T : GeneratorTuple D q A) (g : Generator ι Y) :
    lift T (generator D q g) = T.toFun g :=
  (RingQuot.liftAlgHom_mkAlgHom_apply K _ _ _).trans (FreeAlgebra.lift_ι_apply _ _)
@[simp] theorem lift_e (T : GeneratorTuple D q A) (i : ι) : lift T (e D q i) = T.e i :=
  lift_generator T (.e i)
@[simp] theorem lift_f (T : GeneratorTuple D q A) (i : ι) : lift T (f D q i) = T.f i :=
  lift_generator T (.f i)
@[simp] theorem lift_k (T : GeneratorTuple D q A) (y : Y) : lift T (k D q y) = T.k y :=
  lift_generator T (.k y)
@[simp] theorem lift_simpleK (T : GeneratorTuple D q A) (i : ι) :
    lift T (simpleK D q i) = T.k (D.simpleTorus i) := lift_k T (D.simpleTorus i)
@[simp] theorem lift_simpleKInv (T : GeneratorTuple D q A) (i : ι) :
    lift T (simpleKInv D q i) = T.k (-D.simpleTorus i) := lift_k T (-D.simpleTorus i)

/-- Two `K`-algebra homomorphisms out of `QuantizedEnvelopingAlgebra D q` agreeing on `e`, `f`, and
`k` are equal. -/
@[ext high]
theorem hom_ext {φ ψ : QuantizedEnvelopingAlgebra D q →ₐ[K] A}
    (he : ∀ i, φ (e D q i) = ψ (e D q i)) (hf : ∀ i, φ (f D q i) = ψ (f D q i))
    (hk : ∀ y, φ (k D q y) = ψ (k D q y)) : φ = ψ := by
  apply RingQuot.ringQuot_ext' K φ ψ
  apply FreeAlgebra.hom_ext; funext g
  rcases g with i | i | y; exacts [he i, hf i, hk y]

/-- Equivalence between `K`-algebra maps `QuantizedEnvelopingAlgebra D q →ₐ[K] A` and
`GeneratorTuple D q A`. -/
noncomputable def liftEquiv :
    (QuantizedEnvelopingAlgebra D q →ₐ[K] A) ≃ GeneratorTuple D q A where
  toFun φ :=
    { e := fun i => φ (e D q i), f := fun i => φ (f D q i), k := fun y => φ (k D q y)
      k_zero := by rw [← map_one φ, ← k_zero D q]
      k_mul_k := fun y z => by rw [← map_mul, k_mul_k]
      conjugate_e := fun y i => by simpa using congrArg φ (k_mul_e_mul_k_neg D q y i)
      conjugate_f := fun y i => by simpa using congrArg φ (k_mul_f_mul_k_neg D q y i)
      commutator_self := fun i => by
        simpa [simpleK_def, simpleKInv_def] using congrArg φ (e_mul_f_sub_f_mul_e_self D q i)
      commutator_ne := fun hij => by simpa using congrArg φ (e_mul_f_sub_f_mul_e_of_ne D q hij)
      serre_e := fun hij => by simpa using congrArg φ (serreE_eq_zero D q hij)
      serre_f := fun hij => by simpa using congrArg φ (serreF_eq_zero D q hij) }
  invFun := lift
  left_inv φ := hom_ext (fun _ => lift_e _ _) (fun _ => lift_f _ _) (fun _ => lift_k _ _)
  right_inv T := by ext <;> simp

@[simp] theorem liftEquiv_apply_e (φ : QuantizedEnvelopingAlgebra D q →ₐ[K] A) (i : ι) :
    (liftEquiv φ).e i = φ (e D q i) := (rfl)
@[simp] theorem liftEquiv_apply_f (φ : QuantizedEnvelopingAlgebra D q →ₐ[K] A) (i : ι) :
    (liftEquiv φ).f i = φ (f D q i) := (rfl)
@[simp] theorem liftEquiv_apply_k (φ : QuantizedEnvelopingAlgebra D q →ₐ[K] A) (y : Y) :
    (liftEquiv φ).k y = φ (k D q y) := (rfl)
@[simp] theorem liftEquiv_symm_apply (T : GeneratorTuple D q A) : liftEquiv.symm T = lift T := (rfl)

end Lift

/-- The generators `Generator ι Y` generate `QuantizedEnvelopingAlgebra D q` as a `K`-algebra. -/
theorem adjoin_range_generator :
    Algebra.adjoin K (Set.range (generator D q)) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_freeAlgebra_lift]
  have h : FreeAlgebra.lift K (generator D q) = mkAlgHom D q :=
    FreeAlgebra.hom_ext (funext fun g => by simp)
  rw [h, AlgHom.range_eq_top]
  exact mkAlgHom_surjective D q

/-- Induction principle on `QuantizedEnvelopingAlgebra D q`: a predicate holding on scalars and on
all generators `e i`, `f i`, `k y`, and closed under addition and multiplication, holds everywhere.
-/
@[elab_as_elim]
theorem induction {P : QuantizedEnvelopingAlgebra D q → Prop}
    (algebraMap' : ∀ c : K, P (algebraMap K (QuantizedEnvelopingAlgebra D q) c))
    (e : ∀ i : ι, P (QuantizedEnvelopingAlgebra.e D q i))
    (f : ∀ i : ι, P (QuantizedEnvelopingAlgebra.f D q i))
    (k : ∀ y : Y, P (QuantizedEnvelopingAlgebra.k D q y))
    (add : ∀ a b, P a → P b → P (a + b)) (mul : ∀ a b, P a → P b → P (a * b))
    (u : QuantizedEnvelopingAlgebra D q) : P u := by
  have hu : u ∈ Algebra.adjoin K (Set.range (generator D q)) := by
    rw [adjoin_range_generator]; exact Algebra.mem_top
  induction hu using Algebra.adjoin_induction with
  | mem _ hx => rcases hx with ⟨i | i | y, rfl⟩; exacts [e i, f i, k y]
  | algebraMap c => exact algebraMap' c
  | add a b _ _ ha hb => exact add a b ha hb
  | mul a b _ _ ha hb => exact mul a b ha hb

/-- An element commuting with all generators `e i`, `f i`, and `k y` commutes with every element of
`QuantizedEnvelopingAlgebra D q`. -/
theorem commute_of_commute_generators {z : QuantizedEnvelopingAlgebra D q}
    (he : ∀ i, Commute (e D q i) z) (hf : ∀ i, Commute (f D q i) z)
    (hk : ∀ y, Commute (k D q y) z) (u : QuantizedEnvelopingAlgebra D q) : Commute u z := by
  refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute (R := K)
    (s := Set.range (generator D q)) ?_ ?_).symm
  · rw [adjoin_range_generator]; exact Algebra.mem_top
  · rintro _ ⟨i | i | y, rfl⟩; exacts [(he i).symm, (hf i).symm, (hk y).symm]

/-- For a root-annihilating coweight `c ∈ Y` (`⟨αᵢ, c⟩ = 0` for all `i`), `K_c` commutes with every
element of `QuantizedEnvelopingAlgebra D q`. -/
theorem commute_k_of_pairing_root_eq_zero {c : Y}
    (hc : ∀ i, D.pairing (D.root i) c = 0) (u : QuantizedEnvelopingAlgebra D q) :
    Commute u (k D q c) := by
  refine commute_of_commute_generators D q (fun i => ?_) (fun i => ?_)
    (fun y => commute_k_k D q y c) u
  · rw [Commute, SemiconjBy, e_mul_k, hc i, neg_zero, zpow_zero, one_smul]
  · rw [Commute, SemiconjBy, f_mul_k, hc i, zpow_zero, one_smul]

/-- For a root-annihilating coweight `c ∈ Y` (`⟨αᵢ, c⟩ = 0` for all `i`), `K_c` belongs to the
center of `QuantizedEnvelopingAlgebra D q`. -/
theorem k_mem_center_of_pairing_root_eq_zero {c : Y} (hc : ∀ i, D.pairing (D.root i) c = 0) :
    k D q c ∈ Subalgebra.center K (QuantizedEnvelopingAlgebra D q) :=
  Subalgebra.mem_center_iff.mpr (commute_k_of_pairing_root_eq_zero D q hc)

/-! ### Diagonal rescaling, Chevalley involution, and datum functoriality -/

private noncomputable def rescaleTuple (c : ι → Kˣ) :
    GeneratorTuple D q (QuantizedEnvelopingAlgebra D q) where
  e i := (c i : K) • e D q i
  f i := (c i : K)⁻¹ • f D q i
  k y := k D q y
  k_zero := k_zero D q
  k_mul_k := k_mul_k D q
  conjugate_e y i := by rw [mul_smul_comm, smul_mul_assoc, k_mul_e_mul_k_neg, smul_comm]
  conjugate_f y i := by rw [mul_smul_comm, smul_mul_assoc, k_mul_f_mul_k_neg, smul_comm]
  commutator_self i := by
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_inv_cancel₀ (c i).ne_zero,
      inv_mul_cancel₀ (c i).ne_zero, one_smul, one_smul, e_mul_f_sub_f_mul_e_self,
      simpleK_def, simpleKInv_def]
  commutator_ne {i j} hij := by
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm ((c j : K)⁻¹) (c i : K), ← smul_sub,
      e_mul_f_sub_f_mul_e_of_ne D q hij, smul_zero]
  serre_e hij := by rw [serreSum_smul, serreE_eq_zero D q hij, smul_zero]
  serre_f hij := by rw [serreSum_smul, serreF_eq_zero D q hij, smul_zero]

/-- Diagonal rescaling automorphism of `QuantizedEnvelopingAlgebra D q`: for units `c : ι → Kˣ`,
sends `Eᵢ ↦ cᵢ • Eᵢ`, `Fᵢ ↦ cᵢ⁻¹ • Fᵢ`, and `K_y ↦ K_y`. -/
noncomputable def rescale (c : ι → Kˣ) :
    QuantizedEnvelopingAlgebra D q ≃ₐ[K] QuantizedEnvelopingAlgebra D q :=
  AlgEquiv.ofAlgHom (lift (rescaleTuple D q c)) (lift (rescaleTuple D q fun i => (c i)⁻¹))
    (by ext i <;> simp [rescaleTuple, smul_smul, Units.ne_zero])
    (by ext i <;> simp [rescaleTuple, smul_smul, Units.ne_zero])

@[simp] theorem rescale_e (c : ι → Kˣ) (i : ι) :
    rescale D q c (e D q i) = (c i : K) • e D q i := lift_e (rescaleTuple D q c) i
@[simp] theorem rescale_f (c : ι → Kˣ) (i : ι) :
    rescale D q c (f D q i) = (c i : K)⁻¹ • f D q i := lift_f (rescaleTuple D q c) i
@[simp] theorem rescale_k (c : ι → Kˣ) (y : Y) :
    rescale D q c (k D q y) = k D q y := lift_k (rescaleTuple D q c) y
@[simp] theorem rescale_symm (c : ι → Kˣ) :
    (rescale D q c).symm = rescale D q (fun i => (c i)⁻¹) := by ext; rfl

private noncomputable def chevalleyTuple :
    GeneratorTuple D q (QuantizedEnvelopingAlgebra D q) where
  e := f D q
  f := e D q
  k y := k D q (-y)
  k_zero := by simp
  k_mul_k y z := by rw [k_mul_k, neg_add_rev, add_comm]
  conjugate_e y i := by simpa only [map_neg, neg_neg] using k_mul_f_mul_k_neg D q (-y) i
  conjugate_f y i := by simpa only [map_neg] using k_mul_e_mul_k_neg D q (-y) i
  commutator_self i := by
    simpa only [neg_sub, ← smul_neg, simpleK_def, simpleKInv_def, neg_neg] using
      congrArg Neg.neg (e_mul_f_sub_f_mul_e_self D q i)
  commutator_ne hij := by
    simpa only [neg_sub, neg_zero] using congrArg Neg.neg (e_mul_f_sub_f_mul_e_of_ne D q hij.symm)
  serre_e := serreF_eq_zero D q
  serre_f := serreE_eq_zero D q

/-- The Chevalley `K`-algebra involution `ω` of `QuantizedEnvelopingAlgebra D q`, swapping
`Eᵢ ↔ Fᵢ` and sending `K_y ↦ K_(-y)`. -/
noncomputable def chevalleyInvolution :
    QuantizedEnvelopingAlgebra D q ≃ₐ[K] QuantizedEnvelopingAlgebra D q :=
  AlgEquiv.ofAlgHom (lift (chevalleyTuple D q)) (lift (chevalleyTuple D q))
    (by ext <;> simp [chevalleyTuple]) (by ext <;> simp [chevalleyTuple])

@[simp] theorem chevalleyInvolution_e (i : ι) :
    chevalleyInvolution D q (e D q i) = f D q i := lift_e (chevalleyTuple D q) i
@[simp] theorem chevalleyInvolution_f (i : ι) :
    chevalleyInvolution D q (f D q i) = e D q i := lift_f (chevalleyTuple D q) i
@[simp] theorem chevalleyInvolution_k (y : Y) :
    chevalleyInvolution D q (k D q y) = k D q (-y) := lift_k (chevalleyTuple D q) y
@[simp] theorem chevalleyInvolution_symm :
    (chevalleyInvolution D q).symm = chevalleyInvolution D q := by ext; rfl
@[simp] theorem chevalleyInvolution_chevalleyInvolution (u : QuantizedEnvelopingAlgebra D q) :
    chevalleyInvolution D q (chevalleyInvolution D q u) = u :=
  (chevalleyInvolution D q).symm_apply_apply u

end Presentation

section Functoriality

variable {ι X Y X' Y' X'' Y'' K : Type*}
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y']
  [AddCommGroup X''] [AddCommGroup Y''] [Field K]
  {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'} {D'' : CartanDatum ι X'' Y''}

/-- A morphism of Cartan data `φ : CartanDatum.Hom D D'` induces a `K`-algebra homomorphism
`QuantizedEnvelopingAlgebra D q →ₐ[K] QuantizedEnvelopingAlgebra D' q` sending `Eᵢ ↦ Eᵢ`,
`Fᵢ ↦ Fᵢ`, and `K_y ↦ K_(φ y)`. -/
noncomputable def map (φ : CartanDatum.Hom D D') (q : K) :
    QuantizedEnvelopingAlgebra D q →ₐ[K] QuantizedEnvelopingAlgebra D' q :=
  lift
    { e := e D' q, f := f D' q, k := fun y => k D' q (φ.toLinearMap y)
      k_zero := by simp
      k_mul_k := fun y z => by rw [k_mul_k, map_add]
      conjugate_e := fun y i => by rw [map_neg, k_mul_e_mul_k_neg, φ.pairing_root_map]
      conjugate_f := fun y i => by rw [map_neg, k_mul_f_mul_k_neg, φ.pairing_root_map]
      commutator_self := fun i => by
        rw [e_mul_f_sub_f_mul_e_self, φ.symmetrizer_eq, map_neg, φ.map_simpleTorus,
          simpleK_def, simpleKInv_def]
      commutator_ne := e_mul_f_sub_f_mul_e_of_ne D' q
      serre_e := fun {i j} hij => by
        simpa only [serreSum_def, φ.serreLength_eq i j, φ.symmetrizer_eq] using
          serreE_eq_zero D' q hij
      serre_f := fun {i j} hij => by
        simpa only [serreSum_def, φ.serreLength_eq i j, φ.symmetrizer_eq] using
          serreF_eq_zero D' q hij }

@[simp] theorem map_e (φ : CartanDatum.Hom D D') (q : K) (i : ι) :
    map φ q (e D q i) = e D' q i := lift_e _ i
@[simp] theorem map_f (φ : CartanDatum.Hom D D') (q : K) (i : ι) :
    map φ q (f D q i) = f D' q i := lift_f _ i
@[simp] theorem map_k (φ : CartanDatum.Hom D D') (q : K) (y : Y) :
    map φ q (k D q y) = k D' q (φ.toLinearMap y) := lift_k _ y
@[simp] theorem map_simpleK (φ : CartanDatum.Hom D D') (q : K) (i : ι) :
    map φ q (simpleK D q i) = simpleK D' q i := by
  rw [simpleK_def, map_k, φ.map_simpleTorus, ← simpleK_def]
@[simp] theorem map_simpleKInv (φ : CartanDatum.Hom D D') (q : K) (i : ι) :
    map φ q (simpleKInv D q i) = simpleKInv D' q i := by
  rw [simpleKInv_def, map_k, map_neg, φ.map_simpleTorus, ← simpleKInv_def]
@[simp] theorem map_normalizedE (φ : CartanDatum.Hom D D') (q : K) (i : ι) :
    map φ q (normalizedE D q i) = normalizedE D' q i := by
  rw [normalizedE_def, map_mul, map_simpleKInv, map_e, ← normalizedE_def]
@[simp] theorem map_normalizedF (φ : CartanDatum.Hom D D') (q : K) (i : ι) :
    map φ q (normalizedF D q i) = normalizedF D' q i := by
  rw [normalizedF_def, map_mul, map_f, map_simpleK, ← normalizedF_def]
@[simp] theorem map_id (D : CartanDatum ι X Y) (q : K) :
    map (CartanDatum.Hom.id D) q = AlgHom.id K (QuantizedEnvelopingAlgebra D q) := by ext <;> simp
theorem map_comp (ψ : CartanDatum.Hom D' D'') (φ : CartanDatum.Hom D D') (q : K) :
    map (ψ.comp φ) q = (map ψ q).comp (map φ q) := by ext <;> simp

end Functoriality

end QuantizedEnvelopingAlgebra

end TauCeti
