/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Sugawara.Basic

import Mathlib.Topology.Algebra.InfiniteSum.Module
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Algebra.Lie.Current.Sugawara.Degree

/-!
# The Segal--Sugawara Virasoro relations

Let `L` be a finite-dimensional Lie algebra over a field `K` whose Killing form `κ_L` is
nondegenerate, let `Φ` be an invariant symmetric bilinear form on `L`, and let
`Û = lim_N U / I_N` be the completed enveloping algebra of the residue central extension of `Φ` at
the central value `a` (`TauCeti.CurrentAlgebra.CompletedEnveloping`). The Segal--Sugawara modes
`Sₙ = ∑ᵢ :xᵢ yᵢ:_n` (`TauCeti.CurrentAlgebra.sugawaraMode`) are built from any basis `xᵢ` of `L`
and its Killing-dual basis `yᵢ`.

When `Φ = c • κ_L`, the commutator of a current mode with `Sₘ` is
`[Sₘ, z_k] = -k (1 - 2 a c) z_{m+k}`. Applying this factor by factor to the summands of a normally
ordered mode `:x y:_n` splits `[Sₘ, :x y:_n]` into a family ordered at the cut `m` with scalar
weights `(1 - 2 a c) (m - l)` and a family ordered at the cut `0` with scalar weights
`(1 - 2 a c) (l - n)`. Both weighted families converge in the nonarchimedean inverse-limit topology
of `Û`. Moving the cut of the first family back to `0` combines the two infinite series into
`(1 - 2 a c) (m - n) :x y:_{m+n}`, while the finite window between `0` and `m` contributes
`(1 - 2 a c) (m (m + 1) / 2) ⁅x, y⁆_{m+n}` and the signed sum of `l (m - l)` between `0` and `m`,
which is `(m ^ 3 - m) / 6`. Both quotients `m (m + 1) / 2` and `(m ^ 3 - m) / 6` are exact integer
divisions computed in `ℤ` before casting to `K`, so summing over Killing-dual bases kills the
bracket term by `∑ᵢ ⁅xᵢ, yᵢ⁆ = 0` and contracts `∑ᵢ Φ(xᵢ, yᵢ) = c · dim L`, yielding the
unnormalised commutator

`[Sₘ, Sₙ] = (1 - 2 a c) (m - n) S_{m+n} - δ_{m+n, 0} ((m ^ 3 - m) / 6) (1 - 2 a c) a c · dim L`

over every field `K` (including characteristics `2` and `3`, where `(m ^ 3 - m) / 6` is still
evaluated in `ℤ` before casting to `K`), at every level including the critical level `1 - 2 a c = 0`
and `a = 0`.

When `Φ = c • κ_L` and `2` and `3` are invertible in `K`, the **Segal--Sugawara Virasoro modes**
`Lₘ = (1 - 2 a c)⁻¹ Sₘ` (`TauCeti.CurrentAlgebra.sugawaraVirasoro`) satisfy the Virasoro commutation
relations

`[Lₘ, Lₙ] = (m - n) L_{m+n} + δ_{m+n, 0} ((m ^ 3 - m) / 12) c_{Vir}`

with central charge `c_{Vir} = -(2 a c) / (1 - 2 a c) · dim L`
(`TauCeti.CurrentAlgebra.sugawaraCentralCharge`), reducing to `0 = 0` at `1 - 2 a c = 0` and giving
the nontrivial Virasoro algebra away from the critical level (`1 - 2 a c ≠ 0`).

## Main results

* `TauCeti.CurrentAlgebra.sugawaraMode_mul_normalOrderedMode_sub_mul_of_eq_smul_killingForm`:
  commutator `[Sₘ, :x y:_n]` for `Φ = c • κ_L`.
* `TauCeti.CurrentAlgebra.sugawaraMode_mul_sugawaraMode_sub_mul_of_eq_smul_killingForm`:
  commutator `[Sₘ, Sₙ]` over an arbitrary field.
* `TauCeti.CurrentAlgebra.sugawaraVirasoro_mul_sugawaraVirasoro_sub_mul`: the Virasoro commutation
  relations of `Lₘ`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §§3.1.1--3.1.4,
  equations (3.1-1)--(3.1-3).
* V. G. Kac, *Vertex Algebras for Beginners*, 2nd ed., §5.7, Theorem 5.7.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.5.10.
-/

public section

noncomputable section

open scoped TensorProduct
open LieAlgebra TauCeti.UniversalEnvelopingAlgebra
open LieAlgebra.ofTwoCocycle (centralElement envelopingι)

namespace TauCeti.CurrentAlgebra

/-! ### Commutator of Segal--Sugawara modes -/

section Commutator

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  {Φ : LinearMap.BilinForm K L} {hΦ : Φ.lieInvariant L} {hΦs : Φ.IsSymm} {a : K}

local notation "UK" => CentralQuotient K (centralElement (twoCocycleOfBilinear K L Φ hΦ hΦs)) a

local notation "ι[" x ", " m "]" =>
  envelopingι (twoCocycleOfBilinear K L Φ hΦ hΦs) a (HahnSeries.single m (1 : K) ⊗ₜ[K] x)

local notation "toC" => toCompletedEnveloping Φ hΦ hΦs a

/-- The commutator of `Sₘ` with the index-`j` summand of `:x y:_n` splits into the index-`(j + m)`
summand of `:x y:_{m+n}` at the cut `m` weighted by `(1 - 2 a c) (-j)`, plus the index-`j` summand
at the cut `0` weighted by `(1 - 2 a c) (j - n)`. -/
private theorem sugawaraMode_mul_normalOrderedSummand_sub_mul {c : K}
    (h : Φ = c • killingForm K L) (x y : L) (m n j : ℤ) :
    sugawaraMode Φ hΦ hΦs a m * toC (normalOrderedSummand Φ hΦ hΦs a 0 n j x y) -
        toC (normalOrderedSummand Φ hΦ hΦs a 0 n j x y) * sugawaraMode Φ hΦ hΦs a m =
      ((1 - 2 * a * c) * -(j : K)) • toC (normalOrderedSummand Φ hΦ hΦs a m (m + n) (j + m) x y) +
        ((1 - 2 * a * c) * (j - n : K)) •
          toC (normalOrderedSummand Φ hΦ hΦs a 0 (m + n) j x y) := by
  have hsub₁ : m + n - (j + m) = n - j := by ring
  have hsub₂ : m + (n - j) = m + n - j := by ring
  have hadd : m + j = j + m := add_comm m j
  have hlt : j + m < m ↔ j < 0 := by omega
  rw [sugawaraMode_mul_sub_mul_of_eq_smul_killingForm h m]
  simp only [normalOrderedSummand_apply, hsub₁, hlt]
  by_cases hj : j < 0 <;> simp only [hj, ↓reduceIte, map_mul, derivationLieAlgebra.leibniz,
    vectorFieldCompletedEnvelopingDerivation_neg, NegMemClass.coe_neg, LinearMap.neg_apply,
    vectorFieldCompletedEnvelopingDerivation_single_add_one_envelopingι_single_tmul,
    ← Int.cast_smul_eq_zsmul K, hadd, hsub₂] <;>
  · simp only [Int.cast_sub, smul_neg, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
    module

/-- **The commutator of a Segal--Sugawara mode with a normally ordered mode**, for `Φ = c • κ_L`
over any field `K` (with `m (m + 1) / 2` and `(m ^ 3 - m) / 6` computed in `ℤ` before casting to
`K`). -/
theorem sugawaraMode_mul_normalOrderedMode_sub_mul_of_eq_smul_killingForm {c : K}
    (h : Φ = c • killingForm K L) (x y : L) (m n : ℤ) :
    sugawaraMode Φ hΦ hΦs a m * normalOrderedMode Φ hΦ hΦs a n x y -
        normalOrderedMode Φ hΦ hΦs a n x y * sugawaraMode Φ hΦ hΦs a m =
      ((1 - 2 * a * c) * (m - n : K)) • normalOrderedMode Φ hΦ hΦs a (m + n) x y +
        ((1 - 2 * a * c) * ((m * (m + 1) / 2 : ℤ) : K)) • toC ι[⁅x, y⁆, m + n] -
        algebraMap K (CompletedEnveloping Φ hΦ hΦs a)
          (if m + n = 0 then ((m ^ 3 - m) / 6 : ℤ) * (1 - 2 * a * c) * a * Φ x y else 0) := by
  -- Stage 1: Distribute `[Sₘ, -]` over the normally ordered series for `:x y:_n`.
  have h₁ := ((hasSum_normalOrderedMode (Φ := Φ) (hΦ := hΦ) (hΦs := hΦs) (a := a) n x y).mul_left
    (sugawaraMode Φ hΦ hΦs a m)).sub
    ((hasSum_normalOrderedMode n x y).mul_right (sugawaraMode Φ hΦ hΦs a m))
  simp only [sugawaraMode_mul_normalOrderedSummand_sub_mul h] at h₁
  -- Stage 2: Sum the cut-`m` and cut-`0` weighted families separately, reindexing `j + m ↦ l`.
  let w₁ (l : ℤ) : K := (1 - 2 * a * c) * -((l - m : ℤ) : K)
  let w₂ (l : ℤ) : K := (1 - 2 * a * c) * (l - n : K)
  have hA₀ := (summable_smul_normalOrderedSummand Φ hΦ hΦs a m (m + n) w₁ x y).hasSum
  have hA : HasSum (fun j : ℤ ↦ ((1 - 2 * a * c) * -(j : K)) •
      toC (normalOrderedSummand Φ hΦ hΦs a m (m + n) (j + m) x y))
      (∑' l : ℤ, w₁ l • toC (normalOrderedSummand Φ hΦ hΦs a m (m + n) l x y)) := by
    simpa only [Function.comp_def, Equiv.coe_addRight, w₁, add_sub_cancel_right] using
      (Equiv.addRight m).hasSum_iff.2 hA₀
  have hB := (summable_smul_normalOrderedSummand Φ hΦ hΦs a 0 (m + n) w₂ x y).hasSum
  -- Stage 3: Move the cut from `m` back to `0` and combine both cut-`0` series.
  rw [h₁.unique (hA.add hB), tsum_smul_normalOrderedSummand, add_right_comm]
  have hsum0 :
      (∑' l : ℤ, w₁ l • toC (normalOrderedSummand Φ hΦ hΦs a 0 (m + n) l x y)) +
        ∑' l : ℤ, w₂ l • toC (normalOrderedSummand Φ hΦ hΦs a 0 (m + n) l x y) =
      ((1 - 2 * a * c) * (m - n : K)) • normalOrderedMode Φ hΦ hΦs a (m + n) x y := by
    rw [← (summable_smul_normalOrderedSummand Φ hΦ hΦs a 0 (m + n) w₁ x y).tsum_add
      (summable_smul_normalOrderedSummand Φ hΦ hΦs a 0 (m + n) w₂ x y)]
    have hpt (l : ℤ) :
        w₁ l • toC (normalOrderedSummand Φ hΦ hΦs a 0 (m + n) l x y) +
          w₂ l • toC (normalOrderedSummand Φ hΦ hΦs a 0 (m + n) l x y) =
        ((1 - 2 * a * c) * (m - n : K)) •
          toC (normalOrderedSummand Φ hΦ hΦs a 0 (m + n) l x y) := by
      simp only [w₁, w₂, Int.cast_sub]
      module
    simp_rw [hpt, (summable_normalOrderedSummand Φ hΦ hΦs a 0 (m + n) x y).tsum_const_smul,
      ← normalOrderedMode_apply]
  have hw₁ (l : ℤ) :
      w₁ l • (ι[x, l] * ι[y, m + n - l] - ι[y, m + n - l] * ι[x, l]) =
        (1 - 2 * a * c) • (((m - l : ℤ) : K) •
          (ι[x, l] * ι[y, m + n - l] - ι[y, m + n - l] * ι[x, l])) := by
    simp only [w₁, smul_smul, Int.cast_sub]
    congr 1
    ring
  rw [hsum0]
  simp_rw [hw₁, ← Finset.smul_sum, ← smul_sub, map_smul]
  rw [sum_Ico_sub_sum_Ico_sub_smul_envelopingι_mul_sub_mul x y m (m + n), map_sub, map_smul,
    smul_sub, smul_smul, AlgHom.commutes]
  have hcent : (1 - 2 * a * c) • algebraMap K (CompletedEnveloping Φ hΦ hΦs a)
      (if m + n = 0 then ((m ^ 3 - m) / 6 : ℤ) * a * Φ x y else 0) =
      algebraMap K (CompletedEnveloping Φ hΦ hΦs a)
        (if m + n = 0 then ((m ^ 3 - m) / 6 : ℤ) * (1 - 2 * a * c) * a * Φ x y else 0) := by
    rw [Algebra.smul_def, ← map_mul]
    congr 1
    split_ifs <;> ring
  rw [hcent]
  abel

/-- **The commutator of two Segal--Sugawara modes**, for `Φ = c • κ_L` over any field `K` and at
every level, including the critical level `1 - 2 a c = 0` and `a = 0`:

`[Sₘ, Sₙ] = (1 - 2 a c) (m - n) S_{m+n} - δ_{m+n, 0} ((m ^ 3 - m) / 6) (1 - 2 a c) a c · dim L`,

where `(m ^ 3 - m) / 6` is computed in `ℤ` before casting to `K`. -/
theorem sugawaraMode_mul_sugawaraMode_sub_mul_of_eq_smul_killingForm {c : K}
    (h : Φ = c • killingForm K L) (m n : ℤ) :
    sugawaraMode Φ hΦ hΦs a m * sugawaraMode Φ hΦ hΦs a n -
        sugawaraMode Φ hΦ hΦs a n * sugawaraMode Φ hΦ hΦs a m =
      ((1 - 2 * a * c) * (m - n : K)) • sugawaraMode Φ hΦ hΦs a (m + n) -
        algebraMap K (CompletedEnveloping Φ hΦ hΦs a)
          (if m + n = 0 then
            ((m ^ 3 - m) / 6 : ℤ) * (1 - 2 * a * c) * a * c * (Module.finrank K L : K)
          else 0) := by
  set b := Module.finBasis K L
  have hnd := LieAlgebra.IsKilling.killingForm_nondegenerate K L
  conv_lhs =>
    rw [sugawaraMode_eq_sum b n, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [sugawaraMode_mul_normalOrderedMode_sub_mul_of_eq_smul_killingForm h,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, ← sugawaraMode_eq_sum b]
  have hlie : ∑ i, toC ι[⁅b i, killingDualBasis b i⁆, m + n] = 0 := by
    rw [← map_sum, ← map_sum, ← TensorProduct.tmul_sum, sum_lie_killingDualBasis_eq_zero,
      TensorProduct.tmul_zero, map_zero, map_zero]
  have htr : ∑ i, Φ (b i) (killingDualBasis b i) = c * (Module.finrank K L : K) := by
    have htrace := LinearMap.BilinForm.sum_apply_dualBasis_eq_trace hnd b (LinearMap.id : L →ₗ[K] L)
    simp only [LinearMap.id_coe, id_eq, LinearMap.trace_id] at htrace
    simp only [h, LinearMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ ↦ LieModule.traceForm_comm K L L (b i) _, htrace]
  have hcent : ∑ i, algebraMap K (CompletedEnveloping Φ hΦ hΦs a)
      (if m + n = 0 then
        ((m ^ 3 - m) / 6 : ℤ) * (1 - 2 * a * c) * a * Φ (b i) (killingDualBasis b i) else 0) =
      algebraMap K (CompletedEnveloping Φ hΦ hΦs a)
        (if m + n = 0 then
          ((m ^ 3 - m) / 6 : ℤ) * (1 - 2 * a * c) * a * c * (Module.finrank K L : K) else 0) := by
    rw [← map_sum]
    congr 1
    split_ifs
    · simp only [← Finset.mul_sum, htr]
      ring
    · simp
  rw [hlie, smul_zero, add_zero, hcent]

end Commutator

/-! ### Virasoro commutation relations -/

section Virasoro

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  {Φ : LinearMap.BilinForm K L} {hΦ : Φ.lieInvariant L} {hΦs : Φ.IsSymm} {a : K}

/-- **The Virasoro commutation relations of the Segal--Sugawara modes** over any field `K` in which
`2` and `3` are invertible: if `Φ = c • κ_L`, then

`[Lₘ, Lₙ] = (m - n) L_{m+n} + δ_{m+n, 0} ((m ^ 3 - m) / 12) c_{Vir}`

(totalised to `0 = 0` when `1 - 2 a c = 0`). -/
theorem sugawaraVirasoro_mul_sugawaraVirasoro_sub_mul [NeZero (2 : K)] [NeZero (3 : K)] {c : K}
    (h : Φ = c • killingForm K L) (m n : ℤ) :
    sugawaraVirasoro Φ hΦ hΦs a c m * sugawaraVirasoro Φ hΦ hΦs a c n -
        sugawaraVirasoro Φ hΦ hΦs a c n * sugawaraVirasoro Φ hΦ hΦs a c m =
      (m - n : K) • sugawaraVirasoro Φ hΦ hΦs a c (m + n) +
        algebraMap K (CompletedEnveloping Φ hΦ hΦs a)
          (if m + n = 0 then ((m : K) ^ 3 - m) / 12 * sugawaraCentralCharge K L a c else 0) := by
  by_cases hc : 1 - 2 * a * c = 0
  · simp [sugawaraVirasoro_def, sugawaraCentralCharge_def, hc]
  have h2 : (2 : K) ≠ 0 := NeZero.ne (2 : K)
  have h3 : (3 : K) ≠ 0 := NeZero.ne (3 : K)
  have h6 : (6 : K) ≠ 0 := by
    simpa [show (6 : K) = 2 * 3 by norm_num] using mul_ne_zero h2 h3
  have hdiv6 : (((m ^ 3 - m) / 6 : ℤ) : K) = ((m : K) ^ 3 - m) / 6 := by
    have hdvd : (6 : ℤ) ∣ m ^ 3 - m :=
      ⟨_, (Finset.six_mul_sum_Ico_zero_mul_sub_sub_sum_Ico_zero_mul_sub m).symm⟩
    simpa using Int.cast_div hdvd (by exact_mod_cast h6)
  rw [sugawaraVirasoro_def, sugawaraVirasoro_def, sugawaraVirasoro_def, smul_mul_smul_comm,
    smul_mul_smul_comm, ← smul_sub, sugawaraMode_mul_sugawaraMode_sub_mul_of_eq_smul_killingForm h,
    smul_sub, smul_smul, smul_smul]
  have hlin : (1 - 2 * a * c)⁻¹ * (1 - 2 * a * c)⁻¹ * ((1 - 2 * a * c) * (m - n : K)) =
      (m - n : K) * (1 - 2 * a * c)⁻¹ := by
    field_simp
  have hcent : -((1 - 2 * a * c)⁻¹ * (1 - 2 * a * c)⁻¹) •
      algebraMap K (CompletedEnveloping Φ hΦ hΦs a)
        (if m + n = 0 then
          ((m ^ 3 - m) / 6 : ℤ) * (1 - 2 * a * c) * a * c * (Module.finrank K L : K) else 0) =
      algebraMap K (CompletedEnveloping Φ hΦ hΦs a)
        (if m + n = 0 then ((m : K) ^ 3 - m) / 12 * sugawaraCentralCharge K L a c else 0) := by
    rw [Algebra.smul_def, ← map_mul]
    congr 1
    split_ifs
    · rw [hdiv6, sugawaraCentralCharge_def]
      have h12 : (12 : K) ≠ 0 := by
        simpa [show (12 : K) = 2 * 6 by norm_num] using mul_ne_zero h2 h6
      field_simp [h12]
      ring
    · simp
  rw [hlin, sub_eq_add_neg, ← neg_smul, hcent]

end Virasoro

end TauCeti.CurrentAlgebra
