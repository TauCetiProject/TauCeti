/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Sugawara.Basic

import Mathlib.Topology.Algebra.InfiniteSum.Module
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Algebra.Lie.Derivation.Basic

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
which is `(m ^ 3 - m) / 6`. Summing over Killing-dual bases kills the bracket term by
`∑ᵢ ⁅xᵢ, yᵢ⁆ = 0` and contracts `∑ᵢ Φ(xᵢ, yᵢ) = c · dim L`, yielding the unnormalised commutator

`[Sₘ, Sₙ] = (1 - 2 a c) (m - n) S_{m+n} - δ_{m+n, 0} ((m ^ 3 - m) / 6) (1 - 2 a c) a c · dim L`

over every field `K`, at every level including the critical level `1 - 2 a c = 0` and `a = 0`.

Away from the critical level, the **Segal--Sugawara Virasoro modes**
`Lₘ = (1 - 2 a c)⁻¹ Sₘ` (`TauCeti.CurrentAlgebra.sugawaraVirasoro`) satisfy, when `2` and `3` are
invertible in `K`, the Virasoro commutation relations

`[Lₘ, Lₙ] = (m - n) L_{m+n} + δ_{m+n, 0} ((m ^ 3 - m) / 12) c_{Vir}`

with central charge `c_{Vir} = -(2 a c) / (1 - 2 a c) · dim L`
(`TauCeti.CurrentAlgebra.sugawaraCentralCharge`).

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

attribute [local instance 100] LieRing.ofAssociativeRing

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
  simp only [normalOrderedSummand_apply, hsub₁, hlt]
  by_cases hj : j < 0 <;> simp only [hj, ↓reduceIte, map_mul] <;>
  · rw [← Ring.lie_def,
      ← LieAlgebra.ad_apply K (CompletedEnveloping Φ hΦ hΦs a) (sugawaraMode Φ hΦ hΦs a m),
      ← coe_innerDerivation K, derivationLieAlgebra.leibniz, coe_innerDerivation,
      LieAlgebra.ad_apply, LieAlgebra.ad_apply, Ring.lie_def, Ring.lie_def,
      ← neg_sub (toC ι[_, _] * _), ← neg_sub (toC ι[_, _] * _),
      toCompletedEnveloping_mul_sugawaraMode_sub_mul_of_eq_smul_killingForm h,
      toCompletedEnveloping_mul_sugawaraMode_sub_mul_of_eq_smul_killingForm h, hadd, hsub₂]
    simp only [Int.cast_sub, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
    module

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
/-- The signed sum of `(m - l) • [x_l, y_{m+n-l}]` between `0` and `m` evaluates to
`(m (m + 1) / 2) ⁅x, y⁆_{m+n}` minus the central term `((m ^ 3 - m) / 6) a Φ(x, y)` at
`m + n = 0`. -/
private theorem sum_Ico_sub_sum_Ico_sub_smul_envelopingι_mul_sub_mul (x y : L) (m n : ℤ) :
    ∑ l ∈ Finset.Ico 0 m, ((m - l : ℤ) : K) • (ι[x, l] * ι[y, m + n - l] -
        ι[y, m + n - l] * ι[x, l]) -
      ∑ l ∈ Finset.Ico m 0, ((m - l : ℤ) : K) • (ι[x, l] * ι[y, m + n - l] -
        ι[y, m + n - l] * ι[x, l]) =
      ((m * (m + 1) / 2 : ℤ) : K) • ι[⁅x, y⁆, m + n] -
        algebraMap K UK (if m + n = 0 then ((m ^ 3 - m) / 6 : ℤ) * a * Φ x y else 0) := by
  have hl (l : ℤ) : ((m - l : ℤ) : K) • (ι[x, l] * ι[y, m + n - l] -
      ι[y, m + n - l] * ι[x, l]) =
      (m + (-1 : ℤ) * l) • (ι[x, l] * ι[y, m + n - l] - ι[y, m + n - l] * ι[x, l]) := by
    rw [Int.cast_smul_eq_zsmul]
    congr 1
    ring
  simp only [hl]
  rw [sum_Ico_sub_sum_Ico_zsmul_envelopingι_mul_sub_mul x y m (-1) m (m + n)]
  have h2 : (m * (m - 1) / 2) * 2 = m * (m - 1) :=
    Int.ediv_mul_cancel (Int.even_mul_pred_self m).two_dvd
  have hc₁ : m * m + -1 * (m * (m - 1) / 2) = m * (m + 1) / 2 := by
    refine Int.eq_ediv_of_mul_eq_right two_ne_zero ?_
    linear_combination -h2
  have hc₂ : m * (m * (m - 1) / 2) + -1 * (m * (m - 1) * (2 * m - 1) / 6) =
      (m ^ 3 - m) / 6 := by
    refine Int.eq_ediv_of_mul_eq_right (by decide : (6 : ℤ) ≠ 0) ?_
    have h6 : (m * (m - 1) * (2 * m - 1) / 6) * 6 = m * (m - 1) * (2 * m - 1) :=
      Int.ediv_mul_cancel ⟨_, (Finset.six_mul_sum_Ico_zero_sq_sub_sum_Ico_zero_sq m).symm⟩
    linear_combination 3 * m * h2 - h6
  rw [hc₁, hc₂, Int.cast_smul_eq_zsmul]
  congr 1
  split_ifs <;> simp [zsmul_eq_mul, mul_assoc]

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
/-- Reordering the cut-`m` summand into cut `0` splits the combined `l`-th summand into
`(1 - 2 a c) (m - n)` times the cut-`0` summand plus the finite window difference between `0` and
`m`. -/
private theorem combined_normalOrderedSummand_eq (c : K) (x y : L) (m n l : ℤ) :
    ((1 - 2 * a * c) * -((l - m : ℤ) : K)) •
        toC (normalOrderedSummand Φ hΦ hΦs a m (m + n) l x y) +
      ((1 - 2 * a * c) * (l - n : K)) •
        toC (normalOrderedSummand Φ hΦ hΦs a 0 (m + n) l x y) =
      ((1 - 2 * a * c) * (m - n : K)) •
        toC (normalOrderedSummand Φ hΦ hΦs a 0 (m + n) l x y) +
      (1 - 2 * a * c) • toC (if l ∈ Finset.Ico 0 m then
        ((m - l : ℤ) : K) • (ι[x, l] * ι[y, m + n - l] - ι[y, m + n - l] * ι[x, l]) else 0) -
      (1 - 2 * a * c) • toC (if l ∈ Finset.Ico m 0 then
        ((m - l : ℤ) : K) • (ι[x, l] * ι[y, m + n - l] - ι[y, m + n - l] * ι[x, l]) else 0) := by
  rw [normalOrderedSummand_eq_add_sub m (m + n) l x y, map_sub, map_add, smul_sub, smul_add]
  have hite (s : Finset ℤ) :
      ((1 - 2 * a * c) * -((l - m : ℤ) : K)) • toC (if l ∈ s then
        ι[x, l] * ι[y, m + n - l] - ι[y, m + n - l] * ι[x, l] else 0) =
      (1 - 2 * a * c) • toC (if l ∈ s then
        ((m - l : ℤ) : K) • (ι[x, l] * ι[y, m + n - l] - ι[y, m + n - l] * ι[x, l]) else 0) := by
    split_ifs <;> simp only [map_zero, smul_zero, map_smul, smul_smul, Int.cast_sub]
    congr 1
    ring
  rw [hite (Finset.Ico 0 m), hite (Finset.Ico m 0), Int.cast_sub]
  module

/-- **The commutator of a Segal--Sugawara mode with a normally ordered mode**, for `Φ = c • κ_L`
over any field `K`. -/
theorem sugawaraMode_mul_normalOrderedMode_sub_mul_of_eq_smul_killingForm {c : K}
    (h : Φ = c • killingForm K L) (x y : L) (m n : ℤ) :
    sugawaraMode Φ hΦ hΦs a m * normalOrderedMode Φ hΦ hΦs a n x y -
        normalOrderedMode Φ hΦ hΦs a n x y * sugawaraMode Φ hΦ hΦs a m =
      ((1 - 2 * a * c) * (m - n : K)) • normalOrderedMode Φ hΦ hΦs a (m + n) x y +
        ((1 - 2 * a * c) * ((m * (m + 1) / 2 : ℤ) : K)) • toC ι[⁅x, y⁆, m + n] -
        algebraMap K (CompletedEnveloping Φ hΦ hΦs a)
          (if m + n = 0 then ((m ^ 3 - m) / 6 : ℤ) * (1 - 2 * a * c) * a * Φ x y else 0) := by
  have h₁ := ((hasSum_normalOrderedMode (Φ := Φ) (hΦ := hΦ) (hΦs := hΦs) (a := a) n x y).mul_left
    (sugawaraMode Φ hΦ hΦs a m)).sub
    ((hasSum_normalOrderedMode n x y).mul_right (sugawaraMode Φ hΦ hΦs a m))
  simp only [sugawaraMode_mul_normalOrderedSummand_sub_mul h] at h₁
  have hA₀ := (summable_smul_completedEnveloping
    (summable_normalOrderedSummand Φ hΦ hΦs a m (m + n) x y)
    (fun l : ℤ ↦ (1 - 2 * a * c) * -((l - m : ℤ) : K))).hasSum
  have hA : HasSum (fun j : ℤ ↦ ((1 - 2 * a * c) * -(j : K)) •
      toC (normalOrderedSummand Φ hΦ hΦs a m (m + n) (j + m) x y))
      (∑' l : ℤ, ((1 - 2 * a * c) * -((l - m : ℤ) : K)) •
        toC (normalOrderedSummand Φ hΦ hΦs a m (m + n) l x y)) := by
    simpa only [Function.comp_def, Equiv.coe_addRight, add_sub_cancel_right] using
      (Equiv.addRight m).hasSum_iff.2 hA₀
  have hB := (summable_smul_completedEnveloping
    (summable_normalOrderedSummand Φ hΦ hΦs a 0 (m + n) x y)
    (fun l : ℤ ↦ (1 - 2 * a * c) * (l - n : K))).hasSum
  have hcomb := hA₀.add hB
  simp only [combined_normalOrderedSummand_eq] at hcomb
  let g (l : ℤ) : UK := ((m - l : ℤ) : K) • (ι[x, l] * ι[y, m + n - l] - ι[y, m + n - l] * ι[x, l])
  have h₂ := (((hasSum_normalOrderedMode (Φ := Φ) (hΦ := hΦ) (hΦs := hΦs) (a := a)
      (m + n) x y).const_smul ((1 - 2 * a * c) * (m - n : K))).add
    ((hasSum_toCompletedEnveloping_ite_mem (Finset.Ico 0 m) g).const_smul (1 - 2 * a * c))).sub
    ((hasSum_toCompletedEnveloping_ite_mem (Finset.Ico m 0) g).const_smul (1 - 2 * a * c))
  rw [h₁.unique (hA.add hB), hcomb.unique h₂, add_sub_assoc, ← smul_sub, ← map_sub,
    sum_Ico_sub_sum_Ico_sub_smul_envelopingι_mul_sub_mul, map_sub, map_smul, smul_sub, smul_smul,
    AlgHom.commutes]
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

`[Sₘ, Sₙ] = (1 - 2 a c) (m - n) S_{m+n} - δ_{m+n, 0} ((m ^ 3 - m) / 6) (1 - 2 a c) a c · dim L`. -/
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
    have hi (i) : Φ (b i) (killingDualBasis b i) = c := by
      rw [h, LinearMap.smul_apply, LinearMap.smul_apply, LieModule.traceForm_comm K L L,
        LinearMap.BilinForm.apply_dualBasis_left hnd b i i]
      simp
    simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm c]
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
`2` and `3` are invertible: if `Φ = c • κ_L` and `1 - 2 a c ≠ 0`, then

`[Lₘ, Lₙ] = (m - n) L_{m+n} + δ_{m+n, 0} ((m ^ 3 - m) / 12) c_{Vir}`. -/
theorem sugawaraVirasoro_mul_sugawaraVirasoro_sub_mul [NeZero (2 : K)] [NeZero (3 : K)] {c : K}
    (h : Φ = c • killingForm K L) (hc : 1 - 2 * a * c ≠ 0) (m n : ℤ) :
    sugawaraVirasoro Φ hΦ hΦs a c m * sugawaraVirasoro Φ hΦ hΦs a c n -
        sugawaraVirasoro Φ hΦ hΦs a c n * sugawaraVirasoro Φ hΦ hΦs a c m =
      (m - n : K) • sugawaraVirasoro Φ hΦ hΦs a c (m + n) +
        algebraMap K (CompletedEnveloping Φ hΦ hΦs a)
          (if m + n = 0 then ((m : K) ^ 3 - m) / 12 * sugawaraCentralCharge K L a c else 0) := by
  have h2 : (2 : K) ≠ 0 := NeZero.ne (2 : K)
  have h3 : (3 : K) ≠ 0 := NeZero.ne (3 : K)
  have h6 : (6 : K) ≠ 0 := by
    have h23 : (2 : K) * 3 ≠ 0 := mul_ne_zero h2 h3
    norm_num at h23
    exact h23
  have hdiv6 : (((m ^ 3 - m) / 6 : ℤ) : K) = ((m : K) ^ 3 - m) / 6 := by
    refine eq_div_of_mul_eq h6 ?_
    have hZ : ((m ^ 3 - m) / 6 : ℤ) * 6 = m ^ 3 - m := by
      have h6Z := Finset.six_mul_sum_Ico_zero_mul_sub_sub_sum_Ico_zero_mul_sub m
      have hq := Int.eq_ediv_of_mul_eq_right (by decide : (6 : ℤ) ≠ 0) h6Z
      linear_combination h6Z - 6 * hq
    have hZK := congrArg (Int.cast : ℤ → K) hZ
    push_cast at hZK
    exact hZK
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
        have h26 : (2 : K) * 6 ≠ 0 := mul_ne_zero h2 h6
        norm_num at h26
        exact h26
      field_simp
      ring
    · simp
  rw [hlin, sub_eq_add_neg, ← neg_smul, hcent]

end Virasoro

end TauCeti.CurrentAlgebra
