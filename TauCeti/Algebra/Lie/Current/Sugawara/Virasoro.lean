/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Sugawara.Basic
public import TauCeti.Algebra.Lie.Killing.DualCoxeterNumber

import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.LinearAlgebra.BilinearForm.Basic

/-!
# The Segal--Sugawara Virasoro relations and central charge

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

Away from the critical level, dividing `Sₘ` by `1 - 2 a c` defines the **Segal--Sugawara Virasoro
modes** `Lₘ = (1 - 2 a c)⁻¹ Sₘ` (`TauCeti.CurrentAlgebra.sugawaraVirasoro`), which satisfy
`[Lₘ, z_k] = -k z_{m+k}` over any field and, when `2` and `3` are invertible in `K`, the Virasoro
commutation relations

`[Lₘ, Lₙ] = (m - n) L_{m+n} + δ_{m+n, 0} ((m ^ 3 - m) / 12) c_{Vir}`

with central charge `c_{Vir} = -(2 a c) / (1 - 2 a c) · dim L`
(`TauCeti.CurrentAlgebra.sugawaraCentralCharge`). For a simple Lie algebra in characteristic zero,
normalising `κ₀` by `κ_L = 2 h^∨ κ₀` at the affine level `Φ = -(k • κ₀)` and `a = 1` gives
`Lₘ = (2 (k + h^∨))⁻¹ ∑ᵢ :eᵢ e^i:_m` in any `κ₀`-dual basis and the Sugawara central charge
`k · dim L / (k + h^∨)`.

## Main definitions

* `TauCeti.CurrentAlgebra.sugawaraVirasoro`: the normalised Segal--Sugawara Virasoro modes
  `Lₘ = (1 - 2 a c)⁻¹ Sₘ`.
* `TauCeti.CurrentAlgebra.sugawaraCentralCharge`: the Sugawara central charge
  `-(2 a c) / (1 - 2 a c) · dim L`.

## Main results

* `TauCeti.CurrentAlgebra.limπ_sugawaraMode`, `TauCeti.CurrentAlgebra.limSmul_sugawaraMode`:
  finite-window formulas for the coordinates and smooth-module action of `Sₙ`.
* `TauCeti.CurrentAlgebra.levelCompletedEnvelopingEquiv_sugawaraMode`: compatibility with the
  completed level comparison, including at level zero.
* `TauCeti.CurrentAlgebra.sugawaraMode_eq_inv_smul_sum_dualBasis`: expansion of `Sₙ` along the dual
  basis of a rescaled invariant form.
* `TauCeti.CurrentAlgebra.sugawaraMode_mul_normalOrderedMode_sub_mul_of_eq_smul_killingForm`:
  commutator `[Sₘ, :x y:_n]` for `Φ = c • κ_L`.
* `TauCeti.CurrentAlgebra.sugawaraMode_mul_sugawaraMode_sub_mul_of_eq_smul_killingForm`:
  commutator `[Sₘ, Sₙ]` over an arbitrary field.
* `TauCeti.CurrentAlgebra.sugawaraVirasoro_mul_sugawaraVirasoro_sub_mul`: the Virasoro commutation
  relations of `Lₘ`.
* `TauCeti.CurrentAlgebra.sugawaraVirasoro_eq_sum_dualBasis_of_dualCoxeterNumber`,
  `TauCeti.CurrentAlgebra.sugawaraCentralCharge_of_dualCoxeterNumber`: the `κ₀`-dual-basis formula
  and central charge `k · dim L / (k + h^∨)` in terms of the dual Coxeter number.

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

/-! ### Coordinates, smooth action, rescaled forms and level comparison -/

section Basic

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]

section FixedForm

variable {Φ : LinearMap.BilinForm K L} {hΦ : Φ.lieInvariant L} {hΦs : Φ.IsSymm} {a : K}

local notation "UK" => CentralQuotient K (centralElement (twoCocycleOfBilinear K L Φ hΦ hΦs)) a

/-- **The coordinates of the Segal--Sugawara modes are finite sums.** Modulo `I_N`, `Sₙ` is
represented in any basis `b` by the summands of `:bᵢ b'ᵢ:_n` in the window
`min (n + 1 - N) 0 ≤ m < N`. -/
theorem limπ_sugawaraMode {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Module.Basis ι K L)
    (n : ℤ) (N : ℕ) :
    (orderQuotientTower Φ hΦ hΦs a).limπ N (sugawaraMode Φ hΦ hΦs a n) =
      ModuleTower.quotientsπ _ (orderLeftIdeal_natCast_antitone Φ hΦ hΦs a) N
        (∑ i, ∑ m ∈ Finset.Ico (min (n + 1 - N) 0) N,
          normalOrderedSummand Φ hΦ hΦs a 0 n m (b i) (killingDualBasis b i)) := by
  rw [sugawaraMode_eq_sum b, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ limπ_normalOrderedMode n (b i) (killingDualBasis b i) N

/-- **The action of a Segal--Sugawara mode on a smooth vector is a finite sum.** On a vector `v`
killed by `I_N`, `Sₙ` acts in any basis `b` by the summands with `min (n + 1 - N) 0 ≤ m < N`. -/
theorem limSmul_sugawaraMode {M : ModuleCat UK}
    (hM : smoothModules (fun n : ℕ ↦ orderLeftIdeal Φ hΦ hΦs a n) M)
    {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Module.Basis ι K L) (n : ℤ) {v : M} {N : ℕ}
    (hv : ∀ c ∈ orderLeftIdeal Φ hΦ hΦs a N, c • v = 0) :
    ModuleTower.limSmul hM (sugawaraMode Φ hΦ hΦs a n) v =
      ∑ i, ∑ m ∈ Finset.Ico (min (n + 1 - N) 0) N,
        normalOrderedSummand Φ hΦ hΦs a 0 n m (b i) (killingDualBasis b i) • v := by
  rw [ModuleTower.limSmul_eq_smul hM _ hv (limπ_sugawaraMode b n N).symm]
  simp only [Finset.sum_smul]

/-- **Expansion of the Segal--Sugawara modes along a rescaled bilinear form.** If `κ_L = d • B` for
a nondegenerate form `B` and `d ≠ 0`, then `Sₙ = d⁻¹ • ∑ᵢ :bᵢ b^i:_n`, where `b^i` is the basis
dual to `b` under `B`. -/
theorem sugawaraMode_eq_inv_smul_sum_dualBasis {B : LinearMap.BilinForm K L}
    (hB : B.Nondegenerate) {d : K} (hd : d ≠ 0) (h : killingForm K L = d • B)
    {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Module.Basis ι K L) (n : ℤ) :
    sugawaraMode Φ hΦ hΦs a n =
      d⁻¹ • ∑ i, normalOrderedMode Φ hΦ hΦs a n (b i) (B.dualBasis hB b i) := by
  have hcongr (B₁ B₂ : LinearMap.BilinForm K L) (h₁ : B₁.Nondegenerate) (h₂ : B₂.Nondegenerate)
      (heq : B₁ = B₂) (i : ι) : B₁.dualBasis h₁ b i = B₂.dualBasis h₂ b i := by
    subst heq
    rfl
  rw [sugawaraMode_eq_sum b, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [killingDualBasis, hcongr _ (d • B) _
    ((TauCeti.BilinForm.nondegenerate_smul_iff (IsRegular.of_ne_zero hd)).mpr hB) h,
    b.dualBasis_smul_apply B hB d hd i, map_smul]

end FixedForm

/-- **The completed level comparison preserves the Segal--Sugawara modes.** If `Ψ = k • Φ`, the
completed level comparison from `Û(ĝ_Ψ)` at central value `1` to `Û(ĝ_Φ)` at central value `k`
sends `Sₙ` to `Sₙ`, for every `k : K`, including `k = 0`. -/
@[simp]
theorem levelCompletedEnvelopingEquiv_sugawaraMode {Φ Ψ : LinearMap.BilinForm K L}
    (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm)
    {k : K} (h : Ψ = k • Φ) (n : ℤ) :
    levelCompletedEnvelopingEquiv hΦ hΦs hΨ hΨs h (sugawaraMode Ψ hΨ hΨs 1 n) =
      sugawaraMode Φ hΦ hΦs k n := by
  rw [sugawaraMode_eq_sum (Module.finBasis K L), sugawaraMode_eq_sum (Module.finBasis K L), map_sum]
  simp only [levelCompletedEnvelopingEquiv_normalOrderedMode]

end Basic

/-! ### Commutator of Segal--Sugawara modes -/

section Commutator

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  {Φ : LinearMap.BilinForm K L} {hΦ : Φ.lieInvariant L} {hΦs : Φ.IsSymm} {a : K}

local notation "UK" => CentralQuotient K (centralElement (twoCocycleOfBilinear K L Φ hΦ hΦs)) a

local notation "ι[" x ", " m "]" =>
  envelopingι (twoCocycleOfBilinear K L Φ hΦ hΦs) a (HahnSeries.single m (1 : K) ⊗ₜ[K] x)

local notation "toC" => toCompletedEnveloping Φ hΦ hΦs a

/-- **The commutator `[Sₘ, z_k]` for a multiple of the Killing form.** If `Φ = c • κ_L`, then
`[Sₘ, z_k] = -k (1 - 2 a c) z_{m+k}`. -/
theorem sugawaraMode_mul_toCompletedEnveloping_sub_mul_of_eq_smul_killingForm {c : K}
    (h : Φ = c • killingForm K L) (z : L) (m k : ℤ) :
    sugawaraMode Φ hΦ hΦs a m * toC ι[z, k] - toC ι[z, k] * sugawaraMode Φ hΦ hΦs a m =
      (-((1 - 2 * a * c) * (k : K))) • toC ι[z, m + k] := by
  have hcomm := toCompletedEnveloping_mul_sugawaraMode_sub_mul_of_eq_smul_killingForm
    (hΦ := hΦ) (hΦs := hΦs) (a := a) h z k m
  calc sugawaraMode Φ hΦ hΦs a m * toC ι[z, k] - toC ι[z, k] * sugawaraMode Φ hΦ hΦs a m
      = -(toC ι[z, k] * sugawaraMode Φ hΦ hΦs a m - sugawaraMode Φ hΦ hΦs a m * toC ι[z, k]) := by
        abel
    _ = (-((1 - 2 * a * c) * (k : K))) • toC ι[z, m + k] := by
        rw [hcomm, ← neg_smul]
        congr 1
        ring

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
  have hL (u v w : CompletedEnveloping Φ hΦ hΦs a) :
      u * (v * w) - v * w * u = (u * v - v * u) * w + v * (u * w - w * u) := by
    simp only [mul_sub, sub_mul, mul_assoc]
    abel
  have hsub₁ : m + n - (j + m) = n - j := by ring
  have hsub₂ : m + (n - j) = m + n - j := by ring
  have hadd : m + j = j + m := add_comm m j
  have hlt : j + m < m ↔ j < 0 := by omega
  simp only [normalOrderedSummand_apply, hsub₁, hlt]
  by_cases hj : j < 0 <;> simp only [hj, ↓reduceIte, map_mul] <;>
  · rw [hL, sugawaraMode_mul_toCompletedEnveloping_sub_mul_of_eq_smul_killingForm h,
      sugawaraMode_mul_toCompletedEnveloping_sub_mul_of_eq_smul_killingForm h, hadd, hsub₂]
    simp only [Int.cast_sub, smul_mul_assoc, mul_smul_comm]
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
      (m - l) • ι[⁅x, y⁆, m + n] + (-(l * (m - l))) •
        algebraMap K UK (if m + n = 0 then a * Φ x y else 0) := by
    rw [envelopingι_single_tmul_mul_sub_mul, add_sub_cancel, smul_add, Int.cast_smul_eq_zsmul]
    congr 1
    split_ifs with hmn
    · rw [hmn, zero_sub, ← map_zsmul, Algebra.smul_def, ← map_mul]
      congr 1
      simp only [zsmul_eq_mul]
      push_cast
      ring
    · simp
  simp only [hl, Finset.sum_add_distrib, ← Finset.sum_smul]
  have hcard : ((Finset.Ico 0 m).card : ℤ) - (Finset.Ico m 0).card = m := by
    simp only [Int.card_Ico]
    omega
  have hs₁ : ∑ l ∈ Finset.Ico 0 m, (m - l) - ∑ l ∈ Finset.Ico m 0, (m - l) =
      m * (m + 1) / 2 := by
    have h2s : 2 * (∑ l ∈ Finset.Ico 0 m, (m - l) - ∑ l ∈ Finset.Ico m 0, (m - l)) =
        m * (m + 1) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
        nsmul_eq_mul, nsmul_eq_mul]
      linear_combination 2 * m * hcard - Finset.two_mul_sum_Ico_zero_sub_sum_Ico_zero m
    exact Int.eq_ediv_of_mul_eq_right two_ne_zero h2s
  have hs₂ : ∑ l ∈ Finset.Ico 0 m, -(l * (m - l)) - ∑ l ∈ Finset.Ico m 0, -(l * (m - l)) =
      -((m ^ 3 - m) / 6) := by
    rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib, ← Int.eq_ediv_of_mul_eq_right
      (by decide : (6 : ℤ) ≠ 0) (Finset.six_mul_sum_Ico_zero_mul_sub_sub_sum_Ico_zero_mul_sub m)]
    ring
  have hw : algebraMap K UK (if m + n = 0 then ((m ^ 3 - m) / 6 : ℤ) * a * Φ x y else 0) =
      ((m ^ 3 - m) / 6 : ℤ) • algebraMap K UK (if m + n = 0 then a * Φ x y else 0) := by
    split_ifs <;> simp [zsmul_eq_mul, mul_assoc]
  have key (c₀ c₁ s₀ s₁ M : ℤ) (v w : UK) (hc : c₀ - c₁ = m * (m + 1) / 2) (hs : s₀ - s₁ = -M) :
      c₀ • v + s₀ • w - (c₁ • v + s₁ • w) = (m * (m + 1) / 2) • v - M • w := by
    rw [← hc, show M = -(s₀ - s₁) by omega]
    simp only [sub_smul, neg_smul]
    abel
  rw [hw, Int.cast_smul_eq_zsmul]
  exact key _ _ _ _ _ _ _ hs₁ hs₂

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
  have hcut : normalOrderedSummand Φ hΦ hΦs a m (m + n) l x y =
      normalOrderedSummand Φ hΦ hΦs a 0 (m + n) l x y +
        (if l ∈ Finset.Ico 0 m then
          ι[x, l] * ι[y, m + n - l] - ι[y, m + n - l] * ι[x, l] else 0) -
        (if l ∈ Finset.Ico m 0 then
          ι[x, l] * ι[y, m + n - l] - ι[y, m + n - l] * ι[x, l] else 0) := by
    simp only [normalOrderedSummand_apply, Finset.mem_Ico]
    split_ifs <;> first | omega | abel
  rw [hcut, map_sub, map_add, smul_sub, smul_add]
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

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
private theorem summable_smul_completedEnveloping {f : ℤ → CompletedEnveloping Φ hΦ hΦs a}
    (hf : Summable f) (r : ℤ → K) : Summable fun l ↦ r l • f l := by
  simpa only [algebraMap_smul] using
    (orderQuotientTower Φ hΦ hΦs a).summable_smul hf fun l ↦ algebraMap K UK (r l)

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
private theorem hasSum_smul_completedEnveloping {f : ℤ → CompletedEnveloping Φ hΦ hΦs a}
    {s : CompletedEnveloping Φ hΦ hΦs a} (hf : HasSum f s) (r : K) :
    HasSum (fun l ↦ r • f l) (r • s) := by
  simpa only [← Algebra.smul_def] using
    hf.mul_left (algebraMap K (CompletedEnveloping Φ hΦ hΦs a) r)

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
private theorem hasSum_ite_mem_completedEnveloping (s : Finset ℤ) (g : ℤ → UK) (r : K) :
    HasSum (fun l : ℤ ↦ r • toC (if l ∈ s then g l else 0))
      (r • toC (∑ l ∈ s, g l)) := by
  have hs : HasSum (fun l : ℤ ↦ toC (if l ∈ s then g l else 0))
      (∑ l ∈ s, toC (if l ∈ s then g l else 0)) :=
    hasSum_sum_of_ne_finset_zero fun l hl ↦ by simp [hl]
  rw [← map_sum, Finset.sum_ite_mem, Finset.inter_self] at hs
  exact hasSum_smul_completedEnveloping hs r

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
  have h₂ := ((hasSum_smul_completedEnveloping (hasSum_normalOrderedMode (Φ := Φ) (hΦ := hΦ)
    (hΦs := hΦs) (a := a) (m + n) x y) ((1 - 2 * a * c) * (m - n : K))).add
    (hasSum_ite_mem_completedEnveloping (Finset.Ico 0 m) g (1 - 2 * a * c))).sub
    (hasSum_ite_mem_completedEnveloping (Finset.Ico m 0) g (1 - 2 * a * c))
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

/-! ### Normalised Segal--Sugawara Virasoro operators and central charge -/

section Virasoro

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (Φ : LinearMap.BilinForm K L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : K)

/-- **The normalised Segal--Sugawara Virasoro modes** `Lₘ = (1 - 2 a c)⁻¹ Sₘ` in `Û`, attached to
`Φ = c • κ_L` away from the critical level `1 - 2 a c = 0`. -/
def sugawaraVirasoro (c : K) (m : ℤ) : CompletedEnveloping Φ hΦ hΦs a :=
  (1 - 2 * a * c)⁻¹ • sugawaraMode Φ hΦ hΦs a m

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
variable (K L) in
/-- **The Sugawara central charge** `c_{Vir} = -(2 a c) / (1 - 2 a c) · dim L` of the Virasoro
algebra generated by `sugawaraVirasoro` for `Φ = c • κ_L` at central value `a`. For the affine
level form `κ = -Φ` with `κ = k κ₀` and `κ_L = 2 h^∨ κ₀` at `a = 1`, this is
`k · dim L / (k + h^∨)`. -/
def sugawaraCentralCharge (a c : K) : K :=
  -(2 * a * c) / (1 - 2 * a * c) * (Module.finrank K L : K)

variable {Φ hΦ hΦs a}

/-- The normalised Segal--Sugawara Virasoro mode `Lₘ` is `(1 - 2 a c)⁻¹ • Sₘ`. -/
theorem sugawaraVirasoro_def (c : K) (m : ℤ) :
    sugawaraVirasoro Φ hΦ hΦs a c m = (1 - 2 * a * c)⁻¹ • sugawaraMode Φ hΦ hΦs a m :=
  (rfl)

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
variable (K L) in
/-- The Sugawara central charge is `-(2 a c) / (1 - 2 a c) · dim L`. -/
theorem sugawaraCentralCharge_def (a c : K) :
    sugawaraCentralCharge K L a c = -(2 * a * c) / (1 - 2 * a * c) * (Module.finrank K L : K) :=
  (rfl)

local notation "ιK[" x ", " m "]" =>
  toCompletedEnveloping Φ hΦ hΦs a
    (envelopingι (twoCocycleOfBilinear K L Φ hΦ hΦs) a (HahnSeries.single m (1 : K) ⊗ₜ[K] x))

/-- **The commutator of a normalised Segal--Sugawara Virasoro mode with a current mode**:
`[Lₘ, z_k] = -k z_{m+k}` whenever `Φ = c • κ_L` and `1 - 2 a c ≠ 0`. -/
theorem sugawaraVirasoro_mul_toCompletedEnveloping_sub_mul {c : K}
    (h : Φ = c • killingForm K L) (hc : 1 - 2 * a * c ≠ 0) (z : L) (m k : ℤ) :
    sugawaraVirasoro Φ hΦ hΦs a c m * ιK[z, k] - ιK[z, k] * sugawaraVirasoro Φ hΦ hΦs a c m =
      (-(k : K)) • ιK[z, m + k] := by
  rw [sugawaraVirasoro, smul_mul_assoc, mul_smul_comm, ← smul_sub,
    sugawaraMode_mul_toCompletedEnveloping_sub_mul_of_eq_smul_killingForm h, smul_smul]
  congr 1
  field_simp

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
    rw [show (6 : K) = 2 * 3 by norm_num]
    exact mul_ne_zero h2 h3
  have hdiv6 : (((m ^ 3 - m) / 6 : ℤ) : K) = ((m : K) ^ 3 - m) / 6 := by
    refine eq_div_of_mul_eq h6 ?_
    have hZ : ((m ^ 3 - m) / 6 : ℤ) * 6 = m ^ 3 - m := by
      have h6Z := Finset.six_mul_sum_Ico_zero_mul_sub_sub_sum_Ico_zero_mul_sub m
      have hq := Int.eq_ediv_of_mul_eq_right (by decide : (6 : ℤ) ≠ 0) h6Z
      linear_combination h6Z - 6 * hq
    have hZK := congrArg (Int.cast : ℤ → K) hZ
    push_cast at hZK
    exact hZK
  rw [sugawaraVirasoro, sugawaraVirasoro, sugawaraVirasoro, smul_mul_smul_comm, smul_mul_smul_comm,
    ← smul_sub, sugawaraMode_mul_sugawaraMode_sub_mul_of_eq_smul_killingForm h, smul_sub,
    smul_smul, smul_smul]
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
    · rw [hdiv6, sugawaraCentralCharge]
      have h12 : (12 : K) ≠ 0 := by
        rw [show (12 : K) = 2 * 6 by norm_num]
        exact mul_ne_zero h2 h6
      field_simp
      ring
    · simp
  rw [hlin, sub_eq_add_neg, ← neg_smul, hcent]

/-- **The completed level comparison preserves the normalised Segal--Sugawara Virasoro modes.** If
`Ψ = k • Φ`, then `Lₘ` at central value `1` for `Ψ = (k * c) • κ_L` maps to `Lₘ` at central value
`k` for `Φ = c • κ_L`. -/
@[simp]
theorem levelCompletedEnvelopingEquiv_sugawaraVirasoro {Ψ : LinearMap.BilinForm K L}
    (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm)
    {k : K} (h : Ψ = k • Φ) (c : K) (m : ℤ) :
    levelCompletedEnvelopingEquiv hΦ hΦs hΨ hΨs h (sugawaraVirasoro Ψ hΨ hΨs 1 (k * c) m) =
      sugawaraVirasoro Φ hΦ hΦs k c m := by
  simp only [sugawaraVirasoro, map_smul, levelCompletedEnvelopingEquiv_sugawaraMode,
    one_mul, mul_assoc]

/-! ### Normalised invariant forms and the dual Coxeter number -/

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
/-- **For a form `κ₀` with `κ_L = (2 d) • κ₀`, the affine level `Φ = -(k • κ₀)` at `a = 1` is
`(-k / (2 d)) • κ_L`.** -/
theorem eq_neg_div_two_mul_smul_killingForm [NeZero (2 : K)] {κ₀ : LinearMap.BilinForm K L}
    {d : K} (hd : d ≠ 0) (hκ₀ : killingForm K L = (2 * d) • κ₀) (k : K)
    (hΦk : Φ = -(k • κ₀)) :
    Φ = (-k / (2 * d)) • killingForm K L := by
  have h2 : (2 : K) ≠ 0 := NeZero.ne (2 : K)
  ext x y
  simp only [hΦk, hκ₀, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul]
  field_simp

/-- **Noncriticality in the affine normalisation**: `1 - 2 · 1 · (-k / (2 d)) ≠ 0` if and only if
`k + d ≠ 0`. -/
theorem one_sub_two_mul_neg_div_two_mul_ne_zero_iff [NeZero (2 : K)] {d : K} (hd : d ≠ 0)
    (k : K) :
    1 - 2 * (1 : K) * (-k / (2 * d)) ≠ 0 ↔ k + d ≠ 0 := by
  have h2 : (2 : K) ≠ 0 := NeZero.ne (2 : K)
  have heq : 1 - 2 * (1 : K) * (-k / (2 * d)) = (k + d) / d := by
    field_simp
    ring
  rw [heq, div_ne_zero_iff]
  exact and_iff_left hd

/-- **The `κ₀`-dual-basis formula for the Segal--Sugawara Virasoro modes.** If
`κ_L = (2 d) • κ₀`, then at `a = 1` and `c = -k / (2 d)`,

`Lₘ = (2 (k + d))⁻¹ • ∑ᵢ :bᵢ b^i:_m`

for every basis `b` of `L` and its `κ₀`-dual basis `b^i`. -/
theorem sugawaraVirasoro_eq_sum_dualBasis [NeZero (2 : K)] {κ₀ : LinearMap.BilinForm K L}
    (hκ₀nd : κ₀.Nondegenerate) {d : K} (hd : d ≠ 0) (hκ₀ : killingForm K L = (2 * d) • κ₀)
    (k : K) {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Module.Basis ι K L) (m : ℤ) :
    sugawaraVirasoro Φ hΦ hΦs 1 (-k / (2 * d)) m =
      (2 * (k + d))⁻¹ • ∑ i, normalOrderedMode Φ hΦ hΦs 1 m (b i) (κ₀.dualBasis hκ₀nd b i) := by
  have h2 : (2 : K) ≠ 0 := NeZero.ne (2 : K)
  rw [sugawaraVirasoro, sugawaraMode_eq_inv_smul_sum_dualBasis hκ₀nd (mul_ne_zero h2 hd) hκ₀ b m,
    smul_smul]
  congr 1
  field_simp
  ring

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
/-- **The Sugawara central charge in the `κ₀`-normalisation** is `k · dim L / (k + d)`. -/
theorem sugawaraCentralCharge_neg_div_two_mul [NeZero (2 : K)] {d : K} (hd : d ≠ 0) (k : K) :
    sugawaraCentralCharge K L 1 (-k / (2 * d)) = k * (Module.finrank K L : K) / (k + d) := by
  have h2 : (2 : K) ≠ 0 := NeZero.ne (2 : K)
  have hnum : -(2 * (1 : K) * (-k / (2 * d))) = k / d := by
    field_simp
  have hden : 1 - 2 * (1 : K) * (-k / (2 * d)) = (k + d) / d := by
    field_simp
    ring
  rw [sugawaraCentralCharge, hnum, hden, div_div_div_cancel_right₀ hd, div_mul_eq_mul_div]

section Simple

variable [CharZero K] [LieAlgebra.IsSimple K L] {H : LieSubalgebra K L}
  [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
  (bp : (LieAlgebra.IsKilling.rootSystem H).Base)

/-- **For a simple Lie algebra in characteristic zero, the Segal--Sugawara Virasoro modes in any
`κ₀`-dual basis are `(2 (k + h^∨))⁻¹ • ∑ᵢ :bᵢ b^i:_m`**, where `h^∨` is the dual Coxeter number
and `κ_L = 2 h^∨ κ₀`. -/
theorem sugawaraVirasoro_eq_sum_dualBasis_of_dualCoxeterNumber {κ₀ : LinearMap.BilinForm K L}
    (hκ₀nd : κ₀.Nondegenerate)
    (hκ₀ : killingForm K L = (2 * (bp.dualCoxeterNumber : K)) • κ₀) (k : K)
    {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Module.Basis ι K L) (m : ℤ) :
    sugawaraVirasoro Φ hΦ hΦs 1 (-k / (2 * (bp.dualCoxeterNumber : K))) m =
      (2 * (k + (bp.dualCoxeterNumber : K)))⁻¹ •
        ∑ i, normalOrderedMode Φ hΦ hΦs 1 m (b i) (κ₀.dualBasis hκ₀nd b i) :=
  sugawaraVirasoro_eq_sum_dualBasis hκ₀nd bp.cast_dualCoxeterNumber_ne_zero hκ₀ k b m

/-- **For a simple Lie algebra in characteristic zero, the Sugawara central charge at level `k` is
`k · dim L / (k + h^∨)`**, where `h^∨` is the dual Coxeter number. -/
theorem sugawaraCentralCharge_of_dualCoxeterNumber (k : K) :
    sugawaraCentralCharge K L 1 (-k / (2 * (bp.dualCoxeterNumber : K))) =
      k * (Module.finrank K L : K) / (k + (bp.dualCoxeterNumber : K)) :=
  sugawaraCentralCharge_neg_div_two_mul bp.cast_dualCoxeterNumber_ne_zero k

end Simple

end Virasoro

end TauCeti.CurrentAlgebra
