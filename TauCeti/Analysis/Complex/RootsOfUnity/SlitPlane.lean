/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Convex
public import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.RingTheory.RootsOfUnity.PowFiber

/-!
# Preimages of the principal cut `[1, ∞)` under `z ↦ z ^ m`

The principal domain `Ω = ℂ ∖ [1, ∞)` of functions with a branch cut along `[1, ∞)`—such as
`-Log (1 - z)` and the principal polylogarithms—is `{z : ℂ | 1 - z ∈ Complex.slitPlane}`. Under
the `m`-th power map `z ↦ z ^ m` (`m ≥ 1`), a point `z` lands on the cut `[1, ∞)` if and only if
`z ^ m = r` for some real `r ≥ 1`; taking `s = r ^ (1 / m) ≥ 1`, the fibres of `u ↦ u ^ m`
(`TauCeti.pow_eq_pow_iff_exists_rootsOfUnity_smul`) show that this happens precisely when `ζ * z`
lies on `[1, ∞)` for some `m`-th root of unity `ζ`.

Consequently, for `m > 0`, `1 - z ^ m ∈ Complex.slitPlane` is equivalent to requiring
`1 - ζ * z ∈ Complex.slitPlane` for every `m`-th root of unity `ζ` (equivalently, for the `m`
rotates `ζ ^ j * z` by a primitive `m`-th root `ζ`, or `exp (2 * π * I * j / m) * z` for
`j < m`). Thus the `m`-ray star-slit domain `Ω_m = ⋂_{j < m} ζ_j⁻¹ Ω` is literally the pullback
`(· ^ m) ⁻¹' Ω`; it is open, star-convex about `0`, and connected for `m > 0`.

## Main declarations

* `Complex.one_sub_pow_mem_slitPlane_iff`: for `0 < m`, `1 - z ^ m ∈ slitPlane` iff
  `1 - ζ * z ∈ slitPlane` for all `ζ` with `ζ ^ m = 1`.
* `IsPrimitiveRoot.one_sub_pow_mem_slitPlane_iff`: primitive-root formulation over
  `j ∈ Finset.range m`.
* `Complex.one_sub_pow_mem_slitPlane_iff_forall_exp`,
  `Complex.setOf_forall_exp_one_sub_mem_slitPlane`: standard exponential-root formulation over
  `j ∈ Finset.range m` and identification of the `m`-ray domain with `{z | 1 - z ^ m ∈ slitPlane}`.
* `Complex.isOpen_one_sub_pow_slitPlane`, `Complex.starConvex_zero_one_sub_pow_slitPlane`,
  `Complex.isConnected_one_sub_pow_slitPlane`: openness, star-convexity at `0`, and connectedness
  of `{z : ℂ | 1 - z ^ m ∈ slitPlane}`.
-/

public section

namespace Complex

/-- For `0 < m`, `1 - z ^ m` lies in the slit plane if and only if `1 - ζ * z` lies in the slit
plane for every `m`-th root of unity `ζ`. Geometrically, the preimage of `[1, ∞)` under `z ↦ z ^ m`
is the union of the `m` rays `ζ⁻¹ · [1, ∞)`. -/
theorem one_sub_pow_mem_slitPlane_iff {m : ℕ} (hm : 0 < m) {z : ℂ} :
    1 - z ^ m ∈ slitPlane ↔ ∀ ζ : ℂ, ζ ^ m = 1 → 1 - ζ * z ∈ slitPlane := by
  refine ⟨fun hz ζ hζ => ?_, fun hz => ?_⟩
  · by_contra hnot
    rw [mem_slitPlane_iff, not_or, not_lt, not_ne_iff] at hnot
    obtain ⟨hre, him⟩ := hnot
    let r : ℝ := (ζ * z).re
    have hζz_re : 1 ≤ r := by
      simp only [sub_re, one_re] at hre
      linarith
    have hζz_im : (ζ * z).im = 0 := by
      simp only [sub_im, one_im] at him
      linarith
    have hζz_eq : ζ * z = (r : ℂ) := Complex.ext rfl hζz_im
    have hzm : z ^ m = ((r ^ m : ℝ) : ℂ) := by
      calc
        z ^ m = (ζ * z) ^ m := by rw [mul_pow, hζ, one_mul]
        _ = (r : ℂ) ^ m := by rw [hζz_eq]
        _ = ((r ^ m : ℝ) : ℂ) := by rw [ofReal_pow]
    have hpow_ge : 1 ≤ r ^ m := one_le_pow₀ hζz_re
    rcases mem_slitPlane_iff.mp hz with hpos | hne
    · rw [hzm, sub_re, one_re, ofReal_re] at hpos
      linarith
    · rw [hzm, sub_im, one_im, ofReal_im, sub_zero] at hne
      exact hne rfl
  · by_contra hnot
    rw [mem_slitPlane_iff, not_or, not_lt, not_ne_iff] at hnot
    obtain ⟨hre, him⟩ := hnot
    have hzm_re : 1 ≤ (z ^ m).re := by
      simp only [sub_re, one_re] at hre
      linarith
    have hzm_im : (z ^ m).im = 0 := by
      simp only [sub_im, one_im] at him
      linarith
    let s : ℝ := (z ^ m).re ^ (m⁻¹ : ℝ)
    have hs_ge : 1 ≤ s := Real.one_le_rpow hzm_re (by positivity)
    have hs_pow : s ^ m = (z ^ m).re := Real.rpow_inv_natCast_pow (by linarith) hm.ne'
    have hzm_eq : z ^ m = (s : ℂ) ^ m := by
      rw [← ofReal_pow, hs_pow]
      exact Complex.ext rfl hzm_im
    obtain ⟨ζ, hζz⟩ := (TauCeti.pow_eq_pow_iff_exists_rootsOfUnity_smul hm.ne').mp hzm_eq
    rw [rootsOfUnity.smul_eq_mul] at hζz
    have hζ_pow : ((ζ : ℂˣ) : ℂ) ^ m = 1 := (mem_rootsOfUnity' m _).mp ζ.2
    have hmem := hz ((ζ : ℂˣ) : ℂ) hζ_pow
    rw [hζz] at hmem
    rcases mem_slitPlane_iff.mp hmem with hpos | hne
    · rw [sub_re, one_re, ofReal_re] at hpos
      linarith
    · rw [sub_im, one_im, ofReal_im, sub_zero] at hne
      exact hne rfl

/-- If `1 - ζ * z` lies in the slit plane for every `m`-th root of unity `ζ` (`0 < m`), then
`1 - z ^ m` lies in the slit plane. -/
theorem one_sub_pow_mem_slitPlane {m : ℕ} (hm : 0 < m) {z : ℂ}
    (hz : ∀ ζ : ℂ, ζ ^ m = 1 → 1 - ζ * z ∈ slitPlane) : 1 - z ^ m ∈ slitPlane :=
  (one_sub_pow_mem_slitPlane_iff hm).mpr hz

end Complex

namespace IsPrimitiveRoot

/-- For a primitive `m`-th root of unity `ζ` (`0 < m`), `1 - z ^ m` lies in the slit plane iff
all `m` rotates `1 - ζ ^ j * z` (`j < m`) lie in the slit plane. -/
theorem one_sub_pow_mem_slitPlane_iff {m : ℕ} {ζ z : ℂ} (hζ : IsPrimitiveRoot ζ m) (hm : 0 < m) :
    1 - z ^ m ∈ Complex.slitPlane ↔
      ∀ j ∈ Finset.range m, 1 - ζ ^ j * z ∈ Complex.slitPlane := by
  have : NeZero m := ⟨hm.ne'⟩
  rw [Complex.one_sub_pow_mem_slitPlane_iff hm]
  refine ⟨fun h j _ => h (ζ ^ j) (by rw [pow_right_comm, hζ.pow_eq_one, one_pow]),
    fun h ξ hξ => ?_⟩
  obtain ⟨j, hj, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
  exact h j (Finset.mem_range.mpr hj)

/-- If all `m` rotates `1 - ζ ^ j * z` (`j < m`) by a primitive `m`-th root of unity lie in the
slit plane (`0 < m`), then `1 - z ^ m` lies in the slit plane. -/
theorem one_sub_pow_mem_slitPlane {m : ℕ} {ζ z : ℂ} (hζ : IsPrimitiveRoot ζ m) (hm : 0 < m)
    (hz : ∀ j ∈ Finset.range m, 1 - ζ ^ j * z ∈ Complex.slitPlane) :
    1 - z ^ m ∈ Complex.slitPlane :=
  (hζ.one_sub_pow_mem_slitPlane_iff hm).mpr hz

end IsPrimitiveRoot

namespace Complex

/-- For `0 < m`, `1 - z ^ m` lies in the slit plane iff `1 - exp (2 * π * I * j / m) * z` lies in
the slit plane for every `j < m`. -/
theorem one_sub_pow_mem_slitPlane_iff_forall_exp {m : ℕ} (hm : 0 < m) {z : ℂ} :
    1 - z ^ m ∈ slitPlane ↔
      ∀ j ∈ Finset.range m, 1 - exp (2 * Real.pi * I * j / m) * z ∈ slitPlane := by
  rw [(isPrimitiveRoot_exp m hm.ne').one_sub_pow_mem_slitPlane_iff hm]
  refine forall₂_congr fun j _ => ?_
  have hexp : exp (2 * Real.pi * I / m) ^ j = exp (2 * Real.pi * I * j / m) := by
    rw [← exp_nat_mul]
    congr 1
    ring
  rw [hexp]

/-- If `1 - exp (2 * π * I * j / m) * z` lies in the slit plane for every `j < m` (`0 < m`), then
`1 - z ^ m` lies in the slit plane. -/
theorem one_sub_pow_mem_slitPlane_of_forall_exp {m : ℕ} (hm : 0 < m) {z : ℂ}
    (hz : ∀ j ∈ Finset.range m, 1 - exp (2 * Real.pi * I * j / m) * z ∈ slitPlane) :
    1 - z ^ m ∈ slitPlane :=
  (one_sub_pow_mem_slitPlane_iff_forall_exp hm).mpr hz

/-- For `0 < m`, the `m`-ray star-slit domain cut out by the rotates `exp (2 * π * I * j / m) * z`
coincides with the pullback `{z : ℂ | 1 - z ^ m ∈ slitPlane}`. -/
theorem setOf_forall_exp_one_sub_mem_slitPlane {m : ℕ} (hm : 0 < m) :
    {z : ℂ | ∀ j ∈ Finset.range m, 1 - exp (2 * Real.pi * I * j / m) * z ∈ slitPlane} =
      {z : ℂ | 1 - z ^ m ∈ slitPlane} :=
  Set.ext fun _ => (one_sub_pow_mem_slitPlane_iff_forall_exp hm).symm

/-- The pullback `{z : ℂ | 1 - z ^ m ∈ slitPlane}` is open for every `m : ℕ`. -/
theorem isOpen_one_sub_pow_slitPlane (m : ℕ) : IsOpen {z : ℂ | 1 - z ^ m ∈ slitPlane} :=
  isOpen_slitPlane.preimage (continuous_const.sub (continuous_pow m))

/-- The pullback `{z : ℂ | 1 - z ^ m ∈ slitPlane}` is star-convex about `0` for every `m : ℕ`. -/
theorem starConvex_zero_one_sub_pow_slitPlane (m : ℕ) :
    StarConvex ℝ 0 {z : ℂ | 1 - z ^ m ∈ slitPlane} := by
  rw [starConvex_zero_iff]
  intro z hz a ha₀ ha₁
  rw [Set.mem_ofPred, real_smul, mul_pow, ← ofReal_pow, mul_comm ((a ^ m : ℝ) : ℂ)]
  exact one_sub_mul_ofReal_mem_slitPlane hz ⟨pow_nonneg ha₀ m, pow_le_one₀ ha₀ ha₁⟩

/-- For `0 < m`, the `m`-ray star-slit domain `{z : ℂ | 1 - z ^ m ∈ slitPlane}` is connected. -/
theorem isConnected_one_sub_pow_slitPlane {m : ℕ} (hm : 0 < m) :
    IsConnected {z : ℂ | 1 - z ^ m ∈ slitPlane} := by
  have h0 : (0 : ℂ) ∈ {z : ℂ | 1 - z ^ m ∈ slitPlane} := by
    simp [zero_pow hm.ne', one_mem_slitPlane]
  exact ((starConvex_zero_one_sub_pow_slitPlane m).isPathConnected h0).isConnected

end Complex

-- At `m = 0` the positivity assumption `0 < m` cannot be dropped: `1 - 0 ^ 0 = 0 ∉ slitPlane`.
example : ¬ (1 - (0 : ℂ) ^ 0 ∈ Complex.slitPlane ↔
    ∀ ζ : ℂ, ζ ^ 0 = 1 → 1 - ζ * 0 ∈ Complex.slitPlane) := by
  simp [Complex.one_mem_slitPlane, Complex.zero_notMem_slitPlane]
