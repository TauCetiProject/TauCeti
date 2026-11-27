/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import TauCeti.Data.ZMod.Count

/-!
# The discrete Fourier transform on `ZMod N`: bounds, reductions and integrality

For `v ∣ N`, a function `f` on `ZMod v` pulls back to `ZMod N` along the reduction
`j ↦ (j.val : ZMod v)`. Its discrete Fourier transform modulo `N` is supported on the multiples
of `L = N / v`, where it is `L` times the transform of `f` modulo `v`:
`𝓕 (f ∘ reduction) (L m) = L • 𝓕 f m`. At the multiples of `L` the additive characters modulo `N`
are those modulo `v`, and every fibre of the reduction has `L` elements. Off the multiples of `L`,
translating by `v`, which fixes the reduction, multiplies the transform by a nontrivial root of
unity, so the transform vanishes.

This is how the Fourier coefficients of a Dirichlet character modulo `v` appear in sums over the
residues modulo a multiple `N` of `v`.

The values of the standard additive character are `N`-th roots of unity, so the transform of a
function with values in a subring `R ⊆ ℂ` containing them again has its values in `R`.

## Main results

* `ZMod.norm_invDFT_le_of_forall_norm_le`: a pointwise bound on a function also bounds every
  coefficient of its inverse Fourier transform.
* `ZMod.stdAddChar_intCast_natCast_mul`: the additive character modulo `m n` at `n x` is the
  additive character modulo `m` at `x`.
* `ZMod.fourier_val_div_eq_stdAddChar`: the Fourier mode `n` at `j.val / N` on the circle is the
  standard additive character at `j * n`, and `ZMod.val_div_natCast_mem_Icc`: `j.val / N` lies in
  `[0, 1]`.
* `ZMod.dft_comp_natCast_val`: the transform of a function of the reduction modulo `v ∣ N`.
* `ZMod.dft_apply_mem`: the transform of an `R`-valued function is `R`-valued when `R` contains
  the `N`-th roots of unity.
* `ZMod.map_dft_of_comp_unitMul`: a cyclotomic coefficient map `σ` sends `𝓕 Φ k` to `𝓕 Ψ k`
  when `Ψ (d * j) = σ (Φ j)`.
-/

public section

namespace ZMod

/-- The normalized inverse discrete Fourier transform preserves uniform norm bounds. -/
theorem norm_invDFT_le_of_forall_norm_le {N : ℕ} [NeZero N] {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℂ E] {Φ : ZMod N → E} {C : ℝ}
    (hΦ : ∀ a, ‖Φ a‖ ≤ C) (k : ZMod N) : ‖𝓕⁻ Φ k‖ ≤ C := by
  rw [invDFT_apply]
  simp only [norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ a : ZMod N, ‖Φ a‖ := by
      gcongr
      simpa [norm_smul, AddChar.norm_apply] using
        norm_sum_le Finset.univ (fun a : ZMod N ↦ stdAddChar (a * k) • Φ a)
    _ ≤ (N : ℝ)⁻¹ * ∑ _a : ZMod N, C := by gcongr; exact hΦ _
    _ = C := by simp [ZMod.card, nsmul_eq_mul, NeZero.ne N]

variable {v N : ℕ} [NeZero v] [NeZero N] {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- **The standard additive character at a multiple.** The standard additive character modulo
`m n` at `n x` is the standard additive character modulo `m` at `x`: both are `e^(2π i x / m)`. -/
theorem stdAddChar_intCast_natCast_mul {m n : ℕ} [NeZero m] [NeZero n] (x : ℤ) :
    stdAddChar (((n * x : ℤ) : ZMod (m * n))) = stdAddChar (x : ZMod m) := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [stdAddChar_coe, stdAddChar_coe]
  congr 1
  push_cast
  field_simp

/-- The Fourier mode `n` at the residue representative `j.val / N` of the circle is the standard
additive character at `j * n`. -/
theorem fourier_val_div_eq_stdAddChar (j : ZMod N) (n : ℤ) :
    fourier n ((j.val / (N : ℝ) : ℝ) : UnitAddCircle) = stdAddChar (j * (n : ZMod N)) := by
  rw [fourier_coe_apply, stdAddChar_apply]
  have h := toCircle_intCast (N := N) (n * j.val)
  rw [Int.cast_mul, Int.cast_natCast, natCast_zmod_val, mul_comm] at h
  rw [h]
  push_cast
  congr 1
  ring

/-- The residue representative `j.val / N` lies in the unit interval. -/
theorem val_div_natCast_mem_Icc (j : ZMod N) : (j.val / (N : ℝ) : ℝ) ∈ Set.Icc 0 1 :=
  ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    (div_le_one (Nat.cast_pos.mpr (NeZero.pos N))).mpr (by exact_mod_cast (val_lt j).le)⟩

/-- **The Fourier transform of a function of the reduction modulo a divisor.** For `v ∣ N` and
`L = N / v`, the discrete Fourier transform modulo `N` of `j ↦ f (j mod v)` is `L • 𝓕 f m` at
`k = L m`, and vanishes at the `k` that are not multiples of `L`. -/
theorem dft_comp_natCast_val (hv : v ∣ N) (f : ZMod v → E) (k : ℤ) :
    𝓕 (fun j : ZMod N ↦ f (j.val : ZMod v)) (k : ZMod N) =
      if ((N / v : ℕ) : ℤ) ∣ k then (N / v) • 𝓕 f ((k / (N / v : ℕ) : ℤ) : ZMod v) else 0 := by
  set L := N / v
  have hN : N = v * L := (Nat.mul_div_cancel' hv).symm
  have hL : L ≠ 0 := fun h ↦ NeZero.ne N (by rw [hN, h, mul_zero])
  rw [dft_apply]
  split_ifs with hk
  · obtain ⟨m, rfl⟩ := hk
    rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hL), dft_apply,
      ← sum_comp_natCast_val hv]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    -- the character modulo `N` at `-j L m` is the character modulo `v` at `-j m`
    have h₁ : -(j * ((L * m : ℤ) : ZMod N)) = ((-((j.val : ℤ) * L * m) : ℤ) : ZMod N) := by
      push_cast
      rw [natCast_zmod_val]
      ring
    have h₂ : -(((j.val : ℕ) : ZMod v) * (m : ZMod v)) = ((-((j.val : ℤ) * m) : ℤ) : ZMod v) := by
      push_cast
      ring
    rw [h₁, h₂, stdAddChar_coe, stdAddChar_coe]
    congr 2
    have hv' : (v : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne v)
    have hL' : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hL
    have hN' : (N : ℂ) = v * L := by exact_mod_cast hN
    rw [hN']
    push_cast
    field_simp
  · -- translating by `v` fixes the reduction and multiplies the transform by `e(-v k / N) ≠ 1`
    set T : ZMod N → E := fun j ↦ stdAddChar (-(j * (k : ZMod N))) • f (j.val : ZMod v)
    have hred (j : ZMod N) : (((j + v).val : ℕ) : ZMod v) = (j.val : ZMod v) := by
      rw [natCast_val, natCast_val, cast_add hv, cast_natCast hv, natCast_self, add_zero]
    have hshift : ∑ j, T j = stdAddChar (-((v : ZMod N) * (k : ZMod N))) • ∑ j, T j := by
      rw [Finset.smul_sum]
      conv_lhs => rw [← Equiv.sum_comp (Equiv.addRight (v : ZMod N)) T]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [T, Equiv.coe_addRight, hred, smul_smul]
      rw [← AddChar.map_add_eq_mul]
      congr 2
      ring
    have hne : stdAddChar (-((v : ZMod N) * (k : ZMod N))) ≠ 1 := by
      intro h
      rw [← AddChar.map_zero_eq_one (stdAddChar (N := N)), injective_stdAddChar.eq_iff,
        neg_eq_zero] at h
      have h' : ((v * k : ℤ) : ZMod N) = 0 := by
        push_cast
        exact h
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hN, Nat.cast_mul] at h'
      exact hk ((mul_dvd_mul_iff_left (by exact_mod_cast NeZero.ne v)).mp h')
    have h0 : (1 - stdAddChar (-((v : ZMod N) * (k : ZMod N)))) • ∑ j, T j = 0 := by
      rw [sub_smul, one_smul, ← hshift, sub_self]
    exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne.symm)

/-- **Integrality of the discrete Fourier transform.** If a subring `R ⊆ ℂ` contains the `N`-th
roots of unity, the discrete Fourier transform of an `R`-valued function on `ZMod N` is
`R`-valued. -/
theorem dft_apply_mem {R : Subring ℂ} (hR : ∀ ζ : ℂ, ζ ^ N = 1 → ζ ∈ R) {Φ : ZMod N → ℂ}
    (hΦ : ∀ j, Φ j ∈ R) (k : ZMod N) : 𝓕 Φ k ∈ R := by
  rw [dft_apply]
  refine R.sum_mem fun j _ ↦ ?_
  rw [smul_eq_mul]
  refine R.mul_mem (hR _ ?_) (hΦ j)
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, natCast_self, zero_mul, AddChar.map_zero_eq_one]

omit [NeZero v] [AddCommGroup E] [Module ℂ E] in
/-- Let `σ` be a coefficient map with `σ (stdAddChar j) = stdAddChar (d * j)` for a unit `d`.
If the input `Ψ` is obtained from `Φ` by conjugating its values and moving the residue variable,
`Ψ (d * j) = σ (Φ j)`, then `σ (𝓕 Φ k) = 𝓕 Ψ k` at the same frequency `k`. No continuity of the
coefficient map is required. -/
theorem map_dft_of_comp_unitMul {σ : ℂ →+* ℂ} {d : (ZMod N)ˣ}
    (hσ : ∀ j : ZMod N, σ (stdAddChar j) = stdAddChar ((d : ZMod N) * j))
    {Φ Ψ : ZMod N → ℂ} (hΦ : ∀ j, Ψ ((d : ZMod N) * j) = σ (Φ j)) (k : ZMod N) :
    σ (𝓕 Φ k) = 𝓕 Ψ k := by
  have hmap : σ (𝓕 Φ k) = 𝓕 (fun j ↦ σ (Φ j)) ((d : ZMod N) * k) := by
    simp only [dft_apply, smul_eq_mul, map_sum, map_mul, hσ]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_neg, mul_left_comm]
  simp only [hmap, ← hΦ, dft_comp_unitMul, Units.inv_mul_cancel_left]

end ZMod
