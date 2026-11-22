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
import TauCeti.Data.ZMod.FinEquiv

/-!
# The discrete Fourier transform on `ZMod N`: reductions and integrality

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

* `ZMod.stdAddChar_intCast_natCast_mul`: the additive character modulo `m n` at `n x` is the
  additive character modulo `m` at `x`.
* `ZMod.fourier_val_div_eq_stdAddChar`, `ZMod.fourier_natCast_div_eq_stdAddChar`: the Fourier mode
  at `j.val / N` or `i / N` on the circle is the standard additive character, and
  `ZMod.val_div_natCast_mem_Icc`: `j.val / N` lies in `[0, 1]`.
* `ZMod.ite_mod_eq_sum_fourier`: indicator of a residue class modulo `q > 0` as a finite Fourier sum
  of rational twists.
* `ZMod.tendsto_cesaro_ite_mod_of_fourier`: vanishing of rational Fourier twists modulo `q` implies
  vanishing of the masked Cesàro average on a residue class `r < q`.
* `ZMod.sum_fourier_div_eq`, `ZMod.sum_fourier_div_eq_zero`: evaluation of
  `∑ j < M, fourier k (j / M)` for any `M ≠ 0` and vanishing when `0 < |k| < M`.
* `ZMod.dft_comp_natCast_val`: the transform of a function of the reduction modulo `v ∣ N`.
* `ZMod.dft_apply_mem`: the transform of an `R`-valued function is `R`-valued when `R` contains
  the `N`-th roots of unity.
-/

public section

namespace ZMod

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

/-- Evaluating `fourier a` at `(i / b : ℝ)` on `UnitAddCircle` coincides with the standard additive
character on `ZMod b`. -/
theorem fourier_natCast_div_eq_stdAddChar {b : ℕ} [NeZero b] (a : ℤ) (i : ℕ) :
    fourier a (((i : ℝ) / (b : ℝ) : ℝ) : UnitAddCircle) =
      stdAddChar ((i : ZMod b) * (a : ZMod b)) := by
  rw [← AddCircle.coe_fract ((i : ℝ) / (b : ℝ)), Int.fract_div_natCast_eq_div_natCast_mod,
    ← val_natCast b i, fourier_val_div_eq_stdAddChar]

/-- Indicator of a residue class modulo `q > 0` expanded as a finite Fourier sum of rational
twists on `ZMod q`. -/
theorem ite_mod_eq_sum_fourier {q r : ℕ} [NeZero q] (hr : r < q) (i : ℕ) :
    (if i % q = r then (1 : ℂ) else 0) = (q : ℂ)⁻¹ * ∑ a : ZMod q,
      stdAddChar (-((r : ZMod q) * a)) *
        fourier (a.val : ℤ) (((i : ℝ) / q : ℝ) : UnitAddCircle) := by
  let δ : ZMod q → ℂ := Pi.single (r : ZMod q) 1
  have hinv := congrFun (dft.symm_apply_apply δ) (i : ZMod q)
  rw [invDFT_apply, (by simp [δ, Pi.single_apply, natCast_eq_natCast_iff',
    Nat.mod_eq_of_lt hr] : δ (i : ZMod q) = if i % q = r then 1 else 0), smul_eq_mul] at hinv
  simp_rw [(fun a : ZMod q ↦ by simp [dft_apply, δ, Pi.single_apply] :
    ∀ a : ZMod q, dft δ a = stdAddChar (-((r : ZMod q) * a))), smul_eq_mul] at hinv
  rw [← hinv]; congr 1; refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [mul_comm, fourier_natCast_div_eq_stdAddChar, Int.cast_natCast, natCast_zmod_val,
    mul_comm (a : ZMod q)]

/-- Vanishing of rational Fourier twists modulo `q` implies vanishing on the residue class `r < q`
for any complex sequence `b : ℕ → ℂ`. -/
theorem tendsto_cesaro_ite_mod_of_fourier {b : ℕ → ℂ} {q r : ℕ} [NeZero q] (hr : r < q)
    (h : ∀ a : ℤ, Filter.Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ i ∈ Finset.range (n + 1), b i * fourier a (((i : ℝ) / q : ℝ) : UnitAddCircle))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ •
        ∑ i ∈ Finset.range (n + 1), if i % q = r then b i else 0) Filter.atTop (nhds (0 : ℂ)) := by
  have hsum : Filter.Tendsto (fun n : ℕ ↦ (q : ℂ)⁻¹ * ∑ a : ZMod q,
      stdAddChar (-((r : ZMod q) * a)) * (((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ Finset.range (n + 1),
        b i * fourier (a.val : ℤ) (((i : ℝ) / q : ℝ) : UnitAddCircle))) Filter.atTop (nhds 0) := by
    have hsum' := (tendsto_const_nhds (x := (q : ℂ)⁻¹)).mul (tendsto_finsetSum Finset.univ fun a _ ↦
      by simpa only [mul_zero] using
        (tendsto_const_nhds (x := stdAddChar (-((r : ZMod q) * a)))).mul (h (a.val : ℤ)))
    rwa [Finset.sum_const_zero, mul_zero] at hsum'
  refine hsum.congr fun n ↦ ?_
  have hterm (i : ℕ) : (if i % q = r then b i else 0) =
      (q : ℂ)⁻¹ * ∑ a : ZMod q, stdAddChar (-((r : ZMod q) * a)) *
        (b i * fourier (a.val : ℤ) (((i : ℝ) / q : ℝ) : UnitAddCircle)) := by
    rw [(by split_ifs <;> simp :
      (if i % q = r then b i else 0) = (if i % q = r then (1 : ℂ) else 0) * b i),
      ite_mod_eq_sum_fourier hr i, mul_assoc, Finset.sum_mul]
    exact congrArg ((q : ℂ)⁻¹ * ·) (Finset.sum_congr rfl fun _ _ ↦ by ring)
  simp_rw [hterm, Complex.real_smul, ← Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.range (n + 1)) (t := Finset.univ), mul_left_comm _ (q : ℂ)⁻¹]
  simp only [Nat.cast_add, Nat.cast_one, Complex.ofReal_inv, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_one]
  congr 1; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ ↦ by rw [← Finset.mul_sum, mul_left_comm]

/-- Sum of an `M`-th root of unity over `0, …, M - 1` equals `M` when `M ∣ k` and `0` otherwise. -/
theorem sum_fourier_div_eq (k : ℤ) (M : ℕ) [NeZero M] :
    ∑ j ∈ Finset.range M, fourier k (((j : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle) =
      if (k : ZMod M) = 0 then (M : ℂ) else 0 := by
  simp_rw [fourier_natCast_div_eq_stdAddChar, ← Fin.sum_univ_eq_sum_range, ← finEquiv_apply]
  rw [Fintype.sum_equiv (finEquiv M).toEquiv
      (fun x : Fin M ↦ stdAddChar (finEquiv M x * (k : ZMod M)))
      (fun x : ZMod M ↦ stdAddChar (x * (k : ZMod M))) (fun _ ↦ rfl),
    AddChar.sum_mulShift (k : ZMod M) (isPrimitive_stdAddChar M), ZMod.card M]
  split_ifs <;> simp

/-- Sum of a nontrivial `M`-th root of unity over `0, …, M - 1` vanishes when `0 < |k| < M`. -/
theorem sum_fourier_div_eq_zero {k : ℤ} {M : ℕ} (hk : k ≠ 0) (hM : k.natAbs < M) :
    ∑ j ∈ Finset.range M, fourier k (((j : ℝ) / (M : ℝ) : ℝ) : UnitAddCircle) = 0 := by
  have : NeZero M := ⟨(Nat.zero_lt_of_lt hM).ne'⟩
  rw [sum_fourier_div_eq, ite_eq_right fun h0 ↦ ?_]
  rw [intCast_zmod_eq_zero_iff_dvd] at h0
  exact False.elim (Nat.not_lt.mpr (Nat.le_of_dvd (Int.natAbs_pos.mpr hk)
    (Int.natCast_dvd.mp h0)) hM)

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

end ZMod
