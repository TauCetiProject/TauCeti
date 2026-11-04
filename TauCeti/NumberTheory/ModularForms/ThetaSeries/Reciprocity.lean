/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Asymptotics
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# The reciprocity law for Gauss sums of an even lattice

Let `L` be an even lattice in a real inner product space `E` of even dimension `n = 2k`, and write
`e(x) = exp (2 π i x)`. For positive integers `a` and `c`, the Gauss sum
`G_L(a, c) = ∑_{y ∈ L/cL} e(a ‖y‖² / (2c))` (`ZLattice.gaussSum`) satisfies the **reciprocity law**

`G_L(a, c) = (c/a)^k (covol L)⁻¹ e(n/8) ∑_{y ∈ L^∨/aL} e(-c ‖y‖² / (2a))`,

which exchanges the modulus `c` and the coefficient `a` at the price of passing to the dual
lattice `L^∨`. Here `e(n/8) = i^k`, and `(covol L)⁻¹ = (det L)^{-1/2}` is the inverse square root
of the order of the discriminant group `L^∨/L`
(`ZLattice.IsIntegral.inv_covolume_eq_inv_sqrt_card_discriminantGroup`). No coprimality of `a` and
`c` is needed.

The proof is analytic. The behaviour of `t^k Θ_L(a/c + i t)` as `t → 0⁺` is computed in two ways.
Splitting `L` into its classes modulo `cL` gives the limit `G_L(a, c) / (c^{2k} covol L)`
(`ZLattice.IsEven.tendsto_pow_mul_thetaSeries_nhdsGT`). On the other hand, the inversion law
`Θ_L(z) = (covol L)⁻¹ (-i)^k (-1/z)^k Θ_{L^∨}(-1/z)` moves the point `z = a/c + i t` to
`-1/z = -c/a + ε`, where `ε = -1/w` with `w = -a/c + i a² / (c² t)`, so `ε` tends to the cusp `0`
with `im (-1/ε) → ∞`. Splitting `L^∨` into its classes modulo `aL` then gives the limit
`(a/c)^k i^k (∑_{y ∈ L^∨/aL} e(-c ‖y‖² / (2a))) / (a^{2k} covol(L)²)`, by the asymptotic
`ZLattice.IsEven.tendsto_pow_mul_thetaSeries_dual_vadd_comap_S`. Comparing the two limits gives
the law. The comparison is between limits of sums, not of their leading terms alone: `G_L(a, c)`
may vanish while `Θ_L(a/c + i t)` does not.

At `a = c = 1` the left side is `1`, and complex conjugation gives **Milgram's formula**
`∑_{γ ∈ L^∨/L} e(‖γ‖² / 2) = √|L^∨/L| · e(n/8)` for a positive definite even lattice.

## Main statements

* `ZLattice.IsEven.gaussSum_eq_mul_dualGaussSum`: the reciprocity law for the Gauss sums of an
  even lattice of even rank.
* `ZLattice.IsEven.dualGaussSum_one_one`: Milgram's formula.

## References

* B. Schoeneberg, *Elliptic Modular Functions*, Springer, 1974, Chapter IX.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Springer, 1973, Appendix 4.
-/

public section

open Complex Filter Module
open UpperHalfPlane (atImInfty coe_vadd modular_S_smul ofComplex ofComplex_apply_of_im_pos)
open scoped Pointwise Real Topology UpperHalfPlane

namespace ZLattice

namespace IsEven

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] {k : ℕ} (hL : IsEven L)
include hL

section Covolume

variable [MeasurableSpace E] [BorelSpace E]

/-- The point `w = -a/c + i a² / (c² t)` of `ℍ`, for `t > 0`. Its image `ε = -1/w` under `S`
satisfies `-1/(a/c + i t) = -c/a + ε`. -/
private noncomputable def recipPoint (a c : ℕ) (t : ℝ) : ℍ :=
  ofComplex (-((a : ℂ) / c) + I * ((a : ℂ) ^ 2 / (c ^ 2 * t)))

omit hL in
private theorem recipPoint_eq (a c : ℕ) (t : ℝ) :
    -((a : ℂ) / c) + I * ((a : ℂ) ^ 2 / (c ^ 2 * t)) =
      ((-(a / c) : ℝ) : ℂ) + I * (((a : ℝ) ^ 2 / (c ^ 2 * t) : ℝ) : ℂ) := by
  push_cast
  ring

omit hL in
private theorem coe_recipPoint {a c : ℕ} [NeZero a] [NeZero c] {t : ℝ} (ht : 0 < t) :
    (recipPoint a c t : ℂ) = -((a : ℂ) / c) + I * ((a : ℂ) ^ 2 / (c ^ 2 * t)) := by
  have ha : (0 : ℝ) < a := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne a))
  have hc : (0 : ℝ) < c := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne c))
  have him : 0 < (-((a : ℂ) / c) + I * ((a : ℂ) ^ 2 / (c ^ 2 * t))).im := by
    rw [recipPoint_eq]
    simp only [add_im, ofReal_im, mul_im, I_re, zero_mul, I_im, ofReal_re, one_mul, zero_add]
    positivity
  rw [recipPoint, ofComplex_apply_of_im_pos him, UpperHalfPlane.coe_mk]

omit hL in
/-- As `t → 0⁺`, the points `S • w` tend to the cusp `0`, since `im w = a² / (c² t) → ∞`. -/
private theorem tendsto_S_smul_recipPoint (a c : ℕ) [NeZero a] [NeZero c] :
    Tendsto (fun t : ℝ ↦ ModularGroup.S • recipPoint a c t) (𝓝[>] 0)
      (comap (ModularGroup.S • ·) atImInfty) := by
  have ha : (0 : ℝ) < a := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne a))
  have hc : (0 : ℝ) < c := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne c))
  rw [tendsto_comap_iff, UpperHalfPlane.atImInfty, tendsto_comap_iff]
  refine (tendsto_inv_nhdsGT_zero.const_mul_atTop (by positivity : 0 < (a : ℝ) ^ 2 / c ^ 2)).congr'
    ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [Function.comp_apply, Function.comp_apply, ModularGroup.S_smul_S_smul, UpperHalfPlane.im,
    coe_recipPoint ht, recipPoint_eq]
  simp only [add_im, ofReal_im, mul_im, I_re, zero_mul, I_im, ofReal_re, one_mul, zero_add]
  field_simp

omit hL in
/-- With `z = a/c + i t` and `w = -a/c + i a² / (c² t)`: `-1/z = -c/a - 1/w` and
`t (-1/z) = (i a / c) (-1/w)`. Both follow from `t w = (i a / c) z`. -/
private theorem neg_inv_eq {a c t : ℂ} (ha : a ≠ 0) (hc : c ≠ 0) (ht : t ≠ 0)
    (hq : a + I * c * t ≠ 0) :
    -(a / c + I * t)⁻¹ = -c / a + -(-(a / c) + I * (a ^ 2 / (c ^ 2 * t)))⁻¹ ∧
      t * -(a / c + I * t)⁻¹ = I * a / c * -(-(a / c) + I * (a ^ 2 / (c ^ 2 * t)))⁻¹ := by
  have hz : a / c + I * t = (a + I * c * t) / c := by field_simp
  have hw : -(a / c) + I * (a ^ 2 / (c ^ 2 * t)) = I * a / (c ^ 2 * t) * (a + I * c * t) := by
    field_simp
    linear_combination (-c * t) * I_sq
  rw [hz, hw]
  constructor
  · field_simp
    linear_combination (c * t) * I_sq
  · field_simp

omit hL in
/-- The point `-1/(a/c + i t)` is `-c/a + ε` with `ε = S • w`, and
`t (-1/(a/c + i t)) = (i a/c) ε`. -/
private theorem S_smul_ofComplex_eq {a c : ℕ} [NeZero a] [NeZero c] {t : ℝ} (ht : 0 < t) :
    ModularGroup.S • ofComplex ((a : ℂ) / c + I * t) =
        (((-(c : ℤ) : ℤ) : ℝ) / a) +ᵥ (ModularGroup.S • recipPoint a c t) ∧
      (t : ℂ) * (ModularGroup.S • ofComplex ((a : ℂ) / c + I * t) : ℍ) =
        I * a / c * (ModularGroup.S • recipPoint a c t : ℍ) := by
  have ha : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne a)
  have hc : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne c)
  have him : 0 < ((a : ℂ) / c + I * t).im := by simpa using ht
  -- `a + i c t` has real part `a ≠ 0`.
  have hq : (a : ℂ) + I * c * t ≠ 0 := fun h ↦ ha <| by
    simpa using congrArg re h
  obtain ⟨h₁, h₂⟩ := neg_inv_eq ha hc (ofReal_ne_zero.mpr ht.ne') hq
  have hS (z : ℍ) : ((ModularGroup.S • z : ℍ) : ℂ) = -(z : ℂ)⁻¹ := by
    rw [modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
  refine ⟨?_, ?_⟩
  · ext
    rw [coe_vadd, hS, hS, ofComplex_apply_of_im_pos him, UpperHalfPlane.coe_mk, coe_recipPoint ht,
      h₁]
    push_cast
    ring
  · rw [hS, hS, ofComplex_apply_of_im_pos him, UpperHalfPlane.coe_mk, coe_recipPoint ht, h₂]

/-- **The other side of the reciprocity law**: if `dim E = 2k`, then for positive integers `a` and
`c`, `t^k Θ_L(a/c + i t) → (a/c)^k (covol L)⁻¹ i^k S / (a^{2k} covol L)` as `t → 0⁺`, where
`S = ∑_{y ∈ L^∨/aL} e(-c ‖y‖² / (2a))`. -/
private theorem tendsto_pow_mul_thetaSeries_nhdsGT_dual (hk : finrank ℝ E = 2 * k) (a c : ℕ)
    [NeZero a] [NeZero c] [Fintype (dual L ⧸ ((a : ℝ) • L).submoduleOf (dual L))] :
    Tendsto (fun t : ℝ ↦ (t : ℂ) ^ k * thetaSeries L (ofComplex ((a : ℂ) / c + I * t)))
      (𝓝[>] 0)
      (𝓝 ((covolume L : ℂ)⁻¹ * ((a : ℂ) / c) ^ k *
        (I ^ k * dualGaussSum L hL (-(c : ℤ)) a / ((a : ℂ) ^ (2 * k) * covolume L)))) := by
  have h := ((tendsto_pow_mul_thetaSeries_dual_vadd_comap_S hL hk (-(c : ℤ)) a).comp
    (tendsto_S_smul_recipPoint a c)).const_mul ((covolume L : ℂ)⁻¹ * ((a : ℂ) / c) ^ k)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  obtain ⟨h₁, h₂⟩ := S_smul_ofComplex_eq (a := a) (c := c) ht
  have hI : -I * (I * a / c) = a / c := by
    have hc : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne c)
    field_simp
    linear_combination (-(a : ℂ)) * I_sq
  -- The inversion law at `S • z` for `z = a/c + i t`, with `-1/z = -c/a + ε` and
  -- `t (-1/z) = (i a/c) ε`.
  have hθ := thetaSeries_S_smul L hk (ModularGroup.S • ofComplex ((a : ℂ) / c + I * t))
  rw [ModularGroup.S_smul_S_smul] at hθ
  rw [Function.comp_apply, hθ, ← h₁]
  calc _ = (covolume L : ℂ)⁻¹ * ((-I * (I * a / c)) ^ k *
        ((ModularGroup.S • recipPoint a c t : ℍ) : ℂ) ^ k) *
        thetaSeries (dual L) (ModularGroup.S • ofComplex ((a : ℂ) / c + I * t)) := by
        rw [hI]; ring
    _ = (covolume L : ℂ)⁻¹ * ((-I) ^ k * ((t : ℂ) *
        (ModularGroup.S • ofComplex ((a : ℂ) / c + I * t) : ℍ)) ^ k) *
        thetaSeries (dual L) (ModularGroup.S • ofComplex ((a : ℂ) / c + I * t)) := by
        rw [h₂]; simp only [mul_pow]; ring
    _ = _ := by rw [mul_pow]; ring

/-- **The reciprocity law for the Gauss sums of an even lattice.** If `L` is an even lattice and
`dim E = 2k`, then for positive integers `a` and `c`,
`G_L(a, c) = (c/a)^k (covol L)⁻¹ i^k ∑_{y ∈ L^∨/aL} e(-c ‖y‖² / (2a))`.
Here `i^k = e(n/8)` for `n = 2k`, and `(covol L)⁻¹ = (det L)^{-1/2}`. -/
theorem gaussSum_eq_mul_dualGaussSum (hk : finrank ℝ E = 2 * k) (a c : ℕ) [NeZero a] [NeZero c]
    [Fintype (dual L ⧸ ((a : ℝ) • L).submoduleOf (dual L))] :
    gaussSum L hL a c =
      ((c : ℂ) / a) ^ k * (covolume L : ℂ)⁻¹ * I ^ k * dualGaussSum L hL (-(c : ℤ)) a := by
  have h₁ := tendsto_pow_mul_thetaSeries_nhdsGT hL hk a c
  have h₂ := tendsto_pow_mul_thetaSeries_nhdsGT_dual hL hk a c
  push_cast at h₁
  have h := tendsto_nhds_unique h₁ h₂
  have ha : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne a)
  have hc : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne c)
  have hcov : (covolume L : ℂ) ≠ 0 := ofReal_ne_zero.mpr (covolume_pos L).ne'
  rw [div_eq_iff (mul_ne_zero (pow_ne_zero _ hc) hcov)] at h
  rw [h, pow_mul, pow_mul, div_pow, div_pow]
  field_simp
  ring

end Covolume

/-- **Milgram's formula.** If `L` is an even lattice and `dim E = 2k`, then
`∑_{γ ∈ L^∨/L} e(‖γ‖² / 2) = √|L^∨/L| · i^k`, where `i^k = e(n/8)` for `n = 2k`. The left side
is written as a sum over `L^∨ / 1L`; `ZLattice.dualGaussSum_one` rewrites it as a sum over the
discriminant group `L^∨/L`. -/
theorem dualGaussSum_one_one (hk : finrank ℝ E = 2 * k)
    [Fintype (dual L ⧸ (((1 : ℕ) : ℝ) • L).submoduleOf (dual L))] :
    dualGaussSum L hL 1 1 = √(Nat.card (DiscriminantGroup L) : ℝ) * I ^ k := by
  -- The statement involves no measure; the reciprocity law uses the Borel volume.
  borelize E
  have h := gaussSum_eq_mul_dualGaussSum hL hk 1 1
  rw [gaussSum_one] at h
  have hcov : (covolume L : ℂ) ≠ 0 := ofReal_ne_zero.mpr (covolume_pos L).ne'
  have hsqrt : covolume L = √(Nat.card (DiscriminantGroup L) : ℝ) :=
    inv_injective (hL.isIntegral.inv_covolume_eq_inv_sqrt_card_discriminantGroup)
  -- At `a = c = 1` the law reads `1 = (covol L)⁻¹ i^k ∑_γ e(-‖γ‖² / 2)`; conjugate it.
  have h' : dualGaussSum L hL (-1) 1 = covolume L * (-I) ^ k := by
    rw [Nat.cast_one, div_one, one_pow, one_mul] at h
    have hI : I ^ k * (-I) ^ k = 1 := by rw [← mul_pow]; simp
    calc _ = (covolume L : ℂ) * (-I) ^ k * ((covolume L : ℂ)⁻¹ * I ^ k *
          dualGaussSum L hL (-1) 1) := by
          field_simp
          linear_combination (-(dualGaussSum L hL (-1) 1)) * hI
      _ = _ := by push_cast at h; rw [← h, mul_one]
  have hconj := conj_dualGaussSum hL (-1) 1
  rw [neg_neg, h', map_mul, conj_ofReal, map_pow, map_neg, conj_I, neg_neg] at hconj
  rw [← hconj, hsqrt]

end IsEven

end ZLattice
