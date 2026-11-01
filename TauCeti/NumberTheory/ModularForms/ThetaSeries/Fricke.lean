/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Scaling
public import TauCeti.NumberTheory.ModularForms.AtkinLehner.Normalizer
public import TauCeti.NumberTheory.ModularForms.Fricke.Matrix
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Inversion
import TauCeti.NumberTheory.ModularForms.Fricke.Operator
import TauCeti.NumberTheory.ModularForms.ThetaSeries.Functoriality

/-!
# Theta series under the Fricke matrix

Let `L` be a full lattice in a real inner product space `E` of even dimension `n = 2k`, and let
`N` be a positive integer. The Fricke matrix `W_N = !![0, -1; N, 0]` (`TauCeti.frickeGL ℝ N`)
acts on `ℍ` by `τ ↦ -1 / (N τ)`, the inversion `S` composed with the dilation `τ ↦ N τ`. The
inversion law of theta series at the point `N τ`, together with
`Θ_{L^∨}(N τ) = Θ_{√N • L^∨}(τ)`, gives the behaviour of `Θ_L` under `W_N`:
```text
Θ_L ∣[k] W_N = (-i)^k N^(k-1) (covol L)⁻¹ Θ_{√N • L^∨}
```
for Mathlib's weight-`k` slash, which carries the factor `(det W_N)^(k-1) = N^(k-1)`. Here
`(covol L)⁻¹ = (det L)^(-1/2)`. When `L` is even of level `N`, the lattice `√N • L^∨` is its
Fricke partner (`TauCeti/Algebra/Module/ZLattice/FrickePartner.lean`), again even with level
dividing `N`, so the Fricke matrix exchanges the theta series of a lattice and of its partner.
The identity itself needs neither evenness nor any relation between `N` and the level.

Since `√N • (√N • L^∨)^∨ = L`, the same law applied to `√N • L^∨` sends its theta series back to
a multiple of `Θ_L`, with constant `(-i)^k N⁻¹ covol L`. The product of the two constants is
`(-1)^k N^(k-2)`, the scalar `TauCeti.frickeScalar N k` by which `W_N²` acts.

The normalized Fricke operator `𝒲_N = (√N)^(2-k) • (· ∣[k] W_N)` of
`TauCeti/NumberTheory/ModularForms/Fricke/Normalized.lean` uses the constant
`TauCeti.atkinLehnerNormalizer N k = (√N)^(2-k)`. On theta series it gives
```text
(√N)^(2-k) • (Θ_L ∣[k] W_N) = (-i)^k (√N)^k (covol L)⁻¹ Θ_{√N • L^∨} .
```
These are statements about functions on `ℍ`: they do not presuppose that `Θ_L` is a modular form
of level `N`.

## Main statements

* `ZLattice.thetaSeries_slash_frickeGL`: the raw Fricke slash of `Θ_L`.
* `ZLattice.atkinLehnerNormalizer_smul_thetaSeries_slash_frickeGL`: its normalized form.
* `ZLattice.thetaSeries_sqrt_smul_dual_slash_frickeGL`: the Fricke slash of `Θ_{√N • L^∨}`.

## References

* B. Schoeneberg, *Elliptic Modular Functions*, Ch. IX.
* H. Iwaniec, *Topics in Classical Automorphic Forms*, AMS, 1997, Chapter 10.
-/

public section

open Complex Module TauCeti
open UpperHalfPlane (coe_pos_real_smul)
open scoped Real ModularForm Pointwise UpperHalfPlane

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  {k : ℕ} (N : ℕ) [NeZero N]

/-- **The Fricke transformation law of theta series**: if `dim E = 2k` and `N` is a positive
integer, then in weight `k`, `Θ_L ∣[k] W_N = (-i)^k N^(k-1) (covol L)⁻¹ Θ_{√N • L^∨}` for the
Fricke matrix `W_N = !![0, -1; N, 0]`. -/
theorem thetaSeries_slash_frickeGL (hk : finrank ℝ E = 2 * k) :
    thetaSeries L ∣[(k : ℤ)] frickeGL ℝ N =
      ((-I) ^ k * (N : ℂ) ^ ((k : ℤ) - 1) * (covolume L : ℂ)⁻¹) •
        thetaSeries (√(N : ℝ) • dual L) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hdet : 0 < (frickeGL ℝ N : Matrix (Fin 2) (Fin 2) ℝ).det := by
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using val_det_frickeGL_pos (K := ℝ) (N := N)
  -- The dilation by `(√N)² = N` turns `Θ_{L^∨}(N τ)` into `Θ_{√N • L^∨}(τ)`.
  have hr : (⟨√(N : ℝ) ^ 2, sq_pos_of_ne_zero (Real.sqrt_pos.mpr hN).ne'⟩ : {r : ℝ // 0 < r}) =
      ⟨N, hN⟩ := Subtype.ext (Real.sq_sqrt hN.le)
  ext τ
  have hden : UpperHalfPlane.denom (frickeGL ℝ N) τ = N * τ := by
    simp [UpperHalfPlane.denom]
  have hτ : ((N : ℂ) * τ) ^ k ≠ 0 :=
    pow_ne_zero k (mul_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne N)) τ.ne_zero)
  rw [ModularForm.slash_apply_of_det_pos _ hdet, frickeGL_smul_eq_S_smul,
    thetaSeries_S_smul L hk, Pi.smul_apply, thetaSeries_smul _ (Real.sqrt_pos.mpr hN).ne', hr]
  simp [hden, coe_pos_real_smul, abs_of_pos hN]
  field_simp

/-- **The normalized Fricke transformation law of theta series**: if `dim E = 2k` and `N` is a
positive integer, then `(√N)^(2-k) • (Θ_L ∣[k] W_N) = (-i)^k (√N)^k (covol L)⁻¹ Θ_{√N • L^∨}`.
The left side is the normalized Fricke operator `𝒲_N` applied to `Θ_L`. -/
theorem atkinLehnerNormalizer_smul_thetaSeries_slash_frickeGL (hk : finrank ℝ E = 2 * k) :
    atkinLehnerNormalizer N k • (thetaSeries L ∣[(k : ℤ)] frickeGL ℝ N) =
      ((-I) ^ k * (√(N : ℝ) : ℂ) ^ k * (covolume L : ℂ)⁻¹) •
        thetaSeries (√(N : ℝ) • dual L) := by
  have hs : ((√(N : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos N))).ne'
  rw [thetaSeries_slash_frickeGL L N hk, smul_smul, atkinLehnerNormalizer_def,
    natCast_eq_ofReal_sqrt_zpow_two, ← zpow_mul]
  congr 1
  have hpow : ((√(N : ℝ) : ℝ) : ℂ) ^ k =
      ((√(N : ℝ) : ℝ) : ℂ) ^ ((2 : ℤ) - k) * ((√(N : ℝ) : ℝ) : ℂ) ^ (2 * ((k : ℤ) - 1)) := by
    rw [← zpow_add₀ hs, ← zpow_natCast]
    congr 1
    ring
  rw [hpow]
  ring

/-- **The Fricke matrix sends the theta series of `√N • L^∨` back to `Θ_L`**: if `dim E = 2k`
and `N` is a positive integer, then in weight `k`,
`Θ_{√N • L^∨} ∣[k] W_N = (-i)^k N⁻¹ (covol L) Θ_L`. -/
theorem thetaSeries_sqrt_smul_dual_slash_frickeGL (hk : finrank ℝ E = 2 * k) :
    thetaSeries (√(N : ℝ) • dual L) ∣[(k : ℤ)] frickeGL ℝ N =
      ((-I) ^ k * (N : ℂ)⁻¹ * (covolume L : ℂ)) • thetaSeries L := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hs : 0 < √(N : ℝ) := Real.sqrt_pos.mpr hN
  have : NeZero √(N : ℝ) := ⟨hs.ne'⟩
  -- The dual of `√N • L^∨` is `(√N)⁻¹ • L`, so its Fricke partner is `L` itself.
  have hL : √(N : ℝ) • dual (√(N : ℝ) • dual L) = L := by
    rw [dual_smul _ hs.ne', dual_dual, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  have hcov : (covolume (√(N : ℝ) • dual L) : ℂ) = (N : ℂ) ^ k * (covolume L : ℂ)⁻¹ := by
    rw [covolume_smul (dual L) hs.ne' MeasureTheory.volume, covolume_dual, hk, abs_of_pos hs,
      pow_mul, Real.sq_sqrt hN.le]
    push_cast
    ring
  have hc : (covolume L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (covolume_pos L).ne'
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [thetaSeries_slash_frickeGL _ N hk, hL, hcov]
  congr 1
  rw [zpow_sub₀ hN', zpow_natCast, zpow_one]
  field_simp

end ZLattice
