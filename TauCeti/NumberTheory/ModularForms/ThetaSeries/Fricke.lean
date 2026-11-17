/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Scaling
public import TauCeti.NumberTheory.ModularForms.Fricke.Normalized
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.GeneralLevel
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Inversion
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
The function-level identities themselves need neither evenness nor any relation between `N` and
the level.

Since `√N • (√N • L^∨)^∨ = L`, the same law applied to `√N • L^∨` sends its theta series back to
a multiple of `Θ_L`, with constant `(-i)^k N⁻¹ covol L`. The product of the two constants is
`(-1)^k N^(k-2)`, the scalar `TauCeti.frickeScalar N k` by which `W_N²` acts.

The normalized Fricke operator `𝒲_N = (√N)^(2-k) • (· ∣[k] W_N)` of
`TauCeti/NumberTheory/ModularForms/Fricke/Normalized.lean` uses the constant
`TauCeti.atkinLehnerNormalizer N k = (√N)^(2-k)`. On theta series it gives
```text
(√N)^(2-k) • (Θ_L ∣[k] W_N) = (-i)^k (√N)^k (covol L)⁻¹ Θ_{√N • L^∨} .
```
Its square is `(-1)^k • id`, so `𝒲_N` is an involution only when the weight `k` is even; even rank
`n = 2k` does not force `k` to be even (for instance `A₂` has rank `2` and weight `k = 1`).

For an even full lattice `L` of rank `2k` and level `N = level L`, the level of the Fricke
partner `√N • L^∨` divides `N`, so its general-level theta form `thetaFormOfLevel` restricts to
`Γ₁(N)`. The bundled operators `TauCeti.frickeOperator` and `TauCeti.normalizedFrickeOperator`
exchange `thetaFormOfLevel` of `L` with this restriction of `thetaFormOfLevel` of `√N • L^∨`.
Because the theta character `χ_L` is quadratic (`χ_L⁻¹ = χ_L`), the restricted theta form of the
Fricke partner lies in the same nebentypus space `modFormCharSpace k χ_L`.

## Main statements

* `ZLattice.thetaSeries_slash_frickeGL`: the raw Fricke slash of `Θ_L`.
* `ZLattice.atkinLehnerNormalizer_smul_thetaSeries_slash_frickeGL`: its normalized form.
* `ZLattice.thetaSeries_sqrt_smul_dual_slash_frickeGL`,
  `ZLattice.atkinLehnerNormalizer_smul_thetaSeries_sqrt_smul_dual_slash_frickeGL`: the raw and
  normalized Fricke slash of `Θ_{√N • L^∨}`.
* `ZLattice.frickeOperator_thetaFormOfLevel`,
  `ZLattice.normalizedFrickeOperator_thetaFormOfLevel`: the raw and normalized Fricke operators on
  `thetaFormOfLevel`.
* `ZLattice.frickeOperator_restrict_thetaFormOfLevel_sqrt_level_smul_dual`,
  `ZLattice.normalizedFrickeOperator_restrict_thetaFormOfLevel_sqrt_level_smul_dual`: the return
  maps from the Fricke partner back to `thetaFormOfLevel`.
* `ZLattice.restrict_thetaFormOfLevel_sqrt_level_smul_dual_mem_modFormCharSpace`: the restricted
  theta form of the Fricke partner has the same nebentypus `χ_L` at level `N`.

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
    rw [covolume_smul (dual L) MeasureTheory.volume, covolume_dual, hk, abs_of_pos hs,
      pow_mul, Real.sq_sqrt hN.le]
    push_cast
    ring
  have hc : (covolume L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (covolume_pos L).ne'
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [thetaSeries_slash_frickeGL _ N hk, hL, hcov]
  congr 1
  rw [zpow_sub₀ hN', zpow_natCast, zpow_one]
  field_simp

/-- **The normalized Fricke operator sends the theta series of `√N • L^∨` back to `Θ_L`**: if
`dim E = 2k` and `N` is a positive integer, then
`(√N)^(2-k) • (Θ_{√N • L^∨} ∣[k] W_N) = (-i)^k (√N)^(-k) (covol L) Θ_L`. -/
theorem atkinLehnerNormalizer_smul_thetaSeries_sqrt_smul_dual_slash_frickeGL
    (hk : finrank ℝ E = 2 * k) :
    atkinLehnerNormalizer N k •
        (thetaSeries (√(N : ℝ) • dual L) ∣[(k : ℤ)] frickeGL ℝ N) =
      ((-I) ^ k * ((√(N : ℝ) : ℂ) ^ k)⁻¹ * (covolume L : ℂ)) • thetaSeries L := by
  have hs : ((√(N : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos N))).ne'
  rw [thetaSeries_sqrt_smul_dual_slash_frickeGL L N hk, smul_smul, atkinLehnerNormalizer_def,
    natCast_eq_ofReal_sqrt_zpow_two]
  congr 1
  rw [zpow_sub₀ hs, zpow_two, zpow_natCast]
  field_simp

section Bundled

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] {k : ℕ}

/-- On underlying functions, the raw Fricke operator `TauCeti.frickeOperator` carries
`thetaFormOfLevel` to `(-i)^k N^{k-1} |A_L|^{-1/2} Θ_{√N • L^∨}`, where `N = level L`. -/
theorem coe_frickeOperator_thetaFormOfLevel [NeZero (level L)] (hL : IsEven L)
    (hk : finrank ℝ E = 2 * k) :
    ⇑(frickeOperator (N := level L) (k : ℤ) (thetaFormOfLevel hL hk)) =
      ((-I) ^ k * (level L : ℂ) ^ ((k : ℤ) - 1) *
        (√(Nat.card (DiscriminantGroup L) : ℝ) : ℂ)⁻¹) •
        thetaSeries (√(level L : ℝ) • dual L) := by
  borelize E
  rw [coe_frickeOperator, coe_thetaFormOfLevel, thetaSeries_slash_frickeGL L (level L) hk,
    hL.isIntegral.covolume_eq_sqrt_card_discriminantGroup]

/-- **The raw Fricke operator on `thetaFormOfLevel`**: `TauCeti.frickeOperator` sends the
general-level theta form of `L` to `(-i)^k N^{k-1} |A_L|^{-1/2}` times the restriction to
`Γ₁(level L)` of the theta form of its Fricke partner `√(level L) • L^∨`. -/
theorem frickeOperator_thetaFormOfLevel [NeZero (level L)]
    [DiscreteTopology (√(level L : ℝ) • dual L : Submodule ℤ E)]
    [IsZLattice ℝ (√(level L : ℝ) • dual L)]
    (hL : IsEven L) (hk : finrank ℝ E = 2 * k) :
    frickeOperator (N := level L) (k : ℤ) (thetaFormOfLevel hL hk) =
      ((-I) ^ k * (level L : ℂ) ^ ((k : ℤ) - 1) *
        (√(Nat.card (DiscriminantGroup L) : ℝ) : ℂ)⁻¹) •
        (thetaFormOfLevel (isEven_sqrt_level_smul_dual L) hk).restrict
          (CongruenceSubgroup.Gamma1_map_le_Gamma1_map_of_dvd
            hL.level_sqrt_level_smul_dual_dvd) := by
  apply ModularForm.ext
  intro τ
  rw [coe_frickeOperator_thetaFormOfLevel]
  simp only [FunLike.coe_smul, Pi.smul_apply, ModularForm.coe_restrict, coe_thetaFormOfLevel]

/-- On underlying functions, the normalized Fricke operator `𝒲_N = TauCeti.normalizedFrickeOperator`
carries `thetaFormOfLevel` to `(-i)^k (√N)^k |A_L|^{-1/2} Θ_{√N • L^∨}`, where `N = level L`. -/
theorem coe_normalizedFrickeOperator_thetaFormOfLevel [NeZero (level L)] (hL : IsEven L)
    (hk : finrank ℝ E = 2 * k) :
    ⇑(normalizedFrickeOperator (N := level L) (k : ℤ) (thetaFormOfLevel hL hk)) =
      ((-I) ^ k * (√(level L : ℝ) : ℂ) ^ k *
        (√(Nat.card (DiscriminantGroup L) : ℝ) : ℂ)⁻¹) •
        thetaSeries (√(level L : ℝ) • dual L) := by
  borelize E
  rw [coe_normalizedFrickeOperator, coe_thetaFormOfLevel,
    atkinLehnerNormalizer_smul_thetaSeries_slash_frickeGL L (level L) hk,
    hL.isIntegral.covolume_eq_sqrt_card_discriminantGroup]

/-- **The normalized Fricke operator `𝒲_N` on `thetaFormOfLevel`**:
`TauCeti.normalizedFrickeOperator` sends the general-level theta form of `L` to
`(-i)^k (√N)^k |A_L|^{-1/2}` times the restriction to `Γ₁(level L)` of the theta form of its
Fricke partner `√(level L) • L^∨`. -/
theorem normalizedFrickeOperator_thetaFormOfLevel [NeZero (level L)]
    [DiscreteTopology (√(level L : ℝ) • dual L : Submodule ℤ E)]
    [IsZLattice ℝ (√(level L : ℝ) • dual L)]
    (hL : IsEven L) (hk : finrank ℝ E = 2 * k) :
    normalizedFrickeOperator (N := level L) (k : ℤ) (thetaFormOfLevel hL hk) =
      ((-I) ^ k * (√(level L : ℝ) : ℂ) ^ k *
        (√(Nat.card (DiscriminantGroup L) : ℝ) : ℂ)⁻¹) •
        (thetaFormOfLevel (isEven_sqrt_level_smul_dual L) hk).restrict
          (CongruenceSubgroup.Gamma1_map_le_Gamma1_map_of_dvd
            hL.level_sqrt_level_smul_dual_dvd) := by
  apply ModularForm.ext
  intro τ
  rw [coe_normalizedFrickeOperator_thetaFormOfLevel]
  simp only [FunLike.coe_smul, Pi.smul_apply, ModularForm.coe_restrict, coe_thetaFormOfLevel]

/-- **The raw Fricke operator sends the Fricke partner back to `thetaFormOfLevel`**:
`W_N` maps the restriction to `Γ₁(level L)` of the theta form of `√(level L) • L^∨` to
`(-i)^k N⁻¹ |A_L|^{1/2}` times `thetaFormOfLevel hL hk`. -/
theorem frickeOperator_restrict_thetaFormOfLevel_sqrt_level_smul_dual [NeZero (level L)]
    [DiscreteTopology (√(level L : ℝ) • dual L : Submodule ℤ E)]
    [IsZLattice ℝ (√(level L : ℝ) • dual L)]
    (hL : IsEven L) (hk : finrank ℝ E = 2 * k) :
    frickeOperator (N := level L) (k : ℤ)
        ((thetaFormOfLevel (isEven_sqrt_level_smul_dual L) hk).restrict
          (CongruenceSubgroup.Gamma1_map_le_Gamma1_map_of_dvd hL.level_sqrt_level_smul_dual_dvd)) =
      ((-I) ^ k * (level L : ℂ)⁻¹ *
        (√(Nat.card (DiscriminantGroup L) : ℝ) : ℂ)) • thetaFormOfLevel hL hk := by
  borelize E
  apply ModularForm.ext
  intro τ
  rw [coe_frickeOperator, FunLike.coe_smul, Pi.smul_apply, coe_thetaFormOfLevel]
  have hcoe : ⇑((thetaFormOfLevel (isEven_sqrt_level_smul_dual L) hk).restrict
      (CongruenceSubgroup.Gamma1_map_le_Gamma1_map_of_dvd hL.level_sqrt_level_smul_dual_dvd)) =
      thetaSeries (√(level L : ℝ) • dual L) := by
    ext z
    rw [ModularForm.coe_restrict, coe_thetaFormOfLevel]
  rw [hcoe, thetaSeries_sqrt_smul_dual_slash_frickeGL L (level L) hk,
    hL.isIntegral.covolume_eq_sqrt_card_discriminantGroup, Pi.smul_apply]

/-- **The normalized Fricke operator `𝒲_N` sends the Fricke partner back to `thetaFormOfLevel`**:
`𝒲_N` maps the restriction to `Γ₁(level L)` of the theta form of `√(level L) • L^∨` to
`(-i)^k (√N)^(-k) |A_L|^{1/2}` times `thetaFormOfLevel hL hk`. -/
theorem normalizedFrickeOperator_restrict_thetaFormOfLevel_sqrt_level_smul_dual [NeZero (level L)]
    [DiscreteTopology (√(level L : ℝ) • dual L : Submodule ℤ E)]
    [IsZLattice ℝ (√(level L : ℝ) • dual L)]
    (hL : IsEven L) (hk : finrank ℝ E = 2 * k) :
    normalizedFrickeOperator (N := level L) (k : ℤ)
        ((thetaFormOfLevel (isEven_sqrt_level_smul_dual L) hk).restrict
          (CongruenceSubgroup.Gamma1_map_le_Gamma1_map_of_dvd hL.level_sqrt_level_smul_dual_dvd)) =
      ((-I) ^ k * ((√(level L : ℝ) : ℂ) ^ k)⁻¹ *
        (√(Nat.card (DiscriminantGroup L) : ℝ) : ℂ)) • thetaFormOfLevel hL hk := by
  borelize E
  apply ModularForm.ext
  intro τ
  have hcoe : ⇑((thetaFormOfLevel (isEven_sqrt_level_smul_dual L) hk).restrict
      (CongruenceSubgroup.Gamma1_map_le_Gamma1_map_of_dvd hL.level_sqrt_level_smul_dual_dvd)) =
      thetaSeries (√(level L : ℝ) • dual L) := by
    ext z
    rw [ModularForm.coe_restrict, coe_thetaFormOfLevel]
  have hfn := atkinLehnerNormalizer_smul_thetaSeries_sqrt_smul_dual_slash_frickeGL L (level L) hk
  rw [coe_normalizedFrickeOperator, FunLike.coe_smul, Pi.smul_apply, coe_thetaFormOfLevel, hcoe]
  simpa only [hL.isIntegral.covolume_eq_sqrt_card_discriminantGroup, Pi.smul_apply] using
    congrFun hfn τ

/-- **The restricted theta form of the Fricke partner lies in the same nebentypus space**:
since `frickeOperator` carries `M_k(Γ₁(N), χ_L)` into `M_k(Γ₁(N), χ_L⁻¹)` and the theta
character `χ_L` is quadratic, the restriction of the Fricke partner's theta form to `Γ₁(level L)`
has nebentypus `χ_L`. -/
theorem restrict_thetaFormOfLevel_sqrt_level_smul_dual_mem_modFormCharSpace [NeZero (level L)]
    [DiscreteTopology (√(level L : ℝ) • dual L : Submodule ℤ E)]
    [IsZLattice ℝ (√(level L : ℝ) • dual L)]
    (hL : IsEven L) (hk : finrank ℝ E = 2 * k) :
    (thetaFormOfLevel (isEven_sqrt_level_smul_dual L) hk).restrict
        (CongruenceSubgroup.Gamma1_map_le_Gamma1_map_of_dvd hL.level_sqrt_level_smul_dual_dvd) ∈
      modFormCharSpace (k : ℤ) (MulChar.equivToUnitHom (hL.thetaCharacter ⟨k, by omega⟩)) := by
  have hmem := frickeOperator_mem_modFormCharSpace (N := level L) (k : ℤ)
    (MulChar.equivToUnitHom (hL.thetaCharacter ⟨k, by omega⟩))
    (thetaFormOfLevel_mem_modFormCharSpace hL hk)
  have hinv : (MulChar.equivToUnitHom (hL.thetaCharacter ⟨k, by omega⟩))⁻¹ =
      MulChar.equivToUnitHom (hL.thetaCharacter ⟨k, by omega⟩) := by
    rw [← MulChar.mulEquivToUnitHom_apply, ← map_inv,
      (hL.thetaCharacter_isQuadratic ⟨k, by omega⟩).inv, MulChar.mulEquivToUnitHom_apply]
  rw [hinv, frickeOperator_thetaFormOfLevel] at hmem
  have hcard : 0 < Nat.card (DiscriminantGroup L) := by
    have := hL.isIntegral.finite_discriminantGroup
    exact Nat.card_pos
  have hc : (-I) ^ k * (level L : ℂ) ^ ((k : ℤ) - 1) *
      (√(Nat.card (DiscriminantGroup L) : ℝ) : ℂ)⁻¹ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr I_ne_zero)) ?_) ?_
    · exact zpow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne (level L)))
    · exact inv_ne_zero
        (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hcard)).ne')
  simpa only [inv_smul_smul₀ hc] using Submodule.smul_mem _
    ((-I) ^ k * (level L : ℂ) ^ ((k : ℤ) - 1) *
      (√(Nat.card (DiscriminantGroup L) : ℝ) : ℂ)⁻¹)⁻¹ hmem

end Bundled

end ZLattice
