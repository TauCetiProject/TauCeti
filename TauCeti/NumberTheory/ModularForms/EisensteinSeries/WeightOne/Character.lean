/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Degeneracy
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Character
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.Weighted
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Weight-one Eisenstein series with character

For Dirichlet characters `ψ` modulo `u` and `φ` modulo `v` and a level `N` with `u v ∣ N`, the
Eisenstein series with character of Diamond–Shurman §4.8 in weight one,
`E₁^{ψ,φ}(z) = ∑_{(c, d)} ψ(c) φ⁻¹(d) (c v z + d)⁻¹`. In weight `k ≥ 3` it is
`TauCeti.EisensteinSeries.charEisensteinSeriesMF`, the residue-weighted series of the weight
`TauCeti.EisensteinSeries.charWeight N ψ φ`. In weight one the series over integer pairs does not
converge absolutely, and we use instead the weight-one series
`TauCeti.EisensteinSeries.weightedE1` of the same weight, built from the division values of the
Weierstrass `ζ` function corrected by its quasi-periods.

The transformation law under `Γ₀(N)` is that of weight `k ≥ 3`, since the slash action on the
weight-one series changes the weight by the same rule: slashing by `γ ∈ Γ₀(N)` with lower-right
entry `d` multiplies the series by `ψ(d) φ(d)`. Hence the series is a modular form for `Γ₁(N)` in
the nebentypus space `M₁(N, ψφ)`. Weight one carries its own parity constraint: the series is zero
unless `ψ(-1) φ(-1) = -1`. Raising by `t` with `t u v ∣ N`, `E₁^{ψ,φ,t}(z) = E₁^{ψ,φ}(t z)` lies in
`M₁(N, ψφ)` as well, and its `q`-expansion is that of `E₁^{ψ,φ}` with `q ↦ q^t`.

## Main definitions

* `TauCeti.EisensteinSeries.charE1MF`: `E₁^{ψ,φ}` as a modular form of weight one for `Γ₁(N)`.
* `TauCeti.EisensteinSeries.charE1MFRaise`: its level raise `E₁^{ψ,φ,t}` to any level divisible
  by `t u v`.

## Main results

* `TauCeti.EisensteinSeries.charE1MF_mem_modFormCharSpace`: `E₁^{ψ,φ} ∈ M₁(N, ψφ)`.
* `TauCeti.EisensteinSeries.charE1MF_eq_zero`: it vanishes unless `ψ(-1) φ(-1) = -1`.
* `TauCeti.EisensteinSeries.charE1MFRaise_mem_modFormCharSpace`: `E₁^{ψ,φ,t} ∈ M₁(N, ψφ)`.
* `TauCeti.EisensteinSeries.qExpansion_charE1MFRaise_coeff`: raising by `t` substitutes
  `q ↦ q^t`.
* `TauCeti.EisensteinSeries.isSupportedOnDvd_qExpansion_charE1MFRaise`: the `q`-expansion of the
  raised series is supported on multiples of `t`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.8.
* [T. Miyake, *Modular forms*][miyake1989], §7.1, §7.2.
-/

public section

noncomputable section

open ModularForm UpperHalfPlane Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open EisensteinSeries

open scoped MatrixGroups

namespace TauCeti.EisensteinSeries

variable {u v N t : ℕ} (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v)

/-- **The weight-one transformation law**: for `γ ∈ Γ₀(N)` with lower-right entry `d`, the
weight-one series of the weight `charWeight N ψ φ` satisfies `E ∣[1] γ = ψ(d) φ(d) • E`. -/
theorem weightedE1_charWeight_slash [NeZero N] (huv : u * v ∣ N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) :
    weightedE1 (charWeight N ψ φ) ∣[(1 : ℤ)] γ =
      (ψ (γ 1 1 : ZMod u) * φ (γ 1 1 : ZMod v)) • weightedE1 (charWeight N ψ φ) := by
  rw [weightedE1_slash_apply, ← weightedE1_smul]
  congr 1
  ext a
  rw [charWeight_vecMul_map_inv ψ φ huv hγ, Pi.smul_apply, smul_eq_mul]

variable [NeZero N]

/-- The weight-one Eisenstein series `E₁^{ψ,φ}` with characters `ψ` modulo `u` and `φ` modulo
`v`, as a modular form of weight one for `Γ₁(N)`, where `u v ∣ N`: the weight-one series
`weightedE1` of the weight `charWeight N ψ φ`, the regularization by Weierstrass `ζ` values of the
series `∑_{x ∈ ℤ², v ∣ x₀} ψ(x₀ / v) φ⁻¹(x₁) (x₀ z + x₁)⁻¹`. -/
def charE1MF (huv : u * v ∣ N) : ModularForm ((Gamma1 N).map (mapGL ℝ)) 1 :=
  ModularForm.ofSlashInvariant Subgroup.IsArithmetic.isCusp_of_isCusp
    (weightedE1MF (charWeight N ψ φ)) fun _ hγ ↦ by
      rw [coe_weightedE1MF]
      exact slash_Gamma1_eq_self_of_slash_Gamma0_eq ψ φ huv
        (fun _ hg ↦ weightedE1_charWeight_slash ψ φ huv hg) hγ

/-- The weight-one Eisenstein series with character is the weight-one series of
`charWeight N ψ φ`. -/
@[simp]
lemma coe_charE1MF (huv : u * v ∣ N) : ⇑(charE1MF ψ φ huv) = weightedE1 (charWeight N ψ φ) := by
  rw [charE1MF, ModularForm.coe_ofSlashInvariant, coe_weightedE1MF]

/-- **The nebentypus of the weight-one Eisenstein series with character**:
`E₁^{ψ,φ} ∈ M₁(N, ψφ)`, the characters being raised to level `N`. -/
theorem charE1MF_mem_modFormCharSpace (huv : u * v ∣ N) :
    charE1MF ψ φ huv ∈ modFormCharSpace 1
      (ψ.changeLevel (dvd_of_mul_right_dvd huv) *
        φ.changeLevel (dvd_of_mul_left_dvd huv)).toUnitHom := by
  refine mem_modFormCharSpace_of_slash_Gamma0_eq ψ φ huv _ fun _ hg ↦ ?_
  rw [coe_charE1MF]
  exact weightedE1_charWeight_slash ψ φ huv hg

/-- **Parity**: the weight-one Eisenstein series with character vanishes unless
`ψ(-1) φ(-1) = -1`. -/
theorem charE1MF_eq_zero (huv : u * v ∣ N) (h : ψ (-1) * φ (-1) ≠ -1) : charE1MF ψ φ huv = 0 := by
  have hmem := charE1MF_mem_modFormCharSpace ψ φ huv
  rwa [modFormCharSpace_eq_bot_of_char_neg_one_ne, Submodule.mem_bot] at hmem
  simpa [MulChar.coe_toUnitHom, DirichletCharacter.changeLevel_apply_neg_one] using h

/-! ### Raising the level -/

/-- The weight-one Eisenstein series with character and raising parameter `t`:
`E₁^{ψ,φ,t} = V_t E₁^{ψ,φ}`, viewed at any level `N` divisible by `t u v`. The series is formed at
its natural level `u v` and raised directly to level `N`. -/
def charE1MFRaise (t : ℕ) (htuv : t * (u * v) ∣ N) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) 1 := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  exact ModularForm.levelRaise t (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv)
    (charE1MF ψ φ dvd_rfl)

/-- The raised series is the degeneracy image of the series at its natural level. -/
theorem charE1MFRaise_eq_levelRaise (t : ℕ) (htuv : t * (u * v) ∣ N) :
    haveI : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
    haveI : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
    charE1MFRaise ψ φ t htuv =
      ModularForm.levelRaise t (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv)
        (charE1MF ψ φ dvd_rfl) := (rfl)

/-- The raised series is the series at its natural level evaluated at `t z`. -/
@[simp]
theorem charE1MFRaise_apply (htuv : t * (u * v) ∣ N) (z : ℍ) :
    haveI : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
    haveI : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
    charE1MFRaise ψ φ t htuv z = charE1MF ψ φ dvd_rfl (scaleGL t • z) := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [charE1MFRaise, ModularForm.levelRaise_apply]

/-- At `t = 1`, the raised series is the series at its natural level `u v` restricted to level
`N`. -/
@[simp]
theorem charE1MFRaise_one (huv : u * v ∣ N) :
    haveI : NeZero (u * v) := NeZero.of_dvd huv
    charE1MFRaise ψ φ 1 (by simpa using huv) =
      ModularForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd huv) (charE1MF ψ φ dvd_rfl) := by
  rw [charE1MFRaise, ModularForm.levelRaise_one]

/-- **The nebentypus after raising**: at every level `N` divisible by `t u v`,
`E₁^{ψ,φ,t} ∈ M₁(N, ψφ)`, with both characters raised directly to level `N`. -/
theorem charE1MFRaise_mem_modFormCharSpace (htuv : t * (u * v) ∣ N) :
    charE1MFRaise ψ φ t htuv ∈ modFormCharSpace 1
      (ψ.changeLevel ((dvd_mul_right u v).trans ((dvd_mul_left (u * v) t).trans htuv)) *
        φ.changeLevel
          ((dvd_mul_left v u).trans ((dvd_mul_left (u * v) t).trans htuv))).toUnitHom := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [charE1MFRaise, DirichletCharacter.changeLevel_trans_mul_toUnitHom ψ φ (dvd_mul_right u v)
    (dvd_mul_left v u)]
  exact ModularForm.levelRaise_mem_modFormCharSpace_of_dvd htuv _
    (charE1MF_mem_modFormCharSpace (N := u * v) ψ φ dvd_rfl)

/-- **Parity after raising**: if `ψ(-1) φ(-1) ≠ -1`, every raised series is zero. -/
theorem charE1MFRaise_eq_zero (htuv : t * (u * v) ∣ N) (h : ψ (-1) * φ (-1) ≠ -1) :
    charE1MFRaise ψ φ t htuv = 0 := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [charE1MFRaise, charE1MF_eq_zero ψ φ dvd_rfl h, ← ModularForm.levelRaiseₗ_apply, map_zero]

/-- The `q`-expansion of `E₁^{ψ,φ,t}` is that of `E₁^{ψ,φ}` with `q ↦ q^t`. -/
@[simp]
theorem qExpansion_charE1MFRaise (htuv : t * (u * v) ∣ N) :
    haveI : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
    haveI : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
    qExpansion 1 (charE1MFRaise ψ φ t htuv) =
      (qExpansion 1 (charE1MF ψ φ (N := u * v) dvd_rfl)).expand t (NeZero.ne t) := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [charE1MFRaise]
  exact ModularForm.qExpansion_levelRaise
    (TauCeti.one_mem_strictPeriods_Gamma1_map (u * v))
    (TauCeti.one_mem_strictPeriods_Gamma1_map N)
    (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv) _

/-- The coefficients of `E₁^{ψ,φ,t}`: `a_n(E₁^{ψ,φ,t}) = a_{n/t}(E₁^{ψ,φ})` when `t ∣ n`, and
`0` otherwise. -/
theorem qExpansion_charE1MFRaise_coeff (htuv : t * (u * v) ∣ N) (n : ℕ) :
    haveI : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
    (qExpansion 1 (charE1MFRaise ψ φ t htuv)).coeff n =
      if t ∣ n then (qExpansion 1 (charE1MF ψ φ (N := u * v) dvd_rfl)).coeff (n / t)
      else 0 := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [charE1MFRaise]
  exact ModularForm.qExpansion_levelRaise_coeff
    (TauCeti.one_mem_strictPeriods_Gamma1_map (u * v))
    (TauCeti.one_mem_strictPeriods_Gamma1_map N)
    (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv) _ n

/-- The `q`-expansion of `E₁^{ψ,φ,t}` is supported on the multiples of `t`. -/
theorem isSupportedOnDvd_qExpansion_charE1MFRaise (htuv : t * (u * v) ∣ N) :
    haveI : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
    PowerSeries.IsSupportedOnDvd t (qExpansion 1 (charE1MFRaise ψ φ t htuv)) := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [charE1MFRaise]
  exact ModularForm.isSupportedOnDvd_qExpansion_levelRaise
    (TauCeti.one_mem_strictPeriods_Gamma1_map (u * v))
    (TauCeti.one_mem_strictPeriods_Gamma1_map N)
    (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv) _

end TauCeti.EisensteinSeries
