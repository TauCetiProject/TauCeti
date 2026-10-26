/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Degeneracy
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Character
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Weighted
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Weight-two Eisenstein series with character

For Dirichlet characters `ψ` modulo `u` and `φ` modulo `v` and a level `N` with `u v ∣ N`, the
Eisenstein series with character of Diamond–Shurman §4.5 in weight two,
`G₂^{ψ,φ}(z) = ∑_{(c, d)} ψ(c) φ⁻¹(d) (c v z + d)⁻²`. In weight `k ≥ 3` it is
`TauCeti.EisensteinSeries.charEisensteinSeriesMF`, the residue-weighted series of the weight
`TauCeti.EisensteinSeries.charWeight N ψ φ`. In weight two that series does not converge
absolutely, and we use instead the weight-two series `TauCeti.EisensteinSeries.weightedG2` of the
same weight, built from Weierstrass division values.

Unless `ψ` and `φ` are both trivial the weight has total mass zero
(`TauCeti.EisensteinSeries.sum_charWeight_eq_zero`), so the weight-two series is the series
`∑_x w(x) (x₀ z + x₁)⁻²` over integer pairs itself, summed over the translates of a fundamental box
of residues modulo `N`, with no regularization
(`TauCeti.EisensteinSeries.hasSum_charG2MF`). For the trivial characters modulo `1` the series
`∑ (c z + d)⁻²` is not modular and the corrected combination
`TauCeti.EisensteinSeries.correctedE2` takes its place.

The transformation law under `Γ₀(N)` is that of weight `k ≥ 3`, since the slash action on the
weight-two series changes the weight by the same rule: slashing by `γ ∈ Γ₀(N)` with lower-right
entry `d` multiplies the series by `ψ(d) φ(d)`. Hence the series is a modular form for `Γ₁(N)` in
the nebentypus space `M₂(N, ψφ)`, zero unless `ψ(-1) φ(-1) = 1`. Raising by `t` with `t u v ∣ N`,
`G₂^{ψ,φ,t}(z) = G₂^{ψ,φ}(t z)` lies in `M₂(N, ψφ)` as well.

## Main definitions

* `TauCeti.EisensteinSeries.charG2MF`: `G₂^{ψ,φ}` as a modular form of weight two for `Γ₁(N)`.
* `TauCeti.EisensteinSeries.charG2MFRaise`: its level raise `G₂^{ψ,φ,t}` to any level divisible
  by `t u v`.

## Main results

* `TauCeti.EisensteinSeries.hasSum_charG2MF`: for a nontrivial pair, the series over integer
  pairs.
* `TauCeti.EisensteinSeries.charG2MF_mem_modFormCharSpace`: `G₂^{ψ,φ} ∈ M₂(N, ψφ)`.
* `TauCeti.EisensteinSeries.charG2MF_eq_zero`: it vanishes unless `ψ(-1) φ(-1) = 1`.
* `TauCeti.EisensteinSeries.charG2MFRaise_mem_modFormCharSpace`: `G₂^{ψ,φ,t} ∈ M₂(N, ψφ)`.
* `TauCeti.EisensteinSeries.qExpansion_charG2MFRaise_coeff`: raising by `t` substitutes
  `q ↦ q^t`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.5, §4.6.
* [T. Miyake, *Modular forms*][miyake1989], §7.1, §7.2.
-/

public section

noncomputable section

open ModularForm UpperHalfPlane Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open EisensteinSeries

open scoped MatrixGroups

namespace TauCeti.EisensteinSeries

variable {u v N t : ℕ} (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v)

/-- **The weight-two transformation law**: for `γ ∈ Γ₀(N)` with lower-right entry `d`, the
weight-two series of the weight `charWeight N ψ φ` satisfies `G ∣[2] γ = ψ(d) φ(d) • G`. -/
theorem weightedG2_charWeight_slash [NeZero N] (huv : u * v ∣ N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) :
    weightedG2 (charWeight N ψ φ) ∣[(2 : ℤ)] γ =
      (ψ (γ 1 1 : ZMod u) * φ (γ 1 1 : ZMod v)) • weightedG2 (charWeight N ψ φ) := by
  rw [weightedG2_slash_apply, ← weightedG2_smul]
  congr 1
  ext a
  rw [charWeight_vecMul_map_inv ψ φ huv hγ, Pi.smul_apply, smul_eq_mul]

variable [NeZero N]

/-- The weight-two Eisenstein series `G₂^{ψ,φ}` with characters `ψ` modulo `u` and `φ` modulo
`v`, as a modular form of weight two for `Γ₁(N)`, where `u v ∣ N`: the weight-two series
`weightedG2` of the weight `charWeight N ψ φ`. Unless `ψ` and `φ` are both trivial it is the series
`∑_{x ∈ ℤ², v ∣ x₀} ψ(x₀ / v) φ⁻¹(x₁) (x₀ z + x₁)⁻²` summed over translates of a box of residues
(`hasSum_charG2MF`). -/
def charG2MF (huv : u * v ∣ N) : ModularForm ((Gamma1 N).map (mapGL ℝ)) 2 :=
  ModularForm.ofSlashInvariant Subgroup.IsArithmetic.isCusp_of_isCusp
    (weightedG2MF (charWeight N ψ φ)) fun γ hγ ↦ by
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
      obtain ⟨hg0, hg1⟩ := mem_Gamma1_iff.mp hg
      have h1 {m : ℕ} (hm : m ∣ N) : ((g 1 1 : ℤ) : ZMod m) = 1 := by
        rw [← map_intCast (ZMod.castHom hm (ZMod m)), hg1, map_one]
      -- `SL_slash`: slashing by `g` is slashing by its image `mapGL ℝ g`
      have hslash : weightedG2 (charWeight N ψ φ) ∣[(2 : ℤ)] mapGL ℝ g = _ :=
        (SL_slash _ g).symm.trans (weightedG2_charWeight_slash ψ φ huv hg0)
      rw [coe_weightedG2MF, hslash, h1 (dvd_of_mul_right_dvd huv),
        h1 (dvd_of_mul_left_dvd huv), map_one, map_one, one_mul, one_smul]

/-- The weight-two Eisenstein series with character is the weight-two series of
`charWeight N ψ φ`. -/
@[simp]
lemma coe_charG2MF (huv : u * v ∣ N) : ⇑(charG2MF ψ φ huv) = weightedG2 (charWeight N ψ φ) := by
  rw [charG2MF, ModularForm.coe_ofSlashInvariant, coe_weightedG2MF]

/-- **The weight-two Eisenstein series with character as a series**: unless `ψ` and `φ` are both
trivial, `G₂^{ψ,φ}(z) = ∑_y ∑_a w(ã - N y) ((ã - N y)₀ z + (ã - N y)₁)⁻²`, with `ã` the least
nonnegative representatives of the residue pair `a` and `w(x) = ψ(x₀ / v) φ⁻¹(x₁)` if `v ∣ x₀`
and `0` otherwise, the series over `y` converging absolutely. -/
theorem hasSum_charG2MF (huv : u * v ∣ N) (h : ψ ≠ 1 ∨ φ ≠ 1) (z : ℍ) :
    HasSum (fun y : Fin 2 → ℤ ↦ ∑ a : Fin 2 → ZMod N,
        (if (v : ℤ) ∣ (a 0).val - N * y 0 then
          ψ ((((a 0).val - N * y 0 : ℤ) / v : ℤ) : ZMod u) *
            φ⁻¹ (((a 1).val - N * y 1 : ℤ) : ZMod v)
        else 0) * eisSummand 2 ((fun i ↦ ((a i).val : ℤ)) - N • y) z)
      (charG2MF ψ φ huv z) := by
  rw [coe_charG2MF]
  refine (hasSum_weightedG2_of_sum_eq_zero (sum_charWeight_eq_zero ψ φ huv h) z).congr_fun
    fun y ↦ Finset.sum_congr rfl fun a _ ↦ ?_
  have ha : ((↑) : ℤ → ZMod N) ∘ ((fun i ↦ ((a i).val : ℤ)) - N • y) = a := by
    ext i
    simp
  conv_rhs => rw [← ha, charWeight_intCast ψ φ huv]
  simp [nsmul_eq_mul]

/-- **The nebentypus of the weight-two Eisenstein series with character**:
`G₂^{ψ,φ} ∈ M₂(N, ψφ)`, the characters being raised to level `N`. -/
theorem charG2MF_mem_modFormCharSpace (huv : u * v ∣ N) :
    charG2MF ψ φ huv ∈ modFormCharSpace 2
      (ψ.changeLevel (dvd_of_mul_right_dvd huv) *
        φ.changeLevel (dvd_of_mul_left_dvd huv)).toUnitHom := by
  rw [mem_modFormCharSpace_iff_nebentypus]
  intro g
  -- `SL_slash`: slashing by `g` is slashing by its image `mapGL ℝ g`
  have hslash : weightedG2 (charWeight N ψ φ) ∣[(2 : ℤ)] mapGL ℝ (g : SL(2, ℤ)) = _ :=
    (SL_slash _ _).symm.trans (weightedG2_charWeight_slash ψ φ huv g.2)
  rw [coe_charG2MF, hslash, MulChar.coe_toUnitHom, MulChar.coeToFun_mul,
    Pi.mul_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    DirichletCharacter.changeLevel_eq_cast_of_dvd]
  simp [Gamma0Map, ZMod.cast_intCast (dvd_of_mul_right_dvd huv),
    ZMod.cast_intCast (dvd_of_mul_left_dvd huv)]

/-- **Parity**: the weight-two Eisenstein series with character vanishes unless
`ψ(-1) φ(-1) = 1`. -/
theorem charG2MF_eq_zero (huv : u * v ∣ N) (h : ψ (-1) * φ (-1) ≠ 1) : charG2MF ψ φ huv = 0 := by
  have hmem := charG2MF_mem_modFormCharSpace ψ φ huv
  rwa [modFormCharSpace_eq_bot_of_char_neg_one_ne, Submodule.mem_bot] at hmem
  simpa [MulChar.coe_toUnitHom, DirichletCharacter.changeLevel_apply_neg_one] using h

/-! ### Raising the level -/

/-- The weight-two Eisenstein series with character and raising parameter `t`:
`G₂^{ψ,φ,t} = V_t G₂^{ψ,φ}`, viewed at any level `N` divisible by `t u v`. The series is formed at
its natural level `u v` and raised directly to level `N`. -/
def charG2MFRaise (t : ℕ) (htuv : t * (u * v) ∣ N) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) 2 := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  exact ModularForm.levelRaise t (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv)
    (charG2MF ψ φ dvd_rfl)

/-- The raised series is the degeneracy image of the series at its natural level. -/
theorem charG2MFRaise_eq_levelRaise (t : ℕ) (htuv : t * (u * v) ∣ N) :
    haveI : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
    haveI : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
    charG2MFRaise ψ φ t htuv =
      ModularForm.levelRaise t (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv)
        (charG2MF ψ φ dvd_rfl) := (rfl)

/-- The raised series is the series at its natural level evaluated at `t z`. -/
@[simp]
theorem charG2MFRaise_apply (htuv : t * (u * v) ∣ N) (z : ℍ) :
    haveI : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
    haveI : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
    charG2MFRaise ψ φ t htuv z = charG2MF ψ φ dvd_rfl (scaleGL t • z) := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [charG2MFRaise, ModularForm.levelRaise_apply]

/-- **The nebentypus after raising**: at every level `N` divisible by `t u v`,
`G₂^{ψ,φ,t} ∈ M₂(N, ψφ)`, with both characters raised directly to level `N`. -/
theorem charG2MFRaise_mem_modFormCharSpace (htuv : t * (u * v) ∣ N) :
    charG2MFRaise ψ φ t htuv ∈ modFormCharSpace 2
      (ψ.changeLevel ((dvd_mul_right u v).trans ((dvd_mul_left (u * v) t).trans htuv)) *
        φ.changeLevel
          ((dvd_mul_left v u).trans ((dvd_mul_left (u * v) t).trans htuv))).toUnitHom := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  have hchar : (ψ.changeLevel ((dvd_mul_right u v).trans ((dvd_mul_left (u * v) t).trans htuv)) *
      φ.changeLevel ((dvd_mul_left v u).trans ((dvd_mul_left (u * v) t).trans htuv))).toUnitHom =
        (ψ.changeLevel (dvd_mul_right u v) * φ.changeLevel (dvd_mul_left v u)).toUnitHom.comp
          (ZMod.unitsMap ((dvd_mul_left (u * v) t).trans htuv)) := by
    rw [DirichletCharacter.changeLevel_trans ψ (dvd_mul_right u v)
        ((dvd_mul_left (u * v) t).trans htuv),
      DirichletCharacter.changeLevel_trans φ (dvd_mul_left v u)
        ((dvd_mul_left (u * v) t).trans htuv), ← map_mul,
      DirichletCharacter.changeLevel_toUnitHom]
  rw [charG2MFRaise, hchar]
  exact ModularForm.levelRaise_mem_modFormCharSpace_of_dvd htuv _
    (charG2MF_mem_modFormCharSpace (N := u * v) ψ φ dvd_rfl)

/-- **Parity after raising**: if `ψ(-1) φ(-1) ≠ 1`, every raised series is zero. -/
theorem charG2MFRaise_eq_zero (htuv : t * (u * v) ∣ N) (h : ψ (-1) * φ (-1) ≠ 1) :
    charG2MFRaise ψ φ t htuv = 0 := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [charG2MFRaise, charG2MF_eq_zero ψ φ dvd_rfl h, ← ModularForm.levelRaiseₗ_apply, map_zero]

/-- The `q`-expansion of `G₂^{ψ,φ,t}` is that of `G₂^{ψ,φ}` with `q ↦ q^t`. -/
@[simp]
theorem qExpansion_charG2MFRaise (htuv : t * (u * v) ∣ N) :
    haveI : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
    haveI : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
    qExpansion 1 (charG2MFRaise ψ φ t htuv) =
      (qExpansion 1 (charG2MF ψ φ (N := u * v) dvd_rfl)).expand t (NeZero.ne t) := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [charG2MFRaise]
  exact ModularForm.qExpansion_levelRaise
    (TauCeti.one_mem_strictPeriods_Gamma1_map (u * v))
    (TauCeti.one_mem_strictPeriods_Gamma1_map N)
    (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv) _

/-- The coefficients of `G₂^{ψ,φ,t}`: `a_n(G₂^{ψ,φ,t}) = a_{n/t}(G₂^{ψ,φ})` when `t ∣ n`, and
`0` otherwise. -/
theorem qExpansion_charG2MFRaise_coeff (htuv : t * (u * v) ∣ N) (n : ℕ) :
    haveI : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
    (qExpansion 1 (charG2MFRaise ψ φ t htuv)).coeff n =
      if t ∣ n then (qExpansion 1 (charG2MF ψ φ (N := u * v) dvd_rfl)).coeff (n / t)
      else 0 := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [charG2MFRaise]
  exact ModularForm.qExpansion_levelRaise_coeff
    (TauCeti.one_mem_strictPeriods_Gamma1_map (u * v))
    (TauCeti.one_mem_strictPeriods_Gamma1_map N)
    (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv) _ n

end TauCeti.EisensteinSeries
