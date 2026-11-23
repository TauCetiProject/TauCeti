/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Conductor.Basic
public import TauCeti.NumberTheory.LocalField.Unramified.Character

import TauCeti.Analysis.Normed.Ring.CompactMonoid
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Quasi-characters of a nonarchimedean local field

Let `K` be a nonarchimedean local field with residue field of cardinality `q`, normalized
valuation `v_K` and normalized absolute value `|x| = q ^ (-v_K(x))`. A *quasi-character* of `K` is
a continuous homomorphism `ω : Kˣ → ℂˣ`. This file develops the invariants of quasi-characters
that Tate's local theory uses.

* For `s : ℂ` the **norm-power character** `ω_s(x) = |x| ^ s` is the unramified character
  `x ↦ (q ^ (-s)) ^ v_K(x)`, so `ω_s(ϖ) = q ^ (-s)` at a uniformizer `ϖ`.
* A quasi-character is **unramified**, that is trivial on `U(K,0) = 𝒪[K]ˣ`, exactly when it is
  `ω_s` for some `s`; and `ω_s = ω_t` exactly when `s - t` is an integer multiple of
  `2πi / log q`. So the unramified quasi-characters are the `ω_s` with `s` determined modulo
  `2πi / log q`, equivalently by `t = q ^ (-s) ∈ ℂˣ`.
* Twisting by `ω_s` does not change the character conductor exponent
  `TauCeti.ClassFieldTheory.characterConductorExp`: `c(ω ω_s) = c(ω)`.
* Every quasi-character has a unique real **exponent** `σ` with `‖ω(x)‖ = |x| ^ σ`, because
  `‖ω‖` is trivial on the compact group `U(K,0)`. The exponent of `ω_s` is `re s`, exponents add
  under multiplication, and `ω ω_{-σ}` is unitary, so that `ω = (ω ω_{-σ}) ω_σ` is a unitary
  character times a norm-power character.

## Main definitions

* `TauCeti.normalizedAbsCpowCharacter K s`: the quasi-character `ω_s(x) = |x| ^ s`.
* `TauCeti.characterExponent K ω`: the real exponent `σ` with `‖ω(x)‖ = |x| ^ σ`.

## Main results

* `TauCeti.coe_normalizedAbsCpowCharacter_apply`: `ω_s(x) = |x| ^ s`.
* `TauCeti.coe_normalizedAbsCpowCharacter_apply_of_isUniformizer`: `ω_s(ϖ) = q ^ (-s)`.
* `TauCeti.exists_eq_normalizedAbsCpowCharacter_iff`: a quasi-character is unramified exactly
  when it is some `ω_s`.
* `TauCeti.normalizedAbsCpowCharacter_eq_iff`: `ω_s = ω_t` exactly when
  `s ∈ t + (2πi / log q) ℤ`.
* `TauCeti.characterConductorExp_mul_normalizedAbsCpowCharacter`: `c(ω ω_s) = c(ω)`.
* `TauCeti.existsUnique_norm_coe_apply_eq_normalizedAbsoluteValue_rpow`: the exponent exists and
  is unique.
* `TauCeti.characterExponent_normalizedAbsCpowCharacter`, `TauCeti.characterExponent_mul`:
  the exponent of `ω_s` is `re s`, and exponents add.
* `TauCeti.norm_coe_mul_normalizedAbsCpowCharacter_neg_characterExponent`: `ω ω_{-σ}` is
  unitary.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels and
  A. Fröhlich, eds., *Algebraic Number Theory*, §2.3.
* S. S. Kudla, *Tate's thesis*, in J. Bernstein and S. Gelbart, eds., *An Introduction to the
  Langlands Program*, §3.
-/

public section

noncomputable section

open ValuativeRel Complex

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### Positivity of `q` -/

private theorem one_lt_natCard_residueField_real : (1 : ℝ) < Nat.card 𝓀[K] := by
  exact_mod_cast (Finite.one_lt_card : 1 < Nat.card 𝓀[K])

private theorem natCard_residueField_pos_real : (0 : ℝ) < Nat.card 𝓀[K] :=
  zero_lt_one.trans (one_lt_natCard_residueField_real K)

private theorem natCard_residueField_ne_zero_complex : (Nat.card 𝓀[K] : ℂ) ≠ 0 := by
  exact_mod_cast (natCard_residueField_pos_real K).ne'

private theorem log_natCard_residueField_ne_zero : Real.log (Nat.card 𝓀[K]) ≠ 0 :=
  Real.log_ne_zero_of_pos_of_ne_one (natCard_residueField_pos_real K)
    (one_lt_natCard_residueField_real K).ne'

private theorem log_natCard_residueField_complex :
    log (Nat.card 𝓀[K] : ℂ) = Real.log (Nat.card 𝓀[K]) := by
  rw [← ofReal_natCast, ofReal_log (Nat.cast_nonneg _)]

private theorem log_natCard_residueField_ne_zero_complex : log (Nat.card 𝓀[K] : ℂ) ≠ 0 := by
  rw [log_natCard_residueField_complex, ofReal_ne_zero]
  exact log_natCard_residueField_ne_zero K

private theorem natCard_residueField_cpow_ne_zero (s : ℂ) : (Nat.card 𝓀[K] : ℂ) ^ (-s) ≠ 0 := by
  simp [natCard_residueField_ne_zero_complex K]

/-! ### The norm-power characters `ω_s` -/

/-- The **norm-power character** `ω_s(x) = |x| ^ s` of a nonarchimedean local field, for `s : ℂ`.
It is the unramified character `x ↦ (q ^ (-s)) ^ v_K(x)`, where `q` is the cardinality of the
residue field; `TauCeti.coe_normalizedAbsCpowCharacter_apply` writes it as `|x| ^ s`. -/
def normalizedAbsCpowCharacter (s : ℂ) : Kˣ →ₜ* ℂˣ :=
  unramifiedCharacter K (Units.mk0 _ (natCard_residueField_cpow_ne_zero K s))

variable {K}

/-- `ω_s(x) = (q ^ (-s)) ^ v_K(x)`. -/
theorem coe_normalizedAbsCpowCharacter_apply_eq_zpow (s : ℂ) (x : Kˣ) :
    (normalizedAbsCpowCharacter K s x : ℂ) =
      ((Nat.card 𝓀[K] : ℂ) ^ (-s)) ^ (normalizedValuation K x).toAdd := by
  simp [normalizedAbsCpowCharacter]

/-- `ω_s(x) = |x| ^ s`, for the normalized absolute value `|x| = q ^ (-v_K(x))`. -/
@[simp]
theorem coe_normalizedAbsCpowCharacter_apply (s : ℂ) (x : Kˣ) :
    (normalizedAbsCpowCharacter K s x : ℂ) =
      (((normalizedAbsoluteValue K (x : K) : ℚ≥0) : ℝ) : ℂ) ^ s := by
  -- Both sides are `q` to a complex power: `q ^ (v_K(x) * (-s))` and `q ^ (-v_K(x) * s)`.
  rw [coe_normalizedAbsCpowCharacter_apply_eq_zpow, coe_normalizedAbsoluteValue_eq_zpow,
    ← Real.rpow_intCast, ← cpow_mul_ofReal_nonneg (Nat.cast_nonneg _), ofReal_natCast,
    ← cpow_int_mul]
  congr 1
  push_cast
  ring

/-- The absolute value of `ω_s(x)` is `|x| ^ re s`. -/
theorem norm_coe_normalizedAbsCpowCharacter_apply (s : ℂ) (x : Kˣ) :
    ‖(normalizedAbsCpowCharacter K s x : ℂ)‖ =
      ((normalizedAbsoluteValue K (x : K) : ℚ≥0) : ℝ) ^ s.re := by
  rw [coe_normalizedAbsCpowCharacter_apply,
    norm_cpow_eq_rpow_re_of_pos (coe_normalizedAbsoluteValue_pos x)]

/-- `ω_s` sends a uniformizer `ϖ` to `q ^ (-s)`. -/
theorem coe_normalizedAbsCpowCharacter_apply_of_isUniformizer (s : ℂ) {ϖ : Kˣ}
    (hϖ : IsUniformizer K ϖ) :
    (normalizedAbsCpowCharacter K s ϖ : ℂ) = (Nat.card 𝓀[K] : ℂ) ^ (-s) := by
  rw [normalizedAbsCpowCharacter, unramifiedCharacter_apply_of_isUniformizer _ hϖ, Units.val_mk0]

variable (K) in
/-- `ω_0` is the trivial character. -/
@[simp]
theorem normalizedAbsCpowCharacter_zero : normalizedAbsCpowCharacter K 0 = 1 := by
  rw [← unramifiedCharacter_one K, normalizedAbsCpowCharacter]
  congr 1
  ext
  simp

variable (K) in
/-- `ω_{s + t} = ω_s ω_t`. -/
theorem normalizedAbsCpowCharacter_add (s t : ℂ) :
    normalizedAbsCpowCharacter K (s + t) =
      normalizedAbsCpowCharacter K s * normalizedAbsCpowCharacter K t := by
  rw [normalizedAbsCpowCharacter, normalizedAbsCpowCharacter, normalizedAbsCpowCharacter,
    ← unramifiedCharacter_mul]
  congr 1
  ext
  simp [cpow_add _ _ (natCard_residueField_ne_zero_complex K), mul_comm]

/-- **`ω_s` determines `s` modulo `2πi / log q`.** -/
theorem normalizedAbsCpowCharacter_eq_iff {s t : ℂ} :
    normalizedAbsCpowCharacter K s = normalizedAbsCpowCharacter K t ↔
      ∃ n : ℤ, s = t + n * (2 * Real.pi * I / Real.log (Nat.card 𝓀[K])) := by
  have hq := natCard_residueField_ne_zero_complex K
  have hlog := log_natCard_residueField_ne_zero_complex K
  rw [normalizedAbsCpowCharacter, normalizedAbsCpowCharacter,
    (unramifiedCharacter_injective K).eq_iff, Units.ext_iff, Units.val_mk0, Units.val_mk0,
    cpow_def_of_ne_zero hq, cpow_def_of_ne_zero hq, exp_eq_exp_iff_exists_int,
    log_natCard_residueField_complex]
  rw [log_natCard_residueField_complex] at hlog
  generalize (Real.log (Nat.card 𝓀[K]) : ℂ) = L at hlog ⊢
  constructor
  · rintro ⟨n, h⟩
    refine ⟨-n, ?_⟩
    field_simp
    push_cast
    linear_combination (-1 : ℂ) * h
  · rintro ⟨n, rfl⟩
    refine ⟨-n, ?_⟩
    field_simp
    push_cast
    ring

/-- **Unramified quasi-characters are norm-power characters.** A quasi-character of `K` is
trivial on `U(K,0) = 𝒪[K]ˣ` exactly when it is `ω_s` for some `s : ℂ`. -/
theorem exists_eq_normalizedAbsCpowCharacter_iff {ω : Kˣ →ₜ* ℂˣ} :
    (∃ s : ℂ, ω = normalizedAbsCpowCharacter K s) ↔ unitFiltration K 0 ≤ ω.ker := by
  have hq := natCard_residueField_ne_zero_complex K
  have hlog := log_natCard_residueField_ne_zero_complex K
  have hker : unitFiltration K 0 ≤ ω.ker ↔ ∀ u : Kˣ, valuation K (u : K) = 1 → ω u = 1 :=
    ⟨fun h u hu ↦ h ((mem_unitFiltration_zero u).2 hu),
      fun h u hu ↦ h u ((mem_unitFiltration_zero u).1 hu)⟩
  rw [hker, ← exists_eq_unramifiedCharacter_iff]
  refine ⟨fun ⟨s, hs⟩ ↦ ⟨_, hs⟩, fun ⟨a, ha⟩ ↦ ⟨-(log a / log (Nat.card 𝓀[K] : ℂ)), ?_⟩⟩
  rw [ha, normalizedAbsCpowCharacter]
  congr 1
  ext
  rw [Units.val_mk0, neg_neg, cpow_def_of_ne_zero hq, mul_div_cancel₀ _ hlog, exp_log a.ne_zero]

variable (K) in
/-- The norm-power character `ω_s` is unramified. -/
theorem unitFiltration_zero_le_ker_normalizedAbsCpowCharacter (s : ℂ) :
    unitFiltration K 0 ≤ (normalizedAbsCpowCharacter K s).ker :=
  exists_eq_normalizedAbsCpowCharacter_iff.1 ⟨s, rfl⟩

variable (K) in
/-- The norm-power character `ω_s` has conductor exponent `0`. -/
@[simp]
theorem characterConductorExp_normalizedAbsCpowCharacter (s : ℂ) :
    ClassFieldTheory.characterConductorExp K (normalizedAbsCpowCharacter K s) = 0 :=
  (ClassFieldTheory.characterConductorExp_eq_zero_iff K _).2
    (unitFiltration_zero_le_ker_normalizedAbsCpowCharacter K s)

/-- **Twisting by `ω_s` preserves the conductor exponent**: `c(ω ω_s) = c(ω)`. -/
@[simp]
theorem characterConductorExp_mul_normalizedAbsCpowCharacter (ω : Kˣ →ₜ* ℂˣ) (s : ℂ) :
    ClassFieldTheory.characterConductorExp K (ω * normalizedAbsCpowCharacter K s) =
      ClassFieldTheory.characterConductorExp K ω :=
  ClassFieldTheory.characterConductorExp_mul_of_unitFiltration_zero_le_ker K ω _
    (unitFiltration_zero_le_ker_normalizedAbsCpowCharacter K s)

/-! ### The exponent of a quasi-character -/

/-- A quasi-character has absolute value one on the compact group `U(K,0) = 𝒪[K]ˣ`. -/
theorem norm_coe_apply_eq_one_of_mem_unitFiltration_zero (ω : Kˣ →ₜ* ℂˣ) {u : Kˣ}
    (hu : u ∈ unitFiltration K 0) : ‖(ω u : ℂ)‖ = 1 := by
  have : CompactSpace (unitFiltration K 0) :=
    isCompact_iff_compactSpace.1 (isCompact_unitFiltration 0)
  exact ContinuousMonoidHom.norm_apply_eq_one_of_compactSpace
    (ω.comp (ContinuousMonoidHom.subgroupSubtype (unitFiltration K 0))) ⟨u, hu⟩

/-- The absolute value of a quasi-character is determined by its value at a uniformizer:
`‖ω(x)‖ = ‖ω(ϖ)‖ ^ v_K(x)`. -/
theorem norm_coe_apply_eq_zpow_of_isUniformizer (ω : Kˣ →ₜ* ℂˣ) {ϖ : Kˣ}
    (hϖ : IsUniformizer K ϖ) (x : Kˣ) :
    ‖(ω x : ℂ)‖ = ‖(ω ϖ : ℂ)‖ ^ (normalizedValuation K x).toAdd := by
  -- `‖ω‖ : Kˣ → ℝˣ` is trivial on `U(K,0)`, so it is the unramified character of `‖ω(ϖ)‖`.
  let δ : Kˣ →* ℝˣ := (Units.map (normHom : ℂ →*₀ ℝ).toMonoidHom).comp ω.toMonoidHom
  have hδ (u : Kˣ) (hu : valuation K (u : K) = 1) : δ u = 1 := Units.ext <|
    norm_coe_apply_eq_one_of_mem_unitFiltration_zero ω ((mem_unitFiltration_zero u).2 hu)
  simpa [δ, unramifiedCharacter_apply] using
    congrArg Units.val (apply_eq_unramifiedCharacter_of_isUniformizer hδ hϖ x)

/-- **The exponent of a quasi-character.** For every quasi-character `ω` of `K` there is a unique
real `σ` with `‖ω(x)‖ = |x| ^ σ` for all `x ∈ Kˣ`. -/
theorem existsUnique_norm_coe_apply_eq_normalizedAbsoluteValue_rpow (ω : Kˣ →ₜ* ℂˣ) :
    ∃! σ : ℝ, ∀ x : Kˣ,
      ‖(ω x : ℂ)‖ = ((normalizedAbsoluteValue K (x : K) : ℚ≥0) : ℝ) ^ σ := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUniformizer K
  have hq := one_lt_natCard_residueField_real K
  have hq₀ := natCard_residueField_pos_real K
  have hϖabs : ((normalizedAbsoluteValue K (ϖ : K) : ℚ≥0) : ℝ) = (Nat.card 𝓀[K] : ℝ)⁻¹ := by
    rw [coe_normalizedAbsoluteValue_eq_zpow, (isUniformizer_def ϖ).1 hϖ, toAdd_ofAdd,
      zpow_neg_one]
  refine ⟨-Real.logb (Nat.card 𝓀[K]) ‖(ω ϖ : ℂ)‖, fun x ↦ ?_, fun σ hσ ↦ ?_⟩
  · -- Both sides are `q` to a real power: `q ^ (logb q ‖ω(ϖ)‖ * v_K(x))` and
    -- `q ^ (-v_K(x) * -logb q ‖ω(ϖ)‖)`.
    rw [norm_coe_apply_eq_zpow_of_isUniformizer ω hϖ, coe_normalizedAbsoluteValue_eq_zpow,
      ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq₀.le]
    nth_rw 1 [← Real.rpow_logb hq₀ hq.ne' (norm_pos_iff.2 (ω ϖ).ne_zero)]
    rw [← Real.rpow_mul hq₀.le]
    congr 1
    push_cast
    ring
  · have h := hσ ϖ
    rw [hϖabs, Real.inv_rpow hq₀.le, ← Real.rpow_neg hq₀.le] at h
    rw [h, Real.logb_rpow hq₀ hq.ne', neg_neg]

variable (K) in
/-- The **exponent** of a quasi-character `ω` of `K`: the unique real `σ` with
`‖ω(x)‖ = |x| ^ σ` for all `x ∈ Kˣ` (`TauCeti.norm_coe_apply_eq_rpow_characterExponent`). -/
def characterExponent (ω : Kˣ →ₜ* ℂˣ) : ℝ :=
  (existsUnique_norm_coe_apply_eq_normalizedAbsoluteValue_rpow ω).exists.choose

/-- The characterizing property of the exponent: `‖ω(x)‖ = |x| ^ σ`. -/
theorem norm_coe_apply_eq_rpow_characterExponent (ω : Kˣ →ₜ* ℂˣ) (x : Kˣ) :
    ‖(ω x : ℂ)‖ = ((normalizedAbsoluteValue K (x : K) : ℚ≥0) : ℝ) ^ characterExponent K ω :=
  (existsUnique_norm_coe_apply_eq_normalizedAbsoluteValue_rpow ω).exists.choose_spec x

/-- The exponent is the only real `σ` with `‖ω(x)‖ = |x| ^ σ` for all `x`. -/
theorem characterExponent_eq_iff (ω : Kˣ →ₜ* ℂˣ) (σ : ℝ) :
    characterExponent K ω = σ ↔
      ∀ x : Kˣ, ‖(ω x : ℂ)‖ = ((normalizedAbsoluteValue K (x : K) : ℚ≥0) : ℝ) ^ σ :=
  ⟨by rintro rfl; exact norm_coe_apply_eq_rpow_characterExponent ω,
    fun h ↦ (existsUnique_norm_coe_apply_eq_normalizedAbsoluteValue_rpow ω).unique
      (norm_coe_apply_eq_rpow_characterExponent ω) h⟩

/-- The exponent of `ω_s` is `re s`. -/
@[simp]
theorem characterExponent_normalizedAbsCpowCharacter (s : ℂ) :
    characterExponent K (normalizedAbsCpowCharacter K s) = s.re :=
  (characterExponent_eq_iff _ _).2 (norm_coe_normalizedAbsCpowCharacter_apply s)

/-- Exponents add under multiplication of quasi-characters. -/
@[simp]
theorem characterExponent_mul (ω χ : Kˣ →ₜ* ℂˣ) :
    characterExponent K (ω * χ) = characterExponent K ω + characterExponent K χ := by
  refine (characterExponent_eq_iff _ _).2 fun x ↦ ?_
  rw [ContinuousMonoidHom.mul_apply, Units.val_mul, norm_mul,
    norm_coe_apply_eq_rpow_characterExponent, norm_coe_apply_eq_rpow_characterExponent,
    Real.rpow_add (coe_normalizedAbsoluteValue_pos x)]

variable (K) in
/-- The trivial character has exponent `0`. -/
@[simp]
theorem characterExponent_one : characterExponent K (1 : Kˣ →ₜ* ℂˣ) = 0 := by
  simpa using characterExponent_normalizedAbsCpowCharacter (K := K) 0

/-- A quasi-character has exponent `0` exactly when it is unitary. -/
theorem characterExponent_eq_zero_iff (ω : Kˣ →ₜ* ℂˣ) :
    characterExponent K ω = 0 ↔ ∀ x : Kˣ, ‖(ω x : ℂ)‖ = 1 := by
  simp [characterExponent_eq_iff]

/-- **Unitary part of a quasi-character.** Twisting `ω` by `ω_{-σ}`, for `σ` its exponent, gives
a unitary character; thus `ω` is a unitary character times `ω_σ`. -/
theorem norm_coe_mul_normalizedAbsCpowCharacter_neg_characterExponent (ω : Kˣ →ₜ* ℂˣ)
    (x : Kˣ) :
    ‖((ω * normalizedAbsCpowCharacter K (-(characterExponent K ω : ℂ))) x : ℂ)‖ = 1 :=
  (characterExponent_eq_zero_iff _).1
    (by rw [characterExponent_mul, characterExponent_normalizedAbsCpowCharacter]; simp) x

end TauCeti
