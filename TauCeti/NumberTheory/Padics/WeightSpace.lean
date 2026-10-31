/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.AddChar
public import TauCeti.NumberTheory.Padics.UnitsDecomposition.Logarithm
import Mathlib.Analysis.Normed.Algebra.Ultra

/-!
# Continuous weights of `ℤ_pˣ` and their parameters

A *weight* with values in a topological monoid `R` is a continuous homomorphism `κ : ℤ_pˣ → Rˣ`
(`TauCeti.WeightSpace p R`). The definition uses only the topologies, not a norm.

Put `q = p` for odd `p` and `q = 4` for `p = 2`, `Δ = (ℤ/qℤ)ˣ` and `γ = exp q`. The decomposition
`TauCeti.padicIntUnitsEquivZModUnitsProd p : ℤ_pˣ ≃ₜ* Δ × ℤ_p`, with section `ω : Δ → ℤ_pˣ`,
`x = ω(x mod q) exp(q s)`, splits a weight into two pieces of data:

* its *finite part* `η = κ ∘ ω : Δ → Rˣ` (`TauCeti.WeightSpace.finiteChar`);
* its *coordinate* `T_κ = κ(γ) - 1` (`TauCeti.WeightSpace.coord`).

The restriction `s ↦ κ(exp(q s))` is a continuous additive character of `ℤ_p`
(`TauCeti.WeightSpace.principalChar`). By Mahler's theorem in the form of Mathlib's
`PadicInt.continuousAddCharEquiv`, when `R` is a normed `ℤ_p`-algebra with contractive action and
ultrametric norm, the coordinate is topologically nilpotent. If `R` is moreover complete, the
character is the binomial series `s ↦ (1 + T_κ) ^ s = ∑ₙ (s choose n) T_κⁿ`. Conversely, if `R`
is complete and commutative, every pair of a homomorphism `η : Δ → Rˣ` and a topologically
nilpotent `t ∈ R` comes from a unique weight,

`κ(x) = η(x mod q) · (1 + t) ^ (log (x / ω(x mod q)) / q)`   (`TauCeti.WeightSpace.ofCoord`).

Together these give the parametrisation `TauCeti.weightSpaceEquiv p R` of the weights by
`(Δ →* Rˣ) × {t : R // tⁿ → 0}`. For a multiplicative norm, as over a normed field, topological
nilpotence is the condition `‖T_κ‖ < 1` (`TauCeti.WeightSpace.norm_coord_lt_one`). Over a normed
division ring over `ℚ_p`, such as the field `ℂ_p`, this holds with no further hypotheses
(`TauCeti.WeightSpace.norm_coord_lt_one_of_normedAlgebra`).

## Main definitions

* `TauCeti.WeightSpace p R`: the continuous homomorphisms `ℤ_pˣ →ₜ* Rˣ`.
* `TauCeti.WeightSpace.finiteChar κ`: the finite part `κ ∘ ω : Δ →* Rˣ`.
* `TauCeti.WeightSpace.principalChar κ`: the additive character `s ↦ κ(exp(q s))` of `ℤ_p`.
* `TauCeti.WeightSpace.coord κ`: the coordinate `T_κ = κ(γ) - 1`.
* `TauCeti.WeightSpace.ofCoord η t ht`: the weight with finite part `η` and coordinate `t`.
* `TauCeti.weightSpaceEquiv p R`: the parametrisation `κ ↦ (η, T_κ)`.

## Main results

* `TauCeti.WeightSpace.tendsto_coord_pow`: the coordinate of a weight is topologically nilpotent.
* `TauCeti.WeightSpace.norm_coord_lt_one_of_normedAlgebra`: over a normed division ring over
  `ℚ_p`, such as `ℂ_p`, the coordinate of a weight has norm less than one.
* `TauCeti.WeightSpace.principalChar_eq_addChar_of_value_at_one`: over a complete `R`, the principal
  part of a weight is the binomial character `s ↦ (1 + T_κ) ^ s`.
* `TauCeti.WeightSpace.ofCoord_finiteChar_coord`, `TauCeti.WeightSpace.finiteChar_ofCoord`,
  `TauCeti.WeightSpace.coord_ofCoord`: the two constructions are mutually inverse.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §§3–4.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.3.
-/

public section

open Filter Topology

namespace TauCeti

variable (p : ℕ) [Fact p.Prime]

/-- The *weight space* of `ℤ_pˣ` with values in a topological monoid `R`: the continuous
homomorphisms `ℤ_pˣ → Rˣ`. -/
abbrev WeightSpace (R : Type*) [Monoid R] [TopologicalSpace R] : Type _ :=
  ℤ_[p]ˣ →ₜ* Rˣ

namespace WeightSpace

variable {p}

section Monoid

variable {R : Type*} [Monoid R] [TopologicalSpace R]

/-- The *finite part* `κ ∘ ω : (ℤ/qℤ)ˣ → Rˣ` of a weight `κ`, where `ω` is the section
`TauCeti.padicUnitsSection p`. -/
noncomputable def finiteChar (κ : WeightSpace p R) : (ZMod (p ^ padicUnitsDepth p))ˣ →* Rˣ :=
  κ.toMonoidHom.comp (padicUnitsSection p)

@[simp]
theorem finiteChar_apply (κ : WeightSpace p R) (δ : (ZMod (p ^ padicUnitsDepth p))ˣ) :
    κ.finiteChar δ = κ (padicUnitsSection p δ) :=
  (rfl)

/-- The *principal part* of a weight `κ`: the additive character `s ↦ κ(exp(q s))` of `ℤ_p`,
the restriction of `κ` to `1 + qℤ_p` read through `TauCeti.unitsPrincipalLogEquiv p`. -/
noncomputable def principalChar (κ : WeightSpace p R) : AddChar ℤ_[p] R where
  toFun s := κ ((unitsPrincipalLogEquiv p).symm (.ofAdd s))
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [ofAdd_add]

@[simp]
theorem principalChar_apply (κ : WeightSpace p R) (s : ℤ_[p]) :
    κ.principalChar s = κ ((unitsPrincipalLogEquiv p).symm (.ofAdd s)) :=
  (rfl)

theorem principalChar_one (κ : WeightSpace p R) :
    κ.principalChar 1 = κ (padicUnitsGenerator p) := by
  rw [principalChar_apply, ← unitsPrincipalLogEquiv_padicUnitsGenerator,
    ContinuousMulEquiv.symm_apply_apply]

theorem continuous_principalChar (κ : WeightSpace p R) : Continuous κ.principalChar :=
  Units.continuous_val.comp <| κ.continuous.comp <| continuous_subtype_val.comp <|
    (unitsPrincipalLogEquiv p).symm.continuous.comp continuous_ofAdd

/-- A weight is determined by its finite part and its principal part. -/
theorem apply_eq_finiteChar_mul_principalChar (κ : WeightSpace p R) (x : ℤ_[p]ˣ) :
    (κ x : R) = κ.finiteChar (padicIntUnitsEquivZModUnitsProd p x).1 *
      κ.principalChar (padicIntUnitsEquivZModUnitsProd p x).2.toAdd := by
  rw [finiteChar_apply, principalChar_apply, ofAdd_toAdd, ← Units.val_mul, ← map_mul,
    ← padicIntUnitsEquivZModUnitsProd_symm_apply, ContinuousMulEquiv.symm_apply_apply]

end Monoid

section Ring

variable {R : Type*} [Ring R] [TopologicalSpace R]

/-- The *coordinate* `T_κ = κ(γ) - 1` of a weight `κ`, where `γ = exp q` is
`TauCeti.padicUnitsGenerator p`. -/
noncomputable def coord (κ : WeightSpace p R) : R :=
  κ (padicUnitsGenerator p) - 1

theorem coord_def (κ : WeightSpace p R) : κ.coord = κ (padicUnitsGenerator p) - 1 :=
  (rfl)

theorem principalChar_one_eq_one_add_coord (κ : WeightSpace p R) :
    κ.principalChar 1 = 1 + κ.coord := by
  rw [principalChar_one, coord_def, add_sub_cancel]

end Ring

section Normed

variable {R : Type*} [NormedRing R] [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R]
  [IsUltrametricDist R]

/-- The coordinate of a weight is topologically nilpotent. -/
theorem tendsto_coord_pow (κ : WeightSpace p R) : Tendsto (κ.coord ^ ·) atTop (𝓝 0) := by
  simpa only [principalChar_one, coord_def] using
    κ.principalChar.tendsto_eval_one_sub_pow κ.continuous_principalChar

/-- For a multiplicative norm, as over a normed field, the coordinate of a weight has norm less
than one. -/
theorem norm_coord_lt_one [NormMulClass R] (κ : WeightSpace p R) : ‖κ.coord‖ < 1 :=
  tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp κ.tendsto_coord_pow

/-- Over a complete `R`, the principal part of a weight `κ` is the binomial character
`s ↦ (1 + T_κ) ^ s`, the Mahler series `∑ₙ (s choose n) T_κⁿ`. -/
theorem principalChar_eq_addChar_of_value_at_one [CompleteSpace R] (κ : WeightSpace p R) :
    κ.principalChar = PadicInt.addChar_of_value_at_one κ.coord κ.tendsto_coord_pow :=
  PadicInt.eq_addChar_of_value_at_one _ κ.continuous_principalChar
    κ.principalChar_one_eq_one_add_coord

end Normed

/-- Over a normed division ring `K` that is a normed `ℚ_p`-algebra, such as `ℂ_p`, the coordinate
of a weight has norm less than one. The `ℤ_p`-algebra structure and the ultrametric property of
`K` needed by `TauCeti.WeightSpace.norm_coord_lt_one` come from the `ℚ_p`-algebra structure. -/
theorem norm_coord_lt_one_of_normedAlgebra {K : Type*} [NormedDivisionRing K]
    [NormedAlgebra ℚ_[p] K] (κ : WeightSpace p K) : ‖κ.coord‖ < 1 := by
  let : Algebra ℤ_[p] K := Algebra.compHom K (algebraMap ℤ_[p] ℚ_[p])
  have : IsBoundedSMul ℤ_[p] K := .of_norm_smul_le fun r x ↦ norm_smul_le (r : ℚ_[p]) x
  have := IsUltrametricDist.of_normedAlgebra ℚ_[p] (L := K)
  exact norm_coord_lt_one κ

section Construction

variable {R : Type*} [NormedCommRing R] [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R]
  [IsUltrametricDist R] [CompleteSpace R]

/-- The weight with finite part `η` and coordinate `t`, for `t` topologically nilpotent:
`x ↦ η(x mod q) · (1 + t) ^ s` where `x = ω(x mod q) exp(q s)`, the binomial power being Mathlib's
`PadicInt.addChar_of_value_at_one t ht`. -/
noncomputable def ofCoord (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Rˣ) (t : R)
    (ht : Tendsto (t ^ ·) atTop (𝓝 0)) : WeightSpace p R where
  toMonoidHom := (η.coprod (PadicInt.addChar_of_value_at_one t ht).toMonoidHom.toHomUnits).comp
    (padicIntUnitsEquivZModUnitsProd p).toMonoidHom
  continuous_toFun := by
    set e := padicIntUnitsEquivZModUnitsProd p
    set f := (η.coprod (PadicInt.addChar_of_value_at_one t ht).toMonoidHom.toHomUnits).comp
      e.toMonoidHom
    -- A homomorphism from a group to `Rˣ` is continuous once its values in `R` are, since
    -- inversion in `Rˣ` is read off by precomposing with inversion in the source.
    have h : Continuous fun x ↦ (f x : R) :=
      (Units.continuous_val.comp <| (continuous_of_discreteTopology (f := η)).comp <|
        continuous_fst.comp e.continuous).mul <|
        (PadicInt.continuous_addChar_of_value_at_one ht).comp <| continuous_toAdd.comp <|
          continuous_snd.comp e.continuous
    have hf : Continuous f := Units.continuous_iff.mpr
      ⟨h, by simpa only [Function.comp_def, ← map_inv] using h.comp continuous_inv⟩
    exact hf

@[simp]
theorem coe_ofCoord_apply (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Rˣ) (t : R)
    (ht : Tendsto (t ^ ·) atTop (𝓝 0)) (x : ℤ_[p]ˣ) :
    (ofCoord η t ht x : R) = η (padicIntUnitsEquivZModUnitsProd p x).1 *
      PadicInt.addChar_of_value_at_one t ht (padicIntUnitsEquivZModUnitsProd p x).2.toAdd :=
  (rfl)

@[simp]
theorem finiteChar_ofCoord (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Rˣ) (t : R)
    (ht : Tendsto (t ^ ·) atTop (𝓝 0)) : (ofCoord η t ht).finiteChar = η := by
  ext δ
  simp

@[simp]
theorem coord_ofCoord (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Rˣ) (t : R)
    (ht : Tendsto (t ^ ·) atTop (𝓝 0)) : (ofCoord η t ht).coord = t := by
  rw [coord_def, coe_ofCoord_apply, padicIntUnitsEquivZModUnitsProd_padicUnitsGenerator]
  simp

@[simp]
theorem ofCoord_finiteChar_coord (κ : WeightSpace p R) :
    ofCoord κ.finiteChar κ.coord κ.tendsto_coord_pow = κ := by
  ext x
  rw [coe_ofCoord_apply, ← principalChar_eq_addChar_of_value_at_one,
    apply_eq_finiteChar_mul_principalChar]

end Construction

end WeightSpace

section Equiv

variable (R : Type*) [NormedCommRing R] [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R]
  [IsUltrametricDist R] [CompleteSpace R]

/-- **The parametrisation of the weights of `ℤ_pˣ`.** For a complete ultrametric normed
commutative `ℤ_p`-algebra `R` with contractive action, a weight `κ` is determined by its finite
part `η = κ ∘ ω : (ℤ/qℤ)ˣ →* Rˣ` and its coordinate `T_κ = κ(γ) - 1`, which is topologically
nilpotent, and every such pair arises. -/
noncomputable def weightSpaceEquiv :
    WeightSpace p R ≃
      ((ZMod (p ^ padicUnitsDepth p))ˣ →* Rˣ) × {t : R // Tendsto (t ^ ·) atTop (𝓝 0)} where
  toFun κ := (κ.finiteChar, ⟨κ.coord, κ.tendsto_coord_pow⟩)
  invFun ηt := WeightSpace.ofCoord ηt.1 ηt.2 ηt.2.2
  left_inv := WeightSpace.ofCoord_finiteChar_coord
  right_inv ηt := by ext <;> simp

@[simp]
theorem weightSpaceEquiv_apply (κ : WeightSpace p R) :
    weightSpaceEquiv p R κ = (κ.finiteChar, ⟨κ.coord, κ.tendsto_coord_pow⟩) :=
  (rfl)

@[simp]
theorem weightSpaceEquiv_symm_apply
    (ηt : ((ZMod (p ^ padicUnitsDepth p))ˣ →* Rˣ) × {t : R // Tendsto (t ^ ·) atTop (𝓝 0)}) :
    (weightSpaceEquiv p R).symm ηt = WeightSpace.ofCoord ηt.1 ηt.2 ηt.2.2 :=
  (rfl)

end Equiv

end TauCeti
