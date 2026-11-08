/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.AddChar
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.NumberTheory.Padics.AddChar
public import TauCeti.NumberTheory.Padics.Basic
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

The same parametrisation holds over a complete separated linearly topologised commutative
`ℤ_p`-algebra `S`, with Mathlib's evaluation of power series in place of Mahler series. The
coordinate of every weight is topologically nilpotent (`TauCeti.WeightSpace.hasEval_coord`), so the
binomial series `(1 + X) ^ s ∈ ℤ_p⟦X⟧` can be evaluated at it, and
`κ(x) = η(x mod q) · (1 + T_κ) ^ s`
(`TauCeti.WeightSpace.apply_eq_finiteChar_mul_aeval_binomialSeries`). Conversely every pair of a
homomorphism `η : Δ →* Sˣ` and a topologically nilpotent `z ∈ S` is the finite part and the
coordinate of exactly one weight, `TauCeti.WeightSpace.ofHasEval η hz`
(`TauCeti.WeightSpace.existsUnique_character_of_hasEval`), which gives the parametrisation
`TauCeti.adicWeightSpaceEquiv p S`. When `S` is both normed and linearly
topologised, as `ℤ_p` is, the two constructions agree (`TauCeti.WeightSpace.ofHasEval_eq_ofCoord`).

## Main definitions

* `TauCeti.WeightSpace p R`: the continuous homomorphisms `ℤ_pˣ →ₜ* Rˣ`.
* `TauCeti.WeightSpace.weightTest κ`: a weight `κ`, viewed as the scalar-valued continuous
  character `x ↦ (κ x : R)`.
* `TauCeti.WeightSpace.inclusion K`: the weight `x ↦ x` with values in a normed `ℚ_p`-algebra
  `K`.
* `TauCeti.WeightSpace.finiteChar κ`: the finite part `κ ∘ ω : Δ →* Rˣ`.
* `TauCeti.WeightSpace.principalChar κ`: the additive character `s ↦ κ(exp(q s))` of `ℤ_p`.
* `TauCeti.WeightSpace.coord κ`: the coordinate `T_κ = κ(γ) - 1`.
* `TauCeti.WeightSpace.ofAddChar η ψ hψ`: the weight with finite part `η` and principal part `ψ`.
* `TauCeti.WeightSpace.ofCoord η t ht`: the weight with finite part `η` and coordinate `t`.
* `TauCeti.WeightSpace.ofHasEval η hz`: the same weight over a complete linearly topologised
  algebra.
* `TauCeti.weightSpaceEquiv p R`: the parametrisation `κ ↦ (η, T_κ)`.
* `TauCeti.adicWeightSpaceEquiv p S`: the same parametrisation over a complete linearly
  topologised algebra.

## Main results

* `TauCeti.WeightSpace.tendsto_coord_pow`: the coordinate of a weight is topologically nilpotent.
* `TauCeti.WeightSpace.norm_coord_lt_one_of_normedAlgebra`: over a normed division ring over
  `ℚ_p`, such as `ℂ_p`, the coordinate of a weight has norm less than one.
* `TauCeti.WeightSpace.principalChar_eq_addChar_of_value_at_one`: over a complete `R`, the principal
  part of a weight is the binomial character `s ↦ (1 + T_κ) ^ s`.
* `TauCeti.WeightSpace.ofCoord_finiteChar_coord`, `TauCeti.WeightSpace.finiteChar_ofCoord`,
  `TauCeti.WeightSpace.coord_ofCoord`: the two constructions are mutually inverse.
* `TauCeti.WeightSpace.coord_mul`: the coordinate of a product of weights.
* `TauCeti.WeightSpace.unitsPrincipal_le_ker_iff`: `κ` is trivial on `1 + q pʲ ℤ_p` exactly when
  `κ(γ) ^ (p ^ j) = 1`.
* `TauCeti.WeightSpace.coord_eq_zero_iff`: `T_κ = 0` exactly when `κ` is trivial on `1 + qℤ_p`.
* `TauCeti.WeightSpace.isPrimitiveRoot_apply_padicUnitsGenerator`: for exact conductor
  `p ^ (k + j + 1)`, `κ(γ)` is a primitive `p ^ (j + 1)`-th root of unity.
* `TauCeti.WeightSpace.ext_finiteChar_coord`: over a Hausdorff ring a weight is determined by its
  finite part and its coordinate.
* `TauCeti.WeightSpace.hasEval_coord`,
  `TauCeti.WeightSpace.apply_eq_finiteChar_mul_aeval_binomialSeries`: over a linearly topologised
  algebra the coordinate is topologically nilpotent, and the weight is given by the binomial series
  evaluated at it.
* `TauCeti.WeightSpace.existsUnique_character_of_hasEval`: the adic universal property, every
  finite part and topologically nilpotent coordinate come from a unique weight.
* `TauCeti.WeightSpace.ofHasEval_eq_ofCoord`: agreement of the adic and normed constructions.

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

/-- A weight `κ : ℤ_pˣ → Rˣ`, viewed as the `R`-valued continuous character `x ↦ (κ x : R)`.
Its underlying continuous function is the test function integrated against measures. -/
noncomputable def weightTest (κ : WeightSpace p R) : ℤ_[p]ˣ →ₜ* R where
  toMonoidHom := (Units.coeHom R).comp κ.toMonoidHom
  continuous_toFun := Units.continuous_val.comp κ.continuous

@[simp]
theorem weightTest_apply (κ : WeightSpace p R) (x : ℤ_[p]ˣ) : κ.weightTest x = (κ x : R) :=
  (rfl)

/-- A weight is determined by its scalar-valued character. -/
theorem weightTest_injective : Function.Injective (weightTest (p := p) (R := R)) :=
  fun κ κ' h ↦ ContinuousMonoidHom.ext fun x ↦ Units.ext (by simpa using congr($h x))

@[simp]
theorem weightTest_inj {κ κ' : WeightSpace p R} : κ.weightTest = κ'.weightTest ↔ κ = κ' :=
  weightTest_injective.eq_iff

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

/-- A weight `κ` is trivial on `1 + q pʲ ℤ_p` exactly when `κ(γ) ^ (p ^ j) = 1`, where
`γ = exp q`: the power `γ ^ (p ^ j)` topologically generates `1 + q pʲ ℤ_p`. -/
theorem unitsPrincipal_le_ker_iff [T2Space R] (κ : WeightSpace p R) (j : ℕ) :
    unitsPrincipal p (padicUnitsDepth p + j) ≤ κ.toMonoidHom.ker ↔
      κ (padicUnitsGenerator p) ^ p ^ j = 1 := by
  have hk := padicUnitsDepth_pos p
  have hmem := pow_pow_mem_unitsPrincipal hk padicUnitsGenerator_mem_unitsPrincipal j
  refine ⟨fun h ↦ by simpa using h hmem, fun h ↦ ?_⟩
  rw [← topologicalClosure_zpowers_eq_unitsPrincipal (by omega)
    (fun h ↦ (two_le_padicUnitsDepth h).trans (Nat.le_add_right _ _)) hmem
    (pow_pow_notMem_unitsPrincipal hk two_le_padicUnitsDepth padicUnitsGenerator_mem_unitsPrincipal
      padicUnitsGenerator_notMem_unitsPrincipal_succ j)]
  refine Subgroup.topologicalClosure_minimal _ ?_ (isClosed_singleton.preimage κ.continuous)
  rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
  simpa using h

end Monoid

section CommMonoid

section
variable {R : Type*} [CommMonoid R] [TopologicalSpace R] [T2Space R]

/-- If a weight `κ` has exact conductor `p ^ (k + j + 1)`, where `q = p ^ k`, that is, `κ` is
trivial on `1 + p ^ (k + j + 1) ℤ_p` but not on `1 + p ^ (k + j) ℤ_p`, then `κ(γ)` is a primitive
`p ^ (j + 1)`-th root of unity. -/
theorem isPrimitiveRoot_apply_padicUnitsGenerator (κ : WeightSpace p R) {j : ℕ}
    (h : unitsPrincipal p (padicUnitsDepth p + j + 1) ≤ κ.toMonoidHom.ker)
    (h' : ¬unitsPrincipal p (padicUnitsDepth p + j) ≤ κ.toMonoidHom.ker) :
    IsPrimitiveRoot (κ (padicUnitsGenerator p) : R) (p ^ (j + 1)) := by
  rw [IsPrimitiveRoot.coe_units_iff]
  rw [unitsPrincipal_le_ker_iff] at h'
  rw [add_assoc, unitsPrincipal_le_ker_iff] at h
  exact orderOf_eq_prime_pow h' h ▸ IsPrimitiveRoot.orderOf _

end
variable {R : Type*} [CommMonoid R] [TopologicalSpace R] [ContinuousMul R]

/-- The weight with finite part `η` and principal part `ψ`, for a continuous additive character
`ψ` of `ℤ_p`: `x ↦ η(x mod q) · ψ(s)` where `x = ω(x mod q) exp(q s)`. -/
noncomputable def ofAddChar (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Rˣ) (ψ : AddChar ℤ_[p] R)
    (hψ : Continuous ψ) : WeightSpace p R where
  toMonoidHom := (η.coprod ψ.toMonoidHom.toHomUnits).comp
    (padicIntUnitsEquivZModUnitsProd p).toMonoidHom
  continuous_toFun := by
    set e := padicIntUnitsEquivZModUnitsProd p
    set f := (η.coprod ψ.toMonoidHom.toHomUnits).comp e.toMonoidHom
    -- A homomorphism from a group to `Rˣ` is continuous once its values in `R` are, since
    -- inversion in `Rˣ` is read off by precomposing with inversion in the source.
    have h : Continuous fun x ↦ (f x : R) :=
      (Units.continuous_val.comp <| (continuous_of_discreteTopology (f := η)).comp <|
        continuous_fst.comp e.continuous).mul <|
        hψ.comp <| continuous_toAdd.comp <| continuous_snd.comp e.continuous
    have hf : Continuous f := Units.continuous_iff.mpr
      ⟨h, by simpa only [Function.comp_def, ← map_inv] using h.comp continuous_inv⟩
    exact hf

@[simp]
theorem coe_ofAddChar_apply (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Rˣ) (ψ : AddChar ℤ_[p] R)
    (hψ : Continuous ψ) (x : ℤ_[p]ˣ) :
    (ofAddChar η ψ hψ x : R) = η (padicIntUnitsEquivZModUnitsProd p x).1 *
      ψ (padicIntUnitsEquivZModUnitsProd p x).2.toAdd :=
  (rfl)

@[simp]
theorem finiteChar_ofAddChar (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Rˣ) (ψ : AddChar ℤ_[p] R)
    (hψ : Continuous ψ) : (ofAddChar η ψ hψ).finiteChar = η := by
  ext δ
  simp

@[simp]
theorem principalChar_ofAddChar (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Rˣ)
    (ψ : AddChar ℤ_[p] R) (hψ : Continuous ψ) : (ofAddChar η ψ hψ).principalChar = ψ := by
  ext s
  have he : padicIntUnitsEquivZModUnitsProd p ((unitsPrincipalLogEquiv p).symm (.ofAdd s)) =
      (1, .ofAdd s) := by
    rw [← (padicIntUnitsEquivZModUnitsProd p).apply_symm_apply (1, .ofAdd s),
      padicIntUnitsEquivZModUnitsProd_symm_apply, map_one, one_mul]
  simp [he]

@[simp]
theorem ofAddChar_finiteChar_principalChar (κ : WeightSpace p R) :
    ofAddChar κ.finiteChar κ.principalChar κ.continuous_principalChar = κ := by
  ext x
  rw [coe_ofAddChar_apply, apply_eq_finiteChar_mul_principalChar]

end CommMonoid

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

/-- The coordinate of a weight vanishes exactly when the weight is trivial on `1 + qℤ_p`, that is,
when its conductor divides `q`. -/
theorem coord_eq_zero_iff [T2Space R] (κ : WeightSpace p R) :
    κ.coord = 0 ↔ unitsPrincipal p (padicUnitsDepth p) ≤ κ.toMonoidHom.ker := by
  simpa [coord_def, sub_eq_zero, Units.val_eq_one] using (unitsPrincipal_le_ker_iff κ 0).symm

/-- The trivial weight has coordinate zero. -/
@[simp]
theorem coord_one : (1 : WeightSpace p R).coord = 0 := by
  simp [coord_def]

theorem coord_eq_principalChar_one_sub (κ : WeightSpace p R) :
    κ.coord = κ.principalChar 1 - 1 := by
  rw [coord_def, principalChar_one]

/-- Over a Hausdorff ring, a weight is determined by its finite part and its coordinate: its
principal part is a continuous additive character of `ℤ_p`, determined by its value
`1 + T_κ` at `1`. -/
theorem ext_finiteChar_coord [T2Space R] {κ κ' : WeightSpace p R}
    (hη : κ.finiteChar = κ'.finiteChar) (ht : κ.coord = κ'.coord) : κ = κ' := by
  have hψ : κ.principalChar = κ'.principalChar :=
    PadicInt.denseRange_natCast.addChar_eq_of_eval_one_eq κ.continuous_principalChar
      κ'.continuous_principalChar (by rw [principalChar_one_eq_one_add_coord,
        principalChar_one_eq_one_add_coord, ht])
  ext x
  rw [apply_eq_finiteChar_mul_principalChar, apply_eq_finiteChar_mul_principalChar, hη, hψ]

end Ring

section CommRing

variable {R : Type*} [CommRing R] [TopologicalSpace R] [ContinuousMul R]

@[simp]
theorem coord_ofAddChar (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Rˣ) (ψ : AddChar ℤ_[p] R)
    (hψ : Continuous ψ) : (ofAddChar η ψ hψ).coord = ψ 1 - 1 := by
  rw [coord_eq_principalChar_one_sub, principalChar_ofAddChar]

end CommRing


/-- The coordinates of weights multiply after adding one: `1 + T_{κκ'} = (1 + T_κ)(1 + T_κ')`. -/
theorem coord_mul {R : Type*} [CommRing R] [TopologicalSpace R] [ContinuousMul R]
    (κ κ' : WeightSpace p R) : (κ * κ').coord = κ.coord * κ'.coord + κ.coord + κ'.coord := by
  simp only [coord_def, ContinuousMonoidHom.mul_apply, Units.val_mul]
  ring

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

section Inclusion

variable (K : Type*) [SeminormedRing K] [NormedAlgebra ℚ_[p] K]

/-- The weight `x ↦ x` of `ℤ_pˣ` with values in a normed `ℚ_p`-algebra `K`. Its powers are the
algebraic weights `x ↦ x ^ k`. -/
noncomputable def inclusion : WeightSpace p K where
  toMonoidHom := Units.map (padicIntAlgebraMap p K).toMonoidHom
  continuous_toFun := Continuous.units_map _ continuous_padicIntAlgebraMap

variable {K}

@[simp]
theorem coe_inclusion_apply (x : ℤ_[p]ˣ) :
    (inclusion K x : K) = padicIntAlgebraMap p K x :=
  (rfl)

/-- Distinct units of `ℤ_p` give distinct values of the weight `x ↦ x` in a nontrivial `K`. -/
theorem inclusion_injective [Nontrivial K] : Function.Injective (inclusion (p := p) K) :=
  fun x y hxy ↦ Units.ext <| padicIntAlgebraMap_injective (K := K) <| by
    rw [← coe_inclusion_apply, ← coe_inclusion_apply, hxy]

end Inclusion

section Construction

variable {R : Type*} [NormedCommRing R] [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R]
  [IsUltrametricDist R] [CompleteSpace R]

/-- The weight with finite part `η` and coordinate `t`, for `t` topologically nilpotent:
`x ↦ η(x mod q) · (1 + t) ^ s` where `x = ω(x mod q) exp(q s)`, the binomial power being Mathlib's
`PadicInt.addChar_of_value_at_one t ht`. -/
noncomputable def ofCoord (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Rˣ) (t : R)
    (ht : Tendsto (t ^ ·) atTop (𝓝 0)) : WeightSpace p R :=
  ofAddChar η (PadicInt.addChar_of_value_at_one t ht)
    (PadicInt.continuous_addChar_of_value_at_one ht)

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
  rw [ofCoord, coord_ofAddChar, PadicInt.addChar_of_value_at_one_def, add_sub_cancel_left]

@[simp]
theorem ofCoord_finiteChar_coord (κ : WeightSpace p R) :
    ofCoord κ.finiteChar κ.coord κ.tendsto_coord_pow = κ := by
  ext x
  rw [coe_ofCoord_apply, ← principalChar_eq_addChar_of_value_at_one,
    apply_eq_finiteChar_mul_principalChar]

end Construction

section Adic

/-! ### Weights in complete linearly topologised algebras

Over a complete separated linearly topologised `ℤ_p`-algebra `S` the coordinate of every weight
satisfies `PowerSeries.HasEval`, and the principal part is the binomial series evaluated at it. -/

/-- The coordinate of a weight with values in a linearly topologised `ℤ_p`-algebra is
topologically nilpotent, so power series over `ℤ_p` can be evaluated at it. -/
theorem hasEval_coord {S : Type*} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [IsLinearTopology S S] [Algebra ℤ_[p] S] [ContinuousSMul ℤ_[p] S] (κ : WeightSpace p S) :
    PowerSeries.HasEval κ.coord := by
  rw [PowerSeries.hasEval_def, coord_eq_principalChar_one_sub]
  exact AddChar.isTopologicallyNilpotent_eval_one_sub κ.continuous_principalChar

variable {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [IsTopologicalRing S]
  [IsLinearTopology S S] [CompleteSpace S] [T2Space S] [Algebra ℤ_[p] S]
  [ContinuousSMul ℤ_[p] S]

/-- The weight with finite part `η` and coordinate `z`, for `z` topologically nilpotent in a
complete linearly topologised `ℤ_p`-algebra: `x ↦ η(x mod q) · (1 + z) ^ s` where
`x = ω(x mod q) exp(q s)`, the binomial power being the binomial series `(1 + X) ^ s` evaluated at
`z` (`PadicInt.binomialAddChar`). -/
noncomputable def ofHasEval (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Sˣ) {z : S}
    (hz : PowerSeries.HasEval z) : WeightSpace p S :=
  ofAddChar η (PadicInt.binomialAddChar hz) (PadicInt.continuous_binomialAddChar hz)

@[simp]
theorem coe_ofHasEval_apply (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Sˣ) {z : S}
    (hz : PowerSeries.HasEval z) (x : ℤ_[p]ˣ) :
    (ofHasEval η hz x : S) = η (padicIntUnitsEquivZModUnitsProd p x).1 *
      PadicInt.binomialAddChar hz (padicIntUnitsEquivZModUnitsProd p x).2.toAdd :=
  (rfl)

@[simp]
theorem finiteChar_ofHasEval (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Sˣ) {z : S}
    (hz : PowerSeries.HasEval z) : (ofHasEval η hz).finiteChar = η :=
  finiteChar_ofAddChar _ _ _

@[simp]
theorem principalChar_ofHasEval (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Sˣ) {z : S}
    (hz : PowerSeries.HasEval z) : (ofHasEval η hz).principalChar = PadicInt.binomialAddChar hz :=
  principalChar_ofAddChar _ _ _

@[simp]
theorem coord_ofHasEval (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Sˣ) {z : S}
    (hz : PowerSeries.HasEval z) : (ofHasEval η hz).coord = z := by
  rw [ofHasEval, coord_ofAddChar, PadicInt.binomialAddChar_one, add_sub_cancel_left]

/-- The principal part of a weight with values in a complete linearly topologised `ℤ_p`-algebra is
the binomial character `s ↦ (1 + T_κ) ^ s` of its coordinate. -/
theorem principalChar_eq_binomialAddChar (κ : WeightSpace p S) :
    κ.principalChar = PadicInt.binomialAddChar κ.hasEval_coord :=
  PadicInt.eq_binomialAddChar _ κ.continuous_principalChar κ.principalChar_one_eq_one_add_coord

/-- **The binomial formula for a weight.** A weight `κ` with values in a complete linearly
topologised `ℤ_p`-algebra is `κ(x) = η(x mod q) · (1 + T_κ) ^ s` for `x = ω(x mod q) exp(q s)`,
where `η` is its finite part and `(1 + T_κ) ^ s` is the binomial series `(1 + X) ^ s` evaluated at
its coordinate `T_κ`. -/
theorem apply_eq_finiteChar_mul_aeval_binomialSeries (κ : WeightSpace p S) (x : ℤ_[p]ˣ) :
    (κ x : S) = κ.finiteChar (padicIntUnitsEquivZModUnitsProd p x).1 *
      PowerSeries.aeval κ.hasEval_coord
        (PowerSeries.binomialSeries ℤ_[p] (padicIntUnitsEquivZModUnitsProd p x).2.toAdd) := by
  rw [apply_eq_finiteChar_mul_principalChar, principalChar_eq_binomialAddChar,
    PadicInt.binomialAddChar_apply]

@[simp]
theorem ofHasEval_finiteChar_coord (κ : WeightSpace p S) :
    ofHasEval κ.finiteChar κ.hasEval_coord = κ :=
  ext_finiteChar_coord (by simp) (by simp)

/-- **The adic universal property of the weights of `ℤ_pˣ`.** Over a complete separated linearly
topologised `ℤ_p`-algebra `S`, every pair of a homomorphism `η : (ℤ/qℤ)ˣ →* Sˣ` and an element
`z ∈ S` at which power series over `ℤ_p` can be evaluated is the finite part and the coordinate of
exactly one weight, namely `TauCeti.WeightSpace.ofHasEval η hz`. -/
theorem existsUnique_character_of_hasEval (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Sˣ) {z : S}
    (hz : PowerSeries.HasEval z) :
    ∃! κ : WeightSpace p S, κ.finiteChar = η ∧ κ.coord = z :=
  ⟨ofHasEval η hz, ⟨by simp, by simp⟩, fun κ ⟨hη, ht⟩ ↦
    ext_finiteChar_coord (by rw [hη, finiteChar_ofHasEval]) (by rw [ht, coord_ofHasEval])⟩

end Adic

section AdicNormed

variable {S : Type*} [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]
  [IsLinearTopology S S] [Algebra ℤ_[p] S] [IsBoundedSMul ℤ_[p] S]

/-- **The adic and normed constructions of weights agree** on a complete ultrametric normed
`ℤ_p`-algebra whose topology is also linear, such as `ℤ_p`. Topological nilpotence
`PowerSeries.HasEval z` is by definition the convergence `z ^ n → 0` assumed by
`TauCeti.WeightSpace.ofCoord`. -/
theorem ofHasEval_eq_ofCoord (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Sˣ) {z : S}
    (hz : PowerSeries.HasEval z) : ofHasEval η hz = ofCoord η z hz :=
  ext_finiteChar_coord ((finiteChar_ofHasEval η hz).trans (finiteChar_ofCoord η z hz).symm)
    ((coord_ofHasEval η hz).trans (coord_ofCoord η z hz).symm)

end AdicNormed

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

section AdicEquiv

variable (S : Type*) [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [IsTopologicalRing S]
  [IsLinearTopology S S] [CompleteSpace S] [T2Space S] [Algebra ℤ_[p] S]
  [ContinuousSMul ℤ_[p] S]

/-- **The adic parametrisation of the weights of `ℤ_pˣ`.** For a complete separated linearly
topologised commutative `ℤ_p`-algebra `S`, a weight `κ` is determined by its finite part
`η = κ ∘ ω : (ℤ/qℤ)ˣ →* Sˣ` and its coordinate `T_κ = κ(γ) - 1`, at which power series over `ℤ_p`
can be evaluated, and every such pair arises, through `TauCeti.WeightSpace.ofHasEval`. -/
noncomputable def adicWeightSpaceEquiv :
    WeightSpace p S ≃
      ((ZMod (p ^ padicUnitsDepth p))ˣ →* Sˣ) × {z : S // PowerSeries.HasEval z} where
  toFun κ := (κ.finiteChar, ⟨κ.coord, κ.hasEval_coord⟩)
  invFun ηz := WeightSpace.ofHasEval ηz.1 ηz.2.2
  left_inv := WeightSpace.ofHasEval_finiteChar_coord
  right_inv ηz := by ext <;> simp

@[simp]
theorem adicWeightSpaceEquiv_apply (κ : WeightSpace p S) :
    adicWeightSpaceEquiv p S κ = (κ.finiteChar, ⟨κ.coord, κ.hasEval_coord⟩) :=
  (rfl)

@[simp]
theorem adicWeightSpaceEquiv_symm_apply
    (ηz : ((ZMod (p ^ padicUnitsDepth p))ˣ →* Sˣ) × {z : S // PowerSeries.HasEval z}) :
    (adicWeightSpaceEquiv p S).symm ηz = WeightSpace.ofHasEval ηz.1 ηz.2.2 :=
  (rfl)

end AdicEquiv

end TauCeti
