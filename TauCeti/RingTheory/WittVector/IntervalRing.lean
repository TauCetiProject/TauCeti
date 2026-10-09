/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import TauCeti.Analysis.Normed.Ring.Completion
public import TauCeti.RingTheory.Huber.Completion
public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Valuation.ExtendToLocalization
public import TauCeti.RingTheory.WittVector.GaussValuation

/-!
# The interval rings `B^I` of the Fargues–Fontaine curve

Let `O` be the ring of integers of a valuation `v : Valuation K ℝ≥0` on a field `K`, perfect of
characteristic `p`, and let `ϖ ∈ O` be a pseudouniformiser, `0 < v(ϖ) < 1`; for instance
`O = 𝒪_F` for a perfect nonarchimedean field `F` of characteristic `p` with pseudouniformiser
`ϖ`, so that `𝕎 O = A_inf`. For `0 < ρ < 1` the Gauss valuation

```text
λ_ρ(∑ₙ [xₙ] pⁿ) = supₙ v(xₙ) ρⁿ
```

(`TauCeti.WittVector.gaussValuation`) does not vanish at `p [ϖ]`, so it extends to the
localisation `𝕎 O[1/(p [ϖ])]` (`TauCeti.WittVector.gaussValuationAway`, an instance of Mathlib's
`Valuation.extendToLocalization`).

For radii `ρ₁, ρ₂ ∈ (0, 1)` the *interval norm* `λ_I = max(λ_{ρ₁}, λ_{ρ₂})` is an ultrametric
ring norm on `𝕎 O[1/(p [ϖ])]`, and the *interval ring* `B^I` is the completion of
`𝕎 O[1/(p [ϖ])]` for `λ_I`. Kedlaya normalises the Gauss norms by an exponent `t > 0` instead,
as `λ(α^t)(x) = supₙ v(xₙ)^t p^(-n)`, which is `λ_ρ(x)^t` for `ρ = p^(-1/t)`, and builds `B^I`
for a closed interval `I ⊂ (0, ∞)` of exponents from the norms `λ(α^t)`, `t ∈ I`. Since
`t ↦ log λ(α^t)(x)` is convex, these are bounded by the norms at the two endpoints, and a positive
power of a norm defines the same uniform structure; so the interval `I = [s, r]` of exponents
corresponds to the radii `ρ₁ = p^(-1/s)` and `ρ₂ = p^(-1/r)` here.

The ring `B^I` is a complete Hausdorff Tate ring: `p` becomes a unit of norm `max(ρ₁, ρ₂) < 1`,
hence a pseudouniformiser (`TauCeti.WittVector.isPseudoUniformizer_natCast_intervalRing`), and the
Tate structure of `𝕎 O[1/(p [ϖ])]` comes from `TauCeti.Huber.IsTateRing.of_isUnit_norm_lt_one`.

The norm `λ_I` is power-multiplicative, though in general not multiplicative, and so is its
extension to `B^I`. Hence the power-bounded elements of `B^I` are exactly its unit ball
`B^{I,+} = {x : λ_I(x) ≤ 1}`, which is therefore a ring of integral elements, and `B^I` is uniform.

## Main definitions

* `TauCeti.WittVector.gaussValuationAway` : the extension of `λ_ρ` to `𝕎 O[1/(p [ϖ])]`.
* `TauCeti.WittVector.IntervalLocalization` : `𝕎 O[1/(p [ϖ])]` normed by `λ_I`.
* `TauCeti.WittVector.intervalNorm` : the ring norm `λ_I = max(λ_{ρ₁}, λ_{ρ₂})`.
* `TauCeti.WittVector.IntervalRing` : the interval ring `B^I`, the completion of
  `IntervalLocalization`.

## Main results

* `TauCeti.WittVector.norm_algebraMap_intervalRing` : `‖x‖ = max(λ_{ρ₁}(x), λ_{ρ₂}(x))` for
  `x ∈ 𝕎 O`.
* `TauCeti.WittVector.isPseudoUniformizer_natCast_intervalRing` : `p` is a pseudouniformiser of
  `B^I`.
* `TauCeti.WittVector.isPseudoUniformizer_teichmuller_intervalRing` : `[ϖ]` is a pseudouniformiser
  of `B^I`.
* `TauCeti.WittVector.coe_powerBoundedSubring_intervalRing` : the power-bounded subring of `B^I`
  is its unit ball `B^{I,+}`.
* `TauCeti.WittVector.isUniform_intervalRing` : `B^I` is uniform.
* `TauCeti.WittVector.continuous_algebraMap_intervalRing` : `𝕎 O → B^I` is continuous for the
  `(p, [ϖ])`-adic topology on `𝕎 O`.
* `TauCeti.WittVector.exists_norm_le_one_algebraMap_eq_mul_intervalRing` : if `λ_ρ(x) ≤ λ_ρ(y)` at
  both radii and `y` is a unit of `𝕎 O[1/(p [ϖ])]`, then `x / y` lies in the unit ball of `B^I`.
* `TauCeti.WittVector.IntervalLocalization.instIsTateRing` : `𝕎 O[1/(p [ϖ])]` with the interval
  norm is a Tate ring, so its completion `B^I` is a complete Hausdorff Tate ring by
  `TauCeti.Huber.IsTateRing.completion`.

## References

* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016, no. 8,
  2544–2567, for the rings `B^I`.
* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, lecture notes, Arizona Winter School 2017,
  §3.1.
* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), Chapter 1.
-/

public section

open scoped NNReal

namespace TauCeti.WittVector

open _root_.WittVector UniformSpace TauCeti.Huber

variable (p : ℕ) [Fact p.Prime] {K O : Type*} [Field K] [CommRing O] [Algebra O K]
  {v : Valuation K ℝ≥0} {ϖ : O}

local notation "𝕎" => _root_.WittVector p

section Away

variable {p} [CharP O p] [PerfectRing O p]

/-- For `0 < ρ < 1` and `ϖ ≠ 0`, the Gauss valuation `λ_ρ` does not vanish at `p [ϖ]`. -/
theorem gaussValuation_natCast_mul_teichmuller_ne_zero (hv : v.Integers O) (hϖ : ϖ ≠ 0)
    {ρ : ℝ≥0} (hρ : ρ ∈ Set.Ioo 0 1) :
    gaussValuation p hv ρ hρ.2 ((p : 𝕎 O) * teichmuller p ϖ) ≠ 0 := by
  simp [hρ.1.ne', map_eq_zero_iff _ hv.hom_inj, hϖ]

variable {B : Type*} [CommRing B] [Algebra (_root_.WittVector p O) B]
  [IsLocalization.Away ((p : _root_.WittVector p O) * teichmuller p ϖ) B]

variable (p) in
/-- **The Gauss valuation on `𝕎 O[1/(p [ϖ])]`**: the extension of `λ_ρ` to a localisation `B` of
`𝕎 O` away from `p [ϖ]`, for `0 < ρ < 1` and `ϖ ≠ 0`. -/
noncomputable def gaussValuationAway (hv : v.Integers O) (hϖ : ϖ ≠ 0) (ρ : ℝ≥0)
    (hρ : ρ ∈ Set.Ioo 0 1) (B : Type*) [CommRing B] [Algebra (𝕎 O) B]
    [IsLocalization.Away ((p : 𝕎 O) * teichmuller p ϖ) B] : Valuation B ℝ≥0 :=
  (gaussValuation p hv ρ hρ.2).extendToLocalization
    (Valuation.powers_le_supp_primeCompl
      (gaussValuation_natCast_mul_teichmuller_ne_zero hv hϖ hρ)) B

/-- The extended Gauss valuation agrees with `λ_ρ` on `𝕎 O`. -/
@[simp]
theorem gaussValuationAway_algebraMap (hv : v.Integers O) (hϖ : ϖ ≠ 0) {ρ : ℝ≥0}
    (hρ : ρ ∈ Set.Ioo 0 1) (x : 𝕎 O) :
    gaussValuationAway p hv hϖ ρ hρ B (algebraMap (𝕎 O) B x) = gaussValuation p hv ρ hρ.2 x :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ x

/-- The extended Gauss valuation of a fraction `x / s` is `λ_ρ(x) / λ_ρ(s)`. -/
@[simp]
theorem gaussValuationAway_mk' (hv : v.Integers O) (hϖ : ϖ ≠ 0) {ρ : ℝ≥0}
    (hρ : ρ ∈ Set.Ioo 0 1) (x : 𝕎 O) (s : Submonoid.powers ((p : 𝕎 O) * teichmuller p ϖ)) :
    gaussValuationAway p hv hϖ ρ hρ B (IsLocalization.mk' B x s) =
      gaussValuation p hv ρ hρ.2 x * (gaussValuation p hv ρ hρ.2 s)⁻¹ :=
  Valuation.extendToLocalization_mk' _ _ _ x s

/-- The extended Gauss valuation vanishes only at zero. -/
@[simp]
theorem gaussValuationAway_eq_zero_iff (hv : v.Integers O) (hϖ : ϖ ≠ 0) {ρ : ℝ≥0}
    (hρ : ρ ∈ Set.Ioo 0 1) {x : B} : gaussValuationAway p hv hϖ ρ hρ B x = 0 ↔ x = 0 := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ hx ▸ map_zero _⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Submonoid.powers ((p : 𝕎 O) * teichmuller p ϖ)) x
  dsimp only at hx ⊢
  have hs : gaussValuation p hv ρ hρ.2 s ≠ 0 :=
    Valuation.powers_le_supp_primeCompl
      (gaussValuation_natCast_mul_teichmuller_ne_zero hv hϖ hρ) s.2
  rw [gaussValuationAway_mk', mul_eq_zero, inv_eq_zero, gaussValuation_eq_zero_iff hv hρ.1,
    or_iff_left hs] at hx
  rw [hx, IsLocalization.mk'_zero]

end Away

section Interval

variable (hv : v.Integers O) (hϖ : ϖ ≠ 0) (hϖ' : v (algebraMap O K ϖ) < 1) {ρ₁ ρ₂ : ℝ≥0}
  (hρ₁ : ρ₁ ∈ Set.Ioo 0 1) (hρ₂ : ρ₂ ∈ Set.Ioo 0 1)

/-- **`𝕎 O[1/(p [ϖ])]` with the interval norm.** This is the localisation of `𝕎 O` away from
`p [ϖ]`, for a pseudouniformiser `ϖ` (`0 < v(ϖ) < 1`), normed by `λ_I = max(λ_{ρ₁}, λ_{ρ₂})`
(`TauCeti.WittVector.intervalNorm`); its completion is the interval ring `B^I`. -/
-- The body is exposed because the ring structures below are transferred from
-- `Localization.Away` along it.
@[expose]
def IntervalLocalization (_hv : v.Integers O) (_hϖ : ϖ ≠ 0) (_hϖ' : v (algebraMap O K ϖ) < 1)
    (_hρ₁ : ρ₁ ∈ Set.Ioo 0 1) (_hρ₂ : ρ₂ ∈ Set.Ioo 0 1) : Type _ :=
  Localization.Away ((p : 𝕎 O) * teichmuller p ϖ)

namespace IntervalLocalization

noncomputable instance : CommRing (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) :=
  inferInstanceAs (CommRing (Localization.Away _))

noncomputable instance : Algebra (𝕎 O) (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) :=
  inferInstanceAs (Algebra (𝕎 O) (Localization.Away _))

instance : IsLocalization.Away ((p : 𝕎 O) * teichmuller p ϖ)
    (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) :=
  inferInstanceAs (IsLocalization.Away ((p : 𝕎 O) * teichmuller p ϖ)
    (Localization.Away ((p : 𝕎 O) * teichmuller p ϖ)))

/-- `p` is a unit of `𝕎 O[1/(p [ϖ])]`. -/
theorem isUnit_natCast : IsUnit (p : IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) := by
  simpa using IsLocalization.Away.isUnit_of_dvd (S := IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂)
    ((p : 𝕎 O) * teichmuller p ϖ) (dvd_mul_right _ _)

/-- `[ϖ]` is a unit of `𝕎 O[1/(p [ϖ])]`. -/
theorem isUnit_algebraMap_teichmuller :
    IsUnit (algebraMap (𝕎 O) (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) (teichmuller p ϖ)) :=
  IsLocalization.Away.isUnit_of_dvd ((p : 𝕎 O) * teichmuller p ϖ) (dvd_mul_left _ _)

end IntervalLocalization

variable [CharP O p] [PerfectRing O p]

local notation "λ₁" =>
  gaussValuationAway p hv hϖ ρ₁ hρ₁ (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂)
local notation "λ₂" =>
  gaussValuationAway p hv hϖ ρ₂ hρ₂ (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂)

/-- `λ_I = max(λ_{ρ₁}, λ_{ρ₂})` is ultrametric. -/
private theorem max_gaussValuationAway_add_le (x y : IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) :
    max (λ₁ (x + y)) (λ₂ (x + y)) ≤ max (max (λ₁ x) (λ₂ x)) (max (λ₁ y) (λ₂ y)) :=
  max_le ((Valuation.map_add _ x y).trans (max_le_max (le_max_left _ _) (le_max_left _ _)))
    ((Valuation.map_add _ x y).trans (max_le_max (le_max_right _ _) (le_max_right _ _)))

/-- **The interval norm** `λ_I = max(λ_{ρ₁}, λ_{ρ₂})` on `𝕎 O[1/(p [ϖ])]`: a ring norm, which is
ultrametric and submultiplicative because each `λ_ρ` is a valuation, and vanishes only at zero
because `λ_{ρ₁}` does. -/
noncomputable def intervalNorm : RingNorm (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) where
  toFun x := max (λ₁ x) (λ₂ x)
  map_zero' := by simp
  add_le' x y := by
    have h := max_gaussValuationAway_add_le p hv hϖ hϖ' hρ₁ hρ₂ x y
    exact_mod_cast h.trans (max_le_add_of_nonneg zero_le zero_le)
  neg' x := by simp
  mul_le' x y := by
    have h : max (λ₁ (x * y)) (λ₂ (x * y)) ≤ max (λ₁ x) (λ₂ x) * max (λ₁ y) (λ₂ y) := by
      rw [map_mul, map_mul]
      exact max_le (mul_le_mul' (le_max_left _ _) (le_max_left _ _))
        (mul_le_mul' (le_max_right _ _) (le_max_right _ _))
    exact_mod_cast h
  eq_zero_of_map_eq_zero' x hx := by
    rw [← NNReal.coe_max, NNReal.coe_eq_zero] at hx
    exact (gaussValuationAway_eq_zero_iff hv hϖ hρ₁).mp
      (nonpos_iff_eq_zero.mp ((le_max_left _ _).trans_eq hx))

/-- The interval norm is the larger of the two Gauss valuations. -/
theorem intervalNorm_apply (x : IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) :
    intervalNorm p hv hϖ hϖ' hρ₁ hρ₂ x = max (λ₁ x : ℝ) (λ₂ x) :=
  NNReal.coe_max _ _

namespace IntervalLocalization

noncomputable instance : NormedCommRing (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) where
  __ := (intervalNorm p hv hϖ hϖ' hρ₁ hρ₂).toNormedRing
  mul_comm := mul_comm

/-- The norm of `𝕎 O[1/(p [ϖ])]` is the interval norm `λ_I`. -/
theorem norm_def (x : IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) :
    ‖x‖ = max (λ₁ x : ℝ) (λ₂ x) :=
  intervalNorm_apply p hv hϖ hϖ' hρ₁ hρ₂ x

/-- On `𝕎 O`, the interval norm is `max(λ_{ρ₁}, λ_{ρ₂})`. -/
@[simp]
theorem norm_algebraMap (x : 𝕎 O) :
    ‖algebraMap (𝕎 O) (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) x‖ =
      max (gaussValuation p hv ρ₁ hρ₁.2 x : ℝ) (gaussValuation p hv ρ₂ hρ₂.2 x) := by
  simp [norm_def]

instance : IsUltrametricDist (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ by
    simp only [norm_def, ← NNReal.coe_max, NNReal.coe_le_coe]
    exact max_gaussValuationAway_add_le p hv hϖ hϖ' hρ₁ hρ₂ x y

instance : NormOneClass (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) :=
  ⟨by simp [norm_def]⟩

/-- The interval norm of `p` is `max(ρ₁, ρ₂)`. -/
@[simp]
theorem norm_natCast : ‖(p : IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂)‖ = max (ρ₁ : ℝ) ρ₂ := by
  rw [← map_natCast (algebraMap (𝕎 O) (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂)), norm_algebraMap,
    gaussValuation_p, gaussValuation_p]

/-- The interval norm of `p` is less than one. -/
theorem norm_natCast_lt_one : ‖(p : IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂)‖ < 1 := by
  rw [norm_natCast]
  exact_mod_cast max_lt hρ₁.2 hρ₂.2

/-- **`𝕎 O[1/(p [ϖ])]` with the interval norm is a Tate ring**, with pseudouniformiser `p`. -/
instance instIsTateRing : IsTateRing (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) :=
  IsTateRing.of_isUnit_norm_lt_one (isUnit_natCast p hv hϖ hϖ' hρ₁ hρ₂)
    (norm_natCast_lt_one p hv hϖ hϖ' hρ₁ hρ₂)

/-- **The interval norm is power-multiplicative**: `λ_I(x ^ n) = λ_I(x) ^ n`, because `λ_{ρ₁}` and
`λ_{ρ₂}` are multiplicative. -/
theorem isPowMul_norm : IsPowMul (‖·‖ : IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂ → ℝ) :=
  fun x n _ ↦ by
    simp only [norm_def, map_pow, ← NNReal.coe_pow, ← NNReal.coe_max, (pow_left_mono n).map_max]

/-- Scalar multiplication by `𝕎 O` is uniformly continuous, so that the `𝕎 O`-algebra structure
extends to the completion `B^I`. -/
instance : UniformContinuousConstSMul (𝕎 O) (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) :=
  ⟨fun c ↦ by
    simp_rw [Algebra.smul_def]
    exact (Ring.uniformContinuousConstSMul _).uniformContinuous_const_smul _⟩

end IntervalLocalization

/-- **The interval ring `B^I`**: the completion of `𝕎 O[1/(p [ϖ])]` for the interval norm
`λ_I = max(λ_{ρ₁}, λ_{ρ₂})`, for radii `ρ₁, ρ₂ ∈ (0, 1)` and a pseudouniformiser `ϖ`
(`0 < v(ϖ) < 1`). It is a complete Hausdorff normed commutative ring and a Tate ring. -/
abbrev IntervalRing : Type _ :=
  Completion (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂)

/-- On `𝕎 O`, the norm of `B^I` is `max(λ_{ρ₁}, λ_{ρ₂})`. -/
@[simp]
theorem norm_algebraMap_intervalRing (x : 𝕎 O) :
    ‖algebraMap (𝕎 O) (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) x‖ =
      max (gaussValuation p hv ρ₁ hρ₁.2 x : ℝ) (gaussValuation p hv ρ₂ hρ₂.2 x) := by
  rw [Completion.algebraMap_def, Completion.norm_coe, IntervalLocalization.norm_algebraMap]

/-- The map `𝕎 O → B^I` is injective. -/
theorem algebraMap_intervalRing_injective :
    Function.Injective (algebraMap (𝕎 O) (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
  rw [Completion.algebraMap_def, Completion.coe_eq_zero_iff] at hx
  rw [← gaussValuation_eq_zero_iff hv hρ₁.1 hρ₁.2, ← gaussValuationAway_algebraMap hv hϖ hρ₁ x
    (B := IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂), hx, map_zero]

/-- The norm of `p` in `B^I` is `max(ρ₁, ρ₂)`. -/
@[simp]
theorem norm_natCast_intervalRing :
    ‖(p : IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)‖ = max (ρ₁ : ℝ) ρ₂ := by
  rw [← map_natCast (Completion.coeRingHom :
    IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂ →+* IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)]
  exact (Completion.norm_coe _).trans (IntervalLocalization.norm_natCast p hv hϖ hϖ' hρ₁ hρ₂)

/-- **`p` is a pseudouniformiser of `B^I`**: it is a unit of norm `max(ρ₁, ρ₂) < 1`. -/
theorem isPseudoUniformizer_natCast_intervalRing :
    IsPseudoUniformizer (p : IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) := by
  rw [← map_natCast (Completion.coeRingHom :
    IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂ →+* IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)]
  exact IsPseudoUniformizer.of_norm_lt_one
    ((IntervalLocalization.isUnit_natCast p hv hϖ hϖ' hρ₁ hρ₂).map _)
    ((Completion.norm_coe _).trans_lt
      (IntervalLocalization.norm_natCast_lt_one p hv hϖ hϖ' hρ₁ hρ₂))

/-- **`[ϖ]` is a pseudouniformiser of `B^I`**: the Teichmüller lift of the pseudouniformiser `ϖ`
is a unit of norm `v(ϖ) < 1`. -/
theorem isPseudoUniformizer_teichmuller_intervalRing :
    IsPseudoUniformizer
      (algebraMap (𝕎 O) (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) (teichmuller p ϖ)) := by
  refine IsPseudoUniformizer.of_norm_lt_one ?_ ?_
  · rw [Completion.algebraMap_def]
    exact (IntervalLocalization.isUnit_algebraMap_teichmuller p hv hϖ hϖ' hρ₁ hρ₂).map
      (Completion.coeRingHom : _ →+* IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)
  · rw [norm_algebraMap_intervalRing, gaussValuation_teichmuller, gaussValuation_teichmuller,
      max_self]
    exact_mod_cast hϖ'

/-- **The norm of `B^I` is power-multiplicative**: `‖x ^ n‖ = ‖x‖ ^ n`. -/
theorem isPowMul_norm_intervalRing : IsPowMul (‖·‖ : IntervalRing p hv hϖ hϖ' hρ₁ hρ₂ → ℝ) :=
  (IntervalLocalization.isPowMul_norm p hv hϖ hϖ' hρ₁ hρ₂).completion

/-- **The power-bounded elements of `B^I` are its unit ball**: `x ∈ B^I` is power-bounded exactly
when `λ_I(x) ≤ 1`. -/
@[simp]
theorem isPowerBounded_iff_norm_le_one_intervalRing {x : IntervalRing p hv hϖ hϖ' hρ₁ hρ₂} :
    IsPowerBounded x ↔ ‖x‖ ≤ 1 :=
  (isPseudoUniformizer_natCast_intervalRing p hv hϖ hϖ' hρ₁ hρ₂).isPowerBounded_iff_norm_le_one
    (isPowMul_norm_intervalRing p hv hϖ hϖ' hρ₁ hρ₂)

/-- **The unit ball `B^{I,+}` of `B^I` is its power-bounded subring `(B^I)°`.** In particular it
is a ring of integral elements of `B^I`, the plus ring of the Huber pair
`TauCeti.Huber.Pair.powerBounded (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)`. -/
theorem coe_powerBoundedSubring_intervalRing :
    (powerBoundedSubring (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) :
      Set (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)) = Metric.closedBall 0 1 :=
  IsPseudoUniformizer.coe_powerBoundedSubring_eq_closedBall
    (isPseudoUniformizer_natCast_intervalRing p hv hϖ hϖ' hρ₁ hρ₂)
    (isPowMul_norm_intervalRing p hv hϖ hϖ' hρ₁ hρ₂)

/-- **`B^I` is uniform**: its power-bounded subring, the unit ball, is bounded. -/
instance isUniform_intervalRing : IsUniform (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) :=
  IsUniform.of_isPowMul (isPseudoUniformizer_natCast_intervalRing p hv hϖ hϖ' hρ₁ hρ₂)
    (isPowMul_norm_intervalRing p hv hϖ hϖ' hρ₁ hρ₂)

/-- **The map `𝕎 O → B^I` is continuous** for the `(p, [ϖ])`-adic topology on `𝕎 O`: both Gauss
valuations are continuous (`isContinuous_gaussValuation`), so near `0` each `λ_{ρᵢ}` is below
`λ_{ρᵢ}(p ^ n) = ρᵢ ^ n`, and hence the interval norm is below `max(ρ₁, ρ₂) ^ n`. -/
theorem continuous_algebraMap_intervalRing [TopologicalSpace (𝕎 O)]
    (hI : IsAdic (Ideal.span {(p : 𝕎 O), teichmuller p ϖ})) :
    Continuous (algebraMap (𝕎 O) (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)) := by
  have : IsTopologicalRing (𝕎 O) := hI ▸ (Ideal.span _).nonarchimedean.toIsTopologicalRing
  have hnhds {ρ : ℝ≥0} (hρ : ρ ∈ Set.Ioo 0 1) (n : ℕ) :
      {a : 𝕎 O | gaussValuation p hv ρ hρ.2 a < ρ ^ n} ∈ nhds 0 := by
    have h := Valuation.isContinuous_def.mp (isContinuous_gaussValuation hI hv hρ.2 hϖ')
      ((p : 𝕎 O) ^ n)
    rw [map_pow, gaussValuation_p] at h
    exact h.mem_nhds (by simpa using pow_pos hρ.1 n)
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, Metric.nhds_basis_ball.tendsto_right_iff]
  intro ε hε
  have hc : max (ρ₁ : ℝ) ρ₂ < 1 := max_lt (mod_cast hρ₁.2) (mod_cast hρ₂.2)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hc
  filter_upwards [hnhds hρ₁ n, hnhds hρ₂ n] with a h₁ h₂
  rw [mem_ball_zero_iff, norm_algebraMap_intervalRing]
  have hlt {ρ x : ℝ≥0} (hρ : (ρ : ℝ) ≤ max (ρ₁ : ℝ) ρ₂) (hx : x < ρ ^ n) : (x : ℝ) < ε := by
    have hx' : (x : ℝ) < ρ ^ n := mod_cast hx
    exact hx'.trans_le ((pow_le_pow_left₀ ρ.2 hρ n).trans hn.le)
  exact max_lt (hlt (le_max_left _ _) h₁) (hlt (le_max_right _ _) h₂)

/-- **Division by a unit of `𝕎 O[1/(p [ϖ])]` within the unit ball.** If `y ∈ 𝕎 O` becomes a unit
of `𝕎 O[1/(p [ϖ])]` and `λ_ρ(x) ≤ λ_ρ(y)` at both radii, then `x = z y` in `B^I` for some `z` in
the unit ball `B^{I,+} = {z : λ_I(z) ≤ 1}`, namely `z = x / y`. -/
theorem exists_norm_le_one_algebraMap_eq_mul_intervalRing {x y : 𝕎 O}
    (hy : IsUnit (algebraMap (𝕎 O) (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) y))
    (h₁ : gaussValuation p hv ρ₁ hρ₁.2 x ≤ gaussValuation p hv ρ₁ hρ₁.2 y)
    (h₂ : gaussValuation p hv ρ₂ hρ₂.2 x ≤ gaussValuation p hv ρ₂ hρ₂.2 y) :
    ∃ z : IntervalRing p hv hϖ hϖ' hρ₁ hρ₂, ‖z‖ ≤ 1 ∧
      algebraMap (𝕎 O) (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) x =
        z * algebraMap (𝕎 O) (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) y := by
  set L := IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂
  set z : L := algebraMap (𝕎 O) L x * ↑hy.unit⁻¹
  -- at each radius `λ_ρ(z) = λ_ρ(x) / λ_ρ(y) ≤ 1`
  have hz {ρ : ℝ≥0} (hρ : ρ ∈ Set.Ioo 0 1)
      (h : gaussValuation p hv ρ hρ.2 x ≤ gaussValuation p hv ρ hρ.2 y) :
      gaussValuationAway p hv hϖ ρ hρ L z ≤ 1 := by
    have hu : gaussValuation p hv ρ hρ.2 y * gaussValuationAway p hv hϖ ρ hρ L ↑hy.unit⁻¹ = 1 := by
      rw [← gaussValuationAway_algebraMap hv hϖ hρ y (B := L), ← map_mul, hy.mul_val_inv, map_one]
    rw [map_mul, gaussValuationAway_algebraMap]
    exact (mul_le_mul_left h _).trans_eq hu
  refine ⟨(z : Completion L), ?_, ?_⟩
  · rw [Completion.norm_coe, IntervalLocalization.norm_def]
    exact_mod_cast max_le (hz hρ₁ h₁) (hz hρ₂ h₂)
  · rw [Completion.algebraMap_def, Completion.algebraMap_def, ← Completion.coe_mul, mul_assoc,
      hy.val_inv_mul, mul_one]

/-! `B^I` is a complete Hausdorff Tate ring: completeness and separatedness hold for every
completion, and the Tate structure is that of `𝕎 O[1/(p [ϖ])]`, carried to the completion by
`TauCeti.Huber.IsTateRing.completion` (Wedhorn, Remark 6.8). -/

example : CompleteSpace (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) := inferInstance

example : T2Space (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) := inferInstance

example : IsTateRing (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) := inferInstance

end Interval

end TauCeti.WittVector
