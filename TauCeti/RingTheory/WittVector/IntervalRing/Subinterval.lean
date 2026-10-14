/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.IntervalRing.Presentation
public import TauCeti.Topology.MetricSpace.Ultra.Completion

/-!
# Interval rings of subintervals

Let `B^{[ρ₁, ρ₂]}` be the interval ring of the Fargues–Fontaine curve
(`TauCeti.WittVector.IntervalRing`): the completion of `𝕎 O[1/(p [ϖ])]` for the norm
`λ_{[ρ₁, ρ₂]} = max(λ_{ρ₁}, λ_{ρ₂})`, in the normalisation `λ_ρ(p) = ρ`, `λ_ρ([x]) = v(x)` of the
Gauss valuations. This file compares interval rings of nested intervals.

On `𝕎 O[1/(p [ϖ])]` every term `v(xₙ) ρ^(n - m)` of `λ_ρ(x / pᵐ)` is monotone in `ρ`, so the Gauss
valuation at a radius inside `[ρ₁, ρ₂]` is at most `λ_{[ρ₁, ρ₂]}` (the Hadamard three circles
inequality, Kedlaya's Lemma 4.4). Hence for `[ρ₁', ρ₂'] ⊆ [ρ₁, ρ₂]` the identity of
`𝕎 O[1/(p [ϖ])]` extends to the restriction map `B^{[ρ₁, ρ₂]} → B^{[ρ₁', ρ₂']}` of Kedlaya's
Corollary 4.6.

The main result presents the interval ring of a smaller left endpoint `ρ₁ ≤ ρ₁' ≤ ρ₂` as a
quotient of a ring of restricted power series over the larger one: the evaluation

```text
B^{[ρ₁, ρ₂]}{T/c, U/ρ₁'⁻¹} → B^{[ρ₁', ρ₂]}{T/c},    T ↦ T,  U ↦ p⁻¹,
```

is surjective. This is the form taken here by the first isomorphism of Kedlaya's Lemma 4.9, which
fixes the left endpoint of the interval. Kedlaya normalises the Gauss norms so that `p` has a
fixed norm and evaluates at a Teichmüller representative `[z]`; here the Teichmüller
representatives have norms independent of the radius, and the variable is sent to `p⁻¹`, of norm
`ρ₁'⁻¹` on `B^{[ρ₁', ρ₂]}`. The evaluation is already surjective on the series with coefficients
in the radius ring `A^{ρ₂}` (`TauCeti.WittVector.RadiusRing.restrictedEvalIntervalRing_surjective`),
since restricting to the subinterval is compatible with the coefficient maps from `A^{ρ₂}`.

## Main definitions

* `TauCeti.WittVector.intervalRingRestrict`: the restriction `B^{[ρ₁, ρ₂]} → B^{[ρ₁', ρ₂']}` to a
  subinterval.
* `TauCeti.WittVector.intervalRingRestrictedEval`: the evaluation
  `B^{[ρ₁, ρ₂]}{T/c, U/ρ₁'⁻¹} → B^{[ρ₁', ρ₂]}{T/c}`, `U ↦ p⁻¹`.

## Main results

* `TauCeti.WittVector.gaussValuationAway_le_max`: the Hadamard three circles inequality on
  `𝕎 O[1/(p [ϖ])]`.
* `TauCeti.WittVector.norm_intervalRingRestrict_le`: restriction to a subinterval does not
  increase the norm.
* `TauCeti.WittVector.intervalRingRestrict_self` and
  `TauCeti.WittVector.intervalRingRestrict_intervalRingRestrict`: restriction is functorial.
* `TauCeti.WittVector.intervalRingRestrict_toIntervalRing`: restriction to a subinterval is
  compatible with the coefficient maps from the radius ring.
* `TauCeti.WittVector.intervalRingRestrictedEval_surjective`: the evaluation at `p⁻¹` is
  surjective.

## References

* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016, no. 8,
  2544–2567; arXiv:1410.5160v3, Lemma 4.4, Corollaries 4.5 and 4.6 and Lemma 4.9.
-/

public section

open scoped NNReal
open UniformSpace

namespace TauCeti.WittVector

open _root_.WittVector

variable (p : ℕ) [Fact p.Prime] {K O : Type*} [Field K] [CommRing O] [Algebra O K]
  {v : Valuation K ℝ≥0} {ϖ : O} [CharP O p] [PerfectRing O p]

local notation "𝕎" => _root_.WittVector p

variable {p}

section Away

variable {B : Type*} [CommRing B] [Algebra (_root_.WittVector p O) B]
  [IsLocalization.Away ((p : _root_.WittVector p O) * teichmuller p ϖ) B]

/-- **The Hadamard three circles inequality on `𝕎 O[1/(p [ϖ])]`.** For radii
`ρ₁ ≤ ρ ≤ ρ₂`, the Gauss valuation `λ_ρ` is bounded by the larger of `λ_{ρ₁}` and `λ_{ρ₂}`, so
the interval norm of an interval dominates every Gauss valuation at a radius inside it. -/
theorem gaussValuationAway_le_max (hv : v.Integers O) (hϖ : ϖ ≠ 0) {ρ ρ₁ ρ₂ : ℝ≥0}
    (hρ : ρ ∈ Set.Ioo 0 1) (hρ₁ : ρ₁ ∈ Set.Ioo 0 1) (hρ₂ : ρ₂ ∈ Set.Ioo 0 1) (h₁ : ρ₁ ≤ ρ)
    (h₂ : ρ ≤ ρ₂) (x : B) :
    gaussValuationAway p hv hϖ ρ hρ B x ≤
      max (gaussValuationAway p hv hϖ ρ₁ hρ₁ B x) (gaussValuationAway p hv hϖ ρ₂ hρ₂ B x) := by
  obtain ⟨⟨y, s⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Submonoid.powers ((p : 𝕎 O) * teichmuller p ϖ)) x
  obtain ⟨m, hm⟩ := s.2
  simp only [gaussValuationAway_mk', ← hm, map_pow, map_mul, gaussValuation_p,
    gaussValuation_teichmuller, mul_pow, mul_inv, ← mul_assoc]
  rw [← max_mul_of_nonneg _ _ zero_le]
  exact mul_le_mul_left (gaussValuation_mul_inv_pow_le_max hv hρ.2 hρ₁.2 hρ₂.2 hρ₁.1 h₁ h₂ y m) _

end Away

section Restrict

variable (hv : v.Integers O) (hϖ : ϖ ≠ 0) (hϖ' : v (algebraMap O K ϖ) < 1) {ρ₁ ρ₂ ρ₁' ρ₂' : ℝ≥0}
  (hρ₁ : ρ₁ ∈ Set.Ioo 0 1) (hρ₂ : ρ₂ ∈ Set.Ioo 0 1) (hρ₁' : ρ₁' ∈ Set.Ioo 0 1)
  (hρ₂' : ρ₂' ∈ Set.Ioo 0 1)

variable (p) in
/-- The canonical isomorphism between `𝕎 O[1/(p [ϖ])]` normed by two interval norms. -/
private noncomputable def intervalLocalizationEquiv :
    IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂ ≃ₐ[𝕎 O] IntervalLocalization p hv hϖ hϖ' hρ₁' hρ₂' :=
  IsLocalization.algEquiv (Submonoid.powers ((p : 𝕎 O) * teichmuller p ϖ)) _ _

variable {hρ₁ hρ₂ hρ₁' hρ₂'} in
/-- For a subinterval `[ρ₁', ρ₂'] ⊆ [ρ₁, ρ₂]`, the interval norm of the subinterval is at most
that of the interval. -/
private theorem norm_intervalLocalizationEquiv_le (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂')
    (h₂ : ρ₂' ≤ ρ₂) (x : IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) :
    ‖intervalLocalizationEquiv p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' hρ₂' x‖ ≤ ‖x‖ := by
  rw [IntervalLocalization.norm_def, IntervalLocalization.norm_def, intervalLocalizationEquiv,
    ← AlgEquiv.coe_toAlgHom, gaussValuationAway_algHom, gaussValuationAway_algHom, ← NNReal.coe_max,
    ← NNReal.coe_max, NNReal.coe_le_coe]
  exact max_le (gaussValuationAway_le_max hv hϖ _ hρ₁ hρ₂ h₁ (h₁₂.trans h₂) x)
    (gaussValuationAway_le_max hv hϖ _ hρ₁ hρ₂ (h₁.trans h₁₂) h₂ x)

variable {hρ₁ hρ₂ hρ₁' hρ₂'} in
private theorem continuous_intervalLocalizationEquiv (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂')
    (h₂ : ρ₂' ≤ ρ₂) :
    Continuous (intervalLocalizationEquiv p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' hρ₂').toRingHom :=
  AddMonoidHomClass.continuous_of_bound
    (intervalLocalizationEquiv p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' hρ₂').toRingHom 1
    fun x ↦ by simpa using norm_intervalLocalizationEquiv_le hv hϖ hϖ' h₁ h₁₂ h₂ x

variable (p) in
/-- **Restriction to a subinterval** (Kedlaya, Corollary 4.6). For a subinterval
`[ρ₁', ρ₂'] ⊆ [ρ₁, ρ₂]`, the identity of `𝕎 O[1/(p [ϖ])]` does not increase the interval norm,
by the Hadamard three circles inequality, so it extends to a `𝕎 O`-algebra homomorphism
`B^{[ρ₁, ρ₂]} → B^{[ρ₁', ρ₂']}` of the completions. -/
noncomputable def intervalRingRestrict (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂') (h₂ : ρ₂' ≤ ρ₂) :
    IntervalRing p hv hϖ hϖ' hρ₁ hρ₂ →ₐ[𝕎 O] IntervalRing p hv hϖ hϖ' hρ₁' hρ₂' where
  toRingHom := Completion.mapRingHom _ (continuous_intervalLocalizationEquiv hv hϖ hϖ' h₁ h₁₂ h₂)
  commutes' x := by
    rw [Completion.algebraMap_def, Completion.algebraMap_def, RingHom.toFun_eq_coe,
      Completion.mapRingHom_coe]
    simp

variable {hv hϖ hϖ' hρ₁ hρ₂ hρ₁' hρ₂'}

/-- Restriction to a subinterval is the extension of the identity of `𝕎 O[1/(p [ϖ])]` to the
completions. -/
private theorem coe_intervalRingRestrict (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂') (h₂ : ρ₂' ≤ ρ₂) :
    ⇑(intervalRingRestrict p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' hρ₂' h₁ h₁₂ h₂) =
      Completion.mapRingHom (intervalLocalizationEquiv p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' hρ₂').toRingHom
        (continuous_intervalLocalizationEquiv hv hϖ hϖ' h₁ h₁₂ h₂) :=
  rfl

/-- Restriction to a subinterval is the identity on fractions `x / s` with `x ∈ 𝕎 O` and `s` a
power of `p [ϖ]`. -/
@[simp]
theorem intervalRingRestrict_coe_mk' (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂') (h₂ : ρ₂' ≤ ρ₂)
    (x : 𝕎 O) (s : Submonoid.powers ((p : 𝕎 O) * teichmuller p ϖ)) :
    intervalRingRestrict p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' hρ₂' h₁ h₁₂ h₂
        (IsLocalization.mk' (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) x s) =
      (IsLocalization.mk' (IntervalLocalization p hv hϖ hϖ' hρ₁' hρ₂') x s :
        IntervalRing p hv hϖ hϖ' hρ₁' hρ₂') := by
  rw [coe_intervalRingRestrict, Completion.mapRingHom_coe]
  simp [intervalLocalizationEquiv]

/-- Restriction to a subinterval on `𝕎 O[1/(p [ϖ])]`. -/
private theorem intervalRingRestrict_coe (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂') (h₂ : ρ₂' ≤ ρ₂)
    (x : IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) :
    intervalRingRestrict p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' hρ₂' h₁ h₁₂ h₂ x =
      (intervalLocalizationEquiv p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' hρ₂' x :
        IntervalRing p hv hϖ hϖ' hρ₁' hρ₂') :=
  Completion.mapRingHom_coe (continuous_intervalLocalizationEquiv hv hϖ hϖ' h₁ h₁₂ h₂) x

/-- Restriction to a subinterval is continuous. -/
theorem continuous_intervalRingRestrict (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂') (h₂ : ρ₂' ≤ ρ₂) :
    Continuous (intervalRingRestrict p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' hρ₂' h₁ h₁₂ h₂) := by
  rw [coe_intervalRingRestrict, Completion.coe_mapRingHom]
  exact Completion.continuous_map

/-- **Restriction to a subinterval does not increase the interval norm.** -/
theorem norm_intervalRingRestrict_le (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂') (h₂ : ρ₂' ≤ ρ₂)
    (x : IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) :
    ‖intervalRingRestrict p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' hρ₂' h₁ h₁₂ h₂ x‖ ≤ ‖x‖ := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_le (continuous_intervalRingRestrict (hv := hv) (hϖ := hϖ) (hϖ' := hϖ')
      (hρ₁ := hρ₁) (hρ₂ := hρ₂) (hρ₁' := hρ₁') (hρ₂' := hρ₂') h₁ h₁₂ h₂).norm continuous_norm
  | ih a =>
    rw [coe_intervalRingRestrict, Completion.mapRingHom_coe, Completion.norm_coe,
      Completion.norm_coe]
    exact norm_intervalLocalizationEquiv_le hv hϖ hϖ' h₁ h₁₂ h₂ a

/-- Restriction of an interval to itself is the identity. -/
@[simp]
theorem intervalRingRestrict_self (h₁₂ : ρ₁ ≤ ρ₂) (x : IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) :
    intervalRingRestrict p hv hϖ hϖ' hρ₁ hρ₂ hρ₁ hρ₂ le_rfl h₁₂ le_rfl x = x := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (continuous_intervalRingRestrict le_rfl h₁₂ le_rfl) continuous_id
  | ih a =>
    obtain ⟨⟨y, s⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (Submonoid.powers ((p : 𝕎 O) * teichmuller p ϖ)) a
    exact intervalRingRestrict_coe_mk' le_rfl h₁₂ le_rfl y s

/-- Restricting to a subinterval and then to a smaller one is restricting to the smaller one. -/
@[simp]
theorem intervalRingRestrict_intervalRingRestrict {ρ₁'' ρ₂'' : ℝ≥0} {hρ₁'' : ρ₁'' ∈ Set.Ioo 0 1}
    {hρ₂'' : ρ₂'' ∈ Set.Ioo 0 1} (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂') (h₂ : ρ₂' ≤ ρ₂)
    (h₁' : ρ₁' ≤ ρ₁'') (h₁₂' : ρ₁'' ≤ ρ₂'') (h₂' : ρ₂'' ≤ ρ₂')
    (x : IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) :
    intervalRingRestrict p hv hϖ hϖ' hρ₁' hρ₂' hρ₁'' hρ₂'' h₁' h₁₂' h₂'
        (intervalRingRestrict p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' hρ₂' h₁ h₁₂ h₂ x) =
      intervalRingRestrict p hv hϖ hϖ' hρ₁ hρ₂ hρ₁'' hρ₂'' (h₁.trans h₁') h₁₂' (h₂'.trans h₂)
        x := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq ((continuous_intervalRingRestrict h₁' h₁₂' h₂').comp
      (continuous_intervalRingRestrict h₁ h₁₂ h₂))
      (continuous_intervalRingRestrict (h₁.trans h₁') h₁₂' (h₂'.trans h₂))
  | ih a =>
    obtain ⟨⟨y, s⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (Submonoid.powers ((p : 𝕎 O) * teichmuller p ϖ)) a
    simp only [intervalRingRestrict_coe_mk']

/-- Restriction to subintervals is compatible with composition. -/
@[simp]
theorem intervalRingRestrict_comp {ρ₁'' ρ₂'' : ℝ≥0} {hρ₁'' : ρ₁'' ∈ Set.Ioo 0 1}
    {hρ₂'' : ρ₂'' ∈ Set.Ioo 0 1} (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂') (h₂ : ρ₂' ≤ ρ₂)
    (h₁' : ρ₁' ≤ ρ₁'') (h₁₂' : ρ₁'' ≤ ρ₂'') (h₂' : ρ₂'' ≤ ρ₂') :
    (intervalRingRestrict p hv hϖ hϖ' hρ₁' hρ₂' hρ₁'' hρ₂'' h₁' h₁₂' h₂').comp
        (intervalRingRestrict p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' hρ₂' h₁ h₁₂ h₂) =
      intervalRingRestrict p hv hϖ hϖ' hρ₁ hρ₂ hρ₁'' hρ₂'' (h₁.trans h₁') h₁₂' (h₂'.trans h₂) :=
  AlgHom.ext fun x ↦ by
    rw [AlgHom.comp_apply, intervalRingRestrict_intervalRingRestrict h₁ h₁₂ h₂ h₁' h₁₂' h₂']

/-- Restricting to a subinterval with the same right endpoint is compatible with the coefficient
maps from the radius ring. -/
@[simp]
theorem intervalRingRestrict_toIntervalRing (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂)
    (x : RadiusRing p hv hϖ hϖ' hρ₂) :
    intervalRingRestrict p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' hρ₂ h₁ h₁₂ le_rfl
        (RadiusRing.toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ (h₁.trans h₁₂) x) =
      RadiusRing.toIntervalRing p hv hϖ hϖ' hρ₁' hρ₂ h₁₂ x := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq ((continuous_intervalRingRestrict h₁ h₁₂ le_rfl).comp
      (RadiusRing.isometry_toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ _).continuous)
      (RadiusRing.isometry_toIntervalRing p hv hϖ hϖ' hρ₁' hρ₂ h₁₂).continuous
  | ih a =>
    rw [RadiusRing.toIntervalRing_coe, RadiusRing.toIntervalRing_coe, intervalRingRestrict_coe]
    -- `𝕎 O`-algebra homomorphisms out of the localisation `𝕎 O[1/[ϖ]]` are unique
    have h : ((intervalLocalizationEquiv p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' hρ₂).toAlgHom.comp
        (RadiusLocalization.toIntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂)) =
          RadiusLocalization.toIntervalLocalization p hv hϖ hϖ' hρ₁' hρ₂ :=
      IsLocalization.algHom_subsingleton (Submonoid.powers (teichmuller p ϖ)) |>.elim _ _
    rw [← h]
    simp

end Restrict

section Presentation

open MvPowerSeries

variable (hv : v.Integers O) (hϖ : ϖ ≠ 0) (hϖ' : v (algebraMap O K ϖ) < 1) {ρ₁ ρ₂ ρ₁' : ℝ≥0}
  (hρ₁ : ρ₁ ∈ Set.Ioo 0 1) (hρ₂ : ρ₂ ∈ Set.Ioo 0 1) (hρ₁' : ρ₁' ∈ Set.Ioo 0 1)

variable {k : ℕ} (c : Fin k → ℝ) [∀ i, Fact (0 < c i)]

variable (p) in
/-- **Evaluation at `p⁻¹` onto a smaller left endpoint.** For `ρ₁ ≤ ρ₁' ≤ ρ₂`, the ring
homomorphism

```text
B^{[ρ₁, ρ₂]}{T/c, U/ρ₁'⁻¹} → B^{[ρ₁', ρ₂]}{T/c},    T ↦ T,  U ↦ p⁻¹,
```

restricting the coefficients to the subinterval. Here `U = X 0` and `T i = X i.succ`, and `U` has
radius `ρ₁'⁻¹`, the norm of `p⁻¹` in `B^{[ρ₁', ρ₂]}`. It is surjective
(`TauCeti.WittVector.intervalRingRestrictedEval_surjective`): this is the form of Kedlaya's
Lemma 4.9 that moves the left endpoint of an interval in the normalisation `λ_ρ(p) = ρ`. -/
noncomputable def intervalRingRestrictedEval (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂) :
    IsRestricted.subring (R := IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)
        (Fin.cons (ρ₁' : ℝ)⁻¹ c : Fin (k + 1) → ℝ) →+*
      IsRestricted.subring (R := IntervalRing p hv hϖ hϖ' hρ₁' hρ₂) c :=
  MvPowerSeries.restrictedEval₂
    ((algebraMap _ _).comp
      (intervalRingRestrict p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' hρ₂ h₁ h₁₂ le_rfl).toRingHom)
    (Fin.cons (algebraMap _ _ (Ring.inverse (p : IntervalRing p hv hϖ hϖ' hρ₁' hρ₂)))
      fun i ↦ ⟨X i, isRestricted_monomial c (Finsupp.single i 1) 1⟩)
    (fun b ↦ by
      simpa using norm_intervalRingRestrict_le h₁ h₁₂ le_rfl b)
    (Fin.cases (by
      have h : ((ρ₂ : ℝ))⁻¹ ≤ (ρ₁' : ℝ)⁻¹ :=
        inv_anti₀ (by exact_mod_cast hρ₁'.1) (by exact_mod_cast h₁₂)
      simpa using h) fun i ↦ by simp)

variable {c}

/-- The presentation restricts constants to the subinterval. -/
@[simp]
theorem intervalRingRestrictedEval_algebraMap (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂)
    (b : IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) :
    intervalRingRestrictedEval p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' c h₁ h₁₂ (algebraMap _ _ b) =
      algebraMap _ _ (intervalRingRestrict p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' hρ₂ h₁ h₁₂ le_rfl b) :=
  restrictedEval₂_algebraMap _ _ _ _ b

/-- The presentation sends the variable `U = X 0` to `p⁻¹`. -/
@[simp]
theorem intervalRingRestrictedEval_X_zero (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂) :
    intervalRingRestrictedEval p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' c h₁ h₁₂
        ⟨X 0, isRestricted_monomial _ (Finsupp.single 0 1) 1⟩ =
      algebraMap _ _ (Ring.inverse (p : IntervalRing p hv hϖ hϖ' hρ₁' hρ₂)) :=
  restrictedEval₂_X _ _ _ _ 0

/-- The presentation sends each variable `T i = X i.succ` to `X i`. -/
@[simp]
theorem intervalRingRestrictedEval_X_succ (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂) (i : Fin k) :
    intervalRingRestrictedEval p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' c h₁ h₁₂
        ⟨X i.succ, isRestricted_monomial _ (Finsupp.single i.succ 1) 1⟩ =
      ⟨X i, isRestricted_monomial c (Finsupp.single i 1) 1⟩ :=
  restrictedEval₂_X _ _ _ _ i.succ

/-- The presentation does not increase the Gauss norm. -/
theorem norm_intervalRingRestrictedEval_le (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂)
    [∀ j, Fact (0 < (Fin.cons (ρ₁' : ℝ)⁻¹ c : Fin (k + 1) → ℝ) j)]
    (g : IsRestricted.subring (R := IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)
      (Fin.cons (ρ₁' : ℝ)⁻¹ c : Fin (k + 1) → ℝ)) :
    ‖intervalRingRestrictedEval p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' c h₁ h₁₂ g‖ ≤ ‖g‖ :=
  norm_restrictedEval₂_le _ _ _ _ g

/-- The presentation is continuous for the Gauss norms. -/
theorem continuous_intervalRingRestrictedEval (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂)
    [∀ j, Fact (0 < (Fin.cons (ρ₁' : ℝ)⁻¹ c : Fin (k + 1) → ℝ) j)] :
    Continuous (intervalRingRestrictedEval p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' c h₁ h₁₂) :=
  continuous_restrictedEval₂ _ _ _ _

/-- **Kedlaya's Lemma 4.9, moving the left endpoint.** For `ρ₁ ≤ ρ₁' ≤ ρ₂`, the evaluation

```text
B^{[ρ₁, ρ₂]}{T/c, U/ρ₁'⁻¹} → B^{[ρ₁', ρ₂]}{T/c},    T ↦ T,  U ↦ p⁻¹,
```

is surjective, so `B^{[ρ₁', ρ₂]}{T/c}` is a quotient of a ring of restricted power series over
`B^{[ρ₁, ρ₂]}` with one more variable. It is already surjective on the series with coefficients in
the radius ring `A^{ρ₂}` (`TauCeti.WittVector.RadiusRing.restrictedEvalIntervalRing_surjective`). -/
theorem intervalRingRestrictedEval_surjective (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂) :
    Function.Surjective (intervalRingRestrictedEval p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' c h₁ h₁₂) := by
  have : ∀ j, Fact (0 < (Fin.cons (ρ₁' : ℝ)⁻¹ c : Fin (k + 1) → ℝ) j) :=
    Fin.cases ⟨inv_pos.mpr (by exact_mod_cast hρ₁'.1)⟩ fun i ↦ ⟨(Fact.out : 0 < c i)⟩
  -- the coefficient map `A^{ρ₂}{T/c, U/ρ₁'⁻¹} → B^{[ρ₁, ρ₂]}{T/c, U/ρ₁'⁻¹}`
  let ι := restrictedEval₂ (c := (Fin.cons (ρ₁' : ℝ)⁻¹ c : Fin (k + 1) → ℝ))
    ((algebraMap _ (IsRestricted.subring
      (R := IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) (Fin.cons (ρ₁' : ℝ)⁻¹ c : Fin (k + 1) → ℝ))).comp
        (RadiusRing.toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ (h₁.trans h₁₂)))
    (fun j ↦ ⟨X j, isRestricted_monomial _ (Finsupp.single j 1) 1⟩) (fun a ↦ by simp)
    fun j ↦ by simp
  have hι : Continuous ι := continuous_restrictedEval₂ _ _ _ _
  have h : (intervalRingRestrictedEval p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' c h₁ h₁₂).comp ι =
      RadiusRing.restrictedEvalIntervalRing p hv hϖ hϖ' hρ₁' hρ₂ c h₁₂ := by
    refine RadiusRing.eq_restrictedEvalIntervalRing p hv hϖ hϖ' hρ₁' hρ₂ h₁₂ _ ?_
      (fun a ↦ by simp [ι]) (by simp [ι]) fun i ↦ by simp [ι]
    rw [RingHom.coe_comp]
    exact (continuous_intervalRingRestrictedEval hv hϖ hϖ' hρ₁ hρ₂ hρ₁' h₁ h₁₂).comp hι
  intro g
  obtain ⟨f, rfl⟩ :=
    RadiusRing.restrictedEvalIntervalRing_surjective p hv hϖ hϖ' hρ₁' hρ₂ h₁₂ g
  exact ⟨ι f, by rw [← h, RingHom.comp_apply]⟩

end Presentation

end TauCeti.WittVector
