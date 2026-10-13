/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.ControlledClosure
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Eval
public import TauCeti.RingTheory.WittVector.IntervalRing.Basic
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
`ρ₁'⁻¹` on `B^{[ρ₁', ρ₂]}`. The proof lifts `d = y / (p [ϖ]) ^ m ∈ 𝕎 O[1/(p [ϖ])]` by splitting the
Teichmüller expansion `y = ∑_{i < m} [yᵢ] pⁱ + pᵐ b`, which gives Kedlaya's estimate (4.9.1) for
the lift, and then lifts all of `B^{[ρ₁', ρ₂]}{T/c}` by the successive approximation of
`controlled_closure_of_complete`, since such polynomials are dense.

Combined with the noetherianity of the restricted power series rings over the radius rings `A^r`
(Kedlaya's Theorem 3.2) and a presentation of `B^{[ρ₁, ρ₂]}` over `A^r` for a suitable `ρ₁`, this
is how Kedlaya proves that the rings `B^I{T/c}` are noetherian (his Theorem 4.10), and hence that
`B^I` is strongly noetherian.

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
* `TauCeti.WittVector.norm_ringInverse_natCast_intervalRing`: `‖p⁻¹‖ = max(ρ₁⁻¹, ρ₂⁻¹)` in
  `B^{[ρ₁, ρ₂]}`.
* `TauCeti.WittVector.intervalRingRestrictedEval_surjective`: the evaluation at `p⁻¹` is
  surjective.

## References

* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016, no. 8,
  2544–2567; arXiv:1410.5160v3, Lemma 4.4, Corollaries 4.5 and 4.6, Lemma 4.9 and Theorem 4.10.
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

end Restrict

section Presentation

open MvPowerSeries

variable (hv : v.Integers O) (hϖ : ϖ ≠ 0) (hϖ' : v (algebraMap O K ϖ) < 1) {ρ₁ ρ₂ ρ₁' : ℝ≥0}
  (hρ₁ : ρ₁ ∈ Set.Ioo 0 1) (hρ₂ : ρ₂ ∈ Set.Ioo 0 1) (hρ₁' : ρ₁' ∈ Set.Ioo 0 1)

/-- **Kedlaya's estimate (4.9.1)** in the normalisation `λ_ρ(p) = ρ`. Every
`d ∈ 𝕎 O[1/(p [ϖ])]` is a polynomial `∑_{i ≤ m} zᵢ p^(-(m - i))` in `p⁻¹` whose coefficients `zᵢ`
satisfy `λ_{[ρ₁, ρ₂]}(zᵢ) ρ₁'^(-(m - i)) ≤ λ_{[ρ₁', ρ₂]}(d)`, for `ρ₁ ≤ ρ₁'`. Write
`d = y / (p [ϖ]) ^ m` and split `y = ∑_{i < m} [yᵢ] pⁱ + pᵐ b`; then `zᵢ = [yᵢ] / [ϖ] ^ m` for
`i < m` and `zₘ = b / [ϖ] ^ m`. -/
private theorem exists_sum_eq_mul_inv_pow (h₁ : ρ₁ ≤ ρ₁')
    (d : IntervalLocalization p hv hϖ hϖ' hρ₁' hρ₂) :
    ∃ (m : ℕ) (z : ℕ → IntervalLocalization p hv hϖ hϖ' hρ₁' hρ₂),
      (∀ i ≤ m, max (gaussValuationAway p hv hϖ ρ₁ hρ₁ _ (z i))
          (gaussValuationAway p hv hϖ ρ₂ hρ₂ _ (z i)) * ρ₁'⁻¹ ^ (m - i) ≤
        max (gaussValuationAway p hv hϖ ρ₁' hρ₁' _ d) (gaussValuationAway p hv hϖ ρ₂ hρ₂ _ d)) ∧
      d = ∑ i ∈ Finset.range (m + 1),
        z i *
          ((IntervalLocalization.isUnit_natCast p hv hϖ hϖ' hρ₁' hρ₂).unit⁻¹ : _) ^ (m - i) := by
  -- Write `d = y / s` with `s = (p [ϖ]) ^ m`, split `y = ∑_{i < m} [yᵢ] pⁱ + pᵐ b`, and take
  -- `zᵢ = tᵢ / s` with `tᵢ = [yᵢ] pᵐ` for `i < m` and `tₘ = b pᵐ`. The first goal compares Gauss
  -- valuations term by term; the second is the identity `∑ tᵢ p^(-(m - i)) = y`.
  obtain ⟨⟨y, s⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Submonoid.powers ((p : 𝕎 O) * teichmuller p ϖ)) d
  set L' := IntervalLocalization p hv hϖ hϖ' hρ₁' hρ₂
  set u := (IntervalLocalization.isUnit_natCast p hv hϖ hϖ' hρ₁' hρ₂).unit
  obtain ⟨m, hm⟩ := s.2
  obtain ⟨b, hb⟩ := exists_eq_sum_teichmullerCoeff_add_pow_mul y m
  set t : ℕ → 𝕎 O := fun i ↦
    if i < m then teichmuller p (y.teichmullerCoeff i) * (p : 𝕎 O) ^ m else b * (p : 𝕎 O) ^ m
  refine ⟨m, fun i ↦ algebraMap (𝕎 O) L' (t i) * IsLocalization.mk' L' 1 s, fun i hi ↦ ?_, ?_⟩
  · set V := v (algebraMap O K ϖ)
    have hs {ρ : ℝ≥0} (hρ : ρ ∈ Set.Ioo 0 1) :
        gaussValuation p hv ρ hρ.2 (s : 𝕎 O) = (ρ * V) ^ m := by
      rw [← hm]
      simp [V]
    have hz {ρ : ℝ≥0} (hρ : ρ ∈ Set.Ioo 0 1) (x : 𝕎 O) :
        gaussValuationAway p hv hϖ ρ hρ L' (algebraMap (𝕎 O) L' x * IsLocalization.mk' L' 1 s) =
          gaussValuation p hv ρ hρ.2 x * ((ρ * V) ^ m)⁻¹ := by
      rw [map_mul, gaussValuationAway_algebraMap, gaussValuationAway_mk', map_one, one_mul, hs hρ]
    -- the factor `ρᵐ` contributed by `pᵐ` cancels against the denominator
    have hcancel {ρ : ℝ≥0} (hρ : ρ ∈ Set.Ioo 0 1) (a : ℝ≥0) :
        a * ρ ^ m * ((ρ * V) ^ m)⁻¹ = a * (V ^ m)⁻¹ := by
      rw [mul_pow, mul_inv, mul_assoc, mul_inv_cancel_left₀ (pow_ne_zero _ hρ.1.ne')]
    have hd₁ : gaussValuationAway p hv hϖ ρ₁' hρ₁' L' (IsLocalization.mk' L' y s) =
        gaussValuation p hv ρ₁' hρ₁'.2 y * ((ρ₁' * V) ^ m)⁻¹ := by
      rw [gaussValuationAway_mk', hs hρ₁']
    have hd₂ : gaussValuationAway p hv hϖ ρ₂ hρ₂ L' (IsLocalization.mk' L' y s) =
        gaussValuation p hv ρ₂ hρ₂.2 y * ((ρ₂ * V) ^ m)⁻¹ := by
      rw [gaussValuationAway_mk', hs hρ₂]
    rw [hd₁, hd₂]
    rcases hi.lt_or_eq with hi | rfl
    · -- a coefficient `[yᵢ] / [ϖ] ^ m` with `i < m`
      have hti (ρ : ℝ≥0) (hρ : ρ ∈ Set.Ioo 0 1) :
          gaussValuationAway p hv hϖ ρ hρ L'
              (algebraMap (𝕎 O) L' (t i) * IsLocalization.mk' L' 1 s) =
            v (algebraMap O K (y.teichmullerCoeff i)) * (V ^ m)⁻¹ := by
        rw [hz hρ]
        simp only [t, hi, ite_true, gaussValuation_teichmuller_mul_pow, hcancel hρ]
      rw [hti ρ₁ hρ₁, hti ρ₂ hρ₂, max_self]
      refine le_max_of_le_left ?_
      calc v (algebraMap O K (y.teichmullerCoeff i)) * (V ^ m)⁻¹ * ρ₁'⁻¹ ^ (m - i)
          = v (algebraMap O K (y.teichmullerCoeff i)) * ρ₁' ^ i * ((ρ₁' * V) ^ m)⁻¹ := by
            have : ρ₁' ^ i ≠ 0 := pow_ne_zero _ hρ₁'.1.ne'
            rw [inv_pow, mul_pow, ← pow_mul_pow_sub ρ₁' hi.le]
            field_simp
        _ ≤ _ := by gcongr; exact le_gaussValuation hv hρ₁'.2 y i
    · -- the tail coefficient `b / [ϖ] ^ m`
      have htm (ρ : ℝ≥0) (hρ : ρ ∈ Set.Ioo 0 1) :
          gaussValuationAway p hv hϖ ρ hρ L'
              (algebraMap (𝕎 O) L' (t i) * IsLocalization.mk' L' 1 s) =
            gaussValuation p hv ρ hρ.2 b * (V ^ i)⁻¹ := by
        rw [hz hρ]
        simp only [t, lt_self_iff_false, ite_false, map_mul, map_pow, gaussValuation_p, hcancel hρ]
      have htail (ρ : ℝ≥0) (hρ : ρ ∈ Set.Ioo 0 1) :
          gaussValuation p hv ρ hρ.2 b * (V ^ i)⁻¹ ≤
            gaussValuation p hv ρ hρ.2 y * ((ρ * V) ^ i)⁻¹ := by
        rw [mul_pow, mul_inv, ← mul_assoc]
        gcongr
        exact (le_mul_inv_iff₀ (pow_pos hρ.1 i)).mpr
          (gaussValuation_mul_pow_le_of_eq_sum_add_pow_mul hv hρ.2 hb)
      rw [htm ρ₁ hρ₁, htm ρ₂ hρ₂, Nat.sub_self, pow_zero, mul_one]
      refine max_le (le_max_of_le_left ((?_ : _ ≤ _).trans (htail ρ₁' hρ₁')))
        (le_max_of_le_right (htail ρ₂ hρ₂))
      gcongr
      exact gaussValuation_mono hv hρ₁.2 hρ₁'.2 h₁ b
  · -- `pᵐ p^(-(m - i)) = pⁱ` turns the sum into the Teichmüller splitting of `y`
    have hpu : (p : L') * (u⁻¹ : L'ˣ) = 1 := by
      simp [u]
    have hpow (i : ℕ) (hi : i ≤ m) :
        (p : L') ^ m * ((u⁻¹ : L'ˣ) : L') ^ (m - i) = (p : L') ^ i := by
      rw [← pow_mul_pow_sub (p : L') hi, mul_assoc, ← mul_pow, hpu, one_pow, mul_one]
    have key : ∀ i ∈ Finset.range m, algebraMap (𝕎 O) L' (t i) * ((u⁻¹ : L'ˣ) : L') ^ (m - i) =
        algebraMap (𝕎 O) L' (teichmuller p (y.teichmullerCoeff i) * (p : 𝕎 O) ^ i) := by
      intro i hi
      simp only [t, Finset.mem_range.mp hi, ite_true, map_mul, map_pow, map_natCast, mul_assoc,
        hpow i (Finset.mem_range.mp hi).le]
    dsimp only
    rw [IsLocalization.mk'_eq_mul_mk'_one y s]
    simp_rw [mul_right_comm _ (IsLocalization.mk' L' 1 s), ← Finset.sum_mul]
    congr 1
    rw [Finset.sum_range_succ, Finset.sum_congr rfl key, ← map_sum, Nat.sub_self, pow_zero, mul_one]
    simp only [t, lt_self_iff_false, ite_false, ← map_add]
    rw [mul_comm b, ← hb]

variable {hv hϖ hϖ' hρ₁ hρ₂} in
/-- `Ring.inverse p` in `B^I` is the image of `p⁻¹ ∈ 𝕎 O[1/(p [ϖ])]`. -/
private theorem ringInverse_natCast_intervalRing :
    Ring.inverse (p : IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) =
      (((IntervalLocalization.isUnit_natCast p hv hϖ hϖ' hρ₁ hρ₂).unit⁻¹ : _ˣ) :
        IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) := by
  set u := (IntervalLocalization.isUnit_natCast p hv hϖ hϖ' hρ₁ hρ₂).unit
  have h : (p : IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) =
      (Units.map (Completion.coeRingHom : IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂ →+*
        IntervalRing p hv hϖ hϖ' hρ₁ hρ₂).toMonoidHom u : _) := by
    simp [u]
  rw [h, Ring.inverse_unit, Units.coe_map_inv]
  -- `Completion.coeRingHom` is the coercion `𝕎 O[1/(p [ϖ])] → B^I`
  rfl

variable {hv hϖ hϖ' hρ₁ hρ₂} in
/-- The norm of `p⁻¹` in `B^I` is `max(ρ₁⁻¹, ρ₂⁻¹)`. -/
theorem norm_ringInverse_natCast_intervalRing :
    ‖Ring.inverse (p : IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)‖ = max (ρ₁ : ℝ)⁻¹ (ρ₂ : ℝ)⁻¹ := by
  have hp (ρ : ℝ≥0) (hρ : ρ ∈ Set.Ioo 0 1) :
      gaussValuationAway p hv hϖ ρ hρ (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) p = ρ := by
    rw [← map_natCast (algebraMap (𝕎 O) (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂)),
      gaussValuationAway_algebraMap, gaussValuation_p]
  rw [ringInverse_natCast_intervalRing, Completion.norm_coe, IntervalLocalization.norm_def,
    map_units_inv, map_units_inv, IsUnit.unit_spec, hp, hp, NNReal.coe_inv, NNReal.coe_inv]

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
      simpa [norm_ringInverse_natCast_intervalRing] using h) fun i ↦ by simp)

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

/-- **Lifting constants from `𝕎 O[1/(p [ϖ])]`.** Every `d ∈ 𝕎 O[1/(p [ϖ])]`, viewed as a constant
of `B^{[ρ₁', ρ₂]}{T/c}`, is the image of a polynomial in `U` of norm at most `λ_{[ρ₁', ρ₂]}(d)`,
by Kedlaya's estimate `exists_sum_eq_mul_inv_pow`. -/
private theorem exists_intervalRingRestrictedEval_eq_algebraMap_coe (h₁ : ρ₁ ≤ ρ₁')
    (h₁₂ : ρ₁' ≤ ρ₂) [∀ j, Fact (0 < (Fin.cons (ρ₁' : ℝ)⁻¹ c : Fin (k + 1) → ℝ) j)]
    (d : IntervalLocalization p hv hϖ hϖ' hρ₁' hρ₂) :
    ∃ g, intervalRingRestrictedEval p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' c h₁ h₁₂ g =
      algebraMap _ _ (d : IntervalRing p hv hϖ hϖ' hρ₁' hρ₂) ∧ ‖g‖ ≤ ‖d‖ := by
  obtain ⟨m, z, hz, hd⟩ := exists_sum_eq_mul_inv_pow hv hϖ hϖ' hρ₁ hρ₂ hρ₁' h₁ d
  set e := intervalLocalizationEquiv p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' hρ₂
  set U : IsRestricted.subring (R := IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)
      (Fin.cons (ρ₁' : ℝ)⁻¹ c : Fin (k + 1) → ℝ) :=
    ⟨X 0, isRestricted_monomial _ (Finsupp.single 0 1) 1⟩
  refine ⟨∑ i ∈ Finset.range (m + 1),
    algebraMap _ _ ((e.symm (z i) : IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) :
      IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) * U ^ (m - i), ?_, ?_⟩
  · simp only [map_sum, map_mul, map_pow, intervalRingRestrictedEval_algebraMap, U,
      intervalRingRestrictedEval_X_zero, intervalRingRestrict_coe, e, AlgEquiv.apply_symm_apply,
      ringInverse_natCast_intervalRing]
    conv_rhs => rw [hd]
    simp only [← map_pow, ← map_mul, ← map_sum]
    congr 1
    -- the completion map `𝕎 O[1/(p [ϖ])] → B^{[ρ₁', ρ₂]}` is a ring homomorphism
    exact (map_sum (Completion.coeRingHom : IntervalLocalization p hv hϖ hϖ' hρ₁' hρ₂ →+* _) _ _
      |>.trans
      (Finset.sum_congr rfl fun i _ ↦ by
        -- `Completion.coeRingHom` is the coercion `𝕎 O[1/(p [ϖ])] → B^{[ρ₁', ρ₂]}`
        rw [map_mul, map_pow]
        rfl)).symm
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg d) fun i hi ↦ ?_
    have hU : ‖U‖ = (ρ₁' : ℝ)⁻¹ := norm_X _
    have hb : ‖((e.symm (z i) : IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) :
        IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)‖ =
          max (gaussValuationAway p hv hϖ ρ₁ hρ₁ _ (z i) : ℝ)
            (gaussValuationAway p hv hϖ ρ₂ hρ₂ _ (z i)) := by
      rw [Completion.norm_coe, IntervalLocalization.norm_def, ← AlgEquiv.coe_toAlgHom,
        gaussValuationAway_algHom, gaussValuationAway_algHom]
    calc _ ≤ ‖algebraMap _ _ ((e.symm (z i) : IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) :
            IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)‖ * ‖U‖ ^ (m - i) :=
          (norm_mul_le _ _).trans (by gcongr; exact norm_pow_le _ _)
      _ ≤ ‖d‖ := by
        rw [norm_algebraMap_isRestrictedSubring, hb, hU, IntervalLocalization.norm_def]
        exact_mod_cast hz i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- **Lifting polynomials with coefficients in `𝕎 O[1/(p [ϖ])]`.** A polynomial in `T` whose
coefficients come from `𝕎 O[1/(p [ϖ])]` is the image of an element of no larger norm: lift each
coefficient by `exists_intervalRingRestrictedEval_eq_algebraMap_coe` and multiply by the matching
monomial in the variables `T`. -/
private theorem exists_intervalRingRestrictedEval_eq_of_finite (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂)
    [∀ j, Fact (0 < (Fin.cons (ρ₁' : ℝ)⁻¹ c : Fin (k + 1) → ℝ) j)]
    {h : IsRestricted.subring (R := IntervalRing p hv hϖ hϖ' hρ₁' hρ₂) c}
    (hfin :
      {α | coeff α (h : MvPowerSeries (Fin k) (IntervalRing p hv hϖ hϖ' hρ₁' hρ₂)) ≠ 0}.Finite)
    (hcoe : ∀ α, ∃ d : IntervalLocalization p hv hϖ hϖ' hρ₁' hρ₂,
      (d : IntervalRing p hv hϖ hϖ' hρ₁' hρ₂) =
        coeff α (h : MvPowerSeries (Fin k) (IntervalRing p hv hϖ hϖ' hρ₁' hρ₂))) :
    ∃ g, intervalRingRestrictedEval p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' c h₁ h₁₂ g = h ∧ ‖g‖ ≤ ‖h‖ := by
  classical
  choose d hd using hcoe
  choose g hg hgn using fun α ↦
    exists_intervalRingRestrictedEval_eq_algebraMap_coe hv hϖ hϖ' hρ₁ hρ₂ hρ₁' h₁ h₁₂ (c := c) (d α)
  -- the monomial `Tᵅ` in the variables `T i = X i.succ`
  set T : (Fin k →₀ ℕ) → IsRestricted.subring (R := IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)
      (Fin.cons (ρ₁' : ℝ)⁻¹ c : Fin (k + 1) → ℝ) := fun α ↦ α.prod fun i n ↦
    ⟨X i.succ, isRestricted_monomial _ (Finsupp.single i.succ 1) 1⟩ ^ n
  have hT (α : Fin k →₀ ℕ) : intervalRingRestrictedEval p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' c h₁ h₁₂ (T α) =
      ⟨monomial α 1, isRestricted_monomial c α 1⟩ := by
    simp [T, mk_monomial_eq_algebraMap_mul_prod]
  have hTn (α : Fin k →₀ ℕ) : ‖T α‖ ≤ α.prod (c · ^ ·) :=
    (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦
      (norm_pow_le _ _).trans (by rw [norm_X, Fin.cons_succ]))
  refine ⟨∑ α ∈ hfin.toFinset, g α * T α, ?_, ?_⟩
  · apply Subtype.ext
    ext β
    simp only [map_sum, map_mul, hg, hT, hd, AddSubmonoidClass.coe_finsetSum, Subring.coe_mul,
      coe_algebraMap_isRestrictedSubring, map_sum, coeff_C_mul, coeff_monomial, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Set.Finite.mem_toFinset]
    split_ifs with hβ
    · rfl
    · exact (not_not.mp hβ).symm
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg h) fun α _ ↦ ?_
    refine ((norm_mul_le _ _).trans (mul_le_mul ((hgn α).trans ?_) (hTn α) (norm_nonneg _)
      (norm_nonneg _))).trans (norm_coeff_mul_prod_le h α)
    rw [← hd α, Completion.norm_coe]

/-- **Kedlaya's Lemma 4.9, moving the left endpoint.** For `ρ₁ ≤ ρ₁' ≤ ρ₂`, the evaluation

```text
B^{[ρ₁, ρ₂]}{T/c, U/ρ₁'⁻¹} → B^{[ρ₁', ρ₂]}{T/c},    T ↦ T,  U ↦ p⁻¹,
```

is surjective, so `B^{[ρ₁', ρ₂]}{T/c}` is a quotient of a ring of restricted power series over
`B^{[ρ₁, ρ₂]}` with one more variable. The lifts are controlled: elements of
`𝕎 O[1/(p [ϖ])]` lift without increasing the norm (Kedlaya's estimate (4.9.1)), and these are dense,
so the open mapping argument of `controlled_closure_of_complete` lifts everything. -/
theorem intervalRingRestrictedEval_surjective (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂) :
    Function.Surjective (intervalRingRestrictedEval p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' c h₁ h₁₂) := by
  classical
  have : ∀ j, Fact (0 < (Fin.cons (ρ₁' : ℝ)⁻¹ c : Fin (k + 1) → ℝ) j) :=
    Fin.cases ⟨inv_pos.mpr (by exact_mod_cast hρ₁'.1)⟩ fun i ↦ ⟨(Fact.out : 0 < c i)⟩
  let Ψ' := (intervalRingRestrictedEval p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' c h₁ h₁₂).toAddMonoidHom
    |>.mkNormedAddGroupHom 1
    fun g ↦ by
      rw [one_mul]
      exact norm_intervalRingRestrictedEval_le hv hϖ hϖ' hρ₁ hρ₂ hρ₁' h₁ h₁₂ g
  -- the polynomials in `T` with coefficients in `𝕎 O[1/(p [ϖ])]`, which are dense
  set s : Set (IntervalRing p hv hϖ hϖ' hρ₁' hρ₂) :=
    Set.range ((↑) : IntervalLocalization p hv hϖ hϖ' hρ₁' hρ₂ → _)
  set K := AddSubgroup.closure ((fun x : (Fin k →₀ ℕ) × IntervalRing p hv hϖ hϖ' hρ₁' hρ₂ ↦
    (⟨monomial x.1 x.2, isRestricted_monomial c x.1 x.2⟩ : IsRestricted.subring (R := _) c)) ''
      (Set.univ ×ˢ s))
  have hK : Ψ'.SurjectiveOnWith K 1 := by
    intro h hh
    -- an element of `K` has finitely many coefficients, all from `𝕎 O[1/(p [ϖ])]`
    have hP :
        {α | coeff α (h : MvPowerSeries (Fin k) (IntervalRing p hv hϖ hϖ' hρ₁' hρ₂)) ≠ 0}.Finite ∧
        ∀ α, ∃ d : IntervalLocalization p hv hϖ hϖ' hρ₁' hρ₂,
          (d : IntervalRing p hv hϖ hϖ' hρ₁' hρ₂) =
            coeff α (h : MvPowerSeries (Fin k) (IntervalRing p hv hϖ hϖ' hρ₁' hρ₂)) := by
      induction hh using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨⟨t, b⟩, ⟨-, d, rfl⟩, rfl⟩ := hx
        refine ⟨(Set.finite_singleton t).subset fun α hα ↦ Set.mem_singleton_iff.mpr ?_,
          fun α ↦ ⟨if α = t then d else 0, ?_⟩⟩
        · by_contra h'
          exact hα (by simp [coeff_monomial, h'])
        · split_ifs with h'
          · simp [h']
          · simp [coeff_monomial, h']
      | zero => exact ⟨by simp, fun α ↦ ⟨0, by simp⟩⟩
      | add x y _ _ hx hy =>
        refine ⟨(hx.1.union hy.1).subset fun α hα ↦ ?_, fun α ↦ ?_⟩
        · by_contra h'
          simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h'
          exact hα (by simp [h'.1, h'.2])
        · obtain ⟨a, ha⟩ := hx.2 α
          obtain ⟨b, hb⟩ := hy.2 α
          exact ⟨a + b, by simp [Completion.coe_add, ha, hb]⟩
      | neg x _ hx =>
        refine ⟨by simpa using hx.1, fun α ↦ ?_⟩
        obtain ⟨a, ha⟩ := hx.2 α
        exact ⟨-a, by simp [Completion.coe_neg, ha]⟩
    obtain ⟨g, hg, hgn⟩ :=
      exists_intervalRingRestrictedEval_eq_of_finite hv hϖ hϖ' hρ₁ hρ₂ hρ₁' h₁ h₁₂ hP.1 hP.2
    exact ⟨g, hg, by simpa using hgn⟩
  have hdense : K.topologicalClosure = ⊤ := by
    rw [eq_top_iff, ← SetLike.coe_subset_coe, AddSubgroup.topologicalClosure_coe,
      (dense_closure_monomial (s := s) Completion.denseRange_coe).closure_eq]
    exact fun _ _ ↦ Set.mem_univ _
  intro h
  obtain ⟨g, hg, -⟩ := controlled_closure_of_complete one_pos one_pos hK h (hdense ▸ trivial)
  exact ⟨g, hg⟩

end Presentation

end TauCeti.WittVector
