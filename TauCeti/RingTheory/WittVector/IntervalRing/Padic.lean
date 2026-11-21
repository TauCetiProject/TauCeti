/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.FractionField
public import TauCeti.RingTheory.WittVector.IntervalRing.Subinterval
public import TauCeti.RingTheory.WittVector.PadicInt

/-!
# The interval rings `B^I` are `ℚ_p`-algebras

Let `O` be the ring of integers of a valuation `v : Valuation K ℝ≥0` on a field `K`, perfect of
characteristic `p`, let `ϖ ∈ O` be a pseudouniformiser, and let `B^I` be the interval ring of
radii `ρ₁, ρ₂ ∈ (0, 1)`, the completion of `𝕎 O[1/(p [ϖ])]` for the interval norm
(`TauCeti.WittVector.IntervalRing`); for `O = 𝒪_F` these rings are the coordinate rings of the
affinoid charts of the period domain `𝒴 = D(p) ∩ D([ϖ])` of the Fargues–Fontaine curve.

The structure map `ℤ_p → 𝕎 O` (`TauCeti.WittVector.padicIntHom`) followed by `𝕎 O → B^I` sends
`p` to a unit, so it extends uniquely to `ℚ_p = ℤ_p[1/p]`. This file makes `𝕎 O[1/(p [ϖ])]`,
and hence its completion `B^I`, a `ℚ_[p]`-algebra in this way, and shows:

* the map `ℚ_[p] → B^I` is continuous, and it is the only continuous ring homomorphism
  `ℚ_[p] → B^I`;
* it carries `ℤ_[p]` into the unit ball `B^{I,+}`, the power-bounded subring of `B^I`, and sends
  `p⁻¹` to the inverse of `p` in `B^I`;
* restriction `B^I → B^J` to a subinterval is `ℚ_[p]`-linear.

So `(ℚ_[p], ℤ_[p]) → (B^I, B^{I,+})` is a continuous map of pairs of rings, compatible with
restriction; this file builds no morphism of adic spaces `Spa(B^I, B^{I,+}) → Spa(ℚ_p, ℤ_p)`.
Together with `TauCeti.WittVector.frobenius_comp_padicIntHom`, which says that Frobenius on
`𝕎 O` is a map over `ℤ_p`, these are the ring-level inputs to the structure maps of the charts
`Spa(B^I, B^{I,+})` to `Spa(ℚ_p, ℤ_p)` and to the factorisation of the structure maps
`𝒴 → Spa(ℤ_p, ℤ_p)` and `𝒳 → Spa(ℤ_p, ℤ_p)` through `Spa(ℚ_p, ℤ_p)`.

## Main results

* `TauCeti.WittVector.algebraMap_padic_coe_intervalRing`: on `ℤ_[p]`, the map `ℚ_[p] → B^I` is
  `ℤ_[p] → 𝕎 O → B^I`.
* `TauCeti.WittVector.continuous_algebraMap_padic_intervalRing` and
  `TauCeti.WittVector.eq_algebraMap_padic_intervalRing_of_continuous`: the map `ℚ_[p] → B^I` is
  the unique continuous ring homomorphism.
* `TauCeti.WittVector.algebraMap_padic_coe_mem_powerBoundedSubring_intervalRing`: it carries
  `ℤ_[p]` into `B^{I,+}`.
* `TauCeti.WittVector.algebraMap_padic_inv_natCast_intervalRing`: it sends `p⁻¹` to the inverse of
  `p` in `B^I`.
* `TauCeti.WittVector.intervalRingRestrict_algebraMap_padic`: restriction to a subinterval is
  `ℚ_[p]`-linear.

## References

* L. Fargues and P. Scholze, *Geometrization of the local Langlands correspondence*, §II.1.1.
* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016, no. 8,
  2544–2567, for the rings `B^I`.
-/

public section

open scoped NNReal

namespace TauCeti.WittVector

open _root_.WittVector UniformSpace TauCeti.Huber

variable {p : ℕ} [Fact p.Prime] {K O : Type*} [Field K] [CommRing O] [Algebra O K]
  [CharP O p] {v : Valuation K ℝ≥0} {ϖ : O}
  {hv : v.Integers O} {hϖ : ϖ ≠ 0} {hϖ' : v (algebraMap O K ϖ) < 1} {ρ₁ ρ₂ : ℝ≥0}
  {hρ₁ : ρ₁ ∈ Set.Ioo 0 1} {hρ₂ : ρ₂ ∈ Set.Ioo 0 1}

local notation "𝕎" => _root_.WittVector p

namespace IntervalLocalization

/-- **`𝕎 O[1/(p [ϖ])]` is a `ℚ_p`-algebra**: the structure map `ℤ_p → 𝕎 O → 𝕎 O[1/(p [ϖ])]`
sends `p` to a unit, so it extends uniquely to `ℚ_[p]`, the fraction field of `ℤ_[p]`. -/
noncomputable instance : Algebra ℚ_[p] (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) :=
  (IsLocalization.lift (M := nonZeroDivisors ℤ_[p]) (S := ℚ_[p])
    (g := (algebraMap (𝕎 O) (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂)).comp (padicIntHom p O))
    fun y ↦ PadicInt.isUnit_map_of_ne_zero _ (isUnit_natCast p hv hϖ hϖ' hρ₁ hρ₂)
      (nonZeroDivisors.coe_ne_zero y)).toAlgebra

/-- On `ℤ_[p]`, the structure map `ℚ_[p] → 𝕎 O[1/(p [ϖ])]` is `ℤ_[p] → 𝕎 O → 𝕎 O[1/(p [ϖ])]`. -/
@[simp]
theorem algebraMap_padic_coe (x : ℤ_[p]) :
    algebraMap ℚ_[p] (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) x =
      algebraMap (𝕎 O) (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) (padicIntHom p O x) := by
  rw [← PadicInt.algebraMap_apply, RingHom.algebraMap_toAlgebra, IsLocalization.lift_eq,
    RingHom.comp_apply]

variable [PerfectRing O p]

/-- Scalar multiplication by `ℚ_[p]` is uniformly continuous, so that the `ℚ_[p]`-algebra
structure extends to the completion `B^I`. -/
instance : UniformContinuousConstSMul ℚ_[p] (IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂) :=
  ⟨fun c ↦ by
    simp_rw [Algebra.smul_def]
    exact (Ring.uniformContinuousConstSMul _).uniformContinuous_const_smul _⟩

end IntervalLocalization

variable [PerfectRing O p]

/-- On `ℤ_[p]`, the structure map `ℚ_[p] → B^I` is `ℤ_[p] → 𝕎 O → B^I`. -/
@[simp]
theorem algebraMap_padic_coe_intervalRing (x : ℤ_[p]) :
    algebraMap ℚ_[p] (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) x =
      algebraMap (𝕎 O) (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) (padicIntHom p O x) := by
  rw [Completion.algebraMap_def, Completion.algebraMap_def,
    IntervalLocalization.algebraMap_padic_coe]

/-- **The structure map `ℚ_[p] → B^I` is continuous.** Its restriction to the open subring
`ℤ_[p]` is the composite of the continuous maps `ℤ_[p] → 𝕎 O` and `𝕎 O → B^I`, for the
`(p, [ϖ])`-adic topology on `𝕎 O`. -/
theorem continuous_algebraMap_padic_intervalRing :
    Continuous (algebraMap ℚ_[p] (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)) := by
  let : TopologicalSpace (𝕎 O) := (Ideal.span {(p : 𝕎 O), teichmuller p ϖ}).adicTopology
  have hI : IsAdic (Ideal.span {(p : 𝕎 O), teichmuller p ϖ}) := rfl
  rw [Padic.continuous_iff_continuous_comp_coe]
  have h := (continuous_algebraMap_intervalRing p hv hϖ hϖ' hρ₁ hρ₂ hI).comp
    (PadicInt.continuous_of_isAdic hI (Ideal.subset_span (by simp)) (padicIntHom p O))
  exact h.congr fun x ↦ (algebraMap_padic_coe_intervalRing x).symm

/-- **The structure map is the unique continuous ring homomorphism `ℚ_[p] → B^I`.** -/
theorem eq_algebraMap_padic_intervalRing_of_continuous
    (f : ℚ_[p] →+* IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) (hf : Continuous f) :
    f = algebraMap ℚ_[p] (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) :=
  Padic.ringHom_ext_of_continuous hf continuous_algebraMap_padic_intervalRing

/-- **The structure map carries `ℤ_[p]` into the unit ball of `B^I`**, since `ℤ_[p]` lands in
`𝕎 O`, on which every Gauss valuation is at most `1`. -/
theorem norm_algebraMap_padic_coe_intervalRing_le_one (x : ℤ_[p]) :
    ‖algebraMap ℚ_[p] (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) x‖ ≤ 1 := by
  rw [algebraMap_padic_coe_intervalRing, norm_algebraMap_intervalRing]
  exact_mod_cast max_le (gaussValuation_le_one hv hρ₁.2 _) (gaussValuation_le_one hv hρ₂.2 _)

/-- **The structure map carries `ℤ_[p]` into `B^{I,+}`**, the power-bounded subring of `B^I`, so
that `(ℚ_[p], ℤ_[p]) → (B^I, B^{I,+})` is a morphism of Huber pairs. -/
theorem algebraMap_padic_coe_mem_powerBoundedSubring_intervalRing (x : ℤ_[p]) :
    algebraMap ℚ_[p] (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) x ∈
      powerBoundedSubring (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) := by
  rw [← SetLike.mem_coe, coe_powerBoundedSubring_intervalRing, mem_closedBall_zero_iff]
  exact norm_algebraMap_padic_coe_intervalRing_le_one x

/-- **The structure map sends `p⁻¹` to the inverse of `p` in `B^I`.** -/
@[simp]
theorem algebraMap_padic_inv_natCast_intervalRing :
    algebraMap ℚ_[p] (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) (p : ℚ_[p])⁻¹ =
      Ring.inverse (p : IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) := by
  have hp : IsUnit (p : ℚ_[p]) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  rw [← Ring.inverse_eq_inv, hp.map_ringInverse, map_natCast]

/-- **Restriction to a subinterval is `ℚ_[p]`-linear**: the restriction
`B^{[ρ₁, ρ₂]} → B^{[ρ₁', ρ₂']}` commutes with the structure maps from `ℚ_[p]`, since it commutes
with those from `𝕎 O`. -/
@[simp]
theorem intervalRingRestrict_algebraMap_padic {ρ₁' ρ₂' : ℝ≥0} {hρ₁' : ρ₁' ∈ Set.Ioo 0 1}
    {hρ₂' : ρ₂' ∈ Set.Ioo 0 1} (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂') (h₂ : ρ₂' ≤ ρ₂) (x : ℚ_[p]) :
    intervalRingRestrict p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' hρ₂' h₁ h₁₂ h₂
        (algebraMap ℚ_[p] (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) x) =
      algebraMap ℚ_[p] (IntervalRing p hv hϖ hϖ' hρ₁' hρ₂') x := by
  have h := IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    (j := (intervalRingRestrict p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' hρ₂' h₁ h₁₂ h₂ : _ →+* _).comp
      (algebraMap ℚ_[p] (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)))
    (k := algebraMap ℚ_[p] (IntervalRing p hv hϖ hϖ' hρ₁' hρ₂')) <| by
      ext y
      simp
  exact congr($h x)

end TauCeti.WittVector
