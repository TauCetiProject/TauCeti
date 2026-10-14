/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.IntervalRing.Radius
public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Eval
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Surjective
import Mathlib.Analysis.Normed.Group.ControlledClosure

/-!
# Interval rings as strict quotients of restricted series over radius rings

For `0 < ρ₁ ≤ ρ₂ < 1`, `a ≠ 0` and `v(ϖ)ᵇ ≤ ρ₁ᵃ`, the evaluation `X ↦ [ϖ]ᵇ/pᵃ` gives a continuous
map `ψ : A^{ρ₂}{X} → B^{[ρ₁, ρ₂]}` from the one-variable restricted series ring over the radius
ring to the interval ring
(`RadiusRing.existsUnique_continuous_denseRange_restrictedSeries_toIntervalRing`).
This file proves that `ψ` does not increase norms, and that it is a strict surjection when the
left endpoint is a rational power of `v(ϖ)`, that is, when `ρ₁ᵃ = v(ϖ)ᵇ`: every `x ∈ B^I` is `ψ f`
for a series `f` whose coefficients have norm at most `(1 + ε) ‖x‖ / ρ₁^(a - 1)`. This presents
`B^I` as a quotient of `A^{ρ₂}{X}` with controlled lifts, which is how Kedlaya transfers the
noetherianity of restricted series over `A^r` (Theorem 3.2) to the interval rings (Theorem 4.10).

The lift of an element of the dense subring `𝕎 O[1/(p [ϖ])]` is explicit. Write it as
`y / (p [ϖ])ᵐ` and split the Teichmüller expansion `y = ∑_{i < m} [yᵢ] pⁱ + pᵐ t`. Since
`p⁻ᵃ = X / [ϖ]ᵇ` in the image, `p^(-(m - i)) = pᵏ (X / [ϖ]ᵇ)ʲ` whenever `a j = m - i + k`, and
choosing `k < a` makes `y / (p [ϖ])ᵐ` the image of
`t / [ϖ]ᵐ + ∑_{i < m} ([yᵢ] pᵏ / [ϖ]^(m + b j)) Xʲ`. Its coefficients have norm at most
`max(λ_{ρ₁}, λ_{ρ₂})(y / (p [ϖ])ᵐ) / ρ₁^(a - 1)`: the tail at `ρ₂` and the terms `[yᵢ]` at `ρ₁`,
where `ρ₁ᵃ = v(ϖ)ᵇ` is used. Mathlib's successive approximation theorem
`controlled_closure_of_complete` then lifts every element of `B^I`, with the coefficient ring
`A^{ρ₂}{X}` normed by its Gauss norm through `TauCeti.Huber.restrictedMvPowerSeriesGaussEquiv`.

Every element of `𝕎 O[1/(p [ϖ])]` is a polynomial in `p⁻¹` with coefficients in `𝕎 O[1/[ϖ]]`
whose weighted norms are bounded by its interval norm (Kedlaya's estimate (4.9.1),
`IntervalLocalization.exists_sum_eq_mul_inv_pow`). Consequently, for every left endpoint
`ρ₁ ≤ ρ₂`, evaluation at `p⁻¹` is a surjection

```text
A^{ρ₂}{T/c, U/ρ₁⁻¹} → B^{[ρ₁, ρ₂]}{T/c},    T ↦ T,  U ↦ p⁻¹,
```

from restricted series at real radii. This is a form of the presentations of Kedlaya's Lemma 4.9,
which evaluate at `[z] / p` with `z ∈ K` instead; evaluating at `p⁻¹` at the real radius `ρ₁⁻¹`
needs no element of `K` of prescribed norm, so `ρ₁` is arbitrary. This is how the rings
`B^{[ρ₁, ρ₂]}{T/c}` inherit noetherianity from the radius ring.

## Main results

* `TauCeti.WittVector.RadiusRing.norm_restrictedSeries_toIntervalRing_le` : `ψ f` has norm at most
  any bound on the coefficient norms of `f`.
* `TauCeti.WittVector.RadiusRing.exists_restrictedSeries_toIntervalRing_eq` : if `ρ₁ᵃ = v(ϖ)ᵇ`,
  every `x ∈ B^I` is `ψ f` for some `f` whose coefficients have norm at most
  `(1 + ε) ‖x‖ / ρ₁^(a - 1)`.
* `TauCeti.WittVector.RadiusRing.surjective_restrictedSeries_toIntervalRing` : if `ρ₁ᵃ = v(ϖ)ᵇ`,
  then `ψ` is surjective.
* `TauCeti.WittVector.RadiusRing.restrictedEvalIntervalRing_surjective` : evaluation at `p⁻¹`
  presents `B^{[ρ₁, ρ₂]}{T/c}` as a quotient of `A^{ρ₂}{T/c, U/ρ₁⁻¹}`.

## References

* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016,
  arXiv:1410.5160v3, Lemma 4.9 (the isomorphism `A^r{T}/(pT - [zⁿ]) ≅ B^{I'''}` and the
  estimate (4.9.1) in its proof) and Theorem 4.10.
-/

public section

noncomputable section

open scoped NNReal

namespace TauCeti.WittVector

open _root_.WittVector UniformSpace TauCeti.Huber

variable (p : ℕ) [Fact p.Prime] {K O : Type*} [Field K] [CommRing O] [Algebra O K]
  [CharP O p] [PerfectRing O p] {v : Valuation K ℝ≥0} {ϖ : O}
  (hv : v.Integers O) (hϖ : ϖ ≠ 0) (hϖ' : v (algebraMap O K ϖ) < 1)
  {ρ₁ ρ₂ : ℝ≥0} (hρ₁ : ρ₁ ∈ Set.Ioo 0 1) (hρ₂ : ρ₂ ∈ Set.Ioo 0 1)

local notation "𝕎" => _root_.WittVector p
local notation "A₀" => RadiusLocalization p hv hϖ hϖ' hρ₂
local notation "B₀" => IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂
local notation "A" => RadiusRing p hv hϖ hϖ' hρ₂
local notation "B" => IntervalRing p hv hϖ hϖ' hρ₁ hρ₂
local notation "𝔸" => weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A))
  isWeightFamily_one_weight
local notation "𝕊" => MvPowerSeries.IsRestricted.subring (R := A) (fun _ : Fin 1 ↦ (1 : ℝ))

namespace RadiusRing

/-- **Evaluation at `[ϖ]ᵇ/pᵃ` does not increase norms.** Let `v(ϖ)ᵇ ≤ ρ₁ᵃ` and `ρ₁ ≤ ρ₂`, and let
`ψ : A^{ρ₂}{X} → B^{[ρ₁, ρ₂]}` be the continuous evaluation `X ↦ [ϖ]ᵇ/pᵃ` along the coefficient
map. If every coefficient of `f` has norm at most `r`, then `‖ψ f‖ ≤ r`. -/
theorem norm_restrictedSeries_toIntervalRing_le (hρ : ρ₁ ≤ ρ₂) {a b : ℕ}
    (hab : v (algebraMap O K ϖ) ^ b ≤ ρ₁ ^ a) {ψ : 𝔸 →+* B} (hψ : Continuous ψ)
    (hC : ∀ c, ψ (weightedC _ isWeightFamily_one_weight c) =
      toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ c)
    (hX : ψ (weightedX _ isWeightFamily_one_weight 0) * (p : B) ^ a =
      algebraMap (𝕎 O) B (teichmuller p ϖ ^ b))
    {f : 𝔸} {r : ℝ} (hf : ∀ ν, ‖MvPowerSeries.coeff ν (f : MvPowerSeries (Fin 1) A)‖ ≤ r) :
    ‖ψ f‖ ≤ r := by
  set φ := toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ
  -- `ψ` is the evaluation `∑ φ(aₖ) zᵏ` at the image `z = [ϖ]ᵇ/pᵃ` of `X`, of norm at most `1`
  obtain ⟨z, hz, hzp⟩ := exists_norm_le_one_algebraMap_eq_mul_intervalRing p hv hϖ hϖ' hρ₁ hρ₂
    (y := (p : 𝕎 O) ^ a) (x := teichmuller p ϖ ^ b)
    (by simpa using (IntervalLocalization.isUnit_natCast p hv hϖ hϖ' hρ₁ hρ₂).pow a)
    (by simpa using hab) (by simpa using hab.trans (pow_le_pow_left₀ zero_le hρ a))
  have hXz : ψ (weightedX _ isWeightFamily_one_weight 0) = z :=
    ((isPseudoUniformizer_natCast_intervalRing p hv hϖ hϖ' hρ₁ hρ₂).isUnit.pow a).mul_right_cancel
      (hX.trans (by simpa using hzp))
  have hφ : ContinuousAt φ 0 :=
    (isometry_toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ).continuous.continuousAt
  have hb : IsWeightBounded φ (fun _ : Fin 1 ↦ ({1} : Set A)) fun _ ↦ z :=
    (isWeightBounded_one_weight_iff_forall_isPowerBounded φ _).mpr fun _ ↦
      (isPowerBounded_iff_norm_le_one_intervalRing p hv hϖ hϖ' hρ₁ hρ₂).mpr hz
  have hψ' : ψ = weightedEvalHom isWeightFamily_one_weight hφ hb :=
    weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight hψ
      (continuous_weightedEvalHom _ hφ hb)
      (fun c ↦ (hC c).trans (weightedEvalHom_weightedC _ hφ hb c).symm)
      (fun i ↦ by rw [Subsingleton.elim i 0, hXz, weightedEvalHom_weightedX])
  rw [hψ', coe_weightedEvalHom, weightedEval_def]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg ((norm_nonneg _).trans (hf 0))
    fun ν ↦ ?_
  rw [weightedEvalTerm_def, Fin.prod_univ_one]
  calc _ ≤ ‖φ (MvPowerSeries.coeff ν (f : MvPowerSeries (Fin 1) A))‖ * ‖z ^ ν 0‖ := norm_mul_le _ _
    _ ≤ ‖MvPowerSeries.coeff ν (f : MvPowerSeries (Fin 1) A)‖ * 1 := by
      rw [norm_toIntervalRing]
      gcongr
      exact (norm_pow_le _ _).trans (pow_le_one₀ (norm_nonneg _) hz)
    _ ≤ r := by simpa using hf ν

include hϖ in
/-- The coefficients of the lift of `y / (p [ϖ])ᵐ` are bounded by its interval norm, up to the
factor `ρ₁^(a - 1)`. In terms of `V = v(ϖ)`, `λᵢ = λ_{ρᵢ}` and `y = ∑_{i < m} [yᵢ] pⁱ + pᵐ t`: the
constant coefficient `t / [ϖ]ᵐ` has norm `λ₂(t) / Vᵐ`; when `a j = m - i + k` with `k < a`, the
coefficient `[yᵢ] pᵏ / [ϖ]^(m + b j)` of `Xʲ` has norm `v(yᵢ) ρ₂ᵏ / V^(m + b j)`; and
`λᵢ(y / (p [ϖ])ᵐ) = λᵢ(y) / (ρᵢ V)ᵐ`. -/
private theorem coeff_le_max_gaussValuation {a b : ℕ} (hab : ρ₁ ^ a = v (algebraMap O K ϖ) ^ b)
    {y t : 𝕎 O} {m : ℕ}
    (ht : y = ∑ i ∈ Finset.range m, teichmuller p (y.teichmullerCoeff i) * (p : 𝕎 O) ^ i +
      (p : 𝕎 O) ^ m * t) :
    ρ₁ ^ (a - 1) * (gaussValuation p hv ρ₂ hρ₂.2 t * (v (algebraMap O K ϖ) ^ m)⁻¹) ≤
        max (gaussValuation p hv ρ₁ hρ₁.2 y * ((ρ₁ * v (algebraMap O K ϖ)) ^ m)⁻¹)
          (gaussValuation p hv ρ₂ hρ₂.2 y * ((ρ₂ * v (algebraMap O K ϖ)) ^ m)⁻¹) ∧
      ∀ i < m, ∀ j k : ℕ, k < a → a * j = m - i + k →
        ρ₁ ^ (a - 1) * (v (algebraMap O K (y.teichmullerCoeff i)) * ρ₂ ^ k *
          (v (algebraMap O K ϖ) ^ (m + b * j))⁻¹) ≤
        max (gaussValuation p hv ρ₁ hρ₁.2 y * ((ρ₁ * v (algebraMap O K ϖ)) ^ m)⁻¹)
          (gaussValuation p hv ρ₂ hρ₂.2 y * ((ρ₂ * v (algebraMap O K ϖ)) ^ m)⁻¹) := by
  set V := v (algebraMap O K ϖ)
  have hV : V ≠ 0 := (map_ne_zero _).mpr ((map_ne_zero_iff _ hv.hom_inj).mpr hϖ)
  have hρ : ρ₁ ≠ 0 := hρ₁.1.ne'
  refine ⟨le_max_of_le_right ?_, fun i hi j k hk hj ↦ le_max_of_le_left ?_⟩
  · -- the tail: `λ₂(t) ρ₂ᵐ ≤ λ₂(y)`, and `ρ₁^(a - 1) ≤ 1`
    refine (mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hρ₁.2.le)).trans ?_
    rw [mul_pow, mul_inv, ← mul_assoc]
    gcongr
    exact (le_mul_inv_iff₀ (pow_pos hρ₂.1 m)).mpr
      (gaussValuation_mul_pow_le_of_eq_sum_add_pow_mul hv hρ₂.2 ht)
  · -- a digit: `v(yᵢ) ρ₁ⁱ ≤ λ₁(y)`, `V^(b j) = ρ₁^(m - i + k)` and `ρ₁^(a - 1) ρ₂ᵏ ≤ ρ₁ᵏ`
    have hk' : k ≤ a - 1 := by omega
    calc ρ₁ ^ (a - 1) * (v (algebraMap O K (y.teichmullerCoeff i)) * ρ₂ ^ k * (V ^ (m + b * j))⁻¹)
        = v (algebraMap O K (y.teichmullerCoeff i)) * ρ₁ ^ i * ((ρ₁ * V) ^ m)⁻¹ *
            (ρ₂ ^ k * ρ₁ ^ (a - 1 - k)) := by
          rw [pow_add, pow_mul, ← hab, ← pow_mul, hj, mul_pow, ← pow_mul_pow_sub ρ₁ hi.le,
            ← pow_mul_pow_sub ρ₁ hk']
          field_simp
          ring
      _ ≤ v (algebraMap O K (y.teichmullerCoeff i)) * ρ₁ ^ i * ((ρ₁ * V) ^ m)⁻¹ * 1 := by
          gcongr
          exact mul_le_one' (pow_le_one₀ zero_le hρ₂.2.le) (pow_le_one₀ zero_le hρ₁.2.le)
      _ ≤ _ := by rw [mul_one]; gcongr; exact le_gaussValuation hv hρ₁.2 y i

/-- **The lift of the dense subring.** If `a ≠ 0` and `ρ₁ᵃ = v(ϖ)ᵇ`, every element `d` of
`𝕎 O[1/(p [ϖ])]` is the image of a polynomial in `X` whose Gauss norm times `ρ₁^(a - 1)` is at most
`‖d‖`. -/
private theorem exists_restrictedSeries_toIntervalRing_eq_coe (hρ : ρ₁ ≤ ρ₂) {a b : ℕ}
    (ha : a ≠ 0) (hab : ρ₁ ^ a = v (algebraMap O K ϖ) ^ b) {ψ : 𝔸 →+* B}
    (hC : ∀ c, ψ (weightedC _ isWeightFamily_one_weight c) =
      toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ c)
    (hX : ψ (weightedX _ isWeightFamily_one_weight 0) * (p : B) ^ a =
      algebraMap (𝕎 O) B (teichmuller p ϖ ^ b))
    (d : B₀) :
    ∃ g : 𝕊, ψ (restrictedMvPowerSeriesGaussEquiv.symm g) = (d : B) ∧
      ρ₁ ^ (a - 1) * ‖g‖ ≤ ‖(d : B)‖ := by
  classical
  -- Write `d = y / s` with `s = (p [ϖ])ᵐ` and split `y = ∑_{i < m} [yᵢ] pⁱ + pᵐ t`.
  obtain ⟨⟨y, s⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Submonoid.powers ((p : 𝕎 O) * teichmuller p ϖ)) d
  obtain ⟨m, hm⟩ := s.2
  obtain ⟨t, ht⟩ := exists_eq_sum_teichmullerCoeff_add_pow_mul y m
  -- `p⁻ᵏ = p^(I k) (X / [ϖ]ᵇ)^(J k)` in the image, where `a (J k) = k + I k` with `I k < a`
  have hceil (k : ℕ) : ∃ j i : ℕ, i < a ∧ a * j = k + i := by
    rcases Nat.eq_zero_or_pos (k % a) with h0 | hpos
    · exact ⟨k / a, 0, Nat.pos_of_ne_zero ha, by have := Nat.div_add_mod k a; omega⟩
    · refine ⟨k / a + 1, a - k % a, by omega, ?_⟩
      have := Nat.div_add_mod k a
      have := Nat.mod_lt k (Nat.pos_of_ne_zero ha)
      rw [mul_add, mul_one]
      omega
  choose J I hI hJ using hceil
  set ι := algebraMap (𝕎 O) A
  set u := (isUnit_algebraMap_teichmuller p hv hϖ hϖ' hρ₂ hϖ).unit
  set y' : ℕ → 𝕎 O := fun i ↦ teichmuller p (y.teichmullerCoeff i)
  set α : ℕ → A := fun i ↦
    ι (y' i * (p : 𝕎 O) ^ I (m - i)) * ((u⁻¹ : Aˣ) : A) ^ (m + b * J (m - i))
  set β : A := ι t * ((u⁻¹ : Aˣ) : A) ^ m
  set X' : 𝕊 := ⟨MvPowerSeries.X 0, MvPowerSeries.isRestricted_monomial _ (Finsupp.single 0 1) 1⟩
  have hu' : (u : A) = ι (teichmuller p ϖ) := IsUnit.unit_spec _
  have hu : ‖((u⁻¹ : Aˣ) : A)‖ = (v (algebraMap O K ϖ) : ℝ)⁻¹ := by
    have h : ‖(u : A)‖ * ‖((u⁻¹ : Aˣ) : A)‖ = 1 := by rw [← norm_mul, u.mul_inv, norm_one]
    rw [hu', norm_algebraMap_radiusRing, gaussValuation_teichmuller] at h
    exact eq_inv_of_mul_eq_one_right h
  refine ⟨algebraMap A 𝕊 β + ∑ i ∈ Finset.range m, algebraMap A 𝕊 (α i) * X' ^ J (m - i),
    ?_, ?_⟩
  · -- `ψ` sends `X` to `z = [ϖ]ᵇ/pᵃ`, so the polynomial goes to `y / (p [ϖ])ᵐ`.
    set φ := toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ
    set ιB := algebraMap (𝕎 O) B
    obtain ⟨z, hz⟩ : ∃ z, ψ (weightedX _ isWeightFamily_one_weight 0) = z := ⟨_, rfl⟩
    obtain ⟨w, hwu⟩ : ∃ w, φ ((u⁻¹ : Aˣ) : A) = w := ⟨_, rfl⟩
    rw [hz] at hX
    have hφι (x : 𝕎 O) : φ (ι x) = ιB x := toIntervalRing_algebraMap p hv hϖ hϖ' hρ₁ hρ₂ hρ x
    have hCe (c : A) : restrictedMvPowerSeriesGaussEquiv.symm (algebraMap A 𝕊 c) =
        weightedC _ isWeightFamily_one_weight c :=
      Subtype.ext (by simp [coe_weightedC])
    have hXe :
        restrictedMvPowerSeriesGaussEquiv.symm X' = weightedX _ isWeightFamily_one_weight 0 :=
      Subtype.ext (by simp [X', coe_weightedX])
    have hw : w * ιB (teichmuller p ϖ) = 1 := by
      rw [← hwu, ← hφι, ← hu', ← map_mul, u.inv_mul, map_one]
    have hs : ιB s = ((p : B) * ιB (teichmuller p ϖ)) ^ m := by
      rw [← hm, map_pow, map_mul, map_natCast]
    have hsu : IsUnit (ιB s) := hs ▸
      ((isPseudoUniformizer_natCast_intervalRing p hv hϖ hϖ' hρ₁ hρ₂).isUnit.mul
        (isPseudoUniformizer_teichmuller_intervalRing p hv hϖ hϖ' hρ₁ hρ₂).isUnit).pow m
    have hd : ((IsLocalization.mk' B₀ y s : B₀) : B) * ιB s = ιB y := by
      rw [Completion.algebraMap_def, Completion.algebraMap_def, ← Completion.coe_mul,
        IsLocalization.mk'_spec]
    -- each digit term: `w^(m + b J) z^J p^I (p [ϖ])ᵐ = pⁱ`, as `a J = m - i + I`
    have hterm (i : ℕ) (hi : i ≤ m) :
        (p : B) ^ I (m - i) * w ^ (m + b * J (m - i)) * z ^ J (m - i) *
          ((p : B) * ιB (teichmuller p ϖ)) ^ m = (p : B) ^ i := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
      rw [Nat.add_sub_cancel_left]
      have hzJ : (w ^ b * (z * (p : B) ^ a)) ^ J k =
          w ^ (b * J k) * z ^ J k * (p : B) ^ (k + I k) := by
        rw [← hJ k]
        ring
      calc _ = (w * ιB (teichmuller p ϖ)) ^ (i + k) * (w ^ b * (z * (p : B) ^ a)) ^ J k *
            (p : B) ^ i := by
            rw [hzJ]
            ring
        _ = (p : B) ^ i := by rw [hX, map_pow, ← mul_pow, hw]; simp
    apply hsu.mul_right_cancel
    rw [hd, ht, hs]
    simp only [map_add, map_sum, map_mul, map_pow, hCe, hXe, hC, hz, hwu, hφι, α, β, y',
      map_natCast, add_mul, Finset.sum_mul]
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [← hterm i (Finset.mem_range.mp hi).le]
      ring
    · calc _ = ιB t * (w * ιB (teichmuller p ϖ)) ^ m * (p : B) ^ m := by ring
        _ = _ := by rw [hw]; ring
  · -- the coefficient bounds of `coeff_le_max_gaussValuation`
    obtain ⟨hβ, hα⟩ := coeff_le_max_gaussValuation p hv hϖ hρ₁ hρ₂ hab ht
    have hnormC (c : A) : ‖algebraMap A 𝕊 c‖ = ‖c‖ := MvPowerSeries.norm_C c
    have hX' : ‖X'‖ = 1 := MvPowerSeries.norm_X 0
    have hρa : (0 : ℝ) < ρ₁ ^ (a - 1) := pow_pos hρ₁.1 _
    have hd : ‖((IsLocalization.mk' B₀ y s : B₀) : B)‖ =
        ↑(max (gaussValuation p hv ρ₁ hρ₁.2 y * ((ρ₁ * v (algebraMap O K ϖ)) ^ m)⁻¹)
          (gaussValuation p hv ρ₂ hρ₂.2 y * ((ρ₂ * v (algebraMap O K ϖ)) ^ m)⁻¹)) := by
      rw [Completion.norm_coe, IntervalLocalization.norm_def, gaussValuationAway_mk',
        gaussValuationAway_mk', ← hm]
      simp
    rw [hd, ← le_div_iff₀' hρa]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [hnormC, norm_mul, norm_pow, hu, norm_algebraMap_radiusRing, inv_pow, le_div_iff₀' hρa]
      exact_mod_cast hβ
    · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi ↦ ?_
      rw [norm_mul, norm_pow, hX', one_pow, mul_one, hnormC, norm_mul, norm_pow, hu,
        norm_algebraMap_radiusRing, gaussValuation_teichmuller_mul_pow, inv_pow,
        le_div_iff₀' hρa]
      exact_mod_cast hα i (Finset.mem_range.mp hi) _ _ (hI _) (hJ _)

/-- **Strict surjectivity of `A^{ρ₂}{X} → B^{[ρ₁, ρ₂]}`**, the surjective half of the third
isomorphism of Kedlaya's Lemma 4.9. Let
`ψ : A^{ρ₂}{X} → B^{[ρ₁, ρ₂]}` be the continuous evaluation `X ↦ [ϖ]ᵇ/pᵃ` along the coefficient
map, where `a ≠ 0`, `ρ₁ᵃ = v(ϖ)ᵇ` and `ρ₁ ≤ ρ₂`. For every `ε > 0`, every `x ∈ B^I` is `ψ f` for
a restricted series `f` whose coefficients have norm at most `(1 + ε) ‖x‖ / ρ₁^(a - 1)`. -/
theorem exists_restrictedSeries_toIntervalRing_eq (hρ : ρ₁ ≤ ρ₂) {a b : ℕ} (ha : a ≠ 0)
    (hab : ρ₁ ^ a = v (algebraMap O K ϖ) ^ b) {ψ : 𝔸 →+* B} (hψ : Continuous ψ)
    (hC : ∀ c, ψ (weightedC _ isWeightFamily_one_weight c) =
      toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ c)
    (hX : ψ (weightedX _ isWeightFamily_one_weight 0) * (p : B) ^ a =
      algebraMap (𝕎 O) B (teichmuller p ϖ ^ b))
    {ε : ℝ} (hε : 0 < ε) (x : B) :
    ∃ f : 𝔸, ψ f = x ∧
      ∀ ν, ρ₁ ^ (a - 1) * ‖MvPowerSeries.coeff ν (f : MvPowerSeries (Fin 1) A)‖ ≤
        (1 + ε) * ‖x‖ := by
  set e := restrictedMvPowerSeriesGaussEquiv (n := 1) (R := A)
  have hρa : (0 : ℝ) < ρ₁ ^ (a - 1) := pow_pos hρ₁.1 _
  -- `ψ ∘ e⁻¹` is a norm-nonincreasing group homomorphism on the Gauss-normed series ring
  have hcoeff (g : 𝕊) (ν : Fin 1 →₀ ℕ) :
      ‖MvPowerSeries.coeff ν (e.symm g : MvPowerSeries (Fin 1) A)‖ ≤ ‖g‖ := by
    simpa [e] using MvPowerSeries.norm_coeff_mul_prod_le g ν
  let Ψ : NormedAddGroupHom 𝕊 B := (ψ.comp e.symm.toRingHom).toAddMonoidHom.mkNormedAddGroupHom 1
    fun g ↦ (one_mul ‖g‖).symm ▸ norm_restrictedSeries_toIntervalRing_le p hv hϖ hϖ' hρ₁ hρ₂ hρ
      hab.ge hψ hC hX (hcoeff g)
  -- elements of the dense subring `𝕎 O[1/(p [ϖ])]` lift with norm control `ρ₁^(1 - a)`
  let L : AddSubgroup B := (Completion.coeRingHom : B₀ →+* B).toAddMonoidHom.range
  have hL : Ψ.SurjectiveOnWith L (ρ₁ ^ (a - 1) : ℝ)⁻¹ := by
    rintro _ ⟨d, rfl⟩
    obtain ⟨g, hg, hgn⟩ :=
      exists_restrictedSeries_toIntervalRing_eq_coe p hv hϖ hϖ' hρ₁ hρ₂ hρ ha hab hC hX d
    exact ⟨g, hg, (le_inv_mul_iff₀ hρa).mpr hgn⟩
  have hx : x ∈ L.topologicalClosure := by
    rw [← SetLike.mem_coe, AddSubgroup.topologicalClosure_coe]
    refine Dense.mono ?_ (Completion.denseRange_coe (α := B₀)) x
    rintro _ ⟨d, rfl⟩
    exact ⟨d, rfl⟩
  obtain ⟨g, hg, hgn⟩ :=
    controlled_closure_of_complete (inv_pos.mpr hρa) (mul_pos (inv_pos.mpr hρa) hε) hL x hx
  refine ⟨e.symm g, hg, fun ν ↦ ?_⟩
  calc (ρ₁ : ℝ) ^ (a - 1) * ‖MvPowerSeries.coeff ν (e.symm g : MvPowerSeries (Fin 1) A)‖
      ≤ ρ₁ ^ (a - 1) * (((ρ₁ ^ (a - 1) : ℝ)⁻¹ + (ρ₁ ^ (a - 1) : ℝ)⁻¹ * ε) * ‖x‖) := by
        gcongr
        exact (hcoeff g ν).trans hgn
    _ = (1 + ε) * ‖x‖ := by field_simp

/-- **Surjectivity of `A^{ρ₂}{X} → B^{[ρ₁, ρ₂]}`** (Kedlaya, Lemma 4.9). If `a ≠ 0` and
`ρ₁ᵃ = v(ϖ)ᵇ` with `ρ₁ ≤ ρ₂`, the continuous evaluation `X ↦ [ϖ]ᵇ/pᵃ` from `A^{ρ₂}{X}` to
`B^{[ρ₁, ρ₂]}` is surjective. -/
theorem surjective_restrictedSeries_toIntervalRing (hρ : ρ₁ ≤ ρ₂) {a b : ℕ} (ha : a ≠ 0)
    (hab : ρ₁ ^ a = v (algebraMap O K ϖ) ^ b) {ψ : 𝔸 →+* B} (hψ : Continuous ψ)
    (hC : ∀ c, ψ (weightedC _ isWeightFamily_one_weight c) =
      toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ c)
    (hX : ψ (weightedX _ isWeightFamily_one_weight 0) * (p : B) ^ a =
      algebraMap (𝕎 O) B (teichmuller p ϖ ^ b)) :
    Function.Surjective ψ := fun x ↦
  (exists_restrictedSeries_toIntervalRing_eq p hv hϖ hϖ' hρ₁ hρ₂ hρ ha hab hψ hC hX one_pos
    x).imp fun _ h ↦ h.1

section Presentation

open MvPowerSeries

variable {k : ℕ} (c : Fin k → ℝ) [∀ i, Fact (0 < c i)]

/-- **Evaluation at `p⁻¹` out of restricted series over the radius ring.** For `ρ₁ ≤ ρ₂`, the
ring homomorphism

```text
A^{ρ₂}{T/c, U/ρ₁⁻¹} → B^{[ρ₁, ρ₂]}{T/c},    T ↦ T,  U ↦ p⁻¹,
```

with coefficients mapped by `toIntervalRing`. Here `U = X 0` and `T i = X i.succ`, and `U` has
radius `ρ₁⁻¹`, the norm of `p⁻¹` in `B^{[ρ₁, ρ₂]}`. It is surjective
(`TauCeti.WittVector.RadiusRing.restrictedEvalIntervalRing_surjective`), for every left endpoint
`ρ₁`. -/
def restrictedEvalIntervalRing (hρ : ρ₁ ≤ ρ₂) :
    IsRestricted.subring (R := A) (Fin.cons (ρ₁ : ℝ)⁻¹ c : Fin (k + 1) → ℝ) →+*
      IsRestricted.subring (R := B) c :=
  restrictedEval₂ ((algebraMap _ _).comp (toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ))
    (Fin.cons (algebraMap _ _ (Ring.inverse (p : B)))
      fun i ↦ ⟨X i, isRestricted_monomial c (Finsupp.single i 1) 1⟩)
    (fun a ↦ by simp)
    (Fin.cases (by
      have h : ((ρ₂ : ℝ))⁻¹ ≤ (ρ₁ : ℝ)⁻¹ :=
        inv_anti₀ (by exact_mod_cast hρ₁.1) (by exact_mod_cast hρ)
      simpa using h) fun i ↦ by simp)

variable {c}

/-- The presentation maps constants by `toIntervalRing`. -/
@[simp]
theorem restrictedEvalIntervalRing_algebraMap (hρ : ρ₁ ≤ ρ₂) (a : A) :
    restrictedEvalIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ c hρ (algebraMap _ _ a) =
      algebraMap _ _ (toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ a) :=
  restrictedEval₂_algebraMap _ _ _ _ a

/-- The presentation sends the variable `U = X 0` to `p⁻¹`. -/
@[simp]
theorem restrictedEvalIntervalRing_X_zero (hρ : ρ₁ ≤ ρ₂) :
    restrictedEvalIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ c hρ
        ⟨X 0, isRestricted_monomial _ (Finsupp.single 0 1) 1⟩ =
      algebraMap _ _ (Ring.inverse (p : B)) :=
  restrictedEval₂_X _ _ _ _ 0

/-- The presentation sends each variable `T i = X i.succ` to `X i`. -/
@[simp]
theorem restrictedEvalIntervalRing_X_succ (hρ : ρ₁ ≤ ρ₂) (i : Fin k) :
    restrictedEvalIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ c hρ
        ⟨X i.succ, isRestricted_monomial _ (Finsupp.single i.succ 1) 1⟩ =
      ⟨X i, isRestricted_monomial c (Finsupp.single i 1) 1⟩ :=
  restrictedEval₂_X _ _ _ _ i.succ

/-- The presentation does not increase the Gauss norm. -/
theorem norm_restrictedEvalIntervalRing_le (hρ : ρ₁ ≤ ρ₂)
    [∀ j, Fact (0 < (Fin.cons (ρ₁ : ℝ)⁻¹ c : Fin (k + 1) → ℝ) j)]
    (f : IsRestricted.subring (R := A) (Fin.cons (ρ₁ : ℝ)⁻¹ c : Fin (k + 1) → ℝ)) :
    ‖restrictedEvalIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ c hρ f‖ ≤ ‖f‖ :=
  norm_restrictedEval₂_le _ _ _ _ f

/-- The presentation is continuous for the Gauss norms. -/
theorem continuous_restrictedEvalIntervalRing (hρ : ρ₁ ≤ ρ₂)
    [∀ j, Fact (0 < (Fin.cons (ρ₁ : ℝ)⁻¹ c : Fin (k + 1) → ℝ) j)] :
    Continuous (restrictedEvalIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ c hρ) :=
  continuous_restrictedEval₂ _ _ _ _

/-- **Uniqueness of the presentation**: a continuous ring homomorphism
`A^{ρ₂}{T/c, U/ρ₁⁻¹} → B^{[ρ₁, ρ₂]}{T/c}` that maps constants by `toIntervalRing` and sends `U` to
`p⁻¹` and each `T i` to `X i` is `restrictedEvalIntervalRing`. -/
theorem eq_restrictedEvalIntervalRing (hρ : ρ₁ ≤ ρ₂)
    [∀ j, Fact (0 < (Fin.cons (ρ₁ : ℝ)⁻¹ c : Fin (k + 1) → ℝ) j)]
    (ψ : IsRestricted.subring (R := A) (Fin.cons (ρ₁ : ℝ)⁻¹ c : Fin (k + 1) → ℝ) →+*
      IsRestricted.subring (R := B) c) (hψ : Continuous ψ)
    (hC : ∀ a, ψ (algebraMap _ _ a) = algebraMap _ _ (toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ a))
    (hU : ψ ⟨X 0, isRestricted_monomial _ (Finsupp.single 0 1) 1⟩ =
      algebraMap _ _ (Ring.inverse (p : B)))
    (hT : ∀ i : Fin k, ψ ⟨X i.succ, isRestricted_monomial _ (Finsupp.single i.succ 1) 1⟩ =
      ⟨X i, isRestricted_monomial c (Finsupp.single i 1) 1⟩) :
    ψ = restrictedEvalIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ c hρ := by
  rw [restrictedEvalIntervalRing]
  exact eq_restrictedEval₂ _ _ _ _ ψ hψ hC (Fin.cases hU hT)

/-- **The interval ring as a quotient of restricted series over the radius ring.** For `ρ₁ ≤ ρ₂`,
the evaluation

```text
A^{ρ₂}{T/c, U/ρ₁⁻¹} → B^{[ρ₁, ρ₂]}{T/c},    T ↦ T,  U ↦ p⁻¹,
```

is surjective, so `B^{[ρ₁, ρ₂]}{T/c}` is a quotient of a ring of restricted power series over the
radius ring `A^{ρ₂}` with one more variable. The left endpoint `ρ₁` is arbitrary. -/
theorem restrictedEvalIntervalRing_surjective (hρ : ρ₁ ≤ ρ₂) :
    Function.Surjective (restrictedEvalIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ c hρ) := by
  have : ∀ j, Fact (0 < (Fin.cons (ρ₁ : ℝ)⁻¹ c : Fin (k + 1) → ℝ) j) :=
    Fin.cases ⟨inv_pos.mpr (by exact_mod_cast hρ₁.1)⟩ fun i ↦ ⟨(Fact.out : 0 < c i)⟩
  set U : IsRestricted.subring (R := A) (Fin.cons (ρ₁ : ℝ)⁻¹ c : Fin (k + 1) → ℝ) :=
    ⟨X 0, isRestricted_monomial _ (Finsupp.single 0 1) 1⟩
  -- the constants from `𝕎 O[1/(p [ϖ])]`, which are dense in `B^{[ρ₁, ρ₂]}`
  refine surjective_of_exists_lift (norm_restrictedEvalIntervalRing_le p hv hϖ hϖ' hρ₁ hρ₂ hρ)
    (D := (Completion.coeRingHom : B₀ →+* B).range.toAddSubgroup)
    Completion.denseRange_coe ?_ fun i ↦ ⟨_, restrictedEvalIntervalRing_X_succ p hv hϖ hϖ' hρ₁
      hρ₂ hρ i, by simp⟩
  rintro _ ⟨d, rfl⟩
  obtain ⟨m, z, hz, hd⟩ := IntervalLocalization.exists_sum_eq_mul_inv_pow p hv hϖ hϖ' hρ₁ hρ₂ d
  -- `Completion.coeRingHom` is the coercion `𝕎 O[1/(p [ϖ])] → B^{[ρ₁, ρ₂]}`
  have hcoe (x : B₀) : (Completion.coeRingHom : B₀ →+* B) x = x := rfl
  refine ⟨∑ i ∈ Finset.range (m + 1), algebraMap A _ (z i : A) * U ^ (m - i), ?_, ?_⟩
  · rw [hd, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [map_mul, map_pow]
    simp [U, ringInverse_natCast_intervalRing, hcoe]
  · rw [hcoe, Completion.norm_coe]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg d) fun i hi ↦ ?_
    have hU : ‖U‖ = (ρ₁ : ℝ)⁻¹ := norm_X _
    calc _ ≤ ‖algebraMap A _ (z i : A)‖ * ‖U‖ ^ (m - i) :=
          (norm_mul_le _ _).trans (by gcongr; exact norm_pow_le _ _)
      _ ≤ ‖d‖ := by
        rw [norm_algebraMap_isRestrictedSubring, Completion.norm_coe, hU]
        exact hz i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

end Presentation

end RadiusRing

end TauCeti.WittVector
