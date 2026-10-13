/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.IntervalRing.Radius
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.RadiusRing

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.FirstCountable
import TauCeti.Topology.Algebra.OpenMapping.Complete

/-!
# The interval rings `B^I` are strongly noetherian

Let `O` be the ring of integers of a valuation `v : Valuation K ℝ≥0` on a field `K`, perfect of
characteristic `p`, and let `ϖ ∈ O` be a pseudouniformiser. For radii `0 < ρ₁ ≤ ρ₂ < 1`, the
radius ring `A = A^{ρ₂}` (`TauCeti.WittVector.RadiusRing`) maps isometrically to the interval ring
`B = B^{[ρ₁, ρ₂]}` (`TauCeti.WittVector.IntervalRing`). When `ρ₁ ^ a = v(ϖ) ^ b` with `a ≠ 0`,
the element `[ϖ] ^ b / p ^ a` of `B` has norm one at the radius `ρ₁`, and the continuous map

```text
ψ : A⟨X⟩ → B,   X ↦ [ϖ] ^ b / p ^ a,
```

out of the one-variable restricted series ring over `A` is an open quotient map. This is the
surjective half of the third isomorphism of Kedlaya's Lemma 4.9,
`A^r_{L,E}{T}/(pT - [z ^ n]) ≅ B^{I'''}_{L,E}`, with `p ^ a` in place of `p`.

The key estimate takes place in `𝕎 O[1/(p [ϖ])]`, which is dense in `B`: writing an element as
`y / (p [ϖ]) ^ m` and expanding `y = ∑ᵢ [yᵢ] pⁱ` into Teichmüller terms, it is a finite sum of
monomials `e ([ϖ] ^ b / p ^ a) ^ j` whose coefficients `e ∈ 𝕎 O[1/[ϖ]]` have norm at most
`ρ₁⁻ᵃ` times its own norm. So the closure of the image under `ψ` of every neighbourhood of zero is
a neighbourhood of zero, and completeness of `A⟨X⟩` removes the closure
(`TauCeti.isOpenMap_of_closure_image_mem_nhds`).

The radius ring is strongly noetherian by Kedlaya's Theorem 3.2
(`TauCeti.WittVector.RadiusRing.isStronglyNoetherian`), hence so is `A⟨X⟩`, and strong
noetherianness descends along open quotient maps. This proves that `B` is strongly noetherian in
Huber's sense (Kedlaya, Theorem 4.10 at unit radii, Remark 4.11) for the intervals whose lower
radius is a rational power of `v(ϖ)`, which include the radii of every window of the
Fargues–Fontaine curve.

## Main results

* `TauCeti.WittVector.RadiusRing.isOpenQuotientMap_restrictedSeries_toIntervalRing` : the
  evaluation `A⟨X⟩ → B`, `X ↦ [ϖ] ^ b / p ^ a`, is an open quotient map when
  `ρ₁ ^ a = v(ϖ) ^ b`.
* `TauCeti.WittVector.isStronglyNoetherian_intervalRing` : `B^{[ρ₁, ρ₂]}` is strongly noetherian
  when `ρ₁ ^ a = v(ϖ) ^ b` for some `a ≠ 0`.

## References

* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016, no. 8,
  2544–2567; arXiv:1410.5160v3, Theorem 3.2, Lemma 4.9, Theorem 4.10 and Remark 4.11.
-/

public section

noncomputable section

open scoped NNReal Topology

namespace TauCeti.WittVector

open _root_.WittVector UniformSpace

variable (p : ℕ) [Fact p.Prime] {K O : Type*} [Field K] [CommRing O] [Algebra O K]
  [CharP O p] [PerfectRing O p] {v : Valuation K ℝ≥0} {ϖ : O}
  (hv : v.Integers O) (hϖ : ϖ ≠ 0) (hϖ' : v (algebraMap O K ϖ) < 1)
  {ρ₁ ρ₂ : ℝ≥0} (hρ₁ : ρ₁ ∈ Set.Ioo 0 1) (hρ₂ : ρ₂ ∈ Set.Ioo 0 1)

local notation "𝕎" => _root_.WittVector p
local notation "A₀" => RadiusLocalization p hv hϖ hϖ' hρ₂
local notation "B₀" => IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂
local notation "A" => RadiusRing p hv hϖ hϖ' hρ₂
local notation "B" => IntervalRing p hv hϖ hϖ' hρ₁ hρ₂
local notation "g" => RadiusLocalization.toIntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂

namespace IntervalLocalization

/-- A Teichmüller monomial `[c] p⁻ᵏ [ϖ]⁻ᵐ` of `𝕎 O[1/(p [ϖ])]` is `e z₀ ^ j` for some `e` in the
radius localisation `𝕎 O[1/[ϖ]]` whose norm `λ_{ρ₂}(e)` is at most `ρ₁⁻ᵃ v(c) ρ₁⁻ᵏ v(ϖ)⁻ᵐ`,
when `ρ₁ ^ a = v(ϖ) ^ b` and `z₀ p ^ a = [ϖ] ^ b`. -/
private theorem exists_toIntervalLocalization_mul_pow_eq {a b : ℕ} (ha : a ≠ 0)
    (hab : ρ₁ ^ a = v (algebraMap O K ϖ) ^ b) {z₀ : B₀}
    (hz : z₀ * (p : B₀) ^ a = algebraMap (𝕎 O) B₀ (teichmuller p ϖ ^ b)) (c : O) (k m : ℕ) :
    ∃ (e : A₀) (j : ℕ),
      g e * z₀ ^ j * ((p : B₀) ^ k * algebraMap (𝕎 O) B₀ (teichmuller p ϖ ^ m)) =
        algebraMap (𝕎 O) B₀ (teichmuller p c) ∧
      ‖e‖ * ρ₁ ^ a * (ρ₁ ^ k * v (algebraMap O K ϖ) ^ m) ≤ v (algebraMap O K c) := by
  have := hv.isDomain
  -- `j = ⌈k / a⌉`, so `a j = k + i` with `i < a`, and `e = [c] pⁱ [ϖ] ^ (-m - b j)`
  obtain ⟨j, i, hi, hji⟩ : ∃ j i : ℕ, i < a ∧ a * j = k + i := by
    have hk := Nat.div_add_mod k a
    rcases Nat.eq_zero_or_pos (k % a) with h0 | hpos
    · exact ⟨k / a, 0, Nat.pos_of_ne_zero ha, by omega⟩
    · refine ⟨k / a + 1, a - k % a, by omega, ?_⟩
      have := Nat.mod_lt k (Nat.pos_of_ne_zero ha)
      rw [mul_add, mul_one]
      omega
  let s : Submonoid.powers (teichmuller p ϖ) := ⟨teichmuller p ϖ ^ (m + b * j), m + b * j, rfl⟩
  let e : A₀ := IsLocalization.mk' A₀ (teichmuller p c * (p : 𝕎 O) ^ i) s
  have hp : IsUnit ((p : B₀) ^ i) := (isUnit_natCast p hv hϖ hϖ' hρ₁ hρ₂).pow i
  refine ⟨e, j, hp.mul_right_cancel ?_, ?_⟩
  · have he : g e * algebraMap (𝕎 O) B₀ (teichmuller p ϖ ^ (m + b * j)) =
        algebraMap (𝕎 O) B₀ (teichmuller p c * (p : 𝕎 O) ^ i) := by
      simpa only [map_mul, AlgHom.commutes] using
        congrArg g (IsLocalization.mk'_spec A₀ (teichmuller p c * (p : 𝕎 O) ^ i) s)
    calc g e * z₀ ^ j * ((p : B₀) ^ k * algebraMap (𝕎 O) B₀ (teichmuller p ϖ ^ m)) * (p : B₀) ^ i
        = g e * ((z₀ * (p : B₀) ^ a) ^ j * algebraMap (𝕎 O) B₀ (teichmuller p ϖ ^ m)) := by
          rw [mul_pow, ← pow_mul, hji, pow_add]
          ring
      _ = algebraMap (𝕎 O) B₀ (teichmuller p c) * (p : B₀) ^ i := by
          rw [hz, ← map_pow, ← map_mul, ← pow_mul, ← pow_add, add_comm, he]
          simp
  · have hw : 0 < (v (algebraMap O K ϖ) : ℝ) := by
      rw [NNReal.coe_pos, pos_iff_ne_zero, map_ne_zero, map_ne_zero_iff _ hv.hom_inj]
      exact hϖ
    have hρ₁0 : (0 : ℝ) < ρ₁ := hρ₁.1
    have hne : ‖e‖ = v (algebraMap O K c) * ρ₂ ^ i *
        ((v (algebraMap O K ϖ) : ℝ) ^ m * ρ₁ ^ k * ρ₁ ^ i)⁻¹ := by
      have hbj : (v (algebraMap O K ϖ) : ℝ) ^ (b * j) = ρ₁ ^ k * ρ₁ ^ i := by
        rw [pow_mul, ← NNReal.coe_pow, ← hab, NNReal.coe_pow, ← pow_mul, hji, pow_add]
      simp [e, s, RadiusLocalization.norm_mk', gaussValuation_teichmuller_mul_pow,
        gaussValuation_teichmuller, pow_add, hbj, mul_assoc]
    have hai : (ρ₁ : ℝ) ^ a = ρ₁ ^ i * ρ₁ ^ (a - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hi.le]
    rw [hne, hai]
    have hle : (ρ₂ : ℝ) ^ i * ρ₁ ^ (a - i) ≤ 1 :=
      (mul_le_of_le_one_left (by positivity) (pow_le_one₀ (by positivity) hρ₂.2.le)).trans
        (pow_le_one₀ (by positivity) hρ₁.2.le)
    calc (v (algebraMap O K c) : ℝ) * ρ₂ ^ i *
          ((v (algebraMap O K ϖ) : ℝ) ^ m * ρ₁ ^ k * ρ₁ ^ i)⁻¹ * (ρ₁ ^ i * ρ₁ ^ (a - i)) *
          (ρ₁ ^ k * v (algebraMap O K ϖ) ^ m)
        = v (algebraMap O K c) * (ρ₂ ^ i * ρ₁ ^ (a - i)) := by
          field_simp
      _ ≤ v (algebraMap O K c) := mul_le_of_le_one_right (by positivity) hle

/-- **Approximation with control in `𝕎 O[1/(p [ϖ])]`.** Let `a ≠ 0`, `ρ₁ ^ a = v(ϖ) ^ b` and
`z₀ p ^ a = [ϖ] ^ b`. Then every `x ∈ 𝕎 O[1/(p [ϖ])]` is a finite sum of elements `e z₀ ^ j`
with `e ∈ 𝕎 O[1/[ϖ]]` and `λ_{ρ₂}(e) ρ₁ ^ a ≤ λ_I(x)`: it lies in every additive subgroup
containing these. -/
private theorem mem_of_forall_toIntervalLocalization_mul_pow_mem {a b : ℕ} (ha : a ≠ 0)
    (hab : ρ₁ ^ a = v (algebraMap O K ϖ) ^ b) {z₀ : B₀}
    (hz : z₀ * (p : B₀) ^ a = algebraMap (𝕎 O) B₀ (teichmuller p ϖ ^ b)) {H : AddSubgroup B₀}
    (x : B₀) (hH : ∀ (e : A₀) (j : ℕ), ‖e‖ * ρ₁ ^ a ≤ ‖x‖ → g e * z₀ ^ j ∈ H) : x ∈ H := by
  have := hv.isDomain
  set ι := algebraMap (𝕎 O) B₀
  obtain ⟨⟨y, s⟩, hx⟩ := IsLocalization.mk'_surjective
    (Submonoid.powers ((p : 𝕎 O) * teichmuller p ϖ)) x
  dsimp only at hx
  subst hx
  obtain ⟨m, hm⟩ := s.2
  dsimp only at hm
  -- Write `x = y / (p [ϖ]) ^ m` and expand `y = ∑_{i ≤ m} [yᵢ] pⁱ + p ^ (m + 1) h`. Each term
  -- `[yᵢ] p ^ (i - m) [ϖ] ^ (-m)` is a monomial `e z₀ ^ j`, and the remainder `p h [ϖ] ^ (-m)`
  -- already lies in `𝕎 O[1/[ϖ]]`.
  obtain ⟨h, hh⟩ := pow_dvd_sub_sum_teichmullerCoeff y m
  have hy : y = ∑ i ∈ Finset.Iic m, teichmuller p (y.teichmullerCoeff i) * (p : 𝕎 O) ^ i +
      (p : 𝕎 O) ^ (m + 1) * h := by
    rw [← hh]
    ring
  choose e j he heb using fun i ↦ exists_toIntervalLocalization_mul_pow_eq p hv hϖ hϖ' hρ₁ hρ₂
    ha hab hz (y.teichmullerCoeff i) (m - i) m
  let t : Submonoid.powers (teichmuller p ϖ) := ⟨teichmuller p ϖ ^ m, m, rfl⟩
  let eh : A₀ := IsLocalization.mk' A₀ ((p : 𝕎 O) * h) t
  have heh : g eh * ι (teichmuller p ϖ ^ m) = ι ((p : 𝕎 O) * h) := by
    simpa only [map_mul, AlgHom.commutes] using
      congrArg g (IsLocalization.mk'_spec A₀ ((p : 𝕎 O) * h) t)
  have hs : ι s = (p : B₀) ^ m * ι (teichmuller p ϖ ^ m) := by
    rw [← hm, map_pow, map_mul, map_natCast, mul_pow, map_pow]
  have hxeq : IsLocalization.mk' B₀ y s = ∑ i ∈ Finset.Iic m, g (e i) * z₀ ^ j i + g eh := by
    apply (IsLocalization.map_units B₀ s).mul_right_cancel
    rw [IsLocalization.mk'_spec, hs, add_mul, Finset.sum_mul]
    conv_lhs => rw [hy]
    rw [map_add, map_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hpm : (p : B₀) ^ m = (p : B₀) ^ (m - i) * (p : B₀) ^ i := by
        rw [← pow_add, Nat.sub_add_cancel (Finset.mem_Iic.mp hi)]
      rw [map_mul, map_pow, map_natCast, ← he i, hpm]
      ring
    · rw [map_mul, map_pow, map_natCast, ← mul_assoc, pow_succ, mul_assoc _ (p : B₀),
        ← map_natCast ι p, ← map_mul, ← heh]
      ring
  -- the bounds, from `λ_ρ(y) = λ_ρ(x) (ρ v(ϖ)) ^ m` at both radii
  have hw : 0 < (v (algebraMap O K ϖ) : ℝ) := by
    rw [NNReal.coe_pos, pos_iff_ne_zero, map_ne_zero, map_ne_zero_iff _ hv.hom_inj]
    exact hϖ
  have hgy {ρ : ℝ≥0} (hρ : ρ ∈ Set.Ioo 0 1) :
      (gaussValuation p hv ρ hρ.2 y : ℝ) =
        gaussValuationAway p hv hϖ ρ hρ B₀ (IsLocalization.mk' B₀ y s) *
          (ρ ^ m * v (algebraMap O K ϖ) ^ m) := by
    have hρ0 : (0 : ℝ) < ρ := hρ.1
    rw [gaussValuationAway_mk', ← hm]
    simp only [map_pow, map_mul, gaussValuation_p, gaussValuation_teichmuller, NNReal.coe_mul,
      NNReal.coe_inv, NNReal.coe_pow]
    field_simp
    ring
  rw [hxeq, ← mul_one (g eh), ← pow_zero z₀]
  refine add_mem (sum_mem fun i hi ↦ hH _ _ ?_) (hH _ 0 ?_)
  · -- `v(yᵢ) ρ₁ ^ i ≤ λ_{ρ₁}(y)`
    have hρ₁0 : (0 : ℝ) < ρ₁ := hρ₁.1
    have him : i ≤ m := Finset.mem_Iic.mp hi
    have hyi : (v (algebraMap O K (y.teichmullerCoeff i)) : ℝ) * ρ₁ ^ i ≤
        gaussValuation p hv ρ₁ hρ₁.2 y := by
      exact_mod_cast le_gaussValuation hv hρ₁.2 y i
    have hpow : (ρ₁ : ℝ) ^ m = ρ₁ ^ (m - i) * ρ₁ ^ i := by
      rw [← pow_add, Nat.sub_add_cancel him]
    have hvy : (v (algebraMap O K (y.teichmullerCoeff i)) : ℝ) ≤
        gaussValuationAway p hv hϖ ρ₁ hρ₁ B₀ (IsLocalization.mk' B₀ y s) *
          (ρ₁ ^ (m - i) * v (algebraMap O K ϖ) ^ m) := by
      refine le_of_mul_le_mul_right (hyi.trans_eq ?_) (pow_pos hρ₁0 i)
      rw [hgy hρ₁, hpow]
      ring
    have hD : (0 : ℝ) < ρ₁ ^ (m - i) * v (algebraMap O K ϖ) ^ m := by positivity
    refine le_of_mul_le_mul_right ((heb i).trans (hvy.trans ?_)) hD
    rw [IntervalLocalization.norm_def]
    gcongr
    exact le_max_left _ _
  · -- `λ_{ρ₂}(p ^ (m + 1) h) ≤ λ_{ρ₂}(y)`, as each Teichmüller term is
    have hρ₂0 : (0 : ℝ) < ρ₂ := hρ₂.1
    have hrem : gaussValuation p hv ρ₂ hρ₂.2 ((p : 𝕎 O) ^ (m + 1) * h) ≤
        gaussValuation p hv ρ₂ hρ₂.2 y := by
      rw [← hh]
      refine Valuation.map_sub_le _ le_rfl (Valuation.map_sum_le _ fun i _ ↦ ?_)
      rw [gaussValuation_teichmuller_mul_pow]
      exact le_gaussValuation hv hρ₂.2 y i
    have hrem' : (ρ₂ : ℝ) ^ m * gaussValuation p hv ρ₂ hρ₂.2 ((p : 𝕎 O) * h) ≤
        gaussValuationAway p hv hϖ ρ₂ hρ₂ B₀ (IsLocalization.mk' B₀ y s) *
          (ρ₂ ^ m * v (algebraMap O K ϖ) ^ m) := by
      rw [← hgy hρ₂]
      simpa [pow_succ, mul_assoc, gaussValuation_p] using (NNReal.coe_le_coe.mpr hrem)
    have hnorm : ‖eh‖ = gaussValuation p hv ρ₂ hρ₂.2 ((p : 𝕎 O) * h) *
        ((v (algebraMap O K ϖ) : ℝ) ^ m)⁻¹ := by
      simp [eh, t, RadiusLocalization.norm_mk', gaussValuation_teichmuller]
    have hρa : (ρ₁ : ℝ) ^ a ≤ 1 := pow_le_one₀ (by positivity) hρ₁.2.le
    refine (mul_le_of_le_one_right (norm_nonneg _) hρa).trans ?_
    rw [hnorm, IntervalLocalization.norm_def]
    refine le_trans ?_ (le_max_right _ _)
    rw [mul_inv_le_iff₀ (by positivity)]
    refine le_of_mul_le_mul_left ?_ (pow_pos hρ₂0 m)
    linarith

end IntervalLocalization

namespace RadiusRing

open TauCeti.Huber

local notation "S" => weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A))
  isWeightFamily_one_weight

/-- **The interval ring is an open quotient of restricted series over the radius ring** (Kedlaya,
Lemma 4.9, third isomorphism, surjectivity). Let `ρ₁ ≤ ρ₂`, `a ≠ 0` and `ρ₁ ^ a = v(ϖ) ^ b`. A
continuous ring homomorphism `ψ : A^{ρ₂}⟨X⟩ → B^{[ρ₁, ρ₂]}` extending the coefficient map and
sending `X` to `[ϖ] ^ b / p ^ a` is an open quotient map. Such a `ψ` exists, and is unique, by
`TauCeti.WittVector.RadiusRing.existsUnique_continuous_denseRange_restrictedSeries_toIntervalRing`.
-/
theorem isOpenQuotientMap_restrictedSeries_toIntervalRing (hρ : ρ₁ ≤ ρ₂) {a b : ℕ} (ha : a ≠ 0)
    (hab : ρ₁ ^ a = v (algebraMap O K ϖ) ^ b) {ψ : S →+* B} (hψ : Continuous ψ)
    (hC : ∀ c, ψ (weightedC _ isWeightFamily_one_weight c) =
      toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ c)
    (hX : ψ (weightedX _ isWeightFamily_one_weight 0) * (p : B) ^ a =
      algebraMap (𝕎 O) B (teichmuller p ϖ ^ b)) :
    IsOpenQuotientMap ψ := by
  have hρa : (0 : ℝ) < ρ₁ ^ a := pow_pos hρ₁.1 a
  -- Mathlib has no application lemmas for `Completion.coeRingHom` at powers and casts.
  have hcoe_pow (x : B₀) (n : ℕ) : ((x ^ n : B₀) : B) = (x : B) ^ n :=
    map_pow (Completion.coeRingHom : B₀ →+* B) x n
  have hcoe_p : (((p : B₀)) : B) = (p : B) := map_natCast (Completion.coeRingHom : B₀ →+* B) p
  -- the value of the variable, `z₀ = [ϖ] ^ b / p ^ a`, already lies in `𝕎 O[1/(p [ϖ])]`
  have hp₀ := IntervalLocalization.isUnit_natCast p hv hϖ hϖ' hρ₁ hρ₂
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : B₀, z₀ * (p : B₀) ^ a = algebraMap (𝕎 O) B₀ (teichmuller p ϖ ^ b) :=
    ⟨algebraMap (𝕎 O) B₀ (teichmuller p ϖ ^ b) * (↑hp₀.unit⁻¹ : B₀) ^ a, by
      rw [mul_assoc, ← mul_pow]
      simp⟩
  have hψX : ψ (weightedX _ isWeightFamily_one_weight 0) = (z₀ : B) := by
    apply ((isPseudoUniformizer_natCast_intervalRing p hv hϖ hϖ' hρ₁ hρ₂).isUnit.pow
      a).mul_right_cancel
    rw [hX, Completion.algebraMap_def, ← hz₀, Completion.coe_mul, hcoe_pow, hcoe_p]
  have hψmono (e : A₀) (j : ℕ) :
      ψ (weightedC _ isWeightFamily_one_weight (e : A) *
        weightedX _ isWeightFamily_one_weight 0 ^ j) = ((g e * z₀ ^ j : B₀) : B) := by
    rw [map_mul, map_pow, hC, hψX, toIntervalRing_coe, Completion.coe_mul, hcoe_pow]
  -- every element of `𝕎 O[1/(p [ϖ])]` lies in the image of the subgroup `V` of series whose
  -- coefficients have norm at most `r`, as soon as its norm is less than `ρ₁ ^ a r`
  have hmem {r : ℝ} (hr : 0 < r) (x : B₀) (hx : ‖x‖ < ρ₁ ^ a * r) :
      (x : B) ∈ ψ '' (weightedNhd (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight
        (IsUltrametricDist.closedBall_openAddSubgroup A hr).toAddSubgroup : Set S) := by
    let H : AddSubgroup B₀ :=
      ((weightedNhd (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight
        (IsUltrametricDist.closedBall_openAddSubgroup A hr).toAddSubgroup).map
          ψ.toAddMonoidHom).comap (Completion.toCompl : B₀ →+ B)
    refine IntervalLocalization.mem_of_forall_toIntervalLocalization_mul_pow_mem p hv hϖ hϖ' hρ₁
      hρ₂ ha hab hz₀ (H := H) x fun e j he ↦ ⟨_, ?_, hψmono e j⟩
    refine weightedC_mul_weightedX_pow_mem_weightedNhd _ ?_
    rw [weightMul_one_weight]
    have : ‖e‖ < r := lt_of_mul_lt_mul_right ((he.trans_lt hx).trans_eq (mul_comm _ _)) hρa.le
    simpa [IsUltrametricDist.closedBall_openAddSubgroup, Completion.norm_coe] using this.le
  -- the closure of the image of every neighbourhood of zero is a neighbourhood of zero
  have hclosure : ∀ U ∈ 𝓝 (0 : S), closure (ψ '' U) ∈ 𝓝 (0 : B) := by
    intro U hU
    obtain ⟨W, -, hWU⟩ := (hasBasis_nhds_zero_weightedTopology isWeightFamily_one_weight).mem_iff.mp
      hU
    obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp (W.mem_nhds_zero)
    have hr : 0 < ε / 2 := half_pos hε
    have hVU : (weightedNhd (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight
        (IsUltrametricDist.closedBall_openAddSubgroup A hr).toAddSubgroup : Set S) ⊆ U := by
      refine subset_trans (SetLike.coe_subset_coe.mpr (weightedNhd_mono fun c hc ↦ hεW ?_)) hWU
      have hc' : ‖c‖ ≤ ε / 2 := by
        simpa [IsUltrametricDist.closedBall_openAddSubgroup] using hc
      simpa using hc'.trans_lt (half_lt_self hε)
    refine Filter.mem_of_superset (Metric.ball_mem_nhds 0 (mul_pos hρa hr)) fun y hy ↦ ?_
    refine closure_mono (Set.image_mono hVU) (closure_mono ?_
      (Completion.denseRange_coe.open_subset_closure_inter Metric.isOpen_ball hy))
    rintro _ ⟨hb, x, rfl⟩
    exact hmem hr x (by simpa [Completion.norm_coe] using hb)
  have hopen : IsOpenMap ψ :=
    isOpenMap_of_closure_image_mem_nhds ψ hψ.continuousAt hclosure
  -- the range is an open, hence closed, subgroup containing the dense image of `𝕎 O[1/(p [ϖ])]`
  refine ⟨fun y ↦ ?_, hψ, hopen⟩
  have hclosed : IsClosed (ψ.toAddMonoidHom.range : Set B) :=
    AddSubgroup.isClosed_of_isOpen _ (by simpa using hopen.isOpen_range)
  have hdense : Dense (ψ.toAddMonoidHom.range : Set B) := by
    refine Completion.denseRange_coe.mono ?_
    rintro _ ⟨x, rfl⟩
    obtain ⟨s, -, hs⟩ := hmem (r := (‖x‖ + 1) / ρ₁ ^ a) (by positivity) x
      (by rw [mul_div_cancel₀ _ hρa.ne']; linarith)
    exact ⟨s, hs⟩
  have huniv : (ψ.toAddMonoidHom.range : Set B) = Set.univ := by
    rw [← hclosed.closure_eq, hdense.closure_eq]
  obtain ⟨s, hs⟩ : y ∈ ψ.toAddMonoidHom.range := by
    rw [← SetLike.mem_coe, huniv]
    trivial
  exact ⟨s, hs⟩

end RadiusRing

open TauCeti.Huber in
/-- **The interval ring `B^I` is strongly noetherian** (Kedlaya, Theorem 4.10 and Remark 4.11),
for radii `ρ₁ ≤ ρ₂` with `ρ₁ ^ a = v(ϖ) ^ b` for some `a ≠ 0`. It is an open quotient of the
restricted series ring `A^{ρ₂}⟨X⟩` over the radius ring, which is strongly noetherian by
Kedlaya's Theorem 3.2. -/
theorem isStronglyNoetherian_intervalRing (hρ : ρ₁ ≤ ρ₂) {a b : ℕ} (ha : a ≠ 0)
    (hab : ρ₁ ^ a = v (algebraMap O K ϖ) ^ b) : IsStronglyNoetherian B := by
  obtain ⟨ψ, hψ, -, hC, hX, -⟩ :=
    RadiusRing.existsUnique_continuous_denseRange_restrictedSeries_toIntervalRing p hv hϖ hϖ' hρ₁
      hρ₂ hρ ha hab.ge
  exact (RadiusRing.isOpenQuotientMap_restrictedSeries_toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ ha
    hab hψ hC hX).isStronglyNoetherian

end TauCeti.WittVector
