/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.IntervalRing.Radius
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.RadiusRing

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.FirstCountable
import TauCeti.RingTheory.WittVector.IntervalRing.Presentation

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

This follows from the controlled lifts of
`TauCeti.WittVector.RadiusRing.exists_restrictedSeries_toIntervalRing_eq`: every `x ∈ B` is the
image of a series whose coefficients have norm at most `2 ‖x‖ / ρ₁ ^ (a - 1)`, so `ψ` is
surjective and the image of every neighbourhood of zero contains a ball around zero.

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

open _root_.WittVector

variable (p : ℕ) [Fact p.Prime] {K O : Type*} [Field K] [CommRing O] [Algebra O K]
  [CharP O p] [PerfectRing O p] {v : Valuation K ℝ≥0} {ϖ : O}
  (hv : v.Integers O) (hϖ : ϖ ≠ 0) (hϖ' : v (algebraMap O K ϖ) < 1)
  {ρ₁ ρ₂ : ℝ≥0} (hρ₁ : ρ₁ ∈ Set.Ioo 0 1) (hρ₂ : ρ₂ ∈ Set.Ioo 0 1)

local notation "𝕎" => _root_.WittVector p
local notation "A" => RadiusRing p hv hϖ hϖ' hρ₂
local notation "B" => IntervalRing p hv hϖ hϖ' hρ₁ hρ₂

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
  have hρa : (0 : ℝ) < ρ₁ ^ (a - 1) := pow_pos hρ₁.1 _
  refine ⟨surjective_restrictedSeries_toIntervalRing p hv hϖ hϖ' hρ₁ hρ₂ hρ ha hab hψ hC hX, hψ,
    IsTopologicalAddGroup.isOpenMap_iff_nhds_zero.mpr fun U hU ↦ ?_⟩
  -- `ψ ⁻¹' U` contains the series whose coefficients lie in a ball of radius `ε`, and every `x`
  -- with `‖x‖ < ρ₁ ^ (a - 1) ε / 2` lifts to such a series
  rw [Filter.mem_map] at hU
  obtain ⟨W, -, hWU⟩ := (hasBasis_nhds_zero_weightedTopology isWeightFamily_one_weight).mem_iff.mp
    hU
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp (W.mem_nhds_zero)
  refine Filter.mem_of_superset (Metric.ball_mem_nhds 0 (by positivity : 0 < ρ₁ ^ (a - 1) * ε / 2))
    fun x hx ↦ ?_
  rw [Metric.mem_ball, dist_zero_right] at hx
  obtain ⟨f, rfl, hf⟩ :=
    exists_restrictedSeries_toIntervalRing_eq p hv hϖ hϖ' hρ₁ hρ₂ hρ ha hab hψ hC hX one_pos x
  refine hWU (mem_weightedNhd.mpr fun ν ↦ ?_)
  rw [weightMul_one_weight]
  refine hεW (mem_ball_zero_iff.mpr (lt_of_mul_lt_mul_left ?_ hρa.le))
  linarith [hf ν]

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
