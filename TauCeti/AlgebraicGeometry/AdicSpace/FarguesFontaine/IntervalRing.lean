/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.FarguesFontaine.GaussPoint
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.UniversalProperty
public import TauCeti.RingTheory.WittVector.IntervalRing

/-!
# The adic spectrum of an interval ring lies over a window

Let `O` be the ring of integers of a valuation `v : Valuation K ℝ≥0` on a field `K`, perfect of
characteristic `p`, let `ϖ ∈ O` be a pseudouniformiser, and give `𝕎 O` the `(p, [ϖ])`-adic
topology. For radii `ρ₁, ρ₂ ∈ (0, 1)` the interval ring `B^I` is the completion of
`𝕎 O[1/(p [ϖ])]` for the norm `λ_I = max(λ_{ρ₁}, λ_{ρ₂})`
(`TauCeti.WittVector.IntervalRing`), and its unit ball `B^{I,+}` is its power-bounded subring.

This file compares `B^I` with the Frobenius windows of `𝒴 ⊆ Spa(𝕎 O, 𝕎 O)`. The structure map
`𝕎 O → B^I` is continuous and carries `𝕎 O` into `B^{I,+}`, so pullback along it sends
`Spa(B^I, B^{I,+})` into `Spa(𝕎 O, 𝕎 O)`; it lands in `𝒴` because `p` and `[ϖ]` are units of
`B^I`. The radius `κ` of a pulled-back point is bounded by the radii of the two Gauss points
`η_{ρ₁}` and `η_{ρ₂}`: if `q ≤ κ(η_{ρᵢ})` for `i = 1, 2`, then `[ϖ] ^ b = z p ^ a` in `B^I` with
`λ_I(z) ≤ 1`, where `q = a / b`, so every point `w` of `Spa(B^I, B^{I,+})` has
`w([ϖ] ^ b) ≤ w(p ^ a)`, that is, `q ≤ κ(w)`; likewise for upper bounds. Hence if both Gauss
points lie in a window `U_n` (or `V_n`), so does the whole image of `Spa(B^I, B^{I,+})`. By
`TauCeti.FarguesFontaine.isRadiusLowerBound_gaussPoint_iff_rpow` this happens exactly when
both radii lie in `[v(ϖ) ^ (1 / q), v(ϖ) ^ (1 / q')]` for the window `q ≤ κ ≤ q'`.

Wedhorn's Lemma 8.1,
`TauCeti.ValuationSpectrum.existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset`,
then turns this into the comparison map of rings: for every presentation `R(T/s)` of a rational
subset containing the window, `𝕎 O → B^I` extends uniquely to a continuous ring homomorphism
`𝕎 O⟨T/s⟩ → B^I` out of the coordinate ring of the rational subset.

## Main results

* `TauCeti.FarguesFontaine.comap_algebraMap_intervalRing_mem_spaY` : pullback along
  `𝕎 O → B^I` sends `Spa(B^I, B^{I,+})` into `𝒴`.
* `TauCeti.FarguesFontaine.isRadiusLowerBound_comap_algebraMap_intervalRing` and its upper
  analogue : a radius bound satisfied by both Gauss points `η_{ρ₁}`, `η_{ρ₂}` holds on the image of
  `Spa(B^I, B^{I,+})`.
* `TauCeti.FarguesFontaine.comap_algebraMap_intervalRing_mem_windowU` and its `V` analogue : if
  both Gauss points lie in a window, the image of `Spa(B^I, B^{I,+})` lies in it.
* `TauCeti.FarguesFontaine.existsUnique_continuous_ringHom_intervalRing_of_windowU_subset` and its
  `V` analogue : the structure map extends uniquely to a continuous ring homomorphism into `B^I`
  from the coordinate ring `𝕎 O⟨T/s⟩` of any rational subset `R(T/s)` containing the window.

## References

* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, lecture notes, Arizona Winter School 2017,
  §3.1, for the windows and the rings `B^I`.
* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016, no. 8,
  2544–2567, for the rings `B^I`.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Lemma 8.1.
-/

public section

open scoped NNReal

namespace TauCeti.FarguesFontaine

open TauCeti.ValuationSpectrum _root_.WittVector TauCeti.WittVector TauCeti.Huber

variable {p : ℕ} [Fact p.Prime] {K O : Type*} [Field K] [CommRing O] [Algebra O K] [CharP O p]
  [PerfectRing O p] {v : Valuation K ℝ≥0} {ϖ : O} (hv : v.Integers O) (hϖ : ϖ ≠ 0)
  (hϖ' : v (algebraMap O K ϖ) < 1) {ρ₁ ρ₂ : ℝ≥0} (hρ₁ : ρ₁ ∈ Set.Ioo 0 1)
  (hρ₂ : ρ₂ ∈ Set.Ioo 0 1)

local notation "𝕎" => _root_.WittVector p

local notation "B^I" => IntervalRing p hv hϖ hϖ' hρ₁ hρ₂

/-- **`Spa(B^I, B^{I,+})` lies over `𝒴`**: pulling a point of `Spa(B^I, B^{I,+})` back along
`𝕎 O → B^I` gives a point of `𝒴 = D(p) ∩ D([ϖ])`, for the `(p, [ϖ])`-adic topology on `𝕎 O`. -/
theorem comap_algebraMap_intervalRing_mem_spaY [TopologicalSpace (𝕎 O)]
    (hI : IsAdic (Ideal.span {(p : 𝕎 O), teichmuller p ϖ})) {w : Spv B^I}
    (hw : w ∈ spa (powerBoundedSubring B^I)) :
    comap (algebraMap (𝕎 O) B^I) w ∈ spaY p ϖ := by
  -- a unit lies in no prime ideal, in particular not in the support of `w`
  have hunit {a : B^I} (ha : IsUnit a) : a ∉ w.supp := fun h ↦
    Ideal.IsPrime.ne_top inferInstance (Ideal.eq_top_of_isUnit_mem _ h ha)
  rw [mem_spaY_iff, supp_comap, Ideal.mem_comap, Ideal.mem_comap, map_natCast]
  refine ⟨comap_mem_spa (continuous_algebraMap_intervalRing p hv hϖ hϖ' hρ₁ hρ₂ hI)
    (fun a _ ↦ ?_) hw, hunit (isPseudoUniformizer_natCast_intervalRing p hv hϖ hϖ' hρ₁ hρ₂).isUnit,
    hunit (isPseudoUniformizer_teichmuller_intervalRing p hv hϖ hϖ' hρ₁ hρ₂).isUnit⟩
  rw [mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one_intervalRing,
    norm_algebraMap_intervalRing]
  exact_mod_cast max_le (gaussValuation_le_one hv hρ₁.2 a) (gaussValuation_le_one hv hρ₂.2 a)

/-- If `x = z y` in `B^I` with `z` in the unit ball, then `w(x) ≤ w(y)` at every point `w` of
`Spa(B^I, B^{I,+})`. -/
private theorem comap_vle_of_exists_norm_le_one {x y : 𝕎 O} {w : Spv B^I}
    (hw : w ∈ spa (powerBoundedSubring B^I))
    (h : ∃ z : B^I, ‖z‖ ≤ 1 ∧ algebraMap (𝕎 O) B^I x = z * algebraMap (𝕎 O) B^I y) :
    (comap (algebraMap (𝕎 O) B^I) w).toValuativeRel.vle x y := by
  obtain ⟨z, hz, hxz⟩ := h
  have hz' := ((mem_spa_iff _ w).mp hw).2 z (by
    rw [mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one_intervalRing]
    exact hz)
  rw [comap_vle, hxz, ← valuation_le_iff, map_mul]
  rw [← valuation_le_iff, map_one] at hz'
  exact mul_le_of_le_one_left' hz'

/-- **Lower radius bounds pass from the Gauss points to `Spa(B^I, B^{I,+})`**: if `q ≤ κ(η_{ρ₁})`
and `q ≤ κ(η_{ρ₂})`, then `q ≤ κ(w)` for the pullback of every point `w` of
`Spa(B^I, B^{I,+})` along `𝕎 O → B^I`. -/
theorem isRadiusLowerBound_comap_algebraMap_intervalRing {q : ℚ≥0}
    (h₁ : IsRadiusLowerBound p ϖ q (gaussPoint p hv ρ₁ hρ₁.2))
    (h₂ : IsRadiusLowerBound p ϖ q (gaussPoint p hv ρ₂ hρ₂.2)) {w : Spv B^I}
    (hw : w ∈ spa (powerBoundedSubring B^I)) :
    IsRadiusLowerBound p ϖ q (comap (algebraMap (𝕎 O) B^I) w) := by
  rw [isRadiusLowerBound_iff_of_eq_div q.den_ne_zero (NNRat.num_div_den q).symm,
    gaussPoint_vle_iff] at h₁ h₂
  rw [isRadiusLowerBound_iff_of_eq_div q.den_ne_zero (NNRat.num_div_den q).symm]
  refine comap_vle_of_exists_norm_le_one hv hϖ hϖ' hρ₁ hρ₂ hw
    (exists_norm_le_one_algebraMap_eq_mul_intervalRing p hv hϖ hϖ' hρ₁ hρ₂ ?_ h₁ h₂)
  rw [map_pow, map_natCast]
  exact (IntervalLocalization.isUnit_natCast p hv hϖ hϖ' hρ₁ hρ₂).pow _

/-- **Upper radius bounds pass from the Gauss points to `Spa(B^I, B^{I,+})`**: if `κ(η_{ρ₁}) ≤ q`
and `κ(η_{ρ₂}) ≤ q`, then `κ(w) ≤ q` for the pullback of every point `w` of
`Spa(B^I, B^{I,+})` along `𝕎 O → B^I`. -/
theorem isRadiusUpperBound_comap_algebraMap_intervalRing {q : ℚ≥0}
    (h₁ : IsRadiusUpperBound p ϖ q (gaussPoint p hv ρ₁ hρ₁.2))
    (h₂ : IsRadiusUpperBound p ϖ q (gaussPoint p hv ρ₂ hρ₂.2)) {w : Spv B^I}
    (hw : w ∈ spa (powerBoundedSubring B^I)) :
    IsRadiusUpperBound p ϖ q (comap (algebraMap (𝕎 O) B^I) w) := by
  rw [isRadiusUpperBound_iff_of_eq_div q.den_ne_zero (NNRat.num_div_den q).symm,
    gaussPoint_vle_iff] at h₁ h₂
  rw [isRadiusUpperBound_iff_of_eq_div q.den_ne_zero (NNRat.num_div_den q).symm]
  refine comap_vle_of_exists_norm_le_one hv hϖ hϖ' hρ₁ hρ₂ hw
    (exists_norm_le_one_algebraMap_eq_mul_intervalRing p hv hϖ hϖ' hρ₁ hρ₂ ?_ h₁ h₂)
  rw [map_pow]
  exact (IntervalLocalization.isUnit_algebraMap_teichmuller p hv hϖ hϖ' hρ₁ hρ₂).pow _

variable [TopologicalSpace (WittVector p O)]
  (hI : IsAdic (Ideal.span {(p : WittVector p O), teichmuller p ϖ}))

include hI in
/-- **`Spa(B^I, B^{I,+})` lies over the window `U_n` containing its Gauss points**: if
`η_{ρ₁}, η_{ρ₂} ∈ U_n`, then pulling a point of `Spa(B^I, B^{I,+})` back along `𝕎 O → B^I`
gives a point of `U_n`. -/
theorem comap_algebraMap_intervalRing_mem_windowU {n : ℤ}
    (h₁ : gaussPoint p hv ρ₁ hρ₁.2 ∈ windowU p ϖ n) (h₂ : gaussPoint p hv ρ₂ hρ₂.2 ∈ windowU p ϖ n)
    {w : Spv B^I} (hw : w ∈ spa (powerBoundedSubring B^I)) :
    comap (algebraMap (𝕎 O) B^I) w ∈ windowU p ϖ n := by
  rw [mem_windowU_iff] at h₁ h₂ ⊢
  exact ⟨comap_algebraMap_intervalRing_mem_spaY hv hϖ hϖ' hρ₁ hρ₂ hI hw,
    isRadiusLowerBound_comap_algebraMap_intervalRing hv hϖ hϖ' hρ₁ hρ₂ h₁.2.1 h₂.2.1 hw,
    isRadiusUpperBound_comap_algebraMap_intervalRing hv hϖ hϖ' hρ₁ hρ₂ h₁.2.2 h₂.2.2 hw⟩

include hI in
/-- **`Spa(B^I, B^{I,+})` lies over the window `V_n` containing its Gauss points**: if
`η_{ρ₁}, η_{ρ₂} ∈ V_n`, then pulling a point of `Spa(B^I, B^{I,+})` back along `𝕎 O → B^I`
gives a point of `V_n`. -/
theorem comap_algebraMap_intervalRing_mem_windowV {n : ℤ}
    (h₁ : gaussPoint p hv ρ₁ hρ₁.2 ∈ windowV p ϖ n) (h₂ : gaussPoint p hv ρ₂ hρ₂.2 ∈ windowV p ϖ n)
    {w : Spv B^I} (hw : w ∈ spa (powerBoundedSubring B^I)) :
    comap (algebraMap (𝕎 O) B^I) w ∈ windowV p ϖ n := by
  rw [mem_windowV_iff] at h₁ h₂ ⊢
  exact ⟨comap_algebraMap_intervalRing_mem_spaY hv hϖ hϖ' hρ₁ hρ₂ hI hw,
    isRadiusLowerBound_comap_algebraMap_intervalRing hv hϖ hϖ' hρ₁ hρ₂ h₁.2.1 h₂.2.1 hw,
    isRadiusUpperBound_comap_algebraMap_intervalRing hv hϖ hϖ' hρ₁ hρ₂ h₁.2.2 h₂.2.2 hw⟩

variable [IsTopologicalRing (WittVector p O)] (P : PairOfDefinition (WittVector p O))
  (T : Finset (WittVector p O)) (s : WittVector p O) (S : Type*) [CommRing S]
  [Algebra (WittVector p O) S] [IsLocalization.Away s S]
  (hden : PairOfDefinition.HasDenominatorPower P T s S)

include hI in
/-- **The coordinate ring of a rational subset containing `U_n` maps to `B^I`.** If the Gauss
points `η_{ρ₁}, η_{ρ₂}` lie in the window `U_n` and `U_n ⊆ R(T/s)`, then `𝕎 O → B^I` extends in
exactly one way to a continuous ring homomorphism `𝕎 O⟨T/s⟩ → B^I`. -/
theorem existsUnique_continuous_ringHom_intervalRing_of_windowU_subset {n : ℤ}
    (hU : windowU p ϖ n ⊆ rationalSubset ⊤ T s) (h₁ : gaussPoint p hv ρ₁ hρ₁.2 ∈ windowU p ϖ n)
    (h₂ : gaussPoint p hv ρ₂ hρ₂.2 ∈ windowU p ϖ n) :
    letI := PairOfDefinition.locUniformSpace P T s S hden
    letI := PairOfDefinition.isUniformAddGroup_locUniformSpace P T s S hden
    letI := PairOfDefinition.isTopologicalRing_locUniformSpace P T s S hden
    ∃! g : UniformSpace.Completion S →+* B^I,
      Continuous g ∧ g.comp (PairOfDefinition.toCompletionLoc P T s S hden) =
        algebraMap (𝕎 O) B^I :=
  existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset P ⊤ T s S hden
    (powerBoundedSubring B^I)
    (Pair.powerBounded_plus (A := B^I) ▸ (Pair.powerBounded B^I).isRingOfIntegralElements)
    (continuous_algebraMap_intervalRing p hv hϖ hϖ' hρ₁ hρ₂ hI).continuousAt
    fun _ hw ↦ hU (comap_algebraMap_intervalRing_mem_windowU hv hϖ hϖ' hρ₁ hρ₂ hI h₁ h₂ hw)

include hI in
/-- **The coordinate ring of a rational subset containing `V_n` maps to `B^I`.** If the Gauss
points `η_{ρ₁}, η_{ρ₂}` lie in the window `V_n` and `V_n ⊆ R(T/s)`, then `𝕎 O → B^I` extends in
exactly one way to a continuous ring homomorphism `𝕎 O⟨T/s⟩ → B^I`. -/
theorem existsUnique_continuous_ringHom_intervalRing_of_windowV_subset {n : ℤ}
    (hV : windowV p ϖ n ⊆ rationalSubset ⊤ T s) (h₁ : gaussPoint p hv ρ₁ hρ₁.2 ∈ windowV p ϖ n)
    (h₂ : gaussPoint p hv ρ₂ hρ₂.2 ∈ windowV p ϖ n) :
    letI := PairOfDefinition.locUniformSpace P T s S hden
    letI := PairOfDefinition.isUniformAddGroup_locUniformSpace P T s S hden
    letI := PairOfDefinition.isTopologicalRing_locUniformSpace P T s S hden
    ∃! g : UniformSpace.Completion S →+* B^I,
      Continuous g ∧ g.comp (PairOfDefinition.toCompletionLoc P T s S hden) =
        algebraMap (𝕎 O) B^I :=
  existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset P ⊤ T s S hden
    (powerBoundedSubring B^I)
    (Pair.powerBounded_plus (A := B^I) ▸ (Pair.powerBounded B^I).isRingOfIntegralElements)
    (continuous_algebraMap_intervalRing p hv hϖ hϖ' hρ₁ hρ₂ hI).continuousAt
    fun _ hw ↦ hV (comap_algebraMap_intervalRing_mem_windowV hv hϖ hϖ' hρ₁ hρ₂ hI h₁ h₂ hw)

end TauCeti.FarguesFontaine
