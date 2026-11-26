/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.FundamentalChain
public import TauCeti.Geometry.Manifold.Morse.Boundary.Pair.Sign

/-!
# Signed pair counts at the critical points of index `0` and of top index

Let `f₀` and `f₁` be Morse functions on a compact boundaryless manifold `M` of dimension `n`, with
pseudo-gradients `X₀` and `X₁` adapted to them, and orientation data
`𝔬₀ : TauCeti.MorseOrientation f₀ X₀` and `𝔬₁ : TauCeti.MorseOrientation f₁ X₁`. The signed pair
map `TauCeti.IsAdaptedPseudoGradient.signedPairMap` counts the points of the rigid intersections
`W^u_{X₀}(p) ∩ W^s_{X₁}(q)`, `ind p = ind q`, with the signs
`TauCeti.IsAdaptedPseudoGradient.pairSign`. At the two extreme indices these signs need no
transversality argument, because one of the two manifolds is a single point.

* **Index `0`.** The unstable manifold of a critical point `p` of index `0` is `{p}`, and the
  spaces of coordinates of negative weight at `p` and at `q` are zero. The sign of a point is then
  the product of the augmentation signs `TauCeti.MorseOrientation.augmentationSign` of `p` and of
  `q` (`TauCeti.IsAdaptedPseudoGradient.pairSign_of_morseIndex_eq_zero`), and the coefficient of
  `q` in the image of `p` is this product when `p ∈ W^s_{X₁}(q)`, and `0` otherwise
  (`TauCeti.IsAdaptedPseudoGradient.signedPairCoeff_of_morseIndex_eq_zero`).
* **Index `n`.** The stable manifold of a critical point `q` of index `n` is `{q}`
  (`TauCeti.IsAdaptedPseudoGradient.stableSet_eq_singleton_of_manifoldMorseIndex_eq_finrank`). For
  an orientation `oM` of `M`, the comparison map at `q` is the unstable frame of `X₀` at `q`
  followed by the inverse of the unstable frame of `X₁` at `q`, and its sign is the product of the
  fundamental signs `TauCeti.IsAdaptedPseudoGradient.fundamentalSign` of `p` and of `q`
  (`TauCeti.IsAdaptedPseudoGradient.pairSign_of_morseIndex_eq_finrank`): both compare the
  orientation of an unstable manifold with `oM`, and the unstable frame of `X₀` compares them in the
  same way at `q` as at `p`
  (`TauCeti.IsAdaptedPseudoGradient.map_unstableFrame_eq_orientationAt_iff`).
  So the coefficient of `q` in the image of `p` is this product when `q ∈ W^u_{X₀}(p)`, and `0`
  otherwise (`TauCeti.IsAdaptedPseudoGradient.signedPairCoeff_of_morseIndex_eq_finrank`).

For a Morse–Smale pair `(X₀, X₁)`, every point lies on exactly one stable manifold of `X₁` and on
exactly one unstable manifold of `X₀`, and the index cannot rise from a critical point of `f₀` to
one of `f₁` along `W^u_{X₀}(p) ∩ W^s_{X₁}(q)`. So a critical point `p` of index `0` lies on the
stable manifold of exactly one critical point of `f₁`, which has index `0`, and dually a critical
point `q` of index `n` lies on the unstable manifold of exactly one critical point of `f₀`, which
has index `n`. Consequently, over every ring of coefficients:

* the signed pair map commutes with the augmentations
  `TauCeti.MorseOrientation.signedMorseAugmentation` of `f₀` and `f₁`
  (`IsMorseSmalePair.signedMorseAugmentation_comp_signedPairMap`);
* for every orientation of `M`, the signed pair map sends the fundamental chain
  `TauCeti.IsAdaptedPseudoGradient.signedMorseFundamentalChain` of `f₀` to that of `f₁`
  (`IsMorseSmalePair.signedPairMap_signedMorseFundamentalChain`).

The integral continuation map along a diffeomorphism `Φ` is the signed pair map of `(X₀, Φ^* X₁)`
followed by a relabelling of the critical points
(`TauCeti.IsAdaptedPseudoGradient.signedContinuationMap_eq_comp_signedPairMap`), so the first
consequence makes the integral continuation maps commute with the augmentations
(`TauCeti.Geometry.Manifold.Morse.Boundary.Continuation.Signed`). On a manifold of dimension one,
every critical point of a Morse function has index `0` or `1`, so there the two formulas give every
coefficient of the signed pair maps.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `pairSign_of_morseIndex_eq_zero`, `signedPairCoeff_of_morseIndex_eq_zero`: the signs and the
  coefficients at critical points of index `0`.
* `pairSign_of_morseIndex_eq_finrank`, `signedPairCoeff_of_morseIndex_eq_finrank`: the signs and
  the coefficients at critical points of index `n`.
* `IsMorseSmalePair.finsum_signedPairCoeff_mul_augmentationSign`,
  `IsMorseSmalePair.signedMorseAugmentation_comp_signedPairMap`: the signed pair map commutes with
  the augmentations.
* `IsMorseSmalePair.finsum_fundamentalSign_mul_signedPairCoeff`,
  `IsMorseSmalePair.signedPairMap_signedMorseFundamentalChain`: the signed pair map preserves the
  fundamental chains.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations of the descending manifolds and signed
  counts) and §4.1 (continuation maps over `ℤ`).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapters 4 and 6 (the Morse complex with integer coefficients, its homology in degree `0`, and
  invariance by continuation).
-/

public section

open Function Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f₀ f₁ : M → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  (𝔬₀ : MorseOrientation f₀ X₀) (𝔬₁ : MorseOrientation f₁ X₁)

/-! ### Critical points of index `0` -/

/-- **The sign of a point at index `0`.** Between critical points `p` of `f₀` and `q` of `f₁` of
index `0`, the sign of every point is the product of the augmentation signs of `p` and of `q`: the
comparison map is the map between the zero spaces of coordinates of negative weight. -/
theorem pairSign_of_morseIndex_eq_zero {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁} (hp : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = 0)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q) (y : M) :
    hX₀.pairSign hX₁ (𝔬₀.chart p) (𝔬₁.chart q) (𝔬₀.orientation p) (𝔬₁.orientation q) hpq y =
      𝔬₀.augmentationSign p * 𝔬₁.augmentationSign q := by
  rw [pairSign_def, 𝔬₀.augmentationSign_of_morseIndex_eq_zero hp,
    𝔬₁.augmentationSign_of_morseIndex_eq_zero (hpq ▸ hp)]
  set bq := Module.finBasisOfFinrankEq ℝ _ (𝔬₁.chart q).finrank_negativeWeight_fun
  -- The bases are indexed by `Fin 0`, so the comparison map sends one to the other.
  rw [Orientation.linearMapSign_eq_signBasis_mul_signBasis _ _
    (Module.finBasisOfFinrankEq ℝ _ (𝔬₀.chart p).finrank_negativeWeight_fun)
    (bq.reindex (finCongr hpq.symm)) fun i ↦ (finCongr hp i).elim0,
    Orientation.signBasis_reindex, Units.val_mul]

open scoped Classical in
/-- **The coefficients at index `0`.** For a Morse function `f₀` and a critical point `p` of
index `0`, the coefficient of a critical point `q` of `f₁` in the image of `p` is the product of
the augmentation signs of `p` and of `q` when `p` lies on the stable manifold of `q`, and `0`
otherwise: the unstable manifold of `p` is `{p}`. -/
theorem signedPairCoeff_of_morseIndex_eq_zero (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    {p : criticalPoints 𝓘(ℝ, E) f₀} (q : criticalPoints 𝓘(ℝ, E) f₁)
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = 0) :
    hX₀.signedPairCoeff hX₁ 𝔬₀ 𝔬₁ p q =
      𝔬₀.augmentationSign p * 𝔬₁.augmentationSign q *
        if (p : M) ∈ hX₁.flow.stableSet q then 1 else 0 := by
  by_cases hq : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = 0
  · have hpq := hp.trans hq.symm
    rw [signedPairCoeff_of_morseIndex_eq hpq, signedPairCount_def,
      hX₀.unstableSet_eq_singleton_of_manifoldMorseIndex_eq_zero hf₀
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.property) hp]
    split_ifs with hs
    · rw [singleton_inter_of_mem hs, finsum_mem_singleton,
        pairSign_of_morseIndex_eq_zero 𝔬₀ 𝔬₁ hp hpq, mul_one]
    · rw [singleton_inter_eq_empty.2 hs, finsum_mem_empty, mul_zero]
  · rw [signedPairCoeff_eq_zero_of_morseIndex_ne (by omega),
      𝔬₁.augmentationSign_of_morseIndex_ne_zero hq, mul_zero, zero_mul]

/-! ### Critical points of top index -/

variable (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E)))

/-- At a critical point `q` of `f₁` where the unstable frame of `X₁` is bijective (one of index
`n`), the comparison map is the unstable frame of `X₀` at `q` followed by the inverse of the
unstable frame of `X₁` at `q`: at `q` the normal coordinates of `W^s_{X₁}(q)` invert the unstable
frame of `X₁`. -/
private theorem ofBijective_trans_symm_apply_eq_pairComparison {p : M} (φp : MorseChart E f₀ p)
    {q : criticalPoints 𝓘(ℝ, E) f₁} (h₀ : Bijective (hX₀.unstableFrame φp q))
    (h₁ : Bijective (hX₁.unstableFrame (𝔬₁.chart q) q))
    (v : {i // φp.weight i < 0} → ℝ) :
    ((LinearEquiv.ofBijective (hX₀.unstableFrame φp q).toLinearMap h₀).trans
        (LinearEquiv.ofBijective (hX₁.unstableFrame (𝔬₁.chart q) q).toLinearMap h₁).symm) v =
      hX₀.pairComparison hX₁ φp (𝔬₁.chart q) q v := by
  set e₁ := LinearEquiv.ofBijective (hX₁.unstableFrame (𝔬₁.chart q) q).toLinearMap h₁ with he₁
  have hv : hX₁.unstableFrame (𝔬₁.chart q) q (e₁.symm (hX₀.unstableFrame φp q v)) =
      hX₀.unstableFrame φp q v := by
    simpa only [he₁, LinearEquiv.ofBijective_apply, ContinuousLinearMap.coe_coe] using
      e₁.apply_symm_apply (hX₀.unstableFrame φp q v)
  rw [pairComparison_apply, LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply,
    ContinuousLinearMap.coe_coe]
  conv_rhs => rw [← hv]
  rw [hX₁.stableNormal_unstableFrame_self (𝔬₁.coord_mfderiv_chart q)]

/-- **The sign of a point at index `n`.** Let `p` and `q` be critical points of index `n = dim M`
of `f₀` and of `f₁`, with `f₀` Morse, such that `q` lies on the unstable manifold of `p`. For an
orientation `oM` of `M`, the sign of `q` as a point of `W^u_{X₀}(p) ∩ W^s_{X₁}(q)` is the product
of the fundamental signs of `p` and of `q`. -/
theorem pairSign_of_morseIndex_eq_finrank (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    {p : criticalPoints 𝓘(ℝ, E) f₀} {q : criticalPoints 𝓘(ℝ, E) f₁}
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = finrank ℝ E)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q)
    (hqp : (q : M) ∈ hX₀.flow.unstableSet p) :
    hX₀.pairSign hX₁ (𝔬₀.chart p) (𝔬₁.chart q) (𝔬₀.orientation p) (𝔬₁.orientation q) hpq q =
      hX₀.fundamentalSign 𝔬₀ oM p * hX₁.fundamentalSign 𝔬₁ oM q := by
  classical
  have hq : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = finrank ℝ E := hpq ▸ hp
  have hφp := 𝔬₀.coord_mfderiv_chart p
  obtain ⟨T, hT⟩ := (hX₀.eventually_mem_linearBackwardTimes hφp hf₀ hqp).exists
  have h₀ : Bijective (hX₀.unstableFrame (𝔬₀.chart p) q) := bijective_unstableFrame hφp hp hT
  have h₁ : Bijective (hX₁.unstableFrame (𝔬₁.chart q) q) := bijective_unstableFrame_self 𝔬₁ hq
  set e₀ := LinearEquiv.ofBijective (hX₀.unstableFrame (𝔬₀.chart p) q).toLinearMap h₀
  set e₁ := LinearEquiv.ofBijective (hX₁.unstableFrame (𝔬₁.chart q) q).toLinearMap h₁ with he₁
  have hcomp := ofBijective_trans_symm_apply_eq_pairComparison 𝔬₁ (𝔬₀.chart p) h₀ h₁
  have hbij : Bijective (hX₀.pairComparison hX₁ (𝔬₀.chart p) (𝔬₁.chart q) q).toLinearMap := by
    rw [ContinuousLinearMap.coe_coe, ← funext hcomp]
    exact (e₀.trans e₁.symm).bijective
  have he : LinearEquiv.ofBijective _ hbij = e₀.trans e₁.symm :=
    LinearEquiv.ext fun v ↦ (hcomp v).symm
  -- Compare both orientations in `Fin n`, where the fundamental signs live.
  set op := (𝔬₀.orientation p).reindex ℝ _ (finCongr hp)
  set oq := (𝔬₁.orientation q).reindex ℝ _ (finCongr hq) with hoq
  have hcardT : Fintype.card (Fin (finrank ℝ E)) = finrank ℝ (TangentSpace 𝓘(ℝ, E) (q : M)) :=
    Fintype.card_fin _
  have hcardV : Fintype.card (Fin (finrank ℝ E)) =
      finrank ℝ ({i // (𝔬₁.chart q).weight i < 0} → ℝ) := by
    rw [Fintype.card_fin, (𝔬₁.chart q).finrank_negativeWeight_fun, hq]
  have key := Orientation.ite_map_mul_ite_map_trans e₀ e₁.symm op (oT := oM.orientationAt q)
    (τ := oq) hcardT hcardV
  -- The first factor is the fundamental sign of `p`, read at the point `q` of `W^u_{X₀}(p)`.
  have h0 : Orientation.map _ e₀ op = oM.orientationAt q ↔
      hX₀.unstableOrientation 𝔬₀ hp = oM.orientationAt p := by
    rw [unstableOrientation_def]
    exact map_unstableFrame_eq_orientationAt_iff hf₀ hφp
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.property) oM op hqp h₀
      (bijective_unstableFrame_self 𝔬₀ hp)
  -- The last one is the fundamental sign of `q`.
  have h1 : Orientation.map _ e₁.symm (oM.orientationAt q) = oq ↔
      hX₁.unstableOrientation 𝔬₁ hq = oM.orientationAt q := by
    rw [unstableOrientation_def, ← he₁, ← hoq]
    constructor
    · rintro hτ
      rw [← hτ, Orientation.map_map_symm]
    · rintro hτ
      rw [← hτ, Orientation.map_symm_map]
  rw [if_congr h0 rfl rfl, if_congr h1 rfl rfl, ← fundamentalSign_of_morseIndex_eq hp,
    ← fundamentalSign_of_morseIndex_eq hq] at key
  rw [pairSign_def, ← Orientation.linearMapSign_reindex (finCongr hp),
    Orientation.reindex_finCongr_reindex_finCongr, Orientation.linearMapSign_of_bijective hbij, he]
  -- Multiply `key` by the fundamental sign of `p`, which squares to `1`.
  have hsq := fundamentalSign_mul_self (R := ℤ) (hX := hX₀) (𝔬 := 𝔬₀) (oM := oM) hp
  rw [Int.cast_id] at hsq
  rw [← key, ← mul_assoc, hsq, one_mul]

open scoped Classical in
/-- **The coefficients at index `n`.** For Morse functions `f₀` and `f₁`, an orientation `oM` of
`M` and a critical point `q` of `f₁` of index `n = dim M`, the coefficient of `q` in the image of a
critical point `p` of `f₀` is the product of the fundamental signs of `p` and of `q` when `q` lies
on the unstable manifold of `p`, and `0` otherwise: the stable manifold of `q` is `{q}`. -/
theorem signedPairCoeff_of_morseIndex_eq_finrank (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (p : criticalPoints 𝓘(ℝ, E) f₀) {q : criticalPoints 𝓘(ℝ, E) f₁}
    (hq : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = finrank ℝ E) :
    hX₀.signedPairCoeff hX₁ 𝔬₀ 𝔬₁ p q =
      hX₀.fundamentalSign 𝔬₀ oM p * hX₁.fundamentalSign 𝔬₁ oM q *
        if (q : M) ∈ hX₀.flow.unstableSet p then 1 else 0 := by
  by_cases hp : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = finrank ℝ E
  · have hpq := hp.trans hq.symm
    rw [signedPairCoeff_of_morseIndex_eq hpq, signedPairCount_def,
      hX₁.stableSet_eq_singleton_of_manifoldMorseIndex_eq_finrank hf₁
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 q.property) hq]
    split_ifs with hs
    · rw [inter_singleton_of_mem hs, finsum_mem_singleton,
        pairSign_of_morseIndex_eq_finrank 𝔬₀ 𝔬₁ oM hf₀ hp hpq hs, mul_one]
    · rw [inter_singleton_eq_empty.2 hs, finsum_mem_empty, mul_zero]
  · rw [signedPairCoeff_eq_zero_of_morseIndex_ne (by omega),
      fundamentalSign_of_morseIndex_ne hp, zero_mul, zero_mul]

/-! ### Augmentations and fundamental chains -/

namespace IsMorseSmalePair

variable (h : IsMorseSmalePair hX₀ hX₁) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
include h hf₀

/-- **The signed pair map commutes with the augmentations**, at the level of coefficients: for a
Morse–Smale pair, the coefficients of the image of a critical point `p` of `f₀`, weighted by the
augmentation signs of `f₁`, add up to the augmentation sign of `p`. -/
theorem finsum_signedPairCoeff_mul_augmentationSign (p : criticalPoints 𝓘(ℝ, E) f₀) :
    ∑ᶠ q, hX₀.signedPairCoeff hX₁ 𝔬₀ 𝔬₁ p q * 𝔬₁.augmentationSign q = 𝔬₀.augmentationSign p := by
  classical
  by_cases hp : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = 0
  · -- `p` lies on the stable manifold of a single critical point `q₀` of `f₁`, of index `0`.
    obtain ⟨c, hc, hpc⟩ := hX₁.exists_mem_stableSet (p : M)
    set q₀ : criticalPoints 𝓘(ℝ, E) f₁ := ⟨c, mem_criticalPoints_iff_mfderiv_eq_zero.2 hc⟩
    have hq₀ : manifoldMorseIndex 𝓘(ℝ, E) f₁ q₀ = 0 := Nat.le_zero.1 (hp ▸
      h.manifoldMorseIndex_le hf₀ ⟨p, hX₀.mem_unstableSet_self p.property, hpc⟩)
    rw [finsum_eq_single _ q₀ fun q hq ↦ ?_]
    · rw [signedPairCoeff_of_morseIndex_eq_zero 𝔬₀ 𝔬₁ hf₀ q₀ hp, ite_eq_left hpc]
      have hsq := 𝔬₁.augmentationSign_mul_self (R := ℤ) hq₀
      rw [Int.cast_id] at hsq
      rw [mul_one, mul_assoc, hsq, mul_one]
    · -- The stable manifolds of distinct critical points are disjoint.
      have hpq : (p : M) ∉ hX₁.flow.stableSet q := fun hpq ↦
        disjoint_left.1 (Flow.disjoint_stableSet (Subtype.coe_injective.ne hq)) hpq hpc
      rw [signedPairCoeff_of_morseIndex_eq_zero 𝔬₀ 𝔬₁ hf₀ q hp, ite_eq_right hpq, mul_zero,
        zero_mul]
  · -- Nonzero coefficients join `p` to critical points of the same positive index.
    rw [𝔬₀.augmentationSign_of_morseIndex_ne_zero hp]
    refine finsum_eq_zero_of_forall_eq_zero fun q ↦ ?_
    by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q
    · rw [𝔬₁.augmentationSign_of_morseIndex_ne_zero (hpq ▸ hp), mul_zero]
    · rw [signedPairCoeff_eq_zero_of_morseIndex_ne hpq, zero_mul]

include hf₁ in
/-- **The signed pair map commutes with the augmentations.** For a Morse–Smale pair of
pseudo-gradients adapted to Morse functions, `ε₁ ∘ P = ε₀` for the augmentations `ε₀` and `ε₁` of
the Morse chains of `f₀` and `f₁`, with coefficients in any ring. -/
theorem signedMorseAugmentation_comp_signedPairMap (R : Type*) [Ring R] :
    𝔬₁.signedMorseAugmentation R ∘ₗ hX₀.signedPairMap hX₁ 𝔬₀ 𝔬₁ hf₁ R =
      𝔬₀.signedMorseAugmentation R := by
  classical
  have := hf₁.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₁)
  refine Finsupp.lhom_ext fun p a ↦ ?_
  rw [LinearMap.comp_apply, MorseOrientation.signedMorseAugmentation_apply,
    Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _, MorseOrientation.signedMorseAugmentation_single,
    ← h.finsum_signedPairCoeff_mul_augmentationSign 𝔬₀ 𝔬₁ hf₀ p, finsum_eq_sum_of_fintype]
  simp only [signedPairMap_single_apply, Int.cast_sum, Int.cast_mul, Finset.mul_sum, mul_assoc]

include hf₁

/-- **The signed pair map preserves the fundamental chains**, at the level of coefficients: for a
Morse–Smale pair and an orientation `oM` of `M`, the coefficients of a critical point `q` of `f₁`
in the images of the critical points of `f₀`, weighted by the fundamental signs of `f₀`, add up to
the fundamental sign of `q`. -/
theorem finsum_fundamentalSign_mul_signedPairCoeff (q : criticalPoints 𝓘(ℝ, E) f₁) :
    ∑ᶠ p, hX₀.fundamentalSign 𝔬₀ oM p * hX₀.signedPairCoeff hX₁ 𝔬₀ 𝔬₁ p q =
      hX₁.fundamentalSign 𝔬₁ oM q := by
  classical
  by_cases hq : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = finrank ℝ E
  · -- `q` lies on the unstable manifold of a single critical point `p₀` of `f₀`, of index `n`.
    obtain ⟨c, hc, hqc⟩ := hX₀.exists_mem_unstableSet (q : M)
    set p₀ : criticalPoints 𝓘(ℝ, E) f₀ := ⟨c, mem_criticalPoints_iff_mfderiv_eq_zero.2 hc⟩
    have hp₀ : manifoldMorseIndex 𝓘(ℝ, E) f₀ p₀ = finrank ℝ E :=
      le_antisymm manifoldMorseIndex_le_finrank (hq ▸
        h.manifoldMorseIndex_le hf₀ ⟨q, hqc, hX₁.mem_stableSet_self q.property⟩)
    rw [finsum_eq_single _ p₀ fun p hp ↦ ?_]
    · rw [signedPairCoeff_of_morseIndex_eq_finrank 𝔬₀ 𝔬₁ oM hf₀ hf₁ p₀ hq, ite_eq_left hqc]
      have hsq := fundamentalSign_mul_self (R := ℤ) (hX := hX₀) (𝔬 := 𝔬₀) (oM := oM) hp₀
      rw [Int.cast_id] at hsq
      rw [mul_one, ← mul_assoc, hsq, one_mul]
    · -- The unstable manifolds of distinct critical points are disjoint.
      have hqp : (q : M) ∉ hX₀.flow.unstableSet p := fun hqp ↦
        disjoint_left.1 (Flow.disjoint_unstableSet (Subtype.coe_injective.ne hp)) hqp hqc
      rw [signedPairCoeff_of_morseIndex_eq_finrank 𝔬₀ 𝔬₁ oM hf₀ hf₁ p hq, ite_eq_right hqp,
        mul_zero, mul_zero]
  · -- Nonzero coefficients join `q` to critical points of the same index, less than `n`.
    rw [fundamentalSign_of_morseIndex_ne hq]
    refine finsum_eq_zero_of_forall_eq_zero fun p ↦ ?_
    by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q
    · rw [fundamentalSign_of_morseIndex_ne (hpq ▸ hq), zero_mul]
    · rw [signedPairCoeff_eq_zero_of_morseIndex_ne hpq, mul_zero]

/-- **The signed pair map preserves the fundamental chains.** For a Morse–Smale pair of
pseudo-gradients adapted to Morse functions and an orientation `oM` of `M`, the signed pair map
sends the fundamental chain `[M]` of `f₀` to the fundamental chain of `f₁`, with coefficients in any
ring. -/
theorem signedPairMap_signedMorseFundamentalChain (R : Type*) [Ring R] :
    hX₀.signedPairMap hX₁ 𝔬₀ 𝔬₁ hf₁ R (hX₀.signedMorseFundamentalChain 𝔬₀ oM hf₀ R) =
      hX₁.signedMorseFundamentalChain 𝔬₁ oM hf₁ R := by
  classical
  have := hf₀.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₀)
  ext q
  rw [signedPairMap_apply, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _,
    signedMorseFundamentalChain_apply,
    ← h.finsum_fundamentalSign_mul_signedPairCoeff 𝔬₀ 𝔬₁ oM hf₀ hf₁ q, finsum_eq_sum_of_fintype]
  simp only [signedMorseFundamentalChain_apply, Int.cast_sum, Int.cast_mul]

end IsMorseSmalePair

end IsAdaptedPseudoGradient

end TauCeti
