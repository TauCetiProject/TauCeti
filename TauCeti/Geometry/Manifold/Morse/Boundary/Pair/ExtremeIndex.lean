/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.FundamentalChain
public import TauCeti.Geometry.Manifold.Morse.Boundary.Pair.Sign
public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedAugmentation

/-!
# Signed pair counts at critical points of extreme index

Let `X₀` and `X₁` be pseudo-gradients adapted to Morse functions `f₀` and `f₁` on a compact
boundaryless manifold `M` of dimension `n`, with orientation data `𝔬₀` and `𝔬₁`
(`TauCeti.MorseOrientation`). For critical points `p` of `f₀` and `q` of `f₁` of the same index,
the coefficient of `q` in the image of `p` under the signed pair map
(`TauCeti.IsAdaptedPseudoGradient.signedPairCoeff`) counts the points of
`W^u_{X₀}(p) ∩ W^s_{X₁}(q)` with signs. At the two extreme indices this intersection has at most one
point, and its sign depends only on the orientation data, through the augmentation and fundamental
signs of the integral Morse complex.

* **Index `0`.** The unstable manifold of `p` is the point `p`
  (`TauCeti.IsAdaptedPseudoGradient.unstableSet_eq_singleton_of_manifoldMorseIndex_eq_zero`), and
  the comparison map at `p` is the map between zero spaces. So the coefficient is the product
  `𝔬₀.augmentationSign p * 𝔬₁.augmentationSign q` of the augmentation signs when `p` lies in
  `W^s_{X₁}(q)`, and `0` otherwise
  (`TauCeti.IsAdaptedPseudoGradient.signedPairCoeff_of_morseIndex_eq_zero`).
* **Index `n`.** The stable manifold of `q` is the point `q`
  (`TauCeti.IsAdaptedPseudoGradient.stableSet_eq_singleton_of_manifoldMorseIndex_eq_finrank`). At
  `q` the normal coordinates of `W^s_{X₁}(q)` invert the unstable frame of `X₁`, so the comparison
  map is the unstable frame of `X₀` followed by the inverse of that of `X₁`. For an orientation
  `oM` of `M`, the unstable frame of `X₀` compares the orientation of `W^u_{X₀}(p)` with `oM` at
  `q` as it does at `p`
  (`TauCeti.IsAdaptedPseudoGradient.map_unstableFrame_eq_orientationAt_iff`). So the coefficient is
  the product of the fundamental signs of `p` and `q` for `oM` when `q` lies in `W^u_{X₀}(p)`, and
  `0` otherwise (`TauCeti.IsAdaptedPseudoGradient.signedPairCoeff_of_morseIndex_eq_finrank`).

Neither formula needs the pair to be Morse–Smale. On a manifold of dimension `1` every critical
point has index `0` or `1`, so the two formulas determine the whole signed pair map; in
`TauCeti.Geometry.Manifold.Morse.Boundary.Continuation.ExtremeIndex` they are applied to the
integral continuation maps.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `pairSign_of_morseIndex_eq_zero`: between critical points of index `0`, the sign of a point is the
  product of the signs of the two orientations relative to the empty bases.
* `signedPairCoeff_of_morseIndex_eq_zero`: the coefficients between critical points of index `0`.
* `pairSign_of_morseIndex_eq_finrank`: between critical points of top index, the sign of the point
  `q` is the product of the fundamental signs.
* `signedPairCoeff_of_morseIndex_eq_finrank`: the coefficients between critical points of top
  index.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations and signed counts) and §4.1 (continuation
  maps over `ℤ`).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapters 4 and 6.
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

section IndexZero

variable {p q : M} {φp : MorseChart E f₀ p} {φq : MorseChart E f₁ q}

/-- **The sign of a point between critical points of index `0`.** When `p` and `q` have index `0`,
the comparison map at any point `y` is the map between zero spaces, and the sign of `y` is the
product of the signs of `op` and `oq` relative to the empty bases. -/
theorem pairSign_of_morseIndex_eq_zero (hp : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = 0)
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₀ p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f₁ q)))
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q) (y : M) :
    hX₀.pairSign hX₁ φp φq op oq hpq y =
      (op.signBasis (Module.finBasisOfFinrankEq ℝ _ φp.finrank_negativeWeight_fun) : ℤ) *
        (oq.signBasis (Module.finBasisOfFinrankEq ℝ _ φq.finrank_negativeWeight_fun) : ℤ) := by
  classical
  set bp := Module.finBasisOfFinrankEq ℝ _ φp.finrank_negativeWeight_fun
  set bq := Module.finBasisOfFinrankEq ℝ _ φq.finrank_negativeWeight_fun
  have hsp : Subsingleton ({i // φp.weight i < 0} → ℝ) :=
    Module.finrank_zero_iff.1 (φp.finrank_negativeWeight_fun.trans hp)
  have hsq : Subsingleton ({i // φq.weight i < 0} → ℝ) :=
    Module.finrank_zero_iff.1 (φq.finrank_negativeWeight_fun.trans (hpq ▸ hp))
  have hC : Bijective (hX₀.pairComparison hX₁ φp φq y) :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun w ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  set L := LinearEquiv.ofBijective (hX₀.pairComparison hX₁ φp φq y).toLinearMap hC
  -- Bases indexed by an empty type agree, so `L` carries the orientation of `bp` to that of `bq`.
  have hb : bp.map L = bq.reindex (finCongr hpq.symm) :=
    Module.Basis.eq_of_apply_eq fun i ↦ absurd i.isLt (by omega)
  have hL : Orientation.map _ L bp.orientation =
      Orientation.reindex ℝ _ (finCongr hpq.symm) bq.orientation := by
    rw [← Module.Basis.orientation_map, hb, Module.Basis.orientation_reindex]
  rw [pairSign_of_bijective hC]
  rcases bp.orientation_eq_or_eq_neg op with rfl | rfl <;>
    rcases bq.orientation_eq_or_eq_neg oq with rfl | rfl <;>
    simp [L, hL, Orientation.reindex_neg, Module.Ray.ne_neg_self,
      (Module.Ray.ne_neg_self _).symm]

end IndexZero

/-- At a critical point `q` where the unstable frame of `X₁` is bijective, the normal coordinates
of `W^s_{X₁}(q)` invert it, so the comparison map at `q` is the unstable frame of `X₀` followed by
the inverse of the unstable frame of `X₁`. -/
private theorem pairComparison_self_eq {p q : M} {φp : MorseChart E f₀ p}
    {φq : MorseChart E f₁ q}
    (hφq : ∀ y ∈ φq.toChart.source, φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X₁ y)) =
      fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
    (hFp : Bijective (hX₀.unstableFrame φp q)) (hFq : Bijective (hX₁.unstableFrame φq q))
    (v : {i // φp.weight i < 0} → ℝ) :
    hX₀.pairComparison hX₁ φp φq q v =
      ((LinearEquiv.ofBijective (hX₀.unstableFrame φp q).toLinearMap hFp).trans
        (LinearEquiv.ofBijective (hX₁.unstableFrame φq q).toLinearMap hFq).symm) v := by
  set 𝓕p := LinearEquiv.ofBijective (hX₀.unstableFrame φp q).toLinearMap hFp
  set 𝓕q := LinearEquiv.ofBijective (hX₁.unstableFrame φq q).toLinearMap hFq
  have h := hX₁.stableNormal_unstableFrame_self hφq (𝓕q.symm (𝓕p v))
  have hq' : hX₁.unstableFrame φq q (𝓕q.symm (𝓕p v)) = 𝓕p v := by
    rw [← ContinuousLinearMap.coe_coe, ← LinearEquiv.ofBijective_apply _ (hf := hFq),
      𝓕q.apply_symm_apply]
  rw [hq'] at h
  rw [pairComparison_apply, LinearEquiv.trans_apply, ← h, LinearEquiv.ofBijective_apply,
    ContinuousLinearMap.coe_coe]

variable (𝔬₀ : MorseOrientation f₀ X₀) (𝔬₁ : MorseOrientation f₁ X₁)

open scoped Classical in
/-- **The signed pair coefficients between critical points of index `0`.** The unstable manifold of
a critical point `p` of index `0` is the point `p` itself, so it meets the stable manifold of a
critical point `q` of index `0` exactly when `p` flows to `q`, and then the coefficient of `q` in
the image of `p` is the product of the augmentation signs of `p` and `q`. -/
theorem signedPairCoeff_of_morseIndex_eq_zero (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    {p : criticalPoints 𝓘(ℝ, E) f₀} {q : criticalPoints 𝓘(ℝ, E) f₁}
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = 0) (hq : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = 0) :
    hX₀.signedPairCoeff hX₁ 𝔬₀ 𝔬₁ p q =
      if (p : M) ∈ hX₁.flow.stableSet q then 𝔬₀.augmentationSign p * 𝔬₁.augmentationSign q
      else 0 := by
  rw [signedPairCoeff_of_morseIndex_eq (hp.trans hq.symm), signedPairCount_def,
    hX₀.unstableSet_eq_singleton_of_manifoldMorseIndex_eq_zero hf₀
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.property) hp,
    𝔬₀.augmentationSign_of_morseIndex_eq_zero hp, 𝔬₁.augmentationSign_of_morseIndex_eq_zero hq]
  split_ifs with h
  · rw [singleton_inter_of_mem h, finsum_mem_singleton]
    exact pairSign_of_morseIndex_eq_zero hp _ _ _ _
  · rw [singleton_inter_eq_empty.2 h, finsum_mem_empty]

/-- **The sign of a critical point of top index in the unstable manifold of another.** If `p` and
`q` have index `n = dim M` and `q` lies in `W^u_{X₀}(p)`, the sign of the point `q` of
`W^u_{X₀}(p) ∩ W^s_{X₁}(q)` is the product of the fundamental signs of `p` and `q` for any
orientation `oM` of `M`. At `q` the normal coordinates of `W^s_{X₁}(q)` invert the unstable frame
of `X₁`, and the unstable frame of `X₀` compares the orientation of `W^u_{X₀}(p)` with `oM` at
`q` as it does at `p`. -/
theorem pairSign_of_morseIndex_eq_finrank (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E))) {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁} (hp : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = finrank ℝ E)
    (hq : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = finrank ℝ E)
    (hqp : (q : M) ∈ hX₀.flow.unstableSet p) :
    hX₀.pairSign hX₁ (𝔬₀.chart p) (𝔬₁.chart q) (𝔬₀.orientation p) (𝔬₁.orientation q)
        (hp.trans hq.symm) q =
      hX₀.fundamentalSign 𝔬₀ oM p * hX₁.fundamentalSign 𝔬₁ oM q := by
  classical
  have hφp := 𝔬₀.coord_mfderiv_chart p
  obtain ⟨T, hT⟩ := (hX₀.eventually_mem_linearBackwardTimes hφp hf₀ hqp).exists
  have hFp := bijective_unstableFrame hφp hp hT
  have hFq := bijective_unstableFrame_self (hX := hX₁) 𝔬₁ hq
  set 𝓕p := LinearEquiv.ofBijective (hX₀.unstableFrame (𝔬₀.chart p) q).toLinearMap hFp
  set 𝓕q := LinearEquiv.ofBijective (hX₁.unstableFrame (𝔬₁.chart q) q).toLinearMap hFq
  -- At `q` the comparison map is the frame of `X₀` followed by the inverse of the frame of `X₁`.
  have hC (v : {i // (𝔬₀.chart p).weight i < 0} → ℝ) :
      (𝓕p.trans 𝓕q.symm) v = hX₀.pairComparison hX₁ (𝔬₀.chart p) (𝔬₁.chart q) q v :=
    (pairComparison_self_eq (𝔬₁.coord_mfderiv_chart q) hFp hFq v).symm
  have hCb : Bijective (hX₀.pairComparison hX₁ (𝔬₀.chart p) (𝔬₁.chart q) q) := by
    rw [← show ⇑(𝓕p.trans 𝓕q.symm) = _ from funext hC]
    exact (𝓕p.trans 𝓕q.symm).bijective
  have hCe : LinearEquiv.ofBijective
      (hX₀.pairComparison hX₁ (𝔬₀.chart p) (𝔬₁.chart q) q).toLinearMap hCb = 𝓕p.trans 𝓕q.symm :=
    LinearEquiv.ext fun v ↦ (hC v).symm
  -- Index all orientations by `Fin n`.
  set op := (𝔬₀.orientation p).reindex ℝ _ (finCongr hp)
  set oq := (𝔬₁.orientation q).reindex ℝ _ (finCongr hq)
  have hn : Fintype.card (Fin (finrank ℝ E)) = finrank ℝ (TangentSpace 𝓘(ℝ, E) (q : M)) :=
    Fintype.card_fin _
  have hsign : hX₀.pairSign hX₁ (𝔬₀.chart p) (𝔬₁.chart q) (𝔬₀.orientation p) (𝔬₁.orientation q)
      (hp.trans hq.symm) q = if Orientation.map _ (𝓕p.trans 𝓕q.symm) op = oq then 1 else -1 := by
    rw [pairSign_of_bijective hCb, hCe]
    refine if_congr ?_ rfl rfl
    rw [← (Orientation.reindex ℝ _ (finCongr hp)).injective.eq_iff, ← Orientation.map_reindex,
      Orientation.reindex_finCongr_reindex_finCongr]
  have h₀ : hX₀.fundamentalSign 𝔬₀ oM p =
      if Orientation.map _ 𝓕p op = oM.orientationAt q then 1 else -1 := by
    rw [fundamentalSign_of_morseIndex_eq hp, unstableOrientation_def]
    exact if_congr (map_unstableFrame_eq_orientationAt_iff hf₀ hφp
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.property) oM op hqp hFp _).symm rfl rfl
  have h₁ : hX₁.fundamentalSign 𝔬₁ oM q =
      if Orientation.map _ 𝓕q oq = oM.orientationAt q then 1 else -1 := by
    rw [fundamentalSign_of_morseIndex_eq hq, unstableOrientation_def]
  have hinv (x : Orientation ℝ _ (Fin (finrank ℝ E))) :
      Orientation.map _ 𝓕q.symm (Orientation.map _ 𝓕q x) = x := by
    rw [← Orientation.map_symm]
    exact (Orientation.map _ 𝓕q).symm_apply_apply x
  rw [hsign, h₀, h₁, Orientation.map_trans]
  rcases Orientation.eq_or_eq_neg_of_card_eq_finrank (Orientation.map _ 𝓕p op)
      (oM.orientationAt q) hn with hp' | hp' <;>
    rcases Orientation.eq_or_eq_neg_of_card_eq_finrank (Orientation.map _ 𝓕q oq)
      (oM.orientationAt q) hn with hq' | hq' <;>
    · have hoq := hinv oq
      rw [hq'] at hoq
      rw [hp', hq', ← hoq]
      simp [Module.Ray.ne_neg_self, (Module.Ray.ne_neg_self _).symm]

open scoped Classical in
/-- **The signed pair coefficients between critical points of top index.** The stable manifold of
a critical point `q` of index `n = dim M` is the point `q` itself, so it meets the unstable
manifold of a critical point `p` of index `n` exactly when `q` lies in `W^u_{X₀}(p)`, and then the
coefficient of `q` in the image of `p` is the product of the fundamental signs of `p` and `q` for
any orientation `oM` of `M`. -/
theorem signedPairCoeff_of_morseIndex_eq_finrank (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E))) {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁} (hp : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = finrank ℝ E)
    (hq : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = finrank ℝ E) :
    hX₀.signedPairCoeff hX₁ 𝔬₀ 𝔬₁ p q =
      if (q : M) ∈ hX₀.flow.unstableSet p then
        hX₀.fundamentalSign 𝔬₀ oM p * hX₁.fundamentalSign 𝔬₁ oM q
      else 0 := by
  rw [signedPairCoeff_of_morseIndex_eq (hp.trans hq.symm), signedPairCount_def,
    hX₁.stableSet_eq_singleton_of_manifoldMorseIndex_eq_finrank
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 q.property) hq]
  split_ifs with h
  · rw [inter_singleton_of_mem h, finsum_mem_singleton]
    exact pairSign_of_morseIndex_eq_finrank 𝔬₀ 𝔬₁ hf₀ oM hp hq h
  · rw [inter_singleton_eq_empty.2 h, finsum_mem_empty]

end IsAdaptedPseudoGradient

end TauCeti
