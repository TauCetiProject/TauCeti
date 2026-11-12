/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Polar.Det
public import TauCeti.Geometry.Manifold.Morse.Cell.InnerDisc
public import TauCeti.Geometry.Manifold.Morse.Cell.NegativeDisc
public import TauCeti.Geometry.Manifold.Morse.Cell.Width

/-!
# Comparing the characteristic maps of two Morse charts

Let `ψ₀` and `ψ₁` be two charts of a manifold `M` with values in `ℝⁿ`, centred at the same critical
point of a smooth function `f`, in which

`f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`,

and whose targets contain the closed ball of radius `√ε`. Each carries a characteristic map
`χᵢ : (D^k, ∂D^k) → (M_{c+ε}, M_{c-ε})`, `w ↦ ψᵢ⁻¹(√ε • (w, 0))`, where `M_a = {f ≤ a}`
(`OpenPartialHomeomorph.morseCharacteristicMap`). Milnor's comparison of the cells attached by
two charts (`TauCeti.morseCellReattachment`) takes as input a homotopy of maps of pairs
`K : χ₁ ≃ χ₀ ∘ h`, that is, a homotopy keeping the boundary sphere in `M_{c-ε}`, for an orthogonal
map `h` of `ℝᵏ`. This file constructs that homotopy
(`TauCeti.exists_homotopy_morseCharacteristicMap_polarFactor`), when `f⁻¹[c - ε, c]` is compact
and has no critical point below the level `c`, and the transition `ψ₀ ∘ ψ₁⁻¹` is differentiable at
the origin. The orthogonal map is the polar factor `h = A_uu (A_uuᵀ A_uu)^{-1/2}` of the negative
block `A_uu = ι† A ι` of the derivative `A` of the transition at the origin, where `ι : ℝᵏ → ℝⁿ`
extends by zero onto the first `k` coordinates.

The homotopy follows Milnor's Remark 3.3. For a small radius `0 < d ≤ 1`, the small negative
discs of radius `√ε d` of the two charts are joined by
`OpenPartialHomeomorph.exists_negativeDisc_homotopy_euclidean`, staying below `c - ‖v‖²`.
Rescaled by `√ε`, this is a homotopy from `χ₁` to `χ₀ ∘ h` on the disc `‖w‖ ≤ d` that keeps the
sphere `‖w‖ = d` in `M_{c-εd²}`. It extends to the whole disc, keeping the boundary sphere in
`M_{c-ε}`, by `TauCeti.exists_homotopy_morseCharacteristicMap_of_innerDisc`, which uses that the
band `f⁻¹[c - ε, c - εd²]` is compact and free of critical points.

When `det A_uu > 0` the polar factor lies in the special orthogonal group and can be removed, so
the attaching maps `∂D^k → M_{c-ε}` of the two charts are homotopic
(`TauCeti.homotopic_morseAttachingMap_of_det_pos`).

The two charts may also be used at different widths: `ψ₀` at width `ε₀` and `ψ₁` at width `ε₁`,
each chart containing only its own closed ball. One compares the charts at the smaller width, where
both balls fit, and then widens the chart with the larger ball through its negative-coordinate
annulus (`OpenPartialHomeomorph.homotopic_morseAttachingMap_comp_retraction`). For any retraction
`r` of the larger lower sublevel onto the smaller one, for instance the retraction of a compact
critical-free band (`TauCeti.exists_sublevelDeformation`), this gives `α₁ ≃ r ∘ α₀ ∘ h` when
`ε₀ ≤ ε₁` (`TauCeti.exists_homotopic_morseAttachingMap_retraction_comp_polarFactor`) and
`r ∘ α₁ ≃ α₀ ∘ h` when `ε₁ ≤ ε₀`
(`TauCeti.exists_homotopic_retraction_comp_morseAttachingMap_polarFactor`), with the same polar
factor `h`, which does not depend on the widths.

## Main results

* `TauCeti.exists_homotopy_morseCharacteristicMap_polarFactor`: the characteristic map of `ψ₁` is
  homotopic as a map of pairs to that of `ψ₀` composed with the polar factor of the negative block
  of the transition.
* `TauCeti.homotopic_morseAttachingMap_of_det_pos`: when that negative block preserves
  orientation, the two attaching maps are homotopic.
* `TauCeti.exists_homotopic_morseAttachingMap_retraction_comp_polarFactor`,
  `TauCeti.exists_homotopic_retraction_comp_morseAttachingMap_polarFactor`: the comparison of the
  attaching maps of the two charts at unequal widths, through a retraction of the band between
  the two lower sublevels.
* `TauCeti.homotopic_morseAttachingMap_retraction_comp_of_det_pos`,
  `TauCeti.homotopic_retraction_comp_morseAttachingMap_of_det_pos`: at unequal widths, when the
  negative block preserves orientation, the polar factor can be dropped.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Remark 3.3 and Lemma 3.6.
-/

public section

noncomputable section

universe u

open Set Metric Topology unitInterval CategoryTheory
open LinearIsometry (piLpExtendByZero)
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {Iₘ : ModelWithCorners ℝ E H} [Iₘ.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold Iₘ ∞ M] [T2Space M]
  {f : M → ℝ} {c ε : ℝ} {n k : ℕ}

/-- **The characteristic maps of two Morse charts are homotopic as maps of pairs, up to the
polar factor of their transition.** Let `ψ₀` and `ψ₁` be charts with a common centre in which
`f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`, whose targets contain the closed ball of radius `√ε`
and whose transition `ψ₀ ∘ ψ₁⁻¹` is differentiable at the origin, with derivative `A`. Suppose
that `f⁻¹[c - ε, c]` is compact and that `f` has no critical point with value in `[c - ε, c)`.
Let `g` be the polar factor of the negative block `ι† A ι` of `A`, where `ι : ℝᵏ → ℝⁿ` extends by
zero onto the first `k` coordinates. Then `g` is a linear isometry, and the characteristic map
`χ₁ : D^k → M_{c+ε}` of `ψ₁` is homotopic to `χ₀ ∘ g` through maps sending the boundary sphere
into the lower sublevel `M_{c-ε}`. -/
theorem exists_homotopy_morseCharacteristicMap_polarFactor (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n) (hε : 0 < ε)
    (hball₀ : closedBall 0 √ε ⊆ ψ₀.target) (hball₁ : closedBall 0 √ε ⊆ ψ₁.target)
    (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ y j ^ 2)
    (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ y j ^ 2)
    (hp : ψ₀.symm 0 = ψ₁.symm 0) (hT : DifferentiableAt ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) c))
    (hreg : ∀ x, c - ε ≤ f x → f x < c → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0) :
    ∃ g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k),
      ⇑g = (ContinuousLinearMap.adjoint
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L
        fderiv ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0 ∘L
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor ∧
      ∃ K : (ψ₁.morseCharacteristicMap hk hε.le hball₁ hf₁).hom.Homotopy
          (g.diskMap ≫ ψ₀.morseCharacteristicMap hk hε.le hball₀ hf₀).hom,
        ∀ t (s : TopCat.diskBoundary.{u} k),
          f (K (t, TopCat.diskBoundaryInclusion k s)) ≤ c - ε := by
  have h0 (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hball : closedBall 0 √ε ⊆ ψ.target) : (0 : EuclideanSpace ℝ (Fin n)) ∈ ψ.target :=
    hball (mem_closedBall_self (Real.sqrt_nonneg ε))
  obtain ⟨g, hg, δ₀, hδ₀, hG⟩ := OpenPartialHomeomorph.exists_negativeDisc_homotopy_euclidean
    ψ₀ ψ₁ hk hf₀ hf₁ (h0 ψ₀ hball₀) (h0 ψ₁ hball₁) hp hT
  -- Compare the negative discs of radius `√ε * d`, for some `0 < d ≤ 1`.
  have hsε : 0 < √ε := Real.sqrt_pos.2 hε
  have hd : 0 < min 1 (δ₀ / √ε) := lt_min one_pos (div_pos hδ₀ hsε)
  set d : I := ⟨min 1 (δ₀ / √ε), hd.le, min_le_left _ _⟩
  obtain ⟨G, hG0, hG1, hGf⟩ := hG (√ε * d) ⟨mul_pos hsε hd,
    (mul_le_mul_of_nonneg_left (min_le_right _ _) hsε.le).trans_eq (mul_div_cancel₀ _ hsε.ne')⟩
  have hεd : 0 < ε * (d : ℝ) ^ 2 := by positivity
  -- Rescale `G` onto the disc of radius `d`, where it joins the two characteristic maps.
  have hmem (w : closedBall (0 : EuclideanSpace ℝ (Fin k)) d) :
      √ε • (w : EuclideanSpace ℝ (Fin k)) ∈ closedBall 0 (√ε * d) := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg hsε.le]
    exact mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 w.2) hsε.le
  let G' : C(I × closedBall (0 : EuclideanSpace ℝ (Fin k)) d, M) :=
    G.comp ⟨fun x ↦ (x.1, ⟨_, hmem x.2⟩), by fun_prop⟩
  have hG' (t : I) (w : closedBall (0 : EuclideanSpace ℝ (Fin k)) d) :
      G' (t, w) = G (t, ⟨_, hmem w⟩) := rfl
  have hnorm (w : EuclideanSpace ℝ (Fin k)) : ‖√ε • w‖ ^ 2 = ε * ‖w‖ ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg hsε.le, mul_pow, Real.sq_sqrt hε.le]
  refine ⟨g, hg, exists_homotopy_morseCharacteristicMap_of_innerDisc hf hk hε.le hball₀ hball₁
    hf₀ hf₁ g (unitInterval.coe_pos.1 hd)
    (hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.continuous)
      (preimage_mono (Icc_subset_Icc le_rfl (by linarith))))
    (fun x h₁ h₂ ↦ hreg x h₁ (by linarith)) G' (fun w ↦ ?_) (fun w ↦ ?_) (fun t w ↦ ?_)
    (fun t w hw ↦ ?_)⟩
  · rw [hG', hG0, OpenPartialHomeomorph.morseCellMap_def, map_smul]
  · rw [hG', hG1, OpenPartialHomeomorph.morseCellMap_def, map_smul, map_smul]
  · rw [hG']
    nlinarith [hGf t ⟨_, hmem w⟩, sq_nonneg ‖√ε • (w : EuclideanSpace ℝ (Fin k))‖]
  · rw [hG']
    refine (hGf t _).trans_eq ?_
    rw [hnorm, hw]

/-- **Two Morse charts whose negative blocks preserve orientation have homotopic attaching
maps.** Under the hypotheses of `TauCeti.exists_homotopy_morseCharacteristicMap_polarFactor`, if
the negative block `ι† A ι` of the derivative `A` of the transition `ψ₀ ∘ ψ₁⁻¹` at the origin has
positive determinant, then the attaching maps `∂D^k → M_{c-ε}` of the two charts are homotopic. -/
theorem homotopic_morseAttachingMap_of_det_pos (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n) (hε : 0 < ε)
    (hball₀ : closedBall 0 √ε ⊆ ψ₀.target) (hball₁ : closedBall 0 √ε ⊆ ψ₁.target)
    (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ y j ^ 2)
    (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ y j ^ 2)
    (hp : ψ₀.symm 0 = ψ₁.symm 0) (hT : DifferentiableAt ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) c))
    (hreg : ∀ x, c - ε ≤ f x → f x < c → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0)
    (hdet : 0 < (ContinuousLinearMap.adjoint
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L
        fderiv ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0 ∘L
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).det) :
    (ψ₁.morseAttachingMap hk hε.le hball₁ hf₁).hom.Homotopic
      (ψ₀.morseAttachingMap hk hε.le hball₀ hf₀).hom := by
  obtain ⟨g, hg, K, hK⟩ := exists_homotopy_morseCharacteristicMap_polarFactor hf ψ₀ ψ₁ hk hε
    hball₀ hball₁ hf₀ hf₁ hp hT hcompact hreg
  refine homotopic_morseAttachingMap_of_det_eq_one hk hε.le hball₀ hball₁ hf₀ hf₁ ?_ K hK
  have hg' : g.toLinearMap = ((ContinuousLinearMap.adjoint
      (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L
        fderiv ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0 ∘L
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor :
            EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) :=
    LinearMap.ext (congrFun hg)
  rw [hg']
  exact ContinuousLinearMap.det_polarFactor_eq_one_iff.2 hdet

section UnequalLevels

variable {ε₀ ε₁ : ℝ}

/-- **Attaching maps of two Morse charts at unequal levels, lower level for the first chart.**
Let `ψ₀` and `ψ₁` be charts with a common centre in which
`f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`, with `0 < ε₀ ≤ ε₁`, such that the target of `ψ₀`
contains the closed ball of radius `√ε₀` and that of `ψ₁` the closed ball of radius `√ε₁`, and
whose transition `ψ₀ ∘ ψ₁⁻¹` is differentiable at the origin. Suppose that `f⁻¹[c - ε₀, c]` is
compact and that `f` has no critical point with value in `[c - ε₀, c)`. Let `g` be the polar
factor of the negative block of the derivative of the transition, as in
`TauCeti.exists_homotopy_morseCharacteristicMap_polarFactor`, and let `r` be any retraction of
`M_{c-ε₀}` onto `M_{c-ε₁}`. Then the attaching map `α₁ : ∂D^k → M_{c-ε₁}` of `ψ₁` at width `ε₁`
is homotopic to `r ∘ α₀ ∘ g`, where `α₀` is the attaching map of `ψ₀` at width `ε₀`. The chart
`ψ₀` need not contain the closed ball of radius `√ε₁`. -/
theorem exists_homotopic_morseAttachingMap_retraction_comp_polarFactor
    (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n) (h₀ : 0 < ε₀)
    (hε : ε₀ ≤ ε₁) (hball₀ : closedBall 0 √ε₀ ⊆ ψ₀.target)
    (hball₁ : closedBall 0 √ε₁ ⊆ ψ₁.target)
    (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ y j ^ 2)
    (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ y j ^ 2)
    (hp : ψ₀.symm 0 = ψ₁.symm 0) (hT : DifferentiableAt ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε₀) c))
    (hreg : ∀ x, c - ε₀ ≤ f x → f x < c → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0)
    (r : C({x : M | f x ≤ c - ε₀}, {x : M | f x ≤ c - ε₁}))
    (hr : ∀ x, r (sublevelInclusion f (c - ε₁) (c - ε₀) (sub_le_sub_left hε c) x) = x) :
    ∃ g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k),
      ⇑g = (ContinuousLinearMap.adjoint
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L
        fderiv ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0 ∘L
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor ∧
      (ψ₁.morseAttachingMap hk (h₀.le.trans hε) hball₁ hf₁).hom.Homotopic
        (r.comp (g.diskBoundaryMap ≫ ψ₀.morseAttachingMap hk h₀.le hball₀ hf₀).hom) := by
  have hball₁' : closedBall 0 √ε₀ ⊆ ψ₁.target :=
    (closedBall_subset_closedBall (Real.sqrt_le_sqrt hε)).trans hball₁
  -- Compare the two charts at the common width `ε₀`, then widen `ψ₁` to `ε₁`.
  obtain ⟨g, hg, K, hK⟩ := exists_homotopy_morseCharacteristicMap_polarFactor hf ψ₀ ψ₁ hk h₀
    hball₀ hball₁' hf₀ hf₁ hp hT hcompact hreg
  refine ⟨g, hg, ?_⟩
  exact (ψ₁.homotopic_morseAttachingMap_comp_retraction hk h₀.le hε hball₁ hf₁ r hr).symm.trans
    ((ContinuousMap.Homotopic.refl r).comp
      (homotopic_morseAttachingMap_diskBoundaryMap_comp hk h₀.le hball₀ hball₁' hf₀ hf₁ K hK))

/-- **Attaching maps of two Morse charts at unequal levels, lower level for the second chart.**
This is the counterpart of `TauCeti.exists_homotopic_morseAttachingMap_retraction_comp_polarFactor`
for `0 < ε₁ ≤ ε₀`, where now the target of `ψ₀` contains the closed ball of radius `√ε₀` and that
of `ψ₁` the closed ball of radius `√ε₁`. Suppose that `f⁻¹[c - ε₁, c]` is compact and that `f` has
no critical point with value in `[c - ε₁, c)`, and let `r` be any retraction of `M_{c-ε₁}` onto
`M_{c-ε₀}`. Then `r ∘ α₁` is homotopic to `α₀ ∘ g`, where `α₁` is the attaching map of `ψ₁` at
width `ε₁`, `α₀` that of `ψ₀` at width `ε₀`, and `g` the polar factor of the negative block of the
derivative of the transition `ψ₀ ∘ ψ₁⁻¹` at the origin. The chart `ψ₁` need not contain the closed
ball of radius `√ε₀`. -/
theorem exists_homotopic_retraction_comp_morseAttachingMap_polarFactor
    (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n) (h₁ : 0 < ε₁)
    (hε : ε₁ ≤ ε₀) (hball₀ : closedBall 0 √ε₀ ⊆ ψ₀.target)
    (hball₁ : closedBall 0 √ε₁ ⊆ ψ₁.target)
    (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ y j ^ 2)
    (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ y j ^ 2)
    (hp : ψ₀.symm 0 = ψ₁.symm 0) (hT : DifferentiableAt ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε₁) c))
    (hreg : ∀ x, c - ε₁ ≤ f x → f x < c → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0)
    (r : C({x : M | f x ≤ c - ε₁}, {x : M | f x ≤ c - ε₀}))
    (hr : ∀ x, r (sublevelInclusion f (c - ε₀) (c - ε₁) (sub_le_sub_left hε c) x) = x) :
    ∃ g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k),
      ⇑g = (ContinuousLinearMap.adjoint
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L
        fderiv ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0 ∘L
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor ∧
      (r.comp (ψ₁.morseAttachingMap hk h₁.le hball₁ hf₁).hom).Homotopic
        (g.diskBoundaryMap ≫ ψ₀.morseAttachingMap hk (h₁.le.trans hε) hball₀ hf₀).hom := by
  have hball₀' : closedBall 0 √ε₁ ⊆ ψ₀.target :=
    (closedBall_subset_closedBall (Real.sqrt_le_sqrt hε)).trans hball₀
  -- Compare the two charts at the common width `ε₁`, then widen `ψ₀` to `ε₀`.
  obtain ⟨g, hg, K, hK⟩ := exists_homotopy_morseCharacteristicMap_polarFactor hf ψ₀ ψ₁ hk h₁
    hball₀' hball₁ hf₀ hf₁ hp hT hcompact hreg
  refine ⟨g, hg, ?_⟩
  have hwiden := (ψ₀.homotopic_morseAttachingMap_comp_retraction hk h₁.le hε hball₀ hf₀ r hr).comp
    (ContinuousMap.Homotopic.refl g.diskBoundaryMap.hom)
  rw [ContinuousMap.comp_assoc, ← TopCat.hom_comp, ← TopCat.hom_comp] at hwiden
  exact ((ContinuousMap.Homotopic.refl r).comp
    (homotopic_morseAttachingMap_diskBoundaryMap_comp hk h₁.le hball₀' hball₁ hf₀ hf₁ K hK)).trans
    hwiden

/-- **Orientation-compatible Morse charts have homotopic attaching maps at unequal levels, lower
level for the first chart.** Under the hypotheses of
`TauCeti.exists_homotopic_morseAttachingMap_retraction_comp_polarFactor`, if the negative block
of the derivative of the transition `ψ₀ ∘ ψ₁⁻¹` at the origin has positive determinant, then the
attaching map `α₁ : ∂D^k → M_{c-ε₁}` of `ψ₁` at width `ε₁` is homotopic to `r ∘ α₀`, where `α₀` is
the attaching map of `ψ₀` at width `ε₀ ≤ ε₁` and `r` is any retraction of `M_{c-ε₀}` onto
`M_{c-ε₁}`. -/
theorem homotopic_morseAttachingMap_retraction_comp_of_det_pos (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n) (h₀ : 0 < ε₀)
    (hε : ε₀ ≤ ε₁) (hball₀ : closedBall 0 √ε₀ ⊆ ψ₀.target)
    (hball₁ : closedBall 0 √ε₁ ⊆ ψ₁.target)
    (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ y j ^ 2)
    (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ y j ^ 2)
    (hp : ψ₀.symm 0 = ψ₁.symm 0) (hT : DifferentiableAt ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε₀) c))
    (hreg : ∀ x, c - ε₀ ≤ f x → f x < c → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0)
    (r : C({x : M | f x ≤ c - ε₀}, {x : M | f x ≤ c - ε₁}))
    (hr : ∀ x, r (sublevelInclusion f (c - ε₁) (c - ε₀) (sub_le_sub_left hε c) x) = x)
    (hdet : 0 < (ContinuousLinearMap.adjoint
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L
        fderiv ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0 ∘L
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).det) :
    (ψ₁.morseAttachingMap hk (h₀.le.trans hε) hball₁ hf₁).hom.Homotopic
      (r.comp (ψ₀.morseAttachingMap hk h₀.le hball₀ hf₀).hom) := by
  have hball₁' : closedBall 0 √ε₀ ⊆ ψ₁.target :=
    (closedBall_subset_closedBall (Real.sqrt_le_sqrt hε)).trans hball₁
  exact (ψ₁.homotopic_morseAttachingMap_comp_retraction hk h₀.le hε hball₁ hf₁ r hr).symm.trans
    ((ContinuousMap.Homotopic.refl r).comp (homotopic_morseAttachingMap_of_det_pos hf ψ₀ ψ₁ hk h₀
      hball₀ hball₁' hf₀ hf₁ hp hT hcompact hreg hdet))

/-- **Orientation-compatible Morse charts have homotopic attaching maps at unequal levels, lower
level for the second chart.** Under the hypotheses of
`TauCeti.exists_homotopic_retraction_comp_morseAttachingMap_polarFactor`, if the negative block
of the derivative of the transition `ψ₀ ∘ ψ₁⁻¹` at the origin has positive determinant, then
`r ∘ α₁` is homotopic to `α₀`, where `α₁` is the attaching map of `ψ₁` at width `ε₁`, `α₀` that
of `ψ₀` at width `ε₀ ≥ ε₁`, and `r` is any retraction of `M_{c-ε₁}` onto `M_{c-ε₀}`. -/
theorem homotopic_retraction_comp_morseAttachingMap_of_det_pos (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n) (h₁ : 0 < ε₁)
    (hε : ε₁ ≤ ε₀) (hball₀ : closedBall 0 √ε₀ ⊆ ψ₀.target)
    (hball₁ : closedBall 0 √ε₁ ⊆ ψ₁.target)
    (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ y j ^ 2)
    (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ y j ^ 2)
    (hp : ψ₀.symm 0 = ψ₁.symm 0) (hT : DifferentiableAt ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε₁) c))
    (hreg : ∀ x, c - ε₁ ≤ f x → f x < c → mfderiv Iₘ 𝓘(ℝ) f x ≠ 0)
    (r : C({x : M | f x ≤ c - ε₁}, {x : M | f x ≤ c - ε₀}))
    (hr : ∀ x, r (sublevelInclusion f (c - ε₀) (c - ε₁) (sub_le_sub_left hε c) x) = x)
    (hdet : 0 < (ContinuousLinearMap.adjoint
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L
        fderiv ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0 ∘L
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).det) :
    (r.comp (ψ₁.morseAttachingMap hk h₁.le hball₁ hf₁).hom).Homotopic
      (ψ₀.morseAttachingMap hk (h₁.le.trans hε) hball₀ hf₀).hom := by
  have hball₀' : closedBall 0 √ε₁ ⊆ ψ₀.target :=
    (closedBall_subset_closedBall (Real.sqrt_le_sqrt hε)).trans hball₀
  exact ((ContinuousMap.Homotopic.refl r).comp (homotopic_morseAttachingMap_of_det_pos hf ψ₀ ψ₁ hk
    h₁ hball₀' hball₁ hf₀ hf₁ hp hT hcompact hreg hdet)).trans
    (ψ₀.homotopic_morseAttachingMap_comp_retraction hk h₁.le hε hball₀ hf₀ r hr)

end UnequalLevels

end TauCeti
