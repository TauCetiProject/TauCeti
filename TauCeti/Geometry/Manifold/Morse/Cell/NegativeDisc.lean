/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import TauCeti.Analysis.Calculus.Morse.NegativeDisc
public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.Polar.Bounded

/-!
# Comparing the small negative discs of two Morse charts

Let `ψ₀` and `ψ₁` be two charts of a space `M` with values in `E × F`, centred at the same point
`p`, in which a function `f` has the split normal form `f = c - ‖u‖² + ‖v‖²`. The negative disc of
radius `δ` of `ψ₁` is `w ↦ ψ₁⁻¹ (w, 0)` for `‖w‖ ≤ δ`; along it `f = c - ‖w‖²`, so its boundary
sphere lies on the level `c - δ²`. Comparing the cells attached by two Morse charts requires
deforming this disc to the negative disc of `ψ₀`, without raising its boundary above the level
`c - δ²`.

When the transition `T = ψ₀ ∘ ψ₁⁻¹` is differentiable at the origin, with derivative `A`, the
negative block `N u = (A (u, 0)).1` of `A` is invertible and has a polar decomposition `N = h P`
with `h` a linear isometry equivalence (`ContinuousLinearMap.polarFactor`). For every sufficiently
small `δ > 0` there is a homotopy `G` from `w ↦ ψ₁⁻¹ (w, 0)` to `w ↦ ψ₀⁻¹ (h w, 0)` on the disc
`‖w‖ ≤ δ` with `f (G (t, w)) ≤ c - ‖w‖²` throughout
(`OpenPartialHomeomorph.exists_negativeDisc_homotopy`). In particular the boundary sphere stays
in the sublevel `{f ≤ c - δ²}`. The homotopy is the coordinate deformation
`HasFDerivAt.exists_negativeDisc_homotopy` read through `ψ₀⁻¹`; only a neighbourhood of the
common centre is used, so the whole negative discs of the two charts need not overlap.

The same holds for charts with values in `ℝⁿ` in the normal form
`f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`, whose negative discs are `w ↦ ψ⁻¹ (w, 0)` with `w ∈ ℝᵏ`
extended by zero along the first `k` coordinates
(`OpenPartialHomeomorph.exists_negativeDisc_homotopy_euclidean`). There the polar factor is that of
the negative block `ι† A ι` of the derivative, where `ι : ℝᵏ → ℝⁿ` is the zero extension. The
proof splits the coordinates as `ℝⁿ ≃ ℝᵏ × ℝⁿ⁻ᵏ` (`EuclideanSpace.sumComplEquivProd`) and uses the
naturality of polar factors under conjugation (`ContinuousLinearMap.polarFactor_conj`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Remark 3.3 and Lemma 3.6.
-/

public section

open Set Metric Topology unitInterval
open LinearIsometry (piLpExtendByZero)

namespace OpenPartialHomeomorph

variable {M E F : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The small negative discs of two Morse charts are homotopic below the critical level.** Let
`ψ₀` and `ψ₁` be charts with a common centre, in which `f = c - ‖u‖² + ‖v‖²`, and whose transition
`ψ₀ ∘ ψ₁⁻¹` is differentiable at the origin. Let the linear isometry `h` be the polar factor of the
negative block of the derivative of the transition. Then for every small `δ > 0`, the negative disc
`w ↦ ψ₁⁻¹ (w, 0)` of radius `δ` is homotopic to `w ↦ ψ₀⁻¹ (h w, 0)` through maps `g` with
`f (g w) ≤ c - ‖w‖²`. -/
theorem exists_negativeDisc_homotopy (ψ₀ ψ₁ : OpenPartialHomeomorph M (E × F)) {f : M → ℝ}
    {c : ℝ} (hf₀ : ∀ y ∈ ψ₀.source, f y = c - ‖(ψ₀ y).1‖ ^ 2 + ‖(ψ₀ y).2‖ ^ 2)
    (hf₁ : ∀ y ∈ ψ₁.source, f y = c - ‖(ψ₁ y).1‖ ^ 2 + ‖(ψ₁ y).2‖ ^ 2)
    (h₀ : (0 : E × F) ∈ ψ₀.target) (h₁ : (0 : E × F) ∈ ψ₁.target)
    (hp : ψ₀.symm 0 = ψ₁.symm 0) (hT : DifferentiableAt ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0) :
    ∃ h : E ≃ₗᵢ[ℝ] E, ⇑h = ((ContinuousLinearMap.fst ℝ E F).comp
        ((fderiv ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0).comp (ContinuousLinearMap.inl ℝ E F))).polarFactor ∧
      ∃ δ₀ > 0, ∀ δ ∈ Ioc 0 δ₀, ∃ G : C(I × closedBall (0 : E) δ, M),
        (∀ w, G (0, w) = ψ₁.symm ((w : E), 0)) ∧ (∀ w, G (1, w) = ψ₀.symm (h w, 0)) ∧
        ∀ t w, f (G (t, w)) ≤ c - ‖(w : E)‖ ^ 2 := by
  -- The transition is a change of coordinates preserving `Q` on the open set `U`.
  set U := ψ₁.target ∩ ψ₁.symm ⁻¹' ψ₀.source
  have hU : IsOpen U := ψ₁.isOpen_inter_preimage_symm ψ₀.open_source
  have h0U : (0 : E × F) ∈ U := ⟨h₁, by simpa [← hp] using ψ₀.map_target h₀⟩
  have hT0 : ψ₀ (ψ₁.symm 0) = 0 := by rw [← hp, ψ₀.right_inv h₀]
  have hc : ContinuousOn (fun z ↦ ψ₀ (ψ₁.symm z)) U :=
    ψ₀.continuousOn.comp (ψ₁.continuousOn_symm.mono inter_subset_left) fun _ hy ↦ hy.2
  have hQ (y : E × F) (hy : y ∈ U) :
      -‖(ψ₀ (ψ₁.symm y)).1‖ ^ 2 + ‖(ψ₀ (ψ₁.symm y)).2‖ ^ 2 = -‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 := by
    have h₀' := hf₀ _ hy.2
    have h₁' := hf₁ _ (ψ₁.map_target hy.1)
    rw [ψ₁.right_inv hy.1] at h₁'
    linarith
  obtain ⟨h, hh, δ₀, hδ₀, hH⟩ := hT.hasFDerivAt.exists_negativeDisc_homotopy hT0 hU h0U hc hQ
    (ψ₀.open_target.mem_nhds h₀)
  refine ⟨h, hh, δ₀, hδ₀, fun δ hδ ↦ ?_⟩
  obtain ⟨hdisc, H, hH0, hH1, hHb⟩ := hH δ hδ
  -- Read the coordinate homotopy through the inverse of `ψ₀`.
  refine ⟨⟨fun p ↦ ψ₀.symm (H p),
    ψ₀.continuousOn_symm.comp_continuous H.continuous fun p ↦ (hHb p.1 p.2).1⟩,
    fun w ↦ ?_, fun w ↦ ?_, fun t w ↦ ?_⟩
  · simp only [ContinuousMap.coe_mk, hH0]
    exact ψ₀.left_inv (hdisc w w.2).2
  · simp only [ContinuousMap.coe_mk, hH1]
  · obtain ⟨hz, hq⟩ := hHb t w
    simp only [ContinuousMap.coe_mk]
    rw [hf₀ _ (ψ₀.map_target hz), ψ₀.right_inv hz]
    linarith


section Euclidean

variable {n k : ℕ}

/-- The negative block `ι† A ι` of an operator `A` of `ℝⁿ`, for the zero extension `ι : ℝᵏ → ℝⁿ`,
is the negative block of `A` read in the splitting of `ℝⁿ` along `j < k`, conjugated back to
`ℝᵏ`; so is its polar factor. -/
private theorem polarFactor_adjoint_comp_comp_piLpExtendByZero (hk : k ≤ n)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (ContinuousLinearMap.adjoint
        (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L A ∘L
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor =
      ((EuclideanSpace.finCastLEEquiv ℝ hk).symm :
          EuclideanSpace ℝ {j : Fin n // j.val < k} →L[ℝ] EuclideanSpace ℝ (Fin k)) ∘L
        (ContinuousLinearMap.fst ℝ _ _ ∘L
          ((EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k)).toContinuousLinearMap ∘L
            A ∘L (EuclideanSpace.sumComplEquivProd ℝ
              (fun j : Fin n ↦ j.val < k)).symm.toContinuousLinearMap) ∘L
          ContinuousLinearMap.inl ℝ _ _).polarFactor ∘L
        ((EuclideanSpace.finCastLEEquiv ℝ hk).symm.symm :
          EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ {j : Fin n // j.val < k}) := by
  rw [← ContinuousLinearMap.polarFactor_conj]
  congr 1
  ext1 w
  simp [EuclideanSpace.adjoint_piLpExtendByZero_castLEEmb_apply,
    ← EuclideanSpace.finCastLEEquiv_symm_fst_sumComplEquivProd,
    EuclideanSpace.sumComplEquivProd_symm_finCastLEEquiv]

/-- **The small negative discs of two Euclidean Morse charts are homotopic below the critical
level.** Let `ψ₀` and `ψ₁` be charts with values in `ℝⁿ` and a common centre, in which
`f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`, and whose transition `ψ₀ ∘ ψ₁⁻¹` is differentiable at the
origin with derivative `A`. Let `ι : ℝᵏ → ℝⁿ` be the zero extension onto the first `k` coordinates
and let the linear isometry `g` be the polar factor of the negative block `ι† A ι`. Then for every
small `δ > 0`, the negative disc `w ↦ ψ₁⁻¹ (ι w)` of radius `δ` is homotopic to
`w ↦ ψ₀⁻¹ (ι (g w))` through maps `G` with `f (G w) ≤ c - ‖w‖²`. -/
theorem exists_negativeDisc_homotopy_euclidean
    (ψ₀ ψ₁ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n) {f : M → ℝ}
    {c : ℝ} (hf₀ : ∀ y ∈ ψ₀.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ y j ^ 2)
    (hf₁ : ∀ y ∈ ψ₁.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ y j ^ 2)
    (h₀ : (0 : EuclideanSpace ℝ (Fin n)) ∈ ψ₀.target) (h₁ : 0 ∈ ψ₁.target)
    (hp : ψ₀.symm 0 = ψ₁.symm 0) (hT : DifferentiableAt ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0) :
    ∃ g : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k),
      ⇑g = (ContinuousLinearMap.adjoint
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L
        fderiv ℝ (fun z ↦ ψ₀ (ψ₁.symm z)) 0 ∘L
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor ∧
      ∃ δ₀ > 0, ∀ δ ∈ Ioc 0 δ₀, ∃ G : C(I × closedBall (0 : EuclideanSpace ℝ (Fin k)) δ, M),
        (∀ w, G (0, w) = ψ₁.symm (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk) w)) ∧
        (∀ w, G (1, w) = ψ₀.symm (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk) (g w))) ∧
        ∀ t w, f (G (t, w)) ≤ c - ‖(w : EuclideanSpace ℝ (Fin k))‖ ^ 2 := by
  -- Split the coordinates into the negative factor `j < k` and the positive factor.
  set S := EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k) with hS
  set e := EuclideanSpace.finCastLEEquiv ℝ hk
  have hsplit (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hψ : ∀ y ∈ ψ.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2) :
      ∀ y ∈ (ψ.transHomeomorph S.toHomeomorph).source,
        f y = c - ‖((ψ.transHomeomorph S.toHomeomorph) y).1‖ ^ 2 +
          ‖((ψ.transHomeomorph S.toHomeomorph) y).2‖ ^ 2 := fun y hy ↦ by
    rw [hψ y hy, EuclideanSpace.sum_ite_neg_one_mul_sq_eq]
    simp only [transHomeomorph_apply, Function.comp_apply,
      ContinuousLinearEquiv.coe_toHomeomorph, hS]
    ring
  have hsymm (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (w) :
      (ψ.transHomeomorph S.toHomeomorph).symm (e w, 0) =
        ψ.symm (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk) w) := by
    simp only [transHomeomorph_symm_apply, Function.comp_apply]
    exact congrArg ψ.symm (EuclideanSpace.sumComplEquivProd_symm_finCastLEEquiv hk w)
  -- The transition of the split charts is the transition of `ψ₀, ψ₁` conjugated by `S`.
  have hTS : (fun z ↦ (ψ₀.transHomeomorph S.toHomeomorph)
      ((ψ₁.transHomeomorph S.toHomeomorph).symm z)) =
        S ∘ (fun z ↦ ψ₀ (ψ₁.symm z)) ∘ S.symm := by
    funext z
    simp
  have hT0 : DifferentiableAt ℝ ((fun z ↦ ψ₀ (ψ₁.symm z)) ∘ S.symm) 0 :=
    DifferentiableAt.comp (0 : _ × _) (by rwa [map_zero]) S.symm.differentiableAt
  obtain ⟨h, hh, δ₀, hδ₀, hG⟩ := exists_negativeDisc_homotopy (ψ₀.transHomeomorph S.toHomeomorph)
    (ψ₁.transHomeomorph S.toHomeomorph) (hsplit ψ₀ hf₀) (hsplit ψ₁ hf₁) (by simpa using h₀)
    (by simpa using h₁) (by simpa using hp) (hTS ▸ S.differentiableAt.comp 0 hT0)
  rw [hTS, S.comp_fderiv, S.symm.comp_right_fderiv, map_zero] at hh
  refine ⟨e.trans (h.trans e.symm), ?_, δ₀, hδ₀, fun δ hδ ↦ ?_⟩
  · rw [polarFactor_adjoint_comp_comp_piLpExtendByZero]
    funext w
    exact congrArg e.symm (congrFun hh (e w))
  -- Read the split homotopy through `e`, which preserves norms.
  obtain ⟨G, hG0, hG1, hGf⟩ := hG δ hδ
  have he (w : closedBall (0 : EuclideanSpace ℝ (Fin k)) δ) : e w ∈ closedBall 0 δ := by
    rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    exact mem_closedBall_zero_iff.1 w.2
  refine ⟨⟨fun p ↦ G (p.1, ⟨e p.2, he p.2⟩), by fun_prop⟩, fun w ↦ ?_, fun w ↦ ?_,
    fun t w ↦ ?_⟩
  · simp only [ContinuousMap.coe_mk, hG0, hsymm]
  · simp only [ContinuousMap.coe_mk, hG1, LinearIsometryEquiv.trans_apply]
    rw [← hsymm, LinearIsometryEquiv.apply_symm_apply]
  · simpa using hGf t ⟨e w, he w⟩

end Euclidean

end OpenPartialHomeomorph
