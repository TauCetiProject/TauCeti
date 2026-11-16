/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import TauCeti.Analysis.Calculus.Morse.NegativeDisc
public import TauCeti.Analysis.InnerProductSpace.Polar.PiL2

/-!
# Comparing the small negative discs of two Morse charts

Let `ψ₀` and `ψ₁` be two charts of a space `M` with values in `E × F`, centred at the same point
`p`, in which a function `f` has the split normal form `f = c - ‖u‖² + ‖v‖²`. The negative disc of
radius `δ` of `ψ₁` is `w ↦ ψ₁⁻¹ (w, 0)` for `‖w‖ ≤ δ`; along it `f = c - ‖w‖²`, so its boundary
sphere lies on the level `c - δ²`. Comparing the cells attached by two Morse charts requires
deforming this disc to the negative disc of `ψ₀`, without raising its boundary above the level
`c - δ²`.

When the transition `T = ψ₀ ∘ ψ₁⁻¹` is differentiable at the origin, with derivative `A`, the
negative block `N u = (A (u, 0)).1` of `A` is injective and has a polar decomposition `N = h P`
with `h` a linear isometry (`ContinuousLinearMap.polarFactor`), orthogonal in finite dimension.
For every sufficiently small `δ > 0` there is a homotopy `G` from `w ↦ ψ₁⁻¹ (w, 0)` to
`w ↦ ψ₀⁻¹ (h w, 0)` on the disc `‖w‖ ≤ δ` with `f (G (t, w)) ≤ c - ‖w‖²` throughout
(`OpenPartialHomeomorph.exists_negativeDisc_homotopy`). In particular the boundary sphere stays
in the sublevel `{f ≤ c - δ²}`. The homotopy is the coordinate deformation
`HasFDerivAt.exists_negativeDisc_homotopy` read through `ψ₀⁻¹`; only a neighbourhood of the
common centre is used, so the whole negative discs of the two charts need not overlap.

The comparison can be made continuously over a compact space `P` of pairs of charts
(`TauCeti.exists_negativeDisc_homotopy_family_of_charts`). If on one common ball about the
origin the inverses of `ψ₀ p` are jointly continuous in `p` and the transitions are
differentiable with jointly continuous derivatives, then the polar factors `h p` depend continuously
on `p`, and one radius `δ` and one homotopy, continuous in `p`, serve the whole family. This is the
coordinate deformation `TauCeti.exists_negativeDisc_homotopy_family` read through `(ψ₀ p)⁻¹`.

The comparison of two charts also holds for charts with values in `ℝⁿ` in the normal form
`f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`, whose negative discs are `w ↦ ψ⁻¹ (w, 0)` with `w ∈ ℝᵏ`
extended by zero along the first `k` coordinates
(`OpenPartialHomeomorph.exists_negativeDisc_homotopy_euclidean`). There the polar factor is that of
the negative block `ι† A ι` of the derivative, where `ι : ℝᵏ → ℝⁿ` is the zero extension. The
proof splits the coordinates as `ℝⁿ ≃ ℝᵏ × ℝⁿ⁻ᵏ` (`EuclideanSpace.sumComplEquivProd`) and uses the
naturality of polar factors under conjugation, which identifies the polar factor of `ι† A ι`
with that of the negative block in the split coordinates
(`EuclideanSpace.polarFactor_adjoint_comp_comp_piLpExtendByZero`). The comparison of compact
families of charts holds in these coordinates as well
(`TauCeti.exists_negativeDisc_homotopy_family_of_charts_euclidean`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Remark 3.3 and Lemma 3.6.
-/

public section

open Set Metric Topology unitInterval
open LinearIsometry (piLpExtendByZero)

namespace OpenPartialHomeomorph

variable {M E F : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
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
    ∃ h : E →ₗᵢ[ℝ] E, ⇑h = ((ContinuousLinearMap.fst ℝ E F).comp
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

/-- In the coordinates of `ℝⁿ` split into the first `k` and the remaining ones, the normal form
`c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²` of a chart reads `c - ‖u‖² + ‖v‖²`. -/
private theorem apply_eq_of_transHomeomorph_sumComplEquivProd
    (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) {f : M → ℝ} {c : ℝ}
    (hψ : ∀ y ∈ ψ.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2) :
    ∀ y ∈ (ψ.transHomeomorph
        (EuclideanSpace.sumComplEquivProd ℝ fun j : Fin n ↦ j.val < k).toHomeomorph).source,
      f y = c - ‖((ψ.transHomeomorph
          (EuclideanSpace.sumComplEquivProd ℝ fun j : Fin n ↦ j.val < k).toHomeomorph) y).1‖ ^ 2 +
        ‖((ψ.transHomeomorph
          (EuclideanSpace.sumComplEquivProd ℝ fun j : Fin n ↦ j.val < k).toHomeomorph) y).2‖ ^ 2 :=
  fun y hy ↦ by
    rw [hψ y hy, EuclideanSpace.sum_ite_neg_one_mul_sq_eq]
    simp only [transHomeomorph_apply, Function.comp_apply, ContinuousLinearEquiv.coe_toHomeomorph]
    ring

/-- In the split coordinates, the point `(w, 0)` of a negative disc is the zero extension of
`w ∈ ℝᵏ` onto the first `k` coordinates of `ℝⁿ`. -/
private theorem transHomeomorph_sumComplEquivProd_symm_finCastLEEquiv
    (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n)
    (w : EuclideanSpace ℝ (Fin k)) :
    (ψ.transHomeomorph
        (EuclideanSpace.sumComplEquivProd ℝ fun j : Fin n ↦ j.val < k).toHomeomorph).symm
        (EuclideanSpace.finCastLEEquiv ℝ hk w, 0) =
      ψ.symm (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk) w) := by
  simp only [transHomeomorph_symm_apply, Function.comp_apply]
  exact congrArg ψ.symm (EuclideanSpace.sumComplEquivProd_symm_finCastLEEquiv hk w)

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
  have hsplit := apply_eq_of_transHomeomorph_sumComplEquivProd (M := M) (n := n) (k := k)
    (f := f) (c := c)
  have hsymm (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) :=
    transHomeomorph_sumComplEquivProd_symm_finCastLEEquiv ψ hk
  set S := EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k)
  set e := EuclideanSpace.finCastLEEquiv ℝ hk
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
  refine ⟨e.trans ((h.toLinearIsometryEquiv rfl).trans e.symm), ?_, δ₀, hδ₀, fun δ hδ ↦ ?_⟩
  · rw [EuclideanSpace.polarFactor_adjoint_comp_comp_piLpExtendByZero]
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
  · simp only [ContinuousMap.coe_mk, hG1, LinearIsometryEquiv.trans_apply,
      LinearIsometry.coe_toLinearIsometryEquiv]
    rw [← hsymm, LinearIsometryEquiv.apply_symm_apply]
  · simpa using hGf t ⟨e w, he w⟩

end Euclidean

end OpenPartialHomeomorph

namespace TauCeti

variable {M E F : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The small negative discs of two compact families of Morse charts are homotopic below the
critical level, continuously in the parameter.** Let `ψ₀ p` and `ψ₁ p` be charts with a common
centre, in which `f = c - ‖u‖² + ‖v‖²`, for `p` in a compact space `P`. Suppose that on one ball
of radius `r` about the origin the inverses of `ψ₀ p` are jointly continuous in `p` and the point,
and the transitions `ψ₀ p ∘ (ψ₁ p)⁻¹` are defined and differentiable with derivatives `D p y`
jointly continuous in `p` and `y`. Then the polar factor `h p` of the negative block of `D p 0`
depends continuously on `p`, and for every small `δ > 0` a single homotopy `G`, continuous in
`p`, deforms the negative discs `w ↦ (ψ₁ p)⁻¹ (w, 0)` of radius `δ` to
`w ↦ (ψ₀ p)⁻¹ (h p w, 0)` through maps `g` with `f (g w) ≤ c - ‖w‖²`. -/
theorem exists_negativeDisc_homotopy_family_of_charts {P : Type*} [TopologicalSpace P]
    [CompactSpace P] (ψ₀ ψ₁ : P → OpenPartialHomeomorph M (E × F)) {f : M → ℝ} {c : ℝ}
    (hf₀ : ∀ p, ∀ y ∈ (ψ₀ p).source, f y = c - ‖(ψ₀ p y).1‖ ^ 2 + ‖(ψ₀ p y).2‖ ^ 2)
    (hf₁ : ∀ p, ∀ y ∈ (ψ₁ p).source, f y = c - ‖(ψ₁ p y).1‖ ^ 2 + ‖(ψ₁ p y).2‖ ^ 2)
    (hp : ∀ p, (ψ₀ p).symm 0 = (ψ₁ p).symm 0) {r : ℝ} (hr : 0 < r)
    (h₀ : ∀ p, ball (0 : E × F) r ⊆ (ψ₀ p).target)
    (h₁ : ∀ p, ball (0 : E × F) r ⊆ (ψ₁ p).target ∩ (ψ₁ p).symm ⁻¹' (ψ₀ p).source)
    (hs₀ : ContinuousOn (fun q : P × (E × F) ↦ (ψ₀ q.1).symm q.2) (univ ×ˢ ball 0 r))
    {D : P → E × F → (E × F) →L[ℝ] E × F}
    (hT : ∀ p, ∀ y ∈ ball (0 : E × F) r, HasFDerivAt (fun z ↦ ψ₀ p ((ψ₁ p).symm z)) (D p y) y)
    (hD : ContinuousOn (Function.uncurry D) (univ ×ˢ ball 0 r)) :
    Continuous (fun p ↦ ((ContinuousLinearMap.fst ℝ E F).comp
        ((D p 0).comp (ContinuousLinearMap.inl ℝ E F))).polarFactor) ∧
      ∃ δ₀ > 0, ∀ δ ∈ Ioc 0 δ₀, ∃ G : C(P × I × closedBall (0 : E) δ, M),
        (∀ p w, G (p, 0, w) = (ψ₁ p).symm ((w : E), 0)) ∧
        (∀ p w, G (p, 1, w) = (ψ₀ p).symm (((ContinuousLinearMap.fst ℝ E F).comp
          ((D p 0).comp (ContinuousLinearMap.inl ℝ E F))).polarFactor w, 0)) ∧
        ∀ p t w, f (G (p, t, w)) ≤ c - ‖(w : E)‖ ^ 2 := by
  have h0r : (0 : E × F) ∈ ball 0 r := mem_ball_self hr
  -- Each transition is a change of coordinates fixing the origin and preserving `Q` on the ball.
  have hT0 (p : P) : ψ₀ p ((ψ₁ p).symm 0) = 0 := by rw [← hp, (ψ₀ p).right_inv (h₀ p h0r)]
  have hQ (p : P) (y : E × F) (hy : y ∈ ball (0 : E × F) r) :
      -‖(ψ₀ p ((ψ₁ p).symm y)).1‖ ^ 2 + ‖(ψ₀ p ((ψ₁ p).symm y)).2‖ ^ 2 =
        -‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 := by
    have h₀' := hf₀ p _ (h₁ p hy).2
    have h₁' := hf₁ p _ ((ψ₁ p).map_target (h₁ p hy).1)
    rw [(ψ₁ p).right_inv (h₁ p hy).1] at h₁'
    linarith
  obtain ⟨hh, δ₀, hδ₀, hH⟩ := exists_negativeDisc_homotopy_family
    (T := fun p z ↦ ψ₀ p ((ψ₁ p).symm z)) hr hT hD hT0 hQ (ball_mem_nhds 0 hr)
  refine ⟨hh, δ₀, hδ₀, fun δ hδ ↦ ?_⟩
  obtain ⟨hdisc, H, hH0, hH1, hHb⟩ := hH δ hδ
  -- Read the coordinate homotopy through the inverses of the charts `ψ₀ p`.
  refine ⟨⟨fun q ↦ (ψ₀ q.1).symm (H q),
    hs₀.comp_continuous (f := fun q : P × I × closedBall (0 : E) δ ↦ (q.1, H q))
      (continuous_fst.prodMk H.continuous) fun q ↦ ⟨mem_univ _, (hHb q.1 q.2.1 q.2.2).1⟩⟩,
    fun p w ↦ ?_, fun p w ↦ ?_, fun p t w ↦ ?_⟩
  · simp only [ContinuousMap.coe_mk, hH0]
    exact (ψ₀ p).left_inv (h₁ p (hdisc w w.2)).2
  · simp only [ContinuousMap.coe_mk, hH1]
  · obtain ⟨hz, hq⟩ := hHb p t w
    simp only [ContinuousMap.coe_mk]
    rw [hf₀ p _ ((ψ₀ p).map_target (h₀ p hz)), (ψ₀ p).right_inv (h₀ p hz)]
    linarith

/-- **The small negative discs of two compact families of Euclidean Morse charts are homotopic
below the critical level, continuously in the parameter.** Let `ψ₀ p` and `ψ₁ p` be charts with
values in `ℝⁿ` and a common centre, in which `f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`, for `p` in a
compact space `P`. Suppose that on one ball of radius `r` about the origin the inverses of `ψ₀ p`
are jointly continuous in `p` and the point, and the transitions `ψ₀ p ∘ (ψ₁ p)⁻¹` are defined and
differentiable with derivatives `D p y` jointly continuous in `p` and `y`. Let `ι : ℝᵏ → ℝⁿ` be the
zero extension onto the first `k` coordinates. Then the polar factor `h p` of the negative block
`ι† (D p 0) ι` depends continuously on `p`, and for every small `δ > 0` a single homotopy `G`,
continuous in `p`, deforms the negative discs `w ↦ (ψ₁ p)⁻¹ (ι w)` of radius `δ` to
`w ↦ (ψ₀ p)⁻¹ (ι (h p w))` through maps `g` with `f (g w) ≤ c - ‖w‖²`. -/
theorem exists_negativeDisc_homotopy_family_of_charts_euclidean {n k : ℕ} {P : Type*}
    [TopologicalSpace P] [CompactSpace P]
    (ψ₀ ψ₁ : P → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n) {f : M → ℝ}
    {c : ℝ}
    (hf₀ : ∀ p, ∀ y ∈ (ψ₀ p).source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ p y j ^ 2)
    (hf₁ : ∀ p, ∀ y ∈ (ψ₁ p).source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ p y j ^ 2)
    (hp : ∀ p, (ψ₀ p).symm 0 = (ψ₁ p).symm 0) {r : ℝ} (hr : 0 < r)
    (h₀ : ∀ p, ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ (ψ₀ p).target)
    (h₁ : ∀ p, ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆
      (ψ₁ p).target ∩ (ψ₁ p).symm ⁻¹' (ψ₀ p).source)
    (hs₀ : ContinuousOn (fun q : P × EuclideanSpace ℝ (Fin n) ↦ (ψ₀ q.1).symm q.2)
      (univ ×ˢ ball 0 r))
    {D : P → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : ∀ p, ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r,
      HasFDerivAt (fun z ↦ ψ₀ p ((ψ₁ p).symm z)) (D p y) y)
    (hD : ContinuousOn (Function.uncurry D) (univ ×ˢ ball 0 r)) :
    Continuous (fun p ↦ (ContinuousLinearMap.adjoint
        (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L D p 0 ∘L
          (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor) ∧
      ∃ δ₀ > 0, ∀ δ ∈ Ioc 0 δ₀,
        ∃ G : C(P × I × closedBall (0 : EuclideanSpace ℝ (Fin k)) δ, M),
          (∀ p w, G (p, 0, w) = (ψ₁ p).symm (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk) w)) ∧
          (∀ p w, G (p, 1, w) = (ψ₀ p).symm (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)
            ((ContinuousLinearMap.adjoint
              (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L D p 0 ∘L
                (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor
              w))) ∧
          ∀ p t w, f (G (p, t, w)) ≤ c - ‖(w : EuclideanSpace ℝ (Fin k))‖ ^ 2 := by
  -- Split the coordinates into the negative factor `j < k` and the positive factor.
  have hsplit (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) :=
    OpenPartialHomeomorph.apply_eq_of_transHomeomorph_sumComplEquivProd ψ (k := k) (f := f) (c := c)
  have hsymm (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) :=
    OpenPartialHomeomorph.transHomeomorph_sumComplEquivProd_symm_finCastLEEquiv ψ hk
  set S := EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k)
  set e := EuclideanSpace.finCastLEEquiv ℝ hk
  -- A ball about the origin of the split coordinates which comes from the ball of radius `r`.
  obtain ⟨r', hr', hr'r⟩ : ∃ r' > 0, ball (0 : _ × _) r' ⊆ S.symm ⁻¹' ball 0 r :=
    Metric.mem_nhds_iff.1 (S.symm.continuous.continuousAt.preimage_mem_nhds
      (by rw [map_zero]; exact ball_mem_nhds 0 hr))
  have hmaps : MapsTo (fun q : P × (EuclideanSpace ℝ {j : Fin n // j.val < k} ×
      EuclideanSpace ℝ {j : Fin n // ¬j.val < k}) ↦ (q.1, S.symm q.2)) (univ ×ˢ ball 0 r')
      (univ ×ˢ ball 0 r) := fun q hq ↦ ⟨mem_univ _, hr'r hq.2⟩
  -- The transitions of the split charts are those of `ψ₀ p, ψ₁ p` conjugated by `S`.
  have hTS (p : P) : (fun z ↦ ((ψ₀ p).transHomeomorph S.toHomeomorph)
      (((ψ₁ p).transHomeomorph S.toHomeomorph).symm z)) =
        S ∘ (fun z ↦ ψ₀ p ((ψ₁ p).symm z)) ∘ S.symm := by
    funext z
    simp
  obtain ⟨hh, δ₀, hδ₀, hG⟩ := exists_negativeDisc_homotopy_family_of_charts
    (fun p ↦ (ψ₀ p).transHomeomorph S.toHomeomorph)
    (fun p ↦ (ψ₁ p).transHomeomorph S.toHomeomorph)
    (fun p ↦ hsplit _ (hf₀ p)) (fun p ↦ hsplit _ (hf₁ p))
    (fun p ↦ by simpa using hp p) hr' (fun p y hy ↦ by simpa using h₀ p (hr'r hy))
    (fun p y hy ↦ by simpa using h₁ p (hr'r hy))
    (hs₀.comp (continuous_fst.prodMk (S.symm.continuous.comp continuous_snd)).continuousOn
      hmaps)
    (D := fun p y ↦ S.toContinuousLinearMap ∘L D p (S.symm y) ∘L S.symm.toContinuousLinearMap)
    (fun p y hy ↦ hTS p ▸ S.hasFDerivAt.comp y ((hT p _ (hr'r hy)).comp y S.symm.hasFDerivAt))
    (continuousOn_const.clm_comp ((hD.comp (continuous_fst.prodMk
      (S.symm.continuous.comp continuous_snd)).continuousOn hmaps).clm_comp continuousOn_const))
  -- The polar factor of `ι† A ι` is that of the negative block in split coordinates, read
  -- through `e`.
  have hpf (p : P) : (ContinuousLinearMap.adjoint
      (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L D p 0 ∘L
        (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor =
      (e.symm : EuclideanSpace ℝ {j : Fin n // j.val < k} →L[ℝ] EuclideanSpace ℝ (Fin k)) ∘L
        ((ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ {j : Fin n // j.val < k})
          (EuclideanSpace ℝ {j : Fin n // ¬j.val < k})).comp
          ((S.toContinuousLinearMap ∘L D p (S.symm 0) ∘L S.symm.toContinuousLinearMap).comp
            (ContinuousLinearMap.inl ℝ _ _))).polarFactor ∘L
        (e : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ {j : Fin n // j.val < k}) := by
    rw [EuclideanSpace.polarFactor_adjoint_comp_comp_piLpExtendByZero, map_zero,
      LinearIsometryEquiv.symm_symm]
  refine ⟨(continuous_const.clm_comp (hh.clm_comp continuous_const)).congr fun p ↦ (hpf p).symm,
    δ₀, hδ₀, fun δ hδ ↦ ?_⟩
  -- Read the split homotopy through `e`, which preserves norms.
  obtain ⟨G, hG0, hG1, hGf⟩ := hG δ hδ
  have he (w : closedBall (0 : EuclideanSpace ℝ (Fin k)) δ) : e w ∈ closedBall 0 δ := by
    rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    exact mem_closedBall_zero_iff.1 w.2
  refine ⟨⟨fun q ↦ G (q.1, q.2.1, ⟨e q.2.2, he q.2.2⟩), by fun_prop⟩, fun p w ↦ ?_,
    fun p w ↦ ?_, fun p t w ↦ ?_⟩
  · simp only [ContinuousMap.coe_mk, hG0, hsymm]
  · simp only [ContinuousMap.coe_mk, hG1, hpf, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [← hsymm, LinearIsometryEquiv.apply_symm_apply]
  · simpa using hGf p t ⟨e w, he w⟩

end TauCeti
