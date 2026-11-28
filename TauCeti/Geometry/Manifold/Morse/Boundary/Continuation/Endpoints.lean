/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Continuation.Signed

/-!
# The integral continuation map does not depend on the endpoints of the slab

Let `f₀` and `f₁` be Morse functions on a compact boundaryless manifold `M`, with pseudo-gradients
`X₀` and `X₁` adapted to them, and orientation data `𝔬₀` and `𝔬₁` orienting their unstable
manifolds. The integral continuation map
`TauCeti.IsAdaptedPseudoGradient.signedContinuationMap` along a diffeomorphism `Φ` of `M` counts
the points of `W^u_{X₀}(p) ∩ Φ⁻¹ (W^s_{X₁}(q))` with signs. For a continuation field `V` from `X₀`
to `X₁`, it is evaluated along the transition diffeomorphism
`TauCeti.continuationTransition C hVs a b` of the slab, for very negative `a` and very positive `b`.
This file shows that the result does not depend on `a` and `b`, so that a continuation field has a
single integral continuation map.

* **Invariance under the end flows.** If `Ψ = Φ_t^{X₁} ∘ Φ ∘ Φ_s^{X₀}` is `Φ` preceded and followed
  by time maps of the flows of `X₀` and `X₁`, the continuation coefficients along `Ψ` and along `Φ`
  agree (`TauCeti.IsAdaptedPseudoGradient.signedContinuationCoeff_eq_of_apply_eq_flow`), and so
  do the continuation maps
  (`TauCeti.IsAdaptedPseudoGradient.signedContinuationMap_eq_of_apply_eq_flow`).
  The flow of `X₀` preserves `W^u_{X₀}(p)` and the flow of `X₁` preserves `W^s_{X₁}(q)`, so
  `Φ_s^{X₀}` carries `W^u_{X₀}(p) ∩ Ψ⁻¹ (W^s_{X₁}(q))` bijectively onto
  `W^u_{X₀}(p) ∩ Φ⁻¹ (W^s_{X₁}(q))`. The sign of a point `y` is that of the comparison map
  `N_q ∘ dΨ_y ∘ F_p` of the unstable frame `F_p` of `p` and the normal coordinates `N_q` of
  `W^s_{X₁}(q)`. Along the flows the unstable frame is multiplied by `e^{s}` and the normal
  coordinates by `e^{t}` (`TauCeti.IsAdaptedPseudoGradient.unstableFrame_flow`,
  `TauCeti.IsAdaptedPseudoGradient.stableNormal_mfderiv_flow`), so the comparison map at `y` is
  `e^{s + t}` times the comparison map of `Φ` at `Φ_s^{X₀} y`, and has the same sign
  (`Orientation.linearMapSign_smul_of_pos`).
* **Flow maps alone.** Along the identity of `M` the integral continuation map is the signed pair
  map of `(X₀, X₁)` (`TauCeti.IsAdaptedPseudoGradient.signedContinuationMap_refl`), so by the
  invariance it is that map along every composite `Φ_t^{X₁} ∘ Φ_s^{X₀}` of time maps of the two
  flows
  (`TauCeti.IsAdaptedPseudoGradient.signedContinuationMap_eq_signedPairMap_of_apply_eq_flow`). For
  a single Morse–Smale pseudo-gradient with the same orientation data at both ends this is the
  identity
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.signedContinuationMap_eq_id_of_coe_eq_flow`), the
  input of the constant-path identity in
  `TauCeti.Geometry.Manifold.Morse.Boundary.Continuation.Constant`.
* **Independence of the endpoints.** For a smooth continuation field at rate `C > 0`, moving the
  endpoints of the slab further out composes the transition diffeomorphism with the end flows
  (`TauCeti.IsContinuationField.eventually_continuationTransition_apply_eq_flow`). So for all
  sufficiently negative `a₀` and sufficiently positive `b₀`, the integral continuation map along the
  transition diffeomorphism from `a` to `b` is the one from `a₀` to `b₀` whenever `a ≤ a₀` and
  `b₀ ≤ b`
  (`TauCeti.IsContinuationField.eventually_signedContinuationMap_continuationTransition_eq`).

## Main results

* `TauCeti.IsAdaptedPseudoGradient.signedContinuationCoeff_eq_of_apply_eq_flow`,
  `TauCeti.IsAdaptedPseudoGradient.signedContinuationMap_eq_of_apply_eq_flow`: the integral
  continuation coefficients and maps are invariant under the end flows.
* `TauCeti.IsAdaptedPseudoGradient.signedContinuationCoeff_refl`,
  `TauCeti.IsAdaptedPseudoGradient.signedContinuationMap_refl`: along the identity, they are the
  signed pair coefficients and map.
* `TauCeti.IsAdaptedPseudoGradient.signedContinuationCoeff_eq_signedPairCoeff_of_apply_eq_flow`,
  `TauCeti.IsAdaptedPseudoGradient.signedContinuationMap_eq_signedPairMap_of_apply_eq_flow`: the
  same along composites of time maps of the two flows.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.signedContinuationMap_eq_id_of_coe_eq_flow`: along
  a flow map of a Morse–Smale pseudo-gradient, the integral continuation map is the identity.
* `TauCeti.IsContinuationField.eventually_signedContinuationCoeff_continuationTransition_eq`,
  `TauCeti.IsContinuationField.eventually_signedContinuationMap_continuationTransition_eq`: for a
  continuation field, they do not depend on the endpoints of the slab once these are far enough
  out.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1 (continuation maps, defined by a time-dependent
  pseudo-gradient which agrees with the two ends outside a compact time interval).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 6 (invariance of Morse homology by continuation).
-/

public section

open Filter Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f₀ f₁ : M → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

/-! ### Signed counts read in the charts at `q` -/

section Transported

variable (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)
  (𝔬₀ : MorseOrientation f₀ X₀) (𝔬₁ : MorseOrientation f₁ X₁)

/-- The comparison map at `y` along a map `Θ` of `M`: the normal coordinates of `W^s_{X₁}(q)` at
`Θ y`, in the chart of `𝔬₁` at `q`, of the image under `dΘ_y` of the unstable frame of `p` at `y`,
in the chart of `𝔬₀` at `p`. -/
private noncomputable def transportedComparison (Θ : M → M) (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (y : M) :
    ({i // (𝔬₀.chart p).weight i < 0} → ℝ) →L[ℝ] ({i // (𝔬₁.chart q).weight i < 0} → ℝ) :=
  (hX₁.stableNormal (𝔬₁.chart q) (Θ y)).comp
    ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Θ y).comp (hX₀.unstableFrame (𝔬₀.chart p) y))

/-- The comparison map along `Θ` applied to a vector. -/
private theorem transportedComparison_apply (Θ : M → M) (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (y : M) (c : {i // (𝔬₀.chart p).weight i < 0} → ℝ) :
    transportedComparison hX₀ hX₁ 𝔬₀ 𝔬₁ Θ p q y c =
      hX₁.stableNormal (𝔬₁.chart q) (Θ y)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Θ y (hX₀.unstableFrame (𝔬₀.chart p) y c)) :=
  rfl

/-- The number of points `y` of `W^u_{X₀}(p) ∩ Θ⁻¹ (W^s_{X₁}(q))` counted with the signs of their
comparison maps `transportedComparison`. For a diffeomorphism `Θ` and `ind p = ind q` it is the
continuation coefficient along `Θ`, read in the chart of `𝔬₁` at `q` rather than in its pullback
along `Θ` at `Θ⁻¹ q`. -/
private noncomputable def transportedCount (Θ : M → M) (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q) : ℤ :=
  ∑ᶠ y ∈ hX₀.flow.unstableSet p ∩ Θ ⁻¹' hX₁.flow.stableSet q,
    (𝔬₀.orientation p).linearMapSign
      (Orientation.reindex ℝ _ (finCongr hpq.symm) (𝔬₁.orientation q))
      (transportedComparison hX₀ hX₁ 𝔬₀ 𝔬₁ Θ p q y).toLinearMap

/-- The continuation coefficient along a diffeomorphism `Φ`, between critical points of the same
index, is the signed count read in the chart of `𝔬₁` at `q`. -/
private theorem signedContinuationCoeff_eq_transportedCount
    (Φ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M) {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁}
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q) :
    hX₀.signedContinuationCoeff hX₁ 𝔬₀ 𝔬₁ Φ p q = transportedCount hX₀ hX₁ 𝔬₀ 𝔬₁ Φ p q hpq := by
  set e := criticalPointsEquivOfComp (σ := Φ) (f' := f₁) rfl
  have hΦ := Φ.mfderiv_apply_mpullback (by simp) X₁
  -- For a critical point `r` of `f₁ ∘ Φ`, the signed count in the chart of `𝔬₁` at `e r`, pulled
  -- back along `Φ`, is the count read in that chart through `dΦ`.
  have key : ∀ (r : criticalPoints 𝓘(ℝ, E) (f₁ ∘ Φ))
      (h : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) (f₁ ∘ Φ) r)
      (h' : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ (e r)),
      hX₀.signedPairCount (hX₁.mpullback Φ) (𝔬₀.chart p) ((𝔬₁.pullback rfl hΦ).chart r)
          (𝔬₀.orientation p) ((𝔬₁.pullback rfl hΦ).orientation r) h =
        transportedCount hX₀ hX₁ 𝔬₀ 𝔬₁ Φ p (e r) h' := by
    intro r h h'
    have hset : (hX₁.mpullback Φ).flow.stableSet r = Φ ⁻¹' hX₁.flow.stableSet (e r) :=
      (preimage_stableSet_diffeomorph (hX₁.mpullback Φ) hX₁ hΦ r).symm
    rw [signedPairCount_def, transportedCount, hset]
    refine finsum_mem_congr rfl fun y hy ↦ ?_
    have hy' : y ∈ (hX₁.mpullback Φ).flow.stableSet r := by
      rw [hset]
      exact hy.2
    rw [pairSign_def, MorseOrientation.pullback_orientation]
    refine congrArg₂ (fun o L ↦ (𝔬₀.orientation p).linearMapSign o L)
      (Orientation.reindex_finCongr_reindex_finCongr _ _ _) (LinearMap.ext fun v ↦ ?_)
    -- The two sides differ in the type of their targets only up to unfolding the pullback.
    exact (pairComparison_apply _ _ _ _ y v).trans
      ((stableNormal_pullback_apply rfl (hX₁.mpullback Φ) hX₁ hΦ
        (𝔬₁.coord_mfderiv_chart (e r)) hy' _).trans
          (transportedComparison_apply hX₀ hX₁ 𝔬₀ 𝔬₁ Φ p (e r) y v).symm)
  have hind := (𝔬₁.chart q).manifoldMorseIndex_criticalPointsEquivOfComp_symm (σ := Φ) rfl
  rw [signedContinuationCoeff_def, signedPairCoeff_of_morseIndex_eq (hpq.trans hind.symm),
    key _ _ (by rwa [Equiv.apply_symm_apply])]
  -- The count is read in the chart of `𝔬₁` at `e (e⁻¹ q)`, which is the critical point `q`.
  have key' : ∀ (c : criticalPoints 𝓘(ℝ, E) f₁) (_ : c = q)
      (h : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ c),
      transportedCount hX₀ hX₁ 𝔬₀ 𝔬₁ Φ p c h = transportedCount hX₀ hX₁ 𝔬₀ 𝔬₁ Φ p q hpq := by
    rintro c rfl h
    rfl
  exact key' _ (Equiv.apply_symm_apply _ _) _

/-- The time-`s` map of the flow of `X₀` carries `W^u_{X₀}(p) ∩ Ψ⁻¹ (W^s_{X₁}(q))` onto
`W^u_{X₀}(p) ∩ Φ⁻¹ (W^s_{X₁}(q))`, for `Ψ = Φ_t^{X₁} ∘ Φ ∘ Φ_s^{X₀}`. -/
private theorem image_flow_unstableSet_inter_preimage_stableSet (Φ : M → M) (s t : ℝ) (p q : M) :
    hX₀.flow s '' (hX₀.flow.unstableSet p ∩
      (hX₁.flow t ∘ Φ ∘ hX₀.flow s) ⁻¹' hX₁.flow.stableSet q) =
      hX₀.flow.unstableSet p ∩ Φ ⁻¹' hX₁.flow.stableSet q := by
  have hinv (z : M) : hX₀.flow s (hX₀.flow (-s) z) = z := by
    rw [← Flow.map_add]
    simp
  ext z
  simp only [mem_image, mem_inter_iff, mem_preimage, comp_apply, Flow.apply_mem_stableSet_iff]
  refine ⟨?_, fun hz ↦ ⟨hX₀.flow (-s) z, ?_, hinv z⟩⟩
  · rintro ⟨y, ⟨hyu, hys⟩, rfl⟩
    exact ⟨(Flow.apply_mem_unstableSet_iff _ _).2 hyu, hys⟩
  · rw [hinv z]
    exact ⟨(Flow.apply_mem_unstableSet_iff _ _).2 hz.1, hz.2⟩

/-- **The comparison maps along the end flows.** At a point `y` of `W^u_{X₀}(p)` with
`Φ (Φ_s^{X₀} y) ∈ W^s_{X₁}(q)`, the comparison map along `Ψ = Φ_t^{X₁} ∘ Φ ∘ Φ_s^{X₀}` is
`e^{s + t}` times the comparison map along `Φ` at `Φ_s^{X₀} y`: the flows multiply the unstable
frame by `e^{s}` and the normal coordinates by `e^{t}`. -/
private theorem transportedComparison_flow_comp (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (Φ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M) (s t : ℝ) {p : criticalPoints 𝓘(ℝ, E) f₀}
    {q : criticalPoints 𝓘(ℝ, E) f₁} {y : M} (hy : y ∈ hX₀.flow.unstableSet p)
    (hz : Φ (hX₀.flow s y) ∈ hX₁.flow.stableSet q) :
    transportedComparison hX₀ hX₁ 𝔬₀ 𝔬₁ (hX₁.flow t ∘ Φ ∘ hX₀.flow s) p q y =
      Real.exp (s + t) • transportedComparison hX₀ hX₁ 𝔬₀ 𝔬₁ Φ p q (hX₀.flow s y) := by
  set z := hX₀.flow s y
  obtain ⟨Tp, hTp⟩ :=
    (hX₀.eventually_mem_linearBackwardTimes (𝔬₀.coord_mfderiv_chart p) hf₀ hy).exists
  obtain ⟨Tq, hTq⟩ := (hX₁.eventually_mem_linearForwardTimes (𝔬₁.coord_mfderiv_chart q) hz).exists
  -- The chain rule for the composite of the two time maps with `Φ`.
  have hd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (hX₁.flow t ∘ Φ ∘ hX₀.flow s) y =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (hX₁.flow t) (Φ z)).comp
        ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ z).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (hX₀.flow s) y)) := by
    rw [mfderiv_comp y (((hX₁.contMDiff_flow_apply t).mdifferentiable (by simp)) _)
        ((Φ.mdifferentiable (by simp) _).comp y
          (((hX₀.contMDiff_flow_apply s).mdifferentiable (by simp)) _)),
      mfderiv_comp y (Φ.mdifferentiable (by simp) _)
        (((hX₀.contMDiff_flow_apply s).mdifferentiable (by simp)) _)]
    simp only [comp_apply, z]
  refine ContinuousLinearMap.ext fun c ↦ ?_
  have hF : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (hX₀.flow s) y (hX₀.unstableFrame (𝔬₀.chart p) y c) =
      Real.exp s • hX₀.unstableFrame (𝔬₀.chart p) z c := by
    rw [unstableFrame_flow (𝔬₀.coord_mfderiv_chart p) hTp s c]
    simp [smul_smul, ← Real.exp_add]
  simp only [transportedComparison_apply, smul_apply, hd, ContinuousLinearMap.comp_apply,
    comp_apply]
  rw [hF, stableNormal_mfderiv_flow (𝔬₁.coord_mfderiv_chart q) hTq]
  simp [smul_smul, ← Real.exp_add, add_comm]

/-- **The signed count is invariant under the end flows**: it is the same along
`Φ_t^{X₁} ∘ Φ ∘ Φ_s^{X₀}` as along `Φ`. -/
private theorem transportedCount_flow_comp (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (Φ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M) (s t : ℝ) (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q) :
    transportedCount hX₀ hX₁ 𝔬₀ 𝔬₁ (hX₁.flow t ∘ Φ ∘ hX₀.flow s) p q hpq =
      transportedCount hX₀ hX₁ 𝔬₀ 𝔬₁ Φ p q hpq := by
  rw [transportedCount, transportedCount,
    ← image_flow_unstableSet_inter_preimage_stableSet hX₀ hX₁ Φ s t p q,
    finsum_mem_image (g := hX₀.flow s) (hX₀.flow.toHomeomorph s).injective.injOn]
  refine finsum_mem_congr rfl fun y hy ↦ ?_
  simp only [mem_inter_iff, mem_preimage, comp_apply] at hy
  rw [transportedComparison_flow_comp hX₀ hX₁ 𝔬₀ 𝔬₁ hf₀ Φ s t hy.1
      ((Flow.apply_mem_stableSet_iff _ _).1 hy.2), ContinuousLinearMap.toLinearMap_smul,
    Orientation.linearMapSign_smul_of_pos (Real.exp_pos _)]

/-- **Along the identity, the signed count is that of the pair.** Read along the identity of `M`,
the comparison maps are those of the pair `(X₀, X₁)`, so the signed count in the chart of `𝔬₁` at
`q` is the signed count of `W^u_{X₀}(p) ∩ W^s_{X₁}(q)`. -/
private theorem transportedCount_id (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q) :
    transportedCount hX₀ hX₁ 𝔬₀ 𝔬₁ id p q hpq =
      hX₀.signedPairCount hX₁ (𝔬₀.chart p) (𝔬₁.chart q) (𝔬₀.orientation p) (𝔬₁.orientation q)
        hpq := by
  rw [transportedCount, signedPairCount_def, preimage_id]
  refine finsum_mem_congr rfl fun y _ ↦ ?_
  rw [pairSign_def]
  refine congrArg (fun L ↦ (𝔬₀.orientation p).linearMapSign _ L) (LinearMap.ext fun v ↦ ?_)
  simp [transportedComparison_apply, mfderiv_id]

end Transported

/-! ### Invariance under the end flows -/

section Flow

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  (𝔬₀ : MorseOrientation f₀ X₀) (𝔬₁ : MorseOrientation f₁ X₁)

/-- **The integral continuation coefficients are invariant under the end flows.** If the
diffeomorphism `Ψ` is `Φ` preceded by the time-`s` map of the flow of `X₀` and followed by the
time-`t` map of the flow of `X₁`, then the coefficients of the integral continuation maps along `Ψ`
and along `Φ` agree. -/
theorem signedContinuationCoeff_eq_of_apply_eq_flow (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    {Φ Ψ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {s t : ℝ}
    (hΨ : ∀ x, Ψ x = hX₁.flow t (Φ (hX₀.flow s x))) (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) :
    hX₀.signedContinuationCoeff hX₁ 𝔬₀ 𝔬₁ Ψ p q = hX₀.signedContinuationCoeff hX₁ 𝔬₀ 𝔬₁ Φ p q := by
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q
  · rw [signedContinuationCoeff_eq_transportedCount hX₀ hX₁ 𝔬₀ 𝔬₁ Ψ hpq,
      signedContinuationCoeff_eq_transportedCount hX₀ hX₁ 𝔬₀ 𝔬₁ Φ hpq,
      show ⇑Ψ = hX₁.flow t ∘ Φ ∘ hX₀.flow s from funext hΨ,
      transportedCount_flow_comp hX₀ hX₁ 𝔬₀ 𝔬₁ hf₀ Φ s t p q hpq]
  · rw [signedContinuationCoeff_eq_zero_of_morseIndex_ne 𝔬₀ 𝔬₁ hpq,
      signedContinuationCoeff_eq_zero_of_morseIndex_ne 𝔬₀ 𝔬₁ hpq]

/-- **The integral continuation map is invariant under the end flows.** If the diffeomorphism `Ψ`
is `Φ` preceded by the time-`s` map of the flow of `X₀` and followed by the time-`t` map of the
flow of `X₁`, then the integral continuation maps along `Ψ` and along `Φ` agree, with coefficients
in any ring. -/
theorem signedContinuationMap_eq_of_apply_eq_flow (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hf₁ : IsMorse 𝓘(ℝ, E) f₁) {Φ Ψ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {s t : ℝ}
    (hΨ : ∀ x, Ψ x = hX₁.flow t (Φ (hX₀.flow s x))) (R : Type*) [Ring R] :
    hX₀.signedContinuationMap hX₁ 𝔬₀ 𝔬₁ Ψ hf₁ R = hX₀.signedContinuationMap hX₁ 𝔬₀ 𝔬₁ Φ hf₁ R :=
  Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ by
    simp [signedContinuationCoeff_eq_of_apply_eq_flow 𝔬₀ 𝔬₁ hf₀ hΨ]

/-- **Along the identity, the integral continuation coefficients are the signed pair counts**: the
coefficient of `q` in the image of `p` counts the points of `W^u_{X₀}(p) ∩ W^s_{X₁}(q)` with their
signs. -/
@[simp]
theorem signedContinuationCoeff_refl (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) :
    hX₀.signedContinuationCoeff hX₁ 𝔬₀ 𝔬₁ (Diffeomorph.refl 𝓘(ℝ, E) M ∞) p q =
      hX₀.signedPairCoeff hX₁ 𝔬₀ 𝔬₁ p q := by
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q
  · rw [signedContinuationCoeff_eq_transportedCount hX₀ hX₁ 𝔬₀ 𝔬₁ _ hpq, Diffeomorph.coe_refl,
      transportedCount_id, signedPairCoeff_of_morseIndex_eq hpq]
  · rw [signedContinuationCoeff_eq_zero_of_morseIndex_ne 𝔬₀ 𝔬₁ hpq,
      signedPairCoeff_eq_zero_of_morseIndex_ne hpq]

/-- **Along the identity, the integral continuation map is the signed pair map** of `(X₀, X₁)`,
with coefficients in any ring. -/
@[simp]
theorem signedContinuationMap_refl (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (R : Type*) [Ring R] :
    hX₀.signedContinuationMap hX₁ 𝔬₀ 𝔬₁ (Diffeomorph.refl 𝓘(ℝ, E) M ∞) hf₁ R =
      hX₀.signedPairMap hX₁ 𝔬₀ 𝔬₁ hf₁ R :=
  Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ by simp

/-- **Along the end flows alone, the integral continuation coefficients are the signed pair
counts.** If the diffeomorphism `Ψ` is the time-`s` map of the flow of `X₀` followed by the
time-`t` map of the flow of `X₁`, the coefficient of `q` in the image of `p` along `Ψ` counts the
points of `W^u_{X₀}(p) ∩ W^s_{X₁}(q)` with their signs. -/
theorem signedContinuationCoeff_eq_signedPairCoeff_of_apply_eq_flow (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    {Ψ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {s t : ℝ} (hΨ : ∀ x, Ψ x = hX₁.flow t (hX₀.flow s x))
    (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁) :
    hX₀.signedContinuationCoeff hX₁ 𝔬₀ 𝔬₁ Ψ p q = hX₀.signedPairCoeff hX₁ 𝔬₀ 𝔬₁ p q := by
  rw [signedContinuationCoeff_eq_of_apply_eq_flow 𝔬₀ 𝔬₁ hf₀ (Φ := Diffeomorph.refl 𝓘(ℝ, E) M ∞)
    hΨ, signedContinuationCoeff_refl]

/-- **Along the end flows alone, the integral continuation map is the signed pair map.** If the
diffeomorphism `Ψ` is the time-`s` map of the flow of `X₀` followed by the time-`t` map of the
flow of `X₁`, the integral continuation map along `Ψ` is the signed pair map of `(X₀, X₁)`, with
coefficients in any ring. -/
theorem signedContinuationMap_eq_signedPairMap_of_apply_eq_flow (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hf₁ : IsMorse 𝓘(ℝ, E) f₁) {Ψ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {s t : ℝ}
    (hΨ : ∀ x, Ψ x = hX₁.flow t (hX₀.flow s x)) (R : Type*) [Ring R] :
    hX₀.signedContinuationMap hX₁ 𝔬₀ 𝔬₁ Ψ hf₁ R = hX₀.signedPairMap hX₁ 𝔬₀ 𝔬₁ hf₁ R := by
  rw [signedContinuationMap_eq_of_apply_eq_flow 𝔬₀ 𝔬₁ hf₀ hf₁
    (Φ := Diffeomorph.refl 𝓘(ℝ, E) M ∞) hΨ, signedContinuationMap_refl]

/-- **Along a flow map of a Morse–Smale pseudo-gradient, the integral continuation map is the
identity**, with the same orientation data at both ends and coefficients in any ring: a critical
point counts once in its own image, and not at all in the image of another critical point. -/
theorem IsMorseSmale.signedContinuationMap_eq_id_of_coe_eq_flow
    {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) (𝔬 : MorseOrientation f X)
    {Ψ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {t : ℝ} (hΨ : ⇑Ψ = hX.flow t)
    (R : Type*) [Ring R] : hX.signedContinuationMap hX 𝔬 𝔬 Ψ hf R = LinearMap.id := by
  rw [signedContinuationMap_eq_signedPairMap_of_apply_eq_flow 𝔬 𝔬 hf hf (s := 0) (t := t)
    (fun x ↦ by rw [hΨ, Flow.map_zero_apply]), h.signedPairMap_self hf]

end Flow

end IsAdaptedPseudoGradient

/-! ### Independence of the endpoints of the slab -/

namespace IsContinuationField

variable {C : ℝ} {V : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}
  (hV : IsContinuationField X₀ X₁ C V) (hX₀ : IsAdaptedPseudoGradient f₀ X₀)
  (hX₁ : IsAdaptedPseudoGradient f₁ X₁) (hC : 0 < C)
  (hVs : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)).tangent ∞
    fun z ↦ (⟨z, V z⟩ : TangentBundle (𝓘(ℝ, E).prod 𝓘(ℝ)) (M × ℝ)))
  (𝔬₀ : MorseOrientation f₀ X₀) (𝔬₁ : MorseOrientation f₁ X₁)
include hV hC

/-- **The integral continuation coefficients do not depend on the endpoints of the slab.** For a
smooth continuation field from `X₀` to `X₁` at rate `C > 0`, with `f₀` Morse, and any orientation
data, for all sufficiently negative `a₀` and sufficiently positive `b₀` the coefficients of the
integral continuation map along the transition diffeomorphism from `a` to `b` are those from `a₀`
to `b₀`, for all `a ≤ a₀` and `b ≥ b₀`. -/
theorem eventually_signedContinuationCoeff_continuationTransition_eq
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀) :
    ∀ᶠ a₀ in atBot, ∀ᶠ b₀ in atTop, ∀ a ≤ a₀, ∀ b, b₀ ≤ b →
      ∀ p q, hX₀.signedContinuationCoeff hX₁ 𝔬₀ 𝔬₁ (continuationTransition C hVs a b) p q =
        hX₀.signedContinuationCoeff hX₁ 𝔬₀ 𝔬₁ (continuationTransition C hVs a₀ b₀) p q := by
  filter_upwards [hV.eventually_continuationTransition_apply_eq_flow hX₀ hX₁ hC hVs] with a₀ ha₀
  filter_upwards [ha₀] with b₀ hb₀ a ha b hb p q
  exact IsAdaptedPseudoGradient.signedContinuationCoeff_eq_of_apply_eq_flow 𝔬₀ 𝔬₁ hf₀
    (hb₀ a ha b hb) p q

/-- **The integral continuation map does not depend on the endpoints of the slab.** For a smooth
continuation field from `X₀` to `X₁` at rate `C > 0`, between pseudo-gradients adapted to Morse
functions, and any orientation data, for all sufficiently negative `a₀` and sufficiently positive
`b₀` the integral continuation map along the transition diffeomorphism from `a` to `b`, with
coefficients in any ring, is the one from `a₀` to `b₀`, for all `a ≤ a₀` and `b ≥ b₀`. -/
theorem eventually_signedContinuationMap_continuationTransition_eq (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (R : Type*) [Ring R] :
    ∀ᶠ a₀ in atBot, ∀ᶠ b₀ in atTop, ∀ a ≤ a₀, ∀ b, b₀ ≤ b →
      hX₀.signedContinuationMap hX₁ 𝔬₀ 𝔬₁ (continuationTransition C hVs a b) hf₁ R =
        hX₀.signedContinuationMap hX₁ 𝔬₀ 𝔬₁ (continuationTransition C hVs a₀ b₀) hf₁ R := by
  filter_upwards [hV.eventually_continuationTransition_apply_eq_flow hX₀ hX₁ hC hVs] with a₀ ha₀
  filter_upwards [ha₀] with b₀ hb₀ a ha b hb
  exact IsAdaptedPseudoGradient.signedContinuationMap_eq_of_apply_eq_flow 𝔬₀ 𝔬₁ hf₀ hf₁
    (hb₀ a ha b hb) R

end IsContinuationField

end TauCeti
