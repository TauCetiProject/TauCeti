/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent.Orientation
public import TauCeti.Geometry.Manifold.Morse.Boundary.Continuation.Signed
public import TauCeti.Geometry.Manifold.Morse.Boundary.Pair.ExtremeIndex
public import TauCeti.Geometry.Manifold.Morse.Boundary.PullbackSign

/-!
# Integral continuation coefficients at critical points of extreme index

Let `X₀` and `X₁` be pseudo-gradients adapted to Morse functions `f₀` and `f₁` on a compact
boundaryless manifold `M` of dimension `n`, with orientation data `𝔬₀` and `𝔬₁`. The integral
continuation map along a diffeomorphism `Φ` of `M`
(`TauCeti.IsAdaptedPseudoGradient.signedContinuationMap`) is the signed pair map of the pair
`(X₀, Φ^* X₁)`, for the orientation data `𝔬₁` pulled back along `Φ`. This file evaluates its
coefficients between critical points of index `0` and between critical points of top index, through
the formulas of `TauCeti.Geometry.Manifold.Morse.Boundary.Pair.ExtremeIndex`.

The signs of `𝔬₁` pulled back along `Φ` are those of `𝔬₁`
(`TauCeti.Geometry.Manifold.Morse.Boundary.PullbackSign`), the fundamental signs as long as `Φ`
preserves the orientation of `M`.

* **Index `0`.** The coefficient of `q` in the image of `p` is
  `𝔬₀.augmentationSign p * 𝔬₁.augmentationSign q` when `Φ p` lies in `W^s_{X₁}(q)`, and `0`
  otherwise (`TauCeti.IsAdaptedPseudoGradient.signedContinuationCoeff_of_morseIndex_eq_zero`).
* **Index `n`.** If `Φ` preserves an orientation `oM` of `M` at `Φ⁻¹ q`, the coefficient is the
  product of the fundamental signs of `p` and `q` for `oM` when `Φ⁻¹ q` lies in `W^u_{X₀}(p)`, and
  `0` otherwise
  (`TauCeti.IsAdaptedPseudoGradient.signedContinuationCoeff_of_morseIndex_eq_finrank`). The
  transition diffeomorphisms of a field on `M × ℝ` preserve every orientation of `M`
  (`TauCeti.isOrientationPreservingAt_continuationTransition`), being time maps of a
  time-dependent flow (`TauCeti.isOrientationPreservingAt_timeDependentFlowOf`).

**Dimension one.** On an oriented manifold of dimension `1` every critical point has index `0` or
`1`. For a smooth continuation field `V` at rate `C > 0` and the transition diffeomorphisms from
very negative `a` to very positive `b`, the points counted by the continuation coefficients are
those counted by the mod-two continuation map
(`TauCeti.IsContinuationField.eventually_morseContinuationCoeff_eq_ncard_inter_preimage`), and
there is at most one of them. So the integral continuation coefficient of `q` in the image of `p`
is the mod-two coefficient, read as `0` or `1`, weighted by the signs of `p` and `q`
(`TauCeti.IsContinuationField.eventually_signedContinuationCoeff_eq_of_finrank_eq_one`). In
particular, if both ends carry the same pseudo-gradient and orientation data and the mod-two
continuation map is the identity, so is the integral continuation map, over every ring
(`TauCeti.IsContinuationField.eventually_signedContinuationMap_eq_id_of_finrank_eq_one`). This is
the integral form of the half-turn of the circle continuation examples, whose mod-two continuation
map is the identity in fixed bases
(`TauCeti.morseContinuationMap_circleCylinderField_add_pi_eq_id`); that the field
`TauCeti.circleCylinderField` of that example is a smooth continuation field between adapted
pseudo-gradients is not proved here.

## Main results

* `TauCeti.isOrientationPreservingAt_continuationTransition`: transition diffeomorphisms preserve
  orientations.
* `TauCeti.IsAdaptedPseudoGradient.signedContinuationCoeff_of_morseIndex_eq_zero`,
  `TauCeti.IsAdaptedPseudoGradient.signedContinuationCoeff_of_morseIndex_eq_finrank`: the integral
  continuation coefficients at the extreme indices.
* `TauCeti.IsContinuationField.eventually_signedContinuationCoeff_eq_of_finrank_eq_one`: the
  integral continuation coefficients in dimension one.
* `TauCeti.IsContinuationField.eventually_signedContinuationMap_eq_id_of_finrank_eq_one`: in
  dimension one, an integral continuation map whose mod-two reduction is the identity is the
  identity.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1 (continuation maps over `ℤ`).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 6 (invariance of Morse homology by continuation).
-/

public section

open Filter Function Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]

/-! ### Transition diffeomorphisms preserve orientations -/

variable {C : ℝ} {V : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}

omit [FiniteDimensional ℝ E] in
/-- **The transition diffeomorphisms of a field on `M × ℝ` preserve orientations.** They are time
maps of the time-dependent flow of the space component of the field. -/
theorem isOrientationPreservingAt_continuationTransition [FiniteDimensional ℝ E]
    (hVs : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)).tangent ∞
      fun z ↦ (⟨z, V z⟩ : TangentBundle (𝓘(ℝ, E).prod 𝓘(ℝ)) (M × ℝ)))
    {ι : Type*} [Fintype ι] (o : Manifold.Orientation 𝓘(ℝ, E) M ι) (a b : ℝ) (x : M) :
    o.IsOrientationPreservingAt o (continuationTransition C hVs a b) x := by
  have hY : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E).tangent 1
      fun p : ℝ × M ↦ (⟨p.2, continuationSpaceField C V p.1 p.2⟩ : TangentBundle 𝓘(ℝ, E) M) :=
    (contMDiff_continuationSpaceField hVs).of_le (by simp)
  rw [coe_continuationTransition]
  exact isOrientationPreservingAt_timeDependentFlowOf
    (isCompleteVectorField_timeDependentSuspensionField_of_compactSpace hY) hY o a b x

/-! ### Integral continuation coefficients at extreme indices -/

namespace IsAdaptedPseudoGradient

variable {f₀ f₁ : M → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)
  (𝔬₀ : MorseOrientation f₀ X₀) (𝔬₁ : MorseOrientation f₁ X₁)
  (Φ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M)

open scoped Classical in
/-- **Integral continuation coefficients at a critical point of index `0`.** The unstable
manifold of a critical point `p` of index `0` is the point `p`, so the coefficient of a critical
point `q` in the image of `p` under the integral continuation map along `Φ` is the product of the
augmentation signs of `p` and `q` when `Φ` carries `p` into `W^s_{X₁}(q)`, and `0` otherwise. Both
sides vanish unless `q` has index `0`. -/
theorem signedContinuationCoeff_of_morseIndex_eq_zero (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    {p : criticalPoints 𝓘(ℝ, E) f₀} {q : criticalPoints 𝓘(ℝ, E) f₁}
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = 0) :
    hX₀.signedContinuationCoeff hX₁ 𝔬₀ 𝔬₁ Φ p q =
      if Φ p ∈ hX₁.flow.stableSet q then 𝔬₀.augmentationSign p * 𝔬₁.augmentationSign q
      else 0 := by
  rw [signedContinuationCoeff_def, signedPairCoeff_of_morseIndex_eq_zero 𝔬₀ _ hf₀ hp]
  rw [hX₁.stableSet_mpullback Φ]
  simp only [coe_criticalPointsEquivOfComp_symm_apply, Diffeomorph.apply_symm_apply, mem_preimage,
    MorseOrientation.augmentationSign_pullback, Equiv.apply_symm_apply]

open scoped Classical in
/-- **Integral continuation coefficients at a critical point of top index.** The stable
manifold of a critical point `q` of index `n = dim M` is the point `q`. So if `Φ` preserves an
orientation `oM` of `M` at `Φ⁻¹ q`, the coefficient of `q` in the image of a critical point `p`
under the integral continuation map along `Φ` is the product of the fundamental signs of `p` and
`q` for `oM` when `Φ⁻¹ q` lies in `W^u_{X₀}(p)`, and `0` otherwise. Both sides vanish unless `p`
has index `n`. -/
theorem signedContinuationCoeff_of_morseIndex_eq_finrank (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E)))
    {p : criticalPoints 𝓘(ℝ, E) f₀} {q : criticalPoints 𝓘(ℝ, E) f₁}
    (hΦ : oM.IsOrientationPreservingAt oM Φ (Φ.symm q))
    (hq : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = finrank ℝ E) :
    hX₀.signedContinuationCoeff hX₁ 𝔬₀ 𝔬₁ Φ p q =
      if Φ.symm q ∈ hX₀.flow.unstableSet p then
        hX₀.fundamentalSign 𝔬₀ oM p * hX₁.fundamentalSign 𝔬₁ oM q
      else 0 := by
  rw [signedContinuationCoeff_def, signedPairCoeff_of_morseIndex_eq_finrank 𝔬₀ _ hf₀ oM
    (((𝔬₁.chart q).manifoldMorseIndex_criticalPointsEquivOfComp_symm (σ := Φ) rfl).trans hq),
    fundamentalSign_pullback rfl _ 𝔬₁ (hX' := hX₁) hf₁ oM oM hΦ]
  simp only [coe_criticalPointsEquivOfComp_symm_apply, Equiv.apply_symm_apply]

end IsAdaptedPseudoGradient

/-! ### Integral continuation maps on oriented one-dimensional manifolds -/

namespace IsContinuationField

variable {f₀ f₁ : M → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)
  (hVs : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)).tangent ∞
    fun z ↦ (⟨z, V z⟩ : TangentBundle (𝓘(ℝ, E).prod 𝓘(ℝ)) (M × ℝ)))

/-- **The integral continuation coefficients in dimension one.** Let `V` be a smooth continuation
field at rate `C > 0` from `X₀` to `X₁` on an oriented manifold `M` of dimension `1`, where every
critical point has index `0` or `1`. For all sufficiently negative `a` and sufficiently positive
`b`, the coefficient of `q` in the image of `p` under the integral continuation map along the
transition diffeomorphism from `a` to `b` is the mod-two continuation coefficient, read as `0` or
`1`, weighted by the signs of `p` and `q`: the augmentation sign at a critical point of index `0`
and the fundamental sign at one of index `1`, one of the two summands being `0`. -/
theorem eventually_signedContinuationCoeff_eq_of_finrank_eq_one
    (hV : IsContinuationField X₀ X₁ C V) (hC : 0 < C) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hE : finrank ℝ E = 1) (𝔬₀ : MorseOrientation f₀ X₀)
    (𝔬₁ : MorseOrientation f₁ X₁)
    (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E))) :
    ∀ᶠ a in atBot, ∀ᶠ b in atTop, ∀ (p : criticalPoints 𝓘(ℝ, E) f₀)
      (q : criticalPoints 𝓘(ℝ, E) f₁),
      hX₀.signedContinuationCoeff hX₁ 𝔬₀ 𝔬₁ (continuationTransition C hVs a b) p q =
        (𝔬₀.augmentationSign p + hX₀.fundamentalSign 𝔬₀ oM p) *
          (𝔬₁.augmentationSign q + hX₁.fundamentalSign 𝔬₁ oM q) *
            (morseContinuationCoeff f₀ f₁ V p q).val := by
  filter_upwards [hV.eventually_morseContinuationCoeff_eq_ncard_inter_preimage hX₀ hX₁ hC
    (hVs.of_le (by simp))] with a ha
  filter_upwards [ha] with b hb p q
  set Φ := continuationTransition C hVs a b
  have hΦ : ⇑Φ = timeDependentFlowOf (continuationSpaceField C V) a b :=
    coe_continuationTransition hVs a b
  have hp₁ : manifoldMorseIndex 𝓘(ℝ, E) f₀ p ≤ 1 := hE ▸ manifoldMorseIndex_le_finrank
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q
  swap
  · rw [IsAdaptedPseudoGradient.signedContinuationCoeff_eq_zero_of_morseIndex_ne 𝔬₀ 𝔬₁ hpq,
      morseContinuationCoeff_eq_zero_of_manifoldMorseIndex_ne hpq, ZMod.val_zero, Nat.cast_zero,
      mul_zero]
  rw [hb p q hpq, ← hΦ]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hp₁ with hp | hp
  · -- Both critical points have index `0`.
    have hq : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = 0 := hpq ▸ hp
    rw [hX₀.signedContinuationCoeff_of_morseIndex_eq_zero hX₁ 𝔬₀ 𝔬₁ Φ hf₀ hp,
      IsAdaptedPseudoGradient.fundamentalSign_of_morseIndex_ne (by omega),
      IsAdaptedPseudoGradient.fundamentalSign_of_morseIndex_ne (hq.trans_ne (by omega)), add_zero,
      add_zero,
      hX₀.unstableSet_eq_singleton_of_manifoldMorseIndex_eq_zero hf₀
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.property) hp]
    split_ifs with h
    · simp [-ZMod.natCast_val, ZMod.val_one_eq_one_mod, singleton_inter_of_mem (mem_preimage.2 h)]
    · simp [singleton_inter_eq_empty.2 (h ∘ mem_preimage.1)]
  · -- Both critical points have index `1 = dim M`.
    have hq : manifoldMorseIndex 𝓘(ℝ, E) f₁ q = 1 := hpq ▸ hp
    rw [hX₀.signedContinuationCoeff_of_morseIndex_eq_finrank hX₁ 𝔬₀ 𝔬₁ Φ hf₀ hf₁ oM
        (isOrientationPreservingAt_continuationTransition hVs oM a b _) (hq.trans hE.symm),
      MorseOrientation.augmentationSign_of_morseIndex_ne_zero _ (by omega),
      MorseOrientation.augmentationSign_of_morseIndex_ne_zero _ (by omega), zero_add, zero_add,
      hX₁.stableSet_eq_singleton_of_manifoldMorseIndex_eq_finrank
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 q.property) (hq.trans hE.symm),
      show ⇑Φ ⁻¹' {(q : M)} = {Φ.symm q} from Set.ext fun x ↦ by
        rw [mem_preimage, mem_singleton_iff, mem_singleton_iff]
        exact Φ.toEquiv.eq_symm_apply.symm]
    split_ifs with h
    · simp [-ZMod.natCast_val, ZMod.val_one_eq_one_mod, inter_singleton_of_mem h]
    · simp [inter_singleton_eq_empty.2 h]

/-- **An integral continuation map in dimension one is the identity when its mod-two reduction
is.** Let `V` be a smooth continuation field at rate `C > 0` from a pseudo-gradient `X` adapted to
a Morse function `f` to itself, on an oriented manifold of dimension `1`. If the mod-two
continuation map of `V` is the identity, then for every orientation data `𝔬` and every ring `R`,
the integral continuation map along the transition diffeomorphism from `a` to `b`, with `𝔬` at
both ends, is the identity for all sufficiently negative `a` and sufficiently positive `b`. -/
theorem eventually_signedContinuationMap_eq_id_of_finrank_eq_one {f : M → ℝ}
    {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hX : IsAdaptedPseudoGradient f X)
    (hV : IsContinuationField X X C V) (hC : 0 < C) (hf : IsMorse 𝓘(ℝ, E) f)
    (hE : finrank ℝ E = 1) (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E)))
    (hid : morseContinuationMap f hf V = LinearMap.id) (𝔬 : MorseOrientation f X) (R : Type*)
    [Ring R] :
    ∀ᶠ a in atBot, ∀ᶠ b in atTop,
      hX.signedContinuationMap hX 𝔬 𝔬 (continuationTransition C hVs a b) hf R = LinearMap.id := by
  classical
  filter_upwards [hV.eventually_signedContinuationCoeff_eq_of_finrank_eq_one hX hX hVs hC hf hf hE
    𝔬 𝔬 oM] with a ha
  filter_upwards [ha] with b hb
  refine Finsupp.lhom_ext fun p c ↦ Finsupp.ext fun q ↦ ?_
  have hcoeff : morseContinuationCoeff f f V p q = if p = q then 1 else 0 := by
    have h := congrArg (fun L ↦ L (Finsupp.single p 1) q) hid
    simpa [Finsupp.single_apply] using h
  rw [IsAdaptedPseudoGradient.signedContinuationMap_single_apply, hb p q, hcoeff,
    LinearMap.id_apply, Finsupp.single_apply]
  split_ifs with hpq
  · subst hpq
    simp [-ZMod.natCast_val, ZMod.val_one_eq_one_mod,
      hX.augmentationSign_add_fundamentalSign_mul_self_of_finrank_eq_one hE]
  · simp

end IsContinuationField

end TauCeti
