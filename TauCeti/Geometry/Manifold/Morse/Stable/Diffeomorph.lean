/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Diffeomorph
public import TauCeti.Geometry.Manifold.Morse.Stable.Pair
import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# The Morse–Smale conditions under diffeomorphisms

Let `σ : M → M'` be a diffeomorphism between compact boundaryless manifolds, and `X₀`, `X₁`
pseudo-gradients on `M` adapted to `f₀` and `f₁`, which `σ` intertwines with pseudo-gradients
`X₀'` and `X₁'` on `M'` adapted to `f₀'` and `f₁'`: `dσ (Xᵢ y) = Xᵢ' (σ y)`. Then `σ` carries the
unstable and stable manifolds of `X₀` and `X₁` onto those of `X₀'` and `X₁'`
(`TauCeti.IsAdaptedPseudoGradient.preimage_unstableSet_diffeomorph`,
`TauCeti.IsAdaptedPseudoGradient.preimage_stableSet_diffeomorph`), and its differential carries
transverse intersections to transverse intersections
(`HasMFDerivAt.span_mtangentConeAt_image_sup_eq_top`). So the Morse–Smale condition for the pair
`(X₀', X₁')` pulls back to the Morse–Smale condition for `(X₀, X₁)`, and likewise for a single
pseudo-gradient.

The intertwining hypothesis holds for the pullbacks `σ^* X₀'` and `σ^* X₁'`
(`TauCeti.IsAdaptedPseudoGradient.mpullback`, `Diffeomorph.mfderiv_apply_mpullback`), whose
unstable and stable manifolds are therefore the preimages under `σ` of those of `X₀'` and `X₁'`
(`TauCeti.IsAdaptedPseudoGradient.unstableSet_mpullback`,
`TauCeti.IsAdaptedPseudoGradient.stableSet_mpullback`). For instance, the stable manifolds of
the pullback of a Morse–Smale pseudo-gradient `X₁` along the transition diffeomorphism of a
continuation are again those of a Morse–Smale pseudo-gradient, which is what the transversality
condition for continuations compares with the unstable manifolds of the pseudo-gradient at the
other end.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `IsMorseSmalePair.pullback`: the Morse–Smale condition for a pair pulls back along a
  diffeomorphism intertwining the fields.
* `IsMorseSmale.pullback`: the Morse–Smale condition pulls back along a diffeomorphism
  intertwining the fields.
* `unstableSet_mpullback`, `stableSet_mpullback`: the unstable and stable manifolds of the pullback
  `σ^* X'` are the preimages under `σ` of those of `X'`.
* `isMorseSmalePair_mpullback_iff`: the pair `(X₀, Φ^* X₁)` is Morse–Smale exactly when the
  unstable manifolds of `X₀` meet the preimages under `Φ` of the stable manifolds of `X₁`
  transversally.
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(ℝ, E) ∞ M']
  [CompactSpace M'] [T2Space M']
  {f₀ f₁ : M → ℝ} {f₀' f₁' : M' → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  {X₀' X₁' : (x : M') → TangentSpace 𝓘(ℝ, E) x} {σ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M'}

namespace IsAdaptedPseudoGradient

section Pullback

variable {f' : M' → ℝ} {X' : (x : M') → TangentSpace 𝓘(ℝ, E) x}
  (hX' : IsAdaptedPseudoGradient f' X') (σ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M')

/-- The unstable manifolds of the pullback `σ^* X'` are the preimages under `σ` of those of `X'`:
`W^u_{σ^* X'}(p) = σ⁻¹ (W^u_{X'}(σ p))`. -/
theorem unstableSet_mpullback (p : M) :
    (hX'.mpullback σ).flow.unstableSet p = σ ⁻¹' hX'.flow.unstableSet (σ p) :=
  (preimage_unstableSet_diffeomorph (hX'.mpullback σ) hX'
    (σ.mfderiv_apply_mpullback (by simp) X') p).symm

/-- The stable manifolds of the pullback `σ^* X'` are the preimages under `σ` of those of `X'`:
`W^s_{σ^* X'}(q) = σ⁻¹ (W^s_{X'}(σ q))`. -/
theorem stableSet_mpullback (q : M) :
    (hX'.mpullback σ).flow.stableSet q = σ ⁻¹' hX'.flow.stableSet (σ q) :=
  (preimage_stableSet_diffeomorph (hX'.mpullback σ) hX'
    (σ.mfderiv_apply_mpullback (by simp) X') q).symm

end Pullback

/-- **The Morse–Smale condition for a pair pulls back along a diffeomorphism.** If `σ` intertwines
`X₀` with `X₀'` and `X₁` with `X₁'`, and `(X₀', X₁')` is a Morse–Smale pair, then so is
`(X₀, X₁)`: at a point `y` of `W^u_{X₀}(a) ∩ W^s_{X₁}(b)`, the differential of `σ⁻¹` at `σ y`
carries the transverse intersection `W^u_{X₀'}(σ a) ∩ W^s_{X₁'}(σ b)` there onto
`W^u_{X₀}(a) ∩ W^s_{X₁}(b)`. -/
theorem IsMorseSmalePair.pullback {hX₀ : IsAdaptedPseudoGradient f₀ X₀}
    {hX₁ : IsAdaptedPseudoGradient f₁ X₁} {hX₀' : IsAdaptedPseudoGradient f₀' X₀'}
    {hX₁' : IsAdaptedPseudoGradient f₁' X₁'} (h : IsMorseSmalePair hX₀' hX₁')
    (hσ₀ : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) σ y (X₀ y) = X₀' (σ y))
    (hσ₁ : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) σ y (X₁ y) = X₁' (σ y)) :
    IsMorseSmalePair hX₀ hX₁ := by
  refine isMorseSmalePair_iff.2 fun a b y hy ↦ ?_
  rw [← preimage_unstableSet_diffeomorph hX₀ hX₀' hσ₀,
    ← preimage_stableSet_diffeomorph hX₁ hX₁' hσ₁] at hy ⊢
  have htr :=
    (σ.symm.mdifferentiable (by simp) (σ y)).hasMFDerivAt.span_mtangentConeAt_image_sup_eq_top
      (σ.symm.isInvertible_mfderiv (by simp)).surjective (h.span_mtangentConeAt_sup_eq_top hy)
  rwa [σ.symm_image_eq_preimage, σ.symm_image_eq_preimage, σ.symm_apply_apply] at htr

/-- **The Morse–Smale condition pulls back along a diffeomorphism.** If `σ` intertwines `X` with
`X'` and `X'` is Morse–Smale, then so is `X`. -/
theorem IsMorseSmale.pullback {f : M → ℝ} {f' : M' → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    {X' : (x : M') → TangentSpace 𝓘(ℝ, E) x} {hX : IsAdaptedPseudoGradient f X}
    {hX' : IsAdaptedPseudoGradient f' X'} (h : hX'.IsMorseSmale)
    (hσX : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) σ y (X y) = X' (σ y)) : hX.IsMorseSmale :=
  (isMorseSmalePair_self_iff hX).1 <|
    ((isMorseSmalePair_self_iff hX').2 h).pullback hσX hσX

/-- **The Morse–Smale condition for a pair pulled back at one end.** For a diffeomorphism `Φ` of
`M`, the pair `(X₀, Φ^* X₁)` is Morse–Smale exactly when, for all points `a` and `b`, the unstable
manifold `W^u_{X₀}(a)` meets the preimage `Φ⁻¹ (W^s_{X₁}(b))` transversally: the stable manifolds of
`Φ^* X₁` are these preimages. -/
theorem isMorseSmalePair_mpullback_iff {hX₀ : IsAdaptedPseudoGradient f₀ X₀}
    (hX₁ : IsAdaptedPseudoGradient f₁ X₁) (Φ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M) :
    IsMorseSmalePair hX₀ (hX₁.mpullback Φ) ↔ ∀ ⦃a b y : M⦄,
      y ∈ hX₀.flow.unstableSet a ∩ Φ ⁻¹' hX₁.flow.stableSet b →
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊔
          Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (Φ ⁻¹' hX₁.flow.stableSet b) y) = ⊤ := by
  simp_rw [isMorseSmalePair_iff, stableSet_mpullback hX₁ Φ]
  refine ⟨fun h a b y hy ↦ ?_, fun h a b y hy ↦ h hy⟩
  have h' := @h a (Φ.symm b) y
  rw [Φ.apply_symm_apply] at h'
  exact h' hy

end IsAdaptedPseudoGradient

end TauCeti
