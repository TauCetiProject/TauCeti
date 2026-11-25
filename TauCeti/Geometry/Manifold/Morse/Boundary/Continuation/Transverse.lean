/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Commutation
public import TauCeti.Geometry.Manifold.Morse.Boundary.Continuation.Transition
public import TauCeti.Geometry.Manifold.Morse.Stable.Diffeomorph
import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Transverse continuations have finite continuation counts

Let `V` be a continuation field on `M × ℝ` from a pseudo-gradient `X₀` adapted to `f₀` to a
pseudo-gradient `X₁` adapted to `f₁`, at rate `C > 0` (`TauCeti.IsContinuationField`), on a
compact boundaryless manifold `M`. Along the base trajectory `β = TauCeti.intervalBaseOrbit C`,
its space component is a time-dependent vector field on `M` (`TauCeti.continuationSpaceField`),
whose time-dependent flow `φ_{s, t}` consists of diffeomorphisms of `M`. For a very negative time
`a` and a very positive time `b`, a trajectory of `V` from `(p, 0)` to `(q, 1)` enters the slab
along the unstable manifold `W^u_{X₀}(p)` before time `a` and leaves it along the stable manifold
`W^s_{X₁}(q)` after time `b`, so its trajectories are recorded by the intersection
`W^u_{X₀}(p) ∩ φ_{a, b}⁻¹ (W^s_{X₁}(q))`
(`TauCeti.IsContinuationField.eventually_morseContinuationSlice_eq_preimage`).

**The transversality condition.** The continuation is **transverse**
(`TauCeti.IsTransverseContinuation`) when, for all sufficiently negative `a` and sufficiently
positive `b`, these intersections are transverse: at each of their points the tangent spaces of
`W^u_{X₀}(p)` and of `φ_{a, b}⁻¹ (W^s_{X₁}(q))` span the tangent space of `M`. This is the
transversality condition of continuation maps, a condition on the trajectories of the whole field
`V` rather than on its slices `t = const`.

**The transition diffeomorphism.** When `V` is smooth, the transition map `φ_{a, b}` is a smooth
diffeomorphism `Φ` of `M` (`TauCeti.continuationTransition`). The pullback `Φ^* X₁` of `X₁` is a
pseudo-gradient adapted to `f₁ ∘ Φ` (`TauCeti.IsAdaptedPseudoGradient.mpullback`), whose stable
manifolds are the preimages `Φ⁻¹ (W^s_{X₁}(q))`, and the continuation is transverse exactly when
the pairs `(X₀, Φ^* X₁)` are Morse–Smale
(`TauCeti.isTransverseContinuation_iff_eventually_isMorseSmalePair`). Through the bijection
`φ_{σ, a}` from the middle level `t = 1 / 2` of the slab, the continuation trajectories from
`(p, 0)` to `(q, 1)` correspond to the points of `W^u_{X₀}(p) ∩ W^s_{Φ^* X₁}(Φ⁻¹ q)`
(`TauCeti.IsContinuationField.eventually_morseContinuationSlice_eq_preimage_mpullback`), so the
coefficients of the mod-two continuation map are the intersection counts of a pair of
pseudo-gradients
(`TauCeti.IsContinuationField.eventually_morseContinuationCoeff_eq_ncard_mpullback`).

**Finiteness.** For a transverse continuation between Morse–Smale pseudo-gradients, the theory of
Morse–Smale pairs (`TauCeti.Geometry.Manifold.Morse.Stable.Pair`) applies to `(X₀, Φ^* X₁)`: the
continuation trajectories from `(p, 0)` to `(q, 1)` are finitely many when `ind q ≥ ind p`
(`TauCeti.IsTransverseContinuation.finite_morseContinuationSlice`), and there are none when
`ind q > ind p` (`TauCeti.IsTransverseContinuation.morseContinuationSlice_eq_empty`). So the
continuation map counts finite sets, and the criterion for it to be a chain map holds without any
finiteness hypothesis: the continuation map commutes with the Morse boundaries exactly when,
between any two critical points, the continuation trajectories broken at the two ends of the slab
are evenly many in total
(`TauCeti.IsTransverseContinuation.morseBoundary_comp_morseContinuationMap_eq_iff`).

**The constant continuation.** For a Morse–Smale pseudo-gradient `X`, the constant continuation
field `(X x, C t (1 - t²))` is transverse
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.isTransverseContinuation_constantContinuationField`):
its transition maps are the time maps of the flow of `X`, which preserve the stable manifolds of
`X`, so the condition reduces to the Morse–Smale condition for `X`.

## Main declarations

* `TauCeti.IsTransverseContinuation`: the transversality condition for a continuation, unfolded
  by `TauCeti.isTransverseContinuation_iff`.
* `TauCeti.isTransverseContinuation_iff_eventually_isMorseSmalePair`: transversality is the
  Morse–Smale condition for the pairs `(X₀, Φ^* X₁)`.
* `TauCeti.IsContinuationField.eventually_morseContinuationCoeff_eq_ncard_mpullback`: the
  continuation coefficients count the points of `W^u_{X₀}(p) ∩ W^s_{Φ^* X₁}(Φ⁻¹ q)`.
* `TauCeti.IsTransverseContinuation.finite_morseContinuationSlice`,
  `TauCeti.IsTransverseContinuation.morseContinuationSlice_eq_empty`: finiteness and emptiness of
  the continuation slices.
* `TauCeti.IsTransverseContinuation.morseBoundary_comp_morseContinuationMap_eq_iff`: the
  chain-map criterion for a transverse continuation.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.isTransverseContinuation_constantContinuationField`:
  the constant continuation of a Morse–Smale pseudo-gradient is transverse.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1 (continuation maps, defined by a time-dependent
  pseudo-gradient, and the transversality of their moduli spaces).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 6 (invariance of Morse homology by continuation).
-/

public section

open Filter Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f₀ f₁ : M → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x} {C : ℝ}
  {V : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}

/-! ### The transversality condition -/

variable (C V) in
/-- **The transversality condition for a continuation** along a field `V` on `M × ℝ`, from the
pseudo-gradient `X₀` to the pseudo-gradient `X₁`. Let `φ_{s, t}` be the time-dependent flow of the
space component of `V` along the base trajectory `TauCeti.intervalBaseOrbit C`
(`TauCeti.continuationSpaceField`). The continuation is transverse when, for all sufficiently
negative times `a` and sufficiently positive times `b`, all points `p` and `q`, and every point
`y` of `W^u_{X₀}(p) ∩ φ_{a, b}⁻¹ (W^s_{X₁}(q))`, the tangent spaces of `W^u_{X₀}(p)` and of
`φ_{a, b}⁻¹ (W^s_{X₁}(q))` at `y` span the tangent space of `M`. -/
def IsTransverseContinuation (hX₀ : IsAdaptedPseudoGradient f₀ X₀)
    (hX₁ : IsAdaptedPseudoGradient f₁ X₁) : Prop :=
  ∀ᶠ a in atBot, ∀ᶠ b in atTop, ∀ ⦃p q y : M⦄,
    y ∈ hX₀.flow.unstableSet p ∩
      timeDependentFlowOf (continuationSpaceField C V) a b ⁻¹' hX₁.flow.stableSet q →
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet p) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E)
        (timeDependentFlowOf (continuationSpaceField C V) a b ⁻¹' hX₁.flow.stableSet q) y) = ⊤

/-- The unfolding of `TauCeti.IsTransverseContinuation`. -/
theorem isTransverseContinuation_iff {hX₀ : IsAdaptedPseudoGradient f₀ X₀}
    {hX₁ : IsAdaptedPseudoGradient f₁ X₁} :
    IsTransverseContinuation C V hX₀ hX₁ ↔ ∀ᶠ a in atBot, ∀ᶠ b in atTop, ∀ ⦃p q y : M⦄,
      y ∈ hX₀.flow.unstableSet p ∩
        timeDependentFlowOf (continuationSpaceField C V) a b ⁻¹' hX₁.flow.stableSet q →
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet p) y) ⊔
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E)
          (timeDependentFlowOf (continuationSpaceField C V) a b ⁻¹' hX₁.flow.stableSet q) y) = ⊤ :=
  Iff.rfl

/-! ### Transversality through the transition diffeomorphism -/

section Transition

variable (hVs : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)).tangent ∞
  fun z ↦ (⟨z, V z⟩ : TangentBundle (𝓘(ℝ, E).prod 𝓘(ℝ)) (M × ℝ)))

/-- **Transversality is the Morse–Smale condition for the transported pairs.** For a smooth field
`V`, the continuation along `V` is transverse exactly when, for all sufficiently negative `a` and
sufficiently positive `b`, the pair `(X₀, Φ^* X₁)` is Morse–Smale, where `Φ` is the transition
diffeomorphism from `a` to `b`. -/
theorem isTransverseContinuation_iff_eventually_isMorseSmalePair
    {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁} :
    IsTransverseContinuation C V hX₀ hX₁ ↔ ∀ᶠ a in atBot, ∀ᶠ b in atTop,
      IsAdaptedPseudoGradient.IsMorseSmalePair hX₀
        (hX₁.mpullback (continuationTransition C hVs a b)) := by
  refine eventually_congr (.of_forall fun a ↦ eventually_congr (.of_forall fun b ↦ ?_))
  rw [IsAdaptedPseudoGradient.isMorseSmalePair_mpullback_iff, coe_continuationTransition]

namespace IsContinuationField

variable (hV : IsContinuationField X₀ X₁ C V) (hX₀ : IsAdaptedPseudoGradient f₀ X₀)
  (hX₁ : IsAdaptedPseudoGradient f₁ X₁) (hC : 0 < C)
include hV hX₀ hX₁ hC hVs

/-- **Continuation trajectories are the intersection points of a transported pair.** Let `V` be a
smooth continuation field from `X₀` to `X₁` at rate `C > 0`, and `σ` the time at which the base
trajectory crosses the middle level `t = 1 / 2`. For all sufficiently negative `a` and sufficiently
positive `b`, with `Φ` the transition diffeomorphism from `a` to `b`, the middle-level slice of the
trajectories from `(p, 0)` to `(q, 1)` is the preimage under the transition diffeomorphism from `σ`
to `a` of `W^u_{X₀}(p) ∩ W^s_{Φ^* X₁}(Φ⁻¹ q)`, for all `p` and `q` at once. -/
theorem eventually_morseContinuationSlice_eq_preimage_mpullback {σ : ℝ}
    (hσ : intervalBaseOrbit C σ = 1 / 2) :
    ∀ᶠ a in atBot, ∀ᶠ b in atTop, ∀ p q : M, morseContinuationSlice V p q =
      continuationTransition C hVs σ a ⁻¹'
        (hX₀.flow.unstableSet p ∩ (hX₁.mpullback (continuationTransition C hVs a b)).flow.stableSet
          ((continuationTransition C hVs a b).symm q)) := by
  have hVs₁ := hVs.of_le (m := 1) (by simp)
  have hY := contMDiff_continuationSpaceField (C := C) hVs₁
  have hcomp := isCompleteVectorField_timeDependentSuspensionField_of_compactSpace hY
  filter_upwards [hV.eventually_morseContinuationSlice_eq_preimage hX₀ hX₁ hC hVs₁ hσ] with a ha
  filter_upwards [ha] with b hb p q
  -- The stable manifolds of `Φ^* X₁` are the preimages under `Φ` of those of `X₁`, and the flow
  -- from `σ` to `b` is the flow from `σ` to `a` followed by the transition `Φ`.
  ext x
  rw [hb, IsAdaptedPseudoGradient.stableSet_mpullback hX₁, Diffeomorph.apply_symm_apply]
  simp only [mem_inter_iff, mem_preimage, coe_continuationTransition,
    timeDependentFlowOf_trans hcomp hY]

/-- **The continuation coefficients are intersection counts of a transported pair.** Let `V` be a
smooth continuation field from `X₀` to `X₁` at rate `C > 0`. For all sufficiently negative `a`
and sufficiently positive `b`, with `Φ` the
transition diffeomorphism from `a` to `b`, the coefficient of `q` in the continuation of `p`, for
critical points of equal index, is the number of points of `W^u_{X₀}(p) ∩ W^s_{Φ^* X₁}(Φ⁻¹ q)`
modulo two. -/
theorem eventually_morseContinuationCoeff_eq_ncard_mpullback :
    ∀ᶠ a in atBot, ∀ᶠ b in atTop, ∀ (p : criticalPoints 𝓘(ℝ, E) f₀)
      (q : criticalPoints 𝓘(ℝ, E) f₁),
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q →
        morseContinuationCoeff f₀ f₁ V p q = ((hX₀.flow.unstableSet p ∩
          (hX₁.mpullback (continuationTransition C hVs a b)).flow.stableSet
            ((continuationTransition C hVs a b).symm q)).ncard : ZMod 2) := by
  filter_upwards [hV.eventually_morseContinuationCoeff_eq_ncard_inter_preimage hX₀ hX₁ hC
    (hVs.of_le (by simp))] with a ha
  filter_upwards [ha] with b hb p q hind
  rw [hb p q hind, IsAdaptedPseudoGradient.stableSet_mpullback hX₁, Diffeomorph.apply_symm_apply,
    coe_continuationTransition]

end IsContinuationField

end Transition

/-! ### Finiteness of the continuation counts -/

namespace IsTransverseContinuation

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  (hT : IsTransverseContinuation C V hX₀ hX₁) (hV : IsContinuationField X₀ X₁ C V) (hC : 0 < C)
  (hVs : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)).tangent ∞
    fun z ↦ (⟨z, V z⟩ : TangentBundle (𝓘(ℝ, E).prod 𝓘(ℝ)) (M × ℝ)))
include hT hV hC hVs

/-- For a transverse smooth continuation, some transition diffeomorphism `Φ` makes `(X₀, Φ^* X₁)`
a Morse–Smale pair and records every slice of the continuation map through a fixed bijection. The
Morse index of `f₁ ∘ Φ` at `Φ⁻¹ q` is that of `f₁` at a critical point `q`. -/
private theorem exists_isMorseSmalePair_and_morseContinuationSlice_eq (hf₁ : IsMorse 𝓘(ℝ, E) f₁) :
    ∃ (Φ Ψ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M), IsAdaptedPseudoGradient.IsMorseSmalePair hX₀
      (hX₁.mpullback Φ) ∧ (∀ p q : M, morseContinuationSlice V p q =
        Ψ ⁻¹' (hX₀.flow.unstableSet p ∩ (hX₁.mpullback Φ).flow.stableSet (Φ.symm q))) ∧
      ∀ q : criticalPoints 𝓘(ℝ, E) f₁,
        manifoldMorseIndex 𝓘(ℝ, E) (f₁ ∘ Φ) (Φ.symm q) = manifoldMorseIndex 𝓘(ℝ, E) f₁ q := by
  obtain ⟨σ, hσ⟩ := exists_intervalBaseOrbit_eq hC.ne' (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)
  have h := ((isTransverseContinuation_iff_eventually_isMorseSmalePair hVs).1 hT).and
    (hV.eventually_morseContinuationSlice_eq_preimage_mpullback hVs hX₀ hX₁ hC hσ)
  obtain ⟨a, ha⟩ := h.exists
  obtain ⟨b, hb₁, hb₂⟩ := (ha.1.and ha.2).exists
  refine ⟨_, continuationTransition C hVs σ a, hb₁, hb₂, fun q ↦ ?_⟩
  set Φ := continuationTransition C hVs a b
  have h := (Φ.isLocalDiffeomorph (Φ.symm q)).manifoldMorseIndex_comp (by simp)
    ((hf₁.contMDiff _).of_le (by simp)) (by rw [Φ.apply_symm_apply]; exact q.property)
  rwa [Φ.apply_symm_apply] at h

/-- **A transverse continuation has no trajectories raising the index.** For a transverse smooth
continuation field at rate `C > 0` between pseudo-gradients adapted to Morse functions, there is no
continuation trajectory from `(p, 0)` to `(q, 1)` when the Morse index of `q` for `f₁` exceeds that
of `p` for `f₀`. -/
theorem morseContinuationSlice_eq_empty (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (p : M) (q : criticalPoints 𝓘(ℝ, E) f₁)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p < manifoldMorseIndex 𝓘(ℝ, E) f₁ q) :
    morseContinuationSlice V p q = ∅ := by
  obtain ⟨Φ, Ψ, hΦ, hs, hind'⟩ :=
    hT.exists_isMorseSmalePair_and_morseContinuationSlice_eq hV hC hVs hf₁
  rw [hs, hΦ.unstableSet_inter_stableSet_eq_empty hf₀ (by rwa [hind']), preimage_empty]

/-- **A transverse continuation has finitely many rigid trajectories.** For a transverse smooth
continuation field at rate `C > 0` between Morse–Smale pseudo-gradients adapted to Morse
functions, there are finitely many continuation trajectories from `(p, 0)` to `(q, 1)` when the
Morse index of `q` for `f₁` is at least that of `p` for `f₀`; they are recorded by the finite
middle-level slice. -/
theorem finite_morseContinuationSlice (h₀ : hX₀.IsMorseSmale) (h₁ : hX₁.IsMorseSmale)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (p : M)
    (q : criticalPoints 𝓘(ℝ, E) f₁)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p ≤ manifoldMorseIndex 𝓘(ℝ, E) f₁ q) :
    (morseContinuationSlice V p q).Finite := by
  obtain ⟨Φ, Ψ, hΦ, hs, hind'⟩ :=
    hT.exists_isMorseSmalePair_and_morseContinuationSlice_eq hV hC hVs hf₁
  -- The pair `(X₀, Φ^* X₁)` is a Morse–Smale pair of Morse–Smale pseudo-gradients.
  have h₁' := h₁.pullback (hX := hX₁.mpullback Φ) (Φ.mfderiv_apply_mpullback (by simp) X₁)
  rw [hs]
  exact (hΦ.finite_unstableSet_inter_stableSet h₀ h₁' hf₀
    (hf₁.comp_isLocalDiffeomorph Φ.isLocalDiffeomorph)
    (by rwa [hind'])).preimage Ψ.injective.injOn

/-- **The chain-map criterion for a transverse continuation.** For a transverse smooth continuation
field at rate `C > 0` between Morse–Smale pseudo-gradients adapted to Morse functions, the mod-two
continuation map commutes with the Morse boundaries exactly when, between any
critical point `p` of `f₀` and any critical point `r` of `f₁`, the continuation trajectories
broken at the source and at the target are evenly many in total. -/
theorem morseBoundary_comp_morseContinuationMap_eq_iff (h₀ : hX₀.IsMorseSmale)
    (h₁ : hX₁.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁) :
    h₁.morseBoundary hf₁ ∘ₗ morseContinuationMap f₀ hf₁ V =
        morseContinuationMap f₀ hf₁ V ∘ₗ h₀.morseBoundary hf₀ ↔
      ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₁),
        Even ((morseSourceBrokenContinuationSet f₁ V hX₀ p r).ncard +
          (morseTargetBrokenContinuationSet f₀ V hX₁ p r).ncard) :=
  TauCeti.morseBoundary_comp_morseContinuationMap_eq_iff h₀ hf₀ h₁ hf₁ fun p q hpq ↦
    hT.finite_morseContinuationSlice hV hC hVs h₀ h₁ hf₀ hf₁ p q hpq.le

end IsTransverseContinuation

/-! ### The constant continuation -/

/-- **The constant continuation of a Morse–Smale pseudo-gradient is transverse.** For a Morse–Smale
pseudo-gradient `X` adapted to `f` and any rate `C`, the continuation along the constant
continuation field `(X x, C t (1 - t²))` is transverse. Its space component is `X` at all times,
so its transition maps are the time maps of the flow of `X`; these preserve the stable manifolds of
`X`, and the condition becomes the Morse–Smale condition for `X`. -/
theorem IsAdaptedPseudoGradient.IsMorseSmale.isTransverseContinuation_constantContinuationField
    {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (C : ℝ) :
    IsTransverseContinuation C (constantContinuationField X C) hX hX := by
  -- The space component is `X = 1 • X` at all times, so the transition maps are flow maps.
  have hY : continuationSpaceField C (constantContinuationField X C) = fun _ ↦ (1 : ℝ) • X := by
    funext s x
    simp [continuationSpaceField_apply]
  have hflow (a b : ℝ) :
      timeDependentFlowOf (continuationSpaceField C (constantContinuationField X C)) a b =
        hX.flow ((b - a) * 1) := by
    rw [hY, timeDependentFlowOf_const_smul (hX.contMDiff.of_le (by simp)) hX.isCompleteVectorField]
    funext y
    rw [hX.flow_apply, flowOf_apply]
  refine isTransverseContinuation_iff.2 <| .of_forall fun a ↦ .of_forall fun b p q y hy ↦ ?_
  -- The flow maps preserve the stable manifolds of `X`.
  have hs : hX.flow ((b - a) * 1) ⁻¹' hX.flow.stableSet q = hX.flow.stableSet q :=
    ext fun _ ↦ Flow.apply_mem_stableSet_iff _ _
  rw [hflow, hs] at hy ⊢
  exact ((isMorseSmalePair_self_iff hX).2 h).span_mtangentConeAt_sup_eq_top hy

end TauCeti
