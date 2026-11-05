/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Local
public import TauCeti.Geometry.Manifold.Morse.Stable.Transversality

/-!
# Unstable and stable manifolds cross a Morse box in transverse discs

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient field
adapted to `f` satisfying the Morse–Smale condition, and `φ` a Morse chart at a critical point `x`
in which `X` is the linear field `z ↦ (-wᵢ zᵢ)ᵢ`. In the split coordinates `(u, v)` of `φ`
(`TauCeti.MorseChart.splitCoord`), the flow near `x` is the split hyperbolic flow, the stable set
`W^s(x)` is the plane `v = 0` and the unstable set `W^u(x)` is the plane `u = 0`.

A trajectory broken at `x` arrives along `W^s(x)` from a critical point `a`, and leaves along
`W^u(x)` towards a critical point `b`. The gluing of such a broken trajectory through the split box
(`TauCeti.exists_homeomorph_closure_splitGluingPairs_of_hasStrictFDerivAt`) takes as input a disc
in `W^u(a)` through a point `(x₀, 0)` of the incoming half, on which the expanding coordinate `v`
has invertible derivative, and a disc in `W^s(b)` through a point `(0, y₀)` of the outgoing half, on
which the contracting coordinate `u` has invertible derivative. This file produces both discs.

Near `x` the set `W^s(x)` is the kernel of `v` read in `φ`, so the Morse–Smale condition at a
point `y` of `W^u(a) ∩ W^s(x)`, which says that the tangent spaces of `W^u(a)` and `W^s(x)` span
`T_y M`, says that `v` maps the tangent space of `W^u(a)` onto the expanding factor. A section of
this surjection, followed by a slice chart of `W^u(a)`, is the disc
(`TauCeti.exists_hasStrictFDerivAt_comp_eq_id_of_span_mtangentConeAt_sup_eq_top`). The outgoing
side is the same argument for `W^s(b)` and `W^u(x)`, the plane `u = 0`, which is the stable set of
`x` for the reversed field `-X` (`TauCeti.IsAdaptedPseudoGradient.neg`).

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `exists_hasStrictFDerivAt_mem_unstableSet`: near `x`, each point of `W^u(a) ∩ W^s(x)` is the
  centre of a disc in `W^u(a)` parametrized, in the split coordinates, as a section of the
  expanding coordinate.
* `exists_hasStrictFDerivAt_mem_stableSet`: near `x`, each point of `W^u(x) ∩ W^s(b)` is the
  centre of a disc in `W^s(b)` parametrized, in the split coordinates, as a section of the
  contracting coordinate.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (gluing of broken trajectories, using a pseudo-gradient that is linear near the
  critical points).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {x : M}

namespace MorseChart

variable (φ : MorseChart E f x)

/-- If, on the open coordinate cube of radius `ε` of a Morse chart, membership in `s` is read off
the chart image by a predicate `P`, then it is read off by `P` on a neighbourhood of each point of
that cube. -/
private theorem eventually_iff_of_norm_lt {ε : ℝ} {s : Set M} {P : E → Prop}
    (h : ∀ y ∈ φ.toChart.source, ‖φ.coord (φ.toChart y)‖ < ε → (y ∈ s ↔ P (φ.toChart y)))
    {y : M} (hy : y ∈ φ.toChart.source) (hyε : ‖φ.coord (φ.toChart y)‖ < ε) :
    ∀ᶠ z in 𝓝 y, z ∈ s ↔ P (φ.toChart z) := by
  have hcoord : Continuous φ.coord :=
    LinearMap.continuous_of_finiteDimensional (φ.coord : E →ₗ[ℝ] Fin (Module.finrank ℝ E) → ℝ)
  have hc : ContinuousAt (fun z ↦ ‖φ.coord (φ.toChart z)‖) y :=
    (hcoord.continuousAt.comp (φ.toChart.continuousAt hy)).norm
  filter_upwards [φ.toChart.open_source.mem_nhds hy, hc.eventually_lt continuousAt_const hyε]
    with z hz hzε
  exact h z hz hzε

end MorseChart

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **A transverse disc read in split coordinates.** Let `φ` be a Morse chart and `pr` a
surjection of the split model onto a finite-dimensional space, and let `s₂` be, on the open
coordinate cube of radius `ε`, the set where `pr` vanishes on the split coordinates. A set `s₁`
flattened by a chart `q` near a point `y` of that cube, and meeting `s₂` transversally at `y`,
contains a disc through `y` which, read in the split coordinates, is a map `ψ` with
`ψ 0 = (u, v)(y)`, strictly differentiable at `0`, whose derivative is a section of `pr`. -/
private theorem exists_hasStrictFDerivAt_splitCoord {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] (φ : MorseChart E f x)
    {pr : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) →L[ℝ] G}
    (hpr : Function.Surjective pr) {ε : ℝ} {s₁ s₂ : Set M}
    (hs₂ : ∀ z ∈ φ.toChart.source, ‖φ.coord (φ.toChart z)‖ < ε →
      (z ∈ s₂ ↔ pr (φ.splitCoord (φ.coord (φ.toChart z))) = 0))
    {L : Submodule ℝ E} {q : OpenPartialHomeomorph M E}
    (hq : q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hs₁ : IsSliceChart q (L : Set E) s₁) {y : M}
    (hyφ : y ∈ φ.toChart.source) (hyε : ‖φ.coord (φ.toChart y)‖ < ε) (hyq : y ∈ q.source)
    (hys₁ : y ∈ s₁) (hys₂ : y ∈ s₂)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) s₁ y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) s₂ y) = ⊤) :
    ∃ (ψ : G → WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)))
      (ψ' : G →L[ℝ] WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))),
      HasStrictFDerivAt ψ ψ' 0 ∧ pr ∘L ψ' = ContinuousLinearMap.id ℝ G ∧
      ψ 0 = φ.splitCoord (φ.coord (φ.toChart y)) ∧
      ∀ᶠ z in 𝓝 0, φ.coord.symm (φ.splitCoord.symm (ψ z)) ∈ φ.toChart.target ∧
        φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (ψ z))) ∈ s₁ := by
  -- The surjection `pr`, read in the chart; near `y` its kernel is `s₂`.
  set π := pr ∘L (φ.splitCoordL : E →L[ℝ] _) with hπ
  have hπs : π.range = ⊤ :=
    LinearMap.range_eq_top_of_surjective _ (hpr.comp φ.splitCoordL.surjective)
  have hs₂' : ∀ᶠ z in 𝓝 y, z ∈ s₂ ↔ π (φ.toChart z) = 0 :=
    φ.eventually_iff_of_norm_lt (P := fun w ↦ π w = 0)
      (fun z hz hzε ↦ (hs₂ z hz hzε).trans (by simp [π])) hyφ hyε
  obtain ⟨ψ, ψ', hψ, hπψ, hψ0, hψs⟩ :=
    exists_hasStrictFDerivAt_comp_eq_id_of_span_mtangentConeAt_sup_eq_top (by simp)
      φ.mem_maximalAtlas hq hs₁ L.closed_of_finiteDimensional hyφ hyq hys₁ hπs hs₂' hys₂ htr
  refine ⟨fun z ↦ φ.splitCoordL (ψ z), (φ.splitCoordL : E →L[ℝ] _) ∘L ψ',
    φ.splitCoordL.hasStrictFDerivAt.comp 0 hψ, ?_, ?_, ?_⟩
  · rw [← hπψ, hπ, ContinuousLinearMap.comp_assoc]
  · simp [hψ0]
  · filter_upwards [hψs] with z hz
    simpa [← φ.splitCoordL_symm_apply] using hz

variable [CompactSpace M] [T2Space M]

namespace IsAdaptedPseudoGradient

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X}

/-- **The unstable manifold of `a` crosses a Morse box at `x` in transverse discs.** Let `φ` be a
Morse chart at the critical point `x` in which `X` is the linear field `z ↦ (-wᵢ zᵢ)ᵢ`. On a
small coordinate cube, every point `y` of `W^u(a) ∩ W^s(x)` is the centre of a disc in `W^u(a)`
which, read in the split coordinates `(u, v)` of `φ`, is a map `ψ` of the expanding factor with
`ψ 0 = (u, v)(y)`, strictly differentiable at `0`, whose derivative is a section of the expanding
coordinate `v`. -/
theorem exists_hasStrictFDerivAt_mem_unstableSet (hMS : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i)) :
    ∃ ε > 0, ∀ ⦃a y : M⦄, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0 →
      y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet x → y ∈ φ.toChart.source →
      ‖φ.coord (φ.toChart y)‖ < ε →
      ∃ (ψ : ({i // ¬φ.weight i = 1} → ℝ) →
          WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)))
        (ψ' : ({i // ¬φ.weight i = 1} → ℝ) →L[ℝ]
          WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))),
        HasStrictFDerivAt ψ ψ' 0 ∧
        WithLp.sndL 2 ℝ ({i // φ.weight i = 1} → ℝ) ({i // ¬φ.weight i = 1} → ℝ) ∘L ψ' =
          ContinuousLinearMap.id ℝ _ ∧
        ψ 0 = φ.splitCoord (φ.coord (φ.toChart y)) ∧
        ∀ᶠ z in 𝓝 0, φ.coord.symm (φ.splitCoord.symm (ψ z)) ∈ φ.toChart.target ∧
          φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (ψ z))) ∈ hX.flow.unstableSet a := by
  obtain ⟨ε, hε, hεs⟩ := hX.exists_forall_mem_stableSet_iff φ hφ
    (hf.contMDiff.mdifferentiable (by simp))
  refine ⟨ε, hε, fun a y ha hy hyφ hyε ↦ ?_⟩
  obtain ⟨L, q, -, hyq, hq, hsq⟩ := hX.exists_isSliceChart_unstableSet hf ha hy.1
  -- Near `x`, the stable set of `x` is the kernel of the expanding coordinate `v`.
  refine exists_hasStrictFDerivAt_splitCoord φ (fun v ↦ ⟨WithLp.toLp 2 (0, v), rfl⟩)
    (fun z hz hzε ↦ (hεs z hz hzε).trans ?_) hq hsq hyφ hyε hyq hy.1 hy.2
    (hMS.span_mtangentConeAt_sup_eq_top ha hx hy)
  simp [funext_iff, φ.weight_ne_one_iff]

/-- **The stable manifold of `b` crosses a Morse box at `x` in transverse discs.** Let `φ` be a
Morse chart at the critical point `x` in which `X` is the linear field `z ↦ (-wᵢ zᵢ)ᵢ`. On a
small coordinate cube, every point `y` of `W^u(x) ∩ W^s(b)` is the centre of a disc in `W^s(b)`
which, read in the split coordinates `(u, v)` of `φ`, is a map `χ` of the contracting factor with
`χ 0 = (u, v)(y)`, strictly differentiable at `0`, whose derivative is a section of the contracting
coordinate `u`. -/
theorem exists_hasStrictFDerivAt_mem_stableSet (hMS : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i)) :
    ∃ ε > 0, ∀ ⦃b y : M⦄, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0 →
      y ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet b → y ∈ φ.toChart.source →
      ‖φ.coord (φ.toChart y)‖ < ε →
      ∃ (χ : ({i // φ.weight i = 1} → ℝ) →
          WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)))
        (χ' : ({i // φ.weight i = 1} → ℝ) →L[ℝ]
          WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))),
        HasStrictFDerivAt χ χ' 0 ∧
        WithLp.fstL 2 ℝ ({i // φ.weight i = 1} → ℝ) ({i // ¬φ.weight i = 1} → ℝ) ∘L χ' =
          ContinuousLinearMap.id ℝ _ ∧
        χ 0 = φ.splitCoord (φ.coord (φ.toChart y)) ∧
        ∀ᶠ z in 𝓝 0, φ.coord.symm (φ.splitCoord.symm (χ z)) ∈ φ.toChart.target ∧
          φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (χ z))) ∈ hX.flow.stableSet b := by
  -- Near `x`, the unstable set of `x` is the stable set of `x` for the reversed field `-X`.
  have hnd := hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hx
  obtain ⟨ε, hε, hεs⟩ := (hX.neg hf).exists_forall_mem_stableSet_iff (φ.neg hnd)
    (φ.coord_mfderiv_neg hφ hnd) (hf.neg.contMDiff.mdifferentiable (by simp))
  simp only [MorseChart.neg_toChart, MorseChart.neg_coord, MorseChart.neg_weight, Pi.neg_apply,
    Left.neg_neg_iff, ← hX.unstableSet_eq_stableSet_neg hf] at hεs
  refine ⟨ε, hε, fun b y hb hy hyφ hyε ↦ ?_⟩
  obtain ⟨L, q, -, hyq, hq, hsq⟩ :=
    hX.exists_isSliceChart_stableSet (hf.contMDiff.mdifferentiable (by simp)) hb hy.2
  -- Near `x`, the unstable set of `x` is the kernel of the contracting coordinate `u`.
  refine exists_hasStrictFDerivAt_splitCoord φ (fun u ↦ ⟨WithLp.toLp 2 (u, 0), rfl⟩)
    (fun z hz hzε ↦ (hεs z hz hzε).trans ?_) hq hsq hyφ hyε hyq hy.2 hy.1
    (by rw [sup_comm]; exact hMS.span_mtangentConeAt_sup_eq_top hx hb hy)
  simp [funext_iff, φ.weight_eq_one_iff]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
