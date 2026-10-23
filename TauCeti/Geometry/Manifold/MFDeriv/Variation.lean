/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Variations of a curve with fixed endpoints

A *variation* of a curve `γ : ℝ → M` is a two-parameter family `F : ℝ → ℝ → M` with `F 0 = γ`,
whose first argument is the variation parameter `s` and whose second argument is the curve
parameter `t`.  Its variation field `TauCeti.Manifold.variationField I F` is the transverse
velocity `V(t) = ∂F/∂s (0, t)`.

This file names the variations against which a curve between the parameters `a` and `b` is
compared with nearby curves joining the same two points:
`TauCeti.Manifold.IsFixedEndpointVariation I n F a b` says that the uncurried family is `C^n` at
every point of `{0} × [a, b]` and that, for `s` near `0`, the curve `F s` has the same endpoints
`F 0 a` and `F 0 b` as the central curve.  The variation field of such a variation vanishes at
both endpoints.

These are the variations of the first variation formula and of the critical points of the energy
(`TauCeti.Geometry.Manifold.Riemannian.FirstVariation`).  The definition uses only the manifold
structure, not a metric; `[a, b]` is the unordered interval `Set.uIcc a b`.

## Main definitions and results

* `TauCeti.Manifold.IsFixedEndpointVariation`: a two-parameter family is a `C^n` variation of its
  central curve with fixed endpoints.
* `TauCeti.Manifold.IsFixedEndpointVariation.contMDiffAt_apply_zero`: the central curve of a
  `C^n` fixed-endpoint variation is `C^n` on `[a, b]`.
* `TauCeti.Manifold.IsFixedEndpointVariation.variationField_left_eq_zero` and
  `TauCeti.Manifold.IsFixedEndpointVariation.variationField_right_eq_zero`: the variation field
  vanishes at the endpoints.
* `TauCeti.Manifold.isFixedEndpointVariation_const_iff`: the constant family at a curve `γ` is a
  `C^n` fixed-endpoint variation exactly when `γ` is `C^n` on `[a, b]`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 9, §2, Definition 2.1 (proper
  variations).
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2nd ed., 2018, Ch. 6, variations of
  curves and proper variations.
-/

public section

open Filter Set
open scoped Manifold Topology

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {m n : WithTop ℕ∞} {F : ℝ → ℝ → M} {a b : ℝ}

variable (I) in
/-- A two-parameter family `F : ℝ → ℝ → M` is a **`C^n` variation with fixed endpoints** of its
central curve `F 0` between the parameters `a` and `b` when the uncurried family
`(s, t) ↦ F s t` is `C^n` at every point of `{0} × [a, b]` and, for `s` near `0`, the curve `F s`
passes through `F 0 a` at `a` and through `F 0 b` at `b`. -/
structure IsFixedEndpointVariation (n : WithTop ℕ∞) (F : ℝ → ℝ → M) (a b : ℝ) : Prop where
  /-- A fixed-endpoint variation is `C^n` at every point of `{0} × [a, b]`. -/
  contMDiffAt : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)
  /-- Near `s = 0`, the curves of a fixed-endpoint variation start at `F 0 a`. -/
  eventually_apply_left : ∀ᶠ s in 𝓝 0, F s a = F 0 a
  /-- Near `s = 0`, the curves of a fixed-endpoint variation end at `F 0 b`. -/
  eventually_apply_right : ∀ᶠ s in 𝓝 0, F s b = F 0 b

namespace IsFixedEndpointVariation

/-- A `C^n` fixed-endpoint variation is a `C^m` fixed-endpoint variation for every `m ≤ n`. -/
theorem of_le (h : IsFixedEndpointVariation I n F a b) (hmn : m ≤ n) :
    IsFixedEndpointVariation I m F a b :=
  ⟨fun t ht ↦ (h.contMDiffAt t ht).of_le hmn, h.eventually_apply_left, h.eventually_apply_right⟩

/-- The central curve of a `C^n` fixed-endpoint variation is `C^n` at every point of `[a, b]`. -/
theorem contMDiffAt_apply_zero (h : IsFixedEndpointVariation I n F a b) {t : ℝ}
    (ht : t ∈ uIcc a b) : ContMDiffAt 𝓘(ℝ, ℝ) I n (F 0) t :=
  (h.contMDiffAt t ht).comp t (contDiff_prodMk_right (0 : ℝ)).contMDiff.contMDiffAt

/-- The variation field of a fixed-endpoint variation vanishes at the left endpoint. -/
theorem variationField_left_eq_zero (h : IsFixedEndpointVariation I n F a b) :
    variationField I F a = 0 :=
  variationField_eq_zero h.eventually_apply_left

/-- The variation field of a fixed-endpoint variation vanishes at the right endpoint. -/
theorem variationField_right_eq_zero (h : IsFixedEndpointVariation I n F a b) :
    variationField I F b = 0 :=
  variationField_eq_zero h.eventually_apply_right

end IsFixedEndpointVariation

/-- **The trivial variation.** The constant family at a curve `γ` is a `C^n` variation of `γ` with
fixed endpoints between `a` and `b` exactly when `γ` is `C^n` at every point of `[a, b]`. -/
@[simp]
theorem isFixedEndpointVariation_const_iff {γ : ℝ → M} :
    IsFixedEndpointVariation I n (fun _ ↦ γ) a b ↔ ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ t :=
  ⟨fun h _ ↦ h.contMDiffAt_apply_zero, fun h ↦
    ⟨fun t ht ↦ (h t ht).comp (0, t) contDiff_snd.contMDiff.contMDiffAt, .of_forall fun _ ↦ rfl,
      .of_forall fun _ ↦ rfl⟩⟩

end TauCeti.Manifold
