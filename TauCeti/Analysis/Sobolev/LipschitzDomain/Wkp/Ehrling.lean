/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.Sobolev.Wkp.Compactness
import TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.LinearIsometry

/-!
# Interpolation inequalities on bounded Lipschitz domains

Let `Ω ⊆ F` be a bounded open set whose image under a linear isometry
`e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)` is a Lipschitz domain, and let `1 ≤ p ≤ ∞`. This file proves the
interpolation inequalities of `W^{k,p}(Ω)` up to the boundary: every intermediate norm is bounded
by an arbitrarily small multiple of a higher norm plus a multiple of the `Lᵖ` norm. For instance,
for every `ε > 0` there is `C` with

`‖∇u‖_{Lᵖ(Ω)} ≤ ε ‖D²u‖_{Lᵖ(Ω)} + C ‖u‖_{Lᵖ(Ω)}` for all `u ∈ W^{2,p}(Ω)`.

No boundary condition is imposed on `u`. The constant `C` depends on `Ω`, `k`, `p` and `ε`, and is
not explicit. For functions vanishing on the boundary or on the whole space the same inequality
holds with an explicit constant
(`TauCeti.Wkp.norm_iteratedGradient_lowerOrder_le_of_mem_wkp0Submodule` and
`TauCeti.Wkp.norm_iteratedGradient_lowerOrder_le`); between concentric balls it holds with
cutoff terms (`TauCeti.Wkp.exists_lpNorm_gradient_ball_le`). Up to the boundary, without a boundary
condition, the Lipschitz hypothesis is what makes it true.

These inequalities absorb lower-order terms in global a priori estimates. A global estimate of a
second-order operator `L` on a domain usually comes first in the form
`‖D²u‖ ≤ C (‖L u‖ + ‖∇u‖ + ‖u‖)`, the lower-order terms being produced by boundary charts and
cutoffs; `TauCeti.Wkp.exists_norm_le_of_norm_iteratedGradient_le_of_isLipschitzDomainWith_image`
turns any estimate of this shape into `‖u‖_{W^{2,p}} ≤ C' (‖L u‖ + ‖u‖_{Lᵖ})`, and likewise at
every order.

The inequalities hold on every open set where forgetting the highest weak derivative is compact
(`TauCeti.Wkp.exists_norm_toOrderL_le_of_isCompactOperator`,
`TauCeti.Wkp.exists_norm_lowerOrder_le_of_isCompactOperator`,
`TauCeti.Wkp.exists_norm_iteratedGradient_lowerOrder_le_of_isCompactOperator` and
`TauCeti.Wkp.exists_norm_le_of_norm_iteratedGradient_le_of_isCompactOperator`, by Ehrling's
inequality). This file supplies that compactness up to the boundary from the higher-order
Rellich–Kondrachov theorem
`TauCeti.Wkp.isCompactOperator_lowerOrderL_of_isLipschitzDomainWith_image` and its consequence
`TauCeti.Wkp.isCompactOperator_toOrderL_of_isLipschitzDomainWith_image`.
The model case `F = WithLp 2 (ℝ × E)` is `e = LinearIsometryEquiv.refl`.

## Main declarations

* `TauCeti.Wkp.exists_norm_toOrderL_le_of_isLipschitzDomainWith_image`: Ehrling's inequality
  `‖u‖_{W^{j,p}} ≤ ε ‖u‖_{W^{k,p}} + C ‖u‖_{Lᵖ}` for `j < k`.
* `TauCeti.Wkp.exists_norm_lowerOrder_le_of_isLipschitzDomainWith_image`: the lower-order part is
  controlled by the top derivative alone, `‖u‖_{W^{k,p}} ≤ ε ‖D^{k+1} u‖ + C ‖u‖_{Lᵖ}` for
  `u ∈ W^{k+1,p}(Ω)`.
* `TauCeti.Wkp.exists_norm_iteratedGradient_lowerOrder_le_of_isLipschitzDomainWith_image`: the
  interpolation inequality `‖D^{k+1} u‖ ≤ ε ‖D^{k+2} u‖ + C ‖u‖_{Lᵖ}` for `u ∈ W^{k+2,p}(Ω)`.
* `TauCeti.Wkp.exists_norm_le_of_norm_iteratedGradient_le_of_isLipschitzDomainWith_image`:
  absorption of the lower-order terms in an estimate of the top derivative.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 7.28 (interpolation inequalities on domains) and the proof of Theorem 9.13.
* G. Ehrling, *On a type of eigenvalue problem for certain elliptic differential operators*,
  Math. Scand. **2** (1954), 267–285.
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 5.2.
-/

public section

noncomputable section

namespace TauCeti

open Bornology MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  {L : ℝ≥0} {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace Wkp

/-- **Ehrling's inequality on Lipschitz domains.** Let `Ω` be a bounded open set whose isometric
image in the model space is a Lipschitz domain, `1 ≤ p ≤ ∞` and `j < k`. For every `ε > 0` there is
`C` with `‖u‖_{W^{j,p}(Ω)} ≤ ε ‖u‖_{W^{k,p}(Ω)} + C ‖u‖_{Lᵖ(Ω)}` for every `u ∈ W^{k,p}(Ω)`. -/
theorem exists_norm_toOrderL_le_of_isLipschitzDomainWith_image
    (e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)) {Ω : Opens F}
    (hΩ : (e '' (Ω : Set F)).IsLipschitzDomainWith L) (hb : IsBounded (Ω : Set F))
    {j k : ℕ} (h : j < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ u : Wkp volume Ω p k, ‖toOrderL h.le u‖ ≤ ε * ‖u‖ + C * ‖value k u‖ :=
  exists_norm_toOrderL_le_of_isCompactOperator h.le
    (isCompactOperator_toOrderL_of_isLipschitzDomainWith_image e hΩ hb h) hε

/-- **The lower-order part is controlled by the top derivative.** Let `Ω` be a bounded open set
whose isometric image in the model space is a Lipschitz domain, and `1 ≤ p ≤ ∞`. For every
`ε > 0` there is `C` with `‖u‖_{W^{k,p}(Ω)} ≤ ε ‖D^{k+1} u‖_{Lᵖ(Ω)} + C ‖u‖_{Lᵖ(Ω)}` for every
`u ∈ W^{k+1,p}(Ω)`, where the left side is the norm of the lower-order part `lowerOrder k u`. -/
theorem exists_norm_lowerOrder_le_of_isLipschitzDomainWith_image
    (e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)) {Ω : Opens F}
    (hΩ : (e '' (Ω : Set F)).IsLipschitzDomainWith L) (hb : IsBounded (Ω : Set F)) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ u : Wkp volume Ω p (k + 1),
      ‖lowerOrder k u‖ ≤ ε * ‖iteratedGradient k u‖ + C * ‖value (k + 1) u‖ :=
  exists_norm_lowerOrder_le_of_isCompactOperator
    (isCompactOperator_lowerOrderL_of_isLipschitzDomainWith_image e hΩ hb k) hε

/-- **The interpolation inequality on Lipschitz domains.** Let `Ω` be a bounded open set whose
isometric image in the model space is a Lipschitz domain, and `1 ≤ p ≤ ∞`. For every `ε > 0` there
is `C` with `‖D^{k+1} u‖_{Lᵖ(Ω)} ≤ ε ‖D^{k+2} u‖_{Lᵖ(Ω)} + C ‖u‖_{Lᵖ(Ω)}` for every
`u ∈ W^{k+2,p}(Ω)`. At `k = 0` this is `‖∇u‖ ≤ ε ‖D²u‖ + C ‖u‖`. -/
theorem exists_norm_iteratedGradient_lowerOrder_le_of_isLipschitzDomainWith_image
    (e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)) {Ω : Opens F}
    (hΩ : (e '' (Ω : Set F)).IsLipschitzDomainWith L) (hb : IsBounded (Ω : Set F)) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ u : Wkp volume Ω p (k + 2),
      ‖iteratedGradient k (lowerOrder (k + 1) u)‖ ≤
        ε * ‖iteratedGradient (k + 1) u‖ + C * ‖value (k + 2) u‖ :=
  exists_norm_iteratedGradient_lowerOrder_le_of_isCompactOperator
    (isCompactOperator_lowerOrderL_of_isLipschitzDomainWith_image e hΩ hb (k + 1)) hε

/-- **Absorbing lower-order terms in a global estimate.** Let `Ω` be a bounded open set whose
isometric image in the model space is a Lipschitz domain, and `1 ≤ p ≤ ∞`. If the top derivative
of every `u ∈ W^{k+1,p}(Ω)` satisfies `‖D^{k+1} u‖ ≤ C (‖T u‖ + ‖u‖_{W^{k,p}})` for some map `T`
into a seminormed group, then there is `D` with `‖u‖_{W^{k+1,p}} ≤ D (‖T u‖ + ‖u‖_{Lᵖ})` for
every `u`. For a second-order operator `T`, this removes the terms `‖∇u‖` and `‖u‖` of the
`W^{1,p}` norm from a global estimate `‖D²u‖ ≤ C (‖T u‖ + ‖∇u‖ + ‖u‖)`, keeping only `‖u‖_{Lᵖ}`. -/
theorem exists_norm_le_of_norm_iteratedGradient_le_of_isLipschitzDomainWith_image
    (e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)) {Ω : Opens F}
    (hΩ : (e '' (Ω : Set F)).IsLipschitzDomainWith L) (hb : IsBounded (Ω : Set F)) {k : ℕ}
    {G : Type*} [SeminormedAddCommGroup G] {T : Wkp volume Ω p (k + 1) → G} {C : ℝ}
    (hT : ∀ u, ‖iteratedGradient k u‖ ≤ C * (‖T u‖ + ‖lowerOrder k u‖)) :
    ∃ D, 0 ≤ D ∧ ∀ u, ‖u‖ ≤ D * (‖T u‖ + ‖value (k + 1) u‖) :=
  exists_norm_le_of_norm_iteratedGradient_le_of_isCompactOperator
    (isCompactOperator_lowerOrderL_of_isLipschitzDomainWith_image e hΩ hb k) hT

end Wkp

end TauCeti
