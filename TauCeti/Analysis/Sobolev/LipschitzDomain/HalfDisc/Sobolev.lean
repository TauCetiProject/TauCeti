/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.HalfDisc.Basic
public import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Trace.Frontier

/-!
# Sobolev spaces on the half-disc

The half-disc `TauCeti.halfDisc r` is a bounded Lipschitz domain
(`TauCeti.exists_isLipschitzDomainWith_halfDisc`), so the Rellich–Kondrachov theorem, the
extension theorem and the trace theorem for bounded Lipschitz domains apply to it.

## Main declarations

* `TauCeti.W1p.isCompactOperator_valueL_halfDisc`: `W^{1,p}(D⁺_r) → Lᵖ(D⁺_r)` is compact.
* `TauCeti.W1p.exists_extensionL_halfDisc`: a bounded extension operator from `W^{1,p}(D⁺_r)` to
  `W^{1,p}` of the plane.
* `TauCeti.W1p.exists_frontierTrace_halfDisc`: the trace `W^{1,p}(D⁺_r) → Lᵖ(frontier D⁺_r)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.4, §5.5 and §5.7.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {r : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Rellich–Kondrachov on the half-disc.** For `1 ≤ p < ∞` the value map
`W^{1,p}(D⁺_r) → Lᵖ(D⁺_r)` is a compact operator. -/
theorem W1p.isCompactOperator_valueL_halfDisc (r : ℝ) (hp : p ≠ ∞) :
    IsCompactOperator (W1p.valueL (mu := volume) (Omega := halfDisc r) (p := p)) :=
  W1p.isCompactOperator_valueL_of_isLipschitzDomainWith hp
    (exists_isLipschitzDomainWith_halfDisc r).choose_spec (isBounded_halfDisc r)

/-- **Extension from the half-disc.** There is a bounded linear extension operator from
`W^{1,p}(D⁺_r)` to `W^{1,p}` of the whole plane, whose restriction to `D⁺_r` is the identity. -/
theorem W1p.exists_extensionL_halfDisc (r : ℝ) :
    ∃ T : W1p volume (halfDisc r) p →L[ℝ] W1p volume (⊤ : Opens (WithLp 2 (ℝ × ℝ))) p,
      (W1p.restrictL le_top).comp T = ContinuousLinearMap.id ℝ (W1p volume (halfDisc r) p) :=
  W1p.exists_extensionL_of_isLipschitzDomainWith
    (exists_isLipschitzDomainWith_halfDisc r).choose_spec (isBounded_halfDisc r)

/-- **The trace on the frontier of the half-disc.** For `1 ≤ p < ∞` there is a bounded linear
operator `W^{1,p}(D⁺_r) → Lᵖ(frontier D⁺_r)`, for one-dimensional Hausdorff measure on the
frontier, sending every function continuous up to the boundary to its restriction. -/
theorem W1p.exists_frontierTrace_halfDisc (r : ℝ) (hp : p ≠ ∞) :
    ∃ T : W1p volume (halfDisc r) p →L[ℝ] Lp ℝ p ((μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict
        (frontier (halfDisc r : Set (WithLp 2 (ℝ × ℝ))))),
      ∀ (u : W1p volume (halfDisc r) p) (f : WithLp 2 (ℝ × ℝ) → ℝ),
        ContinuousOn f (closure (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))) →
        W1p.value u =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))] f →
        T u =ᵐ[(μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict
          (frontier (halfDisc r : Set (WithLp 2 (ℝ × ℝ))))] f := by
  have h := W1p.exists_frontierTrace hp (exists_isLipschitzDomainWith_halfDisc r).choose_spec
    (isBounded_halfDisc r)
  rwa [Module.finrank_self] at h

end TauCeti
