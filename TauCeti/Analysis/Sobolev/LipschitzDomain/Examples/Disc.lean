/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Ball
public import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Trace.Frontier
public import TauCeti.Analysis.Sobolev.W1p.InfiniteDimensional

/-!
# Sobolev analysis on the closed unit disc

The open unit disc `unitDisc` of the Euclidean plane `WithLp 2 (ℝ × ℝ)` is a bounded Lipschitz
domain (`TauCeti.isLipschitzDomainWith_ball`), so the general theory of
`TauCeti.Analysis.Sobolev.LipschitzDomain` applies to it. This file records the consequences used
for the closed disc in the analysis of pseudoholomorphic curves:

* Rellich compactness: for `1 ≤ p < ∞`, the value map `W^{1,p}(D) → Lᵖ(D)` is compact;
* a bounded extension operator `W^{1,p}(D) → W^{1,p}(ℝ²)` that is a right inverse of restriction;
* a bounded trace operator `W^{1,p}(D) → Lᵖ(S¹)` for arc-length measure on the unit circle, which
  restricts functions continuous on the closed disc to the circle;
* the identity of `W^{1,p}(D)` is not compact, so Rellich compactness genuinely loses a derivative.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix B.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5 and §5.7.
-/

public section

noncomputable section

namespace TauCeti

open Bornology Metric MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal

/-- The open unit disc of the Euclidean plane `WithLp 2 (ℝ × ℝ)`, as an open set. -/
@[expose] def unitDisc : Opens (WithLp 2 (ℝ × ℝ)) :=
  ⟨ball 0 1, isOpen_ball⟩

@[simp]
theorem coe_unitDisc : (unitDisc : Set (WithLp 2 (ℝ × ℝ))) = ball 0 1 :=
  rfl

/-- The frontier of the unit disc is the unit circle. -/
theorem frontier_unitDisc : frontier (unitDisc : Set (WithLp 2 (ℝ × ℝ))) = sphere 0 1 :=
  frontier_ball 0 one_ne_zero

/-- The closure of the unit disc is the closed unit disc. -/
theorem closure_unitDisc : closure (unitDisc : Set (WithLp 2 (ℝ × ℝ))) = closedBall 0 1 :=
  closure_ball 0 one_ne_zero

/-- The unit disc is a Lipschitz domain with every positive Lipschitz constant. -/
theorem isLipschitzDomainWith_unitDisc {L : ℝ≥0} (hL : 0 < L) :
    (unitDisc : Set (WithLp 2 (ℝ × ℝ))).IsLipschitzDomainWith L :=
  isLipschitzDomainWith_ball 0 one_pos hL

/-- The unit disc is bounded. -/
theorem isBounded_unitDisc : IsBounded (unitDisc : Set (WithLp 2 (ℝ × ℝ))) :=
  isBounded_ball

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Rellich compactness on the closed disc.** For `1 ≤ p < ∞`, the value map
`W^{1,p}(D) → Lᵖ(D)` of the unit disc is a compact operator. -/
theorem W1p.isCompactOperator_valueL_unitDisc (hp : p ≠ ∞) :
    IsCompactOperator (W1p.valueL (mu := volume) (Omega := unitDisc) (p := p)) :=
  W1p.isCompactOperator_valueL_of_isLipschitzDomainWith hp
    (isLipschitzDomainWith_unitDisc one_pos) isBounded_unitDisc

/-- **Extension from the closed disc.** There is a bounded linear extension operator
`W^{1,p}(D) → W^{1,p}(ℝ²)` whose composite with restriction to the disc is the identity. -/
theorem W1p.exists_extensionL_unitDisc :
    ∃ T : W1p volume unitDisc p →L[ℝ] W1p volume (⊤ : Opens (WithLp 2 (ℝ × ℝ))) p,
      (W1p.restrictL le_top).comp T = ContinuousLinearMap.id ℝ (W1p volume unitDisc p) :=
  W1p.exists_extensionL_of_isLipschitzDomainWith (isLipschitzDomainWith_unitDisc one_pos)
    isBounded_unitDisc

/-- **Trace on the unit circle.** For `1 ≤ p < ∞` there is a bounded linear trace operator from
`W^{1,p}(D)` to `Lᵖ` of the unit circle with its arc-length measure, which sends every function
continuous on the closed disc to its restriction to the circle. -/
theorem W1p.exists_trace_unitDisc (hp : p ≠ ∞) :
    ∃ T : W1p volume unitDisc p →L[ℝ]
        Lp ℝ p ((μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (sphere 0 1)),
      ∀ (u : W1p volume unitDisc p) (f : WithLp 2 (ℝ × ℝ) → ℝ),
        ContinuousOn f (closedBall 0 1) →
        W1p.value u =ᵐ[volume.restrict (unitDisc : Set (WithLp 2 (ℝ × ℝ)))] f →
        T u =ᵐ[(μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (sphere 0 1)] f := by
  have h := W1p.exists_frontierTrace (p := p) hp (isLipschitzDomainWith_unitDisc one_pos)
    isBounded_unitDisc
  rwa [finrank_self, frontier_unitDisc, closure_unitDisc] at h

/-- **The identity of `W^{1,p}(D)` is not compact.** Unlike the value map into `Lᵖ(D)`, the
identity of the infinite-dimensional space `W^{1,p}(D)` is not a compact operator. -/
theorem W1p.not_isCompactOperator_id_unitDisc :
    ¬IsCompactOperator (id : W1p volume unitDisc p → W1p volume unitDisc p) :=
  W1p.not_isCompactOperator_id isBounded_unitDisc ⟨0, by simp⟩

end TauCeti
