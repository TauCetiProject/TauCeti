/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder

/-!
# First-order operators on `L²` jets

The jet of a section `ξ : ℝ × ℝ → V` of a trivial bundle over a domain of the plane is a map
`ℝ × ℝ → V × V × V` collecting a zeroth-order term and the two first partial derivatives of `ξ`.
A first-order operator with coefficient field `M : ℝ × ℝ → L(V × V × V, W)` acts on jets
pointwise, `f ↦ (z ↦ M z (f z))`. For a measure `μ` on the plane and `M` essentially bounded for
`μ`, this is a bounded operator `L²(μ, V × V × V) → L²(μ, W)` (`TauCeti.jetOperator`), built
from Mathlib's Hölder pairing `ContinuousLinearMap.holderL`.

The Sobolev spaces on the cylinder (with the strip measure) and on conformally weighted domains
of the plane (with Lebesgue measure restricted to the domain) both realize first-order operators
through this one construction.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B,
  on Sobolev spaces and first-order elliptic operators.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

open scoped Classical in
/-- The first-order operator `f ↦ (z ↦ M z (f z))` on `L²(μ)` jets, for a coefficient field `M`
essentially bounded for `μ`. On the jet of a section `ξ` it is the first-order operator with
coefficients `M`. If `M` is not essentially bounded for `μ`, it is `0` by convention. -/
def jetOperator (μ : Measure (ℝ × ℝ)) (M : ℝ × ℝ → V × V × V →L[ℝ] W) :
    Lp (V × V × V) 2 μ →L[ℝ] Lp W 2 μ :=
  if hM : MemLp M ∞ μ then
    (ContinuousLinearMap.id ℝ (V × V × V →L[ℝ] W)).holderL μ ∞ 2 2 (hM.toLp M)
  else 0

/-- The first-order operator of a coefficient field that is not essentially bounded is `0`. -/
theorem jetOperator_of_not_memLp {μ : Measure (ℝ × ℝ)} {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : ¬ MemLp M ∞ μ) : jetOperator μ M = 0 := by
  simp [jetOperator, hM]

/-- The first-order operator of an essentially bounded coefficient field acts pointwise on
`L²` jets. -/
theorem coeFn_jetOperator {μ : Measure (ℝ × ℝ)} {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ μ) (f : Lp (V × V × V) 2 μ) :
    jetOperator μ M f =ᵐ[μ] fun z ↦ M z (f z) := by
  simp only [jetOperator, hM, ↓reduceDIte, ContinuousLinearMap.holderL_apply_apply]
  filter_upwards [(ContinuousLinearMap.id ℝ (V × V × V →L[ℝ] W)).coeFn_holder (r := 2)
    (hM.toLp M) f, hM.coeFn_toLp] with z h₁ h₂
  rw [h₁, ContinuousLinearMap.id_apply, h₂]

end TauCeti
