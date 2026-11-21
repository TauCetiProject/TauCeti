/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.ClosedAnnulus
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.ZeroOneForm

/-!
# Bordered Sobolev `(0,1)`-forms on the closed annulus

This file instantiates `TauCeti.borderedZeroOneSobolevSections` on the concrete bordered Riemann
surface `Complex.closedAnnulus r₁ r₂`, witnessing completeness, complementedness, and the
injective embedding of `Cᵏ` `(0,1)`-forms up to the boundary.
-/

public noncomputable section

open scoped ENNReal

namespace TauCeti.Examples.BorderedZeroOneForm

/-- On a closed annulus `Complex.closedAnnulus r₁ r₂` with `0 < r₁ < r₂`, a finite bundle atlas
admits complete, closed-complemented bordered Sobolev `(0,1)`-forms and an injective embedding of
`Cᵏ` `(0,1)`-forms up to the boundary. -/
example (r₁ r₂ : ℝ) [hr₁ : Fact (0 < r₁)] [hr₁₂ : Fact (r₁ < r₂)]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ) :
    ∃ A : FiniteBundleAtlas ClosedUpperHalfPlane (Complex.closedAnnulus r₁ r₂) ℂ
        (Bundle.Trivial (Complex.closedAnnulus r₁ r₂) ℂ),
      CompleteSpace (borderedZeroOneSobolevSections A p k) ∧
      (borderedZeroOneSobolevSections A p k).ClosedComplemented ∧
      Function.Injective (borderedZeroOneOfContMDiffSection A p k) := by
  have : LocallyCompactSpace ClosedUpperHalfPlane :=
    (isClosed_le continuous_const Complex.continuous_im).locallyCompactSpace
  have : Nonempty (Complex.closedAnnulus r₁ r₂) := ⟨⟨(r₁ : ℂ), Complex.mem_closedAnnulus.2
    ⟨by simp [abs_of_pos hr₁.out], by simp [abs_of_pos hr₁.out, hr₁₂.out.le]⟩⟩⟩
  obtain ⟨A⟩ := FiniteBundleAtlas.nonempty (E := ClosedUpperHalfPlane)
    (M := Complex.closedAnnulus r₁ r₂) (F := ℂ) (V := Bundle.Trivial _ ℂ)
  exact ⟨A, inferInstance, closedComplemented_borderedZeroOneSobolevSections,
    borderedZeroOneOfContMDiffSection_injective A p k⟩

end TauCeti.Examples.BorderedZeroOneForm
