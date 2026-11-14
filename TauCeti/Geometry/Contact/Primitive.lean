/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Flat
public import TauCeti.Geometry.Manifold.Flow.Primitive

/-!
# Local solutions of the Reeb-direction equation

For a contact form `α` and a function `b` smooth near a point, the equation `dh(R_α) = b` has a
smooth solution near that point, normalized to zero on a local transverse slice. The slice is the
zero set of a smooth function `s` with `ds(R_α) = 1`. In particular the Reeb-direction equation
appearing in the strict contact-Moser equations is locally solvable. This is a local result with a
constructed slice; it makes no assertion of global solvability along closed Reeb orbits or of
simultaneous solutions for a family of contact forms.

## References

* A. Kriegl and P. W. Michor, *The Convenient Setting of Global Analysis*, Proposition 43.18
  (the scalar Reeb-direction equation in the strict Legendrian neighborhood argument).
-/

public noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace TauCeti.SmoothForm.IsContactForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {α : SmoothForm I M ℝ 1}

/-- The scalar Reeb-direction equation `dh(R_α) = b` has a smooth solution near each point,
with zero initial values on a constructed transverse slice `s = 0`. The slice contains the
chosen point and satisfies `ds(R_α) = 1` throughout the neighbourhood. The function `b` need
only be smooth on a neighbourhood `W` of the point, and the solution neighbourhood lies in `W`. -/
theorem exists_contMDiffOn_mvfderiv_reebVectorField_eq (hα : α.IsContactForm)
    {b : M → ℝ} {W : Set M} {x : M} (hb : ContMDiffOn I 𝓘(ℝ) ∞ b W) (hW : W ∈ 𝓝 x) :
    ∃ (U : Set M) (h s : M → ℝ), IsOpen U ∧ x ∈ U ∧ U ⊆ W ∧
      ContMDiffOn I 𝓘(ℝ) ∞ h U ∧ ContMDiffOn I 𝓘(ℝ) ∞ s U ∧ s x = 0 ∧
      (∀ y ∈ U, mvfderiv I h y (α.reebVectorField y) = b y) ∧
      (∀ y ∈ U, mvfderiv I s y (α.reebVectorField y) = 1) ∧
      (∀ y ∈ U, s y = 0 → h y = 0) := by
  exact exists_contMDiffOn_mvfderiv_apply_eq_of_ne_zero hα.contMDiff_reebVectorField.contMDiffOn
    hb hW (hα.reebVectorField_ne_zero x)

end TauCeti.SmoothForm.IsContactForm
