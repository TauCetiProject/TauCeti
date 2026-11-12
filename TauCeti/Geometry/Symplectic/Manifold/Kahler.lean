/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.Manifold.Nijenhuis
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Symplectic.StandardCompatible

/-!
# The Kähler condition on the real carrier

A smooth real two-form `ω` on a manifold is **Kähler** for a smooth almost complex structure `J`
when `ω` is closed, `ω` is compatible with `J` (invariant under `J` and positive on complex lines,
`TauCeti.SmoothTwoForm.Compatible`), and the Nijenhuis tensor of `J` vanishes. By the
Newlander–Nirenberg theorem the last condition says that `J` comes from a complex atlas; the
first two say that the Hermitian metric `g(u, v) = ω(u, J v)` of that complex structure has a
closed fundamental form `ω`. The predicate is stated on the real carrier `SmoothTwoForm I M` with
`TauCeti.SmoothForm.IsClosed`, `TauCeti.SmoothTwoForm.Compatible` and
`TauCeti.SmoothAlmostComplexStructure.nijenhuis`.

## Main declarations

* `TauCeti.SmoothTwoForm.IsKahler`: the Kähler condition on a two-form and an almost complex
  structure.
* `TauCeti.SmoothTwoForm.isKahler_iff`: it is the conjunction of the three conditions.
* `TauCeti.SmoothTwoForm.IsKahler.isSymplectic`: a Kähler form is symplectic.
* `TauCeti.SmoothTwoForm.isKahler_ofComplexManifold_iff`: on a complex manifold, a two-form is
  Kähler for the almost complex structure of the manifold exactly when it is closed and
  compatible, since that structure is integrable.
* `TauCeti.SymplecticForm.isKahler_constSmooth_iff`: a constant pair on a vector space is Kähler
  exactly when the underlying linear pair is compatible.
* `TauCeti.isKahler_constSmooth_stdSymplecticForm_product`: the flat Kähler structure
  `(ω₀, J₀)` on `W × W`, in particular on `ℝ²ⁿ = ℂⁿ`.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 3.1.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Section 2.2.
-/

public section

open scoped ContDiff Manifold TauCeti.ComplexManifold

noncomputable section

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {form : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}

/-- The **Kähler condition** on the real carrier: a closed real two-form compatible with a smooth
almost complex structure (invariant and positive on complex lines) whose Nijenhuis tensor
vanishes. Through the Newlander–Nirenberg theorem it is a Kähler metric `g(u, v) = ω(u, J v)` on
the induced complex manifold. -/
structure IsKahler (form : SmoothTwoForm I M) (J : SmoothAlmostComplexStructure I M) : Prop where
  /-- A Kähler form is closed. -/
  isClosed : form.IsClosed
  /-- A Kähler form is compatible with the almost complex structure. -/
  compatible : form.Compatible J
  /-- The almost complex structure of a Kähler pair is integrable. -/
  nijenhuis_eq_zero : J.nijenhuis = 0

/-- The Kähler condition is the conjunction of closedness, compatibility, and vanishing of the
Nijenhuis tensor. -/
theorem isKahler_iff :
    form.IsKahler J ↔ form.IsClosed ∧ form.Compatible J ∧ J.nijenhuis = 0 :=
  ⟨fun h ↦ ⟨h.isClosed, h.compatible, h.nijenhuis_eq_zero⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

/-- A Kähler form is fiberwise nondegenerate. -/
theorem IsKahler.isNondegenerate (h : form.IsKahler J) : form.IsNondegenerate :=
  h.compatible.isNondegenerate

/-- **A Kähler form is symplectic.** -/
theorem IsKahler.isSymplectic (h : form.IsKahler J) : form.IsSymplectic :=
  ⟨h.isClosed, h.isNondegenerate⟩

end SmoothTwoForm

namespace SmoothTwoForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {form : SmoothTwoForm 𝓘(ℝ, E) M}

/-- On a complex manifold, whose almost complex structure is integrable, a real two-form is Kähler
exactly when it is closed and compatible with multiplication by `i`. -/
theorem isKahler_ofComplexManifold_iff :
    form.IsKahler (SmoothAlmostComplexStructure.ofComplexManifold E M) ↔
      form.IsClosed ∧ form.Compatible (SmoothAlmostComplexStructure.ofComplexManifold E M) := by
  rw [isKahler_iff, SmoothAlmostComplexStructure.nijenhuis_ofComplexManifold, and_iff_left rfl]

end SmoothTwoForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

namespace SymplecticForm

/-- A pair of constant smooth structures on a vector space is Kähler exactly when the underlying
linear pair is compatible. -/
@[simp]
theorem isKahler_constSmooth_iff {omegaForm : SymplecticForm V} {J : AlmostComplexStructure V} :
    omegaForm.constSmooth.IsKahler J.constSmooth ↔ omegaForm.Compatible J := by
  rw [SmoothTwoForm.isKahler_iff, compatible_constSmooth_iff,
    AlmostComplexStructure.nijenhuis_constSmooth]
  exact ⟨fun h ↦ h.2.1, fun h ↦ ⟨isClosed_constSmooth omegaForm, h, rfl⟩⟩

end SymplecticForm

/-- **Flat Kähler space.** On the doubled space `W × W` of a finite-dimensional real inner product
space, the constant standard symplectic form `ω₀` is Kähler for the constant product almost complex
structure `J₀(x, y) = (-y, x)`. For `W = ℝⁿ` this is the standard Kähler structure on
`ℝ²ⁿ = ℂⁿ`. -/
theorem isKahler_constSmooth_stdSymplecticForm_product {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] :
    (stdSymplecticForm (V := W)).constSmooth.IsKahler
      (AlmostComplexStructure.product W).constSmooth :=
  SymplecticForm.isKahler_constSmooth_iff.mpr stdSymplecticForm_compatible_product

end TauCeti

end
