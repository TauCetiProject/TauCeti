/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.FiniteDimensional
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.ConjCovector
import TauCeti.LinearAlgebra.Complex.Finrank

/-!
# Holomorphic `1`-forms and antiholomorphic `(0,1)`-forms

On a complex manifold `M` modelled on `E`, with its almost complex structure
`TauCeti.SmoothAlmostComplexStructure.ofComplexManifold E M`, a complex valued `(0,1)`-form at a
point, that is a `(0,1)`-form with values in the trivial bundle `M × ℂ`, is a real linear map
`η : E → ℂ` with `η (i • v) = -(i • η v)`: a complex antilinear covector
(`TauCeti.isZeroOneForm_ofComplexManifold_iff`). Complex conjugation `φ ↦ conj ∘ φ` is a real
linear bijection from the complex linear covectors `E →L[ℂ] ℂ` onto the complex antilinear ones
(`TauCeti.conjCovectorEquiv`, from
`TauCeti.Topology.Algebra.Module.ContinuousLinearMap.ConjCovector`).

On a Riemann surface `X` this identifies the holomorphic `1`-forms
`TauCeti.RiemannSurface.holomorphicOneForms X` of the meromorphic differential theory with the
antiholomorphic `(0,1)`-forms `x ↦ conj ∘ ω x`, which is how the cokernel of `∂bar` on functions,
a space of antiholomorphic `(0,1)`-forms by `L²`-duality, is compared with the holomorphic
differentials. As real vector spaces the two are isomorphic
(`TauCeti.RiemannSurface.holomorphicOneFormsEquivAntiholomorphic`), so the real dimension of the
antiholomorphic `(0,1)`-forms is twice the complex dimension `g` of the holomorphic `1`-forms
(`TauCeti.RiemannSurface.finrank_antiholomorphicZeroOneForms`), finite when `X` is compact and
connected.

## Main declarations

* `TauCeti.isZeroOneForm_ofComplexManifold_iff`: the complex valued `(0,1)`-forms of a complex
  manifold are the complex antilinear covectors.
* `TauCeti.RiemannSurface.OneForm.conjZeroOne`: the conjugate `(0,1)`-form of a `1`-form, a
  `(0,1)`-form (`TauCeti.RiemannSurface.OneForm.isZeroOneForm_conjZeroOne`); every complex valued
  `(0,1)`-covector is the conjugate of a unique complex covector
  (`TauCeti.RiemannSurface.isZeroOneForm_iff_existsUnique_conjCovector`).
* `TauCeti.RiemannSurface.antiholomorphicZeroOneForms X`: the conjugates of the holomorphic
  `1`-forms, with `TauCeti.RiemannSurface.holomorphicOneFormsEquivAntiholomorphic` and
  `TauCeti.RiemannSurface.finrank_antiholomorphicZeroOneForms`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1 and the proof of Theorem C.1.10 (the cokernel of `∂bar` on the trivial bundle).
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §9 (holomorphic and antiholomorphic differential forms).
-/

public section

open Module
open scoped ComplexConjugate Manifold TauCeti.ComplexManifold

noncomputable section

namespace TauCeti

/-! ### `(0,1)`-forms on a complex manifold -/

section ComplexManifold

open SmoothAlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) (⊤ : ℕ∞) M]

/-- On a complex manifold, a complex valued `(0,1)`-form at a point, for the almost complex
structure of the manifold, is a complex antilinear covector. -/
theorem isZeroOneForm_ofComplexManifold_iff {x : M} {η : E →L[ℝ] ℂ} :
    (ofComplexManifold E M).IsZeroOneForm (V := Bundle.Trivial M ℂ) (x := x) η ↔
      η ∈ antilinearCovectors E := by
  rw [mem_antilinearCovectors_iff]
  refine isZeroOneForm_iff.trans (forall_congr' fun v ↦ ?_)
  exact Iff.of_eq (congrArg (fun w ↦ η w = -(Complex.I • η v))
    (ofComplexManifold_apply (E := E) (M := M) x v))

end ComplexManifold

/-! ### Antiholomorphic `(0,1)`-forms on a Riemann surface -/

namespace RiemannSurface

open SmoothAlmostComplexStructure

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- On a Riemann surface, a real linear map `η : T_x X → ℂ` is a complex valued `(0,1)`-form at
`x` exactly when it is the conjugate of a unique complex covector at `x`. -/
theorem isZeroOneForm_iff_existsUnique_conjCovector [IsManifold 𝓘(ℂ) (⊤ : ℕ∞) X] {x : X}
    {η : ℂ →L[ℝ] ℂ} :
    (ofComplexManifold ℂ X).IsZeroOneForm (V := Bundle.Trivial X ℂ) (x := x) η ↔
      ∃! φ : TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ, conjCovector ℂ φ = η :=
  isZeroOneForm_ofComplexManifold_iff.trans mem_antilinearCovectors_iff_existsUnique

namespace OneForm

/-- The conjugate `(0,1)`-form `x ↦ conj ∘ ω x` of a `1`-form `ω` on a Riemann surface, a complex
valued `(0,1)`-form for the almost complex structure of `X`
(`TauCeti.RiemannSurface.OneForm.isZeroOneForm_conjZeroOne`). -/
def conjZeroOne (ω : OneForm X) (x : X) : TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℂ :=
  conjCovector ℂ (ω x)

@[simp]
theorem conjZeroOne_apply (ω : OneForm X) (x : X) (v : TangentSpace 𝓘(ℝ, ℂ) x) :
    ω.conjZeroOne x v = conj (ω x v) :=
  conjCovector_apply (E := ℂ) (ω x) v

/-- The conjugate of a `1`-form is a `(0,1)`-form for the almost complex structure of `X`. -/
theorem isZeroOneForm_conjZeroOne [IsManifold 𝓘(ℂ) (⊤ : ℕ∞) X] (ω : OneForm X) (x : X) :
    (ofComplexManifold ℂ X).IsZeroOneForm (V := Bundle.Trivial X ℂ) (ω.conjZeroOne x) :=
  isZeroOneForm_ofComplexManifold_iff.2 (conjCovector_mem_antilinearCovectors _)

variable (X) in
/-- Conjugation `ω ↦ (x ↦ conj ∘ ω x)` of `1`-forms, as a real linear map into the real
`1`-forms with complex values. -/
def conjZeroOneₗ : OneForm X →ₗ[ℝ] Π x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℂ where
  toFun ω := ω.conjZeroOne
  map_add' ω η := funext fun x ↦ map_add (conjCovector ℂ) (ω x) (η x)
  map_smul' c ω := funext fun x ↦ map_smul (conjCovector ℂ) c (ω x)

@[simp]
theorem conjZeroOneₗ_apply (ω : OneForm X) : conjZeroOneₗ X ω = ω.conjZeroOne :=
  (rfl)

/-- A `1`-form is determined by its conjugate `(0,1)`-form. -/
theorem conjZeroOne_injective : Function.Injective (conjZeroOne (X := X)) := fun _ _ h ↦
  funext fun x ↦ conjCovector_injective (congrFun h x)

end OneForm

variable (X) in
/-- The antiholomorphic `(0,1)`-forms on a Riemann surface: the conjugates `x ↦ conj ∘ ω x` of
the holomorphic `1`-forms `ω`, as a real subspace of the complex valued real `1`-forms. Each is a
`(0,1)`-form (`TauCeti.RiemannSurface.isZeroOneForm_of_mem_antiholomorphicZeroOneForms`). -/
def antiholomorphicZeroOneForms : Submodule ℝ (Π x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℂ) :=
  ((holomorphicOneForms X).restrictScalars ℝ).map (OneForm.conjZeroOneₗ X)

theorem mem_antiholomorphicZeroOneForms {η : Π x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℂ} :
    η ∈ antiholomorphicZeroOneForms X ↔ ∃ ω ∈ holomorphicOneForms X, ω.conjZeroOne = η :=
  Iff.rfl

theorem conjZeroOne_mem_antiholomorphicZeroOneForms {ω : OneForm X}
    (hω : ω ∈ holomorphicOneForms X) : ω.conjZeroOne ∈ antiholomorphicZeroOneForms X :=
  ⟨ω, hω, rfl⟩

/-- An antiholomorphic `(0,1)`-form is a `(0,1)`-form at every point. -/
theorem isZeroOneForm_of_mem_antiholomorphicZeroOneForms [IsManifold 𝓘(ℂ) (⊤ : ℕ∞) X]
    {η : Π x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℂ} (hη : η ∈ antiholomorphicZeroOneForms X)
    (x : X) : (ofComplexManifold ℂ X).IsZeroOneForm (V := Bundle.Trivial X ℂ) (η x) := by
  obtain ⟨ω, -, rfl⟩ := hη
  exact ω.isZeroOneForm_conjZeroOne x

variable (X) in
/-- Conjugation identifies the holomorphic `1`-forms with the antiholomorphic `(0,1)`-forms, as
real vector spaces. -/
def holomorphicOneFormsEquivAntiholomorphic :
    holomorphicOneForms X ≃ₗ[ℝ] antiholomorphicZeroOneForms X :=
  (((holomorphicOneForms X).restrictScalarsEquiv ℝ).restrictScalars ℝ).symm ≪≫ₗ
    Submodule.equivMapOfInjective (OneForm.conjZeroOneₗ X) OneForm.conjZeroOne_injective _

@[simp]
theorem coe_holomorphicOneFormsEquivAntiholomorphic_apply (ω : holomorphicOneForms X) :
    (holomorphicOneFormsEquivAntiholomorphic X ω : Π x : X, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℂ) =
      (ω : OneForm X).conjZeroOne :=
  (rfl)

/-- The real dimension of the antiholomorphic `(0,1)`-forms is twice the complex dimension of the
holomorphic `1`-forms. On a compact connected Riemann surface both are finite
(`TauCeti.RiemannSurface.finiteDimensional_antiholomorphicZeroOneForms`). -/
theorem finrank_antiholomorphicZeroOneForms :
    finrank ℝ (antiholomorphicZeroOneForms X) = 2 * finrank ℂ (holomorphicOneForms X) := by
  rw [← (holomorphicOneFormsEquivAntiholomorphic X).finrank_eq]
  exact finrank_real_eq_two_mul_finrank_complex (V := holomorphicOneForms X)

/-- On a compact connected Riemann surface the antiholomorphic `(0,1)`-forms form a
finite-dimensional real vector space. -/
instance finiteDimensional_antiholomorphicZeroOneForms [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X]
    [CompactSpace X] : FiniteDimensional ℝ (antiholomorphicZeroOneForms X) :=
  have : Module.Finite ℝ (holomorphicOneForms X) := Module.Finite.trans ℂ _
  Module.Finite.equiv (holomorphicOneFormsEquivAntiholomorphic X)

end RiemannSurface

end TauCeti
