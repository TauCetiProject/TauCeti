/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.FiniteDimensional
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Topology.Algebra.Module.ComplexSmulI

/-!
# Holomorphic `1`-forms and antiholomorphic `(0,1)`-forms

On a complex manifold `M` modelled on `E`, with its almost complex structure
`TauCeti.SmoothAlmostComplexStructure.ofComplexManifold E M`, a complex valued `(0,1)`-form at a
point, that is a `(0,1)`-form with values in the trivial bundle `M × ℂ`, is a real linear map
`η : E → ℂ` with `η (i • v) = -(i • η v)`: a complex antilinear covector
(`TauCeti.isZeroOneForm_ofComplexManifold_iff`). Complex conjugation `φ ↦ conj ∘ φ` is a real
linear bijection from the complex linear covectors `E →L[ℂ] ℂ` onto the complex antilinear ones
(`TauCeti.conjCovectorEquiv`).

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

* `TauCeti.antilinearCovectors E`: the complex antilinear real covectors on `E`.
* `TauCeti.conjCovector`, `TauCeti.conjCovectorEquiv`: conjugation of complex covectors, a real
  linear equivalence onto the complex antilinear covectors.
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

/-! ### Complex linear and complex antilinear covectors -/

section Covector

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The complex antilinear real covectors on a complex normed space `E`: the continuous real
linear maps `η : E → ℂ` with `η (i • v) = -(i • η v)`. -/
def antilinearCovectors : Submodule ℝ (E →L[ℝ] ℂ) where
  carrier := {η | ∀ v, η (Complex.I • v) = -(Complex.I • η v)}
  add_mem' {η η'} hη hη' v := by
    simp [hη v, hη' v]
    ring
  zero_mem' v := by simp
  smul_mem' c η hη v := by
    simp [hη v]
    ring

variable {E}

theorem mem_antilinearCovectors_iff {η : E →L[ℝ] ℂ} :
    η ∈ antilinearCovectors E ↔ ∀ v, η (Complex.I • v) = -(Complex.I • η v) :=
  Iff.rfl

variable (E) in
/-- The complex conjugate `v ↦ conj (φ v)` of a complex covector `φ`, as a real covector. It is
complex antilinear (`TauCeti.conjCovector_mem_antilinearCovectors`). -/
def conjCovector : (E →L[ℂ] ℂ) →ₗ[ℝ] E →L[ℝ] ℂ where
  toFun φ := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (φ.restrictScalars ℝ)
  map_add' φ ψ := by ext; simp
  map_smul' c φ := by ext; simp

@[simp]
theorem conjCovector_apply (φ : E →L[ℂ] ℂ) (v : E) : conjCovector E φ v = conj (φ v) :=
  (rfl)

/-- The conjugate of a complex covector is complex antilinear. -/
theorem conjCovector_mem_antilinearCovectors (φ : E →L[ℂ] ℂ) :
    conjCovector E φ ∈ antilinearCovectors E := fun v ↦ by
  simp

/-- Conjugation of complex covectors is injective. -/
theorem conjCovector_injective : Function.Injective (conjCovector E) := fun φ ψ h ↦ by
  ext v
  simpa using congrArg (fun η : E →L[ℝ] ℂ ↦ conj (η v)) h

private theorem conjAntilinear_aux (η : antilinearCovectors E) (v : E) :
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (η : E →L[ℝ] ℂ) (Complex.I • v) =
      Complex.I • (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (η : E →L[ℝ] ℂ) v := by
  simp [mem_antilinearCovectors_iff.1 η.2 v]

/-- The conjugate `v ↦ conj (η v)` of a complex antilinear covector, a complex linear covector. -/
private def conjAntilinear (η : antilinearCovectors E) : E →L[ℂ] ℂ :=
  ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (η : E →L[ℝ] ℂ)).complexOfMapISmul (conjAntilinear_aux η)

private theorem conjAntilinear_apply (η : antilinearCovectors E) (v : E) :
    conjAntilinear η v = conj ((η : E →L[ℝ] ℂ) v) :=
  congrFun (ContinuousLinearMap.coe_complexOfMapISmul _ (conjAntilinear_aux η)) v

variable (E) in
/-- Complex conjugation is a real linear equivalence between the complex linear covectors on `E`
and the complex antilinear ones. -/
def conjCovectorEquiv : (E →L[ℂ] ℂ) ≃ₗ[ℝ] antilinearCovectors E where
  toFun φ := ⟨conjCovector E φ, conjCovector_mem_antilinearCovectors φ⟩
  map_add' φ ψ := Subtype.ext (map_add _ φ ψ)
  map_smul' c φ := Subtype.ext (map_smul _ c φ)
  invFun := conjAntilinear
  left_inv φ := by ext v; simp [conjAntilinear_apply]
  right_inv η := by ext v; simp [conjAntilinear_apply]

@[simp]
theorem coe_conjCovectorEquiv_apply (φ : E →L[ℂ] ℂ) :
    (conjCovectorEquiv E φ : E →L[ℝ] ℂ) = conjCovector E φ :=
  (rfl)

@[simp]
theorem conjCovectorEquiv_symm_apply_apply (η : antilinearCovectors E) (v : E) :
    (conjCovectorEquiv E).symm η v = conj ((η : E →L[ℝ] ℂ) v) :=
  conjAntilinear_apply η v

/-- The complex antilinear covectors are exactly the conjugates of the complex linear ones. -/
theorem range_conjCovector : LinearMap.range (conjCovector E) = antilinearCovectors E := by
  refine le_antisymm ?_ fun η hη ↦ ⟨(conjCovectorEquiv E).symm ⟨η, hη⟩, ?_⟩
  · rintro _ ⟨φ, rfl⟩
    exact conjCovector_mem_antilinearCovectors φ
  · exact congrArg Subtype.val ((conjCovectorEquiv E).apply_symm_apply ⟨η, hη⟩)

/-- A real covector is complex antilinear exactly when it is the conjugate of a unique complex
linear covector. -/
theorem mem_antilinearCovectors_iff_existsUnique {η : E →L[ℝ] ℂ} :
    η ∈ antilinearCovectors E ↔ ∃! φ : E →L[ℂ] ℂ, conjCovector E φ = η := by
  refine ⟨fun hη ↦ ?_, fun ⟨φ, hφ, _⟩ ↦ hφ ▸ conjCovector_mem_antilinearCovectors φ⟩
  rw [← range_conjCovector] at hη
  obtain ⟨φ, rfl⟩ := hη
  exact ⟨φ, rfl, fun ψ h ↦ conjCovector_injective h⟩

end Covector

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
  (rfl)

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

/-- The real dimension of a complex subspace is twice its complex dimension. -/
private theorem finrank_real_submodule {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
    [IsScalarTower ℝ ℂ V] (p : Submodule ℂ V) : finrank ℝ p = 2 * finrank ℂ p := by
  rw [← Module.finrank_mul_finrank ℝ ℂ p, Complex.finrank_real_complex]

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
  rw [← (holomorphicOneFormsEquivAntiholomorphic X).finrank_eq, finrank_real_submodule]

/-- On a compact connected Riemann surface the antiholomorphic `(0,1)`-forms form a
finite-dimensional real vector space. -/
instance finiteDimensional_antiholomorphicZeroOneForms [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X]
    [CompactSpace X] : FiniteDimensional ℝ (antiholomorphicZeroOneForms X) :=
  have : Module.Finite ℝ (holomorphicOneForms X) := Module.Finite.trans ℂ _
  Module.Finite.equiv (holomorphicOneFormsEquivAntiholomorphic X)

end RiemannSurface

end TauCeti
