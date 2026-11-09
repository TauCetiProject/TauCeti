/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Uniqueness
import TauCeti.Geometry.Manifold.IsManifold.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The vector space of Jacobi fields on a parameter set

`jacobiFieldSpace` represents Jacobi fields on a prescribed parameter set by their
canonical zero extensions. Regularity and covariant derivatives are taken only within
that set; no regularity across its boundary is asserted. Values outside the set are
fixed to zero, so equality is determined by the actual section on the set.

Initial value and covariant derivative give an injective linear map on a nonempty
preconnected parameter set. Consequently this space is finite dimensional, of dimension
at most twice the manifold dimension. Surjectivity of the initial-data map is not asserted.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 10
  (initial data and uniqueness for Jacobi fields).
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {s : Set ℝ}

/-- Jacobi fields on `s`, represented by their zero extensions outside `s`. -/
def jacobiFieldSpace (hγ : IsGeodesicCurveOn I γ s) :
    Submodule ℝ (∀ t, TangentSpace I (γ t)) where
  carrier := {V | IsJacobiFieldOn I γ V s ∧ ∀ t ∉ s, V t = 0}
  zero_mem' := ⟨isJacobiFieldOn_zero hγ, by simp⟩
  add_mem' := fun ⟨hV, hV₀⟩ ⟨hW, hW₀⟩ ↦
    ⟨hV.add hW, fun t ht ↦ by simp [hV₀ t ht, hW₀ t ht]⟩
  smul_mem' := fun c V ⟨hV, hV₀⟩ ↦
    ⟨hV.const_smul c, fun t ht ↦ by simp [hV₀ t ht]⟩

/-- Membership in the Jacobi-field space imposes no arbitrary data off the parameter set. -/
@[simp]
theorem mem_jacobiFieldSpace (hγ : IsGeodesicCurveOn I γ s)
    (V : ∀ t, TangentSpace I (γ t)) :
    V ∈ jacobiFieldSpace hγ ↔ IsJacobiFieldOn I γ V s ∧ ∀ t ∉ s, V t = 0 :=
  Iff.rfl

/-- Equality of Jacobi fields is determined on the parameter set. -/
@[ext]
theorem jacobiFieldSpace_ext {hγ : IsGeodesicCurveOn I γ s}
    {V W : jacobiFieldSpace hγ} (h : ∀ t ∈ s, V.val t = W.val t) : V = W := by
  apply Subtype.ext
  funext t
  by_cases ht : t ∈ s
  · exact h t ht
  · exact (V.property.2 t ht).trans (W.property.2 t ht).symm

/-- The section represented by an element of the Jacobi-field space solves the Jacobi equation. -/
theorem isJacobiFieldOn_of_mem_jacobiFieldSpace {hγ : IsGeodesicCurveOn I γ s}
    (V : jacobiFieldSpace hγ) : IsJacobiFieldOn I γ V.val s :=
  V.property.1

/-- Restrict a Jacobi field to its parameter set, using the canonical zero extension. -/
def IsJacobiFieldOn.toJacobiFieldSpace {V : ∀ t, TangentSpace I (γ t)}
    (hV : IsJacobiFieldOn I γ V s) : jacobiFieldSpace hV.isGeodesicCurveOn := by
  classical
  exact ⟨s.piecewise V 0, hV.congr (fun t ht ↦ by simp [ht]),
    fun t ht ↦ by simp [ht]⟩

/-- The canonical representative agrees with the original Jacobi field on its parameter set. -/
@[simp]
theorem IsJacobiFieldOn.toJacobiFieldSpace_apply {V : ∀ t, TangentSpace I (γ t)}
    (hV : IsJacobiFieldOn I γ V s) {t : ℝ} (ht : t ∈ s) :
    hV.toJacobiFieldSpace.val t = V t := by
  classical
  simp [IsJacobiFieldOn.toJacobiFieldSpace, ht]

/-- The canonical representative is zero outside the parameter set. -/
@[simp]
theorem IsJacobiFieldOn.toJacobiFieldSpace_apply_of_notMem
    {V : ∀ t, TangentSpace I (γ t)} (hV : IsJacobiFieldOn I γ V s)
    {t : ℝ} (ht : t ∉ s) : hV.toJacobiFieldSpace.val t = 0 :=
  hV.toJacobiFieldSpace.property.2 t ht

/-- Taking the canonical representative again does not change a Jacobi field. -/
@[simp]
theorem toJacobiFieldSpace_of_mem {hγ : IsGeodesicCurveOn I γ s}
    (V : jacobiFieldSpace hγ) :
    (isJacobiFieldOn_of_mem_jacobiFieldSpace V).toJacobiFieldSpace = V := by
  apply jacobiFieldSpace_ext
  intro t ht
  exact IsJacobiFieldOn.toJacobiFieldSpace_apply _ ht

/-- The initial value and covariant derivative of a Jacobi field, as a linear map. -/
def jacobiInitialData (hγ : IsGeodesicCurveOn I γ s) {a : ℝ} (ha : a ∈ s) :
    jacobiFieldSpace hγ →ₗ[ℝ] TangentSpace I (γ a) × TangentSpace I (γ a) where
  toFun V := (V.val a, alongCurveWithin (leviCivitaConnection I M) γ V.val s a)
  map_add' V W := by
    apply Prod.ext
    · rfl
    · exact alongCurveWithin_add _ γ V.val W.val s
        (V.property.1.differentiableWithinAt_sectionCoord ha)
        (W.property.1.differentiableWithinAt_sectionCoord ha)
  map_smul' c V := by
    apply Prod.ext
    · rfl
    · exact alongCurveWithin_const_smul _ γ V.val c s a

/-- Evaluation of the initial-data map. -/
@[simp]
theorem jacobiInitialData_apply (hγ : IsGeodesicCurveOn I γ s) {a : ℝ} (ha : a ∈ s)
    (V : jacobiFieldSpace hγ) :
    jacobiInitialData hγ ha V =
      (V.val a, alongCurveWithin (leviCivitaConnection I M) γ V.val s a) :=
  (rfl)

/-- Covariant differentiation within the parameter set ignores the zero extension. -/
@[simp]
theorem IsJacobiFieldOn.alongCurveWithin_toJacobiFieldSpace
    {V : ∀ t, TangentSpace I (γ t)} (hV : IsJacobiFieldOn I γ V s)
    {a : ℝ} (ha : a ∈ s) :
    alongCurveWithin (leviCivitaConnection I M) γ hV.toJacobiFieldSpace.val s a =
      alongCurveWithin (leviCivitaConnection I M) γ V s a :=
  alongCurveWithin_congr _ γ _
    (Filter.mem_of_superset self_mem_nhdsWithin fun _ ht ↦ hV.toJacobiFieldSpace_apply ht)
    (hV.toJacobiFieldSpace_apply ha)

/-- Uniqueness makes the initial-data map injective on a preconnected parameter set. -/
theorem jacobiInitialData_injective (hγ : IsGeodesicCurveOn I γ s)
    (hs : IsPreconnected s) {a : ℝ} (ha : a ∈ s) :
    Function.Injective (jacobiInitialData hγ ha) := by
  intro V W h
  apply jacobiFieldSpace_ext
  intro t ht
  exact V.property.1.eq_of_eq_of_alongCurveWithin_eq W.property.1 hs ha
    (congrArg Prod.fst h) (congrArg Prod.snd h) ht

/-- The space of Jacobi fields on a nonempty preconnected parameter set is finite dimensional. -/
theorem finiteDimensional_jacobiFieldSpace (hγ : IsGeodesicCurveOn I γ s)
    (hs : IsPreconnected s) {a : ℝ} (ha : a ∈ s) :
    FiniteDimensional ℝ (jacobiFieldSpace hγ) :=
  FiniteDimensional.of_injective (jacobiInitialData hγ ha)
    (jacobiInitialData_injective hγ hs ha)

/-- Initial data bound the dimension of the Jacobi-field space by twice the manifold dimension. -/
theorem finrank_jacobiFieldSpace_le (hγ : IsGeodesicCurveOn I γ s)
    (hs : IsPreconnected s) {a : ℝ} (ha : a ∈ s) :
    Module.finrank ℝ (jacobiFieldSpace hγ) ≤ 2 * Module.finrank ℝ E := by
  simpa [Module.finrank_prod, TauCeti.finrank_tangentSpace, two_mul] using
    LinearMap.finrank_le_finrank_of_injective
      (jacobiInitialData_injective hγ hs ha)

end TauCeti.Manifold
