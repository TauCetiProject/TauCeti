/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Space
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Tangential
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Convexity
import TauCeti.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Conjugate parameters and their multiplicity

Two parameters are conjugate along a geodesic when a Jacobi field, nonzero somewhere
on the parameter set, vanishes at both. The multiplicity is the dimension of the
endpoint-zero Jacobi-field space. Canonical zero extensions ensure that nonzero fields
really are nonzero on the parameter set, rather than merely outside it.

For distinct parameters on a preconnected set, every endpoint-zero Jacobi field is
normal: its pairing with the velocity is affine and vanishes at both endpoints.
Its initial covariant derivative determines it injectively and lies in the orthogonal
complement of the initial velocity. Thus multiplicity is at most `n - 1` when the
velocity is nonzero. Nonpositive sectional curvature rules out conjugate parameters
on any preconnected parameter set.

These statements do not identify multiplicity with a singular exponential differential
or with index-form nullity.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 10
  (conjugate points and normal Jacobi fields).
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {s : Set ℝ} {a b : ℝ}

/-- The subspace of Jacobi fields vanishing at the two specified parameters. -/
def endpointJacobiFieldSpace (hγ : IsGeodesicCurveOn I γ s) (a b : ℝ) :
    Submodule ℝ (jacobiFieldSpace hγ) where
  carrier := {V | V.val a = 0 ∧ V.val b = 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := fun ⟨hVa, hVb⟩ ⟨hWa, hWb⟩ ↦
    ⟨by simp [hVa, hWa], by simp [hVb, hWb]⟩
  smul_mem' := fun c V ⟨hVa, hVb⟩ ↦ ⟨by simp [hVa], by simp [hVb]⟩

/-- Endpoint-zero fields are exactly the kernel of the two endpoint evaluations. -/
@[simp]
theorem mem_endpointJacobiFieldSpace (hγ : IsGeodesicCurveOn I γ s)
    (V : jacobiFieldSpace hγ) :
    V ∈ endpointJacobiFieldSpace hγ a b ↔ V.val a = 0 ∧ V.val b = 0 :=
  Iff.rfl

/-- Swapping endpoints does not change the endpoint-zero solution space. -/
theorem endpointJacobiFieldSpace_comm (hγ : IsGeodesicCurveOn I γ s) :
    endpointJacobiFieldSpace hγ a b = endpointJacobiFieldSpace hγ b a := by
  ext V
  simp only [mem_endpointJacobiFieldSpace, and_comm]

variable (I γ s a b) in
/-- Conjugacy requires distinct parameters in the set and a Jacobi field nonzero on that set. -/
def IsConjugateOn : Prop :=
  a ∈ s ∧ b ∈ s ∧ a ≠ b ∧
    ∃ V : ∀ t, TangentSpace I (γ t), IsJacobiFieldOn I γ V s ∧
      V a = 0 ∧ V b = 0 ∧ ∃ t ∈ s, V t ≠ 0

/-- The characteristic conditions for conjugacy along the prescribed parameter set. -/
theorem isConjugateOn_iff : IsConjugateOn I γ s a b ↔
    a ∈ s ∧ b ∈ s ∧ a ≠ b ∧
      ∃ V : ∀ t, TangentSpace I (γ t), IsJacobiFieldOn I γ V s ∧
        V a = 0 ∧ V b = 0 ∧ ∃ t ∈ s, V t ≠ 0 :=
  Iff.rfl

/-- A parameter is not conjugate to itself. -/
@[simp]
theorem not_isConjugateOn_self : ¬ IsConjugateOn I γ s a a := by
  simp [isConjugateOn_iff]

/-- Conjugacy is symmetric in the two parameters. -/
theorem isConjugateOn_comm : IsConjugateOn I γ s a b ↔ IsConjugateOn I γ s b a := by
  constructor <;> rintro ⟨ha, hb, hab, V, hV, hVa, hVb, hne⟩ <;>
    exact ⟨hb, ha, hab.symm, V, hV, hVb, hVa, hne⟩

/-- Conjugacy is equivalent to a nonzero endpoint-zero Jacobi field in the intrinsic space. -/
theorem isConjugateOn_iff_exists_ne_zero (hγ : IsGeodesicCurveOn I γ s)
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    IsConjugateOn I γ s a b ↔ ∃ V : endpointJacobiFieldSpace hγ a b, V ≠ 0 := by
  classical
  constructor
  · rintro ⟨_, _, _, V, hV, hVa, hVb, t, ht, hVt⟩
    let W : endpointJacobiFieldSpace hγ a b :=
      ⟨hV.toJacobiFieldSpace, by simpa [ha, hb] using And.intro hVa hVb⟩
    refine ⟨W, fun hW ↦ hVt ?_⟩
    have h := congrArg (fun J : endpointJacobiFieldSpace hγ a b ↦ J.val.val t) hW
    simpa [W, ht] using h
  · rintro ⟨V, hV⟩
    refine ⟨ha, hb, hab, V.val.val, isJacobiFieldOn_of_mem_jacobiFieldSpace V.val,
      V.property.1, V.property.2, ?_⟩
    by_contra! hzero
    apply hV
    apply Subtype.ext
    exact jacobiFieldSpace_ext hzero

/-- An endpoint-zero Jacobi field has initial covariant derivative orthogonal to the velocity,
provided the two parameters are distinct and belong to a preconnected parameter set. -/
theorem inner_endpointJacobiFieldSpace_deriv_velocity_eq_zero
    {hγ : IsGeodesicCurveOn I γ s} (V : endpointJacobiFieldSpace hγ a b)
    (hs : IsPreconnected s) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    ⟪alongCurveWithin (leviCivitaConnection I M) γ V.val.val s a,
      curveVelocityWithin I γ s a⟫_ℝ = 0 := by
  have h := (isJacobiFieldOn_of_mem_jacobiFieldSpace V.val).inner_curveVelocityWithin_eq hs ha hb
  rw [V.property.1, V.property.2, inner_zero_left, inner_zero_left, zero_add] at h
  exact (mul_eq_zero.1 h.symm).resolve_left (sub_ne_zero.2 hab.symm)

/-- Every endpoint-zero Jacobi field is normal on a preconnected parameter set. -/
theorem inner_endpointJacobiFieldSpace_velocity_eq_zero
    {hγ : IsGeodesicCurveOn I γ s} (V : endpointJacobiFieldSpace hγ a b)
    (hs : IsPreconnected s) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    {t : ℝ} (ht : t ∈ s) : ⟪V.val.val t, curveVelocityWithin I γ s t⟫_ℝ = 0 := by
  rw [(isJacobiFieldOn_of_mem_jacobiFieldSpace V.val).inner_curveVelocityWithin_eq hs ha ht,
    V.property.1,
    inner_zero_left, inner_endpointJacobiFieldSpace_deriv_velocity_eq_zero V hs ha hb hab,
    mul_zero, add_zero]

/-- The initial covariant derivative on the endpoint-zero Jacobi-field space. -/
def endpointJacobiInitialDerivative (hγ : IsGeodesicCurveOn I γ s) (ha : a ∈ s) (b : ℝ) :
    endpointJacobiFieldSpace hγ a b →ₗ[ℝ] TangentSpace I (γ a) :=
  (LinearMap.snd ℝ (TangentSpace I (γ a)) (TangentSpace I (γ a))).comp
    ((jacobiInitialData hγ ha).comp (endpointJacobiFieldSpace hγ a b).subtype)

/-- Evaluation of the initial derivative on endpoint-zero fields. -/
@[simp]
theorem endpointJacobiInitialDerivative_apply (hγ : IsGeodesicCurveOn I γ s)
    (ha : a ∈ s) (V : endpointJacobiFieldSpace hγ a b) :
    endpointJacobiInitialDerivative hγ ha b V =
      alongCurveWithin (leviCivitaConnection I M) γ V.val.val s a := by
  simp [endpointJacobiInitialDerivative]

/-- The initial derivative determines an endpoint-zero Jacobi field uniquely. -/
theorem endpointJacobiInitialDerivative_injective (hγ : IsGeodesicCurveOn I γ s)
    (hs : IsPreconnected s) (ha : a ∈ s) :
    Function.Injective (endpointJacobiInitialDerivative hγ ha b) := by
  intro V W h
  apply Subtype.ext
  apply jacobiInitialData_injective hγ hs ha
  simp only [jacobiInitialData_apply]
  apply Prod.ext
  · exact V.property.1.trans W.property.1.symm
  · simpa only [endpointJacobiInitialDerivative_apply] using h

/-- Conjugate multiplicity is the dimension of the endpoint-zero solution space.
Preconnectedness and an initial parameter ensure that this dimension is finite. -/
def conjugateMultiplicity (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s)
    (ha : a ∈ s) (b : ℝ) : ℕ :=
  let := finiteDimensional_jacobiFieldSpace hγ hs ha
  Module.finrank ℝ (endpointJacobiFieldSpace hγ a b)

/-- The dimension formula defining conjugate multiplicity. -/
@[simp]
theorem conjugateMultiplicity_eq_finrank (hγ : IsGeodesicCurveOn I γ s)
    (hs : IsPreconnected s) (ha : a ∈ s) :
    conjugateMultiplicity hγ hs ha b = Module.finrank ℝ (endpointJacobiFieldSpace hγ a b) :=
  (rfl)

/-- Multiplicity is unchanged when the endpoints are exchanged. -/
theorem conjugateMultiplicity_comm (hγ : IsGeodesicCurveOn I γ s)
    (hs : IsPreconnected s) (ha : a ∈ s) (hb : b ∈ s) :
    conjugateMultiplicity hγ hs ha b = conjugateMultiplicity hγ hs hb a := by
  simp only [conjugateMultiplicity_eq_finrank]
  exact congrArg (fun p : Submodule ℝ (jacobiFieldSpace hγ) ↦ Module.finrank ℝ p)
    (endpointJacobiFieldSpace_comm hγ)

/-- Multiplicity is positive exactly when the two parameters are conjugate. -/
theorem conjugateMultiplicity_pos_iff (hγ : IsGeodesicCurveOn I γ s)
    (hs : IsPreconnected s) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    0 < conjugateMultiplicity hγ hs ha b ↔ IsConjugateOn I γ s a b := by
  let := finiteDimensional_jacobiFieldSpace hγ hs ha
  unfold conjugateMultiplicity
  exact (Module.finrank_pos_iff_exists_ne_zero
    (R := ℝ) (M := endpointJacobiFieldSpace hγ a b)).trans
      (isConjugateOn_iff_exists_ne_zero hγ ha hb hab).symm

/-- Along a geodesic with nonzero velocity, distinct conjugate parameters have multiplicity
at most the manifold dimension minus one. -/
theorem conjugateMultiplicity_le (hγ : IsGeodesicCurveOn I γ s)
    (hs : IsPreconnected s) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hv : curveVelocityWithin I γ s a ≠ 0) :
    conjugateMultiplicity hγ hs ha b ≤ Module.finrank ℝ E - 1 := by
  let N := (ℝ ∙ curveVelocityWithin I γ s a)ᗮ
  let D : endpointJacobiFieldSpace hγ a b →ₗ[ℝ] N :=
    (endpointJacobiInitialDerivative hγ ha b).codRestrict N fun V ↦
      Submodule.mem_orthogonal_singleton_iff_inner_left.2
        (by simpa only [endpointJacobiInitialDerivative_apply] using
          inner_endpointJacobiFieldSpace_deriv_velocity_eq_zero V hs ha hb hab)
  have hD : Function.Injective D := fun V W h ↦
    endpointJacobiInitialDerivative_injective hγ hs ha (congrArg Subtype.val h)
  have hdim := (ℝ ∙ curveVelocityWithin I γ s a).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hv, TauCeti.finrank_tangentSpace] at hdim
  have hle := LinearMap.finrank_le_finrank_of_injective hD
  dsimp [conjugateMultiplicity, N] at *
  omega

/-- Nonpositive sectional curvature excludes conjugate parameters on a preconnected set. -/
theorem not_isConjugateOn_of_sectionalCurvature_nonpos (hs : IsPreconnected s)
    (hK : ∀ r ∈ s, ∀ u v : TangentSpace I (γ r), LinearIndependent ℝ ![u, v] →
      (leviCivitaConnection I M).sectionalCurvature (isMetricCompatible_leviCivitaConnection I)
        (γ r) u v ≤ 0) : ¬ IsConjugateOn I γ s a b := by
  rintro ⟨ha, hb, hab, V, hV, hVa, hVb, t, ht, hVt⟩
  exact hVt (hV.eq_zero_of_endpoints_eq_zero_of_sectionalCurvature_nonpos
    hs hK ha hb hab hVa hVb ht)

end TauCeti.Manifold
