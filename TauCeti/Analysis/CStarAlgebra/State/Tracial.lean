/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.KMS.StateSpace
public import TauCeti.Analysis.CStarAlgebra.State.Unitization
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import TauCeti.Analysis.CStarAlgebra.Action.KMS.Dense
import TauCeti.RingTheory.TraceFunctional.Star

/-!
# Tracial states of C⋆-algebras

A *tracial state* of a possibly nonunital C⋆-algebra `A` is a state `τ`, a positive continuous
functional of norm one, with `τ (a * b) = τ (b * a)` for all `a, b`. These are exactly the
`0`-KMS states of the trivial dynamics, `TauCeti.CStarAction.isKMSState_zero_iff`, and the
predicate `PositiveContinuousLinearMap.IsTracialState` is defined that way, so that the
theory of KMS states applies to it directly. The tracial state space `TauCeti.tracialStates A`
is the corresponding set `T(A)` in the weak-* dual; `TauCeti.tracialStates_eq_kmsStates` identifies
it with the set of β-KMS states of the trivial dynamics for every `β`.

* `PositiveContinuousLinearMap.isTracialState_iff`: a tracial state is a positive functional of
  norm one with `τ (a * b) = τ (b * a)`; `PositiveContinuousLinearMap.isTracialState_iff_map_one`
  replaces the norm condition by `τ 1 = 1` for unital `A`.
* `PositiveContinuousLinearMap.isTracialState_iff_map_star_mul_self`: traciality can be tested
  on the pairs `(star a, a)`, `τ (star a * a) = τ (a * star a)`, by polarization.
* `PositiveContinuousLinearMap.isTracialState_iff_map_unitary_conj`: for unital `A`, a state is
  tracial exactly when it is invariant under every inner automorphism `a ↦ u * a * star u`,
  because a unital C⋆-algebra is spanned by its unitaries. The underlying linear-algebra fact,
  for any complex linear map, is `LinearMap.forall_map_mul_comm_iff_forall_map_unitary_conj`.
* `PositiveContinuousLinearMap.IsTracialState.comp`: tracial states pull back to tracial states
  along unital star homomorphisms of unital algebras; without a unit, the pullback is tracial
  when it has norm one (`IsTracialState.comp_of_norm_eq_one`), in particular along surjections
  (`IsTracialState.comp_of_surjective`).
* `PositiveContinuousLinearMap.isTracialState_iff_of_comm`: on a commutative C⋆-algebra every
  state is tracial, so `T(A) = S(A)` (`TauCeti.tracialStates_eq_stateSpace`).
* `PositiveContinuousLinearMap.isTracialState_unitization_iff`: the extension `τ⁺¹` of a positive
  functional to the unitization (`PositiveContinuousLinearMap.unitization`) is a tracial state
  exactly when `τ` is.
* `PositiveContinuousLinearMap.not_isTracialState_of_mul_star_add_mul_star_eq_one`: a unital
  C⋆-algebra containing two isometries `s, t` with `s * star s + t * star t = 1` has no tracial
  state.

The set `T(A)` is convex (`TauCeti.convex_tracialStates`), contains every weak-* limit point
of itself that has norm one (`TauCeti.closure_tracialStates_inter_subset`), and for unital `A`
is weak-* closed and compact (`TauCeti.isClosed_tracialStates`,
`TauCeti.isCompact_tracialStates`). Without a unit it need not be weak-* closed: on `c₀` the
point evaluations are tracial states converging weak-* to `0`. It is always closed in the norm
topology of the continuous dual (`TauCeti.isClosed_preimage_toWeakDual_tracialStates`), and its
elements are the functionals of tracial states
(`TauCeti.mem_tracialStates_iff_exists_isTracialState`).

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Mem. Amer.
  Math. Soc. 184 (2006), no. 865, Chapter 2.
* A. Tikuisis, S. White, W. Winter, *Quasidiagonality of nuclear C⋆-algebras*, Ann. of Math.
  185 (2017), Section 1.
-/

public section

open Set WeakDual
open scoped ComplexOrder

namespace LinearMap

variable {A M : Type*} [CStarAlgebra A] [AddCommGroup M] [Module ℂ M]

/-- **Unitary criterion for traciality.** A complex linear map `f` on a unital C⋆-algebra
satisfies `f (a * b) = f (b * a)` for all `a, b` exactly when it is invariant under every inner
automorphism `a ↦ u * a * star u`. The converse direction uses that a unital C⋆-algebra is
spanned by its unitaries. -/
theorem forall_map_mul_comm_iff_forall_map_unitary_conj (f : A →ₗ[ℂ] M) :
    (∀ a b, f (a * b) = f (b * a)) ↔ ∀ u ∈ unitary A, ∀ a, f (u * a * star u) = f a := by
  refine ⟨fun h u hu a => ?_, fun h a b => ?_⟩
  · rw [h, ← mul_assoc, Unitary.star_mul_self_of_mem hu, one_mul]
  -- `a ↦ f (a * b)` and `a ↦ f (b * a)` are linear and agree on the unitaries, which span `A`
  have key : f ∘ₗ LinearMap.mulRight ℂ b = f ∘ₗ LinearMap.mulLeft ℂ b := by
    refine LinearMap.ext_on (CStarAlgebra.span_unitary A) fun u hu => ?_
    have := h u hu (b * u)
    rw [mul_assoc, mul_assoc, Unitary.mul_star_self_of_mem hu, mul_one] at this
    simpa using this
  simpa using LinearMap.congr_fun key a

end LinearMap

namespace PositiveContinuousLinearMap

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {τ : A →P[ℂ] ℂ}

/-- A *tracial state* of a possibly nonunital C⋆-algebra: a `0`-KMS state of the trivial
dynamics. By `PositiveContinuousLinearMap.isTracialState_iff` this says exactly that the
positive functional `τ` has norm one and satisfies `τ (a * b) = τ (b * a)`. The zero algebra
has no tracial state. -/
def IsTracialState (τ : A →P[ℂ] ℂ) : Prop :=
  (TauCeti.CStarAction.trivial : TauCeti.CStarAction (Multiplicative ℝ) A).IsKMSState 0 τ

/-- A tracial state is a positive functional of norm one with `τ (a * b) = τ (b * a)`. -/
theorem isTracialState_iff :
    τ.IsTracialState ↔ ‖(τ : A →L[ℂ] ℂ)‖ = 1 ∧ ∀ a b, τ (a * b) = τ (b * a) :=
  TauCeti.CStarAction.isKMSState_zero_iff

/-- For the trivial dynamics the β-KMS states are the tracial states, at every inverse
temperature `β`. -/
@[simp]
theorem _root_.TauCeti.CStarAction.isKMSState_trivial_iff_isTracialState {β : ℝ} :
    (TauCeti.CStarAction.trivial : TauCeti.CStarAction (Multiplicative ℝ) A).IsKMSState β τ ↔
      τ.IsTracialState :=
  TauCeti.CStarAction.isKMSState_trivial_iff.trans isTracialState_iff.symm

/-- A tracial state has norm one. -/
theorem IsTracialState.norm_eq_one (hτ : τ.IsTracialState) : ‖(τ : A →L[ℂ] ℂ)‖ = 1 :=
  (isTracialState_iff.1 hτ).1

/-- A tracial state satisfies `τ (a * b) = τ (b * a)`. -/
theorem IsTracialState.map_mul_comm (hτ : τ.IsTracialState) (a b : A) :
    τ (a * b) = τ (b * a) :=
  (isTracialState_iff.1 hτ).2 a b

/-- **Polarization criterion.** A positive functional is a tracial state exactly when it has
norm one and `τ (star a * a) = τ (a * star a)` for every `a`. -/
theorem isTracialState_iff_map_star_mul_self :
    τ.IsTracialState ↔
      ‖(τ : A →L[ℂ] ℂ)‖ = 1 ∧ ∀ a, τ (star a * a) = τ (a * star a) := by
  rw [isTracialState_iff]
  exact and_congr_right fun _ =>
    LinearMap.forall_map_mul_comm_iff_forall_map_star_mul_self (τ : A →ₗ[ℂ] ℂ)

/-- On a commutative C⋆-algebra every state is tracial. -/
theorem isTracialState_iff_of_comm {B : Type*} [NonUnitalCommCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] {σ : B →P[ℂ] ℂ} : σ.IsTracialState ↔ ‖(σ : B →L[ℂ] ℂ)‖ = 1 :=
  TauCeti.CStarAction.isKMSState_zero_iff_of_comm

variable {B F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B] {σ : B →P[ℂ] ℂ}

/-- **Pullback of tracial states.** Composing a tracial state of `B` with a star homomorphism
`f : A → B` gives a tracial state of `A` as soon as the composite has norm one. Without the norm
condition the composite is only a tracial positive functional: for the corner `z ↦ z • e₁₁` of
`ℂ` in `2 × 2` matrices, the normalized trace pulls back to `z ↦ z / 2`. -/
theorem IsTracialState.comp_of_norm_eq_one (hσ : σ.IsTracialState) (f : F)
    (hnorm : ‖((σ.comp (.ofClass f) : A →P[ℂ] ℂ) : A →L[ℂ] ℂ)‖ = 1) :
    (σ.comp (.ofClass f)).IsTracialState :=
  isTracialState_iff.2 ⟨hnorm, fun a b => by simp [hσ.map_mul_comm (f a)]⟩

/-- **Pullback of tracial states along surjections.** Composing a tracial state with a surjective
star homomorphism gives a tracial state. -/
theorem IsTracialState.comp_of_surjective (hσ : σ.IsTracialState) (f : F)
    (hf : Function.Surjective f) : (σ.comp (.ofClass f)).IsTracialState :=
  hσ.comp_of_norm_eq_one f <| (opNorm_comp_ofClass_of_surjective σ f hf).trans hσ.norm_eq_one

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {τ : A →P[ℂ] ℂ}

/-- On a unital C⋆-algebra, a positive functional is a tracial state exactly when `τ 1 = 1` and
`τ (a * b) = τ (b * a)`. -/
theorem isTracialState_iff_map_one :
    τ.IsTracialState ↔ τ 1 = 1 ∧ ∀ a b, τ (a * b) = τ (b * a) := by
  rw [isTracialState_iff, ← ofReal_opNorm_eq_map_one]
  exact_mod_cast Iff.rfl

/-- A tracial state of a unital C⋆-algebra takes the value `1` at `1`. -/
theorem IsTracialState.map_one (hτ : τ.IsTracialState) : τ 1 = 1 :=
  (isTracialState_iff_map_one.1 hτ).1

/-- A tracial state is invariant under the inner automorphism `a ↦ u * a * star u` of a unitary
`u`. -/
theorem IsTracialState.map_unitary_conj (hτ : τ.IsTracialState) {u : A} (hu : u ∈ unitary A)
    (a : A) : τ (u * a * star u) = τ a :=
  (LinearMap.forall_map_mul_comm_iff_forall_map_unitary_conj (τ : A →ₗ[ℂ] ℂ)).1
    hτ.map_mul_comm u hu a

/-- **Unitary criterion.** On a unital C⋆-algebra, a positive functional is a tracial state
exactly when `τ 1 = 1` and `τ` is invariant under every inner automorphism `a ↦ u * a * star u`.
This is `LinearMap.forall_map_mul_comm_iff_forall_map_unitary_conj` for positive functionals. -/
theorem isTracialState_iff_map_unitary_conj :
    τ.IsTracialState ↔ τ 1 = 1 ∧ ∀ u ∈ unitary A, ∀ a, τ (u * a * star u) = τ a := by
  rw [isTracialState_iff_map_one]
  exact and_congr_right fun _ =>
    LinearMap.forall_map_mul_comm_iff_forall_map_unitary_conj (τ : A →ₗ[ℂ] ℂ)

/-- **No trace in the presence of two complementary isometries.** If a unital C⋆-algebra
contains isometries `s, t` (`star s * s = 1 = star t * t`) whose range projections add up to
the identity, `s * star s + t * star t = 1`, then it has no tracial state, since
`τ 1 = τ (s * star s) + τ (t * star t) = τ (star s * s) + τ (star t * t) = 2 τ 1`. Such
isometries exist, for example, among the bounded operators on an infinite-dimensional Hilbert
space. -/
theorem not_isTracialState_of_mul_star_add_mul_star_eq_one {s t : A} (hs : star s * s = 1)
    (ht : star t * t = 1) (hst : s * star s + t * star t = 1) : ¬ τ.IsTracialState := by
  intro hτ
  have h := congrArg τ hst
  rw [map_add, hτ.map_mul_comm s, hτ.map_mul_comm t, hs, ht, hτ.map_one] at h
  norm_num at h

variable {B F : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [AlgHomClass F ℂ A B] [StarHomClass F A B] {σ : B →P[ℂ] ℂ}

/-- **Pullback of tracial states along unital star homomorphisms.** Composing a tracial state of
`B` with a unital star homomorphism `f : A → B` gives a tracial state of `A`; in particular a
tracial state restricts to a tracial state on every C⋆-subalgebra containing the unit. -/
theorem IsTracialState.comp (hσ : σ.IsTracialState) (f : F) :
    (σ.comp (.ofClass f)).IsTracialState :=
  hσ.comp_of_norm_eq_one f <| Complex.ofReal_injective <| by
    simpa [hσ.map_one] using ofReal_opNorm_eq_map_one (σ.comp (.ofClass f))

end Unital

end PositiveContinuousLinearMap

namespace TauCeti

open PositiveContinuousLinearMap

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {φ : WeakDual ℂ A}

variable (A) in
/-- The **tracial state space** `T(A)` of a C⋆-algebra `A`: the tracial states, as a subset of
the weak-* dual `WeakDual ℂ A`. It is the set of `0`-KMS states of the trivial dynamics. -/
noncomputable def tracialStates : Set (WeakDual ℂ A) :=
  (CStarAction.trivial : CStarAction (Multiplicative ℝ) A).kmsStates 0

/-- The tracial state space is the set of β-KMS states of the trivial dynamics, at every inverse
temperature `β`, so the theory of KMS state spaces applies to `T(A)`. -/
theorem tracialStates_eq_kmsStates (β : ℝ) :
    tracialStates A = (CStarAction.trivial : CStarAction (Multiplicative ℝ) A).kmsStates β := by
  ext φ
  simp only [tracialStates, CStarAction.mem_kmsStates_iff,
    CStarAction.isKMSState_trivial_iff_isTracialState]

/-- A positive functional lies in `T(A)` exactly when it is a tracial state. -/
@[simp]
theorem toWeakDual_mem_tracialStates_iff {τ : A →P[ℂ] ℂ} :
    StrongDual.toWeakDual (τ : A →L[ℂ] ℂ) ∈ tracialStates A ↔ τ.IsTracialState :=
  CStarAction.toWeakDual_mem_kmsStates_iff

/-- The elements of `T(A)` are the states `φ` with `φ (a * b) = φ (b * a)`. -/
theorem mem_tracialStates_iff :
    φ ∈ tracialStates A ↔ φ ∈ stateSpace A ∧ ∀ a b, φ (a * b) = φ (b * a) := by
  simp [tracialStates, CStarAction.mem_kmsStates_iff_forall_isEntireAnalytic,
    CStarAction.isEntireAnalytic_trivial, mem_stateSpace_iff, and_assoc]

/-- Tracial states are states. -/
theorem tracialStates_subset_stateSpace : tracialStates A ⊆ stateSpace A :=
  CStarAction.kmsStates_subset_stateSpace

/-- **Convexity of `T(A)`.** Convex combinations of tracial states are tracial states. -/
theorem convex_tracialStates : Convex ℝ (tracialStates A) :=
  CStarAction.convex_kmsStates

/-- **Weak-* limits of tracial states.** A weak-* limit point of tracial states which has norm
one is a tracial state. The norm condition cannot be dropped without a unit: on `c₀` the point
evaluations converge weak-* to `0`. -/
theorem closure_tracialStates_inter_subset :
    closure (tracialStates A) ∩ {φ | ‖toStrongDual φ‖ = 1} ⊆ tracialStates A :=
  CStarAction.closure_kmsStates_inter_subset

/-- The elements of `T(A)` are the functionals induced by tracial states. -/
theorem mem_tracialStates_iff_exists_isTracialState :
    φ ∈ tracialStates A ↔ ∃ τ : A →P[ℂ] ℂ, τ.IsTracialState ∧
      StrongDual.toWeakDual (τ : A →L[ℂ] ℂ) = φ := by
  simp only [tracialStates, CStarAction.mem_kmsStates_iff,
    CStarAction.isKMSState_trivial_iff_isTracialState]

/-- In the norm topology of the continuous dual, the tracial state space is closed. -/
theorem isClosed_preimage_toWeakDual_tracialStates :
    IsClosed (StrongDual.toWeakDual ⁻¹' tracialStates A) := by
  have h : StrongDual.toWeakDual ⁻¹' tracialStates A = StrongDual.toWeakDual ⁻¹' stateSpace A ∩
      ⋂ a : A, ⋂ b : A, {x : StrongDual ℂ A | x (a * b) = x (b * a)} := by
    ext x
    simp [mem_tracialStates_iff]
  rw [h]
  exact isClosed_preimage_toWeakDual_stateSpace.inter <| isClosed_iInter fun a =>
    isClosed_iInter fun b => isClosed_eq (ContinuousLinearMap.apply ℂ ℂ (a * b)).continuous
      (ContinuousLinearMap.apply ℂ ℂ (b * a)).continuous

/-- On a commutative C⋆-algebra every state is tracial: `T(A) = S(A)`. -/
theorem tracialStates_eq_stateSpace {B : Type*} [NonUnitalCommCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] : tracialStates B = stateSpace B := by
  ext φ
  simp [mem_tracialStates_iff, mul_comm]

variable {B F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- **Pullback of tracial states along surjections.** Precomposition with a surjective star
homomorphism `A → B` maps `T(B)` to `T(A)`. -/
theorem mapsTo_pullbackFunctional_tracialStates_of_surjective (f : F)
    (hf : Function.Surjective f) :
    MapsTo (pullbackFunctional A f) (tracialStates B) (tracialStates A) := by
  intro φ hφ
  rw [mem_tracialStates_iff] at hφ ⊢
  exact ⟨mapsTo_pullbackFunctional_stateSpace_of_surjective f hf hφ.1,
    fun a b => by simp [hφ.2 (f a)]⟩

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- For unital `A`, the tracial state space is weak-* closed. -/
theorem isClosed_tracialStates : IsClosed (tracialStates A) :=
  CStarAction.isClosed_kmsStates

/-- **Weak-* compactness of `T(A)`.** For unital `A`, the tracial state space is weak-*
compact. -/
theorem isCompact_tracialStates : IsCompact (tracialStates A) :=
  CStarAction.isCompact_kmsStates

variable {B F : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [AlgHomClass F ℂ A B] [StarHomClass F A B]

/-- **Pullback of tracial states along unital star homomorphisms.** Precomposition with a unital
star homomorphism `A → B` maps `T(B)` to `T(A)`. -/
theorem mapsTo_pullbackFunctional_tracialStates (f : F) :
    MapsTo (pullbackFunctional A f) (tracialStates B) (tracialStates A) := by
  intro φ hφ
  rw [mem_tracialStates_iff] at hφ ⊢
  exact ⟨mapsTo_pullbackFunctional_stateSpace f hφ.1, fun a b => by simp [hφ.2 (f a)]⟩

end Unital

end TauCeti

namespace PositiveContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {τ : A →P[ℂ] ℂ}

/-- The extension `τ⁺¹` is a tracial state of `Unitization ℂ A` exactly when `τ` is a tracial
state of `A`. -/
@[simp]
theorem isTracialState_unitization_iff : τ.unitization.IsTracialState ↔ τ.IsTracialState := by
  simp only [isTracialState_iff, norm_unitization, and_congr_right_iff]
  refine fun _ => ⟨fun h a b => ?_, unitization_map_mul_comm⟩
  simpa only [← Unitization.inr_mul, unitization_apply_inr] using h a b

/-- The extension of a tracial state to the unitization is a tracial state. -/
theorem IsTracialState.unitization (hτ : τ.IsTracialState) : τ.unitization.IsTracialState :=
  isTracialState_unitization_iff.mpr hτ

end PositiveContinuousLinearMap
