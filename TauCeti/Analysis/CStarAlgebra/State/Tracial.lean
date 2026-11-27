/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import TauCeti.Analysis.CStarAlgebra.Action.KMS.StateSpace
public import TauCeti.Analysis.CStarAlgebra.State.Unitization
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Positive
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import TauCeti.Analysis.CStarAlgebra.Action.KMS.Dense
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
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
  on the pairs `(star a, a)`, `τ (star a * a) = τ (a * star a)`, by polarization
  (`TauCeti.mem_tracialStates_iff_map_star_mul_self` on `T(A)`).
* `PositiveContinuousLinearMap.isTracialState_iff_map_unitary_conj`: for unital `A`, a state is
  tracial exactly when it is invariant under every inner automorphism `a ↦ u * a * star u`,
  because a unital C⋆-algebra is spanned by its unitaries
  (`TauCeti.mem_tracialStates_iff_map_unitary_conj` on `T(A)`). The underlying linear-algebra fact,
  for any complex linear map, is `LinearMap.forall_map_mul_comm_iff_forall_map_unitary_conj`.
* `PositiveContinuousLinearMap.IsTracialState.comp`,
  `PositiveContinuousLinearMap.IsTracialState.domRestrict`: tracial states pull back to tracial
  states along unital star homomorphisms of unital algebras and restrict to closed unital star
  subalgebras; without a unit, the pullback or restriction is tracial when it has norm one
  (`IsTracialState.comp_of_norm_eq_one`, `IsTracialState.domRestrict_of_norm_eq_one`), in
  particular along surjections (`IsTracialState.comp_of_surjective`,
  `isTracialState_comp_iff_of_surjective`), and lifting along a surjective star homomorphism via
  `PositiveContinuousLinearMap.liftOfSurjective` preserves the trace identity and tracial states
  (`liftOfSurjective_map_mul_comm`, `isTracialState_liftOfSurjective_iff`).
* `PositiveContinuousLinearMap.isTracialState_iff_of_comm`: on a commutative C⋆-algebra every
  state is tracial, so `T(A) = S(A)` (`TauCeti.tracialStates_eq_stateSpace`).
* `PositiveContinuousLinearMap.isTracialState_unitization_iff`: the extension `τ⁺¹` of a positive
  functional to the unitization (`PositiveContinuousLinearMap.unitization`) is a tracial state
  exactly when `τ` is.
* `PositiveContinuousLinearMap.not_isTracialState_of_mul_star_add_mul_star_le_one`: a unital
  C⋆-algebra containing two isometries `s, t` with `s * star s + t * star t ≤ 1` has no tracial
  state (`TauCeti.tracialStates_eq_empty_of_mul_star_add_mul_star_le_one`).

The set `T(A)` is convex (`TauCeti.convex_tracialStates`), norm-closed in the continuous dual
(`TauCeti.isClosed_preimage_toWeakDual_tracialStates`), contains every weak-* limit point of itself
that has norm one (`TauCeti.closure_tracialStates_inter_subset`, so it is relatively weak-* closed
in `stateSpace A`, `TauCeti.closure_tracialStates_inter_stateSpace`), and for unital `A` is weak-*
closed and compact (`TauCeti.isClosed_tracialStates`, `TauCeti.isCompact_tracialStates`) and equal
to the weak-* closed convex hull of its extreme points
(`TauCeti.closure_convexHull_extremePoints_tracialStates`). Without a unit it need not be weak-*
closed: on `c₀` the point evaluations are tracial states converging weak-* to `0`. Its elements are
the functionals of tracial states (`TauCeti.mem_tracialStates_iff_exists_isTracialState`).

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Mem. Amer.
  Math. Soc. 184 (2006), no. 865, Chapters 2–3.
* G. K. Pedersen, *C⋆-Algebras and Their Automorphism Groups*, second edition, Chapter 3.
* A. Tikuisis, S. White, W. Winter, *Quasidiagonality of nuclear C⋆-algebras*, Ann. of Math.
  185 (2017), Section 1.
-/

public section

open Filter Set WeakDual
open scoped CStarAlgebra ComplexOrder Topology

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
  (isTracialState_iff.mp hτ).left

/-- A tracial state is nonzero. -/
theorem IsTracialState.ne_zero (hτ : τ.IsTracialState) : τ ≠ 0 := by
  rintro rfl
  simpa using hτ.norm_eq_one

/-- A C⋆-algebra admitting a tracial state is nontrivial. -/
theorem IsTracialState.nontrivial (hτ : τ.IsTracialState) : Nontrivial A :=
  TauCeti.nontrivial_of_mem_stateSpace (τ.toWeakDual_mem_stateSpace_iff.mpr hτ.norm_eq_one)

/-- A tracial state satisfies `τ (a * b) = τ (b * a)`. -/
theorem IsTracialState.map_mul_comm (hτ : τ.IsTracialState) (a b : A) :
    τ (a * b) = τ (b * a) :=
  (isTracialState_iff.mp hτ).right a b

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

/-- **Pointwise limits of tracial states.** If tracial states converge pointwise to a positive
functional of norm one, then the limit is a tracial state. -/
theorem IsTracialState.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {τ' : ι → A →P[ℂ] ℂ}
    (hτ' : ∀ᶠ i in l, (τ' i).IsTracialState) (hlim : ∀ a, Tendsto (fun i => τ' i a) l (𝓝 (τ a)))
    (hnorm : ‖(τ : A →L[ℂ] ℂ)‖ = 1) : τ.IsTracialState :=
  TauCeti.CStarAction.IsKMSState.of_tendsto hτ' hlim hnorm

section Pullback

variable {B F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B] {σ : B →P[ℂ] ℂ}

/-- **Pullback of tracial states.** Composing a tracial state of `B` with a star homomorphism
`f : A → B` gives a tracial state of `A` as soon as the composite has norm one. Without the norm
condition the composite is only a tracial positive functional: for the corner `z ↦ z • e₁₁` of
`ℂ` in `2 × 2` matrices, the normalized trace pulls back to `z ↦ z / 2`. -/
theorem IsTracialState.comp_of_norm_eq_one (hσ : σ.IsTracialState) (f : F)
    (hnorm : ‖((σ.comp (.ofClass f) : A →P[ℂ] ℂ) : A →L[ℂ] ℂ)‖ = 1) :
    (σ.comp (.ofClass f)).IsTracialState :=
  isTracialState_iff.mpr ⟨hnorm, fun a b => by simp [hσ.map_mul_comm (f a)]⟩

/-- **Pullback of tracial states along surjections.** Composing a tracial state with a surjective
star homomorphism gives a tracial state. -/
theorem IsTracialState.comp_of_surjective (hσ : σ.IsTracialState) (f : F)
    (hf : Function.Surjective f) : (σ.comp (.ofClass f)).IsTracialState :=
  hσ.comp_of_norm_eq_one f <| (opNorm_comp_ofClass_of_surjective σ f hf).trans hσ.norm_eq_one

/-- Along a surjective star homomorphism `f : A → B`, a positive functional `σ` on `B` is a tracial
state if and only if its pullback `σ ∘ f` is a tracial state on `A`. -/
theorem isTracialState_comp_iff_of_surjective (f : F) (hf : Function.Surjective f) :
    (σ.comp (.ofClass f)).IsTracialState ↔ σ.IsTracialState :=
  TauCeti.CStarAction.isKMSState_comp_iff_of_surjective
    (TauCeti.CStarAction.Hom.mk (.ofClass f) fun _ _ => by simp) hf

/-- Lifting a tracial positive functional along a surjective star homomorphism preserves the
trace identity. -/
theorem liftOfSurjective_map_mul_comm (τ : A →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → τ a = 0) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (x y : B) :
    τ.liftOfSurjective f hf hker (x * y) = τ.liftOfSurjective f hf hker (y * x) := by
  obtain ⟨a, rfl⟩ := hf x
  obtain ⟨b, rfl⟩ := hf y
  rw [← map_mul, ← map_mul, liftOfSurjective_apply, liftOfSurjective_apply, hτ]

/-- `τ.liftOfSurjective f hf hker` is a tracial state if and only if `τ` is a tracial state. -/
@[simp]
theorem isTracialState_liftOfSurjective_iff (τ : A →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → τ a = 0) :
    (τ.liftOfSurjective f hf hker).IsTracialState ↔ τ.IsTracialState := by
  rw [← isTracialState_comp_iff_of_surjective f hf, liftOfSurjective_comp_ofClass]

end Pullback

/-- Restricting a tracial state `τ` to a closed nonunital star subalgebra `S` gives a tracial state
whenever the restriction still has norm one. -/
theorem IsTracialState.domRestrict_of_norm_eq_one (hτ : τ.IsTracialState)
    (S : NonUnitalStarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (hnorm : ‖(τ.domRestrict S : S →L[ℂ] ℂ)‖ = 1) :
    (τ.domRestrict S).IsTracialState := by
  rw [← comp_ofClass_eq_domRestrict τ (NonUnitalStarSubalgebraClass.subtype S) (fun _ => rfl)]
    at hnorm ⊢
  exact hτ.comp_of_norm_eq_one (NonUnitalStarSubalgebraClass.subtype S) hnorm

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
  (isTracialState_iff_map_one.mp hτ).left

/-- On a unital C⋆-algebra, a positive functional is a tracial state if and only if `τ 1 = 1` and
`τ (star a * a) = τ (a * star a)` for all `a : A`. -/
theorem isTracialState_iff_map_one_and_map_star_mul_self :
    τ.IsTracialState ↔ τ 1 = 1 ∧ ∀ a : A, τ (star a * a) = τ (a * star a) := by
  rw [isTracialState_iff_map_one]
  exact and_congr_right fun _ =>
    LinearMap.forall_map_mul_comm_iff_forall_map_star_mul_self (τ : A →ₗ[ℂ] ℂ)

/-- A tracial state is invariant under the inner automorphism `a ↦ u * a * star u` of a unitary
`u`. -/
theorem IsTracialState.map_unitary_conj (hτ : τ.IsTracialState) {u : A} (hu : u ∈ unitary A)
    (a : A) : τ (u * a * star u) = τ a :=
  (LinearMap.forall_map_mul_comm_iff_forall_map_unitary_conj (τ : A →ₗ[ℂ] ℂ)).mp
    hτ.map_mul_comm u hu a

/-- **Unitary criterion.** On a unital C⋆-algebra, a positive functional is a tracial state
exactly when `τ 1 = 1` and `τ` is invariant under every inner automorphism `a ↦ u * a * star u`.
This is `LinearMap.forall_map_mul_comm_iff_forall_map_unitary_conj` for positive functionals. -/
theorem isTracialState_iff_map_unitary_conj :
    τ.IsTracialState ↔ τ 1 = 1 ∧ ∀ u ∈ unitary A, ∀ a, τ (u * a * star u) = τ a := by
  rw [isTracialState_iff_map_one]
  exact and_congr_right fun _ =>
    LinearMap.forall_map_mul_comm_iff_forall_map_unitary_conj (τ : A →ₗ[ℂ] ℂ)

/-- **No trace in the presence of two orthogonal isometries.** If a unital C⋆-algebra contains
isometries `s, t` (`star s * s = 1 = star t * t`) with `s * star s + t * star t ≤ 1` (for instance
on `B(ℓ²)` or any properly infinite C⋆-algebra), then it has no tracial state. -/
theorem not_isTracialState_of_mul_star_add_mul_star_le_one {s t : A} (hs : star s * s = 1)
    (ht : star t * t = 1) (hst : s * star s + t * star t ≤ 1) : ¬ τ.IsTracialState := by
  intro hτ
  have hle : τ (s * star s + t * star t) ≤ τ 1 := τ.mono hst
  rw [map_add, hτ.map_mul_comm s, hτ.map_mul_comm t, hs, ht, hτ.map_one] at hle
  have hre := (Complex.le_def.mp hle).left
  norm_num at hre

/-- Pulling a tracial state back along a star homomorphism between unital C⋆-algebras that maps `1`
to `1` yields a tracial state. -/
theorem IsTracialState.comp_of_map_one {B F : Type*}
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    {σ : B →P[ℂ] ℂ} (hσ : σ.IsTracialState) (f : F) (hf : f 1 = 1) :
    (σ.comp (.ofClass f)).IsTracialState :=
  hσ.comp_of_norm_eq_one f ((opNorm_comp_ofClass_of_map_one σ f hf).trans hσ.norm_eq_one)

section PullbackUnital

variable {B F : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [AlgHomClass F ℂ A B] [StarHomClass F A B] {σ : B →P[ℂ] ℂ}

/-- **Pullback of tracial states along unital star homomorphisms.** Composing a tracial state of
`B` with a unital star homomorphism `f : A → B` gives a tracial state of `A`; in particular a
tracial state restricts to a tracial state on every C⋆-subalgebra containing the unit. -/
theorem IsTracialState.comp (hσ : σ.IsTracialState) (f : F) :
    (σ.comp (.ofClass f)).IsTracialState :=
  hσ.comp_of_map_one f (_root_.map_one f)

end PullbackUnital

/-- Restricting a tracial state to a closed unital star subalgebra `S ⊆ A` yields a tracial state
of `S` without any norm hypothesis. -/
theorem IsTracialState.domRestrict (hτ : τ.IsTracialState) (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] :
    (τ.domRestrict S).IsTracialState :=
  comp_ofClass_eq_domRestrict τ S.subtype (fun _ => rfl) ▸ hτ.comp S.subtype

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

/-- Elements of `T(A)` are the weak-* dual images of tracial states `A →P[ℂ] ℂ`. -/
theorem mem_tracialStates_iff_exists_isTracialState :
    φ ∈ tracialStates A ↔
      ∃ τ : A →P[ℂ] ℂ, τ.IsTracialState ∧ StrongDual.toWeakDual (τ : A →L[ℂ] ℂ) = φ :=
  CStarAction.mem_kmsStates_iff

/-- The elements of `T(A)` are the states `φ` with `φ (a * b) = φ (b * a)`. -/
theorem mem_tracialStates_iff :
    φ ∈ tracialStates A ↔ φ ∈ stateSpace A ∧ ∀ a b, φ (a * b) = φ (b * a) := by
  simp [tracialStates, CStarAction.mem_kmsStates_iff_forall_isEntireAnalytic,
    CStarAction.isEntireAnalytic_trivial, mem_stateSpace_iff, and_assoc]

/-- Every functional in `T(A)` satisfies `φ (a * b) = φ (b * a)`. -/
theorem map_mul_comm_of_mem_tracialStates (hφ : φ ∈ tracialStates A) (a b : A) :
    φ (a * b) = φ (b * a) :=
  (mem_tracialStates_iff.mp hφ).right a b

/-- **Polarization description of `T(A)`.** A functional belongs to `tracialStates A` if and only
if it is a state satisfying `φ (star a * a) = φ (a * star a)` for all `a : A`. -/
theorem mem_tracialStates_iff_map_star_mul_self :
    φ ∈ tracialStates A ↔ φ ∈ stateSpace A ∧ ∀ a : A, φ (star a * a) = φ (a * star a) := by
  rw [mem_tracialStates_iff]
  exact and_congr_right fun _ =>
    LinearMap.forall_map_mul_comm_iff_forall_map_star_mul_self (toStrongDual φ : A →ₗ[ℂ] ℂ)

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

/-- **Relative weak-* closedness.** `tracialStates A` is weak-* closed in `stateSpace A`. -/
@[simp]
theorem closure_tracialStates_inter_stateSpace :
    closure (tracialStates A) ∩ stateSpace A = tracialStates A := by
  refine Subset.antisymm (fun φ ⟨hclos, hstate⟩ => ?_)
    (subset_inter subset_closure tracialStates_subset_stateSpace)
  exact closure_tracialStates_inter_subset
    ⟨hclos, norm_toStrongDual_of_mem_stateSpace hstate⟩

/-- In the norm topology of the continuous dual, `tracialStates A` is closed. -/
theorem isClosed_preimage_toWeakDual_tracialStates :
    IsClosed (StrongDual.toWeakDual ⁻¹' tracialStates A) := by
  have h : StrongDual.toWeakDual ⁻¹' tracialStates A =
      (StrongDual.toWeakDual ⁻¹' stateSpace A) ∩
        ⋂ (a : A) (b : A), {ψ : StrongDual ℂ A | ψ (a * b) = ψ (b * a)} := by
    ext ψ
    simp [mem_tracialStates_iff]
  rw [h]
  refine isClosed_preimage_toWeakDual_stateSpace.inter <|
    isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq ((ContinuousLinearMap.apply ℂ ℂ (a * b)).continuous)
        ((ContinuousLinearMap.apply ℂ ℂ (b * a)).continuous)

/-- On a subsingleton (zero) C⋆-algebra, the tracial state space is empty. -/
@[simp]
theorem tracialStates_eq_empty [Subsingleton A] : tracialStates A = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun _ hφ =>
    not_nontrivial A (nontrivial_of_mem_stateSpace (tracialStates_subset_stateSpace hφ))

/-- On a commutative C⋆-algebra every state is tracial: `T(A) = S(A)`. -/
@[simp]
theorem tracialStates_eq_stateSpace {B : Type*} [NonUnitalCommCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] : tracialStates B = stateSpace B := by
  ext φ
  simp [mem_tracialStates_iff, mul_comm]

section PullbackWeakDual

variable {B F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- **Pullback of tracial states along surjections.** Precomposition with a surjective star
homomorphism `A → B` maps `T(B)` to `T(A)`. -/
theorem mapsTo_pullbackFunctional_tracialStates_of_surjective (f : F)
    (hf : Function.Surjective f) :
    MapsTo (pullbackFunctional A f) (tracialStates B) (tracialStates A) := by
  intro φ hφ
  rw [mem_tracialStates_iff] at hφ ⊢
  exact ⟨mapsTo_pullbackFunctional_stateSpace_of_surjective f hf hφ.left,
    fun a b => by simp [hφ.right (f a)]⟩

end PullbackWeakDual

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {φ : WeakDual ℂ A}

/-- On a unital C⋆-algebra, membership in `tracialStates A` unfolds to positivity, `φ 1 = 1`, and
the trace identity. -/
theorem mem_tracialStates_iff_map_one :
    φ ∈ tracialStates A ↔
      (∀ a, 0 ≤ a → 0 ≤ φ a) ∧ φ 1 = 1 ∧ ∀ a b : A, φ (a * b) = φ (b * a) := by
  rw [mem_tracialStates_iff, mem_stateSpace_iff_map_one, and_assoc]

/-- **Unitary invariance description of `T(A)`.** On a unital C⋆-algebra, a functional belongs to
`tracialStates A` if and only if it is a state invariant under unitary conjugation. -/
theorem mem_tracialStates_iff_map_unitary_conj :
    φ ∈ tracialStates A ↔
      φ ∈ stateSpace A ∧ ∀ u ∈ unitary A, ∀ a : A, φ (u * a * star u) = φ a := by
  rw [mem_tracialStates_iff]
  exact and_congr_right fun _ =>
    LinearMap.forall_map_mul_comm_iff_forall_map_unitary_conj (toStrongDual φ : A →ₗ[ℂ] ℂ)

/-- For unital `A`, the tracial state space is weak-* closed. -/
theorem isClosed_tracialStates : IsClosed (tracialStates A) :=
  CStarAction.isClosed_kmsStates

/-- **Weak-* compactness of `T(A)`.** For unital `A`, the tracial state space is weak-*
compact. -/
theorem isCompact_tracialStates : IsCompact (tracialStates A) :=
  CStarAction.isCompact_kmsStates

/-- **Krein–Milman for tracial states.** For unital `A`, `tracialStates A` is the weak-* closed
convex hull of its extreme points (including when `tracialStates A` is empty). -/
theorem closure_convexHull_extremePoints_tracialStates :
    closure (convexHull ℝ (extremePoints ℝ (tracialStates A))) = tracialStates A :=
  closure_convexHull_extremePoints isCompact_tracialStates convex_tracialStates

/-- Every nonempty weak-* compact tracial state space of a unital C⋆-algebra has an extreme
tracial state. -/
theorem extremePoints_tracialStates_nonempty (h : (tracialStates A).Nonempty) :
    (extremePoints ℝ (tracialStates A)).Nonempty :=
  isCompact_tracialStates.extremePoints_nonempty h

/-- The only tracial state of `ℂ` is the identity functional. -/
theorem tracialStates_complex :
    tracialStates ℂ = {StrongDual.toWeakDual (ContinuousLinearMap.id ℂ ℂ)} := by
  rw [tracialStates_eq_stateSpace, stateSpace_complex]

/-- If a unital C⋆-algebra contains two isometries with orthogonal ranges
(`s * star s + t * star t ≤ 1`), its tracial state space is empty. -/
theorem tracialStates_eq_empty_of_mul_star_add_mul_star_le_one {s t : A}
    (hs : star s * s = 1) (ht : star t * t = 1) (hst : s * star s + t * star t ≤ 1) :
    tracialStates A = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro ψ hψ
  obtain ⟨τ, hτ, -⟩ := mem_tracialStates_iff_exists_isTracialState.mp hψ
  exact not_isTracialState_of_mul_star_add_mul_star_le_one hs ht hst hτ

section PullbackUnitalWeakDual

variable {B F : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [AlgHomClass F ℂ A B] [StarHomClass F A B]

/-- **Pullback of tracial states along unital star homomorphisms.** Precomposition with a unital
star homomorphism `A → B` maps `T(B)` to `T(A)`. -/
theorem mapsTo_pullbackFunctional_tracialStates (f : F) :
    MapsTo (pullbackFunctional A f) (tracialStates B) (tracialStates A) := by
  intro ψ hψ
  rw [mem_tracialStates_iff] at hψ ⊢
  exact ⟨mapsTo_pullbackFunctional_stateSpace f hψ.left, fun a b => by simp [hψ.right (f a)]⟩

end PullbackUnitalWeakDual

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
