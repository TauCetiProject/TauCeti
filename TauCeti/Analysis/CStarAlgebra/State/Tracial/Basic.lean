/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import TauCeti.Analysis.CStarAlgebra.Action.KMS.StateSpace
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Positive
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
import TauCeti.RingTheory.TraceFunctional.Polarization

/-!
# Tracial states and the tracial state space of a C⋆-algebra

A *tracial state* of a possibly nonunital C⋆-algebra `A` is a positive continuous linear functional
`τ : A →P[ℂ] ℂ` of norm one satisfying the trace identity `τ (a * b) = τ (b * a)` for all
`a, b : A`. Equivalently, `τ` is a `0`-KMS state of the trivial real dynamics on `A`, and the
*tracial state space* `TauCeti.tracialStateSpace A ⊆ WeakDual ℂ A` is the set of `0`-KMS states of
`TauCeti.CStarAction.trivial`.

Specializing the KMS theory to `0` and the trivial action immediately gives convexity of
`tracialStateSpace A` without assuming a unit (`TauCeti.convex_tracialStateSpace`), relative
weak-* closedness inside `TauCeti.stateSpace A`
(`TauCeti.closure_tracialStateSpace_inter_stateSpace`), weak-* closedness and compactness for
unital `A` (`TauCeti.isClosed_tracialStateSpace`, `TauCeti.isCompact_tracialStateSpace`), and
pullback along star homomorphisms that preserve norm `1` (in particular surjective ones).

In addition, this file establishes algebraic and norm-theoretic characterizations specific to
traces:

* **Polarization** (`PositiveContinuousLinearMap.isTracialState_iff_star_mul_self`,
  `TauCeti.mem_tracialStateSpace_iff_star_mul_self`): a state is tracial if and only if
  `τ (star a * a) = τ (a * star a)` for all `a : A`, via
  `TauCeti.forall_map_mul_comm_iff_star_mul_self`.
* **Unitary invariance** (`TauCeti.CStarAlgebra.forall_map_mul_comm_iff_unitary_conj`,
  `PositiveContinuousLinearMap.isTracialState_iff_unitary_conj`,
  `TauCeti.mem_tracialStateSpace_iff_unitary_conj`): on a unital C⋆-algebra, a linear map or state
  is tracial if and only if it is invariant under conjugation `a ↦ u * a * star u` by every unitary
  `u`, because every element is a linear combination of four unitaries
  (`CStarAlgebra.exists_sum_four_unitary`).
* **Unital pullback and restriction** (`PositiveContinuousLinearMap.IsTracialState.comp_of_map_one`,
  `PositiveContinuousLinearMap.IsTracialState.comp_unital`,
  `PositiveContinuousLinearMap.IsTracialState.domRestrict`,
  `TauCeti.mapsTo_pullbackFunctional_tracialStateSpace`): pulling a positive functional back along
  a unital star homomorphism preserves its norm (`PositiveContinuousLinearMap.opNorm_comp_ofClass`),
  so tracial states pull back along arbitrary unital star homomorphisms and restrict to closed
  unital star subalgebras.
* **Obstruction from orthogonal isometries**
  (`PositiveContinuousLinearMap.IsTracialState.false_of_isometries`,
  `TauCeti.tracialStateSpace_eq_empty_of_isometries`): a unital C⋆-algebra containing two
  isometries with orthogonal ranges admits no tracial state.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Memoirs of the
  American Mathematical Society 184 (2006), no. 865, Chapter 3.
* G. K. Pedersen, *C⋆-Algebras and Their Automorphism Groups*, second edition, Chapter 3.
-/

public section

open Complex Set Filter WeakDual
open scoped ComplexOrder Topology

namespace TauCeti.CStarAlgebra

/-- **Unitary conjugation criterion for traciality.** On a unital C⋆-algebra `A`, a `ℂ`-linear map
`f` into any `ℂ`-module satisfies `f (a * b) = f (b * a)` for all `a, b` if and only if it is
invariant under every inner automorphism `a ↦ u * a * star u` (`u : unitary A`). -/
theorem forall_map_mul_comm_iff_unitary_conj {A M F : Type*} [CStarAlgebra A]
    [AddCommGroup M] [Module ℂ M] [FunLike F A M] [LinearMapClass F ℂ A M] (f : F) :
    (∀ a b : A, f (a * b) = f (b * a)) ↔
      ∀ (u : unitary A) (a : A), f ((u : A) * a * star (u : A)) = f a := by
  refine ⟨fun h u a => ?_, fun h a b => ?_⟩
  · rw [h ((u : A) * a) (star (u : A)), ← mul_assoc, Unitary.coe_star_mul_self, one_mul]
  · -- Evaluating `h u` at `b * u` shows that unitaries are central in `f`; then expand `a` as a
    -- linear combination of four unitaries.
    have hu (u : unitary A) : f ((u : A) * b) = f (b * (u : A)) := by
      have h1 := h u (b * (u : A))
      rwa [mul_assoc (u : A) (b * (u : A)) (star (u : A)), mul_assoc b,
        ← Unitary.coe_star, Unitary.coe_mul_star_self, mul_one] at h1
    obtain ⟨u, c, rfl, -⟩ := _root_.CStarAlgebra.exists_sum_four_unitary a
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, map_sum, map_smul, hu]

end TauCeti.CStarAlgebra

namespace PositiveContinuousLinearMap

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {τ : A →P[ℂ] ℂ}

/-- A positive continuous linear functional `τ : A →P[ℂ] ℂ` on a C⋆-algebra is a **tracial state**
if it has norm `1` and satisfies `τ (a * b) = τ (b * a)` for all `a, b : A`. It is defined as a
`0`-KMS state of the trivial real action on `A`. -/
def IsTracialState (τ : A →P[ℂ] ℂ) : Prop :=
  (TauCeti.CStarAction.trivial : TauCeti.CStarAction (Multiplicative ℝ) A).IsKMSState 0 τ

/-- A positive functional is a tracial state if and only if it is a `0`-KMS state of the trivial
real action. -/
theorem isTracialState_iff_isKMSState_trivial :
    τ.IsTracialState ↔
      (TauCeti.CStarAction.trivial : TauCeti.CStarAction (Multiplicative ℝ) A).IsKMSState 0 τ :=
  (Iff.rfl)

/-- Characterization of tracial states by norm one and the trace identity. -/
theorem isTracialState_iff :
    τ.IsTracialState ↔ ‖(τ : A →L[ℂ] ℂ)‖ = 1 ∧ ∀ a b : A, τ (a * b) = τ (b * a) :=
  TauCeti.CStarAction.isKMSState_zero_iff

/-- A tracial state has operator norm one. -/
theorem IsTracialState.norm_eq_one (hτ : τ.IsTracialState) : ‖(τ : A →L[ℂ] ℂ)‖ = 1 :=
  (isTracialState_iff.mp hτ).1

/-- A tracial state is nonzero. -/
theorem IsTracialState.ne_zero (hτ : τ.IsTracialState) : τ ≠ 0 := by
  rintro rfl
  simpa using hτ.norm_eq_one

/-- A C⋆-algebra admitting a tracial state is nontrivial. -/
theorem IsTracialState.nontrivial (hτ : τ.IsTracialState) : Nontrivial A := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply hτ.ne_zero
  ext x
  simp [Subsingleton.elim x 0]

/-- A tracial state vanishes on commutators: `τ (a * b) = τ (b * a)`. -/
theorem IsTracialState.mul_comm (hτ : τ.IsTracialState) (a b : A) : τ (a * b) = τ (b * a) :=
  (isTracialState_iff.mp hτ).2 a b

/-- **Polarization criterion for tracial states.** A positive continuous linear functional is a
tracial state if and only if it has norm one and satisfies `τ (star a * a) = τ (a * star a)` for
every `a : A`. -/
theorem isTracialState_iff_star_mul_self :
    τ.IsTracialState ↔ ‖(τ : A →L[ℂ] ℂ)‖ = 1 ∧ ∀ a : A, τ (star a * a) = τ (a * star a) := by
  rw [isTracialState_iff, TauCeti.forall_map_mul_comm_iff_star_mul_self]

/-- On a commutative C⋆-algebra, a positive functional is a tracial state if and only if it has
norm one. -/
theorem isTracialState_iff_of_comm {B : Type*} [NonUnitalCommCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] {ψ : B →P[ℂ] ℂ} :
    ψ.IsTracialState ↔ ‖(ψ : B →L[ℂ] ℂ)‖ = 1 :=
  TauCeti.CStarAction.isKMSState_zero_iff_of_comm

/-- **Pointwise limits of tracial states.** If tracial states converge pointwise to a positive
functional of norm one, then the limit is a tracial state. -/
theorem IsTracialState.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {τ' : ι → A →P[ℂ] ℂ}
    (hτ' : ∀ᶠ i in l, (τ' i).IsTracialState) (hlim : ∀ a, Tendsto (fun i => τ' i a) l (𝓝 (τ a)))
    (hnorm : ‖(τ : A →L[ℂ] ℂ)‖ = 1) : τ.IsTracialState :=
  TauCeti.CStarAction.IsKMSState.of_tendsto hτ' hlim hnorm

section Pullback

variable {B F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- **Pullback of tracial states.** Pulling a tracial state `τ` of `B` back along a star
homomorphism `f : A → B` gives a tracial state of `A` whenever the composite has norm one. -/
theorem IsTracialState.comp {τ : B →P[ℂ] ℂ} (hτ : τ.IsTracialState) (f : F)
    (hnorm : ‖((τ.comp (.ofClass f) : A →P[ℂ] ℂ) : A →L[ℂ] ℂ)‖ = 1) :
    (τ.comp (.ofClass f)).IsTracialState :=
  TauCeti.CStarAction.IsKMSState.comp hτ
    (TauCeti.CStarAction.Hom.mk (.ofClass f) fun _ _ => by simp) hnorm

/-- **Pullback of tracial states along surjections.** Pulling a tracial state back along a
surjective star homomorphism gives a tracial state without any norm hypothesis. -/
theorem IsTracialState.comp_of_surjective {τ : B →P[ℂ] ℂ} (hτ : τ.IsTracialState) (f : F)
    (hf : Function.Surjective f) : (τ.comp (.ofClass f)).IsTracialState :=
  TauCeti.CStarAction.IsKMSState.comp_of_surjective hτ
    (TauCeti.CStarAction.Hom.mk (.ofClass f) fun _ _ => by simp) hf

/-- Along a surjective star homomorphism `f : A → B`, a positive functional `τ` on `B` is a tracial
state if and only if its pullback `τ ∘ f` is a tracial state on `A`. -/
theorem isTracialState_comp_iff_of_surjective {τ : B →P[ℂ] ℂ} (f : F)
    (hf : Function.Surjective f) :
    (τ.comp (.ofClass f)).IsTracialState ↔ τ.IsTracialState :=
  TauCeti.CStarAction.isKMSState_comp_iff_of_surjective
    (TauCeti.CStarAction.Hom.mk (.ofClass f) fun _ _ => by simp) hf

end Pullback

/-- Restricting a tracial state `τ` to a closed nonunital star subalgebra `S` gives a tracial state
whenever the restriction still has norm one. -/
theorem IsTracialState.domRestrict_of_norm_eq_one (hτ : τ.IsTracialState)
    (S : NonUnitalStarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (hnorm : ‖(τ.domRestrict S : S →L[ℂ] ℂ)‖ = 1) :
    (τ.domRestrict S).IsTracialState := by
  simp [isTracialState_iff, hnorm, hτ.mul_comm]

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {τ : A →P[ℂ] ℂ}

/-- A tracial state on a unital C⋆-algebra takes the value `1` at `1`. -/
theorem IsTracialState.map_one (hτ : τ.IsTracialState) : τ 1 = 1 := by
  rw [← τ.ofReal_opNorm_eq_map_one, hτ.norm_eq_one, Complex.ofReal_one]

/-- On a unital C⋆-algebra, a positive functional is a tracial state if and only if `τ 1 = 1` and
`τ (a * b) = τ (b * a)` for all `a, b : A`. -/
theorem isTracialState_iff_map_one :
    τ.IsTracialState ↔ τ 1 = 1 ∧ ∀ a b : A, τ (a * b) = τ (b * a) := by
  rw [isTracialState_iff, ← τ.ofReal_opNorm_eq_map_one]
  exact and_congr_left' (by norm_cast)

/-- On a unital C⋆-algebra, a positive functional is a tracial state if and only if `τ 1 = 1` and
`τ (star a * a) = τ (a * star a)` for all `a : A`. -/
theorem isTracialState_iff_map_one_and_star_mul_self :
    τ.IsTracialState ↔ τ 1 = 1 ∧ ∀ a : A, τ (star a * a) = τ (a * star a) := by
  rw [isTracialState_iff_map_one, TauCeti.forall_map_mul_comm_iff_star_mul_self]

/-- A tracial state on a unital C⋆-algebra is invariant under conjugation by every unitary. -/
theorem IsTracialState.unitary_conj (hτ : τ.IsTracialState) (u : unitary A) (a : A) :
    τ ((u : A) * a * star (u : A)) = τ a :=
  (TauCeti.CStarAlgebra.forall_map_mul_comm_iff_unitary_conj τ).mp hτ.mul_comm u a

/-- **Unitary invariance criterion for tracial states.** On a unital C⋆-algebra, a positive
functional is a tracial state if and only if `τ 1 = 1` and `τ (u * a * star u) = τ a` for every
unitary `u` and every `a : A`. -/
theorem isTracialState_iff_unitary_conj :
    τ.IsTracialState ↔
      τ 1 = 1 ∧ ∀ (u : unitary A) (a : A), τ ((u : A) * a * star (u : A)) = τ a := by
  rw [isTracialState_iff_map_one, TauCeti.CStarAlgebra.forall_map_mul_comm_iff_unitary_conj]

/-- Pulling a tracial state back along a star homomorphism between unital C⋆-algebras that maps `1`
to `1` yields a tracial state. -/
theorem IsTracialState.comp_of_map_one {B F : Type*}
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    {τ : B →P[ℂ] ℂ} (hτ : τ.IsTracialState) (f : F) (hf : f 1 = 1) :
    (τ.comp (.ofClass f)).IsTracialState :=
  hτ.comp f ((opNorm_comp_ofClass_of_map_one τ f hf).trans hτ.norm_eq_one)

/-- **Unital pullback of tracial states.** Pulling a tracial state back along a unital star
homomorphism between unital C⋆-algebras yields a tracial state without any norm hypothesis. -/
theorem IsTracialState.comp_unital {B F : Type*}
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [FunLike F A B] [AlgHomClass F ℂ A B] [StarHomClass F A B]
    {τ : B →P[ℂ] ℂ} (hτ : τ.IsTracialState) (f : F) :
    (τ.comp (.ofClass f)).IsTracialState :=
  hτ.comp_of_map_one f (_root_.map_one f)

/-- Restricting a tracial state to a closed unital star subalgebra `S ⊆ A` yields a tracial state
of `S` without any norm hypothesis. -/
theorem IsTracialState.domRestrict (hτ : τ.IsTracialState) (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] :
    (τ.domRestrict S).IsTracialState := by
  simp [isTracialState_iff_map_one, hτ.map_one, hτ.mul_comm]

/-- **No tracial state in the presence of two orthogonal isometries.** If `s₁, s₂ : A` satisfy
`star s₁ * s₁ = 1`, `star s₂ * s₂ = 1`, and `s₁ * star s₁ + s₂ * star s₂ ≤ 1` (for instance on
`B(ℓ²)` or any properly infinite C⋆-algebra), then `A` admits no tracial state. -/
theorem IsTracialState.false_of_isometries (hτ : τ.IsTracialState) {s₁ s₂ : A}
    (hs₁ : star s₁ * s₁ = 1) (hs₂ : star s₂ * s₂ = 1)
    (hsum : s₁ * star s₁ + s₂ * star s₂ ≤ 1) : False := by
  have hle : τ (s₁ * star s₁ + s₂ * star s₂) ≤ τ 1 := τ.mono hsum
  rw [map_add, hτ.mul_comm s₁ (star s₁), hτ.mul_comm s₂ (star s₂), hs₁, hs₂, hτ.map_one] at hle
  have hre := (Complex.le_def.mp hle).1
  norm_num at hre

end Unital

end PositiveContinuousLinearMap

namespace TauCeti

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {φ : WeakDual ℂ A}

variable (A) in
/-- The **tracial state space** `T(A)` of a C⋆-algebra `A`, as a subset of the weak-* dual
`WeakDual ℂ A`: the weak-* images of tracial states `A →P[ℂ] ℂ`, equivalently the `0`-KMS states of
the trivial real action on `A`. -/
noncomputable def tracialStateSpace : Set (WeakDual ℂ A) :=
  (CStarAction.trivial : CStarAction (Multiplicative ℝ) A).kmsStates 0

/-- `tracialStateSpace A` is literally the `0`-KMS state space of the trivial action on `A`. -/
theorem tracialStateSpace_eq_kmsStates_trivial :
    tracialStateSpace A = (CStarAction.trivial : CStarAction (Multiplicative ℝ) A).kmsStates 0 :=
  (rfl)

/-- A positive continuous linear functional belongs to `tracialStateSpace A` if and only if it is a
tracial state. -/
@[simp]
theorem _root_.PositiveContinuousLinearMap.toWeakDual_mem_tracialStateSpace_iff (τ : A →P[ℂ] ℂ) :
    StrongDual.toWeakDual (τ : A →L[ℂ] ℂ) ∈ tracialStateSpace A ↔ τ.IsTracialState :=
  CStarAction.toWeakDual_mem_kmsStates_iff

/-- Elements of `tracialStateSpace A` are the weak-* dual images of tracial states `A →P[ℂ] ℂ`. -/
theorem mem_tracialStateSpace_iff_exists :
    φ ∈ tracialStateSpace A ↔
      ∃ τ : A →P[ℂ] ℂ, τ.IsTracialState ∧ StrongDual.toWeakDual (τ : A →L[ℂ] ℂ) = φ :=
  CStarAction.mem_kmsStates_iff

/-- Tracial states are states. -/
theorem tracialStateSpace_subset_stateSpace : tracialStateSpace A ⊆ stateSpace A :=
  CStarAction.kmsStates_subset_stateSpace

/-- Membership in `tracialStateSpace A` is equivalent to membership in `stateSpace A` together with
the trace identity `φ (a * b) = φ (b * a)`. -/
theorem mem_tracialStateSpace_iff :
    φ ∈ tracialStateSpace A ↔ φ ∈ stateSpace A ∧ ∀ a b : A, φ (a * b) = φ (b * a) := by
  rw [mem_tracialStateSpace_iff_exists]
  refine ⟨fun ⟨τ, hτ, hφ⟩ => ?_, fun ⟨hstate, htr⟩ => ?_⟩
  · subst hφ
    exact ⟨tracialStateSpace_subset_stateSpace (τ.toWeakDual_mem_tracialStateSpace_iff.mpr hτ),
      hτ.mul_comm⟩
  · obtain ⟨ω, hω, rfl⟩ := mem_stateSpace_iff_exists_positiveLinearMap.mp hstate
    exact ⟨.ofClass ω, PositiveContinuousLinearMap.isTracialState_iff.mpr ⟨hω, htr⟩, rfl⟩

/-- Every functional in `tracialStateSpace A` satisfies `φ (a * b) = φ (b * a)`. -/
theorem mul_comm_of_mem_tracialStateSpace (hφ : φ ∈ tracialStateSpace A) (a b : A) :
    φ (a * b) = φ (b * a) :=
  (mem_tracialStateSpace_iff.mp hφ).2 a b

/-- **Polarization description of `tracialStateSpace A`.** A functional belongs to
`tracialStateSpace A` if and only if it is a state satisfying `φ (star a * a) = φ (a * star a)` for
all `a : A`. -/
theorem mem_tracialStateSpace_iff_star_mul_self :
    φ ∈ tracialStateSpace A ↔ φ ∈ stateSpace A ∧ ∀ a : A, φ (star a * a) = φ (a * star a) := by
  rw [mem_tracialStateSpace_iff, forall_map_mul_comm_iff_star_mul_self]

/-- **Convexity of `tracialStateSpace A`.** Real convex combinations of tracial states are tracial
states, with no unit needed. -/
theorem convex_tracialStateSpace : Convex ℝ (tracialStateSpace A) :=
  CStarAction.convex_kmsStates

/-- A weak-* limit point of tracial states that still has norm one is a tracial state. -/
theorem closure_tracialStateSpace_inter_norm_subset :
    closure (tracialStateSpace A) ∩ {φ | ‖toStrongDual φ‖ = 1} ⊆ tracialStateSpace A :=
  CStarAction.closure_kmsStates_inter_subset

/-- **Relative weak-* closedness.** `tracialStateSpace A` is weak-* closed in `stateSpace A`. -/
@[simp]
theorem closure_tracialStateSpace_inter_stateSpace :
    closure (tracialStateSpace A) ∩ stateSpace A = tracialStateSpace A := by
  refine Subset.antisymm (fun φ ⟨hclos, hstate⟩ => ?_)
    (subset_inter subset_closure tracialStateSpace_subset_stateSpace)
  exact closure_tracialStateSpace_inter_norm_subset
    ⟨hclos, norm_toStrongDual_of_mem_stateSpace hstate⟩

/-- In the norm topology of the continuous dual, `tracialStateSpace A` is closed. -/
theorem isClosed_preimage_toWeakDual_tracialStateSpace :
    IsClosed (StrongDual.toWeakDual ⁻¹' tracialStateSpace A) := by
  have h : StrongDual.toWeakDual ⁻¹' tracialStateSpace A =
      (StrongDual.toWeakDual ⁻¹' stateSpace A) ∩
        ⋂ (a : A) (b : A), {ψ : StrongDual ℂ A | ψ (a * b) = ψ (b * a)} := by
    ext ψ
    simp [mem_tracialStateSpace_iff]
  rw [h]
  refine isClosed_preimage_toWeakDual_stateSpace.inter <|
    isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq ((ContinuousLinearMap.apply ℂ ℂ (a * b)).continuous)
        ((ContinuousLinearMap.apply ℂ ℂ (b * a)).continuous)

/-- On a subsingleton (zero) C⋆-algebra, the tracial state space is empty. -/
@[simp]
theorem tracialStateSpace_eq_empty [Subsingleton A] : tracialStateSpace A = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro φ hφ
  obtain ⟨τ, hτ, -⟩ := mem_tracialStateSpace_iff_exists.mp hφ
  exact not_nontrivial A hτ.nontrivial

/-- On a commutative C⋆-algebra, every state is tracial: `tracialStateSpace B = stateSpace B`. -/
@[simp]
theorem tracialStateSpace_eq_stateSpace {B : Type*} [NonUnitalCommCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] : tracialStateSpace B = stateSpace B := by
  ext φ
  simp [mem_tracialStateSpace_iff, mul_comm]

/-- **Pullback of `tracialStateSpace` along a surjective star homomorphism.** -/
theorem mapsTo_pullbackFunctional_tracialStateSpace_of_surjective {B F : Type*}
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    (f : F) (hf : Function.Surjective f) :
    MapsTo (pullbackFunctional A f) (tracialStateSpace B) (tracialStateSpace A) := by
  intro φ hφ
  rw [mem_tracialStateSpace_iff] at hφ ⊢
  refine ⟨mapsTo_pullbackFunctional_stateSpace_of_surjective f hf hφ.1, fun a b => ?_⟩
  simp only [pullbackFunctional_apply, map_mul]
  exact hφ.2 (f a) (f b)

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {φ : WeakDual ℂ A}

/-- On a unital C⋆-algebra, membership in `tracialStateSpace A` unfolds to positivity, `φ 1 = 1`,
and the trace identity. -/
theorem mem_tracialStateSpace_iff_map_one :
    φ ∈ tracialStateSpace A ↔
      (∀ a, 0 ≤ a → 0 ≤ φ a) ∧ φ 1 = 1 ∧ ∀ a b : A, φ (a * b) = φ (b * a) := by
  rw [mem_tracialStateSpace_iff, mem_stateSpace_iff_map_one, and_assoc]

/-- **Unitary invariance description of `tracialStateSpace A`.** On a unital C⋆-algebra, a
functional belongs to `tracialStateSpace A` if and only if it is a state invariant under unitary
conjugation. -/
theorem mem_tracialStateSpace_iff_unitary_conj :
    φ ∈ tracialStateSpace A ↔
      φ ∈ stateSpace A ∧ ∀ (u : unitary A) (a : A), φ ((u : A) * a * star (u : A)) = φ a := by
  rw [mem_tracialStateSpace_iff, CStarAlgebra.forall_map_mul_comm_iff_unitary_conj]

/-- For unital `A`, `tracialStateSpace A` is weak-* closed. -/
theorem isClosed_tracialStateSpace : IsClosed (tracialStateSpace A) :=
  CStarAction.isClosed_kmsStates

/-- **Weak-* compactness of `tracialStateSpace A`.** For unital `A`, the tracial state space is
weak-* compact. -/
theorem isCompact_tracialStateSpace : IsCompact (tracialStateSpace A) :=
  CStarAction.isCompact_kmsStates

/-- **Krein–Milman for tracial states.** For unital `A`, `tracialStateSpace A` is the weak-* closed
convex hull of its extreme points (including when `tracialStateSpace A` is empty). -/
theorem closure_convexHull_extremePoints_tracialStateSpace :
    closure (convexHull ℝ (extremePoints ℝ (tracialStateSpace A))) = tracialStateSpace A :=
  closure_convexHull_extremePoints isCompact_tracialStateSpace convex_tracialStateSpace

/-- Every nonempty weak-* compact tracial state space of a unital C⋆-algebra has an extreme
tracial state. -/
theorem extremePoints_tracialStateSpace_nonempty (h : (tracialStateSpace A).Nonempty) :
    (extremePoints ℝ (tracialStateSpace A)).Nonempty :=
  isCompact_tracialStateSpace.extremePoints_nonempty h

/-- The only tracial state of `ℂ` is the identity functional. -/
theorem tracialStateSpace_complex :
    tracialStateSpace ℂ = {StrongDual.toWeakDual (ContinuousLinearMap.id ℂ ℂ)} := by
  rw [tracialStateSpace_eq_stateSpace, stateSpace_complex]

/-- If a unital C⋆-algebra contains two isometries with orthogonal ranges (`s₁ s₁⋆ + s₂ s₂⋆ ≤ 1`),
its tracial state space is empty. -/
theorem tracialStateSpace_eq_empty_of_isometries {s₁ s₂ : A}
    (hs₁ : star s₁ * s₁ = 1) (hs₂ : star s₂ * s₂ = 1)
    (hsum : s₁ * star s₁ + s₂ * star s₂ ≤ 1) :
    tracialStateSpace A = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro φ hφ
  obtain ⟨τ, hτ, -⟩ := mem_tracialStateSpace_iff_exists.mp hφ
  exact hτ.false_of_isometries hs₁ hs₂ hsum

/-- **Pullback of `tracialStateSpace` along a unital star homomorphism.** Composing a tracial state
of `B` with a unital star homomorphism `A → B` gives a tracial state of `A`. -/
theorem mapsTo_pullbackFunctional_tracialStateSpace {B F : Type*}
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [FunLike F A B] [AlgHomClass F ℂ A B] [StarHomClass F A B] (f : F) :
    MapsTo (pullbackFunctional A f) (tracialStateSpace B) (tracialStateSpace A) := by
  intro φ hφ
  rw [mem_tracialStateSpace_iff] at hφ ⊢
  refine ⟨mapsTo_pullbackFunctional_stateSpace f hφ.1, fun a b => ?_⟩
  simp only [pullbackFunctional_apply, map_mul]
  exact hφ.2 (f a) (f b)

end Unital

end TauCeti
