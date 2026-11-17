/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import TauCeti.Analysis.CStarAlgebra.Action.KMS.StateSpace
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import TauCeti.Analysis.CStarAlgebra.PositiveLinearFunctional

/-!
# Tracial states and the tracial state space of a C⋆-algebra

A *tracial state* of a possibly nonunital complex C⋆-algebra `A` is a state `τ : A →P[ℂ] ℂ`
satisfying `τ (a * b) = τ (b * a)` for all `a, b : A`. Because the `0`-KMS states of a C⋆-dynamical
system are precisely the tracial states (`TauCeti.CStarAction.isKMSState_zero_iff`), we define
`PositiveContinuousLinearMap.IsTracialState τ` as the `0`-KMS condition for the trivial action
`TauCeti.CStarAction.trivial`, and `TauCeti.tracialStateSpace A` as the corresponding set of
`0`-KMS states in the weak-* dual `WeakDual ℂ A`.

## Main results

* `LinearMap.forall_mul_comm_iff_forall_star_mul_self`: by complex polarization, a `ℂ`-linear map
  `f` on a nonunital complex star algebra satisfies `f (a * b) = f (b * a)` for all `a, b` if and
  only if `f (star a * a) = f (a * star a)` for all `a`.
* `LinearMap.forall_mul_comm_iff_forall_unitary_conj`: on a unital C⋆-algebra, a `ℂ`-linear map
  `f` satisfies `f (a * b) = f (b * a)` for all `a, b` if and only if `f (u * a * star u) = f a`
  for all unitaries `u` and all `a`, since the unitaries span the algebra
  (`CStarAlgebra.span_unitary`).
* `PositiveContinuousLinearMap.isTracialState_iff`,
  `PositiveContinuousLinearMap.isTracialState_iff_apply_star_mul_self`, and
  `PositiveContinuousLinearMap.isTracialState_iff_apply_unitary_conj`: characterizations of tracial
  states by commutativity, by polarization, and (for unital algebras) by unitary invariance.
* Pullback and restriction of tracial states:
  `PositiveContinuousLinearMap.IsTracialState.comp`,
  `PositiveContinuousLinearMap.IsTracialState.comp_of_surjective`,
  `PositiveContinuousLinearMap.IsTracialState.comp_unital`,
  `PositiveContinuousLinearMap.IsTracialState.restrict`, and
  `PositiveContinuousLinearMap.IsTracialState.restrict_starSubalgebra`.
* `TauCeti.tracialStateSpace`: the tracial state space in `WeakDual ℂ A`, with convexity
  (`TauCeti.convex_tracialStateSpace`), norm-one weak-* closure
  (`TauCeti.closure_tracialStateSpace_inter_subset`), weak-* closedness and compactness for unital
  algebras (`TauCeti.isClosed_tracialStateSpace`, `TauCeti.isCompact_tracialStateSpace`), and
  identification on commutative algebras (`TauCeti.tracialStateSpace_eq_stateSpace`) and on `ℂ`
  (`TauCeti.tracialStateSpace_complex`).

## References

* N. P. Brown, *Invariant Means and Finite Representation Theory of C*-Algebras*, Mem. Amer. Math.
  Soc. 184 (2006), Chapter 2.
* G. K. Pedersen, *C*-Algebras and their Automorphism Groups*, second edition (2018), Chapter 3.
* A. Tikuisis, S. White, and W. Winter, *Quasidiagonality of nuclear C*-algebras*, Ann. of Math.
  185 (2017), Section 1.
-/

public section

open Complex Filter Set Topology
open scoped CStarAlgebra ComplexOrder

namespace LinearMap

/-- **Polarization criterion for tracial linear maps.** A `ℂ`-linear map on a nonunital complex
star algebra satisfies `f (a * b) = f (b * a)` for all `a, b` if and only if
`f (star a * a) = f (a * star a)` for all `a`. -/
theorem forall_mul_comm_iff_forall_star_mul_self {A M : Type*} [NonUnitalNonAssocSemiring A]
    [StarRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]
    [AddCommMonoid M] [Module ℂ M] (f : A →ₗ[ℂ] M) :
    (∀ a b : A, f (a * b) = f (b * a)) ↔ ∀ a : A, f (star a * a) = f (a * star a) := by
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup ℂ
  refine ⟨fun h a => h (star a) a, fun h a b => ?_⟩
  let d (x y : A) : M := f (star x * y) - f (y * star x)
  have hpol (x y : A) : d x y = 0 := by
    have h₁ : d x y + d y x = 0 := by
      have hxy := h (x + y)
      simp only [star_add, add_mul, mul_add, map_add, h x, h y] at hxy
      have hsub := sub_eq_zero.mpr hxy
      simpa only [d] using (by abel_nf at hsub ⊢; exact hsub)
    have h₂ : I • d x y - I • d y x = 0 := by
      have hxy := h (x + I • y)
      simp only [star_add, star_smul, Complex.star_def, conj_I, add_mul, mul_add,
        smul_mul_assoc, mul_smul_comm, map_add, map_smul, neg_smul,
        smul_add, smul_smul, neg_mul, mul_neg, I_mul_I, neg_neg, one_smul, h x, h y] at hxy
      have hsub := sub_eq_zero.mpr hxy
      simp only [d, smul_sub]
      abel_nf at hsub ⊢
      exact hsub
    have h₃ : d x y - d y x = 0 := by
      have := congrArg ((-I) • ·) h₂
      simp only [smul_sub, smul_smul, neg_mul, I_mul_I, neg_neg, one_smul, smul_zero] at this
      exact this
    have h₄ : (2 : ℂ) • d x y = 0 := by
      have hadd : (d x y + d y x) + (d x y - d y x) = 0 := by rw [h₁, h₃, add_zero]
      rw [two_smul]
      abel_nf at hadd ⊢
      exact hadd
    have := congrArg ((2 : ℂ)⁻¹ • ·) h₄
    simpa [smul_smul] using this
  have hab := hpol (star a) b
  simp only [d, star_star, sub_eq_zero] at hab
  exact hab

/-- **Unitary invariance criterion for tracial linear maps.** A `ℂ`-linear map on a unital
C⋆-algebra satisfies `f (a * b) = f (b * a)` for all `a, b` if and only if
`f (u * a * star u) = f a` for every unitary `u` and every `a`. -/
theorem forall_mul_comm_iff_forall_unitary_conj {A M : Type*} [CStarAlgebra A]
    [AddCommMonoid M] [Module ℂ M] (f : A →ₗ[ℂ] M) :
    (∀ a b : A, f (a * b) = f (b * a)) ↔
      ∀ (u : unitary A) (a : A), f ((u : A) * a * star (u : A)) = f a := by
  refine ⟨fun h u a => ?_, fun h a b => ?_⟩
  · rw [h, ← mul_assoc, Unitary.coe_star_mul_self, one_mul]
  · have hlin : f.comp (LinearMap.mul ℂ A a) = f.comp ((LinearMap.mul ℂ A).flip a) := by
      refine LinearMap.ext_on (CStarAlgebra.span_unitary A) fun u hu => ?_
      simp only [LinearMap.comp_apply, LinearMap.mul_apply', LinearMap.flip_apply]
      have hconj := h ⟨u, hu⟩ (a * u)
      have huu : u * (a * u) * star u = u * a := by
        rw [← mul_assoc u a u, mul_assoc (u * a) u (star u), (Unitary.mem_iff.mp hu).2, mul_one]
      simpa only [huu] using hconj.symm
    exact LinearMap.congr_fun hlin b

end LinearMap

namespace PositiveContinuousLinearMap

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {τ : A →P[ℂ] ℂ}

/-- A *tracial state* of a possibly nonunital C⋆-algebra `A` is a state (a positive continuous
linear functional of norm one) satisfying `τ (a * b) = τ (b * a)` for all `a, b : A`, realized as
a `0`-KMS state of the trivial action `TauCeti.CStarAction.trivial`. -/
def IsTracialState (τ : A →P[ℂ] ℂ) : Prop :=
  (TauCeti.CStarAction.trivial : TauCeti.CStarAction (Multiplicative ℝ) A).IsKMSState 0 τ

/-- A positive continuous linear functional is a tracial state if and only if it has norm one and
satisfies `τ (a * b) = τ (b * a)` for all `a, b`. -/
theorem isTracialState_iff :
    τ.IsTracialState ↔ ‖(τ : A →L[ℂ] ℂ)‖ = 1 ∧ ∀ a b : A, τ (a * b) = τ (b * a) :=
  TauCeti.CStarAction.isKMSState_zero_iff

/-- A tracial state has operator norm one. -/
theorem IsTracialState.norm_eq_one (hτ : τ.IsTracialState) : ‖(τ : A →L[ℂ] ℂ)‖ = 1 :=
  (isTracialState_iff.mp hτ).1

/-- A tracial state satisfies `τ (a * b) = τ (b * a)`. -/
theorem IsTracialState.apply_mul_comm (hτ : τ.IsTracialState) (a b : A) :
    τ (a * b) = τ (b * a) :=
  (isTracialState_iff.mp hτ).2 a b

/-- A tracial state satisfies `τ (star a * a) = τ (a * star a)`. -/
theorem IsTracialState.apply_star_mul_self (hτ : τ.IsTracialState) (a : A) :
    τ (star a * a) = τ (a * star a) :=
  hτ.apply_mul_comm (star a) a

/-- A tracial state is nonzero. -/
theorem IsTracialState.ne_zero (hτ : τ.IsTracialState) : τ ≠ 0 := by
  intro h0
  have h1 := hτ.norm_eq_one
  simp [h0] at h1

/-- **Polarization criterion for tracial states.** A positive functional is a tracial state if and
only if it has norm one and satisfies `τ (star a * a) = τ (a * star a)` for all `a`. -/
theorem isTracialState_iff_apply_star_mul_self :
    τ.IsTracialState ↔ ‖(τ : A →L[ℂ] ℂ)‖ = 1 ∧ ∀ a : A, τ (star a * a) = τ (a * star a) := by
  rw [isTracialState_iff]
  exact and_congr_right fun _ =>
    τ.toPositiveLinearMap.toLinearMap.forall_mul_comm_iff_forall_star_mul_self

/-- On a commutative C⋆-algebra, a positive functional is a tracial state if and only if it has
norm one. -/
theorem isTracialState_iff_of_comm {B : Type*} [NonUnitalCommCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] {ψ : B →P[ℂ] ℂ} :
    ψ.IsTracialState ↔ ‖(ψ : B →L[ℂ] ℂ)‖ = 1 :=
  TauCeti.CStarAction.isKMSState_zero_iff_of_comm

/-- The zero C⋆-algebra admits no tracial state. -/
theorem not_isTracialState_of_subsingleton [Subsingleton A] (τ : A →P[ℂ] ℂ) :
    ¬ τ.IsTracialState := by
  intro hτ
  exact hτ.ne_zero (DFunLike.ext _ _ fun a => by simp [Subsingleton.elim a 0])

/-- **Pointwise limits of tracial states.** If tracial states converge pointwise to a positive
functional of norm one, then the limit is a tracial state. -/
theorem IsTracialState.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {τ' : ι → A →P[ℂ] ℂ}
    (hτ' : ∀ᶠ i in l, (τ' i).IsTracialState) (hlim : ∀ a, Tendsto (fun i => τ' i a) l (𝓝 (τ a)))
    (hnorm : ‖(τ : A →L[ℂ] ℂ)‖ = 1) : τ.IsTracialState :=
  TauCeti.CStarAction.IsKMSState.of_tendsto hτ' hlim hnorm

section Pullback

variable {B F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B]

/-- **Pullback of tracial states.** Pulling a tracial state back along a multiplicative continuous
positive linear map gives a tracial state whenever the pullback has norm one. -/
theorem IsTracialState.comp [ContinuousLinearMapClass F ℂ A B] [OrderHomClass F A B]
    [MulHomClass F A B] {ψ : B →P[ℂ] ℂ} (hψ : ψ.IsTracialState) (f : F)
    (hnorm : ‖((ψ.comp (.ofClass f) : A →P[ℂ] ℂ) : A →L[ℂ] ℂ)‖ = 1) :
    (ψ.comp (.ofClass f)).IsTracialState := by
  refine isTracialState_iff.mpr ⟨hnorm, fun a b => ?_⟩
  simp [hψ.apply_mul_comm]

variable [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- **Pullback of tracial states along surjective homomorphisms.** Pulling a tracial state back
along a surjective star homomorphism automatically preserves the norm and yields a tracial state. -/
theorem IsTracialState.comp_of_surjective {ψ : B →P[ℂ] ℂ} (hψ : ψ.IsTracialState) (f : F)
    (hf : Function.Surjective f) : (ψ.comp (.ofClass f)).IsTracialState :=
  hψ.comp f <| (opNorm_comp_ofClass_of_surjective ψ f hf).trans hψ.norm_eq_one

/-- Along a surjective star homomorphism `f`, a positive functional `ψ` is a tracial state if and
only if its pullback `ψ ∘ f` is a tracial state. -/
theorem isTracialState_comp_iff_of_surjective {ψ : B →P[ℂ] ℂ} (f : F)
    (hf : Function.Surjective f) :
    (ψ.comp (.ofClass f)).IsTracialState ↔ ψ.IsTracialState := by
  refine ⟨fun h => isTracialState_iff.mpr ⟨?_, fun x y => ?_⟩, fun h => h.comp_of_surjective f hf⟩
  · rw [← opNorm_comp_ofClass_of_surjective ψ f hf]
    exact h.norm_eq_one
  · obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    simpa [map_mul] using h.apply_mul_comm a b

/-- **Restriction to a closed star subalgebra.** The restriction of a tracial state to a closed
nonunital star subalgebra is a tracial state whenever it retains norm one. -/
theorem IsTracialState.restrict (hτ : τ.IsTracialState) (S : NonUnitalStarSubalgebra ℂ A)
    [IsClosed (S : Set A)]
    (hnorm : ‖((τ.comp (.ofClass (NonUnitalStarSubalgebraClass.subtype S)) : S →P[ℂ] ℂ) :
      S →L[ℂ] ℂ)‖ = 1) :
    (τ.comp (.ofClass (NonUnitalStarSubalgebraClass.subtype S))).IsTracialState :=
  hτ.comp (NonUnitalStarSubalgebraClass.subtype S) hnorm

end Pullback

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {τ : A →P[ℂ] ℂ}

/-- On a unital C⋆-algebra, a positive functional is a tracial state if and only if `τ 1 = 1` and
`τ (a * b) = τ (b * a)` for all `a, b`. -/
theorem isTracialState_iff_map_one :
    τ.IsTracialState ↔ τ 1 = 1 ∧ ∀ a b : A, τ (a * b) = τ (b * a) := by
  rw [isTracialState_iff, ← Complex.ofReal_eq_one, τ.ofReal_opNorm_eq_map_one]

/-- A tracial state on a unital C⋆-algebra takes the value `1` at `1`. -/
theorem IsTracialState.map_one (hτ : τ.IsTracialState) : τ 1 = 1 :=
  (isTracialState_iff_map_one.mp hτ).1

/-- **Unitary invariance criterion for tracial states.** On a unital C⋆-algebra, a positive
functional is a tracial state if and only if `τ 1 = 1` and `τ (u * a * star u) = τ a` for every
unitary `u` and every `a`. -/
theorem isTracialState_iff_apply_unitary_conj :
    τ.IsTracialState ↔
      τ 1 = 1 ∧ ∀ (u : unitary A) (a : A), τ ((u : A) * a * star (u : A)) = τ a := by
  rw [isTracialState_iff_map_one]
  exact and_congr_right fun _ =>
    τ.toPositiveLinearMap.toLinearMap.forall_mul_comm_iff_forall_unitary_conj

/-- A tracial state on a unital C⋆-algebra is invariant under unitary conjugation. -/
theorem IsTracialState.apply_unitary_conj (hτ : τ.IsTracialState) (u : unitary A) (a : A) :
    τ ((u : A) * a * star (u : A)) = τ a :=
  (isTracialState_iff_apply_unitary_conj.mp hτ).2 u a

/-- **Pullback of tracial states along a unital multiplicative positive map.** Precomposing a
tracial state of a unital C⋆-algebra with a unital multiplicative continuous positive linear map
yields a tracial state, with no norm hypothesis. -/
theorem IsTracialState.comp_unital {B F : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [FunLike F A B] [ContinuousLinearMapClass F ℂ A B] [OrderHomClass F A B]
    [MonoidHomClass F A B] {ψ : B →P[ℂ] ℂ} (hψ : ψ.IsTracialState) (f : F) :
    (ψ.comp (.ofClass f)).IsTracialState := by
  refine isTracialState_iff_map_one.mpr ⟨?_, fun a b => ?_⟩
  · simp [hψ.map_one]
  · simp [hψ.apply_mul_comm]

/-- **Restriction to a closed unital star subalgebra.** The restriction of a tracial state on a
unital C⋆-algebra to a closed unital star subalgebra is a tracial state. -/
theorem IsTracialState.restrict_starSubalgebra (hτ : τ.IsTracialState) (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] :
    (τ.comp (.ofClass S.subtype)).IsTracialState :=
  hτ.comp_unital S.subtype

/-- The identity functional on `ℂ` is a tracial state. -/
theorem isTracialState_id_complex : (PositiveContinuousLinearMap.id ℂ ℂ).IsTracialState :=
  isTracialState_iff_map_one.mpr ⟨by simp, fun a b => mul_comm a b⟩

end Unital

end PositiveContinuousLinearMap

namespace TauCeti

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {φ : WeakDual ℂ A}

variable (A) in
/-- The **tracial state space** `T(A)` of a possibly nonunital C⋆-algebra `A`, as a subset of the
weak-* dual `WeakDual ℂ A`: the set of `0`-KMS states of the trivial action. -/
noncomputable def tracialStateSpace : Set (WeakDual ℂ A) :=
  (CStarAction.trivial : CStarAction (Multiplicative ℝ) A).kmsStates 0

/-- A positive continuous linear functional lies in the tracial state space if and only if it is
a tracial state. -/
@[simp]
theorem _root_.PositiveContinuousLinearMap.toWeakDual_mem_tracialStateSpace_iff (τ : A →P[ℂ] ℂ) :
    StrongDual.toWeakDual (τ : A →L[ℂ] ℂ) ∈ tracialStateSpace A ↔ τ.IsTracialState :=
  CStarAction.toWeakDual_mem_kmsStates_iff

/-- Membership in the tracial state space unfolds to being a state and satisfying
`φ (a * b) = φ (b * a)` for all `a, b`. -/
theorem mem_tracialStateSpace_iff :
    φ ∈ tracialStateSpace A ↔ φ ∈ stateSpace A ∧ ∀ a b : A, φ (a * b) = φ (b * a) := by
  rw [tracialStateSpace, CStarAction.mem_kmsStates_iff]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨τ.toWeakDual_mem_stateSpace_iff.mpr hτ.norm_eq_one,
      (PositiveContinuousLinearMap.isTracialState_iff.mp hτ).2⟩
  · rintro ⟨hφ, htr⟩
    let τ : A →P[ℂ] ℂ := .mk₀ (WeakDual.toStrongDual φ) fun _ => map_nonneg_of_mem_stateSpace hφ
    have hτ_clm : (τ : A →L[ℂ] ℂ) = WeakDual.toStrongDual φ :=
      PositiveContinuousLinearMap.toContinuousLinearMap_mk₀ _ _
    refine ⟨τ, PositiveContinuousLinearMap.isTracialState_iff.mpr
      ⟨hτ_clm ▸ norm_toStrongDual_of_mem_stateSpace hφ, htr⟩, ?_⟩
    rw [hτ_clm, WeakDual.toWeakDual_toStrongDual]

/-- **Polarization criterion on the tracial state space.** A functional lies in `T(A)` if and only
if it is a state satisfying `φ (star a * a) = φ (a * star a)` for all `a`. -/
theorem mem_tracialStateSpace_iff_apply_star_mul_self :
    φ ∈ tracialStateSpace A ↔ φ ∈ stateSpace A ∧ ∀ a : A, φ (star a * a) = φ (a * star a) := by
  rw [mem_tracialStateSpace_iff]
  exact and_congr_right fun _ =>
    (WeakDual.toStrongDual φ : A →ₗ[ℂ] ℂ).forall_mul_comm_iff_forall_star_mul_self

/-- Every tracial state is a state. -/
theorem tracialStateSpace_subset_stateSpace : tracialStateSpace A ⊆ stateSpace A :=
  CStarAction.kmsStates_subset_stateSpace

/-- On a commutative C⋆-algebra, every state is tracial. -/
theorem tracialStateSpace_eq_stateSpace {B : Type*} [NonUnitalCommCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] : tracialStateSpace B = stateSpace B := by
  ext φ
  simp [mem_tracialStateSpace_iff, mul_comm]

/-- **Convexity of the tracial state space.** Real convex combinations of tracial states are
tracial states. -/
theorem convex_tracialStateSpace : Convex ℝ (tracialStateSpace A) :=
  CStarAction.convex_kmsStates

/-- **Weak-* limits of tracial states.** A weak-* limit point of tracial states that has norm one
is a tracial state. -/
theorem closure_tracialStateSpace_inter_subset :
    closure (tracialStateSpace A) ∩ {φ | ‖WeakDual.toStrongDual φ‖ = 1} ⊆ tracialStateSpace A :=
  CStarAction.closure_kmsStates_inter_subset

/-- The zero C⋆-algebra has empty tracial state space. -/
theorem tracialStateSpace_eq_empty_of_subsingleton [Subsingleton A] :
    tracialStateSpace A = ∅ := by
  ext φ
  rw [tracialStateSpace, CStarAction.mem_kmsStates_iff]
  simp only [mem_empty_iff_false, iff_false]
  rintro ⟨τ, hτ, -⟩
  exact PositiveContinuousLinearMap.not_isTracialState_of_subsingleton τ hτ

/-- **Pullback of tracial states along a surjective star homomorphism.** -/
theorem mapsTo_pullbackFunctional_tracialStateSpace_of_surjective {B F : Type*}
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    (f : F) (hf : Function.Surjective f) :
    MapsTo (pullbackFunctional A f) (tracialStateSpace B) (tracialStateSpace A) := by
  intro φ hφ
  obtain ⟨hstate, htr⟩ := mem_tracialStateSpace_iff.mp hφ
  refine mem_tracialStateSpace_iff.mpr
    ⟨mapsTo_pullbackFunctional_stateSpace_of_surjective f hf hstate, fun a b => ?_⟩
  simp [map_mul, htr]

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {φ : WeakDual ℂ A}

/-- **Unitary invariance criterion on the tracial state space.** On a unital C⋆-algebra, a
functional lies in `T(A)` if and only if it is a state invariant under unitary conjugation. -/
theorem mem_tracialStateSpace_iff_apply_unitary_conj :
    φ ∈ tracialStateSpace A ↔
      φ ∈ stateSpace A ∧ ∀ (u : unitary A) (a : A), φ ((u : A) * a * star (u : A)) = φ a := by
  rw [mem_tracialStateSpace_iff]
  exact and_congr_right fun _ =>
    (WeakDual.toStrongDual φ : A →ₗ[ℂ] ℂ).forall_mul_comm_iff_forall_unitary_conj

/-- For unital `A`, the tracial state space is weak-* closed. -/
theorem isClosed_tracialStateSpace : IsClosed (tracialStateSpace A) :=
  CStarAction.isClosed_kmsStates

/-- **Weak-* compactness of the tracial state space.** For unital `A`, the tracial state space is
weak-* compact. -/
theorem isCompact_tracialStateSpace : IsCompact (tracialStateSpace A) :=
  CStarAction.isCompact_kmsStates

/-- **Pullback of tracial states along a unital star homomorphism.** -/
theorem mapsTo_pullbackFunctional_tracialStateSpace {B F : Type*} [CStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B]
    [FunLike F A B] [AlgHomClass F ℂ A B] [StarHomClass F A B] (f : F) :
    MapsTo (pullbackFunctional A f) (tracialStateSpace B) (tracialStateSpace A) := by
  intro φ hφ
  obtain ⟨hstate, htr⟩ := mem_tracialStateSpace_iff.mp hφ
  refine mem_tracialStateSpace_iff.mpr
    ⟨mapsTo_pullbackFunctional_stateSpace f hstate, fun a b => ?_⟩
  simp [map_mul, htr]

/-- The only tracial state of `ℂ` is the identity functional. -/
theorem tracialStateSpace_complex :
    tracialStateSpace ℂ = {StrongDual.toWeakDual (ContinuousLinearMap.id ℂ ℂ)} := by
  rw [tracialStateSpace_eq_stateSpace, stateSpace_complex]

end Unital

end TauCeti
