/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.LocallyConvex.WeakDual
public import Mathlib.Analysis.Normed.Module.WeakDual
public import TauCeti.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# The state space of a C⋆-algebra

A *state* of a possibly nonunital C⋆-algebra `A` is a positive linear functional of norm one.
This file defines the state space `TauCeti.stateSpace A` as a subset of the weak-* dual
`WeakDual ℂ A`, so that convexity, closedness and compactness refer to the weak-* topology.

* `TauCeti.mem_stateSpace_iff_exists_positiveLinearMap`: the states are exactly the positive
  linear maps `A →ₚ[ℂ] ℂ` of norm one, through the automatic continuity of positive maps.
* `TauCeti.convex_stateSpace`: the state space is convex. No unit is needed, because the norm of
  a positive functional is its limit along an approximate unit.
* `TauCeti.pullbackFunctional`: precomposition with a star homomorphism, as a complex-linear map
  of weak-* duals. By `TauCeti.mapsTo_pullbackFunctional_stateSpace_of_surjective` and
  `TauCeti.mapsTo_pullbackFunctional_stateSpace` it restricts to an affine map of state spaces
  along surjective star homomorphisms and along unital star homomorphisms.

For unital `A`:

* `TauCeti.mem_stateSpace_iff_map_one`: a positive functional is a state exactly when `φ 1 = 1`,
  and `TauCeti.mem_stateSpace_iff_norm_eq_one_and_map_one`: a functional is a state exactly when
  `‖φ‖ = φ 1 = 1`, with positivity then automatic.
* `TauCeti.isCompact_stateSpace`: the state space is weak-* compact, by Banach–Alaoglu.
* `TauCeti.stateSpace_nonempty`: if `A` is nonzero it has a state, by Hahn–Banach. The state
  space of `ℂ` is the single functional `z ↦ z`, `TauCeti.stateSpace_complex`.
* `TauCeti.closure_convexHull_extremePoints_stateSpace`: the state space is the weak-* closed
  convex hull of its extreme points, the pure states, by the Krein–Milman theorem; in particular
  a nonzero unital C⋆-algebra has a pure state, `TauCeti.extremePoints_stateSpace_nonempty`.

Without a unit the state space is still closed in the norm topology of the dual,
`TauCeti.isClosed_preimage_toWeakDual_stateSpace`, but in general it is not weak-* closed: on
`c₀` the point evaluations are states that converge weak-* to `0`.

## References

Jesse Peterson, *Notes on operator algebras*, Section 4.1.
-/

public section

open Set Filter WeakDual
open scoped ComplexOrder Topology

namespace TauCeti

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] {φ : WeakDual ℂ A}

variable (A) in
/-- The **state space** of a C⋆-algebra `A`: the functionals in the weak-* dual of `A` that are
nonnegative on nonnegative elements and have norm one. The results about it take the order on `A`
to be the C⋆-algebra order, through `StarOrderedRing A`. -/
def stateSpace : Set (WeakDual ℂ A) :=
  {φ | (∀ a, 0 ≤ a → 0 ≤ φ a) ∧ ‖toStrongDual φ‖ = 1}

/-- Membership in the state space unfolds to positivity and norm one. -/
theorem mem_stateSpace_iff :
    φ ∈ stateSpace A ↔ (∀ a, 0 ≤ a → 0 ≤ φ a) ∧ ‖toStrongDual φ‖ = 1 :=
  Iff.rfl

/-- A state is nonnegative on nonnegative elements. -/
theorem map_nonneg_of_mem_stateSpace (hφ : φ ∈ stateSpace A) {a : A} (ha : 0 ≤ a) : 0 ≤ φ a :=
  (mem_stateSpace_iff.1 hφ).1 a ha

/-- A state has norm one. -/
theorem norm_toStrongDual_of_mem_stateSpace (hφ : φ ∈ stateSpace A) : ‖toStrongDual φ‖ = 1 :=
  (mem_stateSpace_iff.1 hφ).2

/-- A state is contractive. -/
theorem norm_apply_le_of_mem_stateSpace (hφ : φ ∈ stateSpace A) (a : A) : ‖φ a‖ ≤ ‖a‖ := by
  simpa [norm_toStrongDual_of_mem_stateSpace hφ] using (toStrongDual φ).le_opNorm a

/-- In the norm topology of the continuous dual, the state space is closed. -/
theorem isClosed_preimage_toWeakDual_stateSpace :
    IsClosed (StrongDual.toWeakDual ⁻¹' stateSpace A) := by
  exact (isClosed_setOf_map_nonneg.preimage NormedSpace.Dual.toWeakDual_continuous).inter
    (isClosed_eq continuous_norm continuous_const)

variable [StarOrderedRing A]

/-- A positive linear functional, continuous by `PositiveLinearMap.exists_norm_apply_le`, is a
state exactly when its norm is one. -/
@[simp]
theorem _root_.PositiveLinearMap.toWeakDual_mem_stateSpace_iff (ω : A →ₚ[ℂ] ℂ) :
    StrongDual.toWeakDual (PositiveContinuousLinearMap.ofClass ω : A →L[ℂ] ℂ) ∈ stateSpace A ↔
      ‖(PositiveContinuousLinearMap.ofClass ω : A →L[ℂ] ℂ)‖ = 1 := by
  simp only [mem_stateSpace_iff, StrongDual.toWeakDual_apply,
    StrongDual.toStrongDual_toWeakDual, and_iff_right_iff_imp]
  exact fun _ a ha => ω.map_nonneg ha

/-- The states of `A` are exactly the positive linear maps `A →ₚ[ℂ] ℂ` of norm one, viewed in the
weak-* dual. -/
theorem mem_stateSpace_iff_exists_positiveLinearMap :
    φ ∈ stateSpace A ↔ ∃ ω : A →ₚ[ℂ] ℂ, ‖(PositiveContinuousLinearMap.ofClass ω : A →L[ℂ] ℂ)‖ = 1 ∧
      StrongDual.toWeakDual (PositiveContinuousLinearMap.ofClass ω : A →L[ℂ] ℂ) = φ := by
  refine ⟨fun hφ => ?_, fun ⟨ω, hω, h⟩ => h ▸ ω.toWeakDual_mem_stateSpace_iff.2 hω⟩
  let ω : A →ₚ[ℂ] ℂ := .mk₀ (toStrongDual φ : A →ₗ[ℂ] ℂ) fun _ => map_nonneg_of_mem_stateSpace hφ
  have hω : (PositiveContinuousLinearMap.ofClass ω : A →L[ℂ] ℂ) = toStrongDual φ := by
    -- `PositiveLinearMap.mk₀` has no evaluation lemma; it evaluates as `φ` by definition
    ext
    rfl
  exact ⟨ω, hω ▸ norm_toStrongDual_of_mem_stateSpace hφ, by rw [hω, toWeakDual_toStrongDual]⟩

/-- **Convexity of the state space.** Real convex combinations of states are states. -/
theorem convex_stateSpace : Convex ℝ (stateSpace A) := by
  intro φ hφ ψ hψ s t hs ht hst
  rw [mem_stateSpace_iff] at hφ hψ ⊢
  have hpos (a : A) (ha : 0 ≤ a) : 0 ≤ (s • φ + t • ψ) a := by
    simpa using add_nonneg (smul_nonneg hs (hφ.1 a ha)) (smul_nonneg ht (hψ.1 a ha))
  refine ⟨hpos, ?_⟩
  -- the norm of a positive functional is its limit along an approximate unit
  have h := ((tendsto_approximateUnit_norm_of_map_nonneg hφ.1).const_smul s).add
    ((tendsto_approximateUnit_norm_of_map_nonneg hψ.1).const_smul t)
  simp only [hφ.2, hψ.2, Complex.ofReal_one, ← add_smul, hst, one_smul] at h
  exact_mod_cast tendsto_nhds_unique (tendsto_approximateUnit_norm_of_map_nonneg hpos)
    (h.congr fun e => by simp)

variable {B F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

variable (A) in
/-- Precomposition of functionals with a star homomorphism `f : A → B`, as a complex-linear map
`WeakDual ℂ B →ₗ[ℂ] WeakDual ℂ A`. On states it is the pullback of states along `f`, which is
affine when `f` is surjective or unital. -/
noncomputable def pullbackFunctional (f : F) : WeakDual ℂ B →ₗ[ℂ] WeakDual ℂ A where
  toFun φ := StrongDual.toWeakDual
    ((toStrongDual φ).comp (PositiveContinuousLinearMap.ofClass f : A →L[ℂ] B))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The pullback of a functional along `f` evaluates as `φ ∘ f`. -/
@[simp]
theorem pullbackFunctional_apply (f : F) (φ : WeakDual ℂ B) (a : A) :
    pullbackFunctional A f φ a = φ (f a) :=
  (rfl)

/-- **Pullback of states along a surjective star homomorphism.** Composing a state of `B` with a
surjective star homomorphism `A → B` gives a state of `A`. Without surjectivity the norm of the
composite can drop, for instance to `0`. -/
theorem mapsTo_pullbackFunctional_stateSpace_of_surjective (f : F) (hf : Function.Surjective f) :
    MapsTo (pullbackFunctional A f) (stateSpace B) (stateSpace A) := by
  intro φ hφ
  let ω : B →P[ℂ] ℂ := .mk₀ (toStrongDual φ) fun _ => map_nonneg_of_mem_stateSpace hφ
  have hcomp : ((ω.comp (.ofClass f) : A →P[ℂ] ℂ) : A →L[ℂ] ℂ) =
      toStrongDual (pullbackFunctional A f φ) := by
    -- `PositiveContinuousLinearMap.mk₀` has no evaluation lemma; both sides evaluate as
    -- `φ ∘ f` by definition
    ext
    rfl
  refine mem_stateSpace_iff.2 ⟨fun a ha => map_nonneg_of_mem_stateSpace hφ (map_nonneg f ha), ?_⟩
  rw [← hcomp, PositiveContinuousLinearMap.opNorm_comp_ofClass_of_surjective ω f hf]
  exact norm_toStrongDual_of_mem_stateSpace hφ

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {φ : WeakDual ℂ A}

/-- On a unital C⋆-algebra, a functional that is nonnegative on nonnegative elements is a state
exactly when it takes the value `1` at `1`. -/
theorem mem_stateSpace_iff_map_one :
    φ ∈ stateSpace A ↔ (∀ a, 0 ≤ a → 0 ≤ φ a) ∧ φ 1 = 1 := by
  refine and_congr_right fun hpos => ?_
  rw [← norm_toStrongDual_eq_map_one_of_map_nonneg hpos]
  exact_mod_cast Iff.rfl

/-- A state of a unital C⋆-algebra takes the value `1` at `1`. -/
theorem map_one_of_mem_stateSpace (hφ : φ ∈ stateSpace A) : φ 1 = 1 :=
  (mem_stateSpace_iff_map_one.1 hφ).2

/-- On a unital C⋆-algebra, a functional is a state exactly when `‖φ‖ = φ 1 = 1`. Positivity is
then automatic: it follows from `φ 1 = ‖φ‖ = 1`. -/
theorem mem_stateSpace_iff_norm_eq_one_and_map_one :
    φ ∈ stateSpace A ↔ ‖toStrongDual φ‖ = 1 ∧ φ 1 = 1 := by
  refine ⟨fun hφ => ⟨norm_toStrongDual_of_mem_stateSpace hφ, map_one_of_mem_stateSpace hφ⟩,
    fun ⟨hnorm, h1⟩ => ?_⟩
  have hmono : Monotone (toStrongDual φ) := by
    rw [ContinuousLinearMap.monotone_iff_opNorm_eq_map_one, hnorm, toStrongDual_apply, h1,
      Complex.ofReal_one]
  exact mem_stateSpace_iff.2
    ⟨fun a ha => by simpa using (monotone_iff_map_nonneg _).mp hmono a ha, hnorm⟩

/-- For unital `A`, the state space is weak-* closed. -/
theorem isClosed_stateSpace : IsClosed (stateSpace A) := by
  have h : stateSpace A = {φ : WeakDual ℂ A | ∀ a, 0 ≤ a → 0 ≤ φ a} ∩ {φ | φ 1 = 1} :=
    Set.ext fun _ => mem_stateSpace_iff_map_one
  rw [h]
  exact isClosed_setOf_map_nonneg.inter (isClosed_eq (eval_continuous 1) continuous_const)

/-- **Weak-* compactness of the state space.** For unital `A`, the state space is weak-* compact,
by the Banach–Alaoglu theorem. -/
theorem isCompact_stateSpace : IsCompact (stateSpace A) := by
  refine (WeakDual.isCompact_closedBall 0 1).of_isClosed_subset isClosed_stateSpace
    fun φ hφ => ?_
  simp [norm_toStrongDual_of_mem_stateSpace hφ]

/-- **Existence of states.** A nonzero unital C⋆-algebra has a state. -/
theorem stateSpace_nonempty [Nontrivial A] : (stateSpace A).Nonempty := by
  -- by Hahn–Banach there is a functional of norm one attaining the norm `‖1‖ = 1` at `1`
  obtain ⟨g, hg, hg1⟩ := exists_dual_vector ℂ (1 : A) (by simp)
  refine ⟨StrongDual.toWeakDual g, mem_stateSpace_iff_norm_eq_one_and_map_one.2 ⟨hg, ?_⟩⟩
  simpa using hg1

/-- **Krein–Milman for states.** For unital `A`, the state space is the weak-* closed convex hull
of its extreme points, the pure states. -/
theorem closure_convexHull_extremePoints_stateSpace :
    closure (convexHull ℝ (extremePoints ℝ (stateSpace A))) = stateSpace A := by
  -- The weak-* dual inherits its real local convexity from the canonical dual pairing.
  let : IsScalarTower ℝ ℂ (WeakDual ℂ A) := inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ A))
  let : LocallyConvexSpace ℝ (WeakDual ℂ A) :=
    inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℂ A)))
  exact closure_convexHull_extremePoints isCompact_stateSpace convex_stateSpace

/-- **Existence of pure states.** A nonzero unital C⋆-algebra has an extreme state. -/
theorem extremePoints_stateSpace_nonempty [Nontrivial A] :
    (extremePoints ℝ (stateSpace A)).Nonempty := by
  -- The weak-* dual inherits its real local convexity from the canonical dual pairing.
  let : IsScalarTower ℝ ℂ (WeakDual ℂ A) := inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ A))
  let : LocallyConvexSpace ℝ (WeakDual ℂ A) :=
    inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℂ A)))
  exact isCompact_stateSpace.extremePoints_nonempty stateSpace_nonempty

/-- The only state of `ℂ` is the identity functional. -/
theorem stateSpace_complex :
    stateSpace ℂ = {StrongDual.toWeakDual (ContinuousLinearMap.id ℂ ℂ)} := by
  ext φ
  rw [mem_stateSpace_iff_map_one, mem_singleton_iff]
  refine ⟨fun ⟨_, h1⟩ => DFunLike.ext _ _ fun z => ?_, ?_⟩
  · simpa [h1] using (toStrongDual φ).map_smul z 1
  · rintro rfl
    exact ⟨fun a ha => by simpa using ha, by simp⟩

variable {B F : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [AlgHomClass F ℂ A B] [StarHomClass F A B]

/-- **Pullback of states along a unital star homomorphism.** Composing a state of `B` with a
unital star homomorphism `A → B` gives a state of `A`. -/
theorem mapsTo_pullbackFunctional_stateSpace (f : F) :
    MapsTo (pullbackFunctional A f) (stateSpace B) (stateSpace A) := by
  intro φ hφ
  refine mem_stateSpace_iff_map_one.2 ⟨fun a ha => ?_, ?_⟩
  · simpa using map_nonneg_of_mem_stateSpace hφ (map_nonneg f ha)
  · simpa using map_one_of_mem_stateSpace hφ

end Unital

end TauCeti
