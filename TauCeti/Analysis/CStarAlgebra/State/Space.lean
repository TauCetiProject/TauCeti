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
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# The state space of a C⋆-algebra

A *state* of a possibly nonunital C⋆-algebra `A` is a positive linear functional of norm one.
This file defines the state space `TauCeti.stateSpace A` as a subset of the weak-* dual
`WeakDual ℂ A`, so that convexity, closedness and compactness refer to the weak-* topology.

* `TauCeti.stateSpace_eq_empty`: the state space of a subsingleton C⋆-algebra is empty.
* `TauCeti.statePositiveLinearMap` and `TauCeti.mem_stateSpace_iff_exists_positiveLinearMap`: the
  states are exactly the positive linear maps `A →ₚ[ℂ] ℂ` of norm one, through the automatic
  continuity of positive maps; in particular every state preserves the involution,
  `TauCeti.map_star_of_mem_stateSpace`.
* `TauCeti.convex_stateSpace` and `TauCeti.toWeakDual_tsum_mem_stateSpace`: the state space is
  closed under finite and infinite convex combinations. No unit is needed, because the norm of a
  positive functional is its limit along an approximate unit.
* `TauCeti.pullbackFunctional`: precomposition with a star homomorphism, as a continuous
  complex-linear map of weak-* duals. By
  `TauCeti.mapsTo_pullbackFunctional_stateSpace_of_surjective` and
  `TauCeti.mapsTo_pullbackFunctional_stateSpace` it restricts to an affine map of state spaces
  along surjective star homomorphisms and along unital star homomorphisms.

For unital `A`:

* `TauCeti.mem_stateSpace_iff_map_one`: a positive functional is a state exactly when `φ 1 = 1`,
  and `TauCeti.mem_stateSpace_iff_norm_eq_one_and_map_one`: a functional is a state exactly when
  `‖φ‖ = φ 1 = 1`, with positivity then automatic.
* `TauCeti.isCompact_stateSpace`: the state space is weak-* compact, by Banach–Alaoglu. The state
  space of `ℂ` is the single functional `z ↦ z`, `TauCeti.stateSpace_complex` (general existence of
  states for nonzero possibly nonunital C⋆-algebras is proved in
  `TauCeti.Analysis.CStarAlgebra.State.Separation`).
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

/-- The state space of a subsingleton C⋆-algebra is empty. -/
@[simp]
theorem stateSpace_eq_empty [Subsingleton A] : stateSpace A = ∅ := by
  ext φ
  have h0 : toStrongDual φ = 0 := by ext a; simp [Subsingleton.elim a 0]
  simp [mem_stateSpace_iff, h0]

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

/-- A positive continuous linear functional is a state exactly when its norm is one. -/
@[simp]
theorem _root_.PositiveContinuousLinearMap.toWeakDual_mem_stateSpace_iff (ω : A →P[ℂ] ℂ) :
    StrongDual.toWeakDual (ω : A →L[ℂ] ℂ) ∈ stateSpace A ↔ ‖(ω : A →L[ℂ] ℂ)‖ = 1 := by
  simp only [mem_stateSpace_iff, StrongDual.toWeakDual_apply,
    StrongDual.toStrongDual_toWeakDual, and_iff_right_iff_imp]
  exact fun _ a ha => ω.map_nonneg ha

/-- A weighted family `w i • toStrongDual (φ i)` of states with nonnegative summable weights `w`
is norm-summable in `StrongDual ℂ A`. -/
theorem summable_smul_toStrongDual_of_mem_stateSpace {ι : Type*} {φ : ι → WeakDual ℂ A}
    (hφ : ∀ i, φ i ∈ stateSpace A) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw : Summable w) :
    Summable fun i ↦ w i • toStrongDual (φ i) :=
  Summable.of_norm_bounded hw fun i ↦ by
    rw [norm_smul, Real.norm_of_nonneg (hw0 i), norm_toStrongDual_of_mem_stateSpace (hφ i), mul_one]

/-- Pointwise evaluation of `StrongDual.toWeakDual (∑' i, w i • toStrongDual (φ i))` is the
corresponding weighted sum of `φ i a`. -/
theorem hasSum_toWeakDual_tsum_apply_of_mem_stateSpace {ι : Type*} {φ : ι → WeakDual ℂ A}
    (hφ : ∀ i, φ i ∈ stateSpace A) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw : Summable w) (a : A) :
    HasSum (fun i ↦ (w i : ℂ) * φ i a)
      (StrongDual.toWeakDual (∑' i, w i • toStrongDual (φ i)) a) := by
  simpa [Complex.real_smul] using
    (ContinuousLinearMap.apply ℂ ℂ a).hasSum
      (summable_smul_toStrongDual_of_mem_stateSpace hφ hw0 hw).hasSum

variable [StarOrderedRing A]

/-- A state `φ : stateSpace A` bundled as a positive linear map `A →ₚ[ℂ] ℂ`. -/
noncomputable def statePositiveLinearMap (φ : stateSpace A) : A →ₚ[ℂ] ℂ :=
  .mk₀ (toStrongDual φ.1 : A →ₗ[ℂ] ℂ) fun _ ↦ map_nonneg_of_mem_stateSpace φ.2

@[simp]
theorem statePositiveLinearMap_apply (φ : stateSpace A) (a : A) :
    statePositiveLinearMap φ a = φ.1 a :=
  (rfl)

/-- Bundling a state as `A →ₚ[ℂ] ℂ` is injective. -/
theorem statePositiveLinearMap_injective :
    Function.Injective (statePositiveLinearMap (A := A)) :=
  fun _ _ h ↦ Subtype.ext <| DFunLike.ext _ _ fun a ↦ DFunLike.congr_fun h a

@[simp]
theorem statePositiveLinearMap_inj {φ ψ : stateSpace A} :
    statePositiveLinearMap φ = statePositiveLinearMap ψ ↔ φ = ψ :=
  statePositiveLinearMap_injective.eq_iff

@[simp]
theorem toWeakDual_ofClass_statePositiveLinearMap (φ : stateSpace A) :
    StrongDual.toWeakDual
      (PositiveContinuousLinearMap.ofClass (statePositiveLinearMap φ) : A →L[ℂ] ℂ) = φ.1 :=
  DFunLike.ext _ _ fun a ↦ by simp

@[simp]
theorem norm_ofClass_statePositiveLinearMap (φ : stateSpace A) :
    ‖(PositiveContinuousLinearMap.ofClass (statePositiveLinearMap φ) : A →L[ℂ] ℂ)‖ = 1 := by
  have h : (PositiveContinuousLinearMap.ofClass (statePositiveLinearMap φ) : A →L[ℂ] ℂ) =
      toStrongDual φ.1 := by
    ext a
    simp
  rw [h, norm_toStrongDual_of_mem_stateSpace φ.2]

/-- The states of `A` are exactly the positive linear maps `A →ₚ[ℂ] ℂ` of norm one, viewed in the
weak-* dual. -/
theorem mem_stateSpace_iff_exists_positiveLinearMap :
    φ ∈ stateSpace A ↔ ∃ ω : A →ₚ[ℂ] ℂ, ‖(PositiveContinuousLinearMap.ofClass ω : A →L[ℂ] ℂ)‖ = 1 ∧
      StrongDual.toWeakDual (PositiveContinuousLinearMap.ofClass ω : A →L[ℂ] ℂ) = φ :=
  ⟨fun hφ => ⟨statePositiveLinearMap ⟨φ, hφ⟩, norm_ofClass_statePositiveLinearMap ⟨φ, hφ⟩,
    toWeakDual_ofClass_statePositiveLinearMap ⟨φ, hφ⟩⟩,
    fun ⟨ω, hω, h⟩ =>
      h ▸ (PositiveContinuousLinearMap.ofClass ω).toWeakDual_mem_stateSpace_iff.2 hω⟩

/-- Every state preserves the involution: `φ (star a) = star (φ a)`. -/
theorem map_star_of_mem_stateSpace (hφ : φ ∈ stateSpace A) (a : A) :
    φ (star a) = star (φ a) := by
  simpa using map_star (statePositiveLinearMap ⟨φ, hφ⟩) a

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

/-- **Infinite convex combinations of states are states.** If `φ i` are states of `A` and
`w i ≥ 0` satisfy `HasSum w 1`, then the norm-convergent series `∑' i, w i • toStrongDual (φ i)`
defines a state of `A`. -/
theorem toWeakDual_tsum_mem_stateSpace {ι : Type*} {φ : ι → WeakDual ℂ A}
    (hφ : ∀ i, φ i ∈ stateSpace A) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : HasSum w 1) :
    StrongDual.toWeakDual (∑' i, w i • toStrongDual (φ i)) ∈ stateSpace A := by
  set ψ : WeakDual ℂ A := StrongDual.toWeakDual (∑' i, w i • toStrongDual (φ i))
  have hpos (a : A) (ha : 0 ≤ a) : 0 ≤ ψ a := by
    refine ge_of_tendsto (hasSum_toWeakDual_tsum_apply_of_mem_stateSpace hφ hw0 hw1.summable a)
      <| .of_forall fun s ↦ Finset.sum_nonneg fun i _ ↦ ?_
    exact mul_nonneg (Complex.zero_le_real.2 (hw0 i)) (map_nonneg_of_mem_stateSpace (hφ i) ha)
  refine mem_stateSpace_iff.2 ⟨hpos, le_antisymm ?_ ?_⟩
  · simpa [ψ] using tsum_of_norm_bounded hw1 fun i ↦ by
      rw [norm_smul, Real.norm_of_nonneg (hw0 i), norm_toStrongDual_of_mem_stateSpace (hφ i),
        mul_one]
  · have hl := CStarAlgebra.increasingApproximateUnit A
    have := hl.neBot
    have hψ_lim : Tendsto (fun e ↦ ψ e) (CStarAlgebra.approximateUnit A)
        (𝓝 (‖toStrongDual ψ‖ : ℂ)) :=
      tendsto_approximateUnit_norm_of_map_nonneg hpos
    refine le_of_tendsto hw1 <| .of_forall fun s ↦ ?_
    have hterm_lim (i : ι) : Tendsto (fun e : A ↦ w i * (φ i e).re)
        (CStarAlgebra.approximateUnit A) (𝓝 (w i)) := by
      have hφi : Tendsto (fun e : A ↦ φ i e) (CStarAlgebra.approximateUnit A) (𝓝 (1 : ℂ)) := by
        simpa [norm_toStrongDual_of_mem_stateSpace (hφ i)] using
          tendsto_approximateUnit_norm_of_map_nonneg
            (fun a ha ↦ map_nonneg_of_mem_stateSpace (hφ i) ha)
      have hre : Tendsto (fun e : A ↦ (φ i e).re) (CStarAlgebra.approximateUnit A) (𝓝 1) :=
        ((Complex.continuous_re.tendsto (1 : ℂ)).comp hφi).congr fun _ ↦ rfl
      simpa only [mul_one] using tendsto_const_nhds.mul hre
    have hψ_re : Tendsto (fun e : A ↦ (ψ e).re) (CStarAlgebra.approximateUnit A)
        (𝓝 ‖toStrongDual ψ‖) :=
      ((Complex.continuous_re.tendsto (‖toStrongDual ψ‖ : ℂ)).comp hψ_lim).congr fun _ ↦ rfl
    refine le_of_tendsto_of_tendsto (tendsto_finsetSum s fun i _ ↦ hterm_lim i) hψ_re ?_
    filter_upwards [hl.eventually_nonneg] with e he
    have he_re : HasSum (fun i ↦ w i * (φ i e).re) (ψ e).re := by
      simpa [ψ] using Complex.reCLM.hasSum
        (hasSum_toWeakDual_tsum_apply_of_mem_stateSpace hφ hw0 hw1.summable e)
    exact he_re.summable.sum_le_tsum s (fun k _ ↦ mul_nonneg (hw0 k)
      (Complex.nonneg_iff.1 (map_nonneg_of_mem_stateSpace (hφ k) he)).1) |>.trans_eq he_re.tsum_eq

variable {B F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

variable (A) in
/-- Precomposition of functionals with a star homomorphism `f : A → B`, as a weak-* continuous
complex-linear map `WeakDual ℂ B →L[ℂ] WeakDual ℂ A`; it is continuous because each evaluation
`φ ↦ φ (f a)` is. On states it is the pullback of states along `f`, which is affine when `f` is
surjective or unital. -/
noncomputable def pullbackFunctional (f : F) : WeakDual ℂ B →L[ℂ] WeakDual ℂ A where
  toFun φ := StrongDual.toWeakDual
    ((toStrongDual φ).comp (PositiveContinuousLinearMap.ofClass f : A →L[ℂ] B))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_of_continuous_eval fun a => eval_continuous (f a)

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

private theorem unital_stateSpace_nonempty [Nontrivial A] : (stateSpace A).Nonempty := by
  -- by Hahn–Banach there is a functional of norm one attaining the norm `‖1‖ = 1` at `1`
  obtain ⟨g, hg, hg1⟩ := exists_dual_vector ℂ (1 : A) (by simp)
  refine ⟨StrongDual.toWeakDual g, mem_stateSpace_iff_norm_eq_one_and_map_one.2 ⟨hg, ?_⟩⟩
  simpa using hg1

/-- **Krein–Milman for states.** For unital `A`, the state space is the weak-* closed convex hull
of its extreme points, the pure states. -/
theorem closure_convexHull_extremePoints_stateSpace :
    closure (convexHull ℝ (extremePoints ℝ (stateSpace A))) = stateSpace A :=
  closure_convexHull_extremePoints isCompact_stateSpace convex_stateSpace

/-- **Existence of pure states.** A nonzero unital C⋆-algebra has an extreme state. -/
theorem extremePoints_stateSpace_nonempty [Nontrivial A] :
    (extremePoints ℝ (stateSpace A)).Nonempty :=
  isCompact_stateSpace.extremePoints_nonempty unital_stateSpace_nonempty

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
