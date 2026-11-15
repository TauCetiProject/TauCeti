/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Star
public import Mathlib.Topology.Hom.ContinuousEvalConst
public import Mathlib.Topology.UniformSpace.Pi
public import TauCeti.Algebra.Star.Basic

/-!
# Pointwise topology and uniform structure on `⋆`-algebra homomorphisms

For any target `B` carrying a topology or uniform structure, `NonUnitalStarAlgHom R A B`
(`A →⋆ₙₐ[R] B`) and `StarAlgHom R A B` (`A →⋆ₐ[R] B`) inherit the topology and uniformity of
pointwise convergence induced by function coercion into `A → B`. When `B` is a normed `⋆`-algebra
or C⋆-algebra, this is the **point-norm topology** on `⋆`-homomorphisms.

When `B` is Hausdorff and its algebraic operations (`+`, `*`, scalar multiplication by `R`, and
`star`) are continuous, `A →⋆ₙₐ[R] B` embeds as a closed subset of `A → B`, and `A →⋆ₐ[R] B`
embeds as the closed locus `{φ | φ 1 = 1}` inside `A →⋆ₙₐ[R] B`. Consequently both homomorphism
spaces inherit `CompleteSpace` from `B`, so pointwise Cauchy nets of `⋆`-homomorphisms converge
to a `⋆`-homomorphism.

## Main definitions and results

* `NonUnitalStarAlgHom.instTopologicalSpace`, `NonUnitalStarAlgHom.instUniformSpace`: pointwise
  topology and uniform structure on `A →⋆ₙₐ[R] B`.
* `NonUnitalStarAlgHom.tendsto_iff_forall_tendsto`, `NonUnitalStarAlgHom.continuous_iff`,
  `NonUnitalStarAlgHom.cauchy_iff_forall_cauchy`: pointwise characterizations of convergence,
  continuity, and Cauchy filters.
* `NonUnitalStarAlgHom.isClosedEmbedding_coeFn`, `NonUnitalStarAlgHom.instCompleteSpace`: closed
  embedding into `A → B` and completeness under continuous target operations.
* `StarAlgHom.instTopologicalSpace`, `StarAlgHom.instUniformSpace`,
  `StarAlgHom.isClosedEmbedding_toNonUnitalStarAlgHom`, `StarAlgHom.instCompleteSpace`:
  corresponding pointwise structures, closed embedding into `A →⋆ₙₐ[R] B`, and completeness for
  unital `⋆`-homomorphisms.
* `Unitary.continuous_conjStarAlgAut_toStarAlgHom`,
  `Unitary.continuous_conjStarAlgAut_toNonUnitalStarAlgHom`: continuity of `u ↦ Ad(u)` from
  `unitary A` into `A →⋆ₐ[R] A` and `A →⋆ₙₐ[R] A`.
-/

public section

open Filter Topology Uniformity

namespace NonUnitalStarAlgHom

section TopologicalSpace

variable {R A B C : Type*} [Monoid R]
  [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
  [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B] [TopologicalSpace B]

/-- The topology of pointwise convergence on `A →⋆ₙₐ[R] B`, induced from `A → B`. -/
instance instTopologicalSpace : TopologicalSpace (A →⋆ₙₐ[R] B) :=
  TopologicalSpace.induced DFunLike.coe Pi.topologicalSpace

theorem isInducing_coeFn : IsInducing (DFunLike.coe : (A →⋆ₙₐ[R] B) → A → B) :=
  ⟨rfl⟩

theorem isEmbedding_coeFn : IsEmbedding (DFunLike.coe : (A →⋆ₙₐ[R] B) → A → B) :=
  ⟨isInducing_coeFn, DFunLike.coe_injective⟩

@[fun_prop]
theorem continuous_coeFn : Continuous (DFunLike.coe : (A →⋆ₙₐ[R] B) → A → B) :=
  isInducing_coeFn.continuous

instance instContinuousEvalConst : ContinuousEvalConst (A →⋆ₙₐ[R] B) A B where
  continuous_eval_const a := (continuous_apply a).comp continuous_coeFn

instance instT0Space [T0Space B] : T0Space (A →⋆ₙₐ[R] B) :=
  isEmbedding_coeFn.t0Space

instance instT2Space [T2Space B] : T2Space (A →⋆ₙₐ[R] B) :=
  isEmbedding_coeFn.t2Space

theorem tendsto_iff_forall_tendsto {ι : Type*} {l : Filter ι} {f : ι → A →⋆ₙₐ[R] B}
    {φ : A →⋆ₙₐ[R] B} :
    Tendsto f l (𝓝 φ) ↔ ∀ a, Tendsto (fun i ↦ f i a) l (𝓝 (φ a)) := by
  rw [isInducing_coeFn.tendsto_nhds_iff, tendsto_pi_nhds]
  rfl

theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → A →⋆ₙₐ[R] B} :
    Continuous f ↔ ∀ a, Continuous fun x ↦ f x a := by
  rw [isInducing_coeFn.continuous_iff, continuous_pi_iff]
  rfl

section Comp

variable [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [Star C] [TopologicalSpace C]

/-- Precomposition by a fixed `⋆`-homomorphism is continuous for the pointwise topology, with no
topological assumptions on `A` or `B`. -/
theorem continuous_comp_right {B : Type*} [NonUnitalNonAssocSemiring B] [DistribMulAction R B]
    [Star B] (ψ : A →⋆ₙₐ[R] B) :
    Continuous fun φ : B →⋆ₙₐ[R] C ↦ φ.comp ψ :=
  continuous_iff.mpr fun a ↦ continuous_eval_const (ψ a)

/-- Postcomposition by a continuous `⋆`-homomorphism is continuous for the pointwise topology. -/
theorem continuous_comp_left {φ : B →⋆ₙₐ[R] C} (hφ : Continuous φ) :
    Continuous fun ψ : A →⋆ₙₐ[R] B ↦ φ.comp ψ :=
  continuous_iff.mpr fun a ↦ hφ.comp (continuous_eval_const a)

end Comp

section Closed

variable [T2Space B] [ContinuousAdd B] [ContinuousMul B] [ContinuousConstSMul R B]
  [ContinuousStar B]

/-- When `B` is Hausdorff with continuous operations, the functions underlying elements of
`A →⋆ₙₐ[R] B` form a closed subset of `A → B`. -/
theorem isClosed_range_coeFn :
    IsClosed (Set.range (DFunLike.coe : (A →⋆ₙₐ[R] B) → A → B)) := by
  have heq : Set.range (DFunLike.coe : (A →⋆ₙₐ[R] B) → A → B) =
      {g : A → B | g 0 = 0} ∩
      (⋂ (a : A) (b : A), {g : A → B | g (a + b) = g a + g b}) ∩
      (⋂ (a : A) (b : A), {g : A → B | g (a * b) = g a * g b}) ∩
      (⋂ (r : R) (a : A), {g : A → B | g (r • a) = r • g a}) ∩
      (⋂ a : A, {g : A → B | g (star a) = star (g a)}) := by
    ext g
    simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    refine ⟨?_, fun ⟨⟨⟨⟨h0, hadd⟩, hmul⟩, hsmul⟩, hstar⟩ ↦ ?_⟩
    · rintro ⟨φ, rfl⟩
      exact ⟨⟨⟨⟨map_zero φ, map_add φ⟩, map_mul φ⟩, map_smul φ⟩, map_star φ⟩
    · exact ⟨{ toFun := g
               map_zero' := h0
               map_add' := hadd
               map_mul' := hmul
               map_smul' := hsmul
               map_star' := hstar }, rfl⟩
  rw [heq]
  refine ((((isClosed_eq (continuous_apply 0) continuous_const).inter ?_).inter ?_).inter ?_).inter
    ?_
  · exact isClosed_iInter fun a ↦ isClosed_iInter fun b ↦
      isClosed_eq (continuous_apply (a + b)) ((continuous_apply a).add (continuous_apply b))
  · exact isClosed_iInter fun a ↦ isClosed_iInter fun b ↦
      isClosed_eq (continuous_apply (a * b)) ((continuous_apply a).mul (continuous_apply b))
  · exact isClosed_iInter fun r ↦ isClosed_iInter fun a ↦
      isClosed_eq (continuous_apply (r • a)) ((continuous_apply a).const_smul r)
  · exact isClosed_iInter fun a ↦
      isClosed_eq (continuous_apply (star a)) (continuous_apply a).star

theorem isClosedEmbedding_coeFn :
    IsClosedEmbedding (DFunLike.coe : (A →⋆ₙₐ[R] B) → A → B) :=
  ⟨isEmbedding_coeFn, isClosed_range_coeFn⟩

end Closed

end TopologicalSpace

section UniformSpace

variable {R A B : Type*} [Monoid R]
  [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
  [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B] [UniformSpace B]

/-- The uniform structure of pointwise convergence on `A →⋆ₙₐ[R] B`, induced from `A → B`.
Its underlying topology is definitionally `NonUnitalStarAlgHom.instTopologicalSpace`. -/
instance instUniformSpace : UniformSpace (A →⋆ₙₐ[R] B) :=
  fast_instance% (UniformSpace.comap DFunLike.coe (Pi.uniformSpace fun _ ↦ B)).replaceTopology rfl

theorem isUniformInducing_coeFn :
    IsUniformInducing (DFunLike.coe : (A →⋆ₙₐ[R] B) → A → B) :=
  ⟨rfl⟩

theorem isUniformEmbedding_coeFn :
    IsUniformEmbedding (DFunLike.coe : (A →⋆ₙₐ[R] B) → A → B) :=
  ⟨isUniformInducing_coeFn, DFunLike.coe_injective⟩

theorem uniformContinuous_coeFn :
    UniformContinuous (DFunLike.coe : (A →⋆ₙₐ[R] B) → A → B) :=
  isUniformInducing_coeFn.uniformContinuous

theorem hasBasis_nhds (φ : A →⋆ₙₐ[R] B) :
    (𝓝 φ).HasBasis (fun p : Finset A × Set (B × B) ↦ p.2 ∈ 𝓤 B)
      fun p ↦ {ψ | ∀ a ∈ p.1, (ψ a, φ a) ∈ p.2} := by
  classical
  rw [isInducing_coeFn.nhds_eq_comap, nhds_pi]
  have hpi := Filter.hasBasis_pi_same_index
    (fun a ↦ nhds_basis_uniformity (x := φ a) (𝓤 B).basis_sets) fun I U hI hU ↦
      ⟨⋂ a ∈ I, U a, (Filter.biInter_mem hI).mpr hU,
        fun a ha _ hb ↦ SetRel.mem_ball.mpr (Set.mem_iInter₂.mp (SetRel.mem_ball.mp hb) a ha)⟩
  refine (hpi.comap DFunLike.coe).to_hasBasis ?_ ?_
  · rintro ⟨I, U⟩ ⟨hI, hU⟩
    exact ⟨⟨hI.toFinset, U⟩, hU, fun ψ hψ a ha ↦
      SetRel.mem_ball.mpr (hψ a (hI.mem_toFinset.mpr ha))⟩
  · rintro ⟨F, U⟩ hU
    exact ⟨⟨(F : Set A), U⟩, ⟨F.finite_toSet, hU⟩, fun ψ hψ a ha ↦ SetRel.mem_ball.mp (hψ a ha)⟩

theorem cauchy_iff_forall_cauchy {l : Filter (A →⋆ₙₐ[R] B)} :
    Cauchy l ↔ ∀ a, Cauchy (l.map (· a)) := by
  rw [← isUniformInducing_coeFn.cauchy_map_iff, cauchy_pi_iff]
  simp [Filter.map_map, Function.comp_def]

theorem cauchySeq_iff_forall_cauchySeq {ι : Type*} [Preorder ι] {f : ι → A →⋆ₙₐ[R] B} :
    CauchySeq f ↔ ∀ a, CauchySeq fun i ↦ f i a := by
  simp only [CauchySeq, cauchy_iff_forall_cauchy, Filter.map_map, Function.comp_def]

instance instCompleteSpace [CompleteSpace B] [T0Space B] [ContinuousAdd B] [ContinuousMul B]
    [ContinuousConstSMul R B] [ContinuousStar B] : CompleteSpace (A →⋆ₙₐ[R] B) := by
  rw [completeSpace_iff_isComplete_range isUniformInducing_coeFn]
  exact isClosed_range_coeFn.isComplete

end UniformSpace

end NonUnitalStarAlgHom

namespace StarAlgHom

section TopologicalSpace

variable {R A B C : Type*} [CommSemiring R]
  [Semiring A] [Algebra R A] [Star A]
  [Semiring B] [Algebra R B] [Star B] [TopologicalSpace B]

/-- The topology of pointwise convergence on `A →⋆ₐ[R] B`, induced from `A → B`. -/
instance instTopologicalSpace : TopologicalSpace (A →⋆ₐ[R] B) :=
  TopologicalSpace.induced DFunLike.coe Pi.topologicalSpace

theorem isInducing_coeFn : IsInducing (DFunLike.coe : (A →⋆ₐ[R] B) → A → B) :=
  ⟨rfl⟩

theorem isEmbedding_coeFn : IsEmbedding (DFunLike.coe : (A →⋆ₐ[R] B) → A → B) :=
  ⟨isInducing_coeFn, DFunLike.coe_injective⟩

@[fun_prop]
theorem continuous_coeFn : Continuous (DFunLike.coe : (A →⋆ₐ[R] B) → A → B) :=
  isInducing_coeFn.continuous

instance instContinuousEvalConst : ContinuousEvalConst (A →⋆ₐ[R] B) A B where
  continuous_eval_const a := (continuous_apply a).comp continuous_coeFn

instance instT0Space [T0Space B] : T0Space (A →⋆ₐ[R] B) :=
  isEmbedding_coeFn.t0Space

instance instT2Space [T2Space B] : T2Space (A →⋆ₐ[R] B) :=
  isEmbedding_coeFn.t2Space

theorem isInducing_toNonUnitalStarAlgHom :
    IsInducing (toNonUnitalStarAlgHom : (A →⋆ₐ[R] B) → A →⋆ₙₐ[R] B) :=
  NonUnitalStarAlgHom.isInducing_coeFn.of_comp_iff.mp isInducing_coeFn

theorem isEmbedding_toNonUnitalStarAlgHom :
    IsEmbedding (toNonUnitalStarAlgHom : (A →⋆ₐ[R] B) → A →⋆ₙₐ[R] B) :=
  ⟨isInducing_toNonUnitalStarAlgHom, toNonUnitalStarAlgHom_injective⟩

@[fun_prop]
theorem continuous_toNonUnitalStarAlgHom :
    Continuous (toNonUnitalStarAlgHom : (A →⋆ₐ[R] B) → A →⋆ₙₐ[R] B) :=
  isInducing_toNonUnitalStarAlgHom.continuous

theorem tendsto_iff_forall_tendsto {ι : Type*} {l : Filter ι} {f : ι → A →⋆ₐ[R] B}
    {φ : A →⋆ₐ[R] B} :
    Tendsto f l (𝓝 φ) ↔ ∀ a, Tendsto (fun i ↦ f i a) l (𝓝 (φ a)) := by
  rw [isInducing_coeFn.tendsto_nhds_iff, tendsto_pi_nhds]
  rfl

theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → A →⋆ₐ[R] B} :
    Continuous f ↔ ∀ a, Continuous fun x ↦ f x a := by
  rw [isInducing_coeFn.continuous_iff, continuous_pi_iff]
  rfl

section Comp

variable [Semiring C] [Algebra R C] [Star C] [TopologicalSpace C]

/-- Precomposition by a fixed `StarAlgHom` is continuous for the pointwise topology, with no
topological assumptions on `A` or `B`. -/
theorem continuous_comp_right {B : Type*} [Semiring B] [Algebra R B] [Star B]
    (ψ : A →⋆ₐ[R] B) : Continuous fun φ : B →⋆ₐ[R] C ↦ φ.comp ψ :=
  continuous_iff.mpr fun a ↦ continuous_eval_const (ψ a)

/-- Postcomposition by a continuous `StarAlgHom` is continuous for the pointwise topology. -/
theorem continuous_comp_left {φ : B →⋆ₐ[R] C} (hφ : Continuous φ) :
    Continuous fun ψ : A →⋆ₐ[R] B ↦ φ.comp ψ :=
  continuous_iff.mpr fun a ↦ hφ.comp (continuous_eval_const a)

end Comp

theorem isClosed_range_toNonUnitalStarAlgHom [T2Space B] :
    IsClosed (Set.range (toNonUnitalStarAlgHom : (A →⋆ₐ[R] B) → A →⋆ₙₐ[R] B)) := by
  rw [range_toNonUnitalStarAlgHom]
  exact isClosed_eq (continuous_eval_const 1) continuous_const

theorem isClosedEmbedding_toNonUnitalStarAlgHom [T2Space B] :
    IsClosedEmbedding (toNonUnitalStarAlgHom : (A →⋆ₐ[R] B) → A →⋆ₙₐ[R] B) :=
  ⟨isEmbedding_toNonUnitalStarAlgHom, isClosed_range_toNonUnitalStarAlgHom⟩

theorem isClosedEmbedding_coeFn [T2Space B] [ContinuousAdd B] [ContinuousMul B]
    [ContinuousConstSMul R B] [ContinuousStar B] :
    IsClosedEmbedding (DFunLike.coe : (A →⋆ₐ[R] B) → A → B) :=
  NonUnitalStarAlgHom.isClosedEmbedding_coeFn.comp isClosedEmbedding_toNonUnitalStarAlgHom

end TopologicalSpace

section UniformSpace

variable {R A B : Type*} [CommSemiring R]
  [Semiring A] [Algebra R A] [Star A]
  [Semiring B] [Algebra R B] [Star B] [UniformSpace B]

/-- The uniform structure of pointwise convergence on `A →⋆ₐ[R] B`, induced from `A → B`.
Its underlying topology is definitionally `StarAlgHom.instTopologicalSpace`. -/
instance instUniformSpace : UniformSpace (A →⋆ₐ[R] B) :=
  fast_instance% (UniformSpace.comap DFunLike.coe (Pi.uniformSpace fun _ ↦ B)).replaceTopology rfl

theorem isUniformInducing_coeFn :
    IsUniformInducing (DFunLike.coe : (A →⋆ₐ[R] B) → A → B) :=
  ⟨rfl⟩

theorem isUniformEmbedding_coeFn :
    IsUniformEmbedding (DFunLike.coe : (A →⋆ₐ[R] B) → A → B) :=
  ⟨isUniformInducing_coeFn, DFunLike.coe_injective⟩

theorem uniformContinuous_coeFn :
    UniformContinuous (DFunLike.coe : (A →⋆ₐ[R] B) → A → B) :=
  isUniformInducing_coeFn.uniformContinuous

theorem isUniformInducing_toNonUnitalStarAlgHom :
    IsUniformInducing (toNonUnitalStarAlgHom : (A →⋆ₐ[R] B) → A →⋆ₙₐ[R] B) :=
  NonUnitalStarAlgHom.isUniformInducing_coeFn.of_comp_iff.mp isUniformInducing_coeFn

theorem isUniformEmbedding_toNonUnitalStarAlgHom :
    IsUniformEmbedding (toNonUnitalStarAlgHom : (A →⋆ₐ[R] B) → A →⋆ₙₐ[R] B) :=
  ⟨isUniformInducing_toNonUnitalStarAlgHom, toNonUnitalStarAlgHom_injective⟩

theorem uniformContinuous_toNonUnitalStarAlgHom :
    UniformContinuous (toNonUnitalStarAlgHom : (A →⋆ₐ[R] B) → A →⋆ₙₐ[R] B) :=
  isUniformInducing_toNonUnitalStarAlgHom.uniformContinuous

theorem hasBasis_nhds (φ : A →⋆ₐ[R] B) :
    (𝓝 φ).HasBasis (fun p : Finset A × Set (B × B) ↦ p.2 ∈ 𝓤 B)
      fun p ↦ {ψ | ∀ a ∈ p.1, (ψ a, φ a) ∈ p.2} := by
  rw [isInducing_toNonUnitalStarAlgHom.nhds_eq_comap]
  exact (φ.toNonUnitalStarAlgHom.hasBasis_nhds).comap toNonUnitalStarAlgHom

theorem cauchy_iff_forall_cauchy {l : Filter (A →⋆ₐ[R] B)} :
    Cauchy l ↔ ∀ a, Cauchy (l.map (· a)) := by
  rw [← isUniformInducing_coeFn.cauchy_map_iff, cauchy_pi_iff]
  simp [Filter.map_map, Function.comp_def]

theorem cauchySeq_iff_forall_cauchySeq {ι : Type*} [Preorder ι] {f : ι → A →⋆ₐ[R] B} :
    CauchySeq f ↔ ∀ a, CauchySeq fun i ↦ f i a := by
  simp only [CauchySeq, cauchy_iff_forall_cauchy, Filter.map_map, Function.comp_def]

instance instCompleteSpace [CompleteSpace B] [T0Space B] [ContinuousAdd B] [ContinuousMul B]
    [ContinuousConstSMul R B] [ContinuousStar B] : CompleteSpace (A →⋆ₐ[R] B) := by
  rw [completeSpace_iff_isComplete_range isUniformInducing_toNonUnitalStarAlgHom]
  exact isClosed_range_toNonUnitalStarAlgHom.isComplete

end UniformSpace

end StarAlgHom

namespace Unitary

variable {R A : Type*} [CommSemiring R] [Semiring A] [StarMul A] [Algebra R A]
  [TopologicalSpace A] [ContinuousMul A] [ContinuousStar A]

/-- Sending a unitary `u : unitary A` to the inner `⋆`-automorphism `x ↦ u * x * star u` is
continuous into `A →⋆ₐ[R] A` equipped with the topology of pointwise convergence. -/
@[fun_prop]
theorem continuous_conjStarAlgAut_toStarAlgHom :
    Continuous fun u : unitary A ↦ (conjStarAlgAut R A u).toStarAlgHom :=
  StarAlgHom.continuous_iff.mpr fun a ↦ by
    simp only [StarAlgEquiv.toStarAlgHom_apply, conjStarAlgAut_apply]
    fun_prop

/-- Sending a unitary `u : unitary A` to the inner `⋆`-automorphism `x ↦ u * x * star u` is
continuous into `A →⋆ₙₐ[R] A` equipped with the topology of pointwise convergence. -/
@[fun_prop]
theorem continuous_conjStarAlgAut_toNonUnitalStarAlgHom :
    Continuous fun u : unitary A ↦ (conjStarAlgAut R A u).toNonUnitalStarAlgHom :=
  StarAlgHom.continuous_toNonUnitalStarAlgHom.comp continuous_conjStarAlgAut_toStarAlgHom

end Unitary
