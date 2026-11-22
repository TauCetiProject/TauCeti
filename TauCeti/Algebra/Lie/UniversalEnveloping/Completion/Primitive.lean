/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Graded.Completion
public import TauCeti.Algebra.Lie.UniversalEnveloping.Completion.Bialgebra

import TauCeti.Algebra.DirectSum.Component
import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Symmetrization.Injective
import TauCeti.Algebra.Lie.UniversalEnveloping.Primitive
import TauCeti.LinearAlgebra.TensorProduct.Decomposition

/-!
# Completed primitive elements of positively graded universal enveloping algebras

Let `L` be a Lie algebra over a commutative ring `R` equipped with a positive grading `ℒ` by
`(d : PositiveDegrees N)`. The canonical Lie homomorphism `ι : L → U(L)` carries the degree ideal
`d.degreeIdeal ℒ k` of elements strictly above cutoff `k` into
`(degreeFiltration ℒ d.degree _).ideal (k + 1)`, inducing compatible Lie homomorphisms
`truncatedLieToU` at every finite cutoff and a Lie homomorphism `completedLieToU` from the
completed Lie algebra `d.completedLie ℒ` into `completedEnveloping`.

Every element in the image of `completedLieToU` is completed primitive and lies in the first
completion ideal. When `ι : L → U(L)` is injective, `truncatedLieToU` and `completedLieToU` are
injective. Conversely, using the internal tensor-product grading of `U(L) ⊗[R] U(L)`, every
homogeneous component of a completed primitive element in `completedEnveloping` is an ordinary
primitive element of `U(L)`. Over a commutative `ℚ`-algebra `R : Type`, combining this
componentwise primitivity with `TauCeti.UniversalEnvelopingAlgebra.primitiveEquiv` identifies the
completed primitive Lie subalgebra of `completedEnveloping` with `d.completedLie ℒ`, without any
freeness or finite-rank hypothesis on `L`.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.truncatedLieToU`: the Lie homomorphism from
  `d.truncatedLie ℒ k` to the order-`k` enveloping quotient.
* `TauCeti.UniversalEnvelopingAlgebra.completedLieToU`: the Lie homomorphism from
  `d.completedLie ℒ` to `completedEnveloping`.
* `TauCeti.UniversalEnvelopingAlgebra.envelopingComponent`: homogeneous component projection on
  `completedEnveloping`, obtained via `TauCeti.PositiveDegrees.completionComponent`.
* `TauCeti.UniversalEnvelopingAlgebra.completedPrimitiveLieEquiv`: Lie isomorphism between
  `d.completedLie ℒ` and `completedPrimitiveLieSubalgebra` over a commutative `ℚ`-algebra.
* `TauCeti.UniversalEnvelopingAlgebra.completedLieExpEquiv`: equivalence between
  `d.completedLie ℒ` and the completed grouplike elements of `completedEnveloping` over a
  commutative `ℚ`-algebra.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.completedLieToU_injective`: `completedLieToU` is injective
  whenever `ι : L → U(L)` is injective.
* `TauCeti.UniversalEnvelopingAlgebra.isCompletedPrimitive_completedLieToU`: every element in the
  image of `completedLieToU` is completed primitive.
* `TauCeti.UniversalEnvelopingAlgebra.isCompletedPrimitive_iff_mem_range_completedLieToU`: over a
  commutative `ℚ`-algebra `R : Type`, the completed primitive elements of `completedEnveloping`
  are precisely the image of `completedLieToU`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter II, §6.
* J.-P. Serre, *Lie Algebras and Lie Groups*, Part I, Chapter IV.
* E. Petracci, *Universal representations of Lie algebras by coderivations*,
  arXiv:math/0303020, §8 (used via `TauCeti.UniversalEnvelopingAlgebra.primitiveEquiv` and
  `TauCeti.UniversalEnvelopingAlgebra.ι_injective_of_algebra_rat`).
-/

public section

open scoped TensorProduct DirectSum

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra
open _root_.DirectSum (decompose decompose_sum decompose_of_mem_same decompose_of_mem_ne
  decomposeLinearEquiv)

section CommRing

variable {N R L : Type*} [AddCommMonoid N] [CommRing R] [LieRing L] [LieAlgebra R L]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "Û" => completedEnveloping ℒ d.degree (d.eq_bot_of_degree_neg ℒ)
local notation "𝓕" => degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)

/-- The canonical Lie map sends `d.degreeIdeal ℒ k` into filtration order `k + 1`. -/
theorem ι_mem_degreeFiltration_succ_of_mem_degreeIdeal {k : ℕ} {x : L}
    (hx : x ∈ d.degreeIdeal ℒ k) : ι R x ∈ (𝓕).ideal (k + 1) := by
  rw [mem_degreeFiltration_ideal_iff]; intro n hn
  rw [ι_apply, coe_decompose_mkAlgHom_ι, (d.mem_degreeIdeal_iff ℒ).mp hx n (by omega), map_zero]

/-- When `ι : L → U(L)` is injective, the preimage of filtration order `k + 1` is
`d.degreeIdeal ℒ k`. -/
theorem comap_degreeFiltration_succ_ι (hι : Function.Injective (ι R : L → U)) (k : ℕ) :
    (((𝓕).ideal (k + 1)).restrictScalars R).comap (ι R : L →ₗ⁅R⁆ U).toLinearMap =
      (d.degreeIdeal ℒ k).toSubmodule := by
  rw [comap_degreeFiltration_ι ℒ d.degree (d.eq_bot_of_degree_neg ℒ) hι (k + 1)]; ext x
  simp only [DirectSum.mem_degreeTail_iff, LieSubmodule.mem_toSubmodule, d.mem_degreeIdeal_iff ℒ]
  exact ⟨fun h n hn => h n (by omega), fun h n hn => h n (by omega)⟩

/-- The Lie homomorphism from the order-`k` Lie truncation to the order-`k` enveloping quotient. -/
noncomputable def truncatedLieToU (k : ℕ) :
    d.truncatedLie ℒ k →ₗ⁅R⁆ U ⧸ (𝓕).ideal (k + 1) :=
  (d.degreeIdeal ℒ k).liftQ ((Ideal.Quotient.mkₐ R ((𝓕).ideal (k + 1))).toLieHom.comp (ι R))
    fun _ hx => by
      simpa [Ideal.Quotient.eq_zero_iff_mem] using
        ι_mem_degreeFiltration_succ_of_mem_degreeIdeal d ℒ hx

@[simp]
theorem truncatedLieToU_mk (k : ℕ) (x : L) :
    truncatedLieToU d ℒ k (LieSubmodule.Quotient.mk x) =
      Ideal.Quotient.mk ((𝓕).ideal (k + 1)) (ι R x) := by simp [truncatedLieToU]

/-- When `ι : L → U(L)` is injective, every truncated Lie-to-enveloping map is injective. -/
theorem truncatedLieToU_injective (hι : Function.Injective (ι R : L → U)) (k : ℕ) :
    Function.Injective (truncatedLieToU d ℒ k) := by
  rw [truncatedLieToU, LieIdeal.liftQ_injective_iff]
  exact fun _ hx => (comap_degreeFiltration_succ_ι d ℒ hι k).le
    (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hx)

/-- `truncatedLieToU` commutes with transitions between degree cutoffs. -/
theorem factor_truncatedLieToU {k l : ℕ} (h : k ≤ l) (z : d.truncatedLie ℒ l) :
    Ideal.Quotient.factor ((𝓕).antitone (Nat.add_le_add_right h 1)) (truncatedLieToU d ℒ l z) =
      truncatedLieToU d ℒ k (LieIdeal.factor (d.degreeIdeal_antitone ℒ h) z) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ l).surjective_mkQ z; simp [LieIdeal.mkQ_apply]

private noncomputable def completedLieToUFun (x : d.completedLie ℒ) : Û :=
  ⟨fun k => truncatedLieToU d ℒ k.unop
      (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k.unop x),
    ((𝓕).mem_completion_iff _).mpr fun {_ _} h => by
      rw [factor_truncatedLieToU d ℒ h, LieIdeal.factor_completionProjection]⟩

private theorem projection_completedLieToUFun (k : ℕ) (x : d.completedLie ℒ) :
    (𝓕).projection k (completedLieToUFun d ℒ x) = truncatedLieToU d ℒ k
      (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k x) :=
  (𝓕).projection_apply k _

/-- The canonical Lie homomorphism from the completed Lie algebra `d.completedLie ℒ` to
`completedEnveloping`. -/
noncomputable def completedLieToU : d.completedLie ℒ →ₗ⁅R⁆ Û where
  toFun := completedLieToUFun d ℒ
  map_add' _ _ := (𝓕).completion_ext fun _ => by
    simp only [map_add, projection_completedLieToUFun]
  map_smul' _ _ := (𝓕).completion_ext fun _ => by
    rw [RingHom.id_apply, projection_completedLieToUFun, map_smul, map_smul,
      ← (𝓕).projectionₐ_apply (R := R), map_smul, (𝓕).projectionₐ_apply,
      projection_completedLieToUFun]
  map_lie' := (𝓕).completion_ext fun _ => by
    simp [projection_completedLieToUFun, LieRing.of_associative_ring_bracket]

/-- At cutoff `k`, `completedLieToU` applies `truncatedLieToU` to the `k`-th Lie projection. -/
@[simp]
theorem projection_completedLieToU (k : ℕ) (x : d.completedLie ℒ) :
    (𝓕).projection k (completedLieToU d ℒ x) = truncatedLieToU d ℒ k
      (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k x) :=
  projection_completedLieToUFun d ℒ k x

/-- `completedLieToU` extends `ι : L → U(L)` along the two completion maps. -/
@[simp]
theorem completedLieToU_toCompletion (x : L) :
    completedLieToU d ℒ
        (LieIdeal.toCompletion (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) x) =
      (𝓕).toCompletion (ι R x) :=
  (degreeFiltration ℒ d.degree _).completion_ext fun _ => by simp [LieIdeal.mkQ_apply]

/-- Every element in the image of `completedLieToU` lies in the first completion ideal. -/
theorem completedLieToU_mem_completionIdeal_one (x : d.completedLie ℒ) :
    completedLieToU d ℒ x ∈ (𝓕).completionIdeal 1 := by
  rw [AlgFiltration.completionIdeal_succ, RingHom.mem_ker, projection_completedLieToU,
    Subsingleton.elim (LieIdeal.completionProjection _ _ 0 x) 0, map_zero]

/-- When `ι : L → U(L)` is injective, `completedLieToU` is injective. -/
theorem completedLieToU_injective (hι : Function.Injective (ι R : L → U)) :
    Function.Injective (completedLieToU d ℒ) := fun _ _ h =>
  LieIdeal.completion_ext _ _ fun k => truncatedLieToU_injective d ℒ hι k <| by
    simpa only [projection_completedLieToU] using congrArg ((𝓕).projection k) h

/-- Every element in the image of `completedLieToU` is completed primitive. -/
theorem isCompletedPrimitive_completedLieToU (x : d.completedLie ℒ) :
    IsCompletedPrimitive ℒ d.degree (d.eq_bot_of_degree_neg ℒ) (completedLieToU d ℒ x) := by
  rw [isCompletedPrimitive_iff_includeCompletion]
  refine ((𝓕).tensorProduct R 𝓕).completion_ext fun k => ?_
  obtain ⟨y, hy⟩ := (d.degreeIdeal ℒ k).surjective_mkQ
    (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k x)
  have hrep : (𝓕).projection k (completedLieToU d ℒ x) =
      (𝓕).projection k ((𝓕).toCompletion (ι R y)) := by
    simp only [projection_completedLieToU, ← hy, LieIdeal.mkQ_apply, truncatedLieToU_mk,
      AlgFiltration.projection_toCompletion]
  have hprim := (isCompletedPrimitive_iff_includeCompletion ℒ d.degree _).mp
    (isCompletedPrimitive_toCompletion_ι ℒ d.degree (d.eq_bot_of_degree_neg ℒ) y)
  simpa only [projection_completedCoproduct, map_add,
    AlgFiltration.projection_includeLeftCompletion, AlgFiltration.projection_includeRightCompletion,
    hrep] using congrArg (((𝓕).tensorProduct R 𝓕).projection k) hprim

/-! ### Homogeneous components of completed primitive elements -/

private noncomputable def envelopingIdealSubmodule (k : ℕ) : Submodule R U :=
  ((𝓕).ideal (k + 1)).restrictScalars R

private theorem envelopingIdealSubmodule_antitone : Antitone (envelopingIdealSubmodule d ℒ) :=
  fun _ _ h => (degreeFiltration ℒ d.degree _).antitone (Nat.add_le_add_right h 1)

private theorem envelopingIdealSubmodule_eq_degreeSubmodule (k : ℕ) :
    envelopingIdealSubmodule d ℒ k = d.degreeSubmodule (homogeneousSubmodule ℒ) k := by
  ext a; rw [envelopingIdealSubmodule, Submodule.restrictScalars_mem,
    mem_degreeFiltration_ideal_iff, d.mem_degreeSubmodule_iff]
  exact ⟨fun h n hn => h n (by omega), fun h n hn => h n (by omega)⟩

private noncomputable def envelopingQuotEquiv (k : ℕ) :
    (ModuleTower.quotients (envelopingIdealSubmodule d ℒ)
        (envelopingIdealSubmodule_antitone d ℒ)).obj (Opposite.op k) ≃ₗ[R]
      U ⧸ (𝓕).ideal (k + 1) :=
  ModuleTower.quotientsLiftEquiv (envelopingIdealSubmodule d ℒ)
    (envelopingIdealSubmodule_antitone d ℒ) k
    (Ideal.Quotient.mkₐ R ((𝓕).ideal (k + 1))).toLinearMap
    (by ext a; simp [envelopingIdealSubmodule, Ideal.Quotient.eq_zero_iff_mem])
    Ideal.Quotient.mk_surjective

private theorem envelopingQuotEquiv_π (k : ℕ) (a : U) :
    envelopingQuotEquiv d ℒ k (ModuleTower.quotientsπ (envelopingIdealSubmodule d ℒ)
      (envelopingIdealSubmodule_antitone d ℒ) k a) = Ideal.Quotient.mk ((𝓕).ideal (k + 1)) a :=
  ModuleTower.quotientsLiftEquiv_quotientsπ _ _ _ _ _ _ a

private theorem envelopingQuotEquiv_transition {k l : ℕ} (h : k ≤ l)
    (x : (ModuleTower.quotients (envelopingIdealSubmodule d ℒ)
      (envelopingIdealSubmodule_antitone d ℒ)).obj (Opposite.op l)) :
    envelopingQuotEquiv d ℒ k ((ModuleTower.quotients (envelopingIdealSubmodule d ℒ)
      (envelopingIdealSubmodule_antitone d ℒ)).transitionOfLE h x) =
      Ideal.Quotient.factor ((degreeFiltration ℒ d.degree _).antitone (Nat.add_le_add_right h 1))
        (envelopingQuotEquiv d ℒ l x) := by
  obtain ⟨a, rfl⟩ := ModuleTower.quotientsπ_surjective _ _ l x
  rw [ModuleTower.transitionOfLE_quotientsπ, envelopingQuotEquiv_π, envelopingQuotEquiv_π,
    Ideal.Quotient.factor_mk]

private noncomputable def toModuleCompletion :
    Û →ₗ[R]
      (ModuleTower.quotients (envelopingIdealSubmodule d ℒ)
        (envelopingIdealSubmodule_antitone d ℒ)).lim :=
  (ModuleTower.quotients _ _).limLift
    (fun k => (envelopingQuotEquiv d ℒ k).symm.toLinearMap.comp
      ((𝓕).projectionₐ (R := R) k).toLinearMap)
    (fun k => by
      ext u; apply (envelopingQuotEquiv d ℒ k).injective
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        ← ModuleTower.transitionOfLE_succ, envelopingQuotEquiv_transition]; simp)

private theorem limπ_toModuleCompletion (k : ℕ) (u : Û) :
    (ModuleTower.quotients (envelopingIdealSubmodule d ℒ)
      (envelopingIdealSubmodule_antitone d ℒ)).limπ k (toModuleCompletion d ℒ u) =
      (envelopingQuotEquiv d ℒ k).symm ((𝓕).projection k u) := by
  rw [toModuleCompletion, ← LinearMap.comp_apply, ModuleTower.limπ_comp_limLift]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply,
    AlgFiltration.projectionₐ_apply]

/-- The `n`-th homogeneous enveloping component of an element of `completedEnveloping`. -/
noncomputable def envelopingComponent (n : N) : Û →ₗ[R] homogeneousSubmodule ℒ n :=
  (d.completionComponent (homogeneousSubmodule ℒ) (envelopingIdealSubmodule d ℒ)
    (envelopingIdealSubmodule_antitone d ℒ)
    (envelopingIdealSubmodule_eq_degreeSubmodule d ℒ) n).comp (toModuleCompletion d ℒ)

/-- Any representative at a cutoff `k ≥ d.degree n` computes `envelopingComponent`. -/
theorem envelopingComponent_eq_of_representative {n : N} {k : ℕ} (hn : d.degree n ≤ k)
    (u : Û) (a : U) (ha : Ideal.Quotient.mk ((𝓕).ideal (k + 1)) a = (𝓕).projection k u) :
    envelopingComponent d ℒ n u = decompose (homogeneousSubmodule ℒ) a n := by
  have hrep : (ModuleTower.quotients (envelopingIdealSubmodule d ℒ)
      (envelopingIdealSubmodule_antitone d ℒ)).limπ k (toModuleCompletion d ℒ u) =
      ModuleTower.quotientsπ _ (envelopingIdealSubmodule_antitone d ℒ) k a := by
    rw [limπ_toModuleCompletion, ← ha, ← envelopingQuotEquiv_π, LinearEquiv.symm_apply_apply]
  rw [envelopingComponent, LinearMap.comp_apply, d.completionComponent_eq_quotientComponent
    (homogeneousSubmodule ℒ) (envelopingIdealSubmodule d ℒ)
    (envelopingIdealSubmodule_antitone d ℒ) (envelopingIdealSubmodule_eq_degreeSubmodule d ℒ)
    n k hn, hrep, d.quotientComponent_mk]

/-- `envelopingComponent` recovers the ordinary homogeneous components on `toCompletion`. -/
@[simp]
theorem envelopingComponent_toCompletion (n : N) (a : U) :
    envelopingComponent d ℒ n ((𝓕).toCompletion a) =
      decompose (homogeneousSubmodule ℒ) a n :=
  envelopingComponent_eq_of_representative d ℒ (Int.self_le_toNat (d.degree n)) _ a
    ((𝓕).projection_toCompletion _ a).symm

/-- `envelopingComponent` on `completedLieToU` is `ι` applied to the corresponding completed Lie
component. -/
theorem envelopingComponent_completedLieToU (n : N) (x : d.completedLie ℒ) :
    (envelopingComponent d ℒ n (completedLieToU d ℒ x) : U) =
      ι R (d.completionLieEquivPi ℒ x n : L) := by
  classical
  let k := (d.degree n).toNat
  have hk : d.degree n ≤ k := Int.self_le_toNat _
  let y : L := ∑ m ∈ (d.finite_cutoff k).toFinset, (d.completionLieEquivPi ℒ x m : L)
  have hproj : Ideal.Quotient.mk ((𝓕).ideal (k + 1)) (ι R y) =
      (𝓕).projection k (completedLieToU d ℒ x) := by
    rw [projection_completedLieToU, d.completionProjection_eq_mkQ_sum ℒ x k,
      LieIdeal.mkQ_apply, truncatedLieToU_mk]
  rw [envelopingComponent_eq_of_representative d ℒ hk _ (ι R y) hproj,
    ι_apply, coe_decompose_mkAlgHom_ι]
  congr 1
  by_cases hnP : n ∈ d.monoid
  · rw [decompose_sum, _root_.DirectSum.sum_apply, Submodule.coe_sum, Finset.sum_eq_single n]
    · exact decompose_of_mem_same ℒ (d.completionLieEquivPi ℒ x n).property
    · exact fun m _ hmn => decompose_of_mem_ne ℒ (d.completionLieEquivPi ℒ x m).property hmn
    · exact fun h => (h (by simp [hnP, hk])).elim
  · have hbot : ℒ n = ⊥ := IsPositiveGrading.eq_bot (d := d) (ℒ := ℒ) n (Or.inl hnP)
    exact ((Submodule.mem_bot R).mp (hbot ▸ (decompose ℒ y n).property)).trans
      ((Submodule.mem_bot R).mp (hbot ▸ (d.completionLieEquivPi ℒ x n).property)).symm

/-- At cutoff `k`, every element of `completedEnveloping` is represented by the finite sum of its
homogeneous components in `d.cutoff k`. -/
theorem mk_sum_envelopingComponent (k : ℕ) (u : Û) :
    Ideal.Quotient.mk ((𝓕).ideal (k + 1))
        (∑ m ∈ (d.finite_cutoff k).toFinset, (envelopingComponent d ℒ m u : U)) =
      (𝓕).projection k u := by
  have h := congrArg (envelopingQuotEquiv d ℒ k) <| d.projection_eq_sum_completionComponent
    (homogeneousSubmodule ℒ) (envelopingIdealSubmodule d ℒ)
    (envelopingIdealSubmodule_antitone d ℒ) (envelopingIdealSubmodule_eq_degreeSubmodule d ℒ)
    (fun _ hn => homogeneousSubmodule_eq_bot_of_not_mem_monoid ℒ d hn)
    k (toModuleCompletion d ℒ u)
  rw [limπ_toModuleCompletion, LinearEquiv.apply_symm_apply, envelopingQuotEquiv_π] at h
  exact h.symm

private def tensorGrading (p : N × N) : Submodule R (U ⊗[R] U) :=
  Submodule.map₂ (TensorProduct.mk R U U)
    (homogeneousSubmodule ℒ p.1) (homogeneousSubmodule ℒ p.2)

omit [DecidableEq N] [GradedLieAlgebra ℒ] in
private theorem mul_mem_tensorGrading {p q : N × N} {x y : U ⊗[R] U}
    (hx : x ∈ tensorGrading ℒ p) (hy : y ∈ tensorGrading ℒ q) :
    x * y ∈ tensorGrading ℒ (p + q) :=
  ((Submodule.map₂_tmul_mul_le _ _ _ _).trans <| Submodule.map₂_le_map₂
    (GradedAlgebra.mul_le_grade_add (homogeneousSubmodule ℒ) p.1 q.1)
    (GradedAlgebra.mul_le_grade_add (homogeneousSubmodule ℒ) p.2 q.2))
    (Submodule.mul_mem_mul hx hy)

private def tensorTotalDegree (m : N) : Submodule R (U ⊗[R] U) :=
  ⨆ p : {p : N × N // p.1 + p.2 = m}, tensorGrading ℒ p.1

omit [DecidableEq N] [GradedLieAlgebra ℒ] in
private theorem mul_mem_tensorTotalDegree {m₁ m₂ : N} {x y : U ⊗[R] U}
    (hx : x ∈ tensorTotalDegree ℒ m₁) (hy : y ∈ tensorTotalDegree ℒ m₂) :
    x * y ∈ tensorTotalDegree ℒ (m₁ + m₂) := by
  rw [tensorTotalDegree] at hx hy
  refine Submodule.iSup_induction _
    (motive := fun x => x * y ∈ tensorTotalDegree ℒ (m₁ + m₂)) hx
    (fun p x hx => ?_) (by simp) (fun _ _ h₁ h₂ => by simpa [add_mul] using add_mem h₁ h₂)
  refine Submodule.iSup_induction _
    (motive := fun y => x * y ∈ tensorTotalDegree ℒ (m₁ + m₂)) hy
    (fun q y hy => ?_) (by simp) (fun _ _ h₁ h₂ => by simpa [mul_add] using add_mem h₁ h₂)
  refine Submodule.mem_iSup_of_mem ⟨p.1 + q.1, ?_⟩ (mul_mem_tensorGrading ℒ hx hy)
  calc (p.1 + q.1).1 + (p.1 + q.1).2 = (p.1.1 + p.1.2) + (q.1.1 + q.1.2) := add_add_add_comm _ _ _ _
    _ = m₁ + m₂ := by rw [p.2, q.2]

omit [DecidableEq N] [GradedLieAlgebra ℒ] in
private theorem comul_mem_tensorTotalDegree {m : N} {a : U}
    (ha : a ∈ homogeneousSubmodule ℒ m) :
    Coalgebra.comul (R := R) a ∈ tensorTotalDegree ℒ m := by
  have hle : homogeneousSubmodule ℒ m ≤
      (tensorTotalDegree ℒ m).comap (Bialgebra.comulAlgHom R U).toLinearMap := by
    clear ha a
    refine (homogeneousSubmodule_le_iff ℒ m _).mpr fun l hl => ?_
    rw [Submodule.mem_comap, AlgHom.toLinearMap_apply]; subst m
    induction l with
    | nil =>
      simp only [List.map_nil, List.prod_nil, List.sum_nil, map_one, Algebra.TensorProduct.one_def]
      exact Submodule.mem_iSup_of_mem ⟨(0, 0), add_zero 0⟩ (Submodule.apply_mem_map₂
        (TensorProduct.mk R U U) (SetLike.one_mem_graded _) (SetLike.one_mem_graded _))
    | cons b l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, map_mul]
      refine mul_mem_tensorTotalDegree ℒ ?_ ih
      rw [Bialgebra.comulAlgHom_apply, comul_ι]
      exact add_mem
        (Submodule.mem_iSup_of_mem ⟨(b.1, 0), add_zero b.1⟩ (Submodule.apply_mem_map₂ _
          (ι_mem_homogeneousSubmodule ℒ b.2.property) (SetLike.one_mem_graded _)))
        (Submodule.mem_iSup_of_mem ⟨(0, b.1), zero_add b.1⟩ (Submodule.apply_mem_map₂ _
          (SetLike.one_mem_graded _) (ι_mem_homogeneousSubmodule ℒ b.2.property)))
  exact hle ha

omit [DecidableEq N] [GradedLieAlgebra ℒ] in
private theorem primDefect_mem_tensorTotalDegree {m : N} {a : U}
    (ha : a ∈ homogeneousSubmodule ℒ m) :
    Coalgebra.comul (R := R) a - (1 ⊗ₜ[R] a + a ⊗ₜ[R] 1) ∈ tensorTotalDegree ℒ m :=
  sub_mem (comul_mem_tensorTotalDegree ℒ ha) (add_mem
    (Submodule.mem_iSup_of_mem ⟨(0, m), zero_add m⟩
      (Submodule.apply_mem_map₂ _ (SetLike.one_mem_graded _) ha))
    (Submodule.mem_iSup_of_mem ⟨(m, 0), add_zero m⟩
      (Submodule.apply_mem_map₂ _ ha (SetLike.one_mem_graded _))))

omit [GradedLieAlgebra ℒ] in
private noncomputable def tensorComponentKer
    [_root_.DirectSum.Decomposition (tensorGrading ℒ)] (p : N × N) : Submodule R (U ⊗[R] U) :=
  LinearMap.ker (homogeneousComponent (tensorGrading ℒ) p)

omit [GradedLieAlgebra ℒ] in
private theorem mem_tensorComponentKer
    [_root_.DirectSum.Decomposition (tensorGrading ℒ)] {p : N × N} {z : U ⊗[R] U} :
    z ∈ tensorComponentKer ℒ p ↔ (decompose (tensorGrading ℒ) z p : U ⊗[R] U) = 0 := by
  simp [tensorComponentKer]

omit [GradedLieAlgebra ℒ] in
private theorem decompose_eq_zero_of_mem_tensorTotalDegree
    [_root_.DirectSum.Decomposition (tensorGrading ℒ)] {m : N} {z : U ⊗[R] U}
    (hz : z ∈ tensorTotalDegree ℒ m) {p : N × N} (hp : p.1 + p.2 ≠ m) :
    (decompose (tensorGrading ℒ) z p : U ⊗[R] U) = 0 :=
  (mem_tensorComponentKer ℒ).mp <| (iSup_le fun q _ hw => (mem_tensorComponentKer ℒ).mpr <|
    decompose_of_mem_ne (tensorGrading ℒ) hw fun h => hp (h ▸ q.2) :
      tensorTotalDegree ℒ m ≤ tensorComponentKer ℒ p) hz

private theorem decompose_eq_zero_of_mem_tensorProduct_ideal
    [_root_.DirectSum.Decomposition (tensorGrading ℒ)] {k : ℕ} {t : U ⊗[R] U}
    (ht : t ∈ ((𝓕).tensorProduct R 𝓕).ideal (k + 1))
    {p : N × N} (hp : d.degree p.1 + d.degree p.2 ≤ k) :
    (decompose (tensorGrading ℒ) t p : U ⊗[R] U) = 0 := by
  refine (mem_tensorComponentKer ℒ).mp <| (?_ : tensorFiltrationTail
      (fun n => ((𝓕).ideal n).restrictScalars R)
      (fun n => ((𝓕).ideal n).restrictScalars R) (k + 1) ≤
      tensorComponentKer ℒ p) (((𝓕).mem_tensorProduct_ideal_iff R 𝓕).mp ht)
  rw [tensorFiltrationTail_def]
  refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
  simp only [degreeFiltration_ideal, GradedAlgebra.degreeIdeal_restrictScalars,
    DirectSum.degreeTail_def, Submodule.map₂_iSup_left, Submodule.map₂_iSup_right, iSup_le_iff,
    Submodule.map₂_le]
  intro j hj i hi x hx y hy
  refine (mem_tensorComponentKer ℒ).mpr <| decompose_of_mem_ne (tensorGrading ℒ)
    (i := (i, j)) (Submodule.apply_mem_map₂ (TensorProduct.mk R U U) hx hy) fun heq => ?_
  rcases Prod.ext_iff.mp heq with ⟨rfl, rfl⟩; omega

private theorem isPrimitiveElem_envelopingComponent_of_mem_monoid {u : Û}
    (hu : IsCompletedPrimitive ℒ d.degree (d.eq_bot_of_degree_neg ℒ) u)
    {n : N} (hnP : n ∈ d.monoid) :
    Bialgebra.IsPrimitiveElem R (envelopingComponent d ℒ n u : U) := by
  classical
  let k := (d.degree n).toNat
  let s := (d.finite_cutoff k).toFinset
  let _ : _root_.DirectSum.Decomposition (tensorGrading ℒ) :=
    (_root_.DirectSum.IsInternal.tensorProduct _ _
      (isInternal_homogeneousSubmodule ℒ)
      (isInternal_homogeneousSubmodule ℒ)).chooseDecomposition
  have hmem := hu.comul_sub_mem_tensorProduct_ideal (mk_sum_envelopingComponent d ℒ k u)
  let δ : U →ₗ[R] U ⊗[R] U :=
    Coalgebra.comul - ((TensorProduct.mk R U U 1) + (TensorProduct.mk R U U).flip 1)
  have hδ (b : U) :
      δ b = Coalgebra.comul (R := R) b - (1 ⊗ₜ[R] b + b ⊗ₜ[R] 1) := by simp [δ]
  refine Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul.mpr (sub_eq_zero.mp ?_)
  apply (decomposeLinearEquiv (tensorGrading ℒ)).injective; rw [map_zero]; ext p
  simp only [_root_.DirectSum.decomposeLinearEquiv_apply, _root_.DirectSum.zero_apply,
    ZeroMemClass.coe_zero]
  by_cases hpn : p.1 + p.2 = n
  · have hpk : d.degree p.1 + d.degree p.2 ≤ k := by
      rw [← map_add, hpn]; exact Int.self_le_toNat _
    have h0 := decompose_eq_zero_of_mem_tensorProduct_ideal d ℒ hmem hpk
    rw [← hδ _, map_sum δ _ s, decompose_sum, _root_.DirectSum.sum_apply,
      Submodule.coe_sum, Finset.sum_eq_single n] at h0
    · rwa [hδ] at h0
    · exact fun m _ hmn => by
        rw [hδ]; exact decompose_eq_zero_of_mem_tensorTotalDegree ℒ
          (primDefect_mem_tensorTotalDegree ℒ (envelopingComponent d ℒ m u).property)
          (hpn.trans_ne hmn.symm)
    · exact fun hns => (hns (by simp [s, k, hnP])).elim
  · exact decompose_eq_zero_of_mem_tensorTotalDegree ℒ
      (primDefect_mem_tensorTotalDegree ℒ (envelopingComponent d ℒ n u).property) hpn

/-- Every homogeneous enveloping component of a completed primitive element is an ordinary
primitive element of `U(L)`. -/
theorem isPrimitiveElem_envelopingComponent {u : Û}
    (hu : IsCompletedPrimitive ℒ d.degree (d.eq_bot_of_degree_neg ℒ) u) (n : N) :
    Bialgebra.IsPrimitiveElem R (envelopingComponent d ℒ n u : U) := by
  by_cases hnP : n ∈ d.monoid
  · exact isPrimitiveElem_envelopingComponent_of_mem_monoid d ℒ hu hnP
  · have hc0 : (envelopingComponent d ℒ n u : U) = 0 := (Submodule.mem_bot R).mp <|
      homogeneousSubmodule_eq_bot_of_not_mem_monoid ℒ d hnP ▸
        (envelopingComponent d ℒ n u).property
    rw [hc0]; exact (Coalgebra.skewPrimitive R (1 : U) 1).zero_mem

end CommRing

/-! ### Identification of completed primitive elements over `ℚ`-algebras -/

section Rational

universe u v

variable {N : Type u} {R : Type} {L : Type v} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "Û" => completedEnveloping ℒ d.degree (d.eq_bot_of_degree_neg ℒ)
local notation "𝓕" => degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)

/-- Over a commutative `ℚ`-algebra `R : Type`, `completedLieToU` is injective without a freeness
hypothesis. -/
theorem completedLieToU_injective_of_algebra_rat : Function.Injective (completedLieToU d ℒ) :=
  completedLieToU_injective d ℒ (ι_injective_of_algebra_rat R L)

/-- Over a commutative `ℚ`-algebra `R : Type`, an element of `completedEnveloping` is completed
primitive if and only if it lies in the image of `completedLieToU`. -/
theorem isCompletedPrimitive_iff_mem_range_completedLieToU (u : Û) :
    IsCompletedPrimitive ℒ d.degree (d.eq_bot_of_degree_neg ℒ) u ↔
      u ∈ Set.range (completedLieToU d ℒ) := by
  refine ⟨fun hu => ?_, ?_⟩
  · let _ := d.lieRingPi ℒ; let _ := d.lieAlgebraPi ℒ
    let y : N → L := fun n => (primitiveEquiv R L).symm
      ⟨(envelopingComponent d ℒ n u : U), isPrimitiveElem_envelopingComponent d ℒ hu n⟩
    let x : ∀ n, ℒ n := fun n => decompose ℒ (y n) n
    have hx (n : N) : ι R (x n : L) = (envelopingComponent d ℒ n u : U) := by
      have hy : ι R (y n) = (envelopingComponent d ℒ n u : U) := ι_primitiveEquiv_symm R L _
      calc ι R (x n : L)
          = (decompose (homogeneousSubmodule ℒ) (ι R (y n)) n : U) := by
              rw [ι_apply (R := R) (x := y n), coe_decompose_mkAlgHom_ι]
        _ = (decompose (homogeneousSubmodule ℒ) (envelopingComponent d ℒ n u : U) n : U) := by
              rw [hy]
        _ = (envelopingComponent d ℒ n u : U) :=
              decompose_of_mem_same _ (envelopingComponent d ℒ n u).property
    refine ⟨(d.completionLieEquivPi ℒ).symm x, (𝓕).completion_ext fun k => ?_⟩
    rw [projection_completedLieToU, d.completionProjection_completionLieEquivPi_symm ℒ x k,
      LieIdeal.mkQ_apply, truncatedLieToU_mk, map_sum]
    simp_rw [hx]; exact mk_sum_envelopingComponent d ℒ k u
  · rintro ⟨x, rfl⟩; exact isCompletedPrimitive_completedLieToU d ℒ x

/-- Over a commutative `ℚ`-algebra `R : Type`, `completedLieToU` identifies `d.completedLie ℒ`
with the Lie subalgebra of completed primitive elements in `completedEnveloping`. -/
noncomputable def completedPrimitiveLieEquiv :
    d.completedLie ℒ ≃ₗ⁅R⁆
      completedPrimitiveLieSubalgebra ℒ d.degree (d.eq_bot_of_degree_neg ℒ) :=
  LieEquiv.ofBijective
    { toLinearMap := (completedLieToU d ℒ).toLinearMap.codRestrict
        (completedPrimitiveLieSubalgebra ℒ d.degree (d.eq_bot_of_degree_neg ℒ)).toSubmodule
        fun x => (mem_completedPrimitiveLieSubalgebra_iff _ _ _).mpr
          (isCompletedPrimitive_completedLieToU d ℒ x)
      map_lie' := fun {x y} => Subtype.ext ((completedLieToU d ℒ).map_lie x y) }
    ⟨fun _ _ h => completedLieToU_injective_of_algebra_rat d ℒ (congrArg Subtype.val h),
      fun u => by
        obtain ⟨x, hx⟩ := (isCompletedPrimitive_iff_mem_range_completedLieToU d ℒ u.1).mp
          ((mem_completedPrimitiveLieSubalgebra_iff _ _ _).mp u.2)
        exact ⟨x, Subtype.ext hx⟩⟩

@[simp]
theorem coe_completedPrimitiveLieEquiv_apply (x : d.completedLie ℒ) :
    (completedPrimitiveLieEquiv d ℒ x : Û) = completedLieToU d ℒ x := (rfl)

@[simp]
theorem completedLieToU_completedPrimitiveLieEquiv_symm
    (u : completedPrimitiveLieSubalgebra ℒ d.degree (d.eq_bot_of_degree_neg ℒ)) :
    completedLieToU d ℒ ((completedPrimitiveLieEquiv d ℒ).symm u) = (u : Û) :=
  congrArg Subtype.val ((completedPrimitiveLieEquiv d ℒ).apply_symm_apply u)

/-- Over a commutative `ℚ`-algebra `R : Type`, `completedExp ∘ completedLieToU` identifies
`d.completedLie ℒ` with the completed grouplike elements of `completedEnveloping`. -/
noncomputable def completedLieExpEquiv :
    d.completedLie ℒ ≃
      {u : Û // IsCompletedGroupLike ℒ d.degree (d.eq_bot_of_degree_neg ℒ) u} :=
  (completedPrimitiveLieEquiv d ℒ).toLinearEquiv.toEquiv.trans
    (completedPrimitiveExpEquiv ℒ d.degree (d.eq_bot_of_degree_nonpos ℒ))

@[simp]
theorem coe_completedLieExpEquiv_apply (x : d.completedLie ℒ) :
    (completedLieExpEquiv d ℒ x : Û) =
      (𝓕).completedExp
        ⟨completedLieToU d ℒ x, completedLieToU_mem_completionIdeal_one d ℒ x⟩ :=
  coe_completedPrimitiveExpEquiv ℒ d.degree (d.eq_bot_of_degree_nonpos ℒ) _

@[simp]
theorem completedLieToU_completedLieExpEquiv_symm
    (u : {u : Û // IsCompletedGroupLike ℒ d.degree (d.eq_bot_of_degree_neg ℒ) u}) :
    completedLieToU d ℒ ((completedLieExpEquiv d ℒ).symm u) =
      (𝓕).completedLog
        ⟨u.1, u.2.sub_one_mem_completionIdeal_one (d.eq_bot_of_degree_nonpos ℒ)⟩ :=
  (completedLieToU_completedPrimitiveLieEquiv_symm d ℒ _).trans
    (coe_completedPrimitiveExpEquiv_symm ℒ d.degree (d.eq_bot_of_degree_nonpos ℒ) u)

end Rational

end TauCeti.UniversalEnvelopingAlgebra
