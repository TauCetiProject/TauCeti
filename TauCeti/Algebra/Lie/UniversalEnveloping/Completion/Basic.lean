/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Graded.Completion
public import TauCeti.Algebra.Lie.UniversalEnveloping.Truncation
public import TauCeti.RingTheory.FilteredAlgebra.Algebra

/-!
# Completions of graded universal enveloping algebras

For a Lie algebra `L` over a commutative ring `R` graded by `Γ` with degree functional
`d : Γ →+ ℤ` and no negative-degree components, `completedEnveloping` is the completion of
`U(L)` along `TauCeti.UniversalEnvelopingAlgebra.degreeFiltration`. When the grading is positive
(`d : PositiveDegrees N`), `ι : L → U(L)` descends to a completed Lie map
`completedLieToU : d.completedLie ℒ →ₗ⁅R⁆ Û`, while `envelopingComponent` extracts homogeneous
components from `completedEnveloping`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter II, §6.
* J.-P. Serre, *Lie Algebras and Lie Groups*, Part I, Chapter IV.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra
open _root_.DirectSum (decompose decompose_sum decompose_of_mem_same decompose_of_mem_ne)

section Nonneg

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L) (d : Γ →+ ℤ)

variable [DecidableEq Γ] [GradedLieAlgebra ℒ]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "𝓕" => degreeFiltration ℒ d

/-- The completion of a graded universal enveloping algebra along its total-degree filtration. -/
noncomputable abbrev completedEnveloping (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :=
  (𝓕 hneg).completion

/-- For a strictly positive Lie grading, canonical Lie generators map into the first completion
ideal. -/
theorem toCompletion_ι_mem_completionIdeal_one (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) (x : L) :
    (𝓕 (fun n hn => hpos n hn.le)).toCompletion (ι R x) ∈
      (𝓕 (fun n hn => hpos n hn.le)).completionIdeal 1 :=
  ((𝓕 _).toCompletion_mem_completionIdeal_iff 1 _).mpr (ι_mem_degreeFiltration_one ℒ d hpos x)

end Nonneg

section Positive

variable {N R L : Type*} [AddCommMonoid N] [CommRing R] [LieRing L] [LieAlgebra R L]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "Û" => completedEnveloping ℒ d.degree (d.eq_bot_of_degree_neg ℒ)
local notation "𝓕" => degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)

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
  map_add' _ _ := (𝓕).completion_ext fun _ => by simp only [map_add, projection_completedLieToUFun]
  map_smul' r x := (𝓕).completion_ext fun k => by
    have h := map_smul ((𝓕).projectionₐ (R := R) k) r (completedLieToUFun d ℒ x)
    simp only [AlgFiltration.projectionₐ_apply] at h
    simp only [RingHom.id_apply, projection_completedLieToUFun, map_smul, h]
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
    completedLieToU d ℒ (LieIdeal.toCompletion (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) x) =
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

/-! ### Homogeneous components in `completedEnveloping` -/

private noncomputable def envelopingIdealSubmodule (k : ℕ) : Submodule R U :=
  ((𝓕).ideal (k + 1)).restrictScalars R

local notation "𝔈" => envelopingIdealSubmodule d ℒ

private theorem envelopingIdealSubmodule_antitone : Antitone (𝔈) :=
  fun _ _ h => (degreeFiltration ℒ d.degree _).antitone (Nat.add_le_add_right h 1)

private theorem envelopingIdealSubmodule_eq_degreeSubmodule (k : ℕ) :
    𝔈 k = d.degreeSubmodule (homogeneousSubmodule ℒ) k := by
  ext a; simp only [envelopingIdealSubmodule, Submodule.restrictScalars_mem,
    mem_degreeFiltration_ideal_iff, d.mem_degreeSubmodule_iff]
  exact ⟨fun h n hn => h n (by omega), fun h n hn => h n (by omega)⟩

private noncomputable def envelopingQuotEquiv (k : ℕ) :
    (ModuleTower.quotients (𝔈) (envelopingIdealSubmodule_antitone d ℒ)).obj (Opposite.op k) ≃ₗ[R]
      U ⧸ (𝓕).ideal (k + 1) :=
  ModuleTower.quotientsLiftEquiv (𝔈) (envelopingIdealSubmodule_antitone d ℒ) k
    (Ideal.Quotient.mkₐ R ((𝓕).ideal (k + 1))).toLinearMap
    (by ext a; simp [envelopingIdealSubmodule, Ideal.Quotient.eq_zero_iff_mem])
    Ideal.Quotient.mk_surjective

private theorem envelopingQuotEquiv_π (k : ℕ) (a : U) :
    envelopingQuotEquiv d ℒ k
        (ModuleTower.quotientsπ (𝔈) (envelopingIdealSubmodule_antitone d ℒ) k a) =
      Ideal.Quotient.mk ((𝓕).ideal (k + 1)) a :=
  ModuleTower.quotientsLiftEquiv_quotientsπ _ _ _ _ _ _ a

private noncomputable def toModuleCompletion :
    Û →ₗ[R] (ModuleTower.quotients (𝔈) (envelopingIdealSubmodule_antitone d ℒ)).lim :=
  (ModuleTower.quotients _ _).limLift (fun k => (envelopingQuotEquiv d ℒ k).symm.toLinearMap.comp
      ((𝓕).projectionₐ (R := R) k).toLinearMap) fun k => by
    ext u; apply (envelopingQuotEquiv d ℒ k).injective
    obtain ⟨a, ha⟩ := ModuleTower.quotientsπ_surjective (𝔈) (envelopingIdealSubmodule_antitone d ℒ)
      (k + 1) ((envelopingQuotEquiv d ℒ (k + 1)).symm ((𝓕).projection (k + 1) u))
    have hfa : Ideal.Quotient.mk ((𝓕).ideal (k + 1 + 1)) a = (𝓕).projection (k + 1) u := by
      rw [← envelopingQuotEquiv_π, ha, LinearEquiv.apply_symm_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply,
      AlgFiltration.projectionₐ_apply, LinearEquiv.apply_symm_apply]
    rw [← ModuleTower.transitionOfLE_succ, ← ha, ModuleTower.transitionOfLE_quotientsπ,
      envelopingQuotEquiv_π, ← AlgFiltration.factor_projection (𝓕) (Nat.le_succ k) u, ← hfa,
      Ideal.Quotient.factor_mk]

private theorem limπ_toModuleCompletion (k : ℕ) (u : Û) :
    (ModuleTower.quotients (𝔈) (envelopingIdealSubmodule_antitone d ℒ)).limπ k
        (toModuleCompletion d ℒ u) = (envelopingQuotEquiv d ℒ k).symm ((𝓕).projection k u) := by
  rw [toModuleCompletion, ← LinearMap.comp_apply, ModuleTower.limπ_comp_limLift]
  simp [AlgFiltration.projectionₐ_apply]

/-- The `n`-th homogeneous enveloping component of an element of `completedEnveloping`. -/
noncomputable def envelopingComponent (n : N) : Û →ₗ[R] homogeneousSubmodule ℒ n :=
  (d.completionComponent (homogeneousSubmodule ℒ) (𝔈) (envelopingIdealSubmodule_antitone d ℒ)
    (envelopingIdealSubmodule_eq_degreeSubmodule d ℒ) n).comp (toModuleCompletion d ℒ)

/-- Any representative at a cutoff `k ≥ d.degree n` computes `envelopingComponent`. -/
theorem envelopingComponent_eq_of_representative {n : N} {k : ℕ} (hn : d.degree n ≤ k)
    (u : Û) (a : U) (ha : Ideal.Quotient.mk ((𝓕).ideal (k + 1)) a = (𝓕).projection k u) :
    envelopingComponent d ℒ n u = decompose (homogeneousSubmodule ℒ) a n := by
  have hrep : (ModuleTower.quotients (𝔈) (envelopingIdealSubmodule_antitone d ℒ)).limπ k
      (toModuleCompletion d ℒ u) =
      ModuleTower.quotientsπ _ (envelopingIdealSubmodule_antitone d ℒ) k a := by
    rw [limπ_toModuleCompletion, ← ha, ← envelopingQuotEquiv_π, LinearEquiv.symm_apply_apply]
  rw [envelopingComponent, LinearMap.comp_apply, d.completionComponent_eq_quotientComponent
    (homogeneousSubmodule ℒ) (𝔈) (envelopingIdealSubmodule_antitone d ℒ)
    (envelopingIdealSubmodule_eq_degreeSubmodule d ℒ) n k hn, hrep, d.quotientComponent_mk]

/-- `envelopingComponent` recovers the ordinary homogeneous components on `toCompletion`. -/
@[simp]
theorem envelopingComponent_toCompletion (n : N) (a : U) :
    envelopingComponent d ℒ n ((𝓕).toCompletion a) = decompose (homogeneousSubmodule ℒ) a n :=
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
    (homogeneousSubmodule ℒ) (𝔈) (envelopingIdealSubmodule_antitone d ℒ)
    (envelopingIdealSubmodule_eq_degreeSubmodule d ℒ)
    (fun _ hn => homogeneousSubmodule_eq_bot_of_notMem_monoid ℒ d hn) k (toModuleCompletion d ℒ u)
  rw [limπ_toModuleCompletion, LinearEquiv.apply_symm_apply, envelopingQuotEquiv_π] at h
  exact h.symm

end Positive

end TauCeti.UniversalEnvelopingAlgebra
