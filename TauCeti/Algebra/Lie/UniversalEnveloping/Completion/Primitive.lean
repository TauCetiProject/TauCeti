/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Completion.Bialgebra

import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Symmetrization.Injective
import TauCeti.Algebra.Lie.UniversalEnveloping.Primitive

/-!
# Completed primitive elements of positively graded universal enveloping algebras

Let `L` be a Lie algebra over a commutative ring `R` equipped with a positive grading `ℒ` by
`d : PositiveDegrees N`. Every element in the image of `completedLieToU` is completed primitive,
and every homogeneous component of a completed primitive element in `completedEnveloping` is an
ordinary primitive element of `U(L)`. Over a commutative `ℚ`-algebra `R`, this identifies
`completedPrimitiveLieSubalgebra` with `d.completedLie ℒ` (`completedPrimitiveLieEquiv`).

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

/-- Every element in the image of `completedLieToU` is completed primitive. -/
theorem isCompletedPrimitive_completedLieToU (x : d.completedLie ℒ) :
    IsCompletedPrimitive ℒ d.degree (d.eq_bot_of_degree_neg ℒ) (completedLieToU d ℒ x) := by
  rw [isCompletedPrimitive_iff_includeLeftCompletion_add_includeRightCompletion]
  refine ((𝓕).tensorProduct R 𝓕).completion_ext fun k => ?_
  obtain ⟨y, hy⟩ := (d.degreeIdeal ℒ k).surjective_mkQ
    (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k x)
  have hrep : (𝓕).projection k (completedLieToU d ℒ x) =
      (𝓕).projection k ((𝓕).toCompletion (ι R y)) := by
    simp only [projection_completedLieToU, ← hy, LieIdeal.mkQ_apply, truncatedLieToU_mk,
      AlgFiltration.projection_toCompletion]
  have hprim := (isCompletedPrimitive_iff_includeLeftCompletion_add_includeRightCompletion
      ℒ d.degree _).mp
    (isCompletedPrimitive_toCompletion_ι ℒ d.degree (d.eq_bot_of_degree_neg ℒ) y)
  simpa only [projection_completedCoproduct, map_add,
    AlgFiltration.projection_includeLeftCompletion, AlgFiltration.projection_includeRightCompletion,
    hrep] using congrArg (((𝓕).tensorProduct R 𝓕).projection k) hprim

private theorem isPrimitiveElem_envelopingComponent_of_mem_monoid {u : Û}
    (hu : IsCompletedPrimitive ℒ d.degree (d.eq_bot_of_degree_neg ℒ) u) {n : N}
    (hnP : n ∈ d.monoid) : Bialgebra.IsPrimitiveElem R (envelopingComponent d ℒ n u : U) := by
  classical
  let k := (d.degree n).toNat
  let s := (d.finite_cutoff k).toFinset
  let _ : _root_.DirectSum.Decomposition (tensorGrading ℒ) :=
    (isInternal_tensorGrading ℒ).chooseDecomposition
  have hmem := hu.comul_sub_mem_tensorProduct_ideal (mk_sum_envelopingComponent d ℒ k u)
  let δ : U →ₗ[R] U ⊗[R] U :=
    Coalgebra.comul - ((TensorProduct.mk R U U 1) + (TensorProduct.mk R U U).flip 1)
  have hδ (b : U) : δ b = Coalgebra.comul (R := R) b - (1 ⊗ₜ[R] b + b ⊗ₜ[R] 1) := by simp [δ]
  refine Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul.mpr (sub_eq_zero.mp ?_)
  apply (decomposeLinearEquiv (tensorGrading ℒ)).injective; rw [map_zero]; ext p
  simp only [_root_.DirectSum.decomposeLinearEquiv_apply, _root_.DirectSum.zero_apply,
    ZeroMemClass.coe_zero]
  by_cases hpn : p.1 + p.2 = n
  · have hpk : d.degree p.1 + d.degree p.2 < (k + 1 : ℕ) := by
      rw [← map_add, hpn]; have := Int.self_le_toNat (d.degree n); omega
    have h0 := decompose_eq_zero_of_mem_tensorProduct_ideal ℒ d.degree _ hmem hpk
    rw [← hδ _, map_sum δ _ s, decompose_sum, _root_.DirectSum.sum_apply, Submodule.coe_sum,
      Finset.sum_eq_single n] at h0
    · rwa [hδ] at h0
    · intro m _ hmn; rw [hδ]
      exact decompose_eq_zero_of_mem_tensorTotalDegree ℒ
        (comul_sub_tmul_add_tmul_mem_tensorTotalDegree ℒ (envelopingComponent d ℒ m u).property)
        (hpn.trans_ne hmn.symm)
    · exact fun hns => (hns (by simp [s, k, hnP])).elim
  · exact decompose_eq_zero_of_mem_tensorTotalDegree ℒ
      (comul_sub_tmul_add_tmul_mem_tensorTotalDegree ℒ (envelopingComponent d ℒ n u).property) hpn

/-- Every homogeneous enveloping component of a completed primitive element is an ordinary
primitive element of `U(L)`. -/
theorem isPrimitiveElem_envelopingComponent {u : Û}
    (hu : IsCompletedPrimitive ℒ d.degree (d.eq_bot_of_degree_neg ℒ) u) (n : N) :
    Bialgebra.IsPrimitiveElem R (envelopingComponent d ℒ n u : U) := by
  by_cases hnP : n ∈ d.monoid
  · exact isPrimitiveElem_envelopingComponent_of_mem_monoid d ℒ hu hnP
  · have hc0 : (envelopingComponent d ℒ n u : U) = 0 := (Submodule.mem_bot R).mp <|
      homogeneousSubmodule_eq_bot_of_notMem_monoid ℒ d hnP ▸ (envelopingComponent d ℒ n u).property
    rw [hc0]; exact (Coalgebra.skewPrimitive R (1 : U) 1).zero_mem

end CommRing

/-! ### Identification of completed primitive elements over `ℚ`-algebras -/

section Rational

variable {N R L : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "Û" => completedEnveloping ℒ d.degree (d.eq_bot_of_degree_neg ℒ)
local notation "𝓕" => degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)

/-- Over a commutative `ℚ`-algebra `R`, `completedLieToU` is injective without a freeness
hypothesis. -/
theorem completedLieToU_injective_of_algebra_rat : Function.Injective (completedLieToU d ℒ) :=
  completedLieToU_injective d ℒ (ι_injective_of_algebra_rat R L)

/-- Over a commutative `ℚ`-algebra `R`, an element of `completedEnveloping` is completed
primitive if and only if it lies in the image of `completedLieToU`. -/
theorem isCompletedPrimitive_iff_mem_range_completedLieToU (u : Û) :
    IsCompletedPrimitive ℒ d.degree (d.eq_bot_of_degree_neg ℒ) u ↔
      u ∈ Set.range (completedLieToU d ℒ) := by
  refine ⟨fun hu => ?_, fun ⟨x, hx⟩ => hx ▸ isCompletedPrimitive_completedLieToU d ℒ x⟩
  let _ := d.lieRingPi ℒ; let _ := d.lieAlgebraPi ℒ
  let y : N → L := fun n => (primitiveEquiv R L).symm
    ⟨(envelopingComponent d ℒ n u : U), isPrimitiveElem_envelopingComponent d ℒ hu n⟩
  let x : ∀ n, ℒ n := fun n => decompose ℒ (y n) n
  have hx (n : N) : ι R (x n : L) = (envelopingComponent d ℒ n u : U) := by
    have hy : ι R (y n) = (envelopingComponent d ℒ n u : U) := ι_primitiveEquiv_symm R L _
    rw [← coe_decompose_mkAlgHom_ι, ← ι_apply (R := R) (x := y n), hy]
    exact decompose_of_mem_same _ (envelopingComponent d ℒ n u).property
  refine ⟨(d.completionLieEquivPi ℒ).symm x, (𝓕).completion_ext fun k => ?_⟩
  rw [projection_completedLieToU, d.completionProjection_completionLieEquivPi_symm ℒ x k,
    LieIdeal.mkQ_apply, truncatedLieToU_mk, map_sum]
  simp_rw [hx]; exact mk_sum_envelopingComponent d ℒ k u

/-- Over a commutative `ℚ`-algebra `R`, `completedLieToU` identifies `d.completedLie ℒ`
with the Lie subalgebra of completed primitive elements in `completedEnveloping`. -/
noncomputable def completedPrimitiveLieEquiv :
    d.completedLie ℒ ≃ₗ⁅R⁆
      completedPrimitiveLieSubalgebra ℒ d.degree (d.eq_bot_of_degree_neg ℒ) :=
  (LieEquiv.ofInjective (completedLieToU d ℒ) (completedLieToU_injective_of_algebra_rat d ℒ)).trans
    (LieEquiv.ofEq _ _ <| by
      ext u
      simp only [SetLike.mem_coe, LieHom.mem_range, mem_completedPrimitiveLieSubalgebra_iff]
      exact (isCompletedPrimitive_iff_mem_range_completedLieToU d ℒ u).symm)

@[simp]
theorem coe_completedPrimitiveLieEquiv_apply (x : d.completedLie ℒ) :
    (completedPrimitiveLieEquiv d ℒ x : Û) = completedLieToU d ℒ x := by
  simp [completedPrimitiveLieEquiv]

@[simp]
theorem completedLieToU_completedPrimitiveLieEquiv_symm
    (u : completedPrimitiveLieSubalgebra ℒ d.degree (d.eq_bot_of_degree_neg ℒ)) :
    completedLieToU d ℒ ((completedPrimitiveLieEquiv d ℒ).symm u) = (u : Û) :=
  congrArg Subtype.val ((completedPrimitiveLieEquiv d ℒ).apply_symm_apply u)

end Rational

end TauCeti.UniversalEnvelopingAlgebra
