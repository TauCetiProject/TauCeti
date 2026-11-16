/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Completion.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Primitive

import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Completed primitive elements of positively graded universal enveloping algebras

For a positively graded Lie algebra `L` over a commutative ring `R` with enveloping degree
filtration `F` on `U(L)`, every completed primitive element of `F.completion` has primitive
homogeneous components at each cutoff (`isPrimitiveElem_decompose_of_isCompletedPrimitive`). Over a
commutative `ℚ`-algebra `R : Type`, `UniversalEnvelopingAlgebra.isPrimitiveElem_iff_mem_range_ι` and
`PositiveDegrees.completionLieEquivPi` show that `completedLieToU` identifies `d.completedLie ℒ`
with `completedPrimitives ℒ d.degree hneg` without any freeness or finite-generation assumption.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.completedLieToPrimitives`: the completed Lie homomorphism
  landing in `completedPrimitives ℒ d.degree hneg`.
* `TauCeti.UniversalEnvelopingAlgebra.completedPrimitiveLieEquiv`: over a commutative `ℚ`-algebra
  `R : Type`, the Lie equivalence `d.completedLie ℒ ≃ₗ⁅R⁆ completedPrimitives ℒ d.degree hneg`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.ι_injective_of_ratAlgebra`: over a commutative `ℚ`-algebra
  `R : Type`, `ι R : L → U(L)` is injective without module freeness.
* `TauCeti.UniversalEnvelopingAlgebra.isPrimitiveElem_decompose_of_isCompletedPrimitive`: every
  homogeneous component extracted from a completed primitive element is primitive in `U(L)`.
* `TauCeti.UniversalEnvelopingAlgebra.isCompletedPrimitive_iff_mem_range_completedLieToU`: over a
  commutative `ℚ`-algebra `R : Type`, completed primitives are the range of `completedLieToU`.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

section Injectivity

universe v

variable (R : Type) (L : Type v) [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]

/-- Over a commutative `ℚ`-algebra `R : Type`, `ι R : L → U(L)` is injective without any freeness
or flatness hypothesis on `L`. -/
theorem ι_injective_of_ratAlgebra :
    Function.Injective (_root_.UniversalEnvelopingAlgebra.ι R :
      L → _root_.UniversalEnvelopingAlgebra R L) :=
  fun _ _ h => (primitiveEquiv R L).injective <| Subtype.ext <| by
    simpa only [coe_primitiveEquiv_apply] using h

end Injectivity

section Components

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L) [DecidableEq Γ] [GradedLieAlgebra ℒ]
  (d : PositiveDegrees Γ) [IsPositiveGrading d ℒ] (hneg : ∀ n, d.degree n < 0 → ℒ n = ⊥)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "𝒰" => homogeneousSubmodule ℒ

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The completed Lie homomorphism from `d.completedLie ℒ` into the Lie subalgebra of completed
primitive elements of `(degreeFiltration ℒ d.degree hneg).completion`. -/
noncomputable def completedLieToPrimitives :
    d.completedLie ℒ →ₗ⁅R⁆ completedPrimitives ℒ d.degree hneg where
  __ := (completedLieToU ℒ d hneg).toLinearMap.codRestrict
    (completedPrimitives ℒ d.degree hneg).toSubmodule fun z =>
    (mem_completedPrimitives_iff ℒ d.degree hneg).mpr
      (isCompletedPrimitive_completedLieToU ℒ d hneg z)
  map_lie' {x y} := Subtype.ext ((completedLieToU ℒ d hneg).map_lie x y)

/-- Coercing `completedLieToPrimitives ℒ d hneg z` to the ambient completion recovers
`completedLieToU ℒ d hneg z`. -/
@[simp]
theorem coe_completedLieToPrimitives_apply (z : d.completedLie ℒ) :
    (completedLieToPrimitives ℒ d hneg z : (degreeFiltration ℒ d.degree hneg).completion) =
      completedLieToU ℒ d hneg z := (rfl)

private theorem map_proj_tmul_one_add_one_tmul (u : U) {n i j : Γ} (hij : i + j = n) :
    TensorProduct.map (_root_.GradedAlgebra.proj 𝒰 i) (_root_.GradedAlgebra.proj 𝒰 j)
        ((1 : U) ⊗ₜ[R] u + u ⊗ₜ[R] (1 : U)) =
      TensorProduct.map (_root_.GradedAlgebra.proj 𝒰 i) (_root_.GradedAlgebra.proj 𝒰 j)
        ((1 : U) ⊗ₜ[R] (DirectSum.decompose 𝒰 u n : U) +
          (DirectSum.decompose 𝒰 u n : U) ⊗ₜ[R] (1 : U)) := by
  have hone : (1 : U) ∈ 𝒰 0 := SetLike.one_mem_graded 𝒰
  have hun : (DirectSum.decompose 𝒰 u n : U) ∈ 𝒰 n := (DirectSum.decompose 𝒰 u n).property
  simp only [map_add, TensorProduct.map_tmul, _root_.GradedAlgebra.proj_apply]
  congr 1
  · by_cases hi : i = 0
    · subst hi; obtain rfl : j = n := by simpa using hij
      rw [_root_.DirectSum.decompose_of_mem_same 𝒰 hun]
    · rw [_root_.DirectSum.decompose_of_mem_ne 𝒰 hone (Ne.symm hi),
        TensorProduct.zero_tmul, TensorProduct.zero_tmul]
  · by_cases hj : j = 0
    · subst hj; obtain rfl : i = n := by simpa using hij
      rw [_root_.DirectSum.decompose_of_mem_same 𝒰 hun]
    · rw [_root_.DirectSum.decompose_of_mem_ne 𝒰 hone (Ne.symm hj),
        TensorProduct.tmul_zero, TensorProduct.tmul_zero]

/-- If `x` is completed primitive in `(degreeFiltration ℒ d.degree hneg).completion`, then for every
degree `n : Γ` and representative `u : U(L)` of the cutoff projection at `(d.degree n).toNat`, the
degree-`n` component of `u` is primitive in `U(L)`. -/
theorem isPrimitiveElem_decompose_of_isCompletedPrimitive
    {x : (degreeFiltration ℒ d.degree hneg).completion}
    (hx : (degreeFiltration ℒ d.degree hneg).IsCompletedPrimitive R x) (n : Γ) {u : U}
    (hu : Ideal.Quotient.mk ((degreeFiltration ℒ d.degree hneg).ideal ((d.degree n).toNat + 1)) u =
      (degreeFiltration ℒ d.degree hneg).projection (d.degree n).toNat x) :
    Bialgebra.IsPrimitiveElem R (DirectSum.decompose 𝒰 u n : U) := by
  by_cases hn_pos : d.degree n ≤ 0
  · have hx0 : (degreeFiltration ℒ d.degree hneg).projection 0 x = 0 := by
      simpa only [AlgFiltration.completionIdeal_succ, RingHom.mem_ker] using
        hx.mem_completionIdeal_one (ker_counitAlgHom_le_positiveDegreeFiltration_one ℒ d hneg)
    have hu1 : u ∈ (degreeFiltration ℒ d.degree hneg).ideal 1 := by
      rw [Int.toNat_of_nonpos hn_pos, hx0] at hu
      exact Ideal.Quotient.eq_zero_iff_mem.mp hu
    rw [(mem_degreeFiltration_ideal_iff ℒ d.degree hneg).mp hu1 n (by omega),
      Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul]
    simp
  · have hn_pos : 0 < d.degree n := lt_of_not_ge hn_pos
    let k := (d.degree n).toNat
    have hk_eq : (k : ℤ) = d.degree n := Int.toNat_of_nonneg hn_pos.le
    have hprim := hx
    rw [AlgFiltration.isCompletedPrimitive_iff_includeCompletion] at hprim
    have hk_proj := congrArg (((degreeFiltration ℒ d.degree hneg).tensorProduct R
      (degreeFiltration ℒ d.degree hneg)).projection k) hprim
    have hu' : Ideal.Quotient.mk ((degreeFiltration ℒ d.degree hneg).ideal (k + 1)) u =
        (degreeFiltration ℒ d.degree hneg).projection k x := hu
    simp only [AlgFiltration.projection_completedCoproduct, map_add,
      AlgFiltration.projection_includeLeftCompletion,
      AlgFiltration.projection_includeRightCompletion] at hk_proj
    rw [← hu'] at hk_proj
    simp only [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, Bialgebra.comulAlgHom_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      ← map_add] at hk_proj
    have hmem := Ideal.Quotient.eq.mp hk_proj
    rw [degreeFiltration_eq_gradedAlgebra_degreeFiltration ℒ d.degree hneg] at hmem
    have hun_mem : (DirectSum.decompose 𝒰 u n : U) ∈ 𝒰 n := (DirectSum.decompose 𝒰 u n).property
    have hone : (1 : U) ∈ 𝒰 0 := SetLike.one_mem_graded 𝒰
    rw [Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul]
    refine TauCeti.GradedAlgebra.tensorProduct_ext 𝒰 𝒰 fun i j => ?_
    by_cases hij : i + j = n
    · have hdeg : d.degree i + d.degree j < ((k + 1 : ℕ) : ℤ) := by
        have := congrArg d.degree hij; simp only [map_add] at this; omega
      have hzero := (TauCeti.GradedAlgebra.mem_tensorProduct_degreeFiltration_ideal_iff 𝒰 𝒰
        d.degree _ d.degree _).mp hmem i j hdeg
      rw [map_sub] at hzero
      rw [show (DirectSum.decompose 𝒰 u n : U) = (DirectSum.decompose 𝒰 u (i + j) : U) by rw [hij],
        ← map_proj_comul ℒ u i j, sub_eq_zero.mp hzero, add_comm (u ⊗ₜ[R] (1 : U))]
      exact map_proj_tmul_one_add_one_tmul ℒ u rfl
    · rw [map_proj_comul_eq_zero_of_mem ℒ hun_mem hij, map_add,
        TensorProduct.map_tmul, TensorProduct.map_tmul]
      simp only [_root_.GradedAlgebra.proj_apply]
      have h1 : (_root_.DirectSum.decompose 𝒰 (1 : U) i : U) ⊗ₜ[R]
          (_root_.DirectSum.decompose 𝒰 (DirectSum.decompose 𝒰 u n : U) j : U) = 0 := by
        by_cases hi : i = 0
        · subst hi
          rw [_root_.DirectSum.decompose_of_mem_ne 𝒰 hun_mem (fun h => hij (by rw [zero_add, h])),
            TensorProduct.tmul_zero]
        · rw [_root_.DirectSum.decompose_of_mem_ne 𝒰 hone (Ne.symm hi), TensorProduct.zero_tmul]
      have h2 : (_root_.DirectSum.decompose 𝒰 (DirectSum.decompose 𝒰 u n : U) i : U) ⊗ₜ[R]
          (_root_.DirectSum.decompose 𝒰 (1 : U) j : U) = 0 := by
        by_cases hj : j = 0
        · subst hj
          rw [_root_.DirectSum.decompose_of_mem_ne 𝒰 hun_mem (fun h => hij (by rw [add_zero, h])),
            TensorProduct.zero_tmul]
        · rw [_root_.DirectSum.decompose_of_mem_ne 𝒰 hone (Ne.symm hj), TensorProduct.tmul_zero]
      rw [h1, h2, add_zero]

end Components

section RatAlgebra

universe u v

variable {Γ : Type u} (R : Type) {L : Type v} [AddCommMonoid Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] (ℒ : Γ → Submodule R L) [DecidableEq Γ] [GradedLieAlgebra ℒ]
  (d : PositiveDegrees Γ) [IsPositiveGrading d ℒ] (hneg : ∀ n, d.degree n < 0 → ℒ n = ⊥)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "𝒰" => homogeneousSubmodule ℒ

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Over a commutative `ℚ`-algebra `R : Type`, each `truncatedLieToU` is injective without any
module-freeness hypothesis. -/
theorem truncatedLieToU_injective_of_ratAlgebra (k : ℕ) :
    Function.Injective (truncatedLieToU ℒ d hneg k) :=
  truncatedLieToU_injective ℒ d hneg (ι_injective_of_ratAlgebra R L) k

/-- Over a commutative `ℚ`-algebra `R : Type`, `completedLieToU` is injective. -/
theorem completedLieToU_injective_of_ratAlgebra :
    Function.Injective (completedLieToU ℒ d hneg) :=
  completedLieToU_injective ℒ d hneg (ι_injective_of_ratAlgebra R L)

/-- Over a commutative `ℚ`-algebra `R : Type`, an element of the degree completion of `U(L)` is
completed primitive precisely when it belongs to the range of `completedLieToU`. -/
theorem isCompletedPrimitive_iff_mem_range_completedLieToU
    {x : (degreeFiltration ℒ d.degree hneg).completion} :
    (degreeFiltration ℒ d.degree hneg).IsCompletedPrimitive R x ↔
      x ∈ Set.range (completedLieToU ℒ d hneg) := by
  classical
  refine ⟨fun hx => ?_, fun ⟨z, hz⟩ => hz ▸ isCompletedPrimitive_completedLieToU ℒ d hneg z⟩
  let _ := d.lieRingPi ℒ
  let _ := d.lieAlgebraPi ℒ
  choose u hu using fun n : Γ => Ideal.Quotient.mk_surjective
    ((degreeFiltration ℒ d.degree hneg).projection (d.degree n).toNat x)
  choose w hw using fun n : Γ => (_root_.UniversalEnvelopingAlgebra.isPrimitiveElem_iff_mem_range_ι
    _).mp (isPrimitiveElem_decompose_of_isCompletedPrimitive ℒ d hneg hx n (hu n))
  let y : ∀ n, ℒ n := fun n => DirectSum.decompose ℒ (w n) n
  have hy (n : Γ) : ι R (y n : L) = (DirectSum.decompose 𝒰 (u n) n : U) := by
    rw [← coe_decompose_mkAlgHom_ι ℒ (w n) n, ← _root_.UniversalEnvelopingAlgebra.ι_apply, hw n,
      _root_.DirectSum.decompose_of_mem_same 𝒰 (DirectSum.decompose 𝒰 (u n) n).property]
  refine ⟨(d.completionLieEquivPi ℒ).symm y,
    (degreeFiltration ℒ d.degree hneg).completion_ext fun k => ?_⟩
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective ((degreeFiltration ℒ d.degree hneg).projection k x)
  rw [projection_completedLieToU, d.completionProjection_completionLieEquivPi_symm ℒ y k,
    truncatedLieToU_mkQ, ← hv, Ideal.Quotient.eq, mem_degreeFiltration_ideal_iff ℒ d.degree hneg]
  intro m hm
  rw [map_sum, _root_.DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub, sub_eq_zero]
  by_cases hm_mon : m ∈ d.monoid
  · have hm_cut : m ∈ (d.finite_cutoff k).toFinset := by
      rw [Set.Finite.mem_toFinset, d.mem_cutoff]; exact ⟨hm_mon, by omega⟩
    have hterm (n : Γ) : (DirectSum.decompose 𝒰 (ι R (y n : L)) m : U) =
        if n = m then ι R (y n : L) else 0 := by
      split_ifs with hnm
      · exact hnm ▸ _root_.DirectSum.decompose_of_mem_same 𝒰 (ι_mem_homogeneousSubmodule ℒ (y n).2)
      · exact _root_.DirectSum.decompose_of_mem_ne 𝒰 (ι_mem_homogeneousSubmodule ℒ (y n).2) hnm
    have hsum : (DirectSum.decompose 𝒰 (∑ n ∈ (d.finite_cutoff k).toFinset, ι R (y n : L)) m : U) =
        ι R (y m : L) := by
      rw [_root_.DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
      simp only [hterm, Finset.sum_ite_eq', hm_cut, ↓reduceIte]
    rw [hsum, hy m]
    have hm_nonneg := d.degree_nonneg hm_mon
    have hfac :=
      (degreeFiltration ℒ d.degree hneg).factor_projection (show (d.degree m).toNat ≤ k by omega) x
    rw [← hv, ← hu m, Ideal.Quotient.factor_mk, Ideal.Quotient.eq] at hfac
    have hdiff := (mem_degreeFiltration_ideal_iff ℒ d.degree hneg).mp hfac m (by omega)
    rwa [_root_.DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub,
      sub_eq_zero, eq_comm] at hdiff
  · have hbot := homogeneousSubmodule_eq_bot_of_not_mem_monoid ℒ d hm_mon
    have hz0 (z : U) : (DirectSum.decompose 𝒰 z m : U) = 0 := by
      simpa only [hbot, Submodule.mem_bot] using (DirectSum.decompose 𝒰 z m).property
    rw [hz0, hz0]

private theorem completedLieToPrimitives_bijective :
    Function.Bijective (completedLieToPrimitives ℒ d hneg).toLinearMap :=
  ⟨fun _ _ hz => completedLieToU_injective_of_ratAlgebra R ℒ d hneg (congrArg Subtype.val hz),
   fun p => by
    obtain ⟨z, hz⟩ := (isCompletedPrimitive_iff_mem_range_completedLieToU R ℒ d hneg).mp
      ((mem_completedPrimitives_iff ℒ d.degree hneg).mp p.property)
    exact ⟨z, Subtype.ext hz⟩⟩

/-- Over a commutative `ℚ`-algebra `R : Type`, `completedLieToPrimitives` identifies
`d.completedLie ℒ` with the Lie subalgebra of completed primitive elements of `F.completion`. -/
noncomputable def completedPrimitiveLieEquiv :
    d.completedLie ℒ ≃ₗ⁅R⁆ completedPrimitives ℒ d.degree hneg :=
  { LinearEquiv.ofBijective (completedLieToPrimitives ℒ d hneg).toLinearMap
      (completedLieToPrimitives_bijective R ℒ d hneg) with
    map_lie' := fun {x y} => (completedLieToPrimitives ℒ d hneg).map_lie x y }

/-- Applying `completedPrimitiveLieEquiv` and coercing to the ambient completion computes
`completedLieToU`. -/
@[simp]
theorem coe_completedPrimitiveLieEquiv_apply (z : d.completedLie ℒ) :
    (completedPrimitiveLieEquiv R ℒ d hneg z :
        (degreeFiltration ℒ d.degree hneg).completion) = completedLieToU ℒ d hneg z :=
  (congrArg Subtype.val
    (LinearEquiv.ofBijective_apply (f := (completedLieToPrimitives ℒ d hneg).toLinearMap)
      (hf := completedLieToPrimitives_bijective R ℒ d hneg) z)).trans
    (coe_completedLieToPrimitives_apply ℒ d hneg z)

/-- Mapping `(completedPrimitiveLieEquiv R ℒ d hneg).symm p` via `completedLieToU` recovers `p`. -/
@[simp]
theorem completedLieToU_completedPrimitiveLieEquiv_symm
    (p : completedPrimitives ℒ d.degree hneg) :
    completedLieToU ℒ d hneg ((completedPrimitiveLieEquiv R ℒ d hneg).symm p) =
      (p : (degreeFiltration ℒ d.degree hneg).completion) := by
  simpa only [coe_completedPrimitiveLieEquiv_apply] using
    congrArg Subtype.val ((completedPrimitiveLieEquiv R ℒ d hneg).apply_symm_apply p)

/-- The inverse of `completedPrimitiveLieEquiv` recovers the Lie preimage of `completedLieToU`. -/
@[simp]
theorem completedPrimitiveLieEquiv_symm_completedLieToU (z : d.completedLie ℒ)
    (hz : completedLieToU ℒ d hneg z ∈ completedPrimitives ℒ d.degree hneg :=
      (mem_completedPrimitives_iff ℒ d.degree hneg).mpr
        (isCompletedPrimitive_completedLieToU ℒ d hneg z)) :
    (completedPrimitiveLieEquiv R ℒ d hneg).symm ⟨completedLieToU ℒ d hneg z, hz⟩ = z :=
  (completedPrimitiveLieEquiv R ℒ d hneg).symm_apply_apply z

end RatAlgebra

end TauCeti.UniversalEnvelopingAlgebra
