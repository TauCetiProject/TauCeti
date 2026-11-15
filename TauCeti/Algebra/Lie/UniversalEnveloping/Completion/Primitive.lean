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

Let `L` be a Lie algebra over a commutative ring `R`, positively graded by `(d, ℒ)`, and let `F` be
the associated enveloping degree filtration on `U(L)`. Over an arbitrary commutative ring `R`,
every completed primitive element of `F.completion` has primitive homogeneous components at each
finite cutoff (`isPrimitiveElem_decompose_of_isCompletedPrimitive`).

When `R : Type` is a commutative `ℚ`-algebra, the uncompleted primitive theorem
`UniversalEnvelopingAlgebra.isPrimitiveElem_iff_mem_range_ι` identifies each primitive homogeneous
piece of `U(L)` with a homogeneous Lie element of the same degree. Assembling these components
through `PositiveDegrees.completionLieEquivPi` shows that every completed primitive element of
`F.completion` comes from a unique element of `d.completedLie ℒ` via `completedLieToU`, with no
freeness or finite-generation assumption on `L`.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.completedLieToPrimitives`: the completed Lie homomorphism
  landing in the Lie subalgebra `completedPrimitives ℒ d.degree hneg`.
* `TauCeti.UniversalEnvelopingAlgebra.completedPrimitiveLieEquiv`: over a commutative `ℚ`-algebra
  `R : Type`, the Lie equivalence `d.completedLie ℒ ≃ₗ⁅R⁆ completedPrimitives ℒ d.degree hneg`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.ι_injective_of_ratAlgebra`: over a commutative `ℚ`-algebra
  `R : Type`, the canonical Lie map `ι R : L → U(L)` is injective without module freeness.
* `TauCeti.UniversalEnvelopingAlgebra.isPrimitiveElem_decompose_of_isCompletedPrimitive`: every
  homogeneous component extracted from a completed primitive element is primitive in `U(L)`.
* `TauCeti.UniversalEnvelopingAlgebra.isCompletedPrimitive_iff_mem_range_completedLieToU`: over a
  commutative `ℚ`-algebra `R : Type`, the completed primitive elements are precisely the range of
  `completedLieToU`.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

section Injectivity

universe v

variable (R : Type) (L : Type v) [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]

/-- Over a commutative `ℚ`-algebra `R : Type`, the canonical map `ι R : L → U(L)` is injective
without any freeness or flatness hypothesis on `L`. -/
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
      completedLieToU ℒ d hneg z :=
  (rfl)

private theorem map_proj_tmul_one_add_one_tmul (u : U) {n i j : Γ} (hij : i + j = n) :
    TensorProduct.map (_root_.GradedAlgebra.proj (homogeneousSubmodule ℒ) i)
        (_root_.GradedAlgebra.proj (homogeneousSubmodule ℒ) j)
        ((1 : U) ⊗ₜ[R] u + u ⊗ₜ[R] (1 : U)) =
      TensorProduct.map (_root_.GradedAlgebra.proj (homogeneousSubmodule ℒ) i)
        (_root_.GradedAlgebra.proj (homogeneousSubmodule ℒ) j)
        ((1 : U) ⊗ₜ[R] (DirectSum.decompose (homogeneousSubmodule ℒ) u n : U) +
          (DirectSum.decompose (homogeneousSubmodule ℒ) u n : U) ⊗ₜ[R] (1 : U)) := by
  have hone : (1 : U) ∈ homogeneousSubmodule ℒ 0 :=
    SetLike.one_mem_graded (homogeneousSubmodule ℒ)
  have hun : (DirectSum.decompose (homogeneousSubmodule ℒ) u n : U) ∈ homogeneousSubmodule ℒ n :=
    (DirectSum.decompose (homogeneousSubmodule ℒ) u n).property
  simp only [map_add, TensorProduct.map_tmul, _root_.GradedAlgebra.proj_apply]
  congr 1
  · by_cases hi : i = 0
    · subst hi
      have hjn : j = n := by simpa only [zero_add] using hij
      subst hjn
      rw [_root_.DirectSum.decompose_of_mem_same (homogeneousSubmodule ℒ) hun]
    · rw [_root_.DirectSum.decompose_of_mem_ne (homogeneousSubmodule ℒ) hone (Ne.symm hi)]
      simp
  · by_cases hj : j = 0
    · subst hj
      have hin : i = n := by simpa only [add_zero] using hij
      subst hin
      rw [_root_.DirectSum.decompose_of_mem_same (homogeneousSubmodule ℒ) hun]
    · rw [_root_.DirectSum.decompose_of_mem_ne (homogeneousSubmodule ℒ) hone (Ne.symm hj)]
      simp

/-- If `x` is completed primitive in `(degreeFiltration ℒ d.degree hneg).completion`, then for every
degree `n : Γ` and every representative `u : U(L)` of the cutoff projection at `(d.degree n).toNat`,
the degree-`n` component of `u` is primitive in `U(L)`. -/
theorem isPrimitiveElem_decompose_of_isCompletedPrimitive
    {x : (degreeFiltration ℒ d.degree hneg).completion}
    (hx : (degreeFiltration ℒ d.degree hneg).IsCompletedPrimitive R x) (n : Γ) {u : U}
    (hu : Ideal.Quotient.mk
        ((degreeFiltration ℒ d.degree hneg).ideal ((d.degree n).toNat + 1)) u =
      (degreeFiltration ℒ d.degree hneg).projection (d.degree n).toNat x) :
    Bialgebra.IsPrimitiveElem R (DirectSum.decompose (homogeneousSubmodule ℒ) u n : U) := by
  by_cases hn_pos : d.degree n ≤ 0
  · have htoNat : (d.degree n).toNat = 0 := Int.toNat_of_nonpos hn_pos
    have hx1 : x ∈ (degreeFiltration ℒ d.degree hneg).completionIdeal 1 :=
      hx.mem_completionIdeal_one (ker_counitAlgHom_le_positiveDegreeFiltration_one ℒ d hneg)
    have hx0 : (degreeFiltration ℒ d.degree hneg).projection 0 x = 0 := by
      simpa only [AlgFiltration.completionIdeal_succ, RingHom.mem_ker] using hx1
    have hu1 : u ∈ (degreeFiltration ℒ d.degree hneg).ideal 1 := by
      rw [htoNat, hx0] at hu
      exact Ideal.Quotient.eq_zero_iff_mem.mp hu
    have hun0 : (DirectSum.decompose (homogeneousSubmodule ℒ) u n : U) = 0 :=
      (mem_degreeFiltration_ideal_iff ℒ d.degree hneg).mp hu1 n (by omega)
    rw [hun0, Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul]
    simp
  · have hn_pos : 0 < d.degree n := lt_of_not_ge hn_pos
    let k := (d.degree n).toNat
    have hk_eq : (k : ℤ) = d.degree n := Int.toNat_of_nonneg hn_pos.le
    have hprim := hx
    rw [AlgFiltration.isCompletedPrimitive_iff_includeCompletion] at hprim
    have hk_proj := congrArg
      (((degreeFiltration ℒ d.degree hneg).tensorProduct R
        (degreeFiltration ℒ d.degree hneg)).projection k) hprim
    simp only [AlgFiltration.projection_completedCoproduct, map_add,
      AlgFiltration.projection_includeLeftCompletion,
      AlgFiltration.projection_includeRightCompletion] at hk_proj
    change _ = _ at hu
    have hu' : Ideal.Quotient.mk ((degreeFiltration ℒ d.degree hneg).ideal (k + 1)) u =
        (degreeFiltration ℒ d.degree hneg).projection k x := hu
    rw [← hu'] at hk_proj
    simp only [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, Bialgebra.comulAlgHom_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      ← map_add] at hk_proj
    have hmem : Coalgebra.comul (R := R) u - (u ⊗ₜ[R] (1 : U) + (1 : U) ⊗ₜ[R] u) ∈
        ((degreeFiltration ℒ d.degree hneg).tensorProduct R
          (degreeFiltration ℒ d.degree hneg)).ideal (k + 1) :=
      Ideal.Quotient.eq.mp hk_proj
    rw [degreeFiltration_eq_gradedAlgebra_degreeFiltration ℒ d.degree hneg] at hmem
    have hun_mem : (DirectSum.decompose (homogeneousSubmodule ℒ) u n : U) ∈
        homogeneousSubmodule ℒ n :=
      (DirectSum.decompose (homogeneousSubmodule ℒ) u n).property
    have hone : (1 : U) ∈ homogeneousSubmodule ℒ 0 :=
      SetLike.one_mem_graded (homogeneousSubmodule ℒ)
    rw [Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul]
    apply TauCeti.GradedAlgebra.tensorProduct_ext (homogeneousSubmodule ℒ) (homogeneousSubmodule ℒ)
    intro i j
    by_cases hij : i + j = n
    · have hdeg : d.degree i + d.degree j < ((k + 1 : ℕ) : ℤ) := by
        have hsum : d.degree i + d.degree j = d.degree n := by
          simpa only [map_add] using congrArg d.degree hij
        omega
      have hzero := (TauCeti.GradedAlgebra.mem_tensorProduct_degreeFiltration_ideal_iff
        (homogeneousSubmodule ℒ) (homogeneousSubmodule ℒ) d.degree _ d.degree _).mp hmem i j hdeg
      rw [map_sub] at hzero
      have hcomul_eq := sub_eq_zero.mp hzero
      have hdec :
          (DirectSum.decompose (homogeneousSubmodule ℒ) u n : U) =
            (DirectSum.decompose (homogeneousSubmodule ℒ) u (i + j) : U) :=
        congrArg (fun m => (DirectSum.decompose (homogeneousSubmodule ℒ) u m : U)) hij.symm
      rw [hdec, ← map_proj_comul ℒ u i j, hcomul_eq, add_comm (u ⊗ₜ[R] (1 : U))]
      exact map_proj_tmul_one_add_one_tmul ℒ u rfl
    · rw [map_proj_comul_eq_zero_of_mem ℒ hun_mem hij, map_add,
        TensorProduct.map_tmul, TensorProduct.map_tmul]
      simp only [_root_.GradedAlgebra.proj_apply]
      have h1 : (_root_.DirectSum.decompose (homogeneousSubmodule ℒ) (1 : U) i : U) ⊗ₜ[R]
          (_root_.DirectSum.decompose (homogeneousSubmodule ℒ)
            (DirectSum.decompose (homogeneousSubmodule ℒ) u n : U) j : U) = 0 := by
        by_cases hi : i = 0
        · subst hi
          have hjn : n ≠ j := fun h => hij (by rw [zero_add, h])
          rw [_root_.DirectSum.decompose_of_mem_ne (homogeneousSubmodule ℒ) hun_mem hjn,
            TensorProduct.tmul_zero]
        · rw [_root_.DirectSum.decompose_of_mem_ne (homogeneousSubmodule ℒ) hone (Ne.symm hi),
            TensorProduct.zero_tmul]
      have h2 : (_root_.DirectSum.decompose (homogeneousSubmodule ℒ)
          (DirectSum.decompose (homogeneousSubmodule ℒ) u n : U) i : U) ⊗ₜ[R]
            (_root_.DirectSum.decompose (homogeneousSubmodule ℒ) (1 : U) j : U) = 0 := by
        by_cases hj : j = 0
        · subst hj
          have hin : n ≠ i := fun h => hij (by rw [add_zero, h])
          rw [_root_.DirectSum.decompose_of_mem_ne (homogeneousSubmodule ℒ) hun_mem hin,
            TensorProduct.zero_tmul]
        · rw [_root_.DirectSum.decompose_of_mem_ne (homogeneousSubmodule ℒ) hone (Ne.symm hj),
            TensorProduct.tmul_zero]
      rw [h1, h2, add_zero]

end Components

section RatAlgebra

universe u v

variable {Γ : Type u} (R : Type) {L : Type v} [AddCommMonoid Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] (ℒ : Γ → Submodule R L) [DecidableEq Γ] [GradedLieAlgebra ℒ]
  (d : PositiveDegrees Γ) [IsPositiveGrading d ℒ] (hneg : ∀ n, d.degree n < 0 → ℒ n = ⊥)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Over a commutative `ℚ`-algebra `R : Type`, each finite-order Lie map `truncatedLieToU` is
injective without any module-freeness hypothesis. -/
theorem truncatedLieToU_injective_of_ratAlgebra (k : ℕ) :
    Function.Injective (truncatedLieToU ℒ d hneg k) :=
  truncatedLieToU_injective ℒ d hneg (ι_injective_of_ratAlgebra R L) k

/-- Over a commutative `ℚ`-algebra `R : Type`, `completedLieToU` embeds `d.completedLie ℒ` into the
degree completion of `U(L)`. -/
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
  refine ⟨fun hx => ?_, ?_⟩
  · let _ := d.lieRingPi ℒ
    let _ := d.lieAlgebraPi ℒ
    have hrep (n : Γ) : ∃ u : U,
        Ideal.Quotient.mk
          ((degreeFiltration ℒ d.degree hneg).ideal ((d.degree n).toNat + 1)) u =
          (degreeFiltration ℒ d.degree hneg).projection (d.degree n).toNat x :=
      Ideal.Quotient.mk_surjective _
    choose u hu using hrep
    have hlie (n : Γ) : ∃ w : L,
        ι R w = (DirectSum.decompose (homogeneousSubmodule ℒ) (u n) n : U) :=
      (_root_.UniversalEnvelopingAlgebra.isPrimitiveElem_iff_mem_range_ι _).mp
        (isPrimitiveElem_decompose_of_isCompletedPrimitive ℒ d hneg hx n (hu n))
    choose w hw using hlie
    let y : ∀ n, ℒ n := fun n => DirectSum.decompose ℒ (w n) n
    have hy (n : Γ) :
        ι R (y n : L) = (DirectSum.decompose (homogeneousSubmodule ℒ) (u n) n : U) := by
      have hun_mem : (DirectSum.decompose (homogeneousSubmodule ℒ) (u n) n : U) ∈
          homogeneousSubmodule ℒ n :=
        (DirectSum.decompose (homogeneousSubmodule ℒ) (u n) n).property
      calc
        ι R (y n : L)
            = (DirectSum.decompose (homogeneousSubmodule ℒ)
                (mkAlgHom R L (TensorAlgebra.ι R (w n))) n : U) :=
              (coe_decompose_mkAlgHom_ι ℒ (w n) n).symm
        _ = (DirectSum.decompose (homogeneousSubmodule ℒ) (ι R (w n)) n : U) := by
              rw [← _root_.UniversalEnvelopingAlgebra.ι_apply]
        _ = (DirectSum.decompose (homogeneousSubmodule ℒ)
              (DirectSum.decompose (homogeneousSubmodule ℒ) (u n) n : U) n : U) := by
              rw [hw n]
        _ = (DirectSum.decompose (homogeneousSubmodule ℒ) (u n) n : U) :=
              _root_.DirectSum.decompose_of_mem_same (homogeneousSubmodule ℒ) hun_mem
    refine ⟨(d.completionLieEquivPi ℒ).symm y, ?_⟩
    apply (degreeFiltration ℒ d.degree hneg).completion_ext
    intro k
    obtain ⟨v, hv⟩ :=
      Ideal.Quotient.mk_surjective ((degreeFiltration ℒ d.degree hneg).projection k x)
    rw [projection_completedLieToU, d.completionProjection_completionLieEquivPi_symm ℒ y k,
      truncatedLieToU_mkQ, ← hv, Ideal.Quotient.eq,
      mem_degreeFiltration_ideal_iff ℒ d.degree hneg]
    intro m hm
    rw [map_sum, _root_.DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub,
      sub_eq_zero]
    by_cases hm_mon : m ∈ d.monoid
    · have hm_cut : m ∈ (d.finite_cutoff k).toFinset := by
        rw [Set.Finite.mem_toFinset, d.mem_cutoff]
        exact ⟨hm_mon, by omega⟩
      have hsum :
          (DirectSum.decompose (homogeneousSubmodule ℒ)
              (∑ n ∈ (d.finite_cutoff k).toFinset, ι R (y n : L)) m : U) =
            ι R (y m : L) := by
        rw [_root_.DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
        have hterm (n : Γ) :
            (DirectSum.decompose (homogeneousSubmodule ℒ) (ι R (y n : L)) m : U) =
              if n = m then ι R (y n : L) else 0 := by
          split_ifs with hnm
          · subst hnm
            exact _root_.DirectSum.decompose_of_mem_same (homogeneousSubmodule ℒ)
              (ι_mem_homogeneousSubmodule ℒ (y n).property)
          · exact _root_.DirectSum.decompose_of_mem_ne (homogeneousSubmodule ℒ)
              (ι_mem_homogeneousSubmodule ℒ (y n).property) hnm
        simp_rw [hterm]
        simp only [Finset.sum_ite_eq', hm_cut, ↓reduceIte]
      rw [hsum, hy m]
      have hm_nonneg : 0 ≤ d.degree m := d.degree_nonneg hm_mon
      have hm_le : (d.degree m).toNat ≤ k := by omega
      have hfac := (degreeFiltration ℒ d.degree hneg).factor_projection hm_le x
      rw [← hv, ← hu m, Ideal.Quotient.factor_mk, Ideal.Quotient.eq] at hfac
      have hdiff := (mem_degreeFiltration_ideal_iff ℒ d.degree hneg).mp hfac m (by omega)
      rw [_root_.DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub,
        sub_eq_zero] at hdiff
      exact hdiff.symm
    · have hbot := homogeneousSubmodule_eq_bot_of_not_mem_monoid ℒ d hm_mon
      have hl0 : (DirectSum.decompose (homogeneousSubmodule ℒ)
          (∑ n ∈ (d.finite_cutoff k).toFinset, ι R (y n : L)) m : U) = 0 := by
        simpa only [hbot, Submodule.mem_bot] using
          (DirectSum.decompose (homogeneousSubmodule ℒ)
            (∑ n ∈ (d.finite_cutoff k).toFinset, ι R (y n : L)) m).property
      have hr0 : (DirectSum.decompose (homogeneousSubmodule ℒ) v m : U) = 0 := by
        simpa only [hbot, Submodule.mem_bot] using
          (DirectSum.decompose (homogeneousSubmodule ℒ) v m).property
      rw [hl0, hr0]
  · rintro ⟨z, rfl⟩
    exact isCompletedPrimitive_completedLieToU ℒ d hneg z

/-- Over a commutative `ℚ`-algebra `R : Type`, `completedLieToPrimitives` identifies the degree
completion `d.completedLie ℒ` with the Lie subalgebra of completed primitive elements of
`(degreeFiltration ℒ d.degree hneg).completion`. -/
noncomputable def completedPrimitiveLieEquiv :
    d.completedLie ℒ ≃ₗ⁅R⁆ completedPrimitives ℒ d.degree hneg :=
  { LinearEquiv.ofBijective (completedLieToPrimitives ℒ d hneg).toLinearMap
      ⟨fun z₁ z₂ hz =>
        completedLieToU_injective_of_ratAlgebra R ℒ d hneg (congrArg Subtype.val hz),
       fun p => by
        obtain ⟨z, hz⟩ :=
          (isCompletedPrimitive_iff_mem_range_completedLieToU R ℒ d hneg).mp
            ((mem_completedPrimitives_iff ℒ d.degree hneg).mp p.property)
        exact ⟨z, Subtype.ext hz⟩⟩ with
    map_lie' := fun {x y} => (completedLieToPrimitives ℒ d hneg).map_lie x y }

/-- Applying `completedPrimitiveLieEquiv` and coercing to the ambient completion computes
`completedLieToU`. -/
@[simp]
theorem coe_completedPrimitiveLieEquiv_apply (z : d.completedLie ℒ) :
    (completedPrimitiveLieEquiv R ℒ d hneg z :
        (degreeFiltration ℒ d.degree hneg).completion) =
      completedLieToU ℒ d hneg z :=
  (congrArg Subtype.val
    (LinearEquiv.ofBijective_apply (f := (completedLieToPrimitives ℒ d hneg).toLinearMap)
      (hf := ⟨fun _ _ hz =>
        completedLieToU_injective_of_ratAlgebra R ℒ d hneg (congrArg Subtype.val hz),
       fun p => by
        obtain ⟨w, hw⟩ :=
          (isCompletedPrimitive_iff_mem_range_completedLieToU R ℒ d hneg).mp
            ((mem_completedPrimitives_iff ℒ d.degree hneg).mp p.property)
        exact ⟨w, Subtype.ext hw⟩⟩) z)).trans
    (coe_completedLieToPrimitives_apply ℒ d hneg z)

/-- Mapping `(completedPrimitiveLieEquiv R ℒ d hneg).symm p` back to the enveloping completion via
`completedLieToU` recovers `p`. -/
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
