/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Completion.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Primitive

import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Symmetrization.Injective

/-!
# Completed primitive elements of graded universal enveloping algebras

For a nonnegatively graded Lie algebra `L` over a commutative ring `R` with enveloping degree
filtration `F` on `U(L)`, every completed primitive element of `F.completion` has primitive
homogeneous components at each cutoff (`isPrimitiveElem_decompose_of_isCompletedPrimitive`). When
`[IsPositiveGrading d ℒ]` over a commutative `ℚ`-algebra `R`,
`UniversalEnvelopingAlgebra.isPrimitiveElem_iff_mem_range_ι` and
`PositiveDegrees.completionLieEquivPi` show that `completedLieToU` identifies `d.completedLie ℒ`
with the Lie subalgebra `completedPrimitives` without any freeness or finite-generation assumption.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.completedLieToPrimitives`: the completed Lie homomorphism
  landing in `completedPrimitives`.
* `TauCeti.UniversalEnvelopingAlgebra.completedPrimitiveLieEquiv`: over a commutative `ℚ`-algebra
  `R`, the Lie equivalence between `d.completedLie ℒ` and `completedPrimitives`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.isPrimitiveElem_decompose_of_isCompletedPrimitive`: every
  homogeneous component extracted from a completed primitive element is primitive in `U(L)`.
* `TauCeti.UniversalEnvelopingAlgebra.isCompletedPrimitive_iff_mem_range_completedLieToU`: over a
  commutative `ℚ`-algebra `R`, completed primitives are the range of `completedLieToU`.

## References

* K. O. Friedrichs, *Mathematical aspects of the quantum theory of fields. V*, Comm. Pure Appl.
  Math. 6 (1953), 1–72.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 1–3, Ch. II, §6.
* E. Petracci, *Universal representations of Lie algebras by coderivations*, arXiv:math/0303020, §8.
* `TauCeti.UniversalEnvelopingAlgebra.primitiveEquiv`.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

section Components

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L) [DecidableEq Γ] [GradedLieAlgebra ℒ]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "𝒰" => homogeneousSubmodule ℒ

attribute [local instance 100] LieRing.ofAssociativeRing

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

/-- If `x` is completed primitive in `(degreeFiltration ℒ d hneg).completion`, then for every
degree `n : Γ` and representative `u : U(L)` of the cutoff projection at `(d n).toNat`, the
degree-`n` component of `u` is primitive in `U(L)`. -/
theorem isPrimitiveElem_decompose_of_isCompletedPrimitive
    (d : Γ →+ ℤ) (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {x : (degreeFiltration ℒ d hneg).completion}
    (hx : (degreeFiltration ℒ d hneg).IsCompletedPrimitive R x) (n : Γ) {u : U}
    (hu : Ideal.Quotient.mk ((degreeFiltration ℒ d hneg).ideal ((d n).toNat + 1)) u =
      (degreeFiltration ℒ d hneg).projection (d n).toNat x) :
    Bialgebra.IsPrimitiveElem R (DirectSum.decompose 𝒰 u n : U) := by
  by_cases hn : d n < 0
  · have hbot := homogeneousSubmodule_eq_bot_of_degree_neg ℒ d hneg hn
    have hu0 : (DirectSum.decompose 𝒰 u n : U) = 0 := by
      simpa only [hbot, Submodule.mem_bot] using (DirectSum.decompose 𝒰 u n).property
    simp [hu0]
  · let k := (d n).toNat
    have hk_eq : (k : ℤ) = d n := Int.toNat_of_nonneg (not_lt.mp hn)
    have hmem := hx.comul_sub_mem_tensorProduct_ideal hu
    rw [degreeFiltration_eq_gradedAlgebra_degreeFiltration ℒ d hneg] at hmem
    have hun_mem : (DirectSum.decompose 𝒰 u n : U) ∈ 𝒰 n := (DirectSum.decompose 𝒰 u n).property
    have hone : (1 : U) ∈ 𝒰 0 := SetLike.one_mem_graded 𝒰
    rw [Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul]
    refine TauCeti.tensorProduct_ext_homogeneousComponent 𝒰 𝒰 fun i j => ?_
    simp only [← TauCeti.GradedAlgebra.proj_eq_homogeneousComponent]
    by_cases hij : i + j = n
    · have hzero := (TauCeti.GradedAlgebra.mem_tensorProduct_degreeFiltration_ideal_iff 𝒰 𝒰
        d _ d _).mp hmem i j (by have := congrArg d hij; simp only [map_add] at this; omega)
      rw [map_sub] at hzero
      rw [← hij, ← map_proj_comul ℒ u i j, sub_eq_zero.mp hzero, add_comm (u ⊗ₜ[R] (1 : U))]
      exact map_proj_tmul_one_add_one_tmul ℒ u rfl
    · rw [map_proj_comul_eq_zero_of_mem_ne ℒ hun_mem hij, map_add,
        TauCeti.GradedAlgebra.proj_eq_homogeneousComponent,
        TauCeti.GradedAlgebra.proj_eq_homogeneousComponent,
        TauCeti.map_homogeneousComponent_eq_zero_of_mem_ne 𝒰 𝒰 (p := (0, n)) (i := i) (j := j)
          (Submodule.apply_mem_map₂ _ hone hun_mem : (1 : U) ⊗ₜ[R] _ ∈ _)
          (fun h => hij (by obtain ⟨rfl, rfl⟩ := Prod.mk.inj h.symm; exact zero_add _)),
        TauCeti.map_homogeneousComponent_eq_zero_of_mem_ne 𝒰 𝒰 (p := (n, 0)) (i := i) (j := j)
          (Submodule.apply_mem_map₂ _ hun_mem hone : _ ⊗ₜ[R] (1 : U) ∈ _)
          (fun h => hij (by obtain ⟨rfl, rfl⟩ := Prod.mk.inj h.symm; exact add_zero _)),
        add_zero]

section PositiveGrading

variable (d : PositiveDegrees Γ) [IsPositiveGrading d ℒ]

local notation "F" => degreeFiltration ℒ (PositiveDegrees.degree d)
  (fun n hn => PositiveDegrees.eq_bot_of_degree_nonpos d ℒ n (le_of_lt hn))
local notation "P" => completedPrimitives ℒ (PositiveDegrees.degree d)
  (fun n hn => PositiveDegrees.eq_bot_of_degree_nonpos d ℒ n (le_of_lt hn))

/-- The completed Lie homomorphism from `d.completedLie ℒ` into the Lie subalgebra of completed
primitive elements of `(F).completion`. -/
noncomputable def completedLieToPrimitives : d.completedLie ℒ →ₗ⁅R⁆ P where
  __ := (completedLieToU ℒ d).toLinearMap.codRestrict (P).toSubmodule fun z =>
    (mem_completedPrimitives_iff ℒ d.degree _).mpr (isCompletedPrimitive_completedLieToU ℒ d z)
  map_lie' {x y} := Subtype.ext ((completedLieToU ℒ d).map_lie x y)

/-- Coercing `completedLieToPrimitives ℒ d z` to the ambient completion recovers
`completedLieToU ℒ d z`. -/
@[simp] theorem coe_completedLieToPrimitives_apply (z : d.completedLie ℒ) :
    (completedLieToPrimitives ℒ d z : (F).completion) = completedLieToU ℒ d z := (rfl)

end PositiveGrading

end Components

section RatAlgebra

variable {Γ : Type*} (R : Type*) {L : Type*} [AddCommMonoid Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] (ℒ : Γ → Submodule R L) [DecidableEq Γ] [GradedLieAlgebra ℒ]
  (d : PositiveDegrees Γ) [IsPositiveGrading d ℒ]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "𝒰" => homogeneousSubmodule ℒ
local notation "F" => degreeFiltration ℒ (PositiveDegrees.degree d)
  (fun n hn => PositiveDegrees.eq_bot_of_degree_nonpos d ℒ n (le_of_lt hn))
local notation "P" => completedPrimitives ℒ (PositiveDegrees.degree d)
  (fun n hn => PositiveDegrees.eq_bot_of_degree_nonpos d ℒ n (le_of_lt hn))

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Over a commutative `ℚ`-algebra `R`, each `truncatedLieToU` is injective without any
module-freeness hypothesis. -/
theorem truncatedLieToU_injective_of_ratAlgebra (k : ℕ) :
    Function.Injective (truncatedLieToU ℒ d k) :=
  truncatedLieToU_injective ℒ d (ι_injective_of_ratAlgebra R L) k

/-- Over a commutative `ℚ`-algebra `R`, `completedLieToU` is injective. -/
theorem completedLieToU_injective_of_ratAlgebra : Function.Injective (completedLieToU ℒ d) :=
  completedLieToU_injective ℒ d (ι_injective_of_ratAlgebra R L)

/-- Over a commutative `ℚ`-algebra `R`, an element of the degree completion of `U(L)` is
completed primitive precisely when it belongs to the range of `completedLieToU`. -/
theorem isCompletedPrimitive_iff_mem_range_completedLieToU {x : (F).completion} :
    (F).IsCompletedPrimitive R x ↔ x ∈ Set.range (completedLieToU ℒ d) := by
  classical
  refine ⟨fun hx => ?_, fun ⟨z, hz⟩ => hz ▸ isCompletedPrimitive_completedLieToU ℒ d z⟩
  let _ := d.lieRingPi ℒ; let _ := d.lieAlgebraPi ℒ
  choose u hu using fun n : Γ => Ideal.Quotient.mk_surjective ((F).projection (d.degree n).toNat x)
  choose w hw using fun n : Γ => (_root_.UniversalEnvelopingAlgebra.isPrimitiveElem_iff_mem_range_ι
    _).mp (isPrimitiveElem_decompose_of_isCompletedPrimitive ℒ d.degree _ hx n (hu n))
  let y : ∀ n, ℒ n := fun n => DirectSum.decompose ℒ (w n) n
  have hy (n : Γ) : ι R (y n : L) = (DirectSum.decompose 𝒰 (u n) n : U) := by
    rw [← coe_decompose_mkAlgHom_ι ℒ (w n) n, ← _root_.UniversalEnvelopingAlgebra.ι_apply, hw n,
      _root_.DirectSum.decompose_of_mem_same 𝒰 (DirectSum.decompose 𝒰 (u n) n).property]
  refine ⟨(d.completionLieEquivPi ℒ).symm y, (F).completion_ext fun k => ?_⟩
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective ((F).projection k x)
  rw [projection_completedLieToU, d.completionProjection_completionLieEquivPi_symm ℒ y k,
    truncatedLieToU_mkQ, ← hv, Ideal.Quotient.eq, mem_degreeFiltration_ideal_iff ℒ d.degree _]
  intro m hm
  rw [map_sum, _root_.DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub, sub_eq_zero]
  by_cases hm_mon : m ∈ d.monoid
  · have hm_cut : m ∈ (d.finite_cutoff k).toFinset := by
      rw [Set.Finite.mem_toFinset, d.mem_cutoff]; exact ⟨hm_mon, by omega⟩
    have hterm (n : Γ) : (DirectSum.decompose 𝒰 (ι R (y n : L)) m : U) =
        if n = m then ι R (y n : L) else 0 := by
      split_ifs with hnm
      · exact hnm ▸ _root_.DirectSum.decompose_of_mem_same 𝒰
          (ι_mem_homogeneousSubmodule ℒ (y n).property)
      · exact _root_.DirectSum.decompose_of_mem_ne 𝒰
          (ι_mem_homogeneousSubmodule ℒ (y n).property) hnm
    rw [_root_.DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
    simp only [hterm, Finset.sum_ite_eq', hm_cut, ↓reduceIte, hy m]
    have hm_nonneg := d.degree_nonneg hm_mon
    have hfac := (F).factor_projection (by omega : (d.degree m).toNat ≤ k) x
    rw [← hv, ← hu m, Ideal.Quotient.factor_mk, Ideal.Quotient.eq] at hfac
    have hdiff := (mem_degreeFiltration_ideal_iff ℒ d.degree _).mp hfac m (by omega)
    rwa [_root_.DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub,
      sub_eq_zero, eq_comm] at hdiff
  · have hbot := homogeneousSubmodule_eq_bot_of_notMem ℒ d.monoid
      (fun m hm => IsPositiveGrading.eq_bot m (Or.inl hm)) hm_mon
    have hz0 (z : U) : (DirectSum.decompose 𝒰 z m : U) = 0 := by
      simpa only [hbot, Submodule.mem_bot] using (DirectSum.decompose 𝒰 z m).property
    rw [hz0, hz0]

/-- Over a commutative `ℚ`-algebra `R`, `completedLieToPrimitives` identifies
`d.completedLie ℒ` with the Lie subalgebra of completed primitive elements of `(F).completion`. -/
noncomputable def completedPrimitiveLieEquiv : d.completedLie ℒ ≃ₗ⁅R⁆ P :=
  LieEquiv.ofBijective (completedLieToPrimitives ℒ d)
    ⟨fun _ _ hz => completedLieToU_injective_of_ratAlgebra R ℒ d (congrArg Subtype.val hz),
     fun p => by
       obtain ⟨z, hz⟩ := (isCompletedPrimitive_iff_mem_range_completedLieToU R ℒ d).mp
         ((mem_completedPrimitives_iff ℒ d.degree _).mp p.property)
       exact ⟨z, Subtype.ext hz⟩⟩

/-- Applying `completedPrimitiveLieEquiv` and coercing to the ambient completion computes
`completedLieToU`. -/
@[simp] theorem coe_completedPrimitiveLieEquiv_apply (z : d.completedLie ℒ) :
    (completedPrimitiveLieEquiv R ℒ d z : (F).completion) = completedLieToU ℒ d z := (rfl)

/-- Mapping `(completedPrimitiveLieEquiv R ℒ d).symm p` via `completedLieToU` recovers `p`. -/
@[simp] theorem completedLieToU_completedPrimitiveLieEquiv_symm (p : P) :
    completedLieToU ℒ d ((completedPrimitiveLieEquiv R ℒ d).symm p) = (p : (F).completion) := by
  simpa only [coe_completedPrimitiveLieEquiv_apply] using
    congrArg Subtype.val ((completedPrimitiveLieEquiv R ℒ d).apply_symm_apply p)

/-- The inverse of `completedPrimitiveLieEquiv` recovers the Lie preimage of `completedLieToU`. -/
@[simp] theorem completedPrimitiveLieEquiv_symm_completedLieToU (z : d.completedLie ℒ)
    (hz : completedLieToU ℒ d z ∈ P :=
      (mem_completedPrimitives_iff ℒ d.degree _).mpr (isCompletedPrimitive_completedLieToU ℒ d z)) :
    (completedPrimitiveLieEquiv R ℒ d).symm ⟨completedLieToU ℒ d z, hz⟩ = z :=
  (completedPrimitiveLieEquiv R ℒ d).symm_apply_apply z

end RatAlgebra

end TauCeti.UniversalEnvelopingAlgebra
