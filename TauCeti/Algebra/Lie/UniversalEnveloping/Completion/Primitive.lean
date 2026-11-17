/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Completion.Bialgebra
public import TauCeti.Algebra.Lie.UniversalEnveloping.Primitive

/-!
# Primitive elements of completed universal enveloping algebras

Over a commutative rational algebra `R : Type`, `TauCeti.PositiveDegrees.completedLieToU`
identifies the completed positively graded Lie algebra `d.completedLie ℒ` with the completed
primitive elements of `(d.envelopingFiltration ℒ).completion`, with no freeness, flatness, or
finite-rank hypothesis on `L`:

* `TauCeti.PositiveDegrees.isCompletedPrimitive_iff_mem_range_completedLieToU`: completed primitive
  elements are precisely the range of `d.completedLieToU ℒ`.
* `TauCeti.PositiveDegrees.completedPrimitiveEquiv`: the resulting `R`-linear equivalence carrying
  the Lie bracket to the associative commutator.

When `U(L)` carries a compatible `ℚ`-algebra structure, combining `completedPrimitiveEquiv` with
`TauCeti.AlgFiltration.completedExpPrimitiveEquivOfKerLe` identifies `d.completedLie ℒ` with the
completed group-like elements (`TauCeti.PositiveDegrees.completedLieExpEquiv`) and defines the
associative completed Baker–Campbell–Hausdorff product (`TauCeti.PositiveDegrees.completedLieBCH`).

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter II, §6.
* E. Petracci, *Universal representations of Lie algebras by coderivations*
  (arXiv:math/0303020), §8.
* D. Quillen, *Rational homotopy theory*, Ann. of Math. (2) **90** (1969), Appendix A.
* J.-P. Serre, *Lie Algebras and Lie Groups*, Part I, Chapter IV.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti.PositiveDegrees

open _root_.UniversalEnvelopingAlgebra TauCeti.UniversalEnvelopingAlgebra

universe u v

section Primitive

variable {N : Type u} {R : Type} {L : Type v}
  [AddCommMonoid N] [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Over a commutative rational algebra `R : Type`, every finite-order map `truncatedLieToU` is
injective. -/
theorem truncatedLieToU_injective_of_rat (k : ℕ) :
    Function.Injective (d.truncatedLieToU ℒ k) :=
  d.truncatedLieToU_injective ℒ (ι_injective_of_rat R L) k

/-- Over a commutative rational algebra `R : Type`, `completedLieToU` is injective. -/
theorem completedLieToU_injective_of_rat :
    Function.Injective (d.completedLieToU ℒ) :=
  d.completedLieToU_injective ℒ (ι_injective_of_rat R L)

omit [Algebra ℚ R] in
private theorem exists_sub_mem_envelopingFiltration_of_degree_le (a : U) (k : ℕ) :
    ∃ b : U, a - b ∈ (d.envelopingFiltration ℒ).ideal (k + 1) ∧
      ∀ m, (k : ℤ) < d.degree m →
        (DirectSum.decompose (homogeneousSubmodule ℒ) b m : U) = 0 := by
  classical
  let H := homogeneousSubmodule ℒ
  let b : U := ∑ n ∈ (DirectSum.decompose H a).support with d.degree n ≤ k,
    (DirectSum.decompose H a n : U)
  refine ⟨b, ?_, fun m hm => ?_⟩
  · have hsum := (Finset.sum_filter_add_sum_filter_not (s := (DirectSum.decompose H a).support)
      (p := fun n => d.degree n ≤ k) (f := fun n => (DirectSum.decompose H a n : U))).trans
      (DirectSum.sum_support_decompose H a)
    rw [(eq_sub_of_add_eq' (by simpa only [b] using hsum)).symm]
    exact Submodule.sum_mem _ fun n hn => d.mem_envelopingFiltration_of_mem_homogeneousSubmodule ℒ
      (DirectSum.decompose H a n).property (by have := (Finset.mem_filter.mp hn).2; omega)
  · simp only [b, ← DirectSum.decomposeLinearEquiv_apply, map_sum, _root_.DirectSum.sum_apply,
      Submodule.coe_sum]
    refine Finset.sum_eq_zero fun n hn => DirectSum.decompose_of_mem_ne H
      (DirectSum.decompose H a n).property fun hnm => ?_
    have := (Finset.mem_filter.mp hn).2; subst hnm; omega

private theorem exists_truncatedLieToU_eq_projection {u : (d.envelopingFiltration ℒ).completion}
    (hu : (d.envelopingFiltration ℒ).IsCompletedPrimitive R
      (d.envelopingFiltration_ideal_le_comap_comul ℒ)
      (d.envelopingFiltration_one_le_ker_counit ℒ) u) (k : ℕ) :
    ∃ y : d.truncatedLie ℒ k, d.truncatedLieToU ℒ k y =
      (d.envelopingFiltration ℒ).projection k u := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((d.envelopingFiltration ℒ).projection k u)
  obtain ⟨b, hab, hdeg⟩ := d.exists_sub_mem_envelopingFiltration_of_degree_le ℒ a k
  have hbu : u - (d.envelopingFiltration ℒ).toCompletion b ∈
      (d.envelopingFiltration ℒ).completionIdeal (k + 1) := by
    rwa [AlgFiltration.completionIdeal_succ, RingHom.mem_ker, map_sub,
      AlgFiltration.projection_toCompletion, ← ha, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨x, hx⟩ := (_root_.UniversalEnvelopingAlgebra.isPrimitiveElem_iff_mem_range_ι b).mp <|
    d.isPrimitiveElem_of_mem_envelopingFiltration_tensorProduct_succ ℒ hdeg
      ((d.envelopingFiltration ℒ).comul_sub_mem_of_isCompletedPrimitive_of_sub_mem R
        (d.envelopingFiltration_ideal_le_comap_comul ℒ)
        (d.envelopingFiltration_one_le_ker_counit ℒ) hu hbu)
  refine ⟨LieSubmodule.Quotient.mk x, ?_⟩
  rw [truncatedLieToU_mk, hx, ← (d.envelopingFiltration ℒ).projection_toCompletion k b]
  exact ((d.envelopingFiltration ℒ).projection_eq_of_sub_mem_completionIdeal_succ hbu).symm

/-- Over a commutative rational algebra `R : Type`, an element of the completed universal enveloping
algebra is completed primitive if and only if it lies in the image of `completedLieToU`. -/
theorem isCompletedPrimitive_iff_mem_range_completedLieToU
    (u : (d.envelopingFiltration ℒ).completion) :
    (d.envelopingFiltration ℒ).IsCompletedPrimitive R
      (d.envelopingFiltration_ideal_le_comap_comul ℒ)
      (d.envelopingFiltration_one_le_ker_counit ℒ) u ↔
      u ∈ Set.range (d.completedLieToU ℒ) := by
  refine ⟨fun hu => ?_, fun ⟨z, hz⟩ => hz ▸ d.isCompletedPrimitive_completedLieToU ℒ z⟩
  choose y hy using d.exists_truncatedLieToU_eq_projection ℒ hu
  have hcompat (k : ℕ) :
      LieIdeal.factor (d.degreeIdeal_antitone ℒ (Nat.le_succ k)) (y (k + 1)) = y k :=
    d.truncatedLieToU_injective_of_rat ℒ k <| by
      rw [← d.factor_truncatedLieToU ℒ (Nat.le_succ k) (y (k + 1)), hy (k + 1),
        (d.envelopingFiltration ℒ).factor_projection (Nat.le_succ k) u, hy k]
  refine ⟨LieIdeal.completionMk (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) y hcompat,
    (d.envelopingFiltration ℒ).completion_ext fun k => ?_⟩
  rw [projection_completedLieToU, LieIdeal.completionProjection_completionMk, hy k]

/-- Over a commutative rational algebra `R : Type`, `completedLieToU` identifies the completed
positively graded Lie algebra with the `R`-submodule of completed primitive elements. -/
noncomputable def completedPrimitiveEquiv :
    d.completedLie ℒ ≃ₗ[R]
      (d.envelopingFiltration ℒ).completedPrimitiveSubmodule R
        (d.envelopingFiltration_ideal_le_comap_comul ℒ)
        (d.envelopingFiltration_one_le_ker_counit ℒ) :=
  LinearEquiv.ofBijective
    ((d.completedLieToU ℒ).toLinearMap.codRestrict _ fun z =>
      ((d.envelopingFiltration ℒ).mem_completedPrimitiveSubmodule R _ _).mpr
        (d.isCompletedPrimitive_completedLieToU ℒ z))
    ⟨(LinearMap.injective_codRestrict_iff _).mpr (d.completedLieToU_injective_of_rat ℒ), fun p =>
      let ⟨z, hz⟩ := (d.isCompletedPrimitive_iff_mem_range_completedLieToU ℒ p.val).mp
        (((d.envelopingFiltration ℒ).mem_completedPrimitiveSubmodule R _ _).mp p.property)
      ⟨z, Subtype.ext hz⟩⟩

/-- `completedPrimitiveEquiv` coerces to `completedLieToU`. -/
@[simp]
theorem coe_completedPrimitiveEquiv_apply (z : d.completedLie ℒ) :
    (d.completedPrimitiveEquiv ℒ z : (d.envelopingFiltration ℒ).completion) =
      d.completedLieToU ℒ z := (rfl)

/-- Recovering a completed Lie element from its completed primitive image returns that element. -/
@[simp]
theorem completedPrimitiveEquiv_symm_completedLieToU (z : d.completedLie ℒ)
    (hz : d.completedLieToU ℒ z ∈
      (d.envelopingFiltration ℒ).completedPrimitiveSubmodule R
        (d.envelopingFiltration_ideal_le_comap_comul ℒ)
        (d.envelopingFiltration_one_le_ker_counit ℒ)) :
    (d.completedPrimitiveEquiv ℒ).symm ⟨d.completedLieToU ℒ z, hz⟩ = z :=
  (d.completedPrimitiveEquiv ℒ).injective (Subtype.ext (by simp))

/-- Applying `completedLieToU` to the inverse of `completedPrimitiveEquiv` recovers the completed
primitive element. -/
@[simp]
theorem completedLieToU_completedPrimitiveEquiv_symm
    (p : (d.envelopingFiltration ℒ).completedPrimitiveSubmodule R
      (d.envelopingFiltration_ideal_le_comap_comul ℒ)
      (d.envelopingFiltration_one_le_ker_counit ℒ)) :
    d.completedLieToU ℒ ((d.completedPrimitiveEquiv ℒ).symm p) = p.val := by
  simpa only [coe_completedPrimitiveEquiv_apply] using
    congrArg Subtype.val ((d.completedPrimitiveEquiv ℒ).apply_symm_apply p)

/-- `completedPrimitiveEquiv` carries the completed Lie bracket to the associative commutator. -/
theorem coe_completedPrimitiveEquiv_lie (x y : d.completedLie ℒ) :
    (d.completedPrimitiveEquiv ℒ ⁅x, y⁆ : (d.envelopingFiltration ℒ).completion) =
      (d.completedPrimitiveEquiv ℒ x : (d.envelopingFiltration ℒ).completion) *
          (d.completedPrimitiveEquiv ℒ y : (d.envelopingFiltration ℒ).completion) -
        (d.completedPrimitiveEquiv ℒ y : (d.envelopingFiltration ℒ).completion) *
          (d.completedPrimitiveEquiv ℒ x : (d.envelopingFiltration ℒ).completion) := by
  simpa only [coe_completedPrimitiveEquiv_apply, LieRing.of_associative_ring_bracket] using
    (d.completedLieToU ℒ).map_lie x y

/-- The inverse of `completedPrimitiveEquiv` carries the associative commutator of two completed
primitive elements to their Lie bracket in `d.completedLie ℒ`. -/
theorem completedPrimitiveEquiv_symm_commutator
    (p q : (d.envelopingFiltration ℒ).completedPrimitiveSubmodule R
      (d.envelopingFiltration_ideal_le_comap_comul ℒ)
      (d.envelopingFiltration_one_le_ker_counit ℒ)) :
    (d.completedPrimitiveEquiv ℒ).symm ⟨p.val * q.val - q.val * p.val,
        ((d.envelopingFiltration ℒ).mem_completedPrimitiveSubmodule R _ _).mpr
          ((((d.envelopingFiltration ℒ).mem_completedPrimitiveSubmodule R _ _).mp
              p.property).commutator
            (((d.envelopingFiltration ℒ).mem_completedPrimitiveSubmodule R _ _).mp q.property))⟩ =
      ⁅(d.completedPrimitiveEquiv ℒ).symm p, (d.completedPrimitiveEquiv ℒ).symm q⁆ := by
  apply (d.completedPrimitiveEquiv ℒ).injective
  exact Subtype.ext (by simp [d.coe_completedPrimitiveEquiv_lie ℒ])

end Primitive

section Exp

variable {N : Type u} {R : Type} {L : Type v}
  [AddCommMonoid N] [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [Algebra ℚ (_root_.UniversalEnvelopingAlgebra R L)]
  [SMulCommClass R ℚ (_root_.UniversalEnvelopingAlgebra R L)]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- `completedExp` after `completedLieToU` identifies the completed positively graded Lie algebra
with the completed group-like elements of the completed universal enveloping algebra. -/
noncomputable def completedLieExpEquiv :
    d.completedLie ℒ ≃
      {u : (d.envelopingFiltration ℒ).completion //
        (d.envelopingFiltration ℒ).IsCompletedGroupLike R
          (d.envelopingFiltration_ideal_le_comap_comul ℒ)
          (d.envelopingFiltration_one_le_ker_counit ℒ) u} :=
  (d.completedPrimitiveEquiv ℒ).toEquiv.trans <|
    (Equiv.subtypeEquivRight fun _ =>
      (d.envelopingFiltration ℒ).mem_completedPrimitiveSubmodule R _ _).trans <|
      (d.envelopingFiltration ℒ).completedExpPrimitiveEquivOfKerLe R
        (d.envelopingFiltration_ideal_le_comap_comul ℒ)
        (d.envelopingFiltration_one_le_ker_counit ℒ)
        (d.ker_counit_le_envelopingFiltration_one ℒ)

@[simp]
theorem coe_completedLieExpEquiv_apply (z : d.completedLie ℒ) :
    (d.completedLieExpEquiv ℒ z : (d.envelopingFiltration ℒ).completion) =
      (d.envelopingFiltration ℒ).completedExp
        ⟨d.completedLieToU ℒ z, d.completedLieToU_mem_completionIdeal_one ℒ z⟩ := by
  simp [completedLieExpEquiv]

/-- The completed Baker–Campbell–Hausdorff product of two elements of `d.completedLie ℒ`, defined
by multiplying their exponentials in the completed enveloping algebra, taking the completed
logarithm, and pulling back along `completedPrimitiveEquiv`. -/
noncomputable def completedLieBCH (x y : d.completedLie ℒ) : d.completedLie ℒ :=
  (d.completedPrimitiveEquiv ℒ).symm
    ⟨(d.envelopingFiltration ℒ).completedLog
        ⟨(d.envelopingFiltration ℒ).completedExp
            ⟨d.completedLieToU ℒ x, d.completedLieToU_mem_completionIdeal_one ℒ x⟩ *
          (d.envelopingFiltration ℒ).completedExp
            ⟨d.completedLieToU ℒ y, d.completedLieToU_mem_completionIdeal_one ℒ y⟩,
          (d.envelopingFiltration ℒ).completedExp_mul_completedExp_sub_one_mem _ _⟩,
      ((d.envelopingFiltration ℒ).mem_completedPrimitiveSubmodule R _ _).mpr <|
        (d.envelopingFiltration ℒ).isCompletedPrimitive_completedLog_completedExp_mul_completedExp R
          (d.envelopingFiltration_ideal_le_comap_comul ℒ)
          (d.envelopingFiltration_one_le_ker_counit ℒ)
          (x := ⟨d.completedLieToU ℒ x, d.completedLieToU_mem_completionIdeal_one ℒ x⟩)
          (y := ⟨d.completedLieToU ℒ y, d.completedLieToU_mem_completionIdeal_one ℒ y⟩)
          (d.isCompletedPrimitive_completedLieToU ℒ x)
          (d.isCompletedPrimitive_completedLieToU ℒ y)⟩

/-- `completedLieToU` sends `completedLieBCH x y` to `log (exp x * exp y)` in the completed
enveloping algebra. -/
@[simp]
theorem completedLieToU_completedLieBCH (x y : d.completedLie ℒ) :
    d.completedLieToU ℒ (d.completedLieBCH ℒ x y) =
      (d.envelopingFiltration ℒ).completedLog
        ⟨(d.envelopingFiltration ℒ).completedExp
            ⟨d.completedLieToU ℒ x, d.completedLieToU_mem_completionIdeal_one ℒ x⟩ *
          (d.envelopingFiltration ℒ).completedExp
            ⟨d.completedLieToU ℒ y, d.completedLieToU_mem_completionIdeal_one ℒ y⟩,
          (d.envelopingFiltration ℒ).completedExp_mul_completedExp_sub_one_mem _ _⟩ :=
  d.completedLieToU_completedPrimitiveEquiv_symm ℒ _

/-- Exponentiating `completedLieBCH x y` in the completed enveloping algebra recovers the product
of the exponentials of `x` and `y`. -/
theorem completedExp_completedLieBCH (x y : d.completedLie ℒ) :
    (d.envelopingFiltration ℒ).completedExp
        ⟨d.completedLieToU ℒ (d.completedLieBCH ℒ x y),
          d.completedLieToU_mem_completionIdeal_one ℒ _⟩ =
      (d.envelopingFiltration ℒ).completedExp
          ⟨d.completedLieToU ℒ x, d.completedLieToU_mem_completionIdeal_one ℒ x⟩ *
        (d.envelopingFiltration ℒ).completedExp
          ⟨d.completedLieToU ℒ y, d.completedLieToU_mem_completionIdeal_one ℒ y⟩ := by
  simp only [completedLieToU_completedLieBCH, AlgFiltration.completedExp_completedLog]

/-- The completed Baker–Campbell–Hausdorff product is associative, inherited from associativity of
multiplication in the completed enveloping algebra. -/
theorem completedLieBCH_assoc (x y z : d.completedLie ℒ) :
    d.completedLieBCH ℒ (d.completedLieBCH ℒ x y) z =
      d.completedLieBCH ℒ x (d.completedLieBCH ℒ y z) :=
  (d.completedLieExpEquiv ℒ).injective <| Subtype.ext <| by
    simp only [coe_completedLieExpEquiv_apply, completedExp_completedLieBCH, mul_assoc]

end Exp

end TauCeti.PositiveDegrees
