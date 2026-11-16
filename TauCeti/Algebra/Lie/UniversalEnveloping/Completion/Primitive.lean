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

Over a commutative rational algebra `R : Type`, the canonical Lie homomorphism
`TauCeti.PositiveDegrees.completedLieToU` identifies the completed positively graded Lie algebra
`d.completedLie ℒ` with the completed primitive elements of the completed universal enveloping
algebra `(d.envelopingFiltration ℒ).completion`, with no freeness, flatness, or finite-rank
hypothesis on the Lie algebra `L`:

* `TauCeti.PositiveDegrees.isCompletedPrimitive_iff_mem_range_completedLieToU`: an element of the
  completed enveloping algebra is completed primitive if and only if it lies in the range of
  `d.completedLieToU ℒ`.
* `TauCeti.PositiveDegrees.completedPrimitiveEquiv`: the resulting `R`-linear equivalence between
  `d.completedLie ℒ` and the completed primitive submodule, sending the Lie bracket to the
  associative commutator.

When `U(L)` carries a compatible `ℚ`-algebra structure (in particular when `R = ℚ`), combining
`completedPrimitiveEquiv` with `TauCeti.AlgFiltration.completedExpPrimitiveEquivOfKerLe` identifies
`d.completedLie ℒ` via `completedExp` and `completedLog` with the completed group-like elements
(`TauCeti.PositiveDegrees.completedLieExpEquiv`) and defines the completed Baker–Campbell–Hausdorff
product `TauCeti.PositiveDegrees.completedLieBCH` on `d.completedLie ℒ`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter II, §6.
* E. Petracci, *Universal representations of Lie algebras by coderivations*
  (arXiv:math/0303020), §8.
* D. Quillen, *Rational homotopy theory*, Ann. of Math. (2) **90** (1969), Appendix A.
* J.-P. Serre, *Lie Algebras and Lie Groups*, Part I, Chapter IV.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe v

/-- Over a commutative rational algebra `R : Type`, the canonical map `ι : L → U(L)` is injective,
without a freeness or flatness assumption on `L`. -/
theorem ι_injective_of_rat (R : Type) (L : Type v) [CommRing R] [Algebra ℚ R]
    [LieRing L] [LieAlgebra R L] :
    Function.Injective (_root_.UniversalEnvelopingAlgebra.ι R :
      L → _root_.UniversalEnvelopingAlgebra R L) :=
  fun _ _ h => (primitiveEquiv R L).injective <| Subtype.ext <| by
    simpa only [coe_primitiveEquiv_apply] using h

end TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.PositiveDegrees

open _root_.UniversalEnvelopingAlgebra TauCeti.UniversalEnvelopingAlgebra

universe u v

section CompletionMk

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

private noncomputable def spanSingletonLieHom {M : Type*} [LieRing M] [LieAlgebra R M]
    (m : M) : R →ₗ⁅R⁆ M where
  toLinearMap := LinearMap.toSpanSingleton R M m
  map_lie' {r s} := by
    rw [LieRing.of_associative_ring_bracket, mul_comm, sub_self]
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.toSpanSingleton_apply,
      zero_smul, smul_lie, lie_smul, lie_self, smul_zero]

@[simp]
private theorem spanSingletonLieHom_apply {M : Type*} [LieRing M] [LieAlgebra R M]
    (m : M) (r : R) : spanSingletonLieHom (R := R) m r = r • m := (rfl)

private noncomputable def lieIdealCompletionMk {I : ℕ → LieIdeal R L} (hI : Antitone I)
    (y : ∀ k, L ⧸ I k)
    (hy : ∀ k, LieIdeal.factor (hI (Nat.le_succ k)) (y (k + 1)) = y k) :
    LieIdeal.completion I hI :=
  LieIdeal.completionLift I hI (fun k => spanSingletonLieHom (y k))
    (fun k => LieHom.ext fun r => by
      simpa only [LieHom.coe_comp, Function.comp_apply, spanSingletonLieHom_apply,
        map_smul] using congrArg (r • ·) (hy k)) 1

private theorem completionProjection_lieIdealCompletionMk {I : ℕ → LieIdeal R L}
    (hI : Antitone I) (y : ∀ k, L ⧸ I k)
    (hy : ∀ k, LieIdeal.factor (hI (Nat.le_succ k)) (y (k + 1)) = y k) (k : ℕ) :
    LieIdeal.completionProjection I hI k (lieIdealCompletionMk hI y hy) = y k := by
  simp [lieIdealCompletionMk]

end CompletionMk

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
  refine ⟨b, ?_, ?_⟩
  · have hsum := Finset.sum_filter_add_sum_filter_not
      (s := (DirectSum.decompose H a).support) (p := fun n => d.degree n ≤ k)
      (f := fun n => (DirectSum.decompose H a n : U))
    have ha_eq := (DirectSum.sum_support_decompose H a).symm
    have hdiff : a - b = ∑ n ∈ (DirectSum.decompose H a).support with ¬ d.degree n ≤ k,
        (DirectSum.decompose H a n : U) :=
      (eq_sub_of_add_eq' (by simpa only [b] using hsum.trans ha_eq.symm)).symm
    rw [hdiff]
    refine Submodule.sum_mem _ fun n hn => ?_
    have hn' : ¬ d.degree n ≤ k := (Finset.mem_filter.mp hn).2
    exact d.mem_envelopingFiltration_of_mem_homogeneousSubmodule ℒ
      (DirectSum.decompose H a n).property (by omega)
  · intro m hm
    simp only [b]
    rw [← DirectSum.decomposeLinearEquiv_apply, map_sum, _root_.DirectSum.sum_apply,
      Submodule.coe_sum]
    refine Finset.sum_eq_zero fun n hn => ?_
    have hnk : d.degree n ≤ k := (Finset.mem_filter.mp hn).2
    rw [DirectSum.decomposeLinearEquiv_apply]
    exact DirectSum.decompose_of_mem_ne H (DirectSum.decompose H a n).property
      (fun hnm => by subst hnm; omega)

private theorem exists_truncatedLieToU_eq_projection
    {u : (d.envelopingFiltration ℒ).completion}
    (hu : (d.envelopingFiltration ℒ).IsCompletedPrimitive R
      (d.envelopingFiltration_ideal_le_comap_comul ℒ)
      (d.envelopingFiltration_one_le_ker_counit ℒ) u)
    (k : ℕ) :
    ∃ y : d.truncatedLie ℒ k, d.truncatedLieToU ℒ k y =
      (d.envelopingFiltration ℒ).projection k u := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((d.envelopingFiltration ℒ).projection k u)
  obtain ⟨b, hab, hdeg⟩ := d.exists_sub_mem_envelopingFiltration_of_degree_le ℒ a k
  have hbu : u - (d.envelopingFiltration ℒ).toCompletion b ∈
      (d.envelopingFiltration ℒ).completionIdeal (k + 1) := by
    rw [AlgFiltration.completionIdeal_succ, RingHom.mem_ker, map_sub,
      AlgFiltration.projection_toCompletion, ← ha, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hab
  have hb_prim : Bialgebra.IsPrimitiveElem R b :=
    d.isPrimitiveElem_of_mem_envelopingFiltration_tensorProduct_succ ℒ hdeg
      ((d.envelopingFiltration ℒ).comul_sub_mem_of_isCompletedPrimitive_of_sub_mem
        (d.envelopingFiltration_ideal_le_comap_comul ℒ)
        (d.envelopingFiltration_one_le_ker_counit ℒ) hu hbu)
  obtain ⟨x, hx⟩ :=
    (_root_.UniversalEnvelopingAlgebra.isPrimitiveElem_iff_mem_range_ι b).mp hb_prim
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
  constructor
  · intro hu
    choose y hy using d.exists_truncatedLieToU_eq_projection ℒ hu
    have hcompat (k : ℕ) :
        LieIdeal.factor (d.degreeIdeal_antitone ℒ (Nat.le_succ k)) (y (k + 1)) = y k := by
      apply d.truncatedLieToU_injective_of_rat ℒ k
      rw [← d.factor_truncatedLieToU ℒ (Nat.le_succ k) (y (k + 1)), hy (k + 1),
        (d.envelopingFiltration ℒ).factor_projection (Nat.le_succ k) u, hy k]
    refine ⟨lieIdealCompletionMk (d.degreeIdeal_antitone ℒ) y hcompat, ?_⟩
    apply (d.envelopingFiltration ℒ).completion_ext
    intro k
    rw [projection_completedLieToU, completionProjection_lieIdealCompletionMk, hy k]
  · rintro ⟨z, rfl⟩
    exact d.isCompletedPrimitive_completedLieToU ℒ z

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
    ⟨(LinearMap.injective_codRestrict_iff _).mpr (d.completedLieToU_injective_of_rat ℒ),
      fun p => by
        obtain ⟨z, hz⟩ := (d.isCompletedPrimitive_iff_mem_range_completedLieToU ℒ p.val).mp
          (((d.envelopingFiltration ℒ).mem_completedPrimitiveSubmodule R _ _).mp p.property)
        exact ⟨z, Subtype.ext hz⟩⟩

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
    (d.completedPrimitiveEquiv ℒ).symm ⟨d.completedLieToU ℒ z, hz⟩ = z := by
  apply (d.completedPrimitiveEquiv ℒ).injective
  apply Subtype.ext
  simp

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
    (d.completedPrimitiveEquiv ℒ).symm
        ⟨p.val * q.val - q.val * p.val,
          ((d.envelopingFiltration ℒ).mem_completedPrimitiveSubmodule R _ _).mpr
            ((((d.envelopingFiltration ℒ).mem_completedPrimitiveSubmodule R _ _).mp
                p.property).commutator
              (((d.envelopingFiltration ℒ).mem_completedPrimitiveSubmodule R _ _).mp
                q.property))⟩ =
      ⁅(d.completedPrimitiveEquiv ℒ).symm p, (d.completedPrimitiveEquiv ℒ).symm q⁆ := by
  apply (d.completedPrimitiveEquiv ℒ).injective
  apply Subtype.ext
  rw [d.coe_completedPrimitiveEquiv_lie ℒ]
  simp only [LinearEquiv.apply_symm_apply]

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
  simp only [completedLieExpEquiv, Equiv.trans_apply, LinearEquiv.coe_toEquiv,
    Equiv.subtypeEquivRight_apply_coe, AlgFiltration.coe_completedExpPrimitiveEquivOfKerLe,
    coe_completedPrimitiveEquiv_apply]

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
        (d.envelopingFiltration ℒ).isCompletedPrimitive_completedLog_completedExp_mul_completedExp
          R (d.envelopingFiltration_ideal_le_comap_comul ℒ)
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
          (d.envelopingFiltration ℒ).completedExp_mul_completedExp_sub_one_mem _ _⟩ := by
  rw [completedLieBCH, d.completedLieToU_completedPrimitiveEquiv_symm ℒ]

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
      d.completedLieBCH ℒ x (d.completedLieBCH ℒ y z) := by
  apply (d.completedLieExpEquiv ℒ).injective
  apply Subtype.ext
  simp only [coe_completedLieExpEquiv_apply, completedExp_completedLieBCH, mul_assoc]

end Exp

end TauCeti.PositiveDegrees
