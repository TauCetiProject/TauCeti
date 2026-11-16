/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Graded.Completion
public import TauCeti.Algebra.Lie.UniversalEnveloping.DegreeFiltration
public import TauCeti.Algebra.Lie.UniversalEnveloping.Primitive
public import TauCeti.LinearAlgebra.TensorProduct.Decomposition
public import TauCeti.RingTheory.FilteredAlgebra.Bialgebra

import TauCeti.Algebra.DirectSum.Internal

/-!
# Completed universal enveloping algebras and primitive classification

For a graded Lie algebra `L = ⨁ n, ℒ n` over a commutative ring `R`, the tensor square
`U(L) ⊗[R] U(L)` carries the total-degree internal direct-sum decomposition
`TauCeti.UniversalEnvelopingAlgebra.tensorHomogeneousSubmodule`, with no freeness or flatness
assumption. The coproduct preserves total degree, so whenever `d : Γ →+ ℤ` assigns nonnegative
degrees to all nonzero pieces of `L`, the degree filtration `degreeFiltration ℒ d hneg` is a
bialgebra filtration (`TauCeti.UniversalEnvelopingAlgebra.degreeFiltration_isBialgebraFiltration`),
and its tensor-product filtration ideals are the degree tails of `tensorHomogeneousSubmodule ℒ`.
Consequently, an element of the completed enveloping algebra is completed primitive if and only if
every finite-order representative has ordinary primitive homogeneous components up to that order.

For a positively graded Lie algebra (`d : PositiveDegrees N`, `[IsPositiveGrading d ℒ]`), the
canonical Lie inclusion `ι : L → U(L)` induces Lie homomorphisms
`TauCeti.UniversalEnvelopingAlgebra.truncatedLieToU` at every finite cutoff and a completed Lie
homomorphism `TauCeti.UniversalEnvelopingAlgebra.completedLieToU : d.completedLie ℒ →ₗ⁅R⁆
completedEnveloping d ℒ` landing in the completed primitive elements.

Over a commutative rational algebra (`R : Type`, `[Algebra ℚ R]`), `completedLieToU` is injective
and identifies `d.completedLie ℒ` with the `R`-submodule of all completed primitive elements of
`completedEnveloping d ℒ` (`isCompletedPrimitive_iff_mem_range_completedLieToU` and
`completedLieEquivCompletedPrimitive`). When `U(L)` also carries `[Algebra ℚ U(L)]`, composing
with the completed exponential gives a bijection `completedLieEquivCompletedGroupLike` between
`d.completedLie ℒ` and the completed group-like elements of `completedEnveloping d ℒ`.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.tensorHomogeneousSubmodule`: total-degree decomposition of
  `U(L) ⊗[R] U(L)`.
* `TauCeti.UniversalEnvelopingAlgebra.degreeFiltration_isBialgebraFiltration`: bialgebra filtration
  instance for the degree filtration on `U(L)`.
* `TauCeti.UniversalEnvelopingAlgebra.positiveDegreeFiltration` and
  `TauCeti.UniversalEnvelopingAlgebra.completedEnveloping`: the degree filtration and completed
  enveloping algebra associated to a positive grading.
* `TauCeti.UniversalEnvelopingAlgebra.truncatedLieToU` and
  `TauCeti.UniversalEnvelopingAlgebra.completedLieToU`: finite-cutoff and completed Lie maps from
  a positively graded Lie algebra into its completed enveloping algebra.
* `TauCeti.UniversalEnvelopingAlgebra.completedLieEquivCompletedPrimitive` and
  `TauCeti.UniversalEnvelopingAlgebra.completedLieEquivCompletedGroupLike`: identification of
  `d.completedLie ℒ` with completed primitives and completed group-like elements over a commutative
  `ℚ`-algebra.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

section TensorGrading

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The total-degree-`n` submodule of `U(L) ⊗[R] U(L)`, spanned by pure tensors of homogeneous
elements whose degrees sum to `n`. -/
def tensorHomogeneousSubmodule (n : Γ) : Submodule R (U ⊗[R] U) :=
  ⨆ p : Γ × Γ, ⨆ (_ : p.1 + p.2 = n),
    Submodule.map₂ (TensorProduct.mk R U U) (homogeneousSubmodule ℒ p.1)
      (homogeneousSubmodule ℒ p.2)

/-- Pure tensors of homogeneous elements belong to the sum of their degrees. -/
theorem tmul_mem_tensorHomogeneousSubmodule {i j : Γ} {a b : U}
    (ha : a ∈ homogeneousSubmodule ℒ i) (hb : b ∈ homogeneousSubmodule ℒ j) :
    a ⊗ₜ[R] b ∈ tensorHomogeneousSubmodule ℒ (i + j) :=
  Submodule.mem_iSup_of_mem (i, j) (by rw [iSup_pos rfl]; exact Submodule.apply_mem_map₂ _ ha hb)

/-- The total-degree pieces of `U(L) ⊗[R] U(L)` form a graded monoid. -/
instance tensorHomogeneousSubmodule_gradedMonoid :
    SetLike.GradedMonoid (tensorHomogeneousSubmodule ℒ) where
  one_mem := by
    have h := tmul_mem_tensorHomogeneousSubmodule ℒ
      (SetLike.GradedOne.one_mem (A := homogeneousSubmodule ℒ))
      (SetLike.GradedOne.one_mem (A := homogeneousSubmodule ℒ))
    simpa only [add_zero, Algebra.TensorProduct.one_def] using h
  mul_mem {m n x y} hx hy := by
    have hright : tensorHomogeneousSubmodule ℒ m ≤
        (tensorHomogeneousSubmodule ℒ (m + n)).comap (LinearMap.mulRight R y) := by
      rw [tensorHomogeneousSubmodule]
      refine iSup_le fun p => iSup_le fun hp => Submodule.map₂_le.mpr fun a₁ ha₁ a₂ ha₂ => ?_
      change (a₁ ⊗ₜ[R] a₂) * y ∈ tensorHomogeneousSubmodule ℒ (m + n)
      have hleft : tensorHomogeneousSubmodule ℒ n ≤
          (tensorHomogeneousSubmodule ℒ (m + n)).comap
            (LinearMap.mulLeft R (a₁ ⊗ₜ[R] a₂)) := by
        rw [tensorHomogeneousSubmodule]
        refine iSup_le fun q => iSup_le fun hq => Submodule.map₂_le.mpr fun b₁ hb₁ b₂ hb₂ => ?_
        change (a₁ ⊗ₜ[R] a₂) * (b₁ ⊗ₜ[R] b₂) ∈ tensorHomogeneousSubmodule ℒ (m + n)
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        have hdeg : (p.1 + q.1) + (p.2 + q.2) = m + n := by
          rw [add_add_add_comm, hp, hq]
        rw [← hdeg]
        exact tmul_mem_tensorHomogeneousSubmodule ℒ
          (SetLike.mul_mem_graded ha₁ hb₁) (SetLike.mul_mem_graded ha₂ hb₂)
      exact hleft hy
    exact hright hx

/-- The coproduct of `U(L)` preserves total Lie degree. -/
theorem comul_mem_tensorHomogeneousSubmodule {n : Γ} {a : U}
    (ha : a ∈ homogeneousSubmodule ℒ n) :
    Coalgebra.comul (R := R) a ∈ tensorHomogeneousSubmodule ℒ n := by
  have hword (l : List (Σ i, ℒ i)) :
      Coalgebra.comul (R := R) (l.map (fun x => ι R (x.2 : L))).prod ∈
        tensorHomogeneousSubmodule ℒ (l.map Sigma.fst).sum := by
    induction l with
    | nil =>
      simp only [List.map_nil, List.prod_nil, List.sum_nil, Bialgebra.comul_one]
      exact SetLike.GradedOne.one_mem
    | cons x l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, Bialgebra.comul_mul]
      have hx : Coalgebra.comul (R := R) (ι R (x.2 : L)) ∈
          tensorHomogeneousSubmodule ℒ x.1 := by
        rw [comul_ι]
        refine add_mem ?_ ?_
        · simpa only [add_zero] using tmul_mem_tensorHomogeneousSubmodule ℒ
            (ι_mem_homogeneousSubmodule ℒ x.2.property)
            (SetLike.GradedOne.one_mem (A := homogeneousSubmodule ℒ))
        · simpa only [zero_add] using tmul_mem_tensorHomogeneousSubmodule ℒ
            (SetLike.GradedOne.one_mem (A := homogeneousSubmodule ℒ))
            (ι_mem_homogeneousSubmodule ℒ x.2.property)
      exact SetLike.mul_mem_graded hx ih
  have hle : homogeneousSubmodule ℒ n ≤
      (tensorHomogeneousSubmodule ℒ n).comap (Bialgebra.comulAlgHom R U).toLinearMap := by
    rw [homogeneousSubmodule_le_iff]
    intro l hl
    simpa only [Submodule.mem_comap, AlgHom.toLinearMap_apply, Bialgebra.comulAlgHom_apply,
      hl] using hword l
  exact hle ha

variable [DecidableEq Γ] [GradedLieAlgebra ℒ]

/-- The total-degree pieces of `U(L) ⊗[R] U(L)` form an internal direct sum over any commutative
ring, without a freeness or flatness assumption. -/
theorem isInternal_tensorHomogeneousSubmodule :
    _root_.DirectSum.IsInternal (tensorHomogeneousSubmodule ℒ) :=
  ((isInternal_homogeneousSubmodule ℒ).tensorProduct
    (homogeneousSubmodule ℒ) (homogeneousSubmodule ℒ)
    (isInternal_homogeneousSubmodule ℒ)).iSup_fiber (fun p : Γ × Γ => p.1 + p.2)

/-- The internal direct-sum decomposition of `U(L) ⊗[R] U(L)` by total Lie degree. -/
noncomputable instance instDecompositionTensorHomogeneousSubmodule :
    _root_.DirectSum.Decomposition (tensorHomogeneousSubmodule ℒ) :=
  (isInternal_tensorHomogeneousSubmodule ℒ).chooseDecomposition

variable (d : Γ →+ ℤ)

/-- The tensor-product filtration ideals of `degreeFiltration` agree with the degree tails of the
total-degree decomposition of `U(L) ⊗[R] U(L)`. -/
theorem tensorProduct_degreeFiltration_ideal_restrictScalars
    (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (k : ℕ) :
    (((degreeFiltration ℒ d hneg).tensorProduct R
        (degreeFiltration ℒ d hneg)).ideal k).restrictScalars R =
      TauCeti.DirectSum.degreeTail (tensorHomogeneousSubmodule ℒ) d k := by
  let F := degreeFiltration ℒ d hneg
  have hF (m : ℕ) : (F.ideal m).restrictScalars R =
      TauCeti.DirectSum.degreeTail (homogeneousSubmodule ℒ) d m := by
    rw [degreeFiltration_ideal, TauCeti.GradedAlgebra.degreeIdeal_restrictScalars]
  apply le_antisymm
  · have hmem : ((F.tensorProduct R F).ideal k).restrictScalars R =
        tensorFiltrationTail (fun m => (F.ideal m).restrictScalars R)
          (fun m => (F.ideal m).restrictScalars R) k := by
      ext t
      exact F.mem_tensorProduct_ideal_iff R F
    rw [hmem, tensorFiltrationTail_le_iff]
    intro a b hab x hx y hy
    change x ∈ (F.ideal a).restrictScalars R at hx
    change y ∈ (F.ideal b).restrictScalars R at hy
    rw [hF a] at hx
    rw [hF b] at hy
    have hleft : TauCeti.DirectSum.degreeTail (homogeneousSubmodule ℒ) d a ≤
        (TauCeti.DirectSum.degreeTail (tensorHomogeneousSubmodule ℒ) d k).comap
          ((TensorProduct.mk R U U).flip y) := by
      rw [TauCeti.DirectSum.degreeTail_def]
      refine iSup_le fun i => iSup_le fun hi x' hx' => ?_
      change x' ⊗ₜ[R] y ∈ TauCeti.DirectSum.degreeTail (tensorHomogeneousSubmodule ℒ) d k
      have hright : TauCeti.DirectSum.degreeTail (homogeneousSubmodule ℒ) d b ≤
          (TauCeti.DirectSum.degreeTail (tensorHomogeneousSubmodule ℒ) d k).comap
            (TensorProduct.mk R U U x') := by
        rw [TauCeti.DirectSum.degreeTail_def]
        refine iSup_le fun j => iSup_le fun hj y' hy' => ?_
        change x' ⊗ₜ[R] y' ∈ TauCeti.DirectSum.degreeTail (tensorHomogeneousSubmodule ℒ) d k
        refine TauCeti.DirectSum.le_degreeTail (tensorHomogeneousSubmodule ℒ) d ?_
          (tmul_mem_tensorHomogeneousSubmodule ℒ hx' hy')
        rw [map_add]
        omega
      exact hright hy
    exact hleft hx
  · rw [TauCeti.DirectSum.degreeTail_def]
    refine iSup_le fun n => iSup_le fun hn => ?_
    rw [tensorHomogeneousSubmodule]
    refine iSup_le fun p => iSup_le fun hp => Submodule.map₂_le.mpr fun x hx y hy => ?_
    change x ⊗ₜ[R] y ∈ (F.tensorProduct R F).ideal k
    by_cases h1 : d p.1 < 0
    · have hx0 : x = 0 := by
        simpa only [homogeneousSubmodule_eq_bot_of_degree_neg ℒ d hneg h1,
          Submodule.mem_bot] using hx
      simp [hx0]
    · by_cases h2 : d p.2 < 0
      · have hy0 : y = 0 := by
          simpa only [homogeneousSubmodule_eq_bot_of_degree_neg ℒ d hneg h2,
            Submodule.mem_bot] using hy
        simp [hy0]
      · have hsum : d p.1 + d p.2 = d n := by rw [← map_add, hp]
        exact F.tmul_mem_tensorProduct_ideal R F
          (a := (d p.1).toNat) (b := (d p.2).toNat) (by omega)
          (mem_degreeFiltration_ideal_of_mem_homogeneousSubmodule ℒ d hneg hx (by omega))
          (mem_degreeFiltration_ideal_of_mem_homogeneousSubmodule ℒ d hneg hy (by omega))

/-- The degree filtration on `U(L)` is a bialgebra filtration whenever all negative-degree pieces
of `L` vanish. -/
instance degreeFiltration_isBialgebraFiltration (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    (degreeFiltration ℒ d hneg).IsBialgebraFiltration R where
  comul_le k := by
    rw [degreeFiltration_ideal_le_iff]
    intro n hn a ha
    have hmem : Coalgebra.comul (R := R) a ∈
        TauCeti.DirectSum.degreeTail (tensorHomogeneousSubmodule ℒ) d k :=
      TauCeti.DirectSum.le_degreeTail (tensorHomogeneousSubmodule ℒ) d hn
        (comul_mem_tensorHomogeneousSubmodule ℒ ha)
    rw [← tensorProduct_degreeFiltration_ideal_restrictScalars ℒ d hneg k] at hmem
    exact hmem
  counit_le := by
    rw [← HopfIdeal.augmentation_toIdeal R U]
    exact degreeFiltration_le_augmentation ℒ d hneg Nat.zero_lt_one

/-- For a strictly positive Lie grading, the first degree-filtration ideal equals the augmentation
ideal. -/
theorem degreeFiltration_ideal_one_eq_augmentation (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) :
    (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).ideal 1 =
      (HopfIdeal.augmentation R U).toIdeal :=
  le_antisymm (degreeFiltration_le_augmentation ℒ d _ Nat.zero_lt_one)
    (augmentation_le_degreeFiltration_one ℒ d hpos)

/-- For a strictly positive Lie grading, the kernel of the counit equals the first
degree-filtration ideal. -/
theorem ker_counitAlgHom_eq_degreeFiltration_one (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) :
    RingHom.ker (Bialgebra.counitAlgHom R U) =
      (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).ideal 1 := by
  rw [← HopfIdeal.augmentation_toIdeal R U, degreeFiltration_ideal_one_eq_augmentation ℒ d hpos]

/-- The primitive-defect linear map `a ↦ Δ(a) - (a ⊗ 1 + 1 ⊗ a)` on `U(L)`. -/
private noncomputable def primitiveDefect : U →ₗ[R] U ⊗[R] U :=
  (Bialgebra.comulAlgHom R U).toLinearMap -
    ((Algebra.TensorProduct.includeLeft : U →ₐ[R] U ⊗[R] U).toLinearMap +
      (Algebra.TensorProduct.includeRight : U →ₐ[R] U ⊗[R] U).toLinearMap)

private theorem primitiveDefect_apply (a : U) :
    primitiveDefect (R := R) (L := L) a =
      Coalgebra.comul (R := R) a - (a ⊗ₜ[R] (1 : U) + (1 : U) ⊗ₜ[R] a) := rfl

private theorem primitiveDefect_eq_zero_iff (a : U) :
    primitiveDefect (R := R) (L := L) a = 0 ↔ Bialgebra.IsPrimitiveElem R a := by
  rw [primitiveDefect_apply, sub_eq_zero, Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul,
    add_comm (a ⊗ₜ[R] (1 : U))]

omit [DecidableEq Γ] [GradedLieAlgebra ℒ] in
private theorem primitiveDefect_mem_tensorHomogeneousSubmodule {n : Γ} {a : U}
    (ha : a ∈ homogeneousSubmodule ℒ n) :
    primitiveDefect (R := R) (L := L) a ∈ tensorHomogeneousSubmodule ℒ n := by
  rw [primitiveDefect_apply]
  refine sub_mem (comul_mem_tensorHomogeneousSubmodule ℒ ha) (add_mem ?_ ?_)
  · simpa only [add_zero] using tmul_mem_tensorHomogeneousSubmodule ℒ ha
      (SetLike.GradedOne.one_mem (A := homogeneousSubmodule ℒ))
  · simpa only [zero_add] using tmul_mem_tensorHomogeneousSubmodule ℒ
      (SetLike.GradedOne.one_mem (A := homogeneousSubmodule ℒ)) ha

/-- An element of the completed enveloping algebra is completed primitive if and only if for every
finite cutoff `k` and every order-`k` representative `a : U(L)`, each homogeneous component of `a`
of degree at most `k` is an ordinary primitive element of `U(L)`. -/
theorem isCompletedPrimitive_iff_forall_isPrimitiveElem_decompose
    (hneg : ∀ n, d n < 0 → ℒ n = ⊥) {u : (degreeFiltration ℒ d hneg).completion} :
    (degreeFiltration ℒ d hneg).IsCompletedPrimitive R u ↔
      ∀ (k : ℕ) (a : U),
        Ideal.Quotient.mk ((degreeFiltration ℒ d hneg).ideal (k + 1)) a =
          (degreeFiltration ℒ d hneg).projection k u →
        ∀ n, d n ≤ k →
          Bialgebra.IsPrimitiveElem R
            (_root_.DirectSum.decompose (homogeneousSubmodule ℒ) a n : U) := by
  let F := degreeFiltration ℒ d hneg
  have hdef_iff (k : ℕ) (a : U) :
      primitiveDefect (R := R) (L := L) a ∈ (F.tensorProduct R F).ideal (k + 1) ↔
        ∀ n, d n ≤ k →
          Bialgebra.IsPrimitiveElem R
            (_root_.DirectSum.decompose (homogeneousSubmodule ℒ) a n : U) := by
    have hmem : primitiveDefect (R := R) (L := L) a ∈ (F.tensorProduct R F).ideal (k + 1) ↔
        primitiveDefect (R := R) (L := L) a ∈
          TauCeti.DirectSum.degreeTail (tensorHomogeneousSubmodule ℒ) d (k + 1) := by
      rw [← tensorProduct_degreeFiltration_ideal_restrictScalars ℒ d hneg (k + 1)]
      exact Iff.rfl
    rw [hmem, TauCeti.DirectSum.mem_degreeTail_iff]
    have hshift (n : Γ) :
        (_root_.DirectSum.decompose (tensorHomogeneousSubmodule ℒ)
            (primitiveDefect (R := R) (L := L) a) n : U ⊗[R] U) =
          primitiveDefect (R := R) (L := L)
            (_root_.DirectSum.decompose (homogeneousSubmodule ℒ) a n : U) :=
      (_root_.DirectSum.map_decompose_shift (homogeneousSubmodule ℒ)
        (tensorHomogeneousSubmodule ℒ) (primitiveDefect (R := R) (L := L)).toAddMonoidHom
        id Function.injective_id
        (fun _ _ hx => primitiveDefect_mem_tensorHomogeneousSubmodule ℒ hx) n a).symm
    refine ⟨fun h n hn => ?_, fun h n hn => ?_⟩
    · rw [← primitiveDefect_eq_zero_iff, ← hshift n]
      exact h n (by omega)
    · rw [hshift n, primitiveDefect_eq_zero_iff]
      exact h n (by omega)
  have hproj_iff (k : ℕ) (a : U) (ha : Ideal.Quotient.mk (F.ideal (k + 1)) a = F.projection k u) :
      (F.tensorProduct R F).projection k (F.completedCoproduct R u) =
        (F.tensorProduct R F).projection k
          (F.includeLeftCompletion R F u + F.includeRightCompletion R F u) ↔
        primitiveDefect (R := R) (L := L) a ∈ (F.tensorProduct R F).ideal (k + 1) := by
    rw [AlgFiltration.projection_completedCoproduct, map_add,
      AlgFiltration.projection_includeLeftCompletion,
      AlgFiltration.projection_includeRightCompletion, ← ha]
    change Ideal.Quotient.mk ((F.tensorProduct R F).ideal (k + 1)) (Coalgebra.comul (R := R) a) =
        Ideal.Quotient.mk ((F.tensorProduct R F).ideal (k + 1)) (a ⊗ₜ[R] (1 : U)) +
          Ideal.Quotient.mk ((F.tensorProduct R F).ideal (k + 1)) ((1 : U) ⊗ₜ[R] a) ↔ _
    rw [← map_add, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, primitiveDefect_apply]
  rw [AlgFiltration.isCompletedPrimitive_iff]
  constructor
  · intro hu k a ha
    refine (hdef_iff k a).mp ((hproj_iff k a ha).mp ?_)
    exact congrArg ((F.tensorProduct R F).projection k) hu
  · intro h
    refine (F.tensorProduct R F).completion_ext fun k => ?_
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection k u)
    exact (hproj_iff k a ha).mpr ((hdef_iff k a).mpr (h k a ha))

end TensorGrading

section PositiveGrading

variable {N R L : Type*} [AddCommMonoid N] [DecidableEq N]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The degree filtration on `U(L)` induced by a positive grading of `L`. -/
noncomputable abbrev positiveDegreeFiltration : AlgFiltration U :=
  degreeFiltration ℒ d.degree (fun n hn => d.eq_bot_of_degree_nonpos ℒ n hn.le)

/-- The completed universal enveloping algebra of a positively graded Lie algebra. -/
noncomputable abbrev completedEnveloping := (positiveDegreeFiltration d ℒ).completion

/-- The canonical Lie homomorphism at cutoff `k` from the truncated Lie algebra into the
order-`k` quotient of the enveloping algebra. -/
noncomputable def truncatedLieToU (k : ℕ) :
    d.truncatedLie ℒ k →ₗ⁅R⁆ U ⧸ (positiveDegreeFiltration d ℒ).ideal (k + 1) :=
  LieIdeal.liftQ _
    ((Ideal.Quotient.mkₐ R ((positiveDegreeFiltration d ℒ).ideal (k + 1))).toLieHom.comp
      (_root_.UniversalEnvelopingAlgebra.ι R))
    (fun x hx => by
      change Ideal.Quotient.mk ((positiveDegreeFiltration d ℒ).ideal (k + 1)) (ι R x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, mem_degreeFiltration_ideal_iff]
      intro n hn
      rw [ι_apply, coe_decompose_mkAlgHom_ι, (d.mem_degreeIdeal_iff ℒ).mp hx n (by omega),
        map_zero])

/-- `truncatedLieToU` sends a quotient class to the class of its canonical enveloping image. -/
@[simp]
theorem truncatedLieToU_mk (k : ℕ) (x : L) :
    truncatedLieToU d ℒ k (LieSubmodule.Quotient.mk x) =
      Ideal.Quotient.mk ((positiveDegreeFiltration d ℒ).ideal (k + 1)) (ι R x) := by
  simp [truncatedLieToU]

/-- The finite-cutoff enveloping maps commute with quotient transition maps. -/
private theorem truncatedLieToU_factor {k l : ℕ} (h : k ≤ l) (x : d.truncatedLie ℒ l) :
    truncatedLieToU d ℒ k (LieIdeal.factor (d.degreeIdeal_antitone ℒ h) x) =
      Ideal.Quotient.factor
        ((positiveDegreeFiltration d ℒ).antitone (Nat.add_le_add_right h 1))
        (truncatedLieToU d ℒ l x) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ l).surjective_mkQ x
  simp [LieIdeal.mkQ_apply, LieIdeal.factor_apply]

/-- The finite-cutoff enveloping maps commute with truncation transitions. -/
theorem truncatedLieToU_truncationMap {k l : ℕ} (h : k ≤ l) (x : d.truncatedLie ℒ l) :
    truncatedLieToU d ℒ k (d.truncationMap ℒ h x) =
      Ideal.Quotient.factor
        ((positiveDegreeFiltration d ℒ).antitone (Nat.add_le_add_right h 1))
        (truncatedLieToU d ℒ l x) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ l).surjective_mkQ x
  simp [LieIdeal.mkQ_apply]

/-- When `ι : L → U(L)` is injective, every finite-cutoff map `truncatedLieToU` is injective. -/
theorem truncatedLieToU_injective (hι : Function.Injective (ι R : L → U)) (k : ℕ) :
    Function.Injective (truncatedLieToU d ℒ k) := by
  rw [truncatedLieToU, LieIdeal.liftQ_injective_iff]
  intro x hx
  have hmem : ι R x ∈ (positiveDegreeFiltration d ℒ).ideal (k + 1) := by
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hx
  have hcomap := comap_degreeFiltration_ι ℒ d.degree
    (fun n hn => d.eq_bot_of_degree_nonpos ℒ n hn.le) hι (k + 1)
  have htail : x ∈ TauCeti.DirectSum.degreeTail ℒ d.degree (k + 1) := by
    rw [← hcomap]
    exact hmem
  rw [d.mem_degreeIdeal_iff ℒ]
  intro n hn
  exact (TauCeti.DirectSum.mem_degreeTail_iff ℒ d.degree).mp htail n (by omega)

/-- The completed Lie homomorphism `d.completedLie ℒ →ₗ⁅R⁆ completedEnveloping d ℒ` induced by the
canonical map `ι : L → U(L)`. -/
noncomputable def completedLieToU : d.completedLie ℒ →ₗ⁅R⁆ completedEnveloping d ℒ where
  toFun x :=
    ⟨fun k => truncatedLieToU d ℒ k.unop
        (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k.unop x),
      ((positiveDegreeFiltration d ℒ).mem_completion_iff _).mpr fun {k l} h => by
        rw [← truncatedLieToU_factor d ℒ h]
        exact congrArg (truncatedLieToU d ℒ k)
          (LieIdeal.factor_completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) h x)⟩
  map_add' x y := (positiveDegreeFiltration d ℒ).completion_ext fun k => by
    simp [AlgFiltration.projection_apply]
  map_smul' r x := (positiveDegreeFiltration d ℒ).completion_ext fun k => by
    rw [← AlgFiltration.projectionₐ_apply (R := R), ← AlgFiltration.projectionₐ_apply (R := R),
      RingHom.id_apply, map_smul, AlgFiltration.projectionₐ_apply, AlgFiltration.projectionₐ_apply]
    simp [AlgFiltration.projection_apply]
  map_lie' {x y} := (positiveDegreeFiltration d ℒ).completion_ext fun k => by
    simp [AlgFiltration.projection_apply, LieRing.of_associative_ring_bracket]

/-- The order-`k` projection of `completedLieToU` is `truncatedLieToU` applied to the order-`k`
Lie projection. -/
@[simp]
theorem projection_completedLieToU (k : ℕ) (x : d.completedLie ℒ) :
    (positiveDegreeFiltration d ℒ).projection k (completedLieToU d ℒ x) =
      truncatedLieToU d ℒ k
        (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k x) := by
  rw [AlgFiltration.projection_apply]
  rfl

/-- `completedLieToU` extends the canonical map `ι : L → U(L)` on canonical elements. -/
@[simp]
theorem completedLieToU_toCompletion (x : L) :
    completedLieToU d ℒ
        (LieIdeal.toCompletion (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) x) =
      (positiveDegreeFiltration d ℒ).toCompletion (ι R x) := by
  refine (positiveDegreeFiltration d ℒ).completion_ext fun k => ?_
  simp [LieIdeal.mkQ_apply]

/-- Every element in the image of `completedLieToU` lies in the first completion ideal. -/
theorem completedLieToU_mem_completionIdeal_one (x : d.completedLie ℒ) :
    completedLieToU d ℒ x ∈ (positiveDegreeFiltration d ℒ).completionIdeal 1 := by
  rw [AlgFiltration.completionIdeal_succ, RingHom.mem_ker, projection_completedLieToU]
  have hz : LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) 0 x = 0 :=
    Subsingleton.elim _ _
  rw [hz, map_zero]

/-- Every element in the image of `completedLieToU` is completed primitive. -/
theorem isCompletedPrimitive_completedLieToU (x : d.completedLie ℒ) :
    (positiveDegreeFiltration d ℒ).IsCompletedPrimitive R (completedLieToU d ℒ x) := by
  let F := positiveDegreeFiltration d ℒ
  rw [AlgFiltration.isCompletedPrimitive_iff]
  refine (F.tensorProduct R F).completion_ext fun k => ?_
  obtain ⟨y, hy⟩ := (d.degreeIdeal ℒ k).surjective_mkQ
    (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k x)
  have hproj : Ideal.Quotient.mk (F.ideal (k + 1)) (ι R y) =
      F.projection k (completedLieToU d ℒ x) := by
    rw [projection_completedLieToU, ← hy, LieIdeal.mkQ_apply, truncatedLieToU_mk]
  rw [AlgFiltration.projection_completedCoproduct, map_add,
    AlgFiltration.projection_includeLeftCompletion,
    AlgFiltration.projection_includeRightCompletion, ← hproj]
  change Ideal.Quotient.mk ((F.tensorProduct R F).ideal (k + 1))
      (Coalgebra.comul (R := R) (ι R y)) =
    Ideal.Quotient.mk ((F.tensorProduct R F).ideal (k + 1)) (ι R y ⊗ₜ[R] (1 : U)) +
      Ideal.Quotient.mk ((F.tensorProduct R F).ideal (k + 1)) ((1 : U) ⊗ₜ[R] ι R y)
  rw [comul_ι, map_add]

/-- When `ι : L → U(L)` is injective, `completedLieToU` is injective. -/
theorem completedLieToU_injective (hι : Function.Injective (ι R : L → U)) :
    Function.Injective (completedLieToU d ℒ) := by
  intro x y hxy
  refine LieIdeal.completion_ext _ _ fun k => ?_
  apply truncatedLieToU_injective d ℒ hι k
  simpa only [projection_completedLieToU] using
    congrArg ((positiveDegreeFiltration d ℒ).projection k) hxy

end PositiveGrading

section RationalClassification

variable {R : Type} [CommRing R] [Algebra ℚ R]
  {N L : Type*} [AddCommMonoid N] [DecidableEq N]
  [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Over a commutative `ℚ`-algebra `R : Type`, the canonical Lie inclusion `ι : L → U(L)` is
injective, with no freeness or basis assumption on `L`. -/
theorem ι_injective_of_algebra_rat : Function.Injective (ι R : L → U) :=
  fun _ _ h => (primitiveEquiv R L).injective (Subtype.ext (by
    simpa only [coe_primitiveEquiv_apply] using h))

variable (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- Over a commutative `ℚ`-algebra `R : Type`, `completedLieToU` is injective. -/
theorem completedLieToU_injective_of_algebra_rat :
    Function.Injective (completedLieToU d ℒ) :=
  completedLieToU_injective d ℒ ι_injective_of_algebra_rat

omit [Algebra ℚ R] in
/-- Construct an element of `d.completedLie ℒ` with prescribed compatible finite-cutoff
projections. -/
private noncomputable def ofCompatibleFamily (x : ∀ k, d.truncatedLie ℒ k)
    (hx : ∀ k, LieIdeal.factor (d.degreeIdeal_antitone ℒ (Nat.le_succ k)) (x (k + 1)) = x k) :
    d.completedLie ℒ :=
  LieIdeal.completionLift (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)
    (fun k =>
      { toFun := fun r : R => r • x k
        map_add' := fun r s => add_smul r s (x k)
        map_smul' := fun r s => mul_smul r s (x k)
        map_lie' := fun {r s} => by
          have hrs : ⁅r, s⁆ = 0 := by
            rw [LieRing.of_associative_ring_bracket, mul_comm, sub_self]
          simp [hrs] })
    (fun k => by
      ext r
      change LieIdeal.factor (d.degreeIdeal_antitone ℒ (Nat.le_succ k)) (r • x (k + 1)) = r • x k
      rw [map_smul, hx k])
    (1 : R)

omit [Algebra ℚ R] in
private theorem completionProjection_ofCompatibleFamily (x : ∀ k, d.truncatedLie ℒ k)
    (hx : ∀ k, LieIdeal.factor (d.degreeIdeal_antitone ℒ (Nat.le_succ k)) (x (k + 1)) = x k)
    (k : ℕ) :
    LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k
      (ofCompatibleFamily d ℒ x hx) = x k := by
  rw [ofCompatibleFamily, LieIdeal.completionProjection_lift]
  exact one_smul R (x k)

/-- **Classification of completed primitive elements.** Over a commutative `ℚ`-algebra `R : Type`,
an element of the completed enveloping algebra of a positively graded Lie algebra is completed
primitive if and only if it lies in the image of `completedLieToU`. -/
theorem isCompletedPrimitive_iff_mem_range_completedLieToU (u : completedEnveloping d ℒ) :
    (positiveDegreeFiltration d ℒ).IsCompletedPrimitive R u ↔
      u ∈ Set.range (completedLieToU d ℒ) := by
  constructor
  · intro hu
    let F := positiveDegreeFiltration d ℒ
    have hexists (k : ℕ) : ∃ xk : d.truncatedLie ℒ k,
        truncatedLieToU d ℒ k xk = F.projection k u := by
      classical
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection k u)
      have hprim := (isCompletedPrimitive_iff_forall_isPrimitiveElem_decompose ℒ d.degree
        (fun n hn => d.eq_bot_of_degree_nonpos ℒ n hn.le)).mp hu k a ha
      let y (n : N) : L :=
        if hn : d.degree n ≤ k then
          (_root_.DirectSum.decompose ℒ
            ((primitiveEquiv R L).symm ⟨_, hprim n hn⟩) n : L)
        else 0
      have hy_mem (n : N) : y n ∈ ℒ n := by
        dsimp only [y]
        split_ifs
        · exact (_root_.DirectSum.decompose ℒ _ n).property
        · exact Submodule.zero_mem _
      have hιy (n : N) (hn : d.degree n ≤ k) :
          ι R (y n) = (_root_.DirectSum.decompose (homogeneousSubmodule ℒ) a n : U) := by
        dsimp only [y]
        simp only [hn, ↓reduceDIte]
        rw [← coe_decompose_mkAlgHom_ι, ← ι_apply, ι_primitiveEquiv_symm]
        exact _root_.DirectSum.decompose_of_mem_same (homogeneousSubmodule ℒ)
          (_root_.DirectSum.decompose (homogeneousSubmodule ℒ) a n).property
      let yk : L := ∑ n ∈ (_root_.DirectSum.decompose (homogeneousSubmodule ℒ) a).support, y n
      refine ⟨LieSubmodule.Quotient.mk yk, ?_⟩
      rw [truncatedLieToU_mk, ← ha, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
        mem_degreeFiltration_ideal_iff]
      intro m hm
      have hmk : d.degree m ≤ k := by omega
      rw [_root_.DirectSum.decompose_sub, _root_.DirectSum.sub_apply, Submodule.coe_sub,
        sub_eq_zero, map_sum, _root_.DirectSum.decompose_sum, _root_.DirectSum.sum_apply,
        Submodule.coe_sum]
      have hterm (n : N) :
          (_root_.DirectSum.decompose (homogeneousSubmodule ℒ) (ι R (y n)) m : U) =
            if n = m then ι R (y n) else 0 := by
        split_ifs with hnm
        · subst hnm
          exact _root_.DirectSum.decompose_of_mem_same (homogeneousSubmodule ℒ)
            (ι_mem_homogeneousSubmodule ℒ (hy_mem n))
        · exact _root_.DirectSum.decompose_of_mem_ne (homogeneousSubmodule ℒ)
            (ι_mem_homogeneousSubmodule ℒ (hy_mem n)) hnm
      simp_rw [hterm]
      rw [Finset.sum_ite_eq']
      split_ifs with hms
      · exact hιy m hmk
      · symm
        simpa [DFinsupp.mem_support_iff] using hms
    choose x hx using hexists
    have hcompat (k : ℕ) :
        LieIdeal.factor (d.degreeIdeal_antitone ℒ (Nat.le_succ k)) (x (k + 1)) = x k := by
      apply truncatedLieToU_injective d ℒ ι_injective_of_algebra_rat k
      rw [truncatedLieToU_factor d ℒ (Nat.le_succ k), hx (k + 1), hx k]
      exact F.factor_projection (Nat.le_succ k) u
    refine ⟨ofCompatibleFamily d ℒ x hcompat, F.completion_ext fun k => ?_⟩
    rw [projection_completedLieToU, completionProjection_ofCompatibleFamily, hx k]
  · rintro ⟨x, rfl⟩
    exact isCompletedPrimitive_completedLieToU d ℒ x

/-- Over a commutative `ℚ`-algebra `R : Type`, `completedLieToU` induces a linear equivalence
between `d.completedLie ℒ` and the submodule of completed primitive elements of
`completedEnveloping d ℒ`. -/
noncomputable def completedLieEquivCompletedPrimitive :
    d.completedLie ℒ ≃ₗ[R]
      (positiveDegreeFiltration d ℒ).completedPrimitiveSubmodule R :=
  LinearEquiv.ofBijective
    ((completedLieToU d ℒ).toLinearMap.codRestrict _ fun x =>
      ((positiveDegreeFiltration d ℒ).mem_completedPrimitiveSubmodule R).mpr
        (isCompletedPrimitive_completedLieToU d ℒ x))
    ⟨(LinearMap.injective_codRestrict_iff _).mpr (completedLieToU_injective_of_algebra_rat d ℒ),
      fun u => by
        obtain ⟨x, hx⟩ := (isCompletedPrimitive_iff_mem_range_completedLieToU d ℒ u).mp
          (((positiveDegreeFiltration d ℒ).mem_completedPrimitiveSubmodule R).mp u.2)
        exact ⟨x, Subtype.ext hx⟩⟩

/-- The forward map of `completedLieEquivCompletedPrimitive` is `completedLieToU`. -/
@[simp]
theorem coe_completedLieEquivCompletedPrimitive (x : d.completedLie ℒ) :
    (completedLieEquivCompletedPrimitive d ℒ x : completedEnveloping d ℒ) =
      completedLieToU d ℒ x :=
  congrArg Subtype.val (LinearEquiv.ofBijective_apply _ x)

/-- Applying `completedLieToU` to the inverse of `completedLieEquivCompletedPrimitive` recovers the
primitive element. -/
@[simp]
theorem completedLieToU_completedLieEquivCompletedPrimitive_symm
    (u : (positiveDegreeFiltration d ℒ).completedPrimitiveSubmodule R) :
    completedLieToU d ℒ ((completedLieEquivCompletedPrimitive d ℒ).symm u) =
      (u : completedEnveloping d ℒ) := by
  simpa only [coe_completedLieEquivCompletedPrimitive] using
    congrArg Subtype.val ((completedLieEquivCompletedPrimitive d ℒ).apply_symm_apply u)

/-- Over a commutative `ℚ`-algebra `R : Type`, when `U(L)` is also equipped with `[Algebra ℚ U(L)]`,
the completed exponential identifies `d.completedLie ℒ` bijectively with the completed group-like
elements of `completedEnveloping d ℒ`. -/
noncomputable def completedLieEquivCompletedGroupLike [Algebra ℚ U] :
    d.completedLie ℒ ≃
      {u : completedEnveloping d ℒ //
        (positiveDegreeFiltration d ℒ).IsCompletedGroupLike R u} :=
  ((completedLieEquivCompletedPrimitive d ℒ).toEquiv.trans
    (Equiv.subtypeEquivRight fun _ =>
      (positiveDegreeFiltration d ℒ).mem_completedPrimitiveSubmodule R)).trans
    ((positiveDegreeFiltration d ℒ).completedExpEquivCompletedGroupLike R
      (ker_counitAlgHom_eq_degreeFiltration_one ℒ d.degree
        (fun n hn => d.eq_bot_of_degree_nonpos ℒ n hn)).le)

/-- The forward map of `completedLieEquivCompletedGroupLike` is `completedExp ∘ completedLieToU`. -/
@[simp]
theorem coe_completedLieEquivCompletedGroupLike [Algebra ℚ U] (x : d.completedLie ℒ) :
    (completedLieEquivCompletedGroupLike d ℒ x : completedEnveloping d ℒ) =
      (positiveDegreeFiltration d ℒ).completedExp
        ⟨completedLieToU d ℒ x, completedLieToU_mem_completionIdeal_one d ℒ x⟩ := by
  simp [completedLieEquivCompletedGroupLike]

/-- Applying `completedLieToU` to the inverse of `completedLieEquivCompletedGroupLike` gives
`completedLog`. -/
@[simp]
theorem completedLieToU_completedLieEquivCompletedGroupLike_symm [Algebra ℚ U]
    (u : {u : completedEnveloping d ℒ //
      (positiveDegreeFiltration d ℒ).IsCompletedGroupLike R u}) :
    completedLieToU d ℒ ((completedLieEquivCompletedGroupLike d ℒ).symm u) =
      (positiveDegreeFiltration d ℒ).completedLog
        ⟨u.1, u.2.sub_one_mem_completionIdeal_one
          (ker_counitAlgHom_eq_degreeFiltration_one ℒ d.degree
            (fun n hn => d.eq_bot_of_degree_nonpos ℒ n hn)).le⟩ := by
  simp [completedLieEquivCompletedGroupLike]

end RationalClassification

end TauCeti.UniversalEnvelopingAlgebra
