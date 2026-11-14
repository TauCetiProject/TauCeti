/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.GroupLike
public import TauCeti.Algebra.Lie.UniversalEnveloping.DegreeFiltration
public import TauCeti.RingTheory.FilteredAlgebra.Exp.Basic
public import TauCeti.RingTheory.FilteredAlgebra.TensorProduct.Basic

/-!
# Completed bialgebra structure on graded universal enveloping algebras

For a Lie algebra `L` over a commutative ring `R` graded by an additive monoid `Γ` with an integral
degree functional `d : Γ →+ ℤ` and no negative-degree components, the enveloping algebra `U(L)`
carries the total-degree filtration `TauCeti.UniversalEnvelopingAlgebra.degreeFiltration`. Its
compatible-family completion `completedEnveloping` is not an ordinary coalgebra, because the
completed tensor product is larger than the algebraic tensor product of completions, and the finite
quotients `U(L) ⧸ I ^ (k + 1)` are not quotient coalgebras. Nevertheless, the bialgebra
comultiplication `Δ : U(L) → U(L) ⊗[R] U(L)` preserves total filtration order for the total-degree
tensor filtration, so it extends to an `R`-algebra homomorphism `completedCoproduct` into the
completed tensor square, while the counit descends through order zero to `completedCounit`.

Within `completedEnveloping`, an element `x` is completed primitive (`IsCompletedPrimitive`) when
`Δ̂(x) = x ⊗̂ 1 + 1 ⊗̂ x`, and completed grouplike (`IsCompletedGroupLike`) when `ε̂(x) = 1` and
`Δ̂(x) = x ⊗̂ x`. Over any commutative ring, completed primitive elements have completed counit
zero and form a Lie subalgebra under the associative commutator, while completed grouplike elements
form a submonoid closed under two-sided inverses. Over a commutative `ℚ`-algebra, `completedExp`
and `completedLog` exchange the completed primitive elements of the first completion ideal with the
completed grouplike elements congruent to `1`; when `L` is supported in strictly positive degrees,
every completed grouplike element is automatically congruent to `1`.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.completedEnveloping`: completion of `U(L)` along
  `degreeFiltration`.
* `TauCeti.UniversalEnvelopingAlgebra.completedCoproduct`: the completed comultiplication into the
  completed tensor square.
* `TauCeti.UniversalEnvelopingAlgebra.completedCounit`: the counit induced on `completedEnveloping`.
* `TauCeti.UniversalEnvelopingAlgebra.IsCompletedPrimitive` and
  `TauCeti.UniversalEnvelopingAlgebra.completedPrimitiveLieSubalgebra`: completed primitive
  elements and their commutator Lie subalgebra.
* `TauCeti.UniversalEnvelopingAlgebra.IsCompletedGroupLike` and
  `TauCeti.UniversalEnvelopingAlgebra.completedGroupLikeSubmonoid`: completed grouplike elements
  and their multiplicative submonoid.
* `TauCeti.UniversalEnvelopingAlgebra.completedPrimitiveExpEquiv`: equivalence between completed
  primitive elements of the first completion ideal and completed grouplike elements for a strictly
  positive Lie grading over a commutative `ℚ`-algebra.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.degreeFiltration_le_comap_comulAlgHom`: comultiplication
  preserves every degree-filtration ideal.
* `TauCeti.UniversalEnvelopingAlgebra.IsCompletedPrimitive.completedCounit_eq_zero`: every
  completed primitive element has completed counit zero.
* `TauCeti.UniversalEnvelopingAlgebra.isCompletedGroupLike_completedExp_iff` and
  `TauCeti.UniversalEnvelopingAlgebra.isCompletedPrimitive_completedLog_iff`: `completedExp` and
  `completedLog` exchange completed primitive and completed grouplike elements.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter II, §6.
* E. Petracci, *Universal representations of Lie algebras by coderivations*
  (arXiv:math/0303020), §8.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

section RationalScalarTower

/-- A universal enveloping algebra over a commutative `ℚ`-algebra inherits its canonical
`ℚ`-algebra structure from the `RingCon` quotient construction. -/
-- Low-priority so `UniversalEnvelopingAlgebra.instAlgebra` wins for `Algebra R U`,
-- and at `R = ℚ` the two instances remain definitionally equal.
instance (priority := low) instAlgebraRat {R L : Type*} [CommRing R] [Algebra ℚ R]
    [LieRing L] [LieAlgebra R L] :
    Algebra ℚ (_root_.UniversalEnvelopingAlgebra R L) :=
  letI : Algebra ℚ (TensorAlgebra R L) :=
    inferInstanceAs (Algebra ℚ (RingCon.Quotient (TensorAlgebra.ringCon R L)))
  inferInstanceAs (Algebra ℚ (RingCon.Quotient (_root_.UniversalEnvelopingAlgebra.ringCon R L)))

instance (priority := low) instIsScalarTowerRat {R L : Type*} [CommRing R] [Algebra ℚ R]
    [LieRing L] [LieAlgebra R L] :
    IsScalarTower ℚ R (_root_.UniversalEnvelopingAlgebra R L) :=
  letI : Algebra ℚ (TensorAlgebra R L) :=
    inferInstanceAs (Algebra ℚ (RingCon.Quotient (TensorAlgebra.ringCon R L)))
  inferInstanceAs
    (IsScalarTower ℚ R (RingCon.Quotient (_root_.UniversalEnvelopingAlgebra.ringCon R L)))

end RationalScalarTower

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L) (d : Γ →+ ℤ)

variable [DecidableEq Γ] [GradedLieAlgebra ℒ]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

private theorem comul_prod_mem_tensorProduct (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    ∀ (l : List (Σ i, ℒ i)), (∀ a ∈ l, 0 ≤ d a.1) →
      Bialgebra.comulAlgHom R U (l.map (fun x => ι R (x.2 : L))).prod ∈
        ((degreeFiltration ℒ d hneg).tensorProduct R (degreeFiltration ℒ d hneg)).ideal
          (d (l.map Sigma.fst).sum).toNat
  | [], _ => by simp [Submodule.mem_top]
  | a :: l, hnonneg => by
    have ha0 : 0 ≤ d a.1 := hnonneg a List.mem_cons_self
    have hl_each : ∀ b ∈ l, 0 ≤ d b.1 := fun b hb => hnonneg b (List.mem_cons_of_mem a hb)
    have hsum0 : 0 ≤ d (l.map Sigma.fst).sum := by
      rw [map_list_sum]
      refine List.sum_nonneg ?_
      intro z hz
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hz
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
      exact hl_each b hb
    have hι : ι R (a.2 : L) ∈ (degreeFiltration ℒ d hneg).ideal (d a.1).toNat :=
      ι_mem_degreeFiltration ℒ d hneg a.2.property (by omega)
    have hhead : Bialgebra.comulAlgHom R U (ι R (a.2 : L)) ∈
        ((degreeFiltration ℒ d hneg).tensorProduct R (degreeFiltration ℒ d hneg)).ideal
          (d a.1).toNat := by
      rw [Bialgebra.comulAlgHom_apply, comul_ι]
      refine Ideal.add_mem _ ?_ ?_
      · exact (degreeFiltration ℒ d hneg).tmul_mem_tensorProduct_ideal R
          (degreeFiltration ℒ d hneg) (a := (d a.1).toNat) (b := 0) (by omega) hι (by simp)
      · exact (degreeFiltration ℒ d hneg).tmul_mem_tensorProduct_ideal R
          (degreeFiltration ℒ d hneg) (a := 0) (b := (d a.1).toNat) (by omega) (by simp) hι
    have htail := comul_prod_mem_tensorProduct hneg l hl_each
    have htoNat : (d ((a :: l).map Sigma.fst).sum).toNat =
        (d a.1).toNat + (d (l.map Sigma.fst).sum).toNat := by
      simp only [List.map_cons, List.sum_cons, map_add]
      omega
    rw [htoNat]
    simp only [List.map_cons, List.prod_cons, map_mul]
    exact ((degreeFiltration ℒ d hneg).tensorProduct R (degreeFiltration ℒ d hneg)).mul_mem
      hhead htail

/-- Comultiplication preserves the total-degree filtration on a graded enveloping algebra. -/
theorem degreeFiltration_le_comap_comulAlgHom (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (k : ℕ) :
    (degreeFiltration ℒ d hneg).ideal k ≤
      (((degreeFiltration ℒ d hneg).tensorProduct R
        (degreeFiltration ℒ d hneg)).ideal k).comap (Bialgebra.comulAlgHom R U) := by
  rw [degreeFiltration_ideal_le_iff]
  intro n hn
  have hle := (homogeneousSubmodule_le_iff ℒ n
    ((((degreeFiltration ℒ d hneg).tensorProduct R
      (degreeFiltration ℒ d hneg)).ideal k).comap
        (Bialgebra.comulAlgHom R U) |>.restrictScalars R)).mpr fun l hl => by
    rw [Submodule.restrictScalars_mem, Ideal.mem_comap]
    by_cases hnonneg : ∀ a ∈ l, 0 ≤ d a.1
    · have hk : k ≤ (d (l.map Sigma.fst).sum).toNat := by
        rw [hl]
        omega
      exact ((degreeFiltration ℒ d hneg).tensorProduct R
        (degreeFiltration ℒ d hneg)).antitone hk
          (comul_prod_mem_tensorProduct ℒ d hneg l hnonneg)
    · push Not at hnonneg
      obtain ⟨a, hal, haneg⟩ := hnonneg
      have ha0 : (a.2 : L) = 0 := by
        simpa only [hneg a.1 haneg, Submodule.mem_bot] using a.2.property
      have hprod : (l.map (fun x => ι R (x.2 : L))).prod = 0 :=
        List.prod_eq_zero <| List.mem_map.mpr ⟨a, hal, by simp [ha0]⟩
      rw [hprod, map_zero]
      exact zero_mem _
  exact fun a ha => (Submodule.restrictScalars_mem R _ _).mp (hle ha)

/-- The completion of a graded universal enveloping algebra along its total-degree filtration. -/
noncomputable abbrev completedEnveloping (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :=
  (degreeFiltration ℒ d hneg).completion

/-- The completed comultiplication, induced on `completedEnveloping` by `Bialgebra.comulAlgHom`. -/
noncomputable def completedCoproduct (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    completedEnveloping ℒ d hneg →ₐ[R]
      ((degreeFiltration ℒ d hneg).tensorProduct R (degreeFiltration ℒ d hneg)).completion :=
  (degreeFiltration ℒ d hneg).mapCompletionₐ
    ((degreeFiltration ℒ d hneg).tensorProduct R (degreeFiltration ℒ d hneg))
    (Bialgebra.comulAlgHom R U) id monotone_id
    (fun k => degreeFiltration_le_comap_comulAlgHom ℒ d hneg (k + 1))

/-- At order `k`, `completedCoproduct` is the quotient map induced by comultiplication. -/
@[simp]
theorem projection_completedCoproduct (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (k : ℕ)
    (x : completedEnveloping ℒ d hneg) :
    ((degreeFiltration ℒ d hneg).tensorProduct R (degreeFiltration ℒ d hneg)).projection k
        (completedCoproduct ℒ d hneg x) =
      Ideal.quotientMapₐ
        (((degreeFiltration ℒ d hneg).tensorProduct R
          (degreeFiltration ℒ d hneg)).ideal (k + 1))
        (Bialgebra.comulAlgHom R U) (degreeFiltration_le_comap_comulAlgHom ℒ d hneg (k + 1))
        ((degreeFiltration ℒ d hneg).projection k x) :=
  (degreeFiltration ℒ d hneg).projection_mapCompletionₐ _ _ id monotone_id _ k x

/-- `completedCoproduct` extends the ordinary comultiplication along `toCompletion`. -/
@[simp]
theorem completedCoproduct_toCompletion (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (u : U) :
    completedCoproduct ℒ d hneg ((degreeFiltration ℒ d hneg).toCompletion u) =
      ((degreeFiltration ℒ d hneg).tensorProduct R (degreeFiltration ℒ d hneg)).toCompletion
        (Coalgebra.comul (R := R) u) :=
  (degreeFiltration ℒ d hneg).mapCompletionₐ_toCompletion _ _ id monotone_id _ u

/-- `completedCoproduct` preserves every induced completion ideal. -/
theorem completedCoproduct_mem_completionIdeal (hneg : ∀ n, d n < 0 → ℒ n = ⊥) {k : ℕ}
    {x : completedEnveloping ℒ d hneg}
    (hx : x ∈ (degreeFiltration ℒ d hneg).completionIdeal k) :
    completedCoproduct ℒ d hneg x ∈
      ((degreeFiltration ℒ d hneg).tensorProduct R
        (degreeFiltration ℒ d hneg)).completionIdeal k := by
  cases k with
  | zero => simp
  | succ k =>
    exact (degreeFiltration ℒ d hneg).mapCompletionₐ_mem_completionIdeal
      _ _ id monotone_id _ k hx

private theorem degreeFiltration_one_le_ker_counitAlgHom (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    (degreeFiltration ℒ d hneg).ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R U) := by
  intro u hu
  exact (HopfIdeal.mem_augmentation R U).mp
    (HopfIdeal.mem_toIdeal.mp (degreeFiltration_le_augmentation ℒ d hneg Nat.one_pos hu))

/-- The completed counit on `completedEnveloping`, factored through the order-zero projection. -/
noncomputable def completedCounit (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    completedEnveloping ℒ d hneg →ₐ[R] R :=
  (Ideal.Quotient.liftₐ ((degreeFiltration ℒ d hneg).ideal 1) (Bialgebra.counitAlgHom R U)
    (fun _ hu => RingHom.mem_ker.mp
      (degreeFiltration_one_le_ker_counitAlgHom ℒ d hneg hu))).comp
    ((degreeFiltration ℒ d hneg).projectionₐ 0)

/-- The completed counit agrees with `Coalgebra.counit` on any order-zero representative. -/
theorem completedCounit_of_representative (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    (x : completedEnveloping ℒ d hneg) (a : U)
    (ha : Ideal.Quotient.mk ((degreeFiltration ℒ d hneg).ideal 1) a =
      (degreeFiltration ℒ d hneg).projection 0 x) :
    completedCounit ℒ d hneg x = Coalgebra.counit (R := R) a := by
  rw [completedCounit, AlgHom.comp_apply, TauCeti.AlgFiltration.projectionₐ_apply, ← ha]
  rfl

/-- `completedCounit` extends the ordinary counit along `toCompletion`. -/
@[simp]
theorem completedCounit_toCompletion (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (u : U) :
    completedCounit ℒ d hneg ((degreeFiltration ℒ d hneg).toCompletion u) =
      Coalgebra.counit (R := R) u :=
  completedCounit_of_representative ℒ d hneg _ u
    ((degreeFiltration ℒ d hneg).projection_toCompletion 0 u).symm

/-- Elements of the first completion ideal have completed counit zero. -/
theorem completedCounit_eq_zero_of_mem_completionIdeal_one (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {x : completedEnveloping ℒ d hneg}
    (hx : x ∈ (degreeFiltration ℒ d hneg).completionIdeal 1) :
    completedCounit ℒ d hneg x = 0 := by
  rw [TauCeti.AlgFiltration.completionIdeal_succ, RingHom.mem_ker] at hx
  rw [completedCounit, AlgHom.comp_apply, TauCeti.AlgFiltration.projectionₐ_apply, hx, map_zero]

/-- For a strictly positive Lie grading, the first degree-filtration ideal equals the augmentation
ideal. -/
theorem degreeFiltration_one_eq_augmentation (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) :
    (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).ideal 1 =
      (TauCeti.HopfIdeal.augmentation R U).toIdeal :=
  le_antisymm (degreeFiltration_le_augmentation ℒ d _ Nat.one_pos)
    (augmentation_le_degreeFiltration_one ℒ d hpos)

/-- For a strictly positive Lie grading, the kernel of `completedCounit` is the first completion
ideal. -/
theorem completedCounit_eq_zero_iff (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥)
    {x : completedEnveloping ℒ d (fun n hn => hpos n hn.le)} :
    completedCounit ℒ d (fun n hn => hpos n hn.le) x = 0 ↔
      x ∈ (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).completionIdeal 1 := by
  refine ⟨fun hx => ?_, completedCounit_eq_zero_of_mem_completionIdeal_one ℒ d _⟩
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    ((degreeFiltration ℒ d (fun n hn => hpos n hn.le)).projection 0 x)
  rw [completedCounit_of_representative ℒ d _ x a ha] at hx
  have hmem : a ∈ (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).ideal 1 := by
    rw [degreeFiltration_one_eq_augmentation ℒ d hpos]
    exact HopfIdeal.mem_toIdeal.mpr ((HopfIdeal.mem_augmentation R U).mpr hx)
  rw [TauCeti.AlgFiltration.completionIdeal_succ, RingHom.mem_ker, ← ha,
    Ideal.Quotient.eq_zero_iff_mem]
  exact hmem

/-- For a strictly positive Lie grading, completed counit one means congruence to `1` modulo the
first completion ideal. -/
theorem completedCounit_eq_one_iff (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥)
    {u : completedEnveloping ℒ d (fun n hn => hpos n hn.le)} :
    completedCounit ℒ d (fun n hn => hpos n hn.le) u = 1 ↔
      u - 1 ∈ (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).completionIdeal 1 := by
  rw [← completedCounit_eq_zero_iff ℒ d hpos, map_sub, map_one, sub_eq_zero]

/-- An element `x` of `completedEnveloping` is completed primitive when
`Δ̂(x) = x ⊗̂ 1 + 1 ⊗̂ x`. -/
def IsCompletedPrimitive (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    (x : completedEnveloping ℒ d hneg) : Prop :=
  completedCoproduct ℒ d hneg x =
    (degreeFiltration ℒ d hneg).completedTensor R (degreeFiltration ℒ d hneg) x 1 +
      (degreeFiltration ℒ d hneg).completedTensor R (degreeFiltration ℒ d hneg) 1 x

/-- Unfolding characterization of `IsCompletedPrimitive`. -/
theorem isCompletedPrimitive_iff (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {x : completedEnveloping ℒ d hneg} :
    IsCompletedPrimitive ℒ d hneg x ↔
      completedCoproduct ℒ d hneg x =
        (degreeFiltration ℒ d hneg).completedTensor R (degreeFiltration ℒ d hneg) x 1 +
          (degreeFiltration ℒ d hneg).completedTensor R (degreeFiltration ℒ d hneg) 1 x :=
  Iff.rfl

/-- `IsCompletedPrimitive` in terms of the two completed tensor inclusions. -/
theorem isCompletedPrimitive_iff_includeCompletion (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {x : completedEnveloping ℒ d hneg} :
    IsCompletedPrimitive ℒ d hneg x ↔
      completedCoproduct ℒ d hneg x =
        (degreeFiltration ℒ d hneg).includeLeftCompletion R (degreeFiltration ℒ d hneg) x +
          (degreeFiltration ℒ d hneg).includeRightCompletion R
            (degreeFiltration ℒ d hneg) x := by
  simp [IsCompletedPrimitive]

private noncomputable def tensorCounitAlgHom : U ⊗[R] U →ₐ[R] R :=
  (Algebra.TensorProduct.lid R R).toAlgHom.comp
    (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R U) (Bialgebra.counitAlgHom R U))

private theorem tensorCounitAlgHom_comp_comulAlgHom :
    (tensorCounitAlgHom (R := R) (L := L)).comp (Bialgebra.comulAlgHom R U) =
      Bialgebra.counitAlgHom R U := by
  apply _root_.UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro x
  simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
    tensorCounitAlgHom, Bialgebra.comulAlgHom_apply, Bialgebra.counitAlgHom_apply,
    comul_ι, counit_ι, map_add, Algebra.TensorProduct.map_tmul, map_one,
    AlgEquiv.toAlgHom_apply, Algebra.TensorProduct.lid_tmul, smul_eq_mul, mul_zero, zero_mul,
    add_zero]

private theorem tensorProduct_one_le_ker_tensorCounitAlgHom
    (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    ((degreeFiltration ℒ d hneg).tensorProduct R (degreeFiltration ℒ d hneg)).ideal 1 ≤
      RingHom.ker (tensorCounitAlgHom (R := R) (L := L)) := by
  intro t ht
  rw [TauCeti.AlgFiltration.mem_tensorProduct_ideal_iff, tensorFiltrationTail_def] at ht
  let K : Submodule R (U ⊗[R] U) :=
    (RingHom.ker (tensorCounitAlgHom (R := R) (L := L))).restrictScalars R
  change t ∈ K
  refine Submodule.iSup_induction _ (motive := fun z => z ∈ K) ht (fun a z hz => ?_)
    (by simp) (fun _ _ hx hy => add_mem hx hy)
  refine Submodule.iSup_induction _ (motive := fun z => z ∈ K) hz (fun b z hz => ?_)
    (by simp) (fun _ _ hx hy => add_mem hx hy)
  refine Submodule.iSup_induction _ (motive := fun z => z ∈ K) hz (fun hab z hz => ?_)
    (by simp) (fun _ _ hx hy => add_mem hx hy)
  refine Submodule.map₂_le.mpr (fun u hu v hv => ?_) hz
  rw [Submodule.restrictScalars_mem, RingHom.mem_ker, TensorProduct.mk_apply,
    tensorCounitAlgHom, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    AlgEquiv.toAlgHom_apply, Algebra.TensorProduct.lid_tmul, smul_eq_mul]
  by_cases ha : 0 < a
  · have hu0 : Bialgebra.counitAlgHom R U u = 0 :=
      RingHom.mem_ker.mp
        (degreeFiltration_one_le_ker_counitAlgHom ℒ d hneg
          ((degreeFiltration ℒ d hneg).antitone ha hu))
    rw [hu0, zero_mul]
  · have hb : 0 < b := by omega
    have hv0 : Bialgebra.counitAlgHom R U v = 0 :=
      RingHom.mem_ker.mp
        (degreeFiltration_one_le_ker_counitAlgHom ℒ d hneg
          ((degreeFiltration ℒ d hneg).antitone hb hv))
    rw [hv0, mul_zero]

/-- Every completed primitive element has completed counit zero. -/
theorem IsCompletedPrimitive.completedCounit_eq_zero {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {x : completedEnveloping ℒ d hneg} (hx : IsCompletedPrimitive ℒ d hneg x) :
    completedCounit ℒ d hneg x = 0 := by
  let 𝒯 := (degreeFiltration ℒ d hneg).tensorProduct R (degreeFiltration ℒ d hneg)
  let ε₂ : 𝒯.completion →ₐ[R] R :=
    (Ideal.Quotient.liftₐ (𝒯.ideal 1) (tensorCounitAlgHom (R := R) (L := L))
      (fun _ ht => RingHom.mem_ker.mp
        (tensorProduct_one_le_ker_tensorCounitAlgHom ℒ d hneg ht))).comp (𝒯.projectionₐ 0)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((degreeFiltration ℒ d hneg).projection 0 x)
  have h1 : Ideal.Quotient.mk ((degreeFiltration ℒ d hneg).ideal (0 + 1)) 1 =
      (degreeFiltration ℒ d hneg).projection 0 1 :=
    (map_one ((degreeFiltration ℒ d hneg).projection 0)).symm
  have hL :
      ε₂ ((degreeFiltration ℒ d hneg).completedTensor R (degreeFiltration ℒ d hneg) x 1) =
        completedCounit ℒ d hneg x := by
    have hp := (degreeFiltration ℒ d hneg).projection_completedTensor_of_representatives
      R (degreeFiltration ℒ d hneg) 0 x 1 a 1 ha h1
    simp only [ε₂, 𝒯, AlgHom.comp_apply, TauCeti.AlgFiltration.projectionₐ_apply, hp,
      Ideal.Quotient.liftₐ_apply]
    simpa [tensorCounitAlgHom] using (completedCounit_of_representative ℒ d hneg x a ha).symm
  have hR :
      ε₂ ((degreeFiltration ℒ d hneg).completedTensor R (degreeFiltration ℒ d hneg) 1 x) =
        completedCounit ℒ d hneg x := by
    have hp := (degreeFiltration ℒ d hneg).projection_completedTensor_of_representatives
      R (degreeFiltration ℒ d hneg) 0 1 x 1 a h1 ha
    simp only [ε₂, 𝒯, AlgHom.comp_apply, TauCeti.AlgFiltration.projectionₐ_apply, hp,
      Ideal.Quotient.liftₐ_apply]
    simpa [tensorCounitAlgHom] using (completedCounit_of_representative ℒ d hneg x a ha).symm
  have hΔ : ε₂ (completedCoproduct ℒ d hneg x) = completedCounit ℒ d hneg x := by
    simp only [ε₂, 𝒯, AlgHom.comp_apply, TauCeti.AlgFiltration.projectionₐ_apply,
      projection_completedCoproduct, ← ha, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.liftₐ_apply]
    have hcomp := AlgHom.congr_fun (tensorCounitAlgHom_comp_comulAlgHom (R := R) (L := L)) a
    exact hcomp.trans (completedCounit_of_representative ℒ d hneg x a ha).symm
  have heq : completedCounit ℒ d hneg x =
      completedCounit ℒ d hneg x + completedCounit ℒ d hneg x := by
    have hε := congrArg ε₂ hx
    rwa [hΔ, map_add, hL, hR] at hε
  calc completedCounit ℒ d hneg x
      = (completedCounit ℒ d hneg x + completedCounit ℒ d hneg x) -
          completedCounit ℒ d hneg x := by abel
    _ = 0 := by rw [← heq, sub_self]

/-- For a strictly positive Lie grading, every completed primitive element lies in the first
completion ideal. -/
theorem IsCompletedPrimitive.mem_completionIdeal_one {hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥}
    {x : completedEnveloping ℒ d (fun n hn => hpos n hn.le)}
    (hx : IsCompletedPrimitive ℒ d (fun n hn => hpos n hn.le) x) :
    x ∈ (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).completionIdeal 1 :=
  (completedCounit_eq_zero_iff ℒ d hpos).mp (hx.completedCounit_eq_zero ℒ d)

/-- Zero is completed primitive. -/
@[simp]
theorem IsCompletedPrimitive.zero (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    IsCompletedPrimitive ℒ d hneg 0 := by
  simp [isCompletedPrimitive_iff_includeCompletion]

/-- Completed primitive elements are closed under addition. -/
theorem IsCompletedPrimitive.add {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {x y : completedEnveloping ℒ d hneg}
    (hx : IsCompletedPrimitive ℒ d hneg x) (hy : IsCompletedPrimitive ℒ d hneg y) :
    IsCompletedPrimitive ℒ d hneg (x + y) := by
  rw [isCompletedPrimitive_iff_includeCompletion] at hx hy ⊢
  rw [map_add, hx, hy, map_add, map_add]
  abel

/-- Completed primitive elements are closed under negation. -/
theorem IsCompletedPrimitive.neg {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {x : completedEnveloping ℒ d hneg} (hx : IsCompletedPrimitive ℒ d hneg x) :
    IsCompletedPrimitive ℒ d hneg (-x) := by
  rw [isCompletedPrimitive_iff_includeCompletion] at hx ⊢
  rw [map_neg, hx, map_neg, map_neg, neg_add]

/-- Completed primitive elements are closed under subtraction. -/
theorem IsCompletedPrimitive.sub {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {x y : completedEnveloping ℒ d hneg}
    (hx : IsCompletedPrimitive ℒ d hneg x) (hy : IsCompletedPrimitive ℒ d hneg y) :
    IsCompletedPrimitive ℒ d hneg (x - y) := by
  simpa only [sub_eq_add_neg] using hx.add ℒ d (hy.neg ℒ d)

/-- Completed primitive elements are closed under scalar multiplication. -/
theorem IsCompletedPrimitive.smul {hneg : ∀ n, d n < 0 → ℒ n = ⊥} (r : R)
    {x : completedEnveloping ℒ d hneg} (hx : IsCompletedPrimitive ℒ d hneg x) :
    IsCompletedPrimitive ℒ d hneg (r • x) := by
  rw [isCompletedPrimitive_iff_includeCompletion] at hx ⊢
  rw [map_smul, hx, map_smul, map_smul, smul_add]

/-- Completed primitive elements are closed under the associative commutator bracket. -/
theorem IsCompletedPrimitive.lie {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {x y : completedEnveloping ℒ d hneg}
    (hx : IsCompletedPrimitive ℒ d hneg x) (hy : IsCompletedPrimitive ℒ d hneg y) :
    IsCompletedPrimitive ℒ d hneg ⁅x, y⁆ := by
  rw [isCompletedPrimitive_iff_includeCompletion] at hx hy ⊢
  have hxy := ((degreeFiltration ℒ d hneg).commute_includeLeftCompletion_includeRightCompletion
    R (degreeFiltration ℒ d hneg) x y).eq
  have hyx := ((degreeFiltration ℒ d hneg).commute_includeLeftCompletion_includeRightCompletion
    R (degreeFiltration ℒ d hneg) y x).eq
  simp only [LieRing.of_associative_ring_bracket, map_sub, map_mul, hx, hy,
    add_mul, mul_add, hxy, hyx]
  abel

/-- The commutator Lie subalgebra of completed primitive elements in `completedEnveloping`. -/
noncomputable def completedPrimitiveLieSubalgebra (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    LieSubalgebra R (completedEnveloping ℒ d hneg) where
  carrier := {x | IsCompletedPrimitive ℒ d hneg x}
  add_mem' hx hy := hx.add ℒ d hy
  zero_mem' := IsCompletedPrimitive.zero ℒ d hneg
  smul_mem' r _ hx := hx.smul ℒ d r
  lie_mem' hx hy := hx.lie ℒ d hy

@[simp]
theorem mem_completedPrimitiveLieSubalgebra_iff (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {x : completedEnveloping ℒ d hneg} :
    x ∈ completedPrimitiveLieSubalgebra ℒ d hneg ↔ IsCompletedPrimitive ℒ d hneg x :=
  Iff.rfl

/-- Ordinary primitive elements of `U(L)` become completed primitive in `completedEnveloping`. -/
theorem isCompletedPrimitive_toCompletion_of_isPrimitiveElem (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {p : U} (hp : Bialgebra.IsPrimitiveElem R p) :
    IsCompletedPrimitive ℒ d hneg ((degreeFiltration ℒ d hneg).toCompletion p) := by
  simp [IsCompletedPrimitive, hp.comul_eq_tmul_add_tmul, add_comm]

/-- Canonical Lie generators map to completed primitive elements in `completedEnveloping`. -/
theorem isCompletedPrimitive_toCompletion_ι (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (x : L) :
    IsCompletedPrimitive ℒ d hneg ((degreeFiltration ℒ d hneg).toCompletion (ι R x)) :=
  isCompletedPrimitive_toCompletion_of_isPrimitiveElem ℒ d hneg (isPrimitiveElem_ι R L x)

/-- An element `u` of `completedEnveloping` is completed grouplike when `ε̂(u) = 1` and
`Δ̂(u) = u ⊗̂ u`. -/
@[mk_iff]
structure IsCompletedGroupLike (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    (u : completedEnveloping ℒ d hneg) : Prop where
  /-- A completed grouplike element has completed counit one. -/
  completedCounit_eq_one : completedCounit ℒ d hneg u = 1
  /-- A completed grouplike element has completed coproduct `u ⊗̂ u`. -/
  completedCoproduct_eq_completedTensor_self :
    completedCoproduct ℒ d hneg u =
      (degreeFiltration ℒ d hneg).completedTensor R (degreeFiltration ℒ d hneg) u u

/-- One is completed grouplike. -/
@[simp]
theorem IsCompletedGroupLike.one (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    IsCompletedGroupLike ℒ d hneg 1 where
  completedCounit_eq_one := map_one _
  completedCoproduct_eq_completedTensor_self := by
    simp [TauCeti.AlgFiltration.completedTensor_apply]

/-- Completed grouplike elements are closed under multiplication. -/
theorem IsCompletedGroupLike.mul {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {u v : completedEnveloping ℒ d hneg}
    (hu : IsCompletedGroupLike ℒ d hneg u) (hv : IsCompletedGroupLike ℒ d hneg v) :
    IsCompletedGroupLike ℒ d hneg (u * v) where
  completedCounit_eq_one := by
    rw [map_mul, hu.completedCounit_eq_one, hv.completedCounit_eq_one, mul_one]
  completedCoproduct_eq_completedTensor_self := by
    rw [map_mul, hu.completedCoproduct_eq_completedTensor_self,
      hv.completedCoproduct_eq_completedTensor_self,
      ((degreeFiltration ℒ d hneg).completedTensor_mul R
        (degreeFiltration ℒ d hneg) u v u v).symm]

/-- Completed grouplike elements form a multiplicative submonoid of `completedEnveloping`. -/
noncomputable def completedGroupLikeSubmonoid (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    Submonoid (completedEnveloping ℒ d hneg) where
  carrier := {u | IsCompletedGroupLike ℒ d hneg u}
  one_mem' := IsCompletedGroupLike.one ℒ d hneg
  mul_mem' hu hv := hu.mul ℒ d hv

@[simp]
theorem mem_completedGroupLikeSubmonoid_iff (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {u : completedEnveloping ℒ d hneg} :
    u ∈ completedGroupLikeSubmonoid ℒ d hneg ↔ IsCompletedGroupLike ℒ d hneg u :=
  Iff.rfl

/-- Completed grouplike elements are closed under natural powers. -/
theorem IsCompletedGroupLike.pow {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {u : completedEnveloping ℒ d hneg} (hu : IsCompletedGroupLike ℒ d hneg u) (n : ℕ) :
    IsCompletedGroupLike ℒ d hneg (u ^ n) :=
  (completedGroupLikeSubmonoid ℒ d hneg).pow_mem hu n

/-- Completed grouplike elements are closed under two-sided inverses. -/
theorem IsCompletedGroupLike.of_mul_eq_one {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {u v : completedEnveloping ℒ d hneg} (huv : u * v = 1) (hvu : v * u = 1)
    (hu : IsCompletedGroupLike ℒ d hneg u) :
    IsCompletedGroupLike ℒ d hneg v where
  completedCounit_eq_one :=
    left_inv_eq_right_inv (a := completedCounit ℒ d hneg u)
      (by rw [← map_mul, hvu, map_one])
      (by rw [hu.completedCounit_eq_one, one_mul])
  completedCoproduct_eq_completedTensor_self :=
    left_inv_eq_right_inv (a := completedCoproduct ℒ d hneg u)
      (by rw [← map_mul, hvu, map_one])
      (by
        rw [hu.completedCoproduct_eq_completedTensor_self,
          ← (degreeFiltration ℒ d hneg).completedTensor_mul R
            (degreeFiltration ℒ d hneg), huv]
        simp [TauCeti.AlgFiltration.completedTensor_apply])

/-- Ordinary grouplike elements of `U(L)` become completed grouplike in `completedEnveloping`. -/
theorem isCompletedGroupLike_toCompletion_of_isGroupLikeElem (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {g : U} (hg : _root_.IsGroupLikeElem R g) :
    IsCompletedGroupLike ℒ d hneg ((degreeFiltration ℒ d hneg).toCompletion g) where
  completedCounit_eq_one := by simp [hg.counit_eq_one]
  completedCoproduct_eq_completedTensor_self := by
    rw [completedCoproduct_toCompletion, hg.comul_eq_tmul_self,
      ((degreeFiltration ℒ d hneg).completedTensor_toCompletion R
        (degreeFiltration ℒ d hneg) g g).symm]

/-- For a strictly positive Lie grading, every completed grouplike element is congruent to `1`
modulo the first completion ideal. -/
theorem IsCompletedGroupLike.sub_one_mem_completionIdeal_one
    {hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥}
    {u : completedEnveloping ℒ d (fun n hn => hpos n hn.le)}
    (hu : IsCompletedGroupLike ℒ d (fun n hn => hpos n hn.le) u) :
    u - 1 ∈ (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).completionIdeal 1 :=
  (completedCounit_eq_one_iff ℒ d hpos).mp hu.completedCounit_eq_one

section Rational

variable [Algebra ℚ R]

/-- `completedCoproduct` commutes with `completedExp` on the first completion ideal. -/
@[simp]
theorem completedCoproduct_completedExp (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    (x : (degreeFiltration ℒ d hneg).completionIdeal 1) :
    completedCoproduct ℒ d hneg ((degreeFiltration ℒ d hneg).completedExp x) =
      ((degreeFiltration ℒ d hneg).tensorProduct R
        (degreeFiltration ℒ d hneg)).completedExp
          ⟨completedCoproduct ℒ d hneg x,
            completedCoproduct_mem_completionIdeal ℒ d hneg x.property⟩ := by
  refine ((degreeFiltration ℒ d hneg).tensorProduct R
    (degreeFiltration ℒ d hneg)).completion_ext fun k => ?_
  simp only [projection_completedCoproduct, TauCeti.AlgFiltration.projection_completedExp]
  exact ((degreeFiltration ℒ d hneg).isNilpotent_projection x.property k).map_exp _

private theorem completedTensor_completedExp_self (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    (x : (degreeFiltration ℒ d hneg).completionIdeal 1) :
    (degreeFiltration ℒ d hneg).completedTensor R (degreeFiltration ℒ d hneg)
        ((degreeFiltration ℒ d hneg).completedExp x)
        ((degreeFiltration ℒ d hneg).completedExp x) =
      ((degreeFiltration ℒ d hneg).tensorProduct R
        (degreeFiltration ℒ d hneg)).completedExp
          (⟨(degreeFiltration ℒ d hneg).includeLeftCompletion R
                (degreeFiltration ℒ d hneg) x,
              (degreeFiltration ℒ d hneg).includeLeftCompletion_mem_completionIdeal
                R (degreeFiltration ℒ d hneg) x.property⟩ +
            ⟨(degreeFiltration ℒ d hneg).includeRightCompletion R
                (degreeFiltration ℒ d hneg) x,
              (degreeFiltration ℒ d hneg).includeRightCompletion_mem_completionIdeal
                R (degreeFiltration ℒ d hneg) x.property⟩) := by
  let 𝒯 := (degreeFiltration ℒ d hneg).tensorProduct R (degreeFiltration ℒ d hneg)
  have hL : (degreeFiltration ℒ d hneg).includeLeftCompletion R (degreeFiltration ℒ d hneg)
        ((degreeFiltration ℒ d hneg).completedExp x) =
      𝒯.completedExp ⟨(degreeFiltration ℒ d hneg).includeLeftCompletion R
          (degreeFiltration ℒ d hneg) x,
        (degreeFiltration ℒ d hneg).includeLeftCompletion_mem_completionIdeal
          R (degreeFiltration ℒ d hneg) x.property⟩ := by
    refine 𝒯.completion_ext fun k => ?_
    simp only [𝒯, TauCeti.AlgFiltration.projection_includeLeftCompletion,
      TauCeti.AlgFiltration.projection_completedExp]
    exact ((degreeFiltration ℒ d hneg).isNilpotent_projection x.property k).map_exp _
  have hR : (degreeFiltration ℒ d hneg).includeRightCompletion R (degreeFiltration ℒ d hneg)
        ((degreeFiltration ℒ d hneg).completedExp x) =
      𝒯.completedExp ⟨(degreeFiltration ℒ d hneg).includeRightCompletion R
          (degreeFiltration ℒ d hneg) x,
        (degreeFiltration ℒ d hneg).includeRightCompletion_mem_completionIdeal
          R (degreeFiltration ℒ d hneg) x.property⟩ := by
    refine 𝒯.completion_ext fun k => ?_
    simp only [𝒯, TauCeti.AlgFiltration.projection_includeRightCompletion,
      TauCeti.AlgFiltration.projection_completedExp]
    exact ((degreeFiltration ℒ d hneg).isNilpotent_projection x.property k).map_exp _
  have hcomm :=
    (degreeFiltration ℒ d hneg).commute_includeLeftCompletion_includeRightCompletion
      R (degreeFiltration ℒ d hneg) (x : completedEnveloping ℒ d hneg) x
  rw [TauCeti.AlgFiltration.completedTensor_apply, hL, hR, ← 𝒯.completedExp_add _ _ hcomm]

/-- Over a commutative `ℚ`-algebra, the completed exponential of an element of the first
completion ideal is completed grouplike if and only if that element is completed primitive. -/
@[simp]
theorem isCompletedGroupLike_completedExp_iff (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    (x : (degreeFiltration ℒ d hneg).completionIdeal 1) :
    IsCompletedGroupLike ℒ d hneg ((degreeFiltration ℒ d hneg).completedExp x) ↔
      IsCompletedPrimitive ℒ d hneg (x : completedEnveloping ℒ d hneg) := by
  let 𝒯 := (degreeFiltration ℒ d hneg).tensorProduct R (degreeFiltration ℒ d hneg)
  have hcounit : completedCounit ℒ d hneg ((degreeFiltration ℒ d hneg).completedExp x) = 1 := by
    have h0 := completedCounit_eq_zero_of_mem_completionIdeal_one ℒ d hneg
      ((degreeFiltration ℒ d hneg).completedExp_sub_one_mem x)
    rwa [map_sub, map_one, sub_eq_zero] at h0
  rw [isCompletedGroupLike_iff, isCompletedPrimitive_iff_includeCompletion, hcounit,
    completedCoproduct_completedExp, completedTensor_completedExp_self]
  simp only [true_and]
  refine ⟨fun h => ?_, fun h => congrArg 𝒯.completedExp (Subtype.ext h)⟩
  let a : 𝒯.completionIdeal 1 := ⟨completedCoproduct ℒ d hneg x,
    completedCoproduct_mem_completionIdeal ℒ d hneg x.property⟩
  let b : 𝒯.completionIdeal 1 :=
    ⟨(degreeFiltration ℒ d hneg).includeLeftCompletion R (degreeFiltration ℒ d hneg) x,
      (degreeFiltration ℒ d hneg).includeLeftCompletion_mem_completionIdeal
        R (degreeFiltration ℒ d hneg) x.property⟩ +
    ⟨(degreeFiltration ℒ d hneg).includeRightCompletion R (degreeFiltration ℒ d hneg) x,
      (degreeFiltration ℒ d hneg).includeRightCompletion_mem_completionIdeal
        R (degreeFiltration ℒ d hneg) x.property⟩
  have hlog :
      𝒯.completedLog ⟨𝒯.completedExp a, 𝒯.completedExp_sub_one_mem a⟩ =
        𝒯.completedLog ⟨𝒯.completedExp b, 𝒯.completedExp_sub_one_mem b⟩ :=
    congrArg 𝒯.completedLog (Subtype.ext h)
  simpa only [TauCeti.AlgFiltration.completedLog_completedExp, a, b, AddMemClass.coe_add]
    using hlog

/-- Over a commutative `ℚ`-algebra, the completed logarithm of an element congruent to `1` modulo
the first completion ideal is completed primitive if and only if that element is completed
grouplike. -/
@[simp]
theorem isCompletedPrimitive_completedLog_iff (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    (u : {u : completedEnveloping ℒ d hneg //
      u - 1 ∈ (degreeFiltration ℒ d hneg).completionIdeal 1}) :
    IsCompletedPrimitive ℒ d hneg ((degreeFiltration ℒ d hneg).completedLog u) ↔
      IsCompletedGroupLike ℒ d hneg (u : completedEnveloping ℒ d hneg) := by
  simpa only [TauCeti.AlgFiltration.completedExp_completedLog, Subtype.coe_mk] using
    (isCompletedGroupLike_completedExp_iff ℒ d hneg
      ⟨(degreeFiltration ℒ d hneg).completedLog u,
        (degreeFiltration ℒ d hneg).completedLog_mem u⟩).symm

/-- For a strictly positive Lie grading over a commutative `ℚ`-algebra, `completedExp` and
`completedLog` identify the completed primitive elements of the first completion ideal with the
completed grouplike elements of `completedEnveloping`. -/
noncomputable def completedPrimitiveExpEquiv (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) :
    {x : (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).completionIdeal 1 //
        IsCompletedPrimitive ℒ d (fun n hn => hpos n hn.le)
          (x : completedEnveloping ℒ d (fun n hn => hpos n hn.le))} ≃
      {u : completedEnveloping ℒ d (fun n hn => hpos n hn.le) //
        IsCompletedGroupLike ℒ d (fun n hn => hpos n hn.le) u} where
  toFun x := ⟨(degreeFiltration ℒ d (fun n hn => hpos n hn.le)).completedExp x.1,
    (isCompletedGroupLike_completedExp_iff ℒ d _ x.1).mpr x.2⟩
  invFun u :=
    let u' : {v : completedEnveloping ℒ d (fun n hn => hpos n hn.le) //
        v - 1 ∈ (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).completionIdeal 1} :=
      ⟨u.1, u.2.sub_one_mem_completionIdeal_one ℒ d⟩
    ⟨⟨(degreeFiltration ℒ d (fun n hn => hpos n hn.le)).completedLog u',
      (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).completedLog_mem u'⟩,
      (isCompletedPrimitive_completedLog_iff ℒ d _ u').mpr u.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact (degreeFiltration ℒ d _).completedLog_completedExp x.1
  right_inv u := by
    apply Subtype.ext
    exact (degreeFiltration ℒ d _).completedExp_completedLog
      ⟨u.1, u.2.sub_one_mem_completionIdeal_one ℒ d⟩

@[simp]
theorem coe_completedPrimitiveExpEquiv (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥)
    (x : {x : (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).completionIdeal 1 //
      IsCompletedPrimitive ℒ d (fun n hn => hpos n hn.le)
        (x : completedEnveloping ℒ d (fun n hn => hpos n hn.le))}) :
    (completedPrimitiveExpEquiv ℒ d hpos x :
      completedEnveloping ℒ d (fun n hn => hpos n hn.le)) =
      (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).completedExp x.1 :=
  (rfl)

@[simp]
theorem coe_completedPrimitiveExpEquiv_symm (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥)
    (u : {u : completedEnveloping ℒ d (fun n hn => hpos n hn.le) //
      IsCompletedGroupLike ℒ d (fun n hn => hpos n hn.le) u}) :
    ((completedPrimitiveExpEquiv ℒ d hpos).symm u :
      completedEnveloping ℒ d (fun n hn => hpos n hn.le)) =
      (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).completedLog
        ⟨u.1, u.2.sub_one_mem_completionIdeal_one ℒ d⟩ :=
  (rfl)

end Rational

end TauCeti.UniversalEnvelopingAlgebra
