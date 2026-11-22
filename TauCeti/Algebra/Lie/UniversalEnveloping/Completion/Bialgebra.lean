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

import Mathlib.RingTheory.Bialgebra.TensorProduct
import TauCeti.RingTheory.FilteredAlgebra.Exp.Map
import TauCeti.RingTheory.FilteredAlgebra.TensorProduct.Exp

/-!
# Completed bialgebra structure on graded universal enveloping algebras

For a Lie algebra `L` over a commutative ring `R` graded by an additive monoid `Γ` with an integral
degree functional `d : Γ →+ ℤ` and no negative-degree components, the enveloping algebra `U(L)`
carries the total-degree filtration `TauCeti.UniversalEnvelopingAlgebra.degreeFiltration`. Its
compatible-family completion `completedEnveloping` is not an ordinary coalgebra, because the
completed tensor product is larger than the algebraic tensor product of completions, and the finite
quotients `U(L) ⧸ (degreeFiltration ℒ d hneg).ideal (k + 1)` are not quotient coalgebras.
Meanwhile, the bialgebra comultiplication `Δ : U(L) → U(L) ⊗[R] U(L)` preserves total
filtration order for the total-degree tensor filtration, so it extends to an `R`-algebra
homomorphism `completedCoproduct` into the completed tensor square, while the counit descends
through order zero to `completedCounit`.

Within `completedEnveloping`, an element `x` is completed primitive (`IsCompletedPrimitive`) when
`Δ̂(x) = x ⊗̂ 1 + 1 ⊗̂ x`, and completed grouplike (`IsCompletedGroupLike`) when
`ε̂(x) = 1` and `Δ̂(x) = x ⊗̂ x`. Over any commutative ring, completed primitive elements
have completed counit zero and form a Lie subalgebra under the associative commutator, while
completed grouplike elements form a submonoid closed under two-sided inverses. Over a commutative
`ℚ`-algebra, `completedExp` and `completedLog` exchange the completed primitive elements of the
first completion ideal with the completed grouplike elements congruent to `1`; when `L` is
supported in strictly positive degrees, every completed primitive element lies in the first
completion ideal and every completed grouplike element is automatically congruent to `1`.

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
  primitive elements and completed grouplike elements for a strictly positive Lie grading over a
  commutative `ℚ`-algebra.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.degreeFiltration_le_comap_comulAlgHom`: comultiplication
  preserves every degree-filtration ideal.
* `TauCeti.UniversalEnvelopingAlgebra.IsCompletedPrimitive.completedCounit_eq_zero`: every
  completed primitive element has completed counit zero.
* `TauCeti.UniversalEnvelopingAlgebra.IsCompletedPrimitive.comul_sub_mem_tensorProduct_ideal`:
  every finite representative of a completed primitive element has primitive defect in the
  corresponding tensor-filtration ideal.
* `TauCeti.UniversalEnvelopingAlgebra.isCompletedGroupLike_completedExp_iff` and
  `TauCeti.UniversalEnvelopingAlgebra.isCompletedPrimitive_completedLog_iff`: `completedExp` and
  `completedLog` exchange completed primitive and completed grouplike elements.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter II, §6.
* J.-P. Serre, *Lie Algebras and Lie Groups*, Part I, Chapter IV.
* Formal analogues for ordinary bialgebras: `Mathlib/RingTheory/Coalgebra/GroupLike.lean` and
  `Mathlib/RingTheory/Bialgebra/GroupLike.lean` (by Yaël Dillies and Michał Mrugała), and
  `Mathlib/RingTheory/Bialgebra/Primitive.lean` (by Robert Hawkins).
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L) (d : Γ →+ ℤ)

variable [DecidableEq Γ] [GradedLieAlgebra ℒ]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "𝓕" => degreeFiltration ℒ d

private theorem comul_prod_mem_tensorProduct (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    ∀ (l : List (Σ i, ℒ i)), (∀ a ∈ l, 0 ≤ d a.1) →
      Bialgebra.comulAlgHom R U (l.map (fun x => ι R (x.2 : L))).prod ∈
        ((𝓕 hneg).tensorProduct R (𝓕 hneg)).ideal (d (l.map Sigma.fst).sum).toNat
  | [], _ => by simp [Submodule.mem_top]
  | a :: l, hnonneg => by
    let 𝒯 := (𝓕 hneg).tensorProduct R (𝓕 hneg)
    have ha0 : 0 ≤ d a.1 := hnonneg a List.mem_cons_self
    have hl : ∀ b ∈ l, 0 ≤ d b.1 := fun b hb => hnonneg b (List.mem_cons_of_mem a hb)
    have : 0 ≤ d (l.map Sigma.fst).sum := by
      rw [map_list_sum, List.map_map]
      exact List.sum_nonneg <| List.forall_mem_map.mpr hl
    have hι : ι R (a.2 : L) ∈ (𝓕 hneg).ideal (d a.1).toNat :=
      ι_mem_degreeFiltration ℒ d hneg a.2.property (by omega)
    have hhead : Bialgebra.comulAlgHom R U (ι R (a.2 : L)) ∈ 𝒯.ideal (d a.1).toNat := by
      rw [Bialgebra.comulAlgHom_apply, comul_ι]
      exact Ideal.add_mem _
        ((𝓕 hneg).tmul_mem_tensorProduct_ideal R (𝓕 hneg)
          (a := (d a.1).toNat) (b := 0) (by omega) hι (by simp))
        ((𝓕 hneg).tmul_mem_tensorProduct_ideal R (𝓕 hneg)
          (a := 0) (b := (d a.1).toNat) (by omega) (by simp) hι)
    have htoNat : (d ((a :: l).map Sigma.fst).sum).toNat =
        (d a.1).toNat + (d (l.map Sigma.fst).sum).toNat := by
      simp only [List.map_cons, List.sum_cons, map_add]; omega
    rw [htoNat, List.map_cons, List.prod_cons, map_mul]
    exact 𝒯.mul_mem hhead (comul_prod_mem_tensorProduct hneg l hl)

/-- Comultiplication preserves the total-degree filtration on a graded enveloping algebra. -/
theorem degreeFiltration_le_comap_comulAlgHom (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (k : ℕ) :
    (𝓕 hneg).ideal k ≤
      (((𝓕 hneg).tensorProduct R (𝓕 hneg)).ideal k).comap (Bialgebra.comulAlgHom R U) := by
  let 𝒯 := (𝓕 hneg).tensorProduct R (𝓕 hneg)
  rw [degreeFiltration_ideal_le_iff]; intro n hn a ha
  refine (Submodule.restrictScalars_mem R _ _).mp <| (homogeneousSubmodule_le_iff ℒ n
    ((𝒯.ideal k).comap (Bialgebra.comulAlgHom R U) |>.restrictScalars R)).mpr (fun l hl => ?_) ha
  rw [Submodule.restrictScalars_mem, Ideal.mem_comap]
  by_cases hnonneg : ∀ a ∈ l, 0 ≤ d a.1
  · exact 𝒯.antitone (by rw [hl]; omega) (comul_prod_mem_tensorProduct ℒ d hneg l hnonneg)
  · push Not at hnonneg; obtain ⟨b, hbl, hbneg⟩ := hnonneg
    have hb0 : (b.2 : L) = 0 := by simpa [hneg b.1 hbneg] using b.2.property
    rw [List.prod_eq_zero (List.mem_map.mpr ⟨b, hbl, by simp [hb0]⟩), map_zero]
    exact zero_mem _

/-- The completion of a graded universal enveloping algebra along its total-degree filtration. -/
noncomputable abbrev completedEnveloping (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :=
  (𝓕 hneg).completion

/-- The completed comultiplication, induced on `completedEnveloping` by `Bialgebra.comulAlgHom`. -/
noncomputable def completedCoproduct (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    completedEnveloping ℒ d hneg →ₐ[R] ((𝓕 hneg).tensorProduct R (𝓕 hneg)).completion :=
  (𝓕 hneg).mapCompletionₐ ((𝓕 hneg).tensorProduct R (𝓕 hneg))
    (Bialgebra.comulAlgHom R U) id monotone_id
    (fun k => degreeFiltration_le_comap_comulAlgHom ℒ d hneg (k + 1))

/-- At order `k`, `completedCoproduct` is the quotient map induced by comultiplication. -/
@[simp]
theorem projection_completedCoproduct (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (k : ℕ)
    (x : completedEnveloping ℒ d hneg) :
    ((𝓕 hneg).tensorProduct R (𝓕 hneg)).projection k (completedCoproduct ℒ d hneg x) =
      Ideal.quotientMapₐ (((𝓕 hneg).tensorProduct R (𝓕 hneg)).ideal (k + 1))
        (Bialgebra.comulAlgHom R U) (degreeFiltration_le_comap_comulAlgHom ℒ d hneg (k + 1))
        ((𝓕 hneg).projection k x) :=
  (𝓕 hneg).projection_mapCompletionₐ _ _ id monotone_id _ k x

/-- `completedCoproduct` extends the ordinary comultiplication along `toCompletion`. -/
@[simp]
theorem completedCoproduct_toCompletion (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (u : U) :
    completedCoproduct ℒ d hneg ((𝓕 hneg).toCompletion u) =
      ((𝓕 hneg).tensorProduct R (𝓕 hneg)).toCompletion (Coalgebra.comul (R := R) u) :=
  (𝓕 hneg).mapCompletionₐ_toCompletion _ _ id monotone_id _ u

/-- `completedCoproduct` preserves every induced completion ideal. -/
theorem completedCoproduct_mem_completionIdeal (hneg : ∀ n, d n < 0 → ℒ n = ⊥) {k : ℕ}
    {x : completedEnveloping ℒ d hneg} (hx : x ∈ (𝓕 hneg).completionIdeal k) :
    completedCoproduct ℒ d hneg x ∈
      ((𝓕 hneg).tensorProduct R (𝓕 hneg)).completionIdeal k :=
  match k with
  | 0 => by simp
  | k + 1 => (𝓕 hneg).mapCompletionₐ_mem_completionIdeal _ _ id monotone_id _ k hx

private theorem degreeFiltration_one_le_ker_counitAlgHom (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    (𝓕 hneg).ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R U) :=
  fun _ hu => (HopfIdeal.mem_augmentation R U).mp
    (HopfIdeal.mem_toIdeal.mp (degreeFiltration_le_augmentation ℒ d hneg Nat.one_pos hu))

/-- The completed counit on `completedEnveloping`, factored through the order-zero projection. -/
noncomputable def completedCounit (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    completedEnveloping ℒ d hneg →ₐ[R] R :=
  (Ideal.Quotient.liftₐ ((𝓕 hneg).ideal 1) (Bialgebra.counitAlgHom R U)
    (fun _ hu => RingHom.mem_ker.mp (degreeFiltration_one_le_ker_counitAlgHom ℒ d hneg hu))).comp
    ((𝓕 hneg).projectionₐ 0)

/-- The completed counit agrees with `Coalgebra.counit` on any order-zero representative. -/
theorem completedCounit_of_representative (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    (x : completedEnveloping ℒ d hneg) (a : U)
    (ha : Ideal.Quotient.mk ((𝓕 hneg).ideal 1) a = (𝓕 hneg).projection 0 x) :
    completedCounit ℒ d hneg x = Coalgebra.counit (R := R) a := by
  rw [completedCounit, AlgHom.comp_apply, AlgFiltration.projectionₐ_apply, ← ha,
    ← Ideal.Quotient.mkₐ_eq_mk R, ← AlgHom.comp_apply, Ideal.Quotient.liftₐ_comp,
    Bialgebra.counitAlgHom_apply]

/-- `completedCounit` extends the ordinary counit along `toCompletion`. -/
@[simp]
theorem completedCounit_toCompletion (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (u : U) :
    completedCounit ℒ d hneg ((𝓕 hneg).toCompletion u) = Coalgebra.counit (R := R) u :=
  completedCounit_of_representative ℒ d hneg _ u ((𝓕 hneg).projection_toCompletion 0 u).symm

/-- Elements of the first completion ideal have completed counit zero. -/
theorem completedCounit_eq_zero_of_mem_completionIdeal_one (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {x : completedEnveloping ℒ d hneg} (hx : x ∈ (𝓕 hneg).completionIdeal 1) :
    completedCounit ℒ d hneg x = 0 := by
  rw [AlgFiltration.completionIdeal_succ, RingHom.mem_ker] at hx
  rw [completedCounit, AlgHom.comp_apply, AlgFiltration.projectionₐ_apply, hx, map_zero]

/-- For a strictly positive Lie grading, canonical Lie generators map into the first completion
ideal. -/
theorem toCompletion_ι_mem_completionIdeal_one (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) (x : L) :
    (𝓕 (fun n hn => hpos n hn.le)).toCompletion (ι R x) ∈
      (𝓕 (fun n hn => hpos n hn.le)).completionIdeal 1 :=
  ((𝓕 _).toCompletion_mem_completionIdeal_iff 1 _).mpr (ι_mem_degreeFiltration_one ℒ d hpos x)

/-- For a strictly positive Lie grading, the kernel of `completedCounit` is the first completion
ideal. -/
theorem completedCounit_eq_zero_iff (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥)
    {x : completedEnveloping ℒ d (fun n hn => hpos n hn.le)} :
    completedCounit ℒ d (fun n hn => hpos n hn.le) x = 0 ↔
      x ∈ (𝓕 (fun n hn => hpos n hn.le)).completionIdeal 1 := by
  refine ⟨fun hx => ?_, completedCounit_eq_zero_of_mem_completionIdeal_one ℒ d _⟩
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((𝓕 _).projection 0 x)
  rw [completedCounit_of_representative ℒ d _ x a ha] at hx
  rw [AlgFiltration.completionIdeal_succ, RingHom.mem_ker, ← ha, Ideal.Quotient.eq_zero_iff_mem,
    degreeFiltration_one_eq_augmentation ℒ d hpos]
  exact HopfIdeal.mem_toIdeal.mpr ((HopfIdeal.mem_augmentation R U).mpr hx)

/-- For a strictly positive Lie grading, completed counit one means congruence to `1` modulo the
first completion ideal. -/
theorem completedCounit_eq_one_iff (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥)
    {u : completedEnveloping ℒ d (fun n hn => hpos n hn.le)} :
    completedCounit ℒ d (fun n hn => hpos n hn.le) u = 1 ↔
      u - 1 ∈ (𝓕 (fun n hn => hpos n hn.le)).completionIdeal 1 := by
  rw [← completedCounit_eq_zero_iff ℒ d hpos, map_sub, map_one, sub_eq_zero]

/-- An element `x` of `completedEnveloping` is completed primitive when
`Δ̂(x) = x ⊗̂ 1 + 1 ⊗̂ x`. -/
def IsCompletedPrimitive (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    (x : completedEnveloping ℒ d hneg) : Prop :=
  completedCoproduct ℒ d hneg x =
    (𝓕 hneg).completedTensor R (𝓕 hneg) x 1 + (𝓕 hneg).completedTensor R (𝓕 hneg) 1 x

/-- Unfolding characterization of `IsCompletedPrimitive`. -/
theorem isCompletedPrimitive_iff (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {x : completedEnveloping ℒ d hneg} :
    IsCompletedPrimitive ℒ d hneg x ↔
      completedCoproduct ℒ d hneg x =
        (𝓕 hneg).completedTensor R (𝓕 hneg) x 1 +
          (𝓕 hneg).completedTensor R (𝓕 hneg) 1 x :=
  Iff.rfl

/-- `IsCompletedPrimitive` in terms of the two completed tensor inclusions. -/
theorem isCompletedPrimitive_iff_includeCompletion (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {x : completedEnveloping ℒ d hneg} :
    IsCompletedPrimitive ℒ d hneg x ↔
      completedCoproduct ℒ d hneg x =
        (𝓕 hneg).includeLeftCompletion R (𝓕 hneg) x +
          (𝓕 hneg).includeRightCompletion R (𝓕 hneg) x := by simp [IsCompletedPrimitive]

private theorem tensorProduct_one_le_ker_counitAlgHom (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    ((𝓕 hneg).tensorProduct R (𝓕 hneg)).ideal 1 ≤
      RingHom.ker (Bialgebra.counitAlgHom R (U ⊗[R] U)) := by
  intro t ht
  refine ((tensorFiltrationTail_le_iff (fun n => ((𝓕 hneg).ideal n).restrictScalars R)
      (fun n => ((𝓕 hneg).ideal n).restrictScalars R)
      (P := (RingHom.ker (Bialgebra.counitAlgHom R (U ⊗[R] U))).restrictScalars R)).mpr
    fun a b hab u hu v hv => ?_) (((𝓕 hneg).mem_tensorProduct_ideal_iff R (𝓕 hneg)).mp ht)
  rw [Submodule.restrictScalars_mem, RingHom.mem_ker, Bialgebra.counitAlgHom_apply,
    TensorProduct.counit_tmul]
  have hzero {w : U} (hw : w ∈ (𝓕 hneg).ideal 1) : Coalgebra.counit (R := R) w = 0 := by
    simpa [Bialgebra.counitAlgHom_apply] using
      degreeFiltration_one_le_ker_counitAlgHom ℒ d hneg hw
  rcases Nat.lt_or_ge 0 a with ha | ha
  · simp [hzero ((𝓕 hneg).antitone ha hu)]
  · simp [hzero ((𝓕 hneg).antitone (by omega) hv)]

variable {ℒ d} in
/-- Every completed primitive element has completed counit zero. -/
theorem IsCompletedPrimitive.completedCounit_eq_zero {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {x : completedEnveloping ℒ d hneg} (hx : IsCompletedPrimitive ℒ d hneg x) :
    completedCounit ℒ d hneg x = 0 := by
  let 𝒯 := (𝓕 hneg).tensorProduct R (𝓕 hneg)
  let ε₂ : 𝒯.completion →ₐ[R] R := (Ideal.Quotient.liftₐ (𝒯.ideal (0 + 1))
    (Bialgebra.counitAlgHom R (U ⊗[R] U))
    (fun _ ht => RingHom.mem_ker.mp (tensorProduct_one_le_ker_counitAlgHom ℒ d hneg ht))).comp
    (𝒯.projectionₐ 0)
  have hε₂ {z : 𝒯.completion} {t : U ⊗[R] U}
      (ht : Ideal.Quotient.mk (𝒯.ideal (0 + 1)) t = 𝒯.projection 0 z) :
      ε₂ z = Coalgebra.counit (R := R) t := by
    rw [AlgHom.comp_apply, AlgFiltration.projectionₐ_apply, ← ht,
      ← Ideal.Quotient.mkₐ_eq_mk R, ← AlgHom.comp_apply, Ideal.Quotient.liftₐ_comp,
      Bialgebra.counitAlgHom_apply]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((𝓕 hneg).projection 0 x)
  have h1 : Ideal.Quotient.mk ((𝓕 hneg).ideal (0 + 1)) 1 = (𝓕 hneg).projection 0 1 :=
    (map_one _).symm
  have hL :
      ε₂ ((𝓕 hneg).completedTensor R (𝓕 hneg) x 1) = completedCounit ℒ d hneg x := by
    rw [hε₂ ((𝓕 hneg).projection_completedTensor_of_representatives
        R (𝓕 hneg) 0 x 1 a 1 ha h1).symm,
      TensorProduct.counit_tmul, Bialgebra.counit_one, one_smul]
    exact (completedCounit_of_representative ℒ d hneg x a ha).symm
  have hR :
      ε₂ ((𝓕 hneg).completedTensor R (𝓕 hneg) 1 x) = completedCounit ℒ d hneg x := by
    rw [hε₂ ((𝓕 hneg).projection_completedTensor_of_representatives
        R (𝓕 hneg) 0 1 x 1 a h1 ha).symm,
      TensorProduct.counit_tmul, Bialgebra.counit_one, smul_eq_mul, mul_one]
    exact (completedCounit_of_representative ℒ d hneg x a ha).symm
  have hΔ : ε₂ (completedCoproduct ℒ d hneg x) = completedCounit ℒ d hneg x := by
    rw [hε₂ (by rw [projection_completedCoproduct, ← ha, Ideal.quotient_map_mkₐ,
      Ideal.Quotient.mkₐ_eq_mk, Bialgebra.comulAlgHom_apply])]
    exact (CoalgHomClass.counit_comp_apply (Coalgebra.comulCoalgHom R U) a).trans
      (completedCounit_of_representative ℒ d hneg x a ha).symm
  have hε := congrArg ε₂ hx; rw [hΔ, map_add, hL, hR] at hε; exact left_eq_add.mp hε

variable {ℒ d} in
/-- Any order-`k` representative of a completed primitive element has primitive defect in the
`(k + 1)`-st tensor-filtration ideal. -/
theorem IsCompletedPrimitive.comul_sub_mem_tensorProduct_ideal
    {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {x : completedEnveloping ℒ d hneg} (hx : IsCompletedPrimitive ℒ d hneg x) {k : ℕ} {a : U}
    (ha : Ideal.Quotient.mk ((𝓕 hneg).ideal (k + 1)) a = (𝓕 hneg).projection k x) :
    Coalgebra.comul (R := R) a - (1 ⊗ₜ[R] a + a ⊗ₜ[R] 1) ∈
      ((𝓕 hneg).tensorProduct R (𝓕 hneg)).ideal (k + 1) := by
  have h1 : Ideal.Quotient.mk ((𝓕 hneg).ideal (k + 1)) (1 : U) = (𝓕 hneg).projection k 1 :=
    (map_one _).symm
  have hproj := congrArg (((𝓕 hneg).tensorProduct R (𝓕 hneg)).projection k) hx
  rwa [map_add, projection_completedCoproduct, ← ha, Ideal.quotient_map_mkₐ,
    Ideal.Quotient.mkₐ_eq_mk, Bialgebra.comulAlgHom_apply,
    (𝓕 hneg).projection_completedTensor_of_representatives R (𝓕 hneg) k x 1 a 1 ha h1,
    (𝓕 hneg).projection_completedTensor_of_representatives R (𝓕 hneg) k 1 x 1 a h1 ha,
    add_comm (Ideal.Quotient.mk _ (a ⊗ₜ[R] 1)), ← map_add, Ideal.Quotient.eq] at hproj

variable {ℒ d} in
/-- For a strictly positive Lie grading, every completed primitive element lies in the first
completion ideal. -/
theorem IsCompletedPrimitive.mem_completionIdeal_one {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {x : completedEnveloping ℒ d hneg} (hx : IsCompletedPrimitive ℒ d hneg x)
    (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) : x ∈ (𝓕 hneg).completionIdeal 1 :=
  (completedCounit_eq_zero_iff ℒ d hpos).mp hx.completedCounit_eq_zero

/-- Zero is completed primitive. -/
@[simp]
theorem IsCompletedPrimitive.zero (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    IsCompletedPrimitive ℒ d hneg 0 := by simp [isCompletedPrimitive_iff_includeCompletion]

variable {ℒ d} in
/-- Completed primitive elements are closed under addition. -/
theorem IsCompletedPrimitive.add {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {x y : completedEnveloping ℒ d hneg}
    (hx : IsCompletedPrimitive ℒ d hneg x) (hy : IsCompletedPrimitive ℒ d hneg y) :
    IsCompletedPrimitive ℒ d hneg (x + y) := by
  rw [isCompletedPrimitive_iff_includeCompletion] at hx hy ⊢
  rw [map_add, hx, hy, map_add, map_add]; abel

variable {ℒ d} in
/-- Completed primitive elements are closed under negation. -/
theorem IsCompletedPrimitive.neg {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {x : completedEnveloping ℒ d hneg} (hx : IsCompletedPrimitive ℒ d hneg x) :
    IsCompletedPrimitive ℒ d hneg (-x) := by
  rw [isCompletedPrimitive_iff_includeCompletion] at hx ⊢
  rw [map_neg, hx, map_neg, map_neg, neg_add]

variable {ℒ d} in
/-- Completed primitive elements are closed under subtraction. -/
theorem IsCompletedPrimitive.sub {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {x y : completedEnveloping ℒ d hneg}
    (hx : IsCompletedPrimitive ℒ d hneg x) (hy : IsCompletedPrimitive ℒ d hneg y) :
    IsCompletedPrimitive ℒ d hneg (x - y) := by simpa only [sub_eq_add_neg] using hx.add hy.neg

variable {ℒ d} in
/-- Completed primitive elements are closed under scalar multiplication. -/
theorem IsCompletedPrimitive.smul {hneg : ∀ n, d n < 0 → ℒ n = ⊥} (r : R)
    {x : completedEnveloping ℒ d hneg} (hx : IsCompletedPrimitive ℒ d hneg x) :
    IsCompletedPrimitive ℒ d hneg (r • x) := by
  rw [isCompletedPrimitive_iff_includeCompletion] at hx ⊢
  rw [map_smul, hx, map_smul, map_smul, smul_add]

variable {ℒ d} in
/-- Completed primitive elements are closed under the associative commutator bracket. -/
theorem IsCompletedPrimitive.lie {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {x y : completedEnveloping ℒ d hneg}
    (hx : IsCompletedPrimitive ℒ d hneg x) (hy : IsCompletedPrimitive ℒ d hneg y) :
    IsCompletedPrimitive ℒ d hneg ⁅x, y⁆ := by
  rw [isCompletedPrimitive_iff_includeCompletion] at hx hy ⊢
  have hxy :=
    ((𝓕 hneg).commute_includeLeftCompletion_includeRightCompletion R (𝓕 hneg) x y).eq
  have hyx :=
    ((𝓕 hneg).commute_includeLeftCompletion_includeRightCompletion R (𝓕 hneg) y x).eq
  simp only [LieRing.of_associative_ring_bracket, map_sub, map_mul, hx, hy, add_mul, mul_add,
    hxy, hyx]; abel

/-- The commutator Lie subalgebra of completed primitive elements in `completedEnveloping`. -/
noncomputable def completedPrimitiveLieSubalgebra (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    LieSubalgebra R (completedEnveloping ℒ d hneg) where
  carrier := {x | IsCompletedPrimitive ℒ d hneg x}
  add_mem' hx hy := hx.add hy
  zero_mem' := IsCompletedPrimitive.zero ℒ d hneg
  smul_mem' r _ hx := hx.smul r
  lie_mem' hx hy := hx.lie hy

@[simp]
theorem mem_completedPrimitiveLieSubalgebra_iff (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {x : completedEnveloping ℒ d hneg} :
    x ∈ completedPrimitiveLieSubalgebra ℒ d hneg ↔
      IsCompletedPrimitive ℒ d hneg x := Iff.rfl

/-- Ordinary primitive elements of `U(L)` become completed primitive in `completedEnveloping`. -/
theorem isCompletedPrimitive_toCompletion_of_isPrimitiveElem (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {p : U} (hp : Bialgebra.IsPrimitiveElem R p) :
    IsCompletedPrimitive ℒ d hneg ((𝓕 hneg).toCompletion p) := by
  simp [IsCompletedPrimitive, hp.comul_eq_tmul_add_tmul, add_comm]

/-- Canonical Lie generators map to completed primitive elements in `completedEnveloping`. -/
theorem isCompletedPrimitive_toCompletion_ι (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (x : L) :
    IsCompletedPrimitive ℒ d hneg ((𝓕 hneg).toCompletion (ι R x)) :=
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
    completedCoproduct ℒ d hneg u = (𝓕 hneg).completedTensor R (𝓕 hneg) u u

/-- One is completed grouplike. -/
@[simp]
theorem IsCompletedGroupLike.one (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    IsCompletedGroupLike ℒ d hneg 1 where
  completedCounit_eq_one := map_one _
  completedCoproduct_eq_completedTensor_self := by simp [AlgFiltration.completedTensor_apply]

variable {ℒ d} in
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
      ((𝓕 hneg).completedTensor_mul R (𝓕 hneg) u v u v).symm]

/-- Completed grouplike elements form a multiplicative submonoid of `completedEnveloping`. -/
noncomputable def completedGroupLikeSubmonoid (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    Submonoid (completedEnveloping ℒ d hneg) where
  carrier := {u | IsCompletedGroupLike ℒ d hneg u}
  one_mem' := IsCompletedGroupLike.one ℒ d hneg
  mul_mem' hu hv := hu.mul hv

@[simp]
theorem mem_completedGroupLikeSubmonoid_iff (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {u : completedEnveloping ℒ d hneg} :
    u ∈ completedGroupLikeSubmonoid ℒ d hneg ↔ IsCompletedGroupLike ℒ d hneg u := Iff.rfl

variable {ℒ d} in
/-- Completed grouplike elements are closed under natural powers. -/
theorem IsCompletedGroupLike.pow {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {u : completedEnveloping ℒ d hneg} (hu : IsCompletedGroupLike ℒ d hneg u) (n : ℕ) :
    IsCompletedGroupLike ℒ d hneg (u ^ n) := (completedGroupLikeSubmonoid ℒ d hneg).pow_mem hu n

variable {ℒ d} in
/-- Completed grouplike elements are closed under two-sided inverses. -/
theorem IsCompletedGroupLike.of_mul_eq_one {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {u v : completedEnveloping ℒ d hneg} (huv : u * v = 1) (hvu : v * u = 1)
    (hu : IsCompletedGroupLike ℒ d hneg u) : IsCompletedGroupLike ℒ d hneg v where
  completedCounit_eq_one := left_inv_eq_right_inv (a := completedCounit ℒ d hneg u)
    (by rw [← map_mul, hvu, map_one]) (by rw [hu.completedCounit_eq_one, one_mul])
  completedCoproduct_eq_completedTensor_self := left_inv_eq_right_inv
    (a := completedCoproduct ℒ d hneg u) (by rw [← map_mul, hvu, map_one]) (by
      rw [hu.completedCoproduct_eq_completedTensor_self,
        ← (𝓕 hneg).completedTensor_mul R (𝓕 hneg), huv]
      simp [AlgFiltration.completedTensor_apply])

/-- Ordinary grouplike elements of `U(L)` become completed grouplike in `completedEnveloping`. -/
theorem isCompletedGroupLike_toCompletion_of_isGroupLikeElem (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {g : U} (hg : _root_.IsGroupLikeElem R g) :
    IsCompletedGroupLike ℒ d hneg ((𝓕 hneg).toCompletion g) where
  completedCounit_eq_one := by simp [hg.counit_eq_one]
  completedCoproduct_eq_completedTensor_self := by
    rw [completedCoproduct_toCompletion, hg.comul_eq_tmul_self,
      ((𝓕 hneg).completedTensor_toCompletion R (𝓕 hneg) g g).symm]

variable {ℒ d} in
/-- For a strictly positive Lie grading, every completed grouplike element is congruent to `1`
modulo the first completion ideal. -/
theorem IsCompletedGroupLike.sub_one_mem_completionIdeal_one
    {hneg : ∀ n, d n < 0 → ℒ n = ⊥} {u : completedEnveloping ℒ d hneg}
    (hu : IsCompletedGroupLike ℒ d hneg u) (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) :
    u - 1 ∈ (𝓕 hneg).completionIdeal 1 :=
  (completedCounit_eq_one_iff ℒ d hpos).mp hu.completedCounit_eq_one

section Rational

variable [Algebra ℚ R]

/-- `completedCoproduct` commutes with `completedExp` on the first completion ideal. -/
@[simp]
theorem completedCoproduct_completedExp (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    (x : (𝓕 hneg).completionIdeal 1) :
    completedCoproduct ℒ d hneg ((𝓕 hneg).completedExp x) =
      ((𝓕 hneg).tensorProduct R (𝓕 hneg)).completedExp
        ⟨completedCoproduct ℒ d hneg x,
          completedCoproduct_mem_completionIdeal ℒ d hneg x.property⟩ :=
  (𝓕 hneg).mapCompletionₐ_completedExp _ (Bialgebra.comulAlgHom R U) id monotone_id
    (fun k => degreeFiltration_le_comap_comulAlgHom ℒ d hneg (k + 1))
    (degreeFiltration_le_comap_comulAlgHom ℒ d hneg 1) x

/-- Over a commutative `ℚ`-algebra, the completed exponential of an element of the first
completion ideal is completed grouplike if and only if that element is completed primitive. -/
@[simp]
theorem isCompletedGroupLike_completedExp_iff (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    (x : (𝓕 hneg).completionIdeal 1) :
    IsCompletedGroupLike ℒ d hneg ((𝓕 hneg).completedExp x) ↔
      IsCompletedPrimitive ℒ d hneg (x : completedEnveloping ℒ d hneg) := by
  let 𝒯 := (𝓕 hneg).tensorProduct R (𝓕 hneg)
  let a : 𝒯.completionIdeal 1 := ⟨completedCoproduct ℒ d hneg x,
    completedCoproduct_mem_completionIdeal ℒ d hneg x.property⟩
  let bL : 𝒯.completionIdeal 1 := ⟨(𝓕 hneg).includeLeftCompletion R (𝓕 hneg) x,
    (𝓕 hneg).includeLeftCompletion_mem_completionIdeal R (𝓕 hneg) x.property⟩
  let bR : 𝒯.completionIdeal 1 := ⟨(𝓕 hneg).includeRightCompletion R (𝓕 hneg) x,
    (𝓕 hneg).includeRightCompletion_mem_completionIdeal R (𝓕 hneg) x.property⟩
  have hcounit : completedCounit ℒ d hneg ((𝓕 hneg).completedExp x) = 1 := by
    have h0 := completedCounit_eq_zero_of_mem_completionIdeal_one ℒ d hneg
      ((𝓕 hneg).completedExp_sub_one_mem x)
    rwa [map_sub, map_one, sub_eq_zero] at h0
  rw [isCompletedGroupLike_iff, isCompletedPrimitive_iff_includeCompletion, hcounit,
    completedCoproduct_completedExp, (𝓕 hneg).completedTensor_completedExp R (𝓕 hneg) x x]
  refine ⟨fun h => ?_, fun h => ⟨rfl, congrArg 𝒯.completedExp (Subtype.ext h)⟩⟩
  have hlog := congrArg 𝒯.completedLog (Subtype.ext h.2 :
    (⟨𝒯.completedExp a, 𝒯.completedExp_sub_one_mem a⟩ :
      {u : 𝒯.completion // u - 1 ∈ 𝒯.completionIdeal 1}) =
    ⟨𝒯.completedExp (bL + bR), 𝒯.completedExp_sub_one_mem (bL + bR)⟩)
  simpa only [AlgFiltration.completedLog_completedExp, a, bL, bR, AddMemClass.coe_add] using hlog

/-- Over a commutative `ℚ`-algebra, the completed logarithm of an element congruent to `1` modulo
the first completion ideal is completed primitive if and only if that element is completed
grouplike. -/
@[simp]
theorem isCompletedPrimitive_completedLog_iff (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    (u : {u : completedEnveloping ℒ d hneg // u - 1 ∈ (𝓕 hneg).completionIdeal 1}) :
    IsCompletedPrimitive ℒ d hneg ((𝓕 hneg).completedLog u) ↔
      IsCompletedGroupLike ℒ d hneg (u : completedEnveloping ℒ d hneg) := by
  simpa only [AlgFiltration.completedExp_completedLog, Subtype.coe_mk] using
    (isCompletedGroupLike_completedExp_iff ℒ d hneg
      ⟨(𝓕 hneg).completedLog u, (𝓕 hneg).completedLog_mem u⟩).symm

/-- For a strictly positive Lie grading over a commutative `ℚ`-algebra, `completedExp` and
`completedLog` identify the completed primitive elements with the completed grouplike elements of
`completedEnveloping`. -/
noncomputable def completedPrimitiveExpEquiv (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) :
    completedPrimitiveLieSubalgebra ℒ d (fun n hn => hpos n hn.le) ≃
      {u : completedEnveloping ℒ d (fun n hn => hpos n hn.le) //
        IsCompletedGroupLike ℒ d (fun n hn => hpos n hn.le) u} where
  toFun x :=
    ⟨(𝓕 _).completedExp
        ⟨x.1, ((mem_completedPrimitiveLieSubalgebra_iff _ _ _).mp
          x.2).mem_completionIdeal_one hpos⟩,
      (isCompletedGroupLike_completedExp_iff ℒ d _
        ⟨x.1, ((mem_completedPrimitiveLieSubalgebra_iff _ _ _).mp x.2).mem_completionIdeal_one
          hpos⟩).mpr ((mem_completedPrimitiveLieSubalgebra_iff _ _ _).mp x.2)⟩
  invFun u :=
    let u' : {v : completedEnveloping ℒ d (fun n hn => hpos n hn.le) //
        v - 1 ∈ (𝓕 (fun n hn => hpos n hn.le)).completionIdeal 1} :=
      ⟨u.1, u.2.sub_one_mem_completionIdeal_one hpos⟩
    ⟨(𝓕 _).completedLog u', (mem_completedPrimitiveLieSubalgebra_iff _ _ _).mpr
      ((isCompletedPrimitive_completedLog_iff ℒ d _ u').mpr u.2)⟩
  left_inv x := Subtype.ext <| (𝓕 _).completedLog_completedExp
    ⟨x.1, ((mem_completedPrimitiveLieSubalgebra_iff _ _ _).mp x.2).mem_completionIdeal_one hpos⟩
  right_inv u := Subtype.ext <| (𝓕 _).completedExp_completedLog
    ⟨u.1, u.2.sub_one_mem_completionIdeal_one hpos⟩

@[simp]
theorem coe_completedPrimitiveExpEquiv (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥)
    (x : completedPrimitiveLieSubalgebra ℒ d (fun n hn => hpos n hn.le)) :
    (completedPrimitiveExpEquiv ℒ d hpos x :
      completedEnveloping ℒ d (fun n hn => hpos n hn.le)) =
      (𝓕 (fun n hn => hpos n hn.le)).completedExp
        ⟨x.1, ((mem_completedPrimitiveLieSubalgebra_iff _ _ _).mp x.2).mem_completionIdeal_one
          hpos⟩ := (rfl)

@[simp]
theorem coe_completedPrimitiveExpEquiv_symm (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥)
    (u : {u : completedEnveloping ℒ d (fun n hn => hpos n hn.le) //
      IsCompletedGroupLike ℒ d (fun n hn => hpos n hn.le) u}) :
    ((completedPrimitiveExpEquiv ℒ d hpos).symm u :
      completedEnveloping ℒ d (fun n hn => hpos n hn.le)) =
      (𝓕 (fun n hn => hpos n hn.le)).completedLog
        ⟨u.1, u.2.sub_one_mem_completionIdeal_one hpos⟩ := (rfl)

end Rational

end TauCeti.UniversalEnvelopingAlgebra
