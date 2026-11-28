/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.GroupLike
public import TauCeti.Algebra.Lie.UniversalEnveloping.Completion.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.FilteredBialgebra

import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# Completed coproduct, counit, and primitive and grouplike elements

For a Lie algebra `L` over `R` graded by `Γ` with degree functional `d : Γ →+ ℤ` and no
negative-degree components, the bialgebra comultiplication extends to `completedCoproduct` into the
completed tensor square, while the counit descends to `completedCounit`.

Within `completedEnveloping`, completed primitive elements (`IsCompletedPrimitive`) have completed
counit zero and form a Lie subalgebra (`completedPrimitiveLieSubalgebra`), while completed
grouplike elements (`IsCompletedGroupLike`) form a submonoid (`completedGroupLikeSubmonoid`)
closed under two-sided inverses.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter II, §6.
* J.-P. Serre, *Lie Algebras and Lie Groups*, Part I, Chapter IV.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L) (d : Γ →+ ℤ) [DecidableEq Γ] [GradedLieAlgebra ℒ]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "𝓕" => degreeFiltration ℒ d

/-- The completed comultiplication, induced on `completedEnveloping` by `Bialgebra.comulAlgHom`. -/
noncomputable def completedCoproduct (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    completedEnveloping ℒ d hneg →ₐ[R] ((𝓕 hneg).tensorProduct R (𝓕 hneg)).completion :=
  (𝓕 hneg).mapCompletionₐ ((𝓕 hneg).tensorProduct R (𝓕 hneg))
    (Bialgebra.comulAlgHom R U) id monotone_id
    (fun k => degreeFiltration_le_comap_comulAlgHom ℒ d hneg (k + 1))

/-- The completed comultiplication is the algebra completion map of `Bialgebra.comulAlgHom`. -/
theorem completedCoproduct_eq_mapCompletionₐ (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    completedCoproduct ℒ d hneg =
      (𝓕 hneg).mapCompletionₐ ((𝓕 hneg).tensorProduct R (𝓕 hneg))
        (Bialgebra.comulAlgHom R U) id monotone_id
        (fun k => degreeFiltration_le_comap_comulAlgHom ℒ d hneg (k + 1)) := (rfl)

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
theorem completedCoproduct_mem_completionIdeal (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    ∀ {k : ℕ} {x : completedEnveloping ℒ d hneg}, x ∈ (𝓕 hneg).completionIdeal k →
      completedCoproduct ℒ d hneg x ∈ ((𝓕 hneg).tensorProduct R (𝓕 hneg)).completionIdeal k
  | 0, _, _ => by simp
  | k + 1, _, hx => (𝓕 hneg).mapCompletionₐ_mem_completionIdeal _ _ id monotone_id _ k hx

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

/-- The completed counit on the completed tensor square of `U(L)`, factored through the
order-zero projection. -/
noncomputable def completedTensorCounit (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    ((𝓕 hneg).tensorProduct R (𝓕 hneg)).completion →ₐ[R] R :=
  (Ideal.Quotient.liftₐ (((𝓕 hneg).tensorProduct R (𝓕 hneg)).ideal 1)
    (Bialgebra.counitAlgHom R (U ⊗[R] U))
    (fun _ ht => RingHom.mem_ker.mp
      (tensorProduct_degreeFiltration_one_le_ker_counitAlgHom ℒ d hneg ht))).comp
    (((𝓕 hneg).tensorProduct R (𝓕 hneg)).projectionₐ 0)

/-- The completed tensor counit agrees with `Coalgebra.counit` on any order-zero
representative. -/
theorem completedTensorCounit_of_representative (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    (z : ((𝓕 hneg).tensorProduct R (𝓕 hneg)).completion) (t : U ⊗[R] U)
    (ht : Ideal.Quotient.mk (((𝓕 hneg).tensorProduct R (𝓕 hneg)).ideal 1) t =
      ((𝓕 hneg).tensorProduct R (𝓕 hneg)).projection 0 z) :
    completedTensorCounit ℒ d hneg z = Coalgebra.counit (R := R) t := by
  rw [completedTensorCounit, AlgHom.comp_apply, AlgFiltration.projectionₐ_apply, ← ht,
    ← Ideal.Quotient.mkₐ_eq_mk R, ← AlgHom.comp_apply, Ideal.Quotient.liftₐ_comp,
    Bialgebra.counitAlgHom_apply]

/-- The completed tensor counit is multiplicative on completed pure tensors. -/
theorem completedTensorCounit_completedTensor (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    (x y : completedEnveloping ℒ d hneg) :
    completedTensorCounit ℒ d hneg ((𝓕 hneg).completedTensor R (𝓕 hneg) x y) =
      completedCounit ℒ d hneg x * completedCounit ℒ d hneg y := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((𝓕 hneg).projection 0 x)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective ((𝓕 hneg).projection 0 y)
  rw [completedTensorCounit_of_representative ℒ d hneg _ _
      ((𝓕 hneg).projection_completedTensor_of_representatives R (𝓕 hneg) 0 x y a b ha hb).symm,
    TensorProduct.counit_tmul, smul_eq_mul, mul_comm,
    completedCounit_of_representative ℒ d hneg x a ha,
    completedCounit_of_representative ℒ d hneg y b hb]

/-- The completed counit is left-invariant under the completed coproduct. -/
@[simp]
theorem completedTensorCounit_completedCoproduct (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    (x : completedEnveloping ℒ d hneg) :
    completedTensorCounit ℒ d hneg (completedCoproduct ℒ d hneg x) =
      completedCounit ℒ d hneg x := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((𝓕 hneg).projection 0 x)
  rw [completedTensorCounit_of_representative ℒ d hneg _ _ (by
    rw [projection_completedCoproduct, ← ha, Ideal.quotient_map_mkₐ,
      Ideal.Quotient.mkₐ_eq_mk, Bialgebra.comulAlgHom_apply])]
  exact (CoalgHomClass.counit_comp_apply (Coalgebra.comulCoalgHom R U) a).trans
    (completedCounit_of_representative ℒ d hneg x a ha).symm

/-- Elements of the first completion ideal have completed counit zero. -/
theorem completedCounit_eq_zero_of_mem_completionIdeal_one (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {x : completedEnveloping ℒ d hneg} (hx : x ∈ (𝓕 hneg).completionIdeal 1) :
    completedCounit ℒ d hneg x = 0 := by
  rw [AlgFiltration.completionIdeal_succ, RingHom.mem_ker] at hx
  rw [completedCounit, AlgHom.comp_apply, AlgFiltration.projectionₐ_apply, hx, map_zero]

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
    IsCompletedPrimitive ℒ d hneg x ↔ completedCoproduct ℒ d hneg x =
      (𝓕 hneg).completedTensor R (𝓕 hneg) x 1 + (𝓕 hneg).completedTensor R (𝓕 hneg) 1 x :=
  Iff.rfl

/-- `IsCompletedPrimitive` in terms of the two completed tensor inclusions. -/
theorem isCompletedPrimitive_iff_includeLeftCompletion_add_includeRightCompletion
    (hneg : ∀ n, d n < 0 → ℒ n = ⊥) {x : completedEnveloping ℒ d hneg} :
    IsCompletedPrimitive ℒ d hneg x ↔ completedCoproduct ℒ d hneg x =
      (𝓕 hneg).includeLeftCompletion R (𝓕 hneg) x +
        (𝓕 hneg).includeRightCompletion R (𝓕 hneg) x := by simp [IsCompletedPrimitive]

variable {ℒ d} in
/-- Every completed primitive element has completed counit zero. -/
theorem IsCompletedPrimitive.completedCounit_eq_zero {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {x : completedEnveloping ℒ d hneg} (hx : IsCompletedPrimitive ℒ d hneg x) :
    completedCounit ℒ d hneg x = 0 := by
  have hε := congrArg (completedTensorCounit ℒ d hneg) hx
  rw [completedTensorCounit_completedCoproduct, map_add,
    completedTensorCounit_completedTensor, completedTensorCounit_completedTensor] at hε
  simp only [map_one, mul_one, one_mul] at hε
  exact left_eq_add.mp hε

variable {ℒ d} in
/-- Any order-`k` representative of a completed primitive element has primitive defect in the
`(k + 1)`-st tensor-filtration ideal. -/
theorem IsCompletedPrimitive.comul_sub_mem_tensorProduct_ideal
    {hneg : ∀ n, d n < 0 → ℒ n = ⊥} {x : completedEnveloping ℒ d hneg}
    (hx : IsCompletedPrimitive ℒ d hneg x) {k : ℕ} {a : U}
    (ha : Ideal.Quotient.mk ((𝓕 hneg).ideal (k + 1)) a = (𝓕 hneg).projection k x) :
    Coalgebra.comul (R := R) a - (1 ⊗ₜ[R] a + a ⊗ₜ[R] 1) ∈
      ((𝓕 hneg).tensorProduct R (𝓕 hneg)).ideal (k + 1) := by
  have hproj := congrArg (((𝓕 hneg).tensorProduct R (𝓕 hneg)).projection k) hx
  rwa [map_add, projection_completedCoproduct, ← ha, Ideal.quotient_map_mkₐ,
    Ideal.Quotient.mkₐ_eq_mk, Bialgebra.comulAlgHom_apply,
    (𝓕 hneg).projection_completedTensor_of_representatives R (𝓕 hneg) k x 1 a 1 ha
      (map_one _).symm,
    (𝓕 hneg).projection_completedTensor_of_representatives R (𝓕 hneg) k 1 x 1 a
      (map_one _).symm ha,
    add_comm (Ideal.Quotient.mk _ (a ⊗ₜ[R] 1)), ← map_add, Ideal.Quotient.eq] at hproj

variable {ℒ d} in
/-- For a strictly positive Lie grading, every completed primitive element lies in the first
completion ideal. -/
theorem IsCompletedPrimitive.mem_completionIdeal_one {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {x : completedEnveloping ℒ d hneg} (hx : IsCompletedPrimitive ℒ d hneg x)
    (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) : x ∈ (𝓕 hneg).completionIdeal 1 :=
  (completedCounit_eq_zero_iff ℒ d hpos).mp hx.completedCounit_eq_zero

/-- Zero is completed primitive. -/
@[simp] theorem IsCompletedPrimitive.zero (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    IsCompletedPrimitive ℒ d hneg 0 := by
  simp [isCompletedPrimitive_iff_includeLeftCompletion_add_includeRightCompletion]

variable {ℒ d} in
/-- Completed primitive elements are closed under addition. -/
theorem IsCompletedPrimitive.add {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {x y : completedEnveloping ℒ d hneg}
    (hx : IsCompletedPrimitive ℒ d hneg x) (hy : IsCompletedPrimitive ℒ d hneg y) :
    IsCompletedPrimitive ℒ d hneg (x + y) := by
  simp only [isCompletedPrimitive_iff_includeLeftCompletion_add_includeRightCompletion,
    map_add] at hx hy ⊢
  rw [hx, hy]; abel

variable {ℒ d} in
/-- Completed primitive elements are closed under negation. -/
theorem IsCompletedPrimitive.neg {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {x : completedEnveloping ℒ d hneg} (hx : IsCompletedPrimitive ℒ d hneg x) :
    IsCompletedPrimitive ℒ d hneg (-x) := by
  simp only [isCompletedPrimitive_iff_includeLeftCompletion_add_includeRightCompletion,
    map_neg] at hx ⊢
  rw [hx, neg_add]

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
  simp only [isCompletedPrimitive_iff_includeLeftCompletion_add_includeRightCompletion,
    map_smul] at hx ⊢
  rw [hx, smul_add]

variable {ℒ d} in
/-- Completed primitive elements are closed under the associative commutator bracket. -/
theorem IsCompletedPrimitive.lie {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {x y : completedEnveloping ℒ d hneg}
    (hx : IsCompletedPrimitive ℒ d hneg x) (hy : IsCompletedPrimitive ℒ d hneg y) :
    IsCompletedPrimitive ℒ d hneg ⁅x, y⁆ := by
  rw [isCompletedPrimitive_iff_includeLeftCompletion_add_includeRightCompletion] at hx hy ⊢
  have hxy := ((𝓕 hneg).commute_includeLeftCompletion_includeRightCompletion R (𝓕 hneg) x y).eq
  have hyx := ((𝓕 hneg).commute_includeLeftCompletion_includeRightCompletion R (𝓕 hneg) y x).eq
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
    x ∈ completedPrimitiveLieSubalgebra ℒ d hneg ↔ IsCompletedPrimitive ℒ d hneg x := Iff.rfl

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
@[simp] theorem IsCompletedGroupLike.one (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
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
      hv.completedCoproduct_eq_completedTensor_self, ← (𝓕 hneg).completedTensor_mul R (𝓕 hneg)]

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
      rw [hu.completedCoproduct_eq_completedTensor_self, ← (𝓕 hneg).completedTensor_mul R (𝓕 hneg),
        huv]; simp [AlgFiltration.completedTensor_apply])

/-- Ordinary grouplike elements of `U(L)` become completed grouplike in `completedEnveloping`. -/
theorem isCompletedGroupLike_toCompletion_of_isGroupLikeElem (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {g : U} (hg : _root_.IsGroupLikeElem R g) :
    IsCompletedGroupLike ℒ d hneg ((𝓕 hneg).toCompletion g) where
  completedCounit_eq_one := by simp [hg.counit_eq_one]
  completedCoproduct_eq_completedTensor_self := by
    rw [completedCoproduct_toCompletion, hg.comul_eq_tmul_self,
      ← (𝓕 hneg).completedTensor_toCompletion R (𝓕 hneg)]

variable {ℒ d} in
/-- For a strictly positive Lie grading, every completed grouplike element is congruent to `1`
modulo the first completion ideal. -/
theorem IsCompletedGroupLike.sub_one_mem_completionIdeal_one {hneg : ∀ n, d n < 0 → ℒ n = ⊥}
    {u : completedEnveloping ℒ d hneg} (hu : IsCompletedGroupLike ℒ d hneg u)
    (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) : u - 1 ∈ (𝓕 hneg).completionIdeal 1 :=
  (completedCounit_eq_one_iff ℒ d hpos).mp hu.completedCounit_eq_one

end TauCeti.UniversalEnvelopingAlgebra
