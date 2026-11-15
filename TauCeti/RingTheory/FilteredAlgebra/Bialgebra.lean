/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.GroupLike
public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Bialgebra.Primitive
public import TauCeti.RingTheory.FilteredAlgebra.Exp.Basic
public import TauCeti.RingTheory.FilteredAlgebra.TensorProduct.Map

/-!
# Completed coproducts, group-like elements, and primitives in filtered bialgebras

When an ideal filtration `F` on an `R`-bialgebra `A` carries each filtration term into the
corresponding total-degree tensor filtration term under comultiplication and kills the first
filtration ideal under the counit (`AlgFiltration.IsBialgFiltration`), the comultiplication and
counit extend to `R`-algebra homomorphisms `AlgFiltration.completedCoproduct` and
`AlgFiltration.completedCounit` on `F.completion`.

Although the finite-order quotients `A ⧸ F.ideal (k + 1)` need not be coalgebras (for instance,
for degree filtrations on enveloping algebras, `F.ideal (k + 1)` is not a coideal for `k ≥ 1`),
group-like and primitive elements are defined directly in the completion by
`ε̂(x) = 1`, `Δ̂(x) = x ⊗̂ x` (`AlgFiltration.IsCompletedGroupLike`) and
`Δ̂(x) = x ⊗̂ 1 + 1 ⊗̂ x` (`AlgFiltration.IsCompletedPrimitive`). Every completed primitive
automatically has completed counit zero, and when `ker ε ≤ F.ideal 1` both predicates place `x`
(respectively `x - 1`) in `F.completionIdeal 1`.

When `A` is also a rational algebra, `AlgFiltration.completedExp` and `AlgFiltration.completedLog`
restrict to inverse bijections between the completed primitive elements of `F.completionIdeal 1`
and the completed group-like elements congruent to `1` modulo `F.completionIdeal 1` (and all
completed group-like elements when `ker ε ≤ F.ideal 1`).

## Main definitions

* `TauCeti.AlgFiltration.IsBialgFiltration`: compatibility of an algebra filtration with the
  comultiplication and counit of a bialgebra.
* `TauCeti.AlgFiltration.completedCoproduct` and `TauCeti.AlgFiltration.completedCounit`: the
  induced algebra homomorphisms on `F.completion`.
* `TauCeti.AlgFiltration.IsCompletedGroupLike` and `TauCeti.AlgFiltration.IsCompletedPrimitive`:
  group-like and primitive predicates in `F.completion`.
* `TauCeti.AlgFiltration.completedGroupLikeSubgroup`: the subgroup of `F.completionˣ` consisting of
  invertible completed group-like elements.
* `TauCeti.AlgFiltration.completedPrimitiveSubmodule`: the `R`-submodule of completed primitive
  elements.
* `TauCeti.AlgFiltration.completedExpPrimitiveEquiv` and
  `TauCeti.AlgFiltration.completedExpGroupLikeEquiv`: the exponential-logarithm bijections between
  completed primitives and completed group-like elements.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 1–3, Ch. II, §6 (completed bialgebras,
  primitive and group-like elements, and their correspondence under `exp` and `log`).
-/

public section

open scoped TensorProduct

namespace TauCeti.AlgFiltration

/-- An algebra filtration on an `R`-bialgebra is a *bialgebra filtration* when comultiplication
preserves filtration order against the total-degree tensor filtration and the counit vanishes on
the first filtration ideal. -/
class IsBialgFiltration (R : Type*) {A : Type*} [CommSemiring R] [Semiring A]
    [Bialgebra R A] (F : AlgFiltration A) : Prop where
  /-- Comultiplication carries filtration order `k` into total tensor filtration order `k`. -/
  ideal_le_comap_comul (k : ℕ) :
    F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A)
  /-- The counit vanishes on the first filtration ideal. -/
  ideal_one_le_ker_counit :
    F.ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R A)

section Completion

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Bialgebra R A]
  (F : AlgFiltration A) [F.IsBialgFiltration R]

/-- The completed coproduct `Δ̂ : F.completion →ₐ[R] (F.tensorProduct R F).completion` induced by
`Bialgebra.comulAlgHom`. -/
noncomputable def completedCoproduct :
    F.completion →ₐ[R] (F.tensorProduct R F).completion :=
  F.mapCompletionₐ (F.tensorProduct R F) (Bialgebra.comulAlgHom R A) id monotone_id
    fun k => IsBialgFiltration.ideal_le_comap_comul (R := R) (F := F) (k + 1)

/-- At order `k`, the completed coproduct is induced on `A ⧸ F.ideal (k + 1)` by
`Bialgebra.comulAlgHom`. -/
@[simp]
theorem projection_completedCoproduct (k : ℕ) (x : F.completion) :
    (F.tensorProduct R F).projection k (F.completedCoproduct R x) =
      Ideal.quotientMapₐ ((F.tensorProduct R F).ideal (k + 1)) (Bialgebra.comulAlgHom R A)
        (IsBialgFiltration.ideal_le_comap_comul (R := R) (F := F) (k + 1)) (F.projection k x) :=
  F.projection_mapCompletionₐ _ _ _ monotone_id _ k x

/-- On canonical images of elements of `A`, the completed coproduct agrees with `Coalgebra.comul`.
-/
@[simp]
theorem completedCoproduct_toCompletion (a : A) :
    F.completedCoproduct R (F.toCompletion a) =
      (F.tensorProduct R F).toCompletion (Coalgebra.comul (R := R) a) :=
  F.mapCompletionₐ_toCompletion _ _ _ monotone_id _ a

/-- The completed coproduct preserves every filtration order. -/
theorem completedCoproduct_mem_completionIdeal {k : ℕ} {x : F.completion}
    (hx : x ∈ F.completionIdeal k) :
    F.completedCoproduct R x ∈ (F.tensorProduct R F).completionIdeal k := by
  cases k with
  | zero => simp
  | succ k => exact F.mapCompletionₐ_mem_completionIdeal _ _ id monotone_id _ k hx

/-- When `A` is cocommutative, the completed coproduct is invariant under completed factor
exchange. -/
theorem completedTensorComm_completedCoproduct [Coalgebra.IsCocomm R A] (x : F.completion) :
    F.completedTensorComm R F (F.completedCoproduct R x) = F.completedCoproduct R x := by
  apply (F.tensorProduct R F).completion_ext
  intro k
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection k x)
  rw [projection_completedTensorComm, projection_completedCoproduct, ← ha]
  simp only [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.coe_toAlgHom,
    Bialgebra.comulAlgHom_apply]
  congr 1
  rw [← AlgEquiv.toLinearEquiv_apply, Algebra.TensorProduct.comm_toLinearEquiv]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using
    LinearMap.congr_fun (Coalgebra.comm_comp_comul R A) a

/-- The completed counit `ε̂ : F.completion →ₐ[R] R` induced through the order-zero quotient
`A ⧸ F.ideal 1`. -/
noncomputable def completedCounit : F.completion →ₐ[R] R :=
  (Ideal.Quotient.liftₐ (F.ideal 1) (Bialgebra.counitAlgHom R A)
    fun _ ha => RingHom.mem_ker.mp (IsBialgFiltration.ideal_one_le_ker_counit ha)).comp
    (F.projectionₐ (R := R) 0)

/-- Any representative of the order-zero projection computes the completed counit. -/
theorem completedCounit_of_representative (x : F.completion) (a : A)
    (ha : Ideal.Quotient.mk (F.ideal 1) a = F.projection 0 x) :
    F.completedCounit R x = Coalgebra.counit (R := R) a := by
  simp only [completedCounit, AlgHom.comp_apply, projectionₐ_apply, ← ha]
  rfl

/-- On canonical images of elements of `A`, the completed counit agrees with `Coalgebra.counit`. -/
@[simp]
theorem completedCounit_toCompletion (a : A) :
    F.completedCounit R (F.toCompletion a) = Coalgebra.counit (R := R) a :=
  F.completedCounit_of_representative R (F.toCompletion a) a (F.projection_toCompletion 0 a).symm

/-- The completed counit vanishes on `F.completionIdeal 1`. -/
theorem completedCounit_eq_zero_of_mem {x : F.completion} (hx : x ∈ F.completionIdeal 1) :
    F.completedCounit R x = 0 := by
  have hx0 : F.projection 0 x = 0 := by
    simpa only [completionIdeal_succ, RingHom.mem_ker] using hx
  simp [completedCounit, hx0]

/-- Elements congruent to `1` modulo `F.completionIdeal 1` have completed counit `1`. -/
theorem completedCounit_eq_one_of_sub_one_mem {u : F.completion}
    (hu : u - 1 ∈ F.completionIdeal 1) :
    F.completedCounit R u = 1 := by
  have hsub := F.completedCounit_eq_zero_of_mem R hu
  rwa [map_sub, map_one, sub_eq_zero] at hsub

/-- When `ker ε ≤ F.ideal 1`, the first completion ideal is precisely the kernel of the completed
counit. -/
theorem mem_completionIdeal_one_iff_completedCounit_eq_zero
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) (x : F.completion) :
    x ∈ F.completionIdeal 1 ↔ F.completedCounit R x = 0 := by
  refine ⟨F.completedCounit_eq_zero_of_mem R, fun hx => ?_⟩
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection 0 x)
  have ha0 : a ∈ F.ideal 1 := hker <| RingHom.mem_ker.mpr <| by
    rw [Bialgebra.counitAlgHom_apply, ← F.completedCounit_of_representative R x a ha, hx]
  rw [completionIdeal_succ, RingHom.mem_ker, ← ha]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha0

/-- When `ker ε ≤ F.ideal 1`, an element is congruent to `1` modulo `F.completionIdeal 1` precisely
when its completed counit is `1`. -/
theorem sub_one_mem_completionIdeal_one_iff_completedCounit_eq_one
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) (u : F.completion) :
    u - 1 ∈ F.completionIdeal 1 ↔ F.completedCounit R u = 1 := by
  rw [F.mem_completionIdeal_one_iff_completedCounit_eq_zero R hker (u - 1), map_sub, map_one,
    sub_eq_zero]

/-- An element `x` of `F.completion` is *completed group-like* when `ε̂(x) = 1` and
`Δ̂(x) = x ⊗̂ x`. -/
structure IsCompletedGroupLike (x : F.completion) : Prop where
  /-- A completed group-like element has completed counit `1`. -/
  completedCounit_eq_one : F.completedCounit R x = 1
  /-- A completed group-like element has completed coproduct `x ⊗̂ x`. -/
  completedCoproduct_eq_completedTensor_self :
    F.completedCoproduct R x = F.completedTensor R F x x

/-- Unfolded characterization of completed group-like elements. -/
theorem isCompletedGroupLike_iff {x : F.completion} :
    F.IsCompletedGroupLike R x ↔
      F.completedCounit R x = 1 ∧ F.completedCoproduct R x = F.completedTensor R F x x :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- An element `x` of `F.completion` is *completed primitive* when `Δ̂(x) = x ⊗̂ 1 + 1 ⊗̂ x`. -/
def IsCompletedPrimitive (x : F.completion) : Prop :=
  F.completedCoproduct R x = F.completedTensor R F x 1 + F.completedTensor R F 1 x

/-- Completed primitivity in terms of the left and right completed tensor inclusions. -/
theorem isCompletedPrimitive_iff_includeCompletion {x : F.completion} :
    F.IsCompletedPrimitive R x ↔
      F.completedCoproduct R x =
        F.includeLeftCompletion R F x + F.includeRightCompletion R F x := by
  simp [IsCompletedPrimitive]

section GroupLike

variable {R F}

/-- The identity element `1` is completed group-like. -/
@[simp]
theorem IsCompletedGroupLike.one : F.IsCompletedGroupLike R 1 where
  completedCounit_eq_one := map_one _
  completedCoproduct_eq_completedTensor_self := by simp

/-- Completed group-like elements are closed under multiplication. -/
theorem IsCompletedGroupLike.mul {x y : F.completion}
    (hx : F.IsCompletedGroupLike R x) (hy : F.IsCompletedGroupLike R y) :
    F.IsCompletedGroupLike R (x * y) where
  completedCounit_eq_one := by simp [map_mul, hx.completedCounit_eq_one, hy.completedCounit_eq_one]
  completedCoproduct_eq_completedTensor_self := by
    rw [map_mul, hx.completedCoproduct_eq_completedTensor_self,
      hy.completedCoproduct_eq_completedTensor_self, F.completedTensor_mul R F]

/-- Completed group-like elements are closed under natural powers. -/
theorem IsCompletedGroupLike.pow {x : F.completion} (hx : F.IsCompletedGroupLike R x) (n : ℕ) :
    F.IsCompletedGroupLike R (x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using IsCompletedGroupLike.one
  | succ n ih => simpa only [pow_succ] using ih.mul hx

/-- Completed group-like elements are closed under two-sided multiplicative inverses. -/
theorem IsCompletedGroupLike.of_mul_eq_one {x y : F.completion}
    (hxy : x * y = 1) (hyx : y * x = 1) (hx : F.IsCompletedGroupLike R x) :
    F.IsCompletedGroupLike R y where
  completedCounit_eq_one :=
    left_inv_eq_right_inv (a := F.completedCounit R x)
      (by rw [← map_mul, hyx, map_one])
      (by rw [hx.completedCounit_eq_one, one_mul])
  completedCoproduct_eq_completedTensor_self :=
    left_inv_eq_right_inv (a := F.completedCoproduct R x)
      (by rw [← map_mul, hyx, map_one])
      (by rw [hx.completedCoproduct_eq_completedTensor_self, ← F.completedTensor_mul R F, hxy,
        F.completedTensor_one_left R F, map_one])

/-- Multiplicative inversion on `F.completionˣ` preserves completed group-likeness. -/
@[simp]
theorem isCompletedGroupLike_unitsInv {u : F.completionˣ} :
    F.IsCompletedGroupLike R (↑u⁻¹ : F.completion) ↔
      F.IsCompletedGroupLike R (u : F.completion) :=
  ⟨IsCompletedGroupLike.of_mul_eq_one u.inv_mul u.mul_inv,
    IsCompletedGroupLike.of_mul_eq_one u.mul_inv u.inv_mul⟩

/-- Canonical images of group-like elements of `A` are completed group-like. -/
theorem isCompletedGroupLike_toCompletion {a : A} (ha : IsGroupLikeElem R a) :
    F.IsCompletedGroupLike R (F.toCompletion a) where
  completedCounit_eq_one := by simp [ha.counit_eq_one]
  completedCoproduct_eq_completedTensor_self := by
    rw [completedCoproduct_toCompletion, ha.comul_eq_tmul_self, completedTensor_toCompletion]

/-- When `ker ε ≤ F.ideal 1`, every completed group-like element is congruent to `1` modulo
`F.completionIdeal 1`. -/
theorem IsCompletedGroupLike.sub_one_mem {u : F.completion} (hu : F.IsCompletedGroupLike R u)
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) :
    u - 1 ∈ F.completionIdeal 1 :=
  (F.sub_one_mem_completionIdeal_one_iff_completedCounit_eq_one R hker u).mpr
    hu.completedCounit_eq_one

end GroupLike

/-- The submonoid of completed group-like elements of `F.completion`. -/
def completedGroupLikeSubmonoid : Submonoid F.completion where
  carrier := {x | F.IsCompletedGroupLike R x}
  one_mem' := IsCompletedGroupLike.one
  mul_mem' hx hy := hx.mul hy

/-- Membership in `F.completedGroupLikeSubmonoid R` unfolds to `F.IsCompletedGroupLike R`. -/
@[simp]
theorem mem_completedGroupLikeSubmonoid_iff {x : F.completion} :
    x ∈ F.completedGroupLikeSubmonoid R ↔ F.IsCompletedGroupLike R x :=
  Iff.rfl

/-- The subgroup of `F.completionˣ` consisting of units that are completed group-like. -/
def completedGroupLikeSubgroup : Subgroup F.completionˣ where
  carrier := {u | F.IsCompletedGroupLike R (u : F.completion)}
  one_mem' := IsCompletedGroupLike.one
  mul_mem' hx hy := hx.mul hy
  inv_mem' hx := isCompletedGroupLike_unitsInv.mpr hx

/-- Membership in `F.completedGroupLikeSubgroup R` unfolds to completed group-likeness of the
underlying element of `F.completion`. -/
@[simp]
theorem mem_completedGroupLikeSubgroup_iff {u : F.completionˣ} :
    u ∈ F.completedGroupLikeSubgroup R ↔ F.IsCompletedGroupLike R (u : F.completion) :=
  Iff.rfl

section Primitive

variable {R F}

/-- Every completed primitive element has completed counit zero. -/
theorem IsCompletedPrimitive.completedCounit_eq_zero {x : F.completion}
    (hx : F.IsCompletedPrimitive R x) :
    F.completedCounit R x = 0 := by
  let ε₂ : A ⊗[R] A →ₐ[R] R :=
    Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R A) (Bialgebra.counitAlgHom R A)
      fun _ _ => Commute.all _ _
  have hker₂ : (F.tensorProduct R F).ideal 1 ≤ RingHom.ker ε₂ := by
    intro t ht
    rw [RingHom.mem_ker]
    have hsub : tensorFiltrationTail (fun n => (F.ideal n).restrictScalars R)
        (fun n => (F.ideal n).restrictScalars R) 1 ≤ LinearMap.ker ε₂.toLinearMap := by
      refine (tensorFiltrationTail_le_iff _ _).mpr fun a b hab u hu v hv => ?_
      rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply]
      dsimp [ε₂]
      by_cases ha : 1 ≤ a
      · have hu0 : Bialgebra.counitAlgHom R A u = 0 :=
          RingHom.mem_ker.mp (IsBialgFiltration.ideal_one_le_ker_counit (F.antitone ha hu))
        simp [hu0]
      · have hb : 1 ≤ b := by omega
        have hv0 : Bialgebra.counitAlgHom R A v = 0 :=
          RingHom.mem_ker.mp (IsBialgFiltration.ideal_one_le_ker_counit (F.antitone hb hv))
        simp [hv0]
    exact hsub ((F.mem_tensorProduct_ideal_iff R F).mp ht)
  let E : (F.tensorProduct R F).completion →ₐ[R] R :=
    (Ideal.Quotient.liftₐ ((F.tensorProduct R F).ideal 1) ε₂
      fun _ ht => RingHom.mem_ker.mp (hker₂ ht)).comp
      ((F.tensorProduct R F).projectionₐ (R := R) 0)
  have hε₂_comul (a : A) : ε₂ (Coalgebra.comul (R := R) a) = Coalgebra.counit (R := R) a := by
    have hlin : ε₂.toLinearMap =
        (Coalgebra.counit (R := R)).comp
          ((TensorProduct.lid R A).toLinearMap.comp (Coalgebra.counit.rTensor A)) := by
      apply TensorProduct.ext'
      intro u v
      simp [ε₂]
    simpa only [AlgHom.toLinearMap_apply, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul,
      LinearEquiv.coe_coe, TensorProduct.lid_tmul, one_smul] using
      LinearMap.congr_fun hlin (Coalgebra.comul (R := R) a)
  have hE_mk (t : A ⊗[R] A) (z : (F.tensorProduct R F).completion)
      (hz : (F.tensorProduct R F).projection 0 z =
        Ideal.Quotient.mk ((F.tensorProduct R F).ideal 1) t) :
      E z = ε₂ t := by
    simp only [E, AlgHom.comp_apply, projectionₐ_apply, hz]
    rfl
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection 0 x)
  have hE_coprod : E (F.completedCoproduct R x) = F.completedCounit R x := by
    rw [F.completedCounit_of_representative R x a ha, ← hε₂_comul a]
    exact hE_mk _ _ (by simp [projection_completedCoproduct, ← ha])
  have hone : Ideal.Quotient.mk (F.ideal (0 + 1)) 1 = F.projection 0 1 :=
    (map_one _).trans (map_one _).symm
  have hE_left : E (F.completedTensor R F x 1) = F.completedCounit R x := by
    rw [F.completedCounit_of_representative R x a ha,
      hE_mk _ _ (F.projection_completedTensor_of_representatives R F 0 x 1 a 1 ha hone)]
    simp [ε₂]
  have hE_right : E (F.completedTensor R F 1 x) = F.completedCounit R x := by
    rw [F.completedCounit_of_representative R x a ha,
      hE_mk _ _ (F.projection_completedTensor_of_representatives R F 0 1 x 1 a hone ha)]
    simp [ε₂]
  have hsum := congrArg E hx
  rw [map_add, hE_coprod, hE_left, hE_right] at hsum
  simpa using congrArg (· - F.completedCounit R x) hsum.symm

/-- When `ker ε ≤ F.ideal 1`, every completed primitive element belongs to `F.completionIdeal 1`.
-/
theorem IsCompletedPrimitive.mem_completionIdeal_one {x : F.completion}
    (hx : F.IsCompletedPrimitive R x)
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) :
    x ∈ F.completionIdeal 1 :=
  (F.mem_completionIdeal_one_iff_completedCounit_eq_zero R hker x).mpr hx.completedCounit_eq_zero

/-- Zero is completed primitive. -/
@[simp]
theorem IsCompletedPrimitive.zero : F.IsCompletedPrimitive R 0 := by
  simp [isCompletedPrimitive_iff_includeCompletion]

/-- Completed primitive elements are closed under addition. -/
theorem IsCompletedPrimitive.add {x y : F.completion}
    (hx : F.IsCompletedPrimitive R x) (hy : F.IsCompletedPrimitive R y) :
    F.IsCompletedPrimitive R (x + y) := by
  rw [isCompletedPrimitive_iff_includeCompletion] at hx hy ⊢
  rw [map_add, hx, hy, map_add, map_add]
  abel

/-- Completed primitive elements are closed under negation. -/
theorem IsCompletedPrimitive.neg {x : F.completion} (hx : F.IsCompletedPrimitive R x) :
    F.IsCompletedPrimitive R (-x) := by
  rw [isCompletedPrimitive_iff_includeCompletion] at hx ⊢
  rw [map_neg, hx, map_neg, map_neg]
  abel

/-- Completed primitive elements are closed under subtraction. -/
theorem IsCompletedPrimitive.sub {x y : F.completion}
    (hx : F.IsCompletedPrimitive R x) (hy : F.IsCompletedPrimitive R y) :
    F.IsCompletedPrimitive R (x - y) := by
  simpa only [sub_eq_add_neg] using hx.add hy.neg

/-- Completed primitive elements are closed under scalar multiplication. -/
theorem IsCompletedPrimitive.smul (r : R) {x : F.completion} (hx : F.IsCompletedPrimitive R x) :
    F.IsCompletedPrimitive R (r • x) := by
  rw [isCompletedPrimitive_iff_includeCompletion] at hx ⊢
  simp [hx, smul_add]

/-- Completed primitive elements are closed under associative commutators `x * y - y * x`. -/
theorem IsCompletedPrimitive.commutator {x y : F.completion}
    (hx : F.IsCompletedPrimitive R x) (hy : F.IsCompletedPrimitive R y) :
    F.IsCompletedPrimitive R (x * y - y * x) := by
  rw [isCompletedPrimitive_iff_includeCompletion] at hx hy ⊢
  have hxy := (F.commute_includeLeftCompletion_includeRightCompletion R F y x).eq
  have hyx := (F.commute_includeLeftCompletion_includeRightCompletion R F x y).eq
  rw [map_sub, map_mul, map_mul, hx, hy, map_sub, map_sub, map_mul, map_mul, map_mul, map_mul,
    add_mul, mul_add, mul_add, add_mul, mul_add, mul_add]
  rw [hyx, hxy]
  abel

/-- Canonical images of primitive elements of `A` are completed primitive. -/
theorem isCompletedPrimitive_toCompletion {a : A} (ha : Bialgebra.IsPrimitiveElem R a) :
    F.IsCompletedPrimitive R (F.toCompletion a) := by
  rw [isCompletedPrimitive_iff_includeCompletion, completedCoproduct_toCompletion,
    ha.comul_eq_tmul_add_tmul, map_add, includeLeftCompletion_toCompletion,
    includeRightCompletion_toCompletion, add_comm]

/-- A filtered bialgebra homomorphism carries completed primitive elements to completed primitive
elements along any monotone cutoff modulus. -/
theorem IsCompletedPrimitive.map {B : Type*} [Ring B] [Bialgebra R B]
    (G : AlgFiltration B) [G.IsBialgFiltration R]
    (f : A →ₐc[R] B) (l : ℕ → ℕ) (hl : Monotone l)
    (hf : ∀ k, F.ideal (l k + 1) ≤ (G.ideal (k + 1)).comap (f : A →ₐ[R] B))
    {x : F.completion} (hx : F.IsCompletedPrimitive R x) :
    G.IsCompletedPrimitive R (F.mapCompletionₐ G (f : A →ₐ[R] B) l hl hf x) := by
  let fₐ : A →ₐ[R] B := f
  have hfₐ : fₐ = AlgHom.ofClass f := AlgHom.ext fun _ => rfl
  let Tf := (F.tensorProduct R F).mapCompletionₐ (G.tensorProduct R G)
    (Algebra.TensorProduct.map fₐ fₐ) (fun k => l k + l k) (hl.add hl)
    (F.tensorProduct_ideal_le_comap_map_of_moduli R F G G fₐ fₐ l l hf hf)
  have hsq : (Algebra.TensorProduct.map fₐ fₐ).comp (Bialgebra.comulAlgHom R A) =
      (Bialgebra.comulAlgHom R B).comp fₐ := by
    rw [hfₐ]
    exact BialgHomClass.map_comp_comulAlgHom f
  have hcomp : Tf.comp (F.completedCoproduct R) =
      (G.completedCoproduct R).comp (F.mapCompletionₐ G fₐ l hl hf) := by
    dsimp only [Tf, completedCoproduct]
    rw [← F.mapCompletionₐ_comp (F.tensorProduct R F) (Bialgebra.comulAlgHom R A) id monotone_id _
      (G.tensorProduct R G) (Algebra.TensorProduct.map fₐ fₐ) (fun k => l k + l k) (hl.add hl) _,
      ← F.mapCompletionₐ_comp G fₐ l hl hf (G.tensorProduct R G) (Bialgebra.comulAlgHom R B)
      id monotone_id _]
    refine AlgHom.toRingHom_injective ?_
    simpa only [coe_mapCompletionₐ, hsq] using
      F.mapCompletion_eq (G.tensorProduct R G)
        (((Bialgebra.comulAlgHom R B).comp fₐ : A →ₐ[R] B ⊗[R] B) : A →+* B ⊗[R] B)
        (monotone_id.comp (hl.add hl)) _ (l ∘ id) (hl.comp monotone_id) _
  have hTf := congrArg Tf hx
  rw [map_add,
    F.mapCompletionₐ_completedTensor_of_moduli R F G G fₐ fₐ l l hl hl hf hf x 1,
    F.mapCompletionₐ_completedTensor_of_moduli R F G G fₐ fₐ l l hl hl hf hf 1 x,
    map_one] at hTf
  exact (AlgHom.congr_fun hcomp.symm x).trans hTf

end Primitive

/-- The `R`-submodule of completed primitive elements of `F.completion`. -/
def completedPrimitiveSubmodule : Submodule R F.completion where
  carrier := {x | F.IsCompletedPrimitive R x}
  zero_mem' := IsCompletedPrimitive.zero
  add_mem' hx hy := hx.add hy
  smul_mem' r _ hx := hx.smul r

/-- Membership in `F.completedPrimitiveSubmodule R` unfolds to `F.IsCompletedPrimitive R`. -/
@[simp]
theorem mem_completedPrimitiveSubmodule_iff {x : F.completion} :
    x ∈ F.completedPrimitiveSubmodule R ↔ F.IsCompletedPrimitive R x :=
  Iff.rfl

section Exp

variable [Algebra ℚ A]

/-- In a rational filtered bialgebra, the completed exponential of `x ∈ F.completionIdeal 1` is
completed group-like if and only if `x` is completed primitive. -/
theorem isCompletedGroupLike_completedExp_iff (x : F.completionIdeal 1) :
    F.IsCompletedGroupLike R (F.completedExp x) ↔
      F.IsCompletedPrimitive R (x : F.completion) := by
  have : SMulCommClass R ℚ A :=
    ⟨fun r q a => by simp only [Algebra.smul_def, ← mul_assoc, Algebra.commutes r]⟩
  let TF := F.tensorProduct R F
  have hcounit : F.completedCounit R (F.completedExp x) = 1 :=
    F.completedCounit_eq_one_of_sub_one_mem R (F.completedExp_sub_one_mem x)
  have hcoprod : F.completedCoproduct R (F.completedExp x) =
      TF.completedExp ⟨F.completedCoproduct R x,
        F.completedCoproduct_mem_completionIdeal R x.property⟩ := by
    apply TF.completion_ext
    intro k
    rw [projection_completedCoproduct, projection_completedExp, projection_completedExp,
      projection_completedCoproduct]
    exact (F.isNilpotent_projection x.property k).map_exp _
  have hleft : F.includeLeftCompletion R F (F.completedExp x) =
      TF.completedExp ⟨F.includeLeftCompletion R F x,
        F.includeLeftCompletion_mem_completionIdeal R F x.property⟩ := by
    apply TF.completion_ext
    intro k
    rw [projection_includeLeftCompletion, projection_completedExp, projection_completedExp,
      projection_includeLeftCompletion]
    exact (F.isNilpotent_projection x.property k).map_exp _
  have hright : F.includeRightCompletion R F (F.completedExp x) =
      TF.completedExp ⟨F.includeRightCompletion R F x,
        F.includeRightCompletion_mem_completionIdeal R F x.property⟩ := by
    apply TF.completion_ext
    intro k
    rw [projection_includeRightCompletion, projection_completedExp, projection_completedExp,
      projection_includeRightCompletion]
    exact (F.isNilpotent_projection x.property k).map_exp _
  let xl : TF.completionIdeal 1 :=
    ⟨F.includeLeftCompletion R F x, F.includeLeftCompletion_mem_completionIdeal R F x.property⟩
  let xr : TF.completionIdeal 1 :=
    ⟨F.includeRightCompletion R F x, F.includeRightCompletion_mem_completionIdeal R F x.property⟩
  have hcomm : Commute (xl : TF.completion) xr :=
    F.commute_includeLeftCompletion_includeRightCompletion R F x x
  have htensor : F.completedTensor R F (F.completedExp x) (F.completedExp x) =
      TF.completedExp (xl + xr) := by
    rw [completedTensor_apply, hleft, hright, ← TF.completedExp_add xl xr hcomm]
  rw [isCompletedGroupLike_iff, and_iff_right hcounit, hcoprod, htensor,
    isCompletedPrimitive_iff_includeCompletion]
  constructor
  · intro h
    rw [← TF.coe_completedExpEquiv, ← TF.coe_completedExpEquiv] at h
    exact congrArg Subtype.val (TF.completedExpEquiv.injective (Subtype.ext h))
  · intro h
    congr 1
    exact Subtype.ext h

/-- In a rational filtered bialgebra, the completed logarithm of an element `u` congruent to `1`
modulo `F.completionIdeal 1` is completed primitive if and only if `u` is completed group-like. -/
theorem isCompletedPrimitive_completedLog_iff
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}) :
    F.IsCompletedPrimitive R (F.completedLog u) ↔
      F.IsCompletedGroupLike R (u : F.completion) := by
  simpa only [completedExp_completedLog] using
    (F.isCompletedGroupLike_completedExp_iff R ⟨F.completedLog u, F.completedLog_mem u⟩).symm

/-- Exponential coordinates identify the completed primitive elements of `F.completionIdeal 1`
with the completed group-like elements congruent to `1` modulo `F.completionIdeal 1`. -/
noncomputable def completedExpPrimitiveEquiv :
    {x : F.completionIdeal 1 // F.IsCompletedPrimitive R (x : F.completion)} ≃
      {u : F.completion // u - 1 ∈ F.completionIdeal 1 ∧ F.IsCompletedGroupLike R u} where
  toFun x := ⟨F.completedExp x.1, F.completedExp_sub_one_mem x.1,
    (F.isCompletedGroupLike_completedExp_iff R x.1).mpr x.2⟩
  invFun u := ⟨⟨F.completedLog ⟨u.1, u.2.1⟩, F.completedLog_mem ⟨u.1, u.2.1⟩⟩,
    (F.isCompletedPrimitive_completedLog_iff R ⟨u.1, u.2.1⟩).mpr u.2.2⟩
  left_inv x := Subtype.ext <| Subtype.ext <| F.completedLog_completedExp x.1
  right_inv u := Subtype.ext <| F.completedExp_completedLog ⟨u.1, u.2.1⟩

/-- The forward map of `F.completedExpPrimitiveEquiv R` is `F.completedExp`. -/
@[simp]
theorem coe_completedExpPrimitiveEquiv
    (x : {x : F.completionIdeal 1 // F.IsCompletedPrimitive R (x : F.completion)}) :
    (F.completedExpPrimitiveEquiv R x : F.completion) = F.completedExp x.1 := (rfl)

/-- The inverse map of `F.completedExpPrimitiveEquiv R` is `F.completedLog`. -/
@[simp]
theorem coe_completedExpPrimitiveEquiv_symm
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1 ∧ F.IsCompletedGroupLike R u}) :
    ((F.completedExpPrimitiveEquiv R).symm u : F.completion) =
      F.completedLog ⟨u.1, u.2.1⟩ := (rfl)

/-- When `ker ε ≤ F.ideal 1`, exponential coordinates identify all completed primitive elements
with all completed group-like elements. -/
noncomputable def completedExpGroupLikeEquiv
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) :
    {x : F.completion // F.IsCompletedPrimitive R x} ≃
      {u : F.completion // F.IsCompletedGroupLike R u} where
  toFun x :=
    let x₁ : F.completionIdeal 1 := ⟨x.1, x.2.mem_completionIdeal_one hker⟩
    ⟨F.completedExp x₁, (F.isCompletedGroupLike_completedExp_iff R x₁).mpr x.2⟩
  invFun u :=
    let u₁ : {v : F.completion // v - 1 ∈ F.completionIdeal 1} :=
      ⟨u.1, u.2.sub_one_mem hker⟩
    ⟨F.completedLog u₁, (F.isCompletedPrimitive_completedLog_iff R u₁).mpr u.2⟩
  left_inv x := Subtype.ext <|
    F.completedLog_completedExp ⟨x.1, x.2.mem_completionIdeal_one hker⟩
  right_inv u := Subtype.ext <|
    F.completedExp_completedLog ⟨u.1, u.2.sub_one_mem hker⟩

/-- The forward map of `F.completedExpGroupLikeEquiv R hker` is `F.completedExp`. -/
@[simp]
theorem coe_completedExpGroupLikeEquiv
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1)
    (x : {x : F.completion // F.IsCompletedPrimitive R x}) :
    (F.completedExpGroupLikeEquiv R hker x : F.completion) =
      F.completedExp ⟨x.1, x.2.mem_completionIdeal_one hker⟩ := (rfl)

/-- The inverse map of `F.completedExpGroupLikeEquiv R hker` is `F.completedLog`. -/
@[simp]
theorem coe_completedExpGroupLikeEquiv_symm
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1)
    (u : {u : F.completion // F.IsCompletedGroupLike R u}) :
    ((F.completedExpGroupLikeEquiv R hker).symm u : F.completion) =
      F.completedLog ⟨u.1, u.2.sub_one_mem hker⟩ := (rfl)

end Exp

end Completion

end TauCeti.AlgFiltration
