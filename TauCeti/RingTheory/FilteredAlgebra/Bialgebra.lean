/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.GroupLike
public import Mathlib.RingTheory.Bialgebra.Primitive
public import TauCeti.RingTheory.FilteredAlgebra.Exp.Basic
public import TauCeti.RingTheory.FilteredAlgebra.TensorProduct.Basic

import Mathlib.RingTheory.Nilpotent.Basic
import TauCeti.RingTheory.FilteredAlgebra.Exp.Map

/-!
# Filtered bialgebras, completed primitives, and completed group-like elements

An algebra filtration `F` on an `R`-bialgebra `A` is a bialgebra filtration
(`TauCeti.AlgFiltration.IsBialgebraFiltration`) when the coproduct sends each filtration ideal into
the corresponding total-degree ideal of `A ⊗[R] A` and the counit vanishes on `F.ideal 1`.

Over a commutative ring `R`, a bialgebra filtration induces a completed coproduct
`F.completedCoproduct R : F.completion →ₐ[R] (F.tensorProduct R F).completion` and a completed
counit `F.completedCounit R : F.completion →ₐ[R] R`. These define completed primitive elements
(`TauCeti.AlgFiltration.IsCompletedPrimitive`) and completed group-like elements
(`TauCeti.AlgFiltration.IsCompletedGroupLike`). Completed primitives form an `R`-submodule closed
under commutators and killed by the completed counit; completed group-like elements form a
submonoid, and those that are units form a subgroup of `F.completionˣ`. When `F.ideal 1` equals
the kernel of the counit, every completed group-like element is a unit in `1 + F.completionIdeal 1`
and every completed primitive lies in `F.completionIdeal 1`.

Over a rational algebra (`[Algebra ℚ A]`), completed exponentiation and logarithm restrict to
mutually inverse bijections between completed primitives in `F.completionIdeal 1` and completed
group-like elements in `1 + F.completionIdeal 1`. When `F.ideal 1` is the augmentation ideal, this
gives an equivalence `TauCeti.AlgFiltration.completedExpEquivCompletedGroupLike` between all
completed primitives and all completed group-like elements.

## Main definitions

* `TauCeti.AlgFiltration.IsBialgebraFiltration`: compatibility of an algebra filtration with the
  coproduct and counit.
* `TauCeti.AlgFiltration.completedCoproduct`: the induced algebra homomorphism
  `F.completion →ₐ[R] (F.tensorProduct R F).completion`.
* `TauCeti.AlgFiltration.completedCounit`: the induced algebra homomorphism
  `F.completion →ₐ[R] R`.
* `TauCeti.AlgFiltration.IsCompletedPrimitive`: the predicate
  `Δ̂ x = ι₁ x + ι₂ x` on `F.completion`.
* `TauCeti.AlgFiltration.completedPrimitiveSubmodule`: the `R`-submodule of completed primitive
  elements.
* `TauCeti.AlgFiltration.IsCompletedGroupLike`: elements with completed counit `1` and
  `Δ̂ u = u ⊗̂ u`.
* `TauCeti.AlgFiltration.completedGroupLikeSubmonoid` and
  `TauCeti.AlgFiltration.completedGroupLikeSubgroup`: the submonoid of completed group-like
  elements and the subgroup of unit group-like elements.
* `TauCeti.AlgFiltration.completedExpEquivCompletedGroupLike`: the exponential/logarithm bijection
  between completed primitives and completed group-like elements when `ker ε = F.ideal 1`.
-/

public section

open scoped TensorProduct

namespace TauCeti.AlgFiltration

section BialgebraFiltration

/-- An algebra filtration on an `R`-bialgebra is a bialgebra filtration if the coproduct preserves
filtration orders with respect to the total-degree filtration on `A ⊗[R] A` and the counit vanishes
on the first filtration ideal. -/
class IsBialgebraFiltration (R : Type*) {A : Type*} [CommSemiring R] [Semiring A]
    [Bialgebra R A] (F : AlgFiltration A) : Prop where
  /-- The coproduct maps each filtration ideal into the corresponding total-degree ideal. -/
  comul_le : ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A)
  /-- The counit vanishes on the first filtration ideal. -/
  counit_le : F.ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R A)

variable {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]
  (F : AlgFiltration A) [F.IsBialgebraFiltration R]

/-- The coproduct maps elements of filtration order `k` into total-degree filtration order `k`. -/
theorem comul_mem_tensorProduct_ideal {k : ℕ} {a : A} (ha : a ∈ F.ideal k) :
    Coalgebra.comul (R := R) a ∈ (F.tensorProduct R F).ideal k :=
  IsBialgebraFiltration.comul_le (R := R) (F := F) k ha

/-- The counit vanishes on the first filtration ideal. -/
theorem counit_eq_zero_of_mem_ideal_one {a : A} (ha : a ∈ F.ideal 1) :
    Coalgebra.counit (R := R) a = 0 :=
  IsBialgebraFiltration.counit_le (R := R) (F := F) ha

end BialgebraFiltration

section CompletedOperations

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Bialgebra R A]
  (F : AlgFiltration A) [F.IsBialgebraFiltration R]

/-- The completed coproduct induced by a bialgebra filtration. -/
noncomputable def completedCoproduct :
    F.completion →ₐ[R] (F.tensorProduct R F).completion :=
  F.mapCompletionₐ (F.tensorProduct R F) (Bialgebra.comulAlgHom R A) id monotone_id fun k =>
    IsBialgebraFiltration.comul_le (R := R) (F := F) (k + 1)

/-- The order-`k` component of the completed coproduct is the quotient map induced by `comul`. -/
@[simp]
theorem projection_completedCoproduct (k : ℕ) (x : F.completion) :
    (F.tensorProduct R F).projection k (F.completedCoproduct R x) =
      Ideal.quotientMapₐ ((F.tensorProduct R F).ideal (k + 1)) (Bialgebra.comulAlgHom R A)
        (IsBialgebraFiltration.comul_le (R := R) (F := F) (k + 1)) (F.projection k x) :=
  F.projection_mapCompletionₐ _ _ _ monotone_id _ k x

/-- The completed coproduct extends the ordinary coproduct on canonical elements. -/
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
  | succ k =>
    exact F.mapCompletionₐ_mem_completionIdeal _ _ id monotone_id _ k hx

/-- The completed counit induced by a bialgebra filtration, factoring through the order-zero
quotient `A ⧸ F.ideal 1`. -/
noncomputable def completedCounit : F.completion →ₐ[R] R :=
  (Ideal.Quotient.liftₐ (F.ideal 1) (Bialgebra.counitAlgHom R A) fun _ ha =>
    IsBialgebraFiltration.counit_le (R := R) (F := F) ha).comp (F.projectionₐ (R := R) 0)

/-- The completed counit extends the ordinary counit on canonical elements. -/
@[simp]
theorem completedCounit_toCompletion (a : A) :
    F.completedCounit R (F.toCompletion a) = Coalgebra.counit (R := R) a := by
  simp only [completedCounit, AlgHom.comp_apply, projectionₐ_apply, projection_toCompletion]
  exact Ideal.Quotient.lift_mk (F.ideal 1) (Bialgebra.counitAlgHom R A).toRingHom _

/-- The completed counit vanishes on the first completion ideal. -/
theorem completedCounit_eq_zero_of_mem_completionIdeal_one {x : F.completion}
    (hx : x ∈ F.completionIdeal 1) : F.completedCounit R x = 0 := by
  have hx0 : F.projection 0 x = 0 := by
    simpa only [completionIdeal_succ, RingHom.mem_ker] using hx
  simp [completedCounit, hx0]

/-- The first completion ideal is contained in the kernel of the completed counit. -/
theorem completionIdeal_one_le_ker_completedCounit :
    F.completionIdeal 1 ≤ RingHom.ker (F.completedCounit R) :=
  fun _ hx => RingHom.mem_ker.mpr (F.completedCounit_eq_zero_of_mem_completionIdeal_one R hx)

/-- When `ker ε ≤ F.ideal 1`, the kernel of the completed counit is `F.completionIdeal 1`. -/
theorem ker_completedCounit_eq_completionIdeal_one
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) :
    RingHom.ker (F.completedCounit R) = F.completionIdeal 1 := by
  refine le_antisymm (fun x hx => ?_) (F.completionIdeal_one_le_ker_completedCounit R)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection 0 x)
  have hε : Bialgebra.counitAlgHom R A a = 0 := by
    have h := RingHom.mem_ker.mp hx
    simp only [completedCounit, AlgHom.comp_apply, projectionₐ_apply, ← ha] at h
    exact h
  have ha1 : a ∈ F.ideal 1 := hker (RingHom.mem_ker.mpr hε)
  rw [completionIdeal_succ, RingHom.mem_ker, ← ha, Ideal.Quotient.eq_zero_iff_mem]
  exact ha1

/-- When `ker ε ≤ F.ideal 1`, vanishing of the completed counit characterizes membership in
`F.completionIdeal 1`. -/
theorem completedCounit_eq_zero_iff
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) {x : F.completion} :
    F.completedCounit R x = 0 ↔ x ∈ F.completionIdeal 1 := by
  rw [← F.ker_completedCounit_eq_completionIdeal_one R hker, RingHom.mem_ker]

/-- When `ker ε ≤ F.ideal 1`, having completed counit `1` characterizes congruence to `1` modulo
`F.completionIdeal 1`. -/
theorem completedCounit_eq_one_iff
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) {x : F.completion} :
    F.completedCounit R x = 1 ↔ x - 1 ∈ F.completionIdeal 1 := by
  rw [← F.completedCounit_eq_zero_iff R hker, map_sub, map_one, sub_eq_zero]

/-- The product of the two counits `a ⊗ b ↦ ε(a) * ε(b)` as an `R`-algebra map on `A ⊗[R] A`. -/
private noncomputable def tensorCounitAlgHom : A ⊗[R] A →ₐ[R] R :=
  Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R A) (Bialgebra.counitAlgHom R A)
    fun _ _ => Commute.all _ _

private theorem tensorCounitAlgHom_eq_zero_of_mem_ideal_one {t : A ⊗[R] A}
    (ht : t ∈ (F.tensorProduct R F).ideal 1) :
    tensorCounitAlgHom R t = 0 := by
  have hle : tensorFiltrationTail (fun n => (F.ideal n).restrictScalars R)
      (fun n => (F.ideal n).restrictScalars R) 1 ≤
      LinearMap.ker (tensorCounitAlgHom R).toLinearMap := by
    refine (tensorFiltrationTail_le_iff _ _).mpr fun a b hab x hx y hy => ?_
    simp only [LinearMap.mem_ker, AlgHom.toLinearMap_apply, tensorCounitAlgHom,
      Algebra.TensorProduct.lift_tmul, Bialgebra.counitAlgHom_apply]
    by_cases ha1 : 1 ≤ a
    · rw [F.counit_eq_zero_of_mem_ideal_one (F.antitone ha1 hx), zero_mul]
    · have hb1 : 1 ≤ b := by omega
      rw [F.counit_eq_zero_of_mem_ideal_one (F.antitone hb1 hy), mul_zero]
  exact hle ((F.mem_tensorProduct_ideal_iff R F).mp ht)

private theorem tensorCounitAlgHom_comul (a : A) :
    tensorCounitAlgHom R (Coalgebra.comul (R := R) a) = Coalgebra.counit (R := R) a := by
  have hlin : (tensorCounitAlgHom R).toLinearMap =
      (Coalgebra.counit (R := R) (A := A)).comp
        ((TensorProduct.lid R A).toLinearMap.comp
          ((Coalgebra.counit (R := R) (A := A)).rTensor A)) := by
    ext x y
    simp [tensorCounitAlgHom]
  have h := LinearMap.congr_fun hlin (Coalgebra.comul (R := R) a)
  have hrc := LinearMap.congr_fun (Coalgebra.rTensor_counit_comp_comul (R := R) (A := A)) a
  simp only [LinearMap.comp_apply] at h hrc
  simpa [hrc] using h

/-- The completed product counit `(F.tensorProduct R F).completion →ₐ[R] R`. -/
private noncomputable def completedTensorCounit :
    (F.tensorProduct R F).completion →ₐ[R] R :=
  (Ideal.Quotient.liftₐ ((F.tensorProduct R F).ideal 1) (tensorCounitAlgHom R) fun _ ht =>
    F.tensorCounitAlgHom_eq_zero_of_mem_ideal_one R ht).comp
      ((F.tensorProduct R F).projectionₐ (R := R) 0)

private theorem completedTensorCounit_completedCoproduct (x : F.completion) :
    F.completedTensorCounit R (F.completedCoproduct R x) = F.completedCounit R x := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection 0 x)
  simp only [completedTensorCounit, completedCounit, AlgHom.comp_apply, projectionₐ_apply,
    projection_completedCoproduct, ← ha]
  exact tensorCounitAlgHom_comul R a

private theorem completedTensorCounit_includeLeftCompletion (x : F.completion) :
    F.completedTensorCounit R (F.includeLeftCompletion R F x) = F.completedCounit R x := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection 0 x)
  simp only [completedTensorCounit, completedCounit, AlgHom.comp_apply, projectionₐ_apply,
    projection_includeLeftCompletion, ← ha]
  change tensorCounitAlgHom R (a ⊗ₜ[R] (1 : A)) = Bialgebra.counitAlgHom R A a
  simp [tensorCounitAlgHom]

private theorem completedTensorCounit_includeRightCompletion (x : F.completion) :
    F.completedTensorCounit R (F.includeRightCompletion R F x) = F.completedCounit R x := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection 0 x)
  simp only [completedTensorCounit, completedCounit, AlgHom.comp_apply, projectionₐ_apply,
    projection_includeRightCompletion, ← ha]
  change tensorCounitAlgHom R ((1 : A) ⊗ₜ[R] a) = Bialgebra.counitAlgHom R A a
  simp [tensorCounitAlgHom]

end CompletedOperations

section Primitive

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Bialgebra R A]
  (F : AlgFiltration A) [F.IsBialgebraFiltration R]

/-- An element `x` of the completion is completed primitive if its completed coproduct is
`x ⊗̂ 1 + 1 ⊗̂ x`, written in terms of the completed left and right inclusions. -/
def IsCompletedPrimitive (x : F.completion) : Prop :=
  F.completedCoproduct R x =
    F.includeLeftCompletion R F x + F.includeRightCompletion R F x

/-- Definition of `IsCompletedPrimitive` in terms of the completed inclusions. -/
theorem isCompletedPrimitive_iff {x : F.completion} :
    F.IsCompletedPrimitive R x ↔
      F.completedCoproduct R x =
        F.includeLeftCompletion R F x + F.includeRightCompletion R F x :=
  Iff.rfl

/-- Equivalent characterization of `IsCompletedPrimitive` using `completedTensor`. -/
theorem isCompletedPrimitive_iff_completedTensor {x : F.completion} :
    F.IsCompletedPrimitive R x ↔
      F.completedCoproduct R x =
        F.completedTensor R F 1 x + F.completedTensor R F x 1 := by
  simp [isCompletedPrimitive_iff, add_comm]

variable {R F}

/-- Every completed primitive element has zero completed counit. -/
theorem IsCompletedPrimitive.counit_eq_zero {x : F.completion}
    (hx : F.IsCompletedPrimitive R x) : F.completedCounit R x = 0 := by
  have h := congrArg (F.completedTensorCounit R) hx
  rw [F.completedTensorCounit_completedCoproduct R, map_add,
    F.completedTensorCounit_includeLeftCompletion R,
    F.completedTensorCounit_includeRightCompletion R] at h
  exact left_eq_add.mp h

/-- When `ker ε ≤ F.ideal 1`, every completed primitive element lies in `F.completionIdeal 1`. -/
theorem IsCompletedPrimitive.mem_completionIdeal_one
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) {x : F.completion}
    (hx : F.IsCompletedPrimitive R x) : x ∈ F.completionIdeal 1 :=
  (F.completedCounit_eq_zero_iff R hker).mp hx.counit_eq_zero

variable (R F)

/-- Zero is completed primitive. -/
theorem isCompletedPrimitive_zero : F.IsCompletedPrimitive R 0 := by
  simp [isCompletedPrimitive_iff]

variable {R F}

/-- The sum of two completed primitive elements is completed primitive. -/
theorem IsCompletedPrimitive.add {x y : F.completion}
    (hx : F.IsCompletedPrimitive R x) (hy : F.IsCompletedPrimitive R y) :
    F.IsCompletedPrimitive R (x + y) := by
  rw [isCompletedPrimitive_iff, map_add, map_add, map_add, hx, hy]
  abel

/-- The negation of a completed primitive element is completed primitive. -/
theorem IsCompletedPrimitive.neg {x : F.completion}
    (hx : F.IsCompletedPrimitive R x) : F.IsCompletedPrimitive R (-x) := by
  rw [isCompletedPrimitive_iff, map_neg, map_neg, map_neg, hx, neg_add]

/-- The difference of two completed primitive elements is completed primitive. -/
theorem IsCompletedPrimitive.sub {x y : F.completion}
    (hx : F.IsCompletedPrimitive R x) (hy : F.IsCompletedPrimitive R y) :
    F.IsCompletedPrimitive R (x - y) := by
  simpa only [sub_eq_add_neg] using hx.add hy.neg

/-- Any `R`-scalar multiple of a completed primitive element is completed primitive. -/
theorem IsCompletedPrimitive.smul (r : R) {x : F.completion}
    (hx : F.IsCompletedPrimitive R x) : F.IsCompletedPrimitive R (r • x) := by
  rw [isCompletedPrimitive_iff, map_smul, map_smul, map_smul, hx, smul_add]

/-- The commutator of two completed primitive elements is completed primitive. -/
theorem IsCompletedPrimitive.commutator {x y : F.completion}
    (hx : F.IsCompletedPrimitive R x) (hy : F.IsCompletedPrimitive R y) :
    F.IsCompletedPrimitive R (x * y - y * x) := by
  rw [isCompletedPrimitive_iff] at hx hy ⊢
  rw [map_sub, map_mul, map_mul, map_sub, map_mul, map_mul, map_sub, map_mul, map_mul, hx, hy]
  have hxy := (F.commute_includeLeftCompletion_includeRightCompletion R F x y).eq
  have hyx := (F.commute_includeLeftCompletion_includeRightCompletion R F y x).eq
  simp only [add_mul, mul_add, hxy, hyx]
  abel

/-- The canonical image of an ordinary primitive element is completed primitive. -/
theorem isCompletedPrimitive_toCompletion_of_isPrimitiveElem {a : A}
    (ha : Bialgebra.IsPrimitiveElem R a) :
    F.IsCompletedPrimitive R (F.toCompletion a) := by
  rw [isCompletedPrimitive_iff_completedTensor, F.completedCoproduct_toCompletion R,
    Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul.mp ha, map_add,
    ← F.completedTensor_toCompletion R F 1 a, ← F.completedTensor_toCompletion R F a 1, map_one]

variable (R F)

/-- The `R`-submodule of completed primitive elements of `F.completion`. -/
def completedPrimitiveSubmodule : Submodule R F.completion where
  carrier := {x | F.IsCompletedPrimitive R x}
  zero_mem' := F.isCompletedPrimitive_zero R
  add_mem' hx hy := hx.add hy
  smul_mem' r _ hx := hx.smul r

/-- Membership in `completedPrimitiveSubmodule` is `IsCompletedPrimitive`. -/
@[simp]
theorem mem_completedPrimitiveSubmodule {x : F.completion} :
    x ∈ F.completedPrimitiveSubmodule R ↔ F.IsCompletedPrimitive R x :=
  Iff.rfl

end Primitive

section GroupLike

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Bialgebra R A]
  (F : AlgFiltration A) [F.IsBialgebraFiltration R]

/-- An element `x` of the completion is completed group-like if its completed counit is `1` and its
completed coproduct is `x ⊗̂ x`. -/
@[mk_iff]
structure IsCompletedGroupLike (x : F.completion) : Prop where
  /-- The completed counit of a completed group-like element is `1`. -/
  counit_eq_one : F.completedCounit R x = 1
  /-- The completed coproduct of a completed group-like element is `x ⊗̂ x`. -/
  comul_eq_completedTensor : F.completedCoproduct R x = F.completedTensor R F x x

/-- One is completed group-like. -/
theorem isCompletedGroupLike_one : F.IsCompletedGroupLike R 1 where
  counit_eq_one := map_one _
  comul_eq_completedTensor := by simp

variable {R F}

/-- The product of two completed group-like elements is completed group-like. -/
theorem IsCompletedGroupLike.mul {x y : F.completion}
    (hx : F.IsCompletedGroupLike R x) (hy : F.IsCompletedGroupLike R y) :
    F.IsCompletedGroupLike R (x * y) where
  counit_eq_one := by rw [map_mul, hx.counit_eq_one, hy.counit_eq_one, mul_one]
  comul_eq_completedTensor := by
    rw [map_mul, hx.comul_eq_completedTensor, hy.comul_eq_completedTensor,
      F.completedTensor_mul R F]

/-- Every natural power of a completed group-like element is completed group-like. -/
theorem IsCompletedGroupLike.pow {x : F.completion} (hx : F.IsCompletedGroupLike R x) (n : ℕ) :
    F.IsCompletedGroupLike R (x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using F.isCompletedGroupLike_one R
  | succ n ih => simpa only [pow_succ] using ih.mul hx

/-- The two-sided inverse of a completed group-like element is completed group-like. -/
theorem IsCompletedGroupLike.of_mul_eq_one {x y : F.completion}
    (hx : F.IsCompletedGroupLike R x) (hxy : x * y = 1) (hyx : y * x = 1) :
    F.IsCompletedGroupLike R y where
  counit_eq_one := by
    have h := congrArg (F.completedCounit R) hxy
    rwa [map_mul, map_one, hx.counit_eq_one, one_mul] at h
  comul_eq_completedTensor :=
    left_inv_eq_right_inv (a := F.completedCoproduct R x)
      (by rw [← map_mul, hyx, map_one])
      (by rw [hx.comul_eq_completedTensor, ← F.completedTensor_mul R F, hxy,
        completedTensor_one_left, map_one])

/-- A unit in `F.completionˣ` is completed group-like if and only if its inverse is. -/
@[simp]
theorem isCompletedGroupLike_unitsInv {u : F.completionˣ} :
    F.IsCompletedGroupLike R ((u⁻¹ : F.completionˣ) : F.completion) ↔
      F.IsCompletedGroupLike R (u : F.completion) :=
  ⟨fun h => h.of_mul_eq_one u.inv_mul u.mul_inv, fun h => h.of_mul_eq_one u.mul_inv u.inv_mul⟩

alias ⟨IsCompletedGroupLike.of_unitsInv, IsCompletedGroupLike.unitsInv⟩ :=
  isCompletedGroupLike_unitsInv

/-- The canonical image of an ordinary group-like element is completed group-like. -/
theorem isCompletedGroupLike_toCompletion_of_isGroupLikeElem {a : A}
    (ha : IsGroupLikeElem R a) :
    F.IsCompletedGroupLike R (F.toCompletion a) where
  counit_eq_one := by rw [F.completedCounit_toCompletion R, ha.counit_eq_one]
  comul_eq_completedTensor := by
    rw [F.completedCoproduct_toCompletion R, ha.comul_eq_tmul_self,
      F.completedTensor_toCompletion R F]

/-- When `ker ε ≤ F.ideal 1`, every completed group-like element is congruent to `1` modulo
`F.completionIdeal 1`. -/
theorem IsCompletedGroupLike.sub_one_mem_completionIdeal_one
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) {u : F.completion}
    (hu : F.IsCompletedGroupLike R u) : u - 1 ∈ F.completionIdeal 1 :=
  (F.completedCounit_eq_one_iff R hker).mp hu.counit_eq_one

/-- Every element of `F.completion` congruent to `1` modulo `F.completionIdeal 1` is a unit. -/
private theorem isUnit_of_sub_one_mem_completionIdeal_one {u : F.completion}
    (hu : u - 1 ∈ F.completionIdeal 1) : IsUnit u := by
  have hunit (k : ℕ) : IsUnit (F.projection k u) := by
    have hnil : IsNilpotent (F.projection k u - 1) := by
      simpa only [map_sub, map_one] using F.isNilpotent_projection hu k
    simpa only [add_sub_cancel] using hnil.isUnit_one_add
  let invk (k : ℕ) : A ⧸ F.ideal (k + 1) := ((hunit k).unit⁻¹ : (A ⧸ F.ideal (k + 1))ˣ)
  have hmul (k : ℕ) : F.projection k u * invk k = 1 := by
    simpa only [invk, (hunit k).unit_spec] using Units.mul_inv (hunit k).unit
  have hinv_mul (k : ℕ) : invk k * F.projection k u = 1 := by
    simpa only [invk, (hunit k).unit_spec] using Units.inv_mul (hunit k).unit
  let inv : F.completion :=
    ⟨fun k => invk k.unop,
      (F.mem_completion_iff _).mpr fun {k l} h => by
        let φ := Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1))
        calc
          φ (invk l) = invk k * (F.projection k u * φ (invk l)) := by
            rw [← mul_assoc, hinv_mul k, one_mul]
          _ = invk k * φ (F.projection l u * invk l) := by
            rw [map_mul, F.factor_projection h u]
          _ = invk k := by rw [hmul l, map_one, mul_one]⟩
  refine ⟨⟨u, inv, ?_, ?_⟩, rfl⟩
  · refine F.completion_ext fun k => ?_
    rw [map_mul, map_one, F.projection_apply k inv]
    exact hmul k
  · refine F.completion_ext fun k => ?_
    rw [map_mul, map_one, F.projection_apply k inv]
    exact hinv_mul k

/-- When `ker ε ≤ F.ideal 1`, every completed group-like element is a unit. -/
theorem IsCompletedGroupLike.isUnit
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) {u : F.completion}
    (hu : F.IsCompletedGroupLike R u) : IsUnit u :=
  F.isUnit_of_sub_one_mem_completionIdeal_one (hu.sub_one_mem_completionIdeal_one hker)

variable (R F)

/-- The submonoid of completed group-like elements of `F.completion`. -/
def completedGroupLikeSubmonoid : Submonoid F.completion where
  carrier := {u | F.IsCompletedGroupLike R u}
  one_mem' := F.isCompletedGroupLike_one R
  mul_mem' hx hy := hx.mul hy

/-- Membership in `completedGroupLikeSubmonoid` is `IsCompletedGroupLike`. -/
@[simp]
theorem mem_completedGroupLikeSubmonoid {u : F.completion} :
    u ∈ F.completedGroupLikeSubmonoid R ↔ F.IsCompletedGroupLike R u :=
  Iff.rfl

/-- The subgroup of unit completed group-like elements in `F.completionˣ`. -/
def completedGroupLikeSubgroup : Subgroup F.completionˣ where
  carrier := {u | F.IsCompletedGroupLike R (u : F.completion)}
  one_mem' := F.isCompletedGroupLike_one R
  mul_mem' hx hy := hx.mul hy
  inv_mem' hx := hx.unitsInv

/-- Membership in `completedGroupLikeSubgroup` is `IsCompletedGroupLike` on the underlying
element. -/
@[simp]
theorem mem_completedGroupLikeSubgroup {u : F.completionˣ} :
    u ∈ F.completedGroupLikeSubgroup R ↔ F.IsCompletedGroupLike R (u : F.completion) :=
  Iff.rfl

end GroupLike

section ExpLog

variable {R A : Type*} [CommRing R] [Ring A] [Bialgebra R A] [Algebra ℚ A]
  {F : AlgFiltration A} [F.IsBialgebraFiltration R]

private lemma smulCommClass_rat : SMulCommClass R ℚ A :=
  ⟨fun r q a => by
    rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← Algebra.commutes,
      mul_assoc, ← Algebra.smul_def, ← Algebra.smul_def]⟩

private theorem completedCoproduct_completedExp_aux (x : F.completionIdeal 1) :
    let _ : SMulCommClass R ℚ A := smulCommClass_rat
    F.completedCoproduct R (F.completedExp x) =
      (F.tensorProduct R F).completedExp
        ⟨F.completedCoproduct R x, F.completedCoproduct_mem_completionIdeal R x.property⟩ := by
  let _ : SMulCommClass R ℚ A := smulCommClass_rat
  have h := F.mapCompletion_completedExp (F.tensorProduct R F)
    (Bialgebra.comulAlgHom R A : A →+* A ⊗[R] A) id monotone_id
    (fun k => IsBialgebraFiltration.comul_le (R := R) (F := F) (k + 1))
    (IsBialgebraFiltration.comul_le (R := R) (F := F) 1) x
  simpa only [completedCoproduct, ← AlgHom.coe_toRingHom, coe_mapCompletionₐ] using h

omit [F.IsBialgebraFiltration R] in
private theorem includeLeftCompletion_completedExp_aux (x : F.completionIdeal 1) :
    let _ : SMulCommClass R ℚ A := smulCommClass_rat
    F.includeLeftCompletion R F (F.completedExp x) =
      (F.tensorProduct R F).completedExp
        ⟨F.includeLeftCompletion R F x,
          F.includeLeftCompletion_mem_completionIdeal R F x.property⟩ := by
  let _ : SMulCommClass R ℚ A := smulCommClass_rat
  refine (F.tensorProduct R F).completion_ext fun k => ?_
  rw [projection_includeLeftCompletion, projection_completedExp, projection_completedExp,
    projection_includeLeftCompletion]
  exact (F.isNilpotent_projection x.property k).map_exp _

omit [F.IsBialgebraFiltration R] in
private theorem includeRightCompletion_completedExp_aux (x : F.completionIdeal 1) :
    let _ : SMulCommClass R ℚ A := smulCommClass_rat
    F.includeRightCompletion R F (F.completedExp x) =
      (F.tensorProduct R F).completedExp
        ⟨F.includeRightCompletion R F x,
          F.includeRightCompletion_mem_completionIdeal R F x.property⟩ := by
  let _ : SMulCommClass R ℚ A := smulCommClass_rat
  refine (F.tensorProduct R F).completion_ext fun k => ?_
  rw [projection_includeRightCompletion, projection_completedExp, projection_completedExp,
    projection_includeRightCompletion]
  exact (F.isNilpotent_projection x.property k).map_exp _

/-- The completed exponential of a completed primitive element in `F.completionIdeal 1` is
completed group-like. -/
theorem IsCompletedPrimitive.completedExp {x : F.completion}
    (hx : F.IsCompletedPrimitive R x) (hx1 : x ∈ F.completionIdeal 1) :
    F.IsCompletedGroupLike R (F.completedExp ⟨x, hx1⟩) := by
  let _ : SMulCommClass R ℚ A := smulCommClass_rat
  let x' : F.completionIdeal 1 := ⟨x, hx1⟩
  refine ⟨?_, ?_⟩
  · have h1 :=
      F.completedCounit_eq_zero_of_mem_completionIdeal_one R (F.completedExp_sub_one_mem x')
    rwa [map_sub, map_one, sub_eq_zero] at h1
  · have hsub : (⟨F.completedCoproduct R x,
          F.completedCoproduct_mem_completionIdeal R hx1⟩ :
          (F.tensorProduct R F).completionIdeal 1) =
        ⟨F.includeLeftCompletion R F x,
          F.includeLeftCompletion_mem_completionIdeal R F hx1⟩ +
        ⟨F.includeRightCompletion R F x,
          F.includeRightCompletion_mem_completionIdeal R F hx1⟩ :=
      Subtype.ext hx
    rw [completedCoproduct_completedExp_aux (R := R) x', hsub,
      (F.tensorProduct R F).completedExp_add _ _
        (F.commute_includeLeftCompletion_includeRightCompletion R F x x),
      ← includeLeftCompletion_completedExp_aux (R := R) x',
      ← includeRightCompletion_completedExp_aux (R := R) x', completedTensor_apply]

/-- The completed logarithm of a completed group-like element in `1 + F.completionIdeal 1` is
completed primitive. -/
theorem IsCompletedGroupLike.completedLog {u : F.completion}
    (hu : F.IsCompletedGroupLike R u) (hu1 : u - 1 ∈ F.completionIdeal 1) :
    F.IsCompletedPrimitive R (F.completedLog ⟨u, hu1⟩) := by
  let _ : SMulCommClass R ℚ A := smulCommClass_rat
  let x : F.completionIdeal 1 := ⟨F.completedLog ⟨u, hu1⟩, F.completedLog_mem ⟨u, hu1⟩⟩
  have hexpx : F.completedExp x = u := F.completedExp_completedLog ⟨u, hu1⟩
  let lhs : (F.tensorProduct R F).completionIdeal 1 :=
    ⟨F.completedCoproduct R x, F.completedCoproduct_mem_completionIdeal R x.property⟩
  let rhs : (F.tensorProduct R F).completionIdeal 1 :=
    ⟨F.includeLeftCompletion R F x,
      F.includeLeftCompletion_mem_completionIdeal R F x.property⟩ +
    ⟨F.includeRightCompletion R F x,
      F.includeRightCompletion_mem_completionIdeal R F x.property⟩
  have heq : (F.tensorProduct R F).completedExp lhs = (F.tensorProduct R F).completedExp rhs := by
    rw [← completedCoproduct_completedExp_aux (R := R) x, hexpx, hu.comul_eq_completedTensor,
      completedTensor_apply, (F.tensorProduct R F).completedExp_add _ _
        (F.commute_includeLeftCompletion_includeRightCompletion R F x x),
      ← includeLeftCompletion_completedExp_aux (R := R) x,
      ← includeRightCompletion_completedExp_aux (R := R) x, hexpx]
  have hsub : lhs = rhs :=
    (F.tensorProduct R F).completedExpEquiv.injective (Subtype.ext (by
      simpa only [coe_completedExpEquiv] using heq))
  exact congrArg Subtype.val hsub

variable (R F)

/-- Completed exponentiation and logarithm identify completed primitives in `F.completionIdeal 1`
with completed group-like elements congruent to `1` modulo `F.completionIdeal 1`. -/
noncomputable def completedExpPrimitiveEquivGroupLike :
    {x : F.completion // x ∈ F.completionIdeal 1 ∧ F.IsCompletedPrimitive R x} ≃
      {u : F.completion // u - 1 ∈ F.completionIdeal 1 ∧ F.IsCompletedGroupLike R u} where
  toFun x :=
    ⟨F.completedExp ⟨x.1, x.2.1⟩,
      F.completedExp_sub_one_mem ⟨x.1, x.2.1⟩,
      x.2.2.completedExp x.2.1⟩
  invFun u :=
    ⟨F.completedLog ⟨u.1, u.2.1⟩,
      F.completedLog_mem ⟨u.1, u.2.1⟩,
      u.2.2.completedLog u.2.1⟩
  left_inv x := Subtype.ext (F.completedLog_completedExp ⟨x.1, x.2.1⟩)
  right_inv u := Subtype.ext (F.completedExp_completedLog ⟨u.1, u.2.1⟩)

/-- The forward map of `completedExpPrimitiveEquivGroupLike` is `completedExp`. -/
@[simp]
theorem coe_completedExpPrimitiveEquivGroupLike
    (x : {x : F.completion // x ∈ F.completionIdeal 1 ∧ F.IsCompletedPrimitive R x}) :
    (F.completedExpPrimitiveEquivGroupLike R x : F.completion) =
      F.completedExp ⟨x.1, x.2.1⟩ := (rfl)

/-- The inverse map of `completedExpPrimitiveEquivGroupLike` is `completedLog`. -/
@[simp]
theorem coe_completedExpPrimitiveEquivGroupLike_symm
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1 ∧ F.IsCompletedGroupLike R u}) :
    ((F.completedExpPrimitiveEquivGroupLike R).symm u : F.completion) =
      F.completedLog ⟨u.1, u.2.1⟩ := (rfl)

/-- When `ker ε ≤ F.ideal 1`, completed exponentiation and logarithm give a bijection between all
completed primitives and all completed group-like elements. -/
noncomputable def completedExpEquivCompletedGroupLike
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) :
    {x : F.completion // F.IsCompletedPrimitive R x} ≃
      {u : F.completion // F.IsCompletedGroupLike R u} where
  toFun x :=
    ⟨F.completedExp ⟨x.1, x.2.mem_completionIdeal_one hker⟩,
      x.2.completedExp (x.2.mem_completionIdeal_one hker)⟩
  invFun u :=
    ⟨F.completedLog ⟨u.1, u.2.sub_one_mem_completionIdeal_one hker⟩,
      u.2.completedLog (u.2.sub_one_mem_completionIdeal_one hker)⟩
  left_inv x := Subtype.ext (F.completedLog_completedExp ⟨x.1, x.2.mem_completionIdeal_one hker⟩)
  right_inv u :=
    Subtype.ext (F.completedExp_completedLog ⟨u.1, u.2.sub_one_mem_completionIdeal_one hker⟩)

/-- The forward map of `completedExpEquivCompletedGroupLike` is `completedExp`. -/
@[simp]
theorem coe_completedExpEquivCompletedGroupLike
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1)
    (x : {x : F.completion // F.IsCompletedPrimitive R x}) :
    (F.completedExpEquivCompletedGroupLike R hker x : F.completion) =
      F.completedExp ⟨x.1, x.2.mem_completionIdeal_one hker⟩ := (rfl)

/-- The inverse map of `completedExpEquivCompletedGroupLike` is `completedLog`. -/
@[simp]
theorem coe_completedExpEquivCompletedGroupLike_symm
    (hker : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1)
    (u : {u : F.completion // F.IsCompletedGroupLike R u}) :
    ((F.completedExpEquivCompletedGroupLike R hker).symm u : F.completion) =
      F.completedLog ⟨u.1, u.2.sub_one_mem_completionIdeal_one hker⟩ := (rfl)

end ExpLog

end TauCeti.AlgFiltration
