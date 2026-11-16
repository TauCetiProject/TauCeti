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

import TauCeti.RingTheory.FilteredAlgebra.Exp.Map

/-!
# Completed bialgebra structure, primitives, and group-like elements

Let `A` be a bialgebra over a commutative ring `R` equipped with a decreasing multiplicative ideal
filtration `F`. When comultiplication maps `F.ideal k` into the total-degree tensor ideal
`(F.tensorProduct R F).ideal k`, it extends to an algebra homomorphism
`TauCeti.AlgFiltration.completedCoproduct` from `F.completion` to
`(F.tensorProduct R F).completion`. When `F.ideal 1` lies in the kernel of the counit, the counit
descends through the order-zero quotient to `TauCeti.AlgFiltration.completedCounit`.

An element `x` of `F.completion` is completed primitive when `Δ̂ x = x ⊗̂ 1 + 1 ⊗̂ x`, written via
the completed left and right tensor inclusions (`TauCeti.AlgFiltration.IsCompletedPrimitive`).
This automatically forces `ε̂ x = 0`, and completed primitives form an `R`-submodule closed under
commutators. An element `u` is completed group-like (`TauCeti.AlgFiltration.IsCompletedGroupLike`)
when `ε̂ u = 1` and `Δ̂ u = u ⊗̂ u`; completed group-like units form a subgroup of `F.completionˣ`.

When `A` is also a `ℚ`-algebra, the completed exponential `TauCeti.AlgFiltration.completedExp` and
completed logarithm `TauCeti.AlgFiltration.completedLog` restrict to mutually inverse bijections
between completed primitives in `F.completionIdeal 1` and completed group-like elements congruent
to one modulo `F.completionIdeal 1`. When `F.ideal 1` equals the kernel of the counit, these
filtration conditions are automatic and every completed group-like element is a unit, identifying
the completed primitives with the completed group-like subgroup. Multiplication may be
noncommutative, and no flatness, separatedness, or antipode is required.

## Main definitions

* `TauCeti.AlgFiltration.completedCoproduct`: the completed comultiplication
  `F.completion →ₐ[R] (F.tensorProduct R F).completion`.
* `TauCeti.AlgFiltration.completedCounit`: the completed counit `F.completion →ₐ[R] R`.
* `TauCeti.AlgFiltration.IsCompletedPrimitive`: the predicate for completed primitive elements.
* `TauCeti.AlgFiltration.completedPrimitiveSubmodule`: the `R`-submodule of completed primitives.
* `TauCeti.AlgFiltration.IsCompletedGroupLike`: the predicate for completed group-like elements.
* `TauCeti.AlgFiltration.completedGroupLikeSubgroup`: the subgroup of completed group-like units.
* `TauCeti.AlgFiltration.completedPrimitiveEquivGroupLike` and
  `TauCeti.AlgFiltration.completedPrimitiveEquivGroupLikeOfKerEq`: the exponential-logarithm
  bijections between completed primitives and completed group-like elements.

## Main results

* `TauCeti.AlgFiltration.IsCompletedPrimitive.completedCounit_eq_zero`: every completed primitive
  element has completed counit zero.
* `TauCeti.AlgFiltration.IsCompletedPrimitive.commutator`: the commutator of completed primitives
  is completed primitive.
* `TauCeti.AlgFiltration.isCompletedGroupLike_completedExp`: the completed exponential of a
  completed primitive in the first completion ideal is completed group-like.
* `TauCeti.AlgFiltration.isCompletedPrimitive_completedLog`: the completed logarithm of a
  completed group-like element congruent to one is completed primitive.
-/

public section

open scoped TensorProduct

namespace TauCeti.AlgFiltration

section Bialgebra

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Bialgebra R A] (F : AlgFiltration A)

section Coproduct

variable (hcomul : ∀ k,
  F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))

/-- The completed comultiplication on a filtered bialgebra whose comultiplication preserves the
filtration. -/
noncomputable def completedCoproduct :
    F.completion →ₐ[R] (F.tensorProduct R F).completion :=
  F.mapCompletionₐ (F.tensorProduct R F) (Bialgebra.comulAlgHom R A) id monotone_id
    fun k => hcomul (k + 1)

/-- The order-`k` projection of the completed coproduct is the quotient comultiplication. -/
@[simp]
theorem projection_completedCoproduct (k : ℕ) (x : F.completion) :
    (F.tensorProduct R F).projection k (F.completedCoproduct R hcomul x) =
      Ideal.quotientMapₐ ((F.tensorProduct R F).ideal (k + 1)) (Bialgebra.comulAlgHom R A)
        (hcomul (k + 1)) (F.projection k x) :=
  F.projection_mapCompletionₐ (F.tensorProduct R F) (Bialgebra.comulAlgHom R A) id monotone_id
    (fun k => hcomul (k + 1)) k x

/-- On canonical elements, the completed coproduct agrees with the original comultiplication. -/
@[simp]
theorem completedCoproduct_toCompletion (a : A) :
    F.completedCoproduct R hcomul (F.toCompletion a) =
      (F.tensorProduct R F).toCompletion (Coalgebra.comul (R := R) a) :=
  F.mapCompletionₐ_toCompletion (F.tensorProduct R F) (Bialgebra.comulAlgHom R A) id monotone_id
    (fun k => hcomul (k + 1)) a

/-- The completed coproduct preserves every completed filtration order. -/
theorem completedCoproduct_mem_completionIdeal {k : ℕ} {x : F.completion}
    (hx : x ∈ F.completionIdeal k) :
    F.completedCoproduct R hcomul x ∈ (F.tensorProduct R F).completionIdeal k := by
  cases k with
  | zero => simp
  | succ k =>
    exact F.mapCompletionₐ_mem_completionIdeal (F.tensorProduct R F) (Bialgebra.comulAlgHom R A)
      id monotone_id (fun j => hcomul (j + 1)) k hx

end Coproduct

section Counit

variable (hcounit : F.ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R A))

/-- The completed counit on a filtered bialgebra whose first filtration ideal lies in the kernel
of the counit. -/
noncomputable def completedCounit : F.completion →ₐ[R] R :=
  (Ideal.Quotient.liftₐ (F.ideal 1) (Bialgebra.counitAlgHom R A) fun _ ha =>
    RingHom.mem_ker.mp (hcounit ha)).comp (F.projectionₐ (R := R) 0)

/-- The completed counit is computed on any representative of the order-zero projection. -/
theorem completedCounit_eq_of_projection_zero {x : F.completion} {a : A}
    (ha : Ideal.Quotient.mk (F.ideal 1) a = F.projection 0 x) :
    F.completedCounit R hcounit x = Coalgebra.counit (R := R) a := by
  rw [completedCounit, AlgHom.comp_apply, projectionₐ_apply, ← ha,
    ← Ideal.Quotient.mkₐ_eq_mk R, ← AlgHom.comp_apply, Ideal.Quotient.liftₐ_comp,
    Bialgebra.counitAlgHom_apply]

/-- On canonical elements, the completed counit agrees with the original counit. -/
@[simp]
theorem completedCounit_toCompletion (a : A) :
    F.completedCounit R hcounit (F.toCompletion a) = Coalgebra.counit (R := R) a :=
  F.completedCounit_eq_of_projection_zero R hcounit (F.projection_toCompletion 0 a).symm

/-- Every element of the first completion ideal has completed counit zero. -/
theorem completedCounit_eq_zero_of_mem_completionIdeal_one {x : F.completion}
    (hx : x ∈ F.completionIdeal 1) :
    F.completedCounit R hcounit x = 0 := by
  have hx₀ : F.projection 0 x = 0 := by
    simpa only [completionIdeal_succ, RingHom.mem_ker] using hx
  rw [completedCounit, AlgHom.comp_apply, projectionₐ_apply, hx₀, map_zero]

end Counit

/-- When the first filtration ideal is the kernel of the counit, membership in the first
completion ideal is equivalent to vanishing of the completed counit. -/
theorem mem_completionIdeal_one_iff_completedCounit_eq_zero
    (hker : F.ideal 1 = RingHom.ker (Bialgebra.counitAlgHom R A)) {x : F.completion} :
    x ∈ F.completionIdeal 1 ↔ F.completedCounit R hker.le x = 0 := by
  constructor
  · exact F.completedCounit_eq_zero_of_mem_completionIdeal_one R hker.le
  · intro hx
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection 0 x)
    have hε : Coalgebra.counit (R := R) a = 0 :=
      (F.completedCounit_eq_of_projection_zero R hker.le ha).symm.trans hx
    have ha₁ : a ∈ F.ideal 1 := by
      rw [hker, RingHom.mem_ker, Bialgebra.counitAlgHom_apply]
      exact hε
    rw [completionIdeal_succ, RingHom.mem_ker, ← ha]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha₁

/-- When the first filtration ideal is the kernel of the counit, congruence to one modulo the
first completion ideal is equivalent to having completed counit one. -/
theorem sub_one_mem_completionIdeal_one_iff_completedCounit_eq_one
    (hker : F.ideal 1 = RingHom.ker (Bialgebra.counitAlgHom R A)) {u : F.completion} :
    u - 1 ∈ F.completionIdeal 1 ↔ F.completedCounit R hker.le u = 1 := by
  rw [F.mem_completionIdeal_one_iff_completedCounit_eq_zero R hker, map_sub, map_one, sub_eq_zero]

/-- An element of the completion is completed primitive if its completed coproduct is the sum of
its left and right tensor inclusions. -/
def IsCompletedPrimitive
    (hcomul : ∀ k,
      F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (x : F.completion) : Prop :=
  F.completedCoproduct R hcomul x =
    F.includeLeftCompletion R F x + F.includeRightCompletion R F x

/-- Characterization of completed primitivity by the completed left and right tensor inclusions. -/
theorem isCompletedPrimitive_iff
    (hcomul : ∀ k,
      F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    {x : F.completion} :
    F.IsCompletedPrimitive R hcomul x ↔
      F.completedCoproduct R hcomul x =
        F.includeLeftCompletion R F x + F.includeRightCompletion R F x :=
  Iff.rfl

/-- Completed primitivity expressed with completed pure tensors `x ⊗̂ 1 + 1 ⊗̂ x`. -/
theorem isCompletedPrimitive_iff_completedTensor
    (hcomul : ∀ k,
      F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    {x : F.completion} :
    F.IsCompletedPrimitive R hcomul x ↔
      F.completedCoproduct R hcomul x =
        F.completedTensor R F x 1 + F.completedTensor R F 1 x := by
  simp only [IsCompletedPrimitive, completedTensor_one_right, completedTensor_one_left]

section Primitive

variable {R F}
variable {hcomul :
  ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A)}

/-- A completed primitive element satisfies the defining coproduct identity. -/
theorem IsCompletedPrimitive.completedCoproduct_eq {x : F.completion}
    (hx : F.IsCompletedPrimitive R hcomul x) :
    F.completedCoproduct R hcomul x =
      F.includeLeftCompletion R F x + F.includeRightCompletion R F x :=
  hx

/-- Zero is completed primitive. -/
theorem IsCompletedPrimitive.zero : F.IsCompletedPrimitive R hcomul 0 := by
  simp [IsCompletedPrimitive]

/-- The sum of completed primitive elements is completed primitive. -/
theorem IsCompletedPrimitive.add {x y : F.completion}
    (hx : F.IsCompletedPrimitive R hcomul x) (hy : F.IsCompletedPrimitive R hcomul y) :
    F.IsCompletedPrimitive R hcomul (x + y) := by
  rw [IsCompletedPrimitive, map_add, map_add, map_add, hx, hy]
  abel

/-- The negation of a completed primitive element is completed primitive. -/
theorem IsCompletedPrimitive.neg {x : F.completion}
    (hx : F.IsCompletedPrimitive R hcomul x) :
    F.IsCompletedPrimitive R hcomul (-x) := by
  rw [IsCompletedPrimitive, map_neg, map_neg, map_neg, hx]
  abel

/-- The difference of completed primitive elements is completed primitive. -/
theorem IsCompletedPrimitive.sub {x y : F.completion}
    (hx : F.IsCompletedPrimitive R hcomul x) (hy : F.IsCompletedPrimitive R hcomul y) :
    F.IsCompletedPrimitive R hcomul (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

/-- Scalar multiples of a completed primitive element are completed primitive. -/
theorem IsCompletedPrimitive.smul {x : F.completion} (r : R)
    (hx : F.IsCompletedPrimitive R hcomul x) :
    F.IsCompletedPrimitive R hcomul (r • x) := by
  rw [IsCompletedPrimitive, map_smul, map_smul, map_smul, hx, smul_add]

/-- The commutator of two completed primitive elements is completed primitive. -/
theorem IsCompletedPrimitive.commutator {x y : F.completion}
    (hx : F.IsCompletedPrimitive R hcomul x) (hy : F.IsCompletedPrimitive R hcomul y) :
    F.IsCompletedPrimitive R hcomul (x * y - y * x) := by
  have hxy : Commute (F.includeLeftCompletion R F x) (F.includeRightCompletion R F y) :=
    F.commute_includeLeftCompletion_includeRightCompletion R F x y
  have hyx : Commute (F.includeLeftCompletion R F y) (F.includeRightCompletion R F x) :=
    F.commute_includeLeftCompletion_includeRightCompletion R F y x
  rw [IsCompletedPrimitive, map_sub, map_mul, map_mul, hx, hy, map_sub, map_mul, map_mul,
    map_sub, map_mul, map_mul]
  simp only [add_mul, mul_add, hxy.eq, hyx.eq]
  abel

/-- The canonical image of a primitive element is completed primitive. -/
theorem IsCompletedPrimitive.toCompletion {a : A} (ha : Bialgebra.IsPrimitiveElem R a) :
    F.IsCompletedPrimitive R hcomul (F.toCompletion a) := by
  rw [IsCompletedPrimitive, F.completedCoproduct_toCompletion R hcomul a,
    F.includeLeftCompletion_toCompletion R F a, F.includeRightCompletion_toCompletion R F a,
    ← map_add, ha.comul_eq_tmul_add_tmul, add_comm]

/-- Multiplying the counits on a tensor product recovers the counit after comultiplication. -/
private theorem lift_counit_comul (a : A) :
    Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R A) (Bialgebra.counitAlgHom R A)
        (fun _ _ => Commute.all _ _) (Coalgebra.comul (R := R) a) =
      Coalgebra.counit (R := R) a := by
  let f : A ⊗[R] A →ₗ[R] R :=
    (Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R A) (Bialgebra.counitAlgHom R A)
      (fun _ _ => Commute.all _ _)).toLinearMap
  let g : A ⊗[R] A →ₗ[R] R :=
    (Coalgebra.counit (R := R)).comp
      ((TensorProduct.lid R A).toLinearMap.comp ((Coalgebra.counit (R := R)).rTensor A))
  have hfg : f = g := by
    apply TensorProduct.ext'
    intro x y
    simp only [f, g, AlgHom.toLinearMap_apply, Algebra.TensorProduct.lift_tmul,
      Bialgebra.counitAlgHom_apply, LinearMap.comp_apply, LinearMap.rTensor_tmul,
      LinearEquiv.coe_coe, TensorProduct.lid_tmul, map_smul, smul_eq_mul]
  have h := LinearMap.congr_fun hfg (Coalgebra.comul (R := R) a)
  have hco := LinearMap.congr_fun (Coalgebra.rTensor_counit_comp_comul (R := R) (A := A)) a
  simp only [f, g, AlgHom.toLinearMap_apply, LinearMap.comp_apply, TensorProduct.mk_apply] at h hco
  rw [h, hco, LinearEquiv.coe_coe, TensorProduct.lid_tmul, one_smul]

/-- Every completed primitive element has completed counit zero. -/
theorem IsCompletedPrimitive.completedCounit_eq_zero
    (hcounit : F.ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R A))
    {x : F.completion} (hx : F.IsCompletedPrimitive R hcomul x) :
    F.completedCounit R hcounit x = 0 := by
  let ε₂ : A ⊗[R] A →ₐ[R] R :=
    Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R A) (Bialgebra.counitAlgHom R A)
      (fun _ _ => Commute.all _ _)
  have hε₂ : ∀ t ∈ (F.tensorProduct R F).ideal 1, ε₂ t = 0 := by
    have hle : tensorFiltrationTail (fun n => (F.ideal n).restrictScalars R)
        (fun n => (F.ideal n).restrictScalars R) 1 ≤ LinearMap.ker ε₂.toLinearMap := by
      refine (tensorFiltrationTail_le_iff _ _).mpr fun a b hab y hy z hz => ?_
      simp only [LinearMap.mem_ker, AlgHom.toLinearMap_apply, ε₂,
        Algebra.TensorProduct.lift_tmul, Bialgebra.counitAlgHom_apply]
      by_cases ha : 1 ≤ a
      · have hy0 : Coalgebra.counit (R := R) y = 0 := by
          simpa only [RingHom.mem_ker, Bialgebra.counitAlgHom_apply] using
            hcounit (F.antitone ha hy)
        rw [hy0, zero_mul]
      · have hb : 1 ≤ b := by omega
        have hz0 : Coalgebra.counit (R := R) z = 0 := by
          simpa only [RingHom.mem_ker, Bialgebra.counitAlgHom_apply] using
            hcounit (F.antitone hb hz)
        rw [hz0, mul_zero]
    intro t ht
    exact LinearMap.mem_ker.mp (hle ((F.mem_tensorProduct_ideal_iff R F).mp ht))
  let ε₂Q : ((A ⊗[R] A) ⧸ (F.tensorProduct R F).ideal 1) →ₐ[R] R :=
    Ideal.Quotient.liftₐ ((F.tensorProduct R F).ideal 1) ε₂ hε₂
  have hε₂Q_mk (t : A ⊗[R] A) :
      ε₂Q (Ideal.Quotient.mk ((F.tensorProduct R F).ideal 1) t) = ε₂ t := by
    rw [← Ideal.Quotient.mkₐ_eq_mk R, ← AlgHom.comp_apply]
    exact AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp _ ε₂ hε₂) t
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection 0 x)
  have hproj := congrArg (fun t => ε₂Q ((F.tensorProduct R F).projection 0 t)) hx
  have hlhs : ε₂Q ((F.tensorProduct R F).projection 0 (F.completedCoproduct R hcomul x)) =
      Coalgebra.counit (R := R) a := by
    rw [projection_completedCoproduct, ← ha, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk,
      hε₂Q_mk, Bialgebra.comulAlgHom_apply]
    exact lift_counit_comul (R := R) a
  have hrhs : ε₂Q ((F.tensorProduct R F).projection 0
        (F.includeLeftCompletion R F x + F.includeRightCompletion R F x)) =
      Coalgebra.counit (R := R) a + Coalgebra.counit (R := R) a := by
    rw [map_add, map_add, projection_includeLeftCompletion, projection_includeRightCompletion,
      ← ha, Ideal.quotient_map_mkₐ, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk,
      hε₂Q_mk, hε₂Q_mk]
    simp [ε₂]
  rw [hlhs, hrhs] at hproj
  rw [F.completedCounit_eq_of_projection_zero R hcounit ha]
  exact left_eq_add.mp hproj

/-- When the first filtration ideal is the kernel of the counit, every completed primitive element
lies in the first completion ideal. -/
theorem IsCompletedPrimitive.mem_completionIdeal_one
    (hker : F.ideal 1 = RingHom.ker (Bialgebra.counitAlgHom R A))
    {x : F.completion} (hx : F.IsCompletedPrimitive R hcomul x) :
    x ∈ F.completionIdeal 1 :=
  (F.mem_completionIdeal_one_iff_completedCounit_eq_zero R hker).mpr
    (hx.completedCounit_eq_zero hker.le)

end Primitive

/-- The `R`-submodule of completed primitive elements. -/
def completedPrimitiveSubmodule
    (hcomul : ∀ k,
      F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A)) :
    Submodule R F.completion where
  carrier := {x | F.IsCompletedPrimitive R hcomul x}
  zero_mem' := IsCompletedPrimitive.zero
  add_mem' hx hy := hx.add hy
  smul_mem' r _ hx := hx.smul r

/-- Membership in `completedPrimitiveSubmodule` is completed primitivity. -/
@[simp]
theorem mem_completedPrimitiveSubmodule
    (hcomul : ∀ k,
      F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    {x : F.completion} :
    x ∈ F.completedPrimitiveSubmodule R hcomul ↔ F.IsCompletedPrimitive R hcomul x :=
  Iff.rfl

/-- An element of the completion is completed group-like if it has completed counit one and its
completed coproduct is its completed tensor square. -/
structure IsCompletedGroupLike
    (hcomul : ∀ k,
      F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (hcounit : F.ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R A))
    (u : F.completion) : Prop where
  /-- The completed counit of a completed group-like element is one. -/
  counit_eq_one : F.completedCounit R hcounit u = 1
  /-- The completed coproduct of a completed group-like element is `u ⊗̂ u`. -/
  comul_eq_completedTensor_self :
    F.completedCoproduct R hcomul u = F.completedTensor R F u u

section GroupLike

variable {R F}
variable {hcomul :
  ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A)}
variable {hcounit : F.ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R A)}

/-- One is completed group-like. -/
theorem IsCompletedGroupLike.one : F.IsCompletedGroupLike R hcomul hcounit 1 where
  counit_eq_one := map_one _
  comul_eq_completedTensor_self := by simp

/-- The product of completed group-like elements is completed group-like. -/
theorem IsCompletedGroupLike.mul {u v : F.completion}
    (hu : F.IsCompletedGroupLike R hcomul hcounit u)
    (hv : F.IsCompletedGroupLike R hcomul hcounit v) :
    F.IsCompletedGroupLike R hcomul hcounit (u * v) where
  counit_eq_one := by rw [map_mul, hu.counit_eq_one, hv.counit_eq_one, mul_one]
  comul_eq_completedTensor_self := by
    rw [map_mul, hu.comul_eq_completedTensor_self, hv.comul_eq_completedTensor_self,
      ← F.completedTensor_mul R F]

/-- Every natural power of a completed group-like element is completed group-like. -/
theorem IsCompletedGroupLike.pow {u : F.completion}
    (hu : F.IsCompletedGroupLike R hcomul hcounit u) (n : ℕ) :
    F.IsCompletedGroupLike R hcomul hcounit (u ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using IsCompletedGroupLike.one
  | succ n ih => simpa only [pow_succ] using ih.mul hu

/-- The two-sided inverse of a completed group-like element is completed group-like. -/
theorem IsCompletedGroupLike.of_mul_eq_one {u v : F.completion}
    (huv : u * v = 1) (hvu : v * u = 1)
    (hu : F.IsCompletedGroupLike R hcomul hcounit u) :
    F.IsCompletedGroupLike R hcomul hcounit v where
  counit_eq_one := by
    have h := congrArg (F.completedCounit R hcounit) hvu
    rw [map_mul, map_one, hu.counit_eq_one, mul_one] at h
    exact h
  comul_eq_completedTensor_self := by
    have hmul : F.completedTensor R F u u * F.completedTensor R F v v = 1 := by
      rw [← F.completedTensor_mul R F, huv]
      simp
    have hΔ : F.completedCoproduct R hcomul v * F.completedTensor R F u u = 1 := by
      rw [← hu.comul_eq_completedTensor_self, ← map_mul, hvu, map_one]
    calc
      F.completedCoproduct R hcomul v
          = F.completedCoproduct R hcomul v *
              (F.completedTensor R F u u * F.completedTensor R F v v) := by rw [hmul, mul_one]
      _ = (F.completedCoproduct R hcomul v * F.completedTensor R F u u) *
            F.completedTensor R F v v := by rw [mul_assoc]
      _ = F.completedTensor R F v v := by rw [hΔ, one_mul]

/-- The inverse of a completed group-like unit is completed group-like. -/
theorem IsCompletedGroupLike.unitsInv {u : F.completionˣ}
    (hu : F.IsCompletedGroupLike R hcomul hcounit (u : F.completion)) :
    F.IsCompletedGroupLike R hcomul hcounit ((u⁻¹ : F.completionˣ) : F.completion) :=
  hu.of_mul_eq_one u.mul_inv u.inv_mul

/-- The canonical image of a group-like element is completed group-like. -/
theorem IsCompletedGroupLike.toCompletion {a : A} (ha : IsGroupLikeElem R a) :
    F.IsCompletedGroupLike R hcomul hcounit (F.toCompletion a) where
  counit_eq_one := by
    rw [F.completedCounit_toCompletion R hcounit a, ha.counit_eq_one]
  comul_eq_completedTensor_self := by
    rw [F.completedCoproduct_toCompletion R hcomul a, ha.comul_eq_tmul_self,
      F.completedTensor_toCompletion R F a a]

/-- When the first filtration ideal is the kernel of the counit, every completed group-like
element is congruent to one modulo the first completion ideal. -/
theorem IsCompletedGroupLike.sub_one_mem_completionIdeal_one
    (hker : F.ideal 1 = RingHom.ker (Bialgebra.counitAlgHom R A))
    {u : F.completion} (hu : F.IsCompletedGroupLike R hcomul hker.le u) :
    u - 1 ∈ F.completionIdeal 1 :=
  (F.sub_one_mem_completionIdeal_one_iff_completedCounit_eq_one R hker).mpr hu.counit_eq_one

end GroupLike

/-- The subgroup of completed group-like units in `F.completionˣ`. -/
def completedGroupLikeSubgroup
    (hcomul : ∀ k,
      F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (hcounit : F.ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R A)) :
    Subgroup F.completionˣ where
  carrier := {u | F.IsCompletedGroupLike R hcomul hcounit (u : F.completion)}
  one_mem' := IsCompletedGroupLike.one
  mul_mem' hu hv := hu.mul hv
  inv_mem' hu := hu.unitsInv

/-- Membership in `completedGroupLikeSubgroup` is being completed group-like. -/
@[simp]
theorem mem_completedGroupLikeSubgroup
    (hcomul : ∀ k,
      F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
    (hcounit : F.ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R A))
    {u : F.completionˣ} :
    u ∈ F.completedGroupLikeSubgroup R hcomul hcounit ↔
      F.IsCompletedGroupLike R hcomul hcounit (u : F.completion) :=
  Iff.rfl

end Bialgebra

section ExpLog

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Bialgebra R A] [Algebra ℚ A]
  (F : AlgFiltration A)
  (hcomul : ∀ k,
    F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))

/-- The completed coproduct commutes with the completed exponential. -/
@[simp]
theorem completedCoproduct_completedExp (x : F.completionIdeal 1) :
    F.completedCoproduct R hcomul (F.completedExp x) =
      (F.tensorProduct R F).completedExp
        ⟨F.completedCoproduct R hcomul x,
          F.completedCoproduct_mem_completionIdeal R hcomul x.property⟩ := by
  simpa only [completedCoproduct, ← AlgHom.coe_toRingHom, coe_mapCompletionₐ] using
    F.mapCompletion_completedExp (F.tensorProduct R F)
      (Bialgebra.comulAlgHom R A : A →+* A ⊗[R] A) id monotone_id
      (fun k => hcomul (k + 1)) (hcomul 1) x

private theorem includeLeftCompletion_completedExp (x : F.completionIdeal 1) :
    F.includeLeftCompletion R F (F.completedExp x) =
      (F.tensorProduct R F).completedExp
        ⟨F.includeLeftCompletion R F x,
          F.includeLeftCompletion_mem_completionIdeal R F x.property⟩ := by
  apply (F.tensorProduct R F).completion_ext
  intro k
  rw [projection_includeLeftCompletion, projection_completedExp, projection_completedExp,
    projection_includeLeftCompletion]
  exact (F.isNilpotent_projection x.property k).map_exp _

private theorem includeRightCompletion_completedExp (x : F.completionIdeal 1) :
    F.includeRightCompletion R F (F.completedExp x) =
      (F.tensorProduct R F).completedExp
        ⟨F.includeRightCompletion R F x,
          F.includeRightCompletion_mem_completionIdeal R F x.property⟩ := by
  apply (F.tensorProduct R F).completion_ext
  intro k
  rw [projection_includeRightCompletion, projection_completedExp, projection_completedExp,
    projection_includeRightCompletion]
  exact (F.isNilpotent_projection x.property k).map_exp _

/-- The completed exponential of a completed primitive in the first completion ideal is completed
group-like. -/
theorem isCompletedGroupLike_completedExp
    (hcounit : F.ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R A))
    (x : F.completionIdeal 1) (hx : F.IsCompletedPrimitive R hcomul (x : F.completion)) :
    F.IsCompletedGroupLike R hcomul hcounit (F.completedExp x) := by
  refine ⟨?_, ?_⟩
  · have hx₀ : F.projection 0 (x : F.completion) = 0 := by
      simpa only [completionIdeal_succ, RingHom.mem_ker] using x.property
    have hproj : F.projection 0 (F.completedExp x) = 1 := by
      rw [F.projection_completedExp, hx₀, IsNilpotent.exp_zero]
    rw [completedCounit, AlgHom.comp_apply, projectionₐ_apply, hproj, map_one]
  · let xL : (F.tensorProduct R F).completionIdeal 1 :=
      ⟨F.includeLeftCompletion R F x,
        F.includeLeftCompletion_mem_completionIdeal R F x.property⟩
    let xR : (F.tensorProduct R F).completionIdeal 1 :=
      ⟨F.includeRightCompletion R F x,
        F.includeRightCompletion_mem_completionIdeal R F x.property⟩
    have hΔexp : F.completedCoproduct R hcomul (F.completedExp x) =
        (F.tensorProduct R F).completedExp (xL + xR) := by
      rw [completedCoproduct_completedExp R F hcomul x]
      congr 1
      exact Subtype.ext hx
    rw [hΔexp, (F.tensorProduct R F).completedExp_add xL xR
      (F.commute_includeLeftCompletion_includeRightCompletion R F x x),
      ← includeLeftCompletion_completedExp R F x, ← includeRightCompletion_completedExp R F x,
      F.completedTensor_apply R F]

/-- The completed logarithm of an element congruent to one whose completed coproduct is its
completed tensor square is completed primitive. -/
theorem isCompletedPrimitive_completedLog
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1})
    (hu : F.completedCoproduct R hcomul (u : F.completion) =
      F.completedTensor R F (u : F.completion) (u : F.completion)) :
    F.IsCompletedPrimitive R hcomul (F.completedLog u) := by
  let x : F.completionIdeal 1 := ⟨F.completedLog u, F.completedLog_mem u⟩
  let y₁ : (F.tensorProduct R F).completionIdeal 1 :=
    ⟨F.completedCoproduct R hcomul (x : F.completion),
      F.completedCoproduct_mem_completionIdeal R hcomul x.property⟩
  let xL : (F.tensorProduct R F).completionIdeal 1 :=
    ⟨F.includeLeftCompletion R F x,
      F.includeLeftCompletion_mem_completionIdeal R F x.property⟩
  let xR : (F.tensorProduct R F).completionIdeal 1 :=
    ⟨F.includeRightCompletion R F x,
      F.includeRightCompletion_mem_completionIdeal R F x.property⟩
  have h1 : (F.tensorProduct R F).completedExp y₁ =
      F.completedCoproduct R hcomul (u : F.completion) := by
    rw [← completedCoproduct_completedExp R F hcomul x, F.completedExp_completedLog u]
  have h2 : (F.tensorProduct R F).completedExp (xL + xR) =
      F.completedTensor R F (u : F.completion) (u : F.completion) := by
    rw [(F.tensorProduct R F).completedExp_add xL xR
      (F.commute_includeLeftCompletion_includeRightCompletion R F x x),
      ← includeLeftCompletion_completedExp R F x, ← includeRightCompletion_completedExp R F x,
      F.completedExp_completedLog u, F.completedTensor_apply R F]
  have heq : (F.tensorProduct R F).completedExp y₁ =
      (F.tensorProduct R F).completedExp (xL + xR) :=
    h1.trans (hu.trans h2.symm)
  have hlog := congrArg (fun v : {v : (F.tensorProduct R F).completion //
      v - 1 ∈ (F.tensorProduct R F).completionIdeal 1} =>
    (F.tensorProduct R F).completedLog v)
    (Subtype.ext heq :
      (⟨(F.tensorProduct R F).completedExp y₁,
          (F.tensorProduct R F).completedExp_sub_one_mem y₁⟩ :
        {v // v - 1 ∈ (F.tensorProduct R F).completionIdeal 1}) =
      ⟨(F.tensorProduct R F).completedExp (xL + xR),
        (F.tensorProduct R F).completedExp_sub_one_mem (xL + xR)⟩)
  rw [(F.tensorProduct R F).completedLog_completedExp,
    (F.tensorProduct R F).completedLog_completedExp] at hlog
  exact hlog

/-- Completed exponential and logarithm identify completed primitives in the first completion
ideal with completed group-like elements congruent to one modulo the first completion ideal. -/
noncomputable def completedPrimitiveEquivGroupLike
    (hcounit : F.ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R A)) :
    {x : F.completion // x ∈ F.completionIdeal 1 ∧ F.IsCompletedPrimitive R hcomul x} ≃
      {u : F.completion // u - 1 ∈ F.completionIdeal 1 ∧
        F.IsCompletedGroupLike R hcomul hcounit u} where
  toFun x :=
    ⟨F.completedExp ⟨x.1, x.2.1⟩, F.completedExp_sub_one_mem ⟨x.1, x.2.1⟩,
      F.isCompletedGroupLike_completedExp R hcomul hcounit ⟨x.1, x.2.1⟩ x.2.2⟩
  invFun u :=
    ⟨F.completedLog ⟨u.1, u.2.1⟩, F.completedLog_mem ⟨u.1, u.2.1⟩,
      F.isCompletedPrimitive_completedLog R hcomul ⟨u.1, u.2.1⟩
        u.2.2.comul_eq_completedTensor_self⟩
  left_inv x := Subtype.ext (F.completedLog_completedExp ⟨x.1, x.2.1⟩)
  right_inv u := Subtype.ext (F.completedExp_completedLog ⟨u.1, u.2.1⟩)

/-- The forward map of `completedPrimitiveEquivGroupLike` is the completed exponential. -/
@[simp]
theorem coe_completedPrimitiveEquivGroupLike
    (hcounit : F.ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R A))
    (x : {x : F.completion // x ∈ F.completionIdeal 1 ∧ F.IsCompletedPrimitive R hcomul x}) :
    (F.completedPrimitiveEquivGroupLike R hcomul hcounit x : F.completion) =
      F.completedExp ⟨x.1, x.2.1⟩ := (rfl)

/-- The inverse map of `completedPrimitiveEquivGroupLike` is the completed logarithm. -/
@[simp]
theorem coe_completedPrimitiveEquivGroupLike_symm
    (hcounit : F.ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R A))
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1 ∧
      F.IsCompletedGroupLike R hcomul hcounit u}) :
    ((F.completedPrimitiveEquivGroupLike R hcomul hcounit).symm u : F.completion) =
      F.completedLog ⟨u.1, u.2.1⟩ := (rfl)

/-- When `F.ideal 1` is the kernel of the counit, every completed group-like element is a unit. -/
theorem isUnit_of_isCompletedGroupLike
    (hker : F.ideal 1 = RingHom.ker (Bialgebra.counitAlgHom R A))
    {u : F.completion} (hu : F.IsCompletedGroupLike R hcomul hker.le u) :
    IsUnit u := by
  have hu₁ := hu.sub_one_mem_completionIdeal_one hker
  let x : F.completionIdeal 1 := ⟨F.completedLog ⟨u, hu₁⟩, F.completedLog_mem ⟨u, hu₁⟩⟩
  have h : F.completedExp x = u := F.completedExp_completedLog ⟨u, hu₁⟩
  exact h ▸ F.isUnit_completedExp x

/-- When `F.ideal 1` is the kernel of the counit, completed exponential and logarithm identify
the completed primitive submodule with the completed group-like subgroup. -/
noncomputable def completedPrimitiveEquivGroupLikeOfKerEq
    (hker : F.ideal 1 = RingHom.ker (Bialgebra.counitAlgHom R A)) :
    F.completedPrimitiveSubmodule R hcomul ≃ F.completedGroupLikeSubgroup R hcomul hker.le where
  toFun x :=
    let hx : F.IsCompletedPrimitive R hcomul x.1 := x.2
    let x₁ : F.completionIdeal 1 := ⟨x.1, hx.mem_completionIdeal_one hker⟩
    ⟨(F.isUnit_completedExp x₁).unit,
      by
        simpa only [mem_completedGroupLikeSubgroup, IsUnit.unit_spec] using
          F.isCompletedGroupLike_completedExp R hcomul hker.le x₁ hx⟩
  invFun u :=
    let hu : F.IsCompletedGroupLike R hcomul hker.le (u.1 : F.completion) := u.2
    let u₁ : {v : F.completion // v - 1 ∈ F.completionIdeal 1} :=
      ⟨(u.1 : F.completion), hu.sub_one_mem_completionIdeal_one hker⟩
    ⟨F.completedLog u₁,
      F.isCompletedPrimitive_completedLog R hcomul u₁ hu.comul_eq_completedTensor_self⟩
  left_inv x := Subtype.ext (by
    have hx : F.IsCompletedPrimitive R hcomul x.1 := x.2
    simpa only [IsUnit.unit_spec] using
      F.completedLog_completedExp ⟨x.1, hx.mem_completionIdeal_one hker⟩)
  right_inv u := Subtype.ext (Units.ext (by
    have hu : F.IsCompletedGroupLike R hcomul hker.le (u.1 : F.completion) := u.2
    simpa only [IsUnit.unit_spec] using
      F.completedExp_completedLog
        ⟨(u.1 : F.completion), hu.sub_one_mem_completionIdeal_one hker⟩))

/-- The forward map of `completedPrimitiveEquivGroupLikeOfKerEq` evaluates to the completed
exponential. -/
@[simp]
theorem coe_completedPrimitiveEquivGroupLikeOfKerEq
    (hker : F.ideal 1 = RingHom.ker (Bialgebra.counitAlgHom R A))
    (x : F.completedPrimitiveSubmodule R hcomul) :
    ((F.completedPrimitiveEquivGroupLikeOfKerEq R hcomul hker x : F.completionˣ) : F.completion) =
      F.completedExp
        ⟨x.1, ((F.mem_completedPrimitiveSubmodule R hcomul).mp x.2).mem_completionIdeal_one
          hker⟩ := by
  simp [completedPrimitiveEquivGroupLikeOfKerEq]

/-- The inverse map of `completedPrimitiveEquivGroupLikeOfKerEq` evaluates to the completed
logarithm. -/
@[simp]
theorem coe_completedPrimitiveEquivGroupLikeOfKerEq_symm
    (hker : F.ideal 1 = RingHom.ker (Bialgebra.counitAlgHom R A))
    (u : F.completedGroupLikeSubgroup R hcomul hker.le) :
    ((F.completedPrimitiveEquivGroupLikeOfKerEq R hcomul hker).symm u : F.completion) =
      F.completedLog
        ⟨(u.1 : F.completion),
          ((F.mem_completedGroupLikeSubgroup R hcomul hker.le).mp
            u.2).sub_one_mem_completionIdeal_one hker⟩ := (rfl)

end ExpLog

end TauCeti.AlgFiltration
