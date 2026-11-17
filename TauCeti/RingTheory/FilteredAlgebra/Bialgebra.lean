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
# Completed counit, comultiplication, and primitive-exponential correspondence

Let `A` be a bialgebra over a commutative ring `R` equipped with a decreasing multiplicative
two-sided ideal filtration `F : AlgFiltration A`. Whenever comultiplication preserves total
filtration degree and the counit vanishes on the first filtration ideal, the bialgebra operations
extend to `F.completion`:

* `TauCeti.AlgFiltration.completedComul`: completed comultiplication
  `F.completion →ₐ[R] (F.tensorProduct R F).completion`.
* `TauCeti.AlgFiltration.completedCounit`: completed counit `F.completion →ₐ[R] R`.

Using `TauCeti.AlgFiltration.completedTensor`, this file defines completed group-like elements
(`TauCeti.AlgFiltration.IsCompletedGroupLike`) and completed primitive elements
(`TauCeti.AlgFiltration.IsCompletedPrimitive`), proving that `Δ̂ x = x ⊗̂ 1 + 1 ⊗̂ x` already forces
`ε̂ x = 0` over any commutative ring. When `A` is also a rational algebra whose rational and
`R`-scalar actions commute, `completedExp` and `completedLog` commute with `completedComul` and
exchange completed primitive elements in the first completion ideal with completed group-like
elements congruent to `1` (`TauCeti.AlgFiltration.completedExpPrimitiveEquiv`), showing that
`log (exp x * exp y)` is completed primitive whenever `x` and `y` are
(`TauCeti.AlgFiltration.isCompletedPrimitive_completedLog_completedExp_mul_completedExp`).

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter II, §6.
* D. Quillen, *Rational homotopy theory*, Ann. of Math. (2) **90** (1969), Appendix A.
* J.-P. Serre, *Lie Algebras and Lie Groups*, Part I, Chapter IV.
-/

public section

open scoped TensorProduct

namespace TauCeti.AlgFiltration

section Comul

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Bialgebra R A] (F : AlgFiltration A)
  (hΔ : ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))

/-- The completed comultiplication `F.completion →ₐ[R] (F.tensorProduct R F).completion` induced by
a filtration-preserving bialgebra comultiplication. -/
noncomputable def completedComul : F.completion →ₐ[R] (F.tensorProduct R F).completion :=
  F.mapCompletionₐ (F.tensorProduct R F) (Bialgebra.comulAlgHom R A) id monotone_id
    fun k => hΔ (k + 1)

/-- Forgetting scalars on `completedComul` gives the ring completion map of comultiplication. -/
@[simp]
theorem coe_completedComul :
    (F.completedComul R hΔ : F.completion →+* (F.tensorProduct R F).completion) =
      F.mapCompletion (F.tensorProduct R F) (Bialgebra.comulAlgHom R A : A →+* A ⊗[R] A)
        id monotone_id (fun k => hΔ (k + 1)) :=
  F.coe_mapCompletionₐ (F.tensorProduct R F) (Bialgebra.comulAlgHom R A) id monotone_id _

/-- Completing a canonical element commutes with comultiplication. -/
@[simp]
theorem completedComul_toCompletion (a : A) :
    F.completedComul R hΔ (F.toCompletion a) =
      (F.tensorProduct R F).toCompletion (Coalgebra.comul (R := R) a) :=
  F.mapCompletionₐ_toCompletion _ _ _ monotone_id _ a

/-- The order-`k` component of `completedComul` is the quotient map induced by comultiplication. -/
@[simp]
theorem projection_completedComul (k : ℕ) (x : F.completion) :
    (F.tensorProduct R F).projection k (F.completedComul R hΔ x) =
      Ideal.quotientMapₐ ((F.tensorProduct R F).ideal (k + 1)) (Bialgebra.comulAlgHom R A)
        (hΔ (k + 1)) (F.projection k x) :=
  F.projection_mapCompletionₐ _ _ _ monotone_id _ k x

/-- Completed comultiplication preserves every completion filtration order. -/
theorem completedComul_mem_completionIdeal {k : ℕ} {x : F.completion}
    (hx : x ∈ F.completionIdeal k) :
    F.completedComul R hΔ x ∈ (F.tensorProduct R F).completionIdeal k := by
  rcases k with _ | k
  · simp
  · exact F.mapCompletionₐ_mem_completionIdeal _ _ id monotone_id _ k hx

end Comul

section Counit

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Bialgebra R A] (F : AlgFiltration A)
  (hε : F.ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R A))

/-- The completed counit `F.completion →ₐ[R] R`, factoring the bialgebra counit through the
order-zero projection `F.projectionₐ 0 : F.completion →ₐ[R] A ⧸ F.ideal 1`. -/
noncomputable def completedCounit : F.completion →ₐ[R] R :=
  (Ideal.Quotient.liftₐ (F.ideal 1) (Bialgebra.counitAlgHom R A)
    fun _ ha => RingHom.mem_ker.mp (hε ha)).comp (F.projectionₐ (R := R) 0)

/-- The completed counit of a representative of the order-zero projection is its ordinary counit. -/
theorem completedCounit_eq_of_mk_eq_projection_zero {x : F.completion} {a : A}
    (ha : Ideal.Quotient.mk (F.ideal 1) a = F.projection 0 x) :
    F.completedCounit R hε x = Coalgebra.counit (R := R) a := by
  rw [completedCounit, AlgHom.comp_apply, projectionₐ_apply, ← ha]; rfl

/-- Completing a canonical element preserves its counit. -/
@[simp]
theorem completedCounit_toCompletion (a : A) :
    F.completedCounit R hε (F.toCompletion a) = Coalgebra.counit (R := R) a :=
  F.completedCounit_eq_of_mk_eq_projection_zero R hε (F.projection_toCompletion 0 a).symm

/-- The first completion ideal lies in the kernel of the completed counit. -/
theorem completionIdeal_one_le_ker_completedCounit :
    F.completionIdeal 1 ≤ RingHom.ker (F.completedCounit R hε) := fun x hx => by
  rw [completionIdeal_succ, RingHom.mem_ker] at hx
  rw [RingHom.mem_ker, completedCounit, AlgHom.comp_apply, projectionₐ_apply, hx, map_zero]

/-- Elements of the first completion ideal have completed counit zero. -/
theorem completedCounit_eq_zero_of_mem {x : F.completion} (hx : x ∈ F.completionIdeal 1) :
    F.completedCounit R hε x = 0 :=
  RingHom.mem_ker.mp (F.completionIdeal_one_le_ker_completedCounit R hε hx)

/-- Elements congruent to `1` modulo the first completion ideal have completed counit `1`. -/
theorem completedCounit_eq_one_of_sub_one_mem {u : F.completion}
    (hu : u - 1 ∈ F.completionIdeal 1) : F.completedCounit R hε u = 1 :=
  sub_eq_zero.mp <| by simpa using F.completedCounit_eq_zero_of_mem R hε hu

/-- When the first filtration ideal equals the augmentation kernel, the kernel of `completedCounit`
is exactly the first completion ideal. -/
theorem ker_completedCounit_eq_completionIdeal_one
    (hε' : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) :
    RingHom.ker (F.completedCounit R hε) = F.completionIdeal 1 := by
  refine le_antisymm (fun x hx => ?_) (F.completionIdeal_one_le_ker_completedCounit R hε)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection 0 x)
  rw [completionIdeal_succ, RingHom.mem_ker, ← ha, Ideal.Quotient.eq_zero_iff_mem]
  exact hε' <| RingHom.mem_ker.mpr <| by
    simpa [← F.completedCounit_eq_of_mk_eq_projection_zero R hε ha] using RingHom.mem_ker.mp hx

/-- When the first filtration ideal contains the counit kernel, membership in the first completion
ideal is equivalent to vanishing of the completed counit. -/
theorem mem_completionIdeal_one_iff_completedCounit_eq_zero
    (hε' : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) {x : F.completion} :
    x ∈ F.completionIdeal 1 ↔ F.completedCounit R hε x = 0 := by
  rw [← F.ker_completedCounit_eq_completionIdeal_one R hε hε', RingHom.mem_ker]

/-- When the first filtration ideal contains the counit kernel, congruence to `1` modulo the first
completion ideal is equivalent to having completed counit `1`. -/
theorem sub_one_mem_completionIdeal_one_iff_completedCounit_eq_one
    (hε' : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) {u : F.completion} :
    u - 1 ∈ F.completionIdeal 1 ↔ F.completedCounit R hε u = 1 := by
  rw [F.mem_completionIdeal_one_iff_completedCounit_eq_zero R hε hε', map_sub, map_one, sub_eq_zero]

end Counit

section GroupLikeAndPrimitive

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Bialgebra R A] (F : AlgFiltration A)
  (hΔ : ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
  (hε : F.ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R A))

private noncomputable def counitMulAlgHom : A ⊗[R] A →ₐ[R] R :=
  (Algebra.TensorProduct.lid R R).toAlgHom.comp
    (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R A) (Bialgebra.counitAlgHom R A))

private theorem counitMulAlgHom_tmul (a b : A) :
    counitMulAlgHom R (a ⊗ₜ[R] b) = Coalgebra.counit (R := R) a * Coalgebra.counit (R := R) b := by
  simp [counitMulAlgHom]

private theorem counitMulAlgHom_comul (a : A) :
    counitMulAlgHom R (Coalgebra.comul (R := R) a) = Coalgebra.counit (R := R) a := by
  have h (t : A ⊗[R] A) : counitMulAlgHom R t =
      Coalgebra.counit (TensorProduct.lid R A (Coalgebra.counit.rTensor A t)) := by
    induction t using TensorProduct.inductionOn with
    | tmul u v => simp [counitMulAlgHom]
    | add x y hx hy => simp [map_add, hx, hy]
  rw [h, Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]

include hε in
private theorem tensorProduct_ideal_one_le_ker_counitMulAlgHom :
    (F.tensorProduct R F).ideal 1 ≤ RingHom.ker (counitMulAlgHom (R := R) (A := A)) := by
  have bound : tensorFiltrationTail (fun n => (F.ideal n).restrictScalars R)
      (fun n => (F.ideal n).restrictScalars R) 1 ≤
      (RingHom.ker (counitMulAlgHom (R := R) (A := A))).restrictScalars R := by
    refine (tensorFiltrationTail_le_iff _ _).mpr fun i j hij a ha b hb => ?_
    simp only [Submodule.restrictScalars_mem, RingHom.mem_ker, counitMulAlgHom_tmul]
    rcases (by omega : 1 ≤ i ∨ 1 ≤ j) with hi | hj
    · have ha0 : Coalgebra.counit (R := R) a = 0 := by
        simpa using RingHom.mem_ker.mp (hε (F.antitone hi ha))
      simp [ha0]
    · have hb0 : Coalgebra.counit (R := R) b = 0 := by
        simpa using RingHom.mem_ker.mp (hε (F.antitone hj hb))
      simp [hb0]
  exact fun t ht => bound ((F.mem_tensorProduct_ideal_iff R F).mp ht)

private noncomputable def completedCounitMul :
    (F.tensorProduct R F).completion →ₐ[R] R :=
  (Ideal.Quotient.liftₐ _ (counitMulAlgHom (R := R))
    fun _ ht => RingHom.mem_ker.mp (F.tensorProduct_ideal_one_le_ker_counitMulAlgHom R hε ht)).comp
    ((F.tensorProduct R F).projectionₐ (R := R) 0)

private theorem completedCounitMul_completedComul (x : F.completion) :
    F.completedCounitMul R hε (F.completedComul R hΔ x) = F.completedCounit R hε x := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection 0 x)
  rw [F.completedCounit_eq_of_mk_eq_projection_zero R hε ha, ← counitMulAlgHom_comul R a]
  simp [completedCounitMul, ← ha]
  rfl

private theorem completedCounitMul_completedTensor (x y : F.completion) :
    F.completedCounitMul R hε (F.completedTensor R F x y) =
      F.completedCounit R hε x * F.completedCounit R hε y := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection 0 x)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (F.projection 0 y)
  rw [F.completedCounit_eq_of_mk_eq_projection_zero R hε ha,
    F.completedCounit_eq_of_mk_eq_projection_zero R hε hb, ← counitMulAlgHom_tmul R a b]
  simp [completedCounitMul, F.projection_completedTensor_of_representatives R F 0 x y a b ha hb]
  rfl

/-- The completed primitive comultiplication identity already forces the completed counit to
vanish, over any commutative base ring. -/
theorem completedCounit_eq_zero_of_completedComul_eq {x : F.completion}
    (hx : F.completedComul R hΔ x = F.completedTensor R F x 1 + F.completedTensor R F 1 x) :
    F.completedCounit R hε x = 0 := by
  have h := congrArg (F.completedCounitMul R hε) hx
  simp only [F.completedCounitMul_completedComul R hΔ hε, map_add,
    F.completedCounitMul_completedTensor R hε, map_one, mul_one, one_mul] at h
  exact left_eq_add.mp h

/-- An element `u` of a completed filtered bialgebra is group-like when `ε̂ u = 1` and
`Δ̂ u = u ⊗̂ u`. -/
@[mk_iff]
structure IsCompletedGroupLike (u : F.completion) : Prop where
  /-- A completed group-like element has completed counit `1`. -/
  completedCounit_eq_one : F.completedCounit R hε u = 1
  /-- A completed group-like element has completed comultiplication `u ⊗̂ u`. -/
  completedComul_eq : F.completedComul R hΔ u = F.completedTensor R F u u

attribute [simp] IsCompletedGroupLike.completedCounit_eq_one IsCompletedGroupLike.completedComul_eq

namespace IsCompletedGroupLike

variable {R F hΔ hε}

/-- `1` is group-like in the completion. -/
@[simp]
theorem one : F.IsCompletedGroupLike R hΔ hε 1 := ⟨map_one _, by simp⟩

/-- Completed group-like elements are closed under multiplication. -/
theorem mul {u v : F.completion} (hu : F.IsCompletedGroupLike R hΔ hε u)
    (hv : F.IsCompletedGroupLike R hΔ hε v) : F.IsCompletedGroupLike R hΔ hε (u * v) where
  completedCounit_eq_one := by simp [hu.completedCounit_eq_one, hv.completedCounit_eq_one]
  completedComul_eq := by
    rw [map_mul, hu.completedComul_eq, hv.completedComul_eq, F.completedTensor_mul R F]

/-- Completed group-like elements are closed under natural powers. -/
theorem pow {u : F.completion} (hu : F.IsCompletedGroupLike R hΔ hε u) (n : ℕ) :
    F.IsCompletedGroupLike R hΔ hε (u ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => simpa [pow_succ] using ih.mul hu

/-- A two-sided multiplicative inverse of a completed group-like element is also completed
group-like. -/
theorem of_mul_eq_one {u v : F.completion} (huv : u * v = 1) (hvu : v * u = 1)
    (hu : F.IsCompletedGroupLike R hΔ hε u) : F.IsCompletedGroupLike R hΔ hε v where
  completedCounit_eq_one := left_inv_eq_right_inv (a := F.completedCounit R hε u)
    (by rw [← map_mul, hvu, map_one]) (by rw [hu.completedCounit_eq_one, mul_one])
  completedComul_eq := left_inv_eq_right_inv (a := F.completedComul R hΔ u)
    (by rw [← map_mul, hvu, map_one])
    (by rw [hu.completedComul_eq, ← F.completedTensor_mul R F, huv,
      F.completedTensor_one_left R F, map_one])

/-- When the first filtration ideal contains the counit kernel, every completed group-like element
is congruent to `1` modulo the first completion ideal. -/
theorem sub_one_mem {u : F.completion} (hε' : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1)
    (hu : F.IsCompletedGroupLike R hΔ hε u) : u - 1 ∈ F.completionIdeal 1 :=
  (F.sub_one_mem_completionIdeal_one_iff_completedCounit_eq_one R hε hε').mpr
    hu.completedCounit_eq_one

end IsCompletedGroupLike

/-- The completed group-like elements form a submonoid of the completion. -/
def completedGroupLikeSubmonoid : Submonoid F.completion where
  carrier := {u | F.IsCompletedGroupLike R hΔ hε u}
  one_mem' := .one
  mul_mem' := .mul

@[simp]
theorem mem_completedGroupLikeSubmonoid {u : F.completion} :
    u ∈ F.completedGroupLikeSubmonoid R hΔ hε ↔ F.IsCompletedGroupLike R hΔ hε u := Iff.rfl

/-- An ordinary group-like element maps to a completed group-like element. -/
theorem isCompletedGroupLike_toCompletion {a : A} (ha : IsGroupLikeElem R a) :
    F.IsCompletedGroupLike R hΔ hε (F.toCompletion a) :=
  ⟨by simp [ha.counit_eq_one], by simp [ha.comul_eq_tmul_self]⟩

/-- An element `x` of a completed filtered bialgebra is primitive when `ε̂ x = 0` and
`Δ̂ x = x ⊗̂ 1 + 1 ⊗̂ x`. -/
@[mk_iff]
structure IsCompletedPrimitive (x : F.completion) : Prop where
  /-- A completed primitive element has completed counit `0`. -/
  completedCounit_eq_zero : F.completedCounit R hε x = 0
  /-- A completed primitive element has completed comultiplication `x ⊗̂ 1 + 1 ⊗̂ x`. -/
  completedComul_eq :
    F.completedComul R hΔ x = F.completedTensor R F x 1 + F.completedTensor R F 1 x

attribute [simp] IsCompletedPrimitive.completedCounit_eq_zero IsCompletedPrimitive.completedComul_eq

/-- Because the counit condition follows automatically from the comultiplication equation, an
element is completed primitive if and only if `Δ̂ x = x ⊗̂ 1 + 1 ⊗̂ x`. -/
theorem isCompletedPrimitive_iff_completedComul_eq {x : F.completion} :
    F.IsCompletedPrimitive R hΔ hε x ↔
      F.completedComul R hΔ x = F.completedTensor R F x 1 + F.completedTensor R F 1 x :=
  ⟨IsCompletedPrimitive.completedComul_eq,
    fun hx => ⟨F.completedCounit_eq_zero_of_completedComul_eq R hΔ hε hx, hx⟩⟩

namespace IsCompletedPrimitive

variable {R F hΔ hε}

/-- `0` is completed primitive. -/
@[simp]
theorem zero : F.IsCompletedPrimitive R hΔ hε 0 := ⟨map_zero _, by simp⟩

/-- Completed primitive elements are closed under addition. -/
theorem add {x y : F.completion} (hx : F.IsCompletedPrimitive R hΔ hε x)
    (hy : F.IsCompletedPrimitive R hΔ hε y) : F.IsCompletedPrimitive R hΔ hε (x + y) :=
  (F.isCompletedPrimitive_iff_completedComul_eq R hΔ hε).mpr <| by
    simp only [map_add, hx.completedComul_eq, hy.completedComul_eq, LinearMap.add_apply]; abel

/-- Completed primitive elements are closed under negation. -/
theorem neg {x : F.completion} (hx : F.IsCompletedPrimitive R hΔ hε x) :
    F.IsCompletedPrimitive R hΔ hε (-x) :=
  (F.isCompletedPrimitive_iff_completedComul_eq R hΔ hε).mpr <| by
    simp only [map_neg, hx.completedComul_eq, LinearMap.neg_apply]; abel

/-- Completed primitive elements are closed under subtraction. -/
theorem sub {x y : F.completion} (hx : F.IsCompletedPrimitive R hΔ hε x)
    (hy : F.IsCompletedPrimitive R hΔ hε y) : F.IsCompletedPrimitive R hΔ hε (x - y) :=
  sub_eq_add_neg x y ▸ hx.add hy.neg

/-- Completed primitive elements are closed under `R`-scalar multiplication. -/
theorem smul {x : F.completion} (hx : F.IsCompletedPrimitive R hΔ hε x) (r : R) :
    F.IsCompletedPrimitive R hΔ hε (r • x) :=
  (F.isCompletedPrimitive_iff_completedComul_eq R hΔ hε).mpr <| by
    simp [hx.completedComul_eq, smul_add]

/-- Completed primitive elements are closed under the associative commutator `x * y - y * x`. -/
theorem commutator {x y : F.completion} (hx : F.IsCompletedPrimitive R hΔ hε x)
    (hy : F.IsCompletedPrimitive R hΔ hε y) :
    F.IsCompletedPrimitive R hΔ hε (x * y - y * x) :=
  (F.isCompletedPrimitive_iff_completedComul_eq R hΔ hε).mpr <| by
    rw [map_sub, map_mul, map_mul, hx.completedComul_eq, hy.completedComul_eq]
    simp only [completedTensor_one_right, completedTensor_one_left]
    simp only [add_mul, mul_add, map_sub, map_mul,
      (F.commute_includeLeftCompletion_includeRightCompletion R F x y).eq,
      (F.commute_includeLeftCompletion_includeRightCompletion R F y x).eq]
    abel

/-- When the first filtration ideal contains the counit kernel, every completed primitive element
lies in the first completion ideal. -/
theorem mem_completionIdeal_one {x : F.completion}
    (hε' : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1)
    (hx : F.IsCompletedPrimitive R hΔ hε x) : x ∈ F.completionIdeal 1 :=
  (F.mem_completionIdeal_one_iff_completedCounit_eq_zero R hε hε').mpr hx.completedCounit_eq_zero

end IsCompletedPrimitive

/-- The `R`-submodule of completed primitive elements. -/
def completedPrimitiveSubmodule : Submodule R F.completion where
  carrier := {x | F.IsCompletedPrimitive R hΔ hε x}
  zero_mem' := .zero
  add_mem' := .add
  smul_mem' r _ hx := hx.smul r

@[simp]
theorem mem_completedPrimitiveSubmodule {x : F.completion} :
    x ∈ F.completedPrimitiveSubmodule R hΔ hε ↔ F.IsCompletedPrimitive R hΔ hε x := Iff.rfl

/-- An ordinary primitive element maps to a completed primitive element. -/
theorem isCompletedPrimitive_toCompletion {a : A} (ha : Bialgebra.IsPrimitiveElem R a) :
    F.IsCompletedPrimitive R hΔ hε (F.toCompletion a) :=
  (F.isCompletedPrimitive_iff_completedComul_eq R hΔ hε).mpr <| by
    rw [completedComul_toCompletion, ha.comul_eq_tmul_add_tmul, map_add,
      ← F.completedTensor_toCompletion R F, ← F.completedTensor_toCompletion R F, map_one, add_comm]

/-- An element of a filtered bialgebra completion that can be approximated modulo every
`completionIdeal (k + 1)` by completed primitive elements is itself completed primitive. -/
theorem isCompletedPrimitive_of_forall_sub_mem {u : F.completion}
    (hu : ∀ k, ∃ v : F.completion, F.IsCompletedPrimitive R hΔ hε v ∧
      u - v ∈ F.completionIdeal (k + 1)) :
    F.IsCompletedPrimitive R hΔ hε u := by
  refine (F.isCompletedPrimitive_iff_completedComul_eq R hΔ hε).mpr <|
    (F.tensorProduct R F).completion_ext fun k => ?_
  obtain ⟨v, hv, huv⟩ := hu k
  have hc : (F.tensorProduct R F).projection k (F.completedComul R hΔ u) =
      (F.tensorProduct R F).projection k (F.completedComul R hΔ v) :=
    (F.tensorProduct R F).projection_eq_of_sub_mem_completionIdeal_succ
      (by rw [← map_sub]; exact F.completedComul_mem_completionIdeal R hΔ huv)
  have hl : (F.tensorProduct R F).projection k (F.completedTensor R F u 1) =
      (F.tensorProduct R F).projection k (F.completedTensor R F v 1) :=
    (F.tensorProduct R F).projection_eq_of_sub_mem_completionIdeal_succ (by
      rw [completedTensor_one_right, completedTensor_one_right, ← map_sub]
      exact F.includeLeftCompletion_mem_completionIdeal R F huv)
  have hr : (F.tensorProduct R F).projection k (F.completedTensor R F 1 u) =
      (F.tensorProduct R F).projection k (F.completedTensor R F 1 v) :=
    (F.tensorProduct R F).projection_eq_of_sub_mem_completionIdeal_succ (by
      rw [completedTensor_one_left, completedTensor_one_left, ← map_sub]
      exact F.includeRightCompletion_mem_completionIdeal R F huv)
  rw [hc, hv.completedComul_eq, map_add, map_add, hl, hr]

/-- If a completed primitive element `u` agrees with `F.toCompletion b` modulo
`completionIdeal (k + 1)`, then `b` is primitive modulo `(F.tensorProduct R F).ideal (k + 1)`. -/
theorem comul_sub_mem_of_isCompletedPrimitive_of_sub_mem
    {u : F.completion} (hu : F.IsCompletedPrimitive R hΔ hε u) {k : ℕ} {b : A}
    (hbu : u - F.toCompletion b ∈ F.completionIdeal (k + 1)) :
    Coalgebra.comul (R := R) b - (b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) ∈
      (F.tensorProduct R F).ideal (k + 1) := by
  have hc : (F.tensorProduct R F).projection k (F.completedComul R hΔ u) =
      Ideal.Quotient.mk ((F.tensorProduct R F).ideal (k + 1)) (Coalgebra.comul (R := R) b) := by
    rw [← (F.tensorProduct R F).projection_toCompletion k (Coalgebra.comul (R := R) b),
      ← F.completedComul_toCompletion R hΔ b]
    exact (F.tensorProduct R F).projection_eq_of_sub_mem_completionIdeal_succ
      (by simpa only [← map_sub] using F.completedComul_mem_completionIdeal R hΔ hbu)
  have hl : (F.tensorProduct R F).projection k (F.completedTensor R F u 1) =
      Ideal.Quotient.mk ((F.tensorProduct R F).ideal (k + 1)) (b ⊗ₜ[R] 1) := by
    rw [← (F.tensorProduct R F).projection_toCompletion k (b ⊗ₜ[R] 1),
      ← F.includeLeftCompletion_toCompletion R F b, ← F.completedTensor_one_right R F]
    exact (F.tensorProduct R F).projection_eq_of_sub_mem_completionIdeal_succ (by
      simpa only [completedTensor_one_right, ← map_sub] using
        F.includeLeftCompletion_mem_completionIdeal R F hbu)
  have hr : (F.tensorProduct R F).projection k (F.completedTensor R F 1 u) =
      Ideal.Quotient.mk ((F.tensorProduct R F).ideal (k + 1)) (1 ⊗ₜ[R] b) := by
    rw [← (F.tensorProduct R F).projection_toCompletion k (1 ⊗ₜ[R] b),
      ← F.includeRightCompletion_toCompletion R F b, ← F.completedTensor_one_left R F]
    exact (F.tensorProduct R F).projection_eq_of_sub_mem_completionIdeal_succ (by
      simpa only [completedTensor_one_left, ← map_sub] using
        F.includeRightCompletion_mem_completionIdeal R F hbu)
  exact Ideal.Quotient.eq_zero_iff_mem.mp <| by
    rw [map_sub, map_add, ← hc, ← hl, ← hr, ← map_add, hu.completedComul_eq, sub_self]

end GroupLikeAndPrimitive

section Exp

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Bialgebra R A]
  [Algebra ℚ A] [SMulCommClass R ℚ A] (F : AlgFiltration A)
  (hΔ : ∀ k, F.ideal k ≤ ((F.tensorProduct R F).ideal k).comap (Bialgebra.comulAlgHom R A))
  (hε : F.ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R A))

/-- The completed left tensor inclusion commutes with `completedExp`. -/
@[simp]
theorem includeLeftCompletion_completedExp (x : F.completionIdeal 1) :
    F.includeLeftCompletion R F (F.completedExp x) =
      (F.tensorProduct R F).completedExp
        ⟨F.includeLeftCompletion R F x,
          F.includeLeftCompletion_mem_completionIdeal R F x.property⟩ := by
  simpa only [← AlgHom.coe_toRingHom, coe_includeLeftCompletion] using
    F.mapCompletion_completedExp (F.tensorProduct R F)
      ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A) : A →+* A ⊗[R] A) id monotone_id
      (fun k => F.ideal_le_comap_includeLeft R F (k + 1)) (F.ideal_le_comap_includeLeft R F 1) x

/-- The completed right tensor inclusion commutes with `completedExp`. -/
@[simp]
theorem includeRightCompletion_completedExp (x : F.completionIdeal 1) :
    F.includeRightCompletion R F (F.completedExp x) =
      (F.tensorProduct R F).completedExp
        ⟨F.includeRightCompletion R F x,
          F.includeRightCompletion_mem_completionIdeal R F x.property⟩ := by
  simpa only [← AlgHom.coe_toRingHom, coe_includeRightCompletion] using
    F.mapCompletion_completedExp (F.tensorProduct R F)
      ((Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A) : A →+* A ⊗[R] A) id monotone_id
      (fun k => F.ideal_le_comap_includeRight R F (k + 1)) (F.ideal_le_comap_includeRight R F 1) x

/-- Completed comultiplication commutes with `completedExp`. -/
@[simp]
theorem completedComul_completedExp (x : F.completionIdeal 1) :
    F.completedComul R hΔ (F.completedExp x) =
      (F.tensorProduct R F).completedExp
        ⟨F.completedComul R hΔ x, F.completedComul_mem_completionIdeal R hΔ x.property⟩ := by
  simpa only [← AlgHom.coe_toRingHom, coe_completedComul] using
    F.mapCompletion_completedExp (F.tensorProduct R F)
      (Bialgebra.comulAlgHom R A : A →+* A ⊗[R] A) id monotone_id
      (fun k => hΔ (k + 1)) (hΔ 1) x

/-- Completed comultiplication commutes with `completedLog`. -/
@[simp]
theorem completedComul_completedLog (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}) :
    F.completedComul R hΔ (F.completedLog u) =
      (F.tensorProduct R F).completedLog ⟨F.completedComul R hΔ u, by
        simpa only [map_sub, map_one] using
          F.completedComul_mem_completionIdeal R hΔ u.property⟩ := by
  simpa only [← AlgHom.coe_toRingHom, coe_completedComul] using
    F.mapCompletion_completedLog (F.tensorProduct R F)
      (Bialgebra.comulAlgHom R A : A →+* A ⊗[R] A) id monotone_id
      (fun k => hΔ (k + 1)) (hΔ 1) u

/-- The completed exponential of a completed primitive element in the first completion ideal is
completed group-like. -/
theorem IsCompletedPrimitive.completedExp {x : F.completionIdeal 1}
    (hx : F.IsCompletedPrimitive R hΔ hε x.val) :
    F.IsCompletedGroupLike R hΔ hε (F.completedExp x) where
  completedCounit_eq_one :=
    F.completedCounit_eq_one_of_sub_one_mem R hε (F.completedExp_sub_one_mem x)
  completedComul_eq := by
    let xl : (F.tensorProduct R F).completionIdeal 1 :=
      ⟨F.includeLeftCompletion R F x, F.includeLeftCompletion_mem_completionIdeal R F x.property⟩
    let xr : (F.tensorProduct R F).completionIdeal 1 :=
      ⟨F.includeRightCompletion R F x, F.includeRightCompletion_mem_completionIdeal R F x.property⟩
    have hsum : (⟨F.completedComul R hΔ x, F.completedComul_mem_completionIdeal R hΔ x.property⟩ :
        (F.tensorProduct R F).completionIdeal 1) = xl + xr :=
      Subtype.ext (by simpa [xl, xr] using hx.completedComul_eq)
    rw [F.completedComul_completedExp R hΔ x, hsum,
      (F.tensorProduct R F).completedExp_add xl xr
        (F.commute_includeLeftCompletion_includeRightCompletion R F x x),
      ← F.includeLeftCompletion_completedExp R x,
      ← F.includeRightCompletion_completedExp R x, ← F.completedTensor_apply R F]

/-- The completed logarithm of a completed group-like element congruent to `1` modulo the first
completion ideal is completed primitive. -/
theorem IsCompletedGroupLike.completedLog
    {u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}}
    (hu : F.IsCompletedGroupLike R hΔ hε u.val) :
    F.IsCompletedPrimitive R hΔ hε (F.completedLog u) := by
  refine (F.isCompletedPrimitive_iff_completedComul_eq R hΔ hε).mpr ?_
  let G := F.tensorProduct R F
  let x : F.completionIdeal 1 := ⟨F.completedLog u, F.completedLog_mem u⟩
  have hxu : F.completedExp x = u.val := F.completedExp_completedLog u
  let xl : G.completionIdeal 1 :=
    ⟨F.includeLeftCompletion R F x, F.includeLeftCompletion_mem_completionIdeal R F x.property⟩
  let xr : G.completionIdeal 1 :=
    ⟨F.includeRightCompletion R F x, F.includeRightCompletion_mem_completionIdeal R F x.property⟩
  let dx : G.completionIdeal 1 :=
    ⟨F.completedComul R hΔ x, F.completedComul_mem_completionIdeal R hΔ x.property⟩
  have hexp : G.completedExp dx = G.completedExp (xl + xr) := by
    rw [← F.completedComul_completedExp R hΔ x, hxu, hu.completedComul_eq,
      G.completedExp_add xl xr (F.commute_includeLeftCompletion_includeRightCompletion R F x x),
      ← F.includeLeftCompletion_completedExp R x, ← F.includeRightCompletion_completedExp R x,
      hxu, ← F.completedTensor_apply R F]
  have hsub : (⟨G.completedExp dx, G.completedExp_sub_one_mem dx⟩ :
      {v : G.completion // v - 1 ∈ G.completionIdeal 1}) =
      ⟨G.completedExp (xl + xr), G.completedExp_sub_one_mem (xl + xr)⟩ := Subtype.ext hexp
  simpa [G, dx, xl, xr, x] using congrArg G.completedLog hsub

/-- For `x` in the first completion ideal, `completedExp x` is completed group-like if and only if
`x` is completed primitive. -/
@[simp]
theorem isCompletedGroupLike_completedExp_iff (x : F.completionIdeal 1) :
    F.IsCompletedGroupLike R hΔ hε (F.completedExp x) ↔
      F.IsCompletedPrimitive R hΔ hε x.val :=
  ⟨fun h => by
      simpa using h.completedLog R F hΔ hε (u := ⟨F.completedExp x, F.completedExp_sub_one_mem x⟩),
    fun h => h.completedExp R F hΔ hε⟩

/-- For `u` congruent to `1` modulo the first completion ideal, `completedLog u` is completed
primitive if and only if `u` is completed group-like. -/
@[simp]
theorem isCompletedPrimitive_completedLog_iff
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}) :
    F.IsCompletedPrimitive R hΔ hε (F.completedLog u) ↔
      F.IsCompletedGroupLike R hΔ hε u.val :=
  ⟨fun h => by simpa using h.completedExp R F hΔ hε (x := ⟨F.completedLog u, F.completedLog_mem u⟩),
    fun h => h.completedLog R F hΔ hε⟩

/-- `completedExp` and `completedLog` exchange completed primitive elements of the first completion
ideal and completed group-like elements congruent to `1` modulo the first completion ideal. -/
noncomputable def completedExpPrimitiveEquiv :
    {x : F.completionIdeal 1 // F.IsCompletedPrimitive R hΔ hε x.val} ≃
      {u : {u : F.completion // u - 1 ∈ F.completionIdeal 1} //
        F.IsCompletedGroupLike R hΔ hε u.val} where
  toFun x := ⟨⟨F.completedExp x.1, F.completedExp_sub_one_mem x.1⟩, x.2.completedExp R F hΔ hε⟩
  invFun u := ⟨⟨F.completedLog u.1, F.completedLog_mem u.1⟩, u.2.completedLog R F hΔ hε⟩
  left_inv x := Subtype.ext (Subtype.ext (F.completedLog_completedExp x.1))
  right_inv u := Subtype.ext (Subtype.ext (F.completedExp_completedLog u.1))

@[simp]
theorem coe_completedExpPrimitiveEquiv
    (x : {x : F.completionIdeal 1 // F.IsCompletedPrimitive R hΔ hε x.val}) :
    ((F.completedExpPrimitiveEquiv R hΔ hε x).val : F.completion) = F.completedExp x.val := (rfl)

@[simp]
theorem coe_completedExpPrimitiveEquiv_symm
    (u : {u : {u : F.completion // u - 1 ∈ F.completionIdeal 1} //
      F.IsCompletedGroupLike R hΔ hε u.val}) :
    ((F.completedExpPrimitiveEquiv R hΔ hε).symm u).val.val = F.completedLog u.val := (rfl)

/-- When the first filtration ideal contains the counit kernel, `completedExp` and `completedLog`
exchange all completed primitive elements and all completed group-like elements. -/
noncomputable def completedExpPrimitiveEquivOfKerLe
    (hε' : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1) :
    {x : F.completion // F.IsCompletedPrimitive R hΔ hε x} ≃
      {u : F.completion // F.IsCompletedGroupLike R hΔ hε u} where
  toFun x := ⟨F.completedExp ⟨x.1, x.2.mem_completionIdeal_one hε'⟩,
    x.2.completedExp R F hΔ hε (x := ⟨x.1, x.2.mem_completionIdeal_one hε'⟩)⟩
  invFun u := ⟨F.completedLog ⟨u.1, u.2.sub_one_mem hε'⟩,
    u.2.completedLog R F hΔ hε (u := ⟨u.1, u.2.sub_one_mem hε'⟩)⟩
  left_inv x := Subtype.ext (F.completedLog_completedExp ⟨x.1, x.2.mem_completionIdeal_one hε'⟩)
  right_inv u := Subtype.ext (F.completedExp_completedLog ⟨u.1, u.2.sub_one_mem hε'⟩)

@[simp]
theorem coe_completedExpPrimitiveEquivOfKerLe
    (hε' : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1)
    (x : {x : F.completion // F.IsCompletedPrimitive R hΔ hε x}) :
    (F.completedExpPrimitiveEquivOfKerLe R hΔ hε hε' x : F.completion) =
      F.completedExp ⟨x.1, x.2.mem_completionIdeal_one hε'⟩ := (rfl)

@[simp]
theorem coe_completedExpPrimitiveEquivOfKerLe_symm
    (hε' : RingHom.ker (Bialgebra.counitAlgHom R A) ≤ F.ideal 1)
    (u : {u : F.completion // F.IsCompletedGroupLike R hΔ hε u}) :
    ((F.completedExpPrimitiveEquivOfKerLe R hΔ hε hε').symm u : F.completion) =
      F.completedLog ⟨u.1, u.2.sub_one_mem hε'⟩ := (rfl)

/-- The product of two completed exponentials is congruent to `1` modulo the first completion
ideal. -/
theorem completedExp_mul_completedExp_sub_one_mem (x y : F.completionIdeal 1) :
    F.completedExp x * F.completedExp y - 1 ∈ F.completionIdeal 1 := by
  have h : F.completedExp x * F.completedExp y - 1 =
      (F.completedExp x - 1) * F.completedExp y + (F.completedExp y - 1) := by
    rw [sub_mul, one_mul, sub_add_sub_cancel]
  exact h ▸ add_mem ((F.completionIdeal 1).mul_mem_right _ (F.completedExp_sub_one_mem x))
    (F.completedExp_sub_one_mem y)

/-- **Completed Baker–Campbell–Hausdorff primitivity**: the completed logarithm of the product of
the exponentials of two completed primitive elements in the first completion ideal is again
completed primitive. -/
theorem isCompletedPrimitive_completedLog_completedExp_mul_completedExp
    {x y : F.completionIdeal 1} (hx : F.IsCompletedPrimitive R hΔ hε x.val)
    (hy : F.IsCompletedPrimitive R hΔ hε y.val) :
    F.IsCompletedPrimitive R hΔ hε
      (F.completedLog ⟨F.completedExp x * F.completedExp y,
        F.completedExp_mul_completedExp_sub_one_mem x y⟩) :=
  ((hx.completedExp R F hΔ hε).mul (hy.completedExp R F hΔ hε)).completedLog R F hΔ hε

end Exp

end TauCeti.AlgFiltration
