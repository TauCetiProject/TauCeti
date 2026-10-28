/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fin.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Fixed coefficients of a weighted cycle

A weighted cycle sends coordinate `i` to coordinate `finRotate _ i`, multiplying
by `a i`. Its fixed tuples are determined by coordinate zero: the other coordinates
are its scalar multiples by the prefix products over every commutative semiring.
Monodromy `1` gives the coefficient module over every commutative semiring.
Over a commutative ring, the closing equation is torsion by `(∏ i, a i) - 1`,
and monodromy `-1` gives its `2`-torsion. The weights are arbitrary.

The basis-facing form of this calculation is in `WeightedCycle.Basis`.

-/

public section

namespace TauCeti.WeightedCycle

variable {A M : Type*} {n : ℕ}

section CommSemiring

variable [CommSemiring A] [AddCommMonoid M] [Module A M]

/-- The weighted cyclic shift: the weight at a source coordinate travels with it. -/
def linearMap (a : Fin (n + 1) → A) : (Fin (n + 1) → M) →ₗ[A] (Fin (n + 1) → M) :=
  LinearMap.pi fun j ↦
    a ((finRotate (n + 1)).symm j) • LinearMap.proj ((finRotate (n + 1)).symm j)

/-- At an arbitrary coordinate, the weighted shift reads the preceding coordinate. -/
theorem linearMap_apply (a : Fin (n + 1) → A) (v : Fin (n + 1) → M)
    (j : Fin (n + 1)) :
    linearMap a v j = a ((finRotate (n + 1)).symm j) •
      v ((finRotate (n + 1)).symm j) := by
  rfl

/-- The coefficient at the successor of `i` comes from `i`. -/
theorem linearMap_apply_rotate (a : Fin (n + 1) → A) (v : Fin (n + 1) → M)
    (i : Fin (n + 1)) :
    linearMap a v (finRotate (n + 1) i) = a i • v i := by
  simp only [linearMap_apply, Equiv.symm_apply_apply]

/-- The coefficient at the cyclic successor of `i` is its weighted source coefficient. -/
@[simp]
theorem linearMap_apply_add_one (a : Fin (n + 1) → A) (v : Fin (n + 1) → M)
    (i : Fin (n + 1)) :
    linearMap a v (i + 1) = a i • v i := by
  simpa only [finRotate_apply] using linearMap_apply_rotate a v i

/-- Fixed tuples satisfy the cyclic recurrence, including its closing edge. -/
theorem mem_fixedSubmodule_iff (a : Fin (n + 1) → A) (v : Fin (n + 1) → M) :
    v ∈ (linearMap a).fixedSubmodule ↔
      ∀ i, v (finRotate (n + 1) i) = a i • v i := by
  rw [LinearMap.mem_fixedSubmodule_iff]
  constructor
  · intro h i
    exact (congrFun h (finRotate (n + 1) i)).symm.trans (linearMap_apply_rotate a v i)
  · intro h
    funext j
    obtain ⟨i, rfl⟩ := (finRotate (n + 1)).surjective j
    exact (linearMap_apply_rotate a v i).trans (h i).symm

/-- Every fixed coordinate is the initial coordinate multiplied by a prefix product. -/
theorem coeff_eq_partialProd_smul (a : Fin (n + 1) → A)
    (v : (linearMap a (M := M)).fixedSubmodule) (i : Fin (n + 1)) :
    v.val i = Fin.partialProd (Fin.init a) i • v.val 0 := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    have h := (mem_fixedSubmodule_iff a v.val).mp v.property i.castSucc
    rw [Fin.finRotate_castSucc] at h
    rw [h, ih, Fin.partialProd_succ]
    rw [mul_smul]
    exact smul_comm _ _ _

/-- A cycle of monodromy one contributes one copy of the coefficient module. -/
def fixedEquivOfProdEqOne (a : Fin (n + 1) → A) (h : ∏ i, a i = 1) :
    (linearMap a (M := M)).fixedSubmodule ≃ₗ[A] M where
  toFun v := v.val 0
  invFun t := ⟨fun i ↦ Fin.partialProd (Fin.init a) i • t, by
    rw [mem_fixedSubmodule_iff]
    intro i
    induction i using Fin.lastCases with
    | last =>
      simp only [finRotate_last, Fin.partialProd_zero, one_smul]
      rw [← mul_smul, Fin.last_mul_partialProd, h, one_smul]
    | cast i =>
      rw [Fin.finRotate_castSucc, Fin.partialProd_succ, mul_smul]
      exact smul_comm _ _ _⟩
  left_inv v := Subtype.ext <| funext fun i ↦ (coeff_eq_partialProd_smul a v i).symm
  right_inv t := by simp
  map_add' v w := rfl
  map_smul' r v := rfl

/-- Positive monodromy: the forward map is evaluation at zero. -/
@[simp]
theorem fixedEquivOfProdEqOne_apply (a : Fin (n + 1) → A) (h : ∏ i, a i = 1)
    (v : (linearMap a (M := M)).fixedSubmodule) :
    fixedEquivOfProdEqOne a h v = v.val 0 := by
  rfl

/-- Positive monodromy: the inverse retains the prefix-product formula. -/
@[simp]
theorem fixedEquivOfProdEqOne_symm_apply (a : Fin (n + 1) → A) (h : ∏ i, a i = 1)
    (t : M) (i : Fin (n + 1)) :
    ((fixedEquivOfProdEqOne a h).symm t).val i = Fin.partialProd (Fin.init a) i • t := by
  rfl

end CommSemiring

section CommRing

variable [CommRing A] [AddCommGroup M] [Module A M]

/-- The fixed condition is the prefix formula together with the monodromy equation. -/
theorem mem_fixedSubmodule_iff_partialProd (a : Fin (n + 1) → A)
    (v : Fin (n + 1) → M) :
    v ∈ (linearMap a).fixedSubmodule ↔
      (∀ i, v i = Fin.partialProd (Fin.init a) i • v 0) ∧
        ((∏ i, a i) - 1) • v 0 = 0 := by
  constructor
  · intro hv
    have hc : ∀ i, v i = Fin.partialProd (Fin.init a) i • v 0 :=
      coeff_eq_partialProd_smul a ⟨v, hv⟩
    refine ⟨hc, ?_⟩
    have h := (mem_fixedSubmodule_iff a v).mp hv (Fin.last n)
    rw [finRotate_last, hc (Fin.last n), ← mul_smul, Fin.last_mul_partialProd] at h
    simpa [sub_smul, sub_eq_zero] using h.symm
  · rintro ⟨hc, hm⟩
    rw [mem_fixedSubmodule_iff]
    intro i
    induction i using Fin.lastCases with
    | last =>
      rw [finRotate_last, hc (Fin.last n), ← mul_smul, Fin.last_mul_partialProd]
      have hm' : (∏ i, a i) • v 0 = v 0 := by
        simpa [sub_smul, sub_eq_zero] using hm
      exact hm'.symm
    | cast i =>
      rw [Fin.finRotate_castSucc, hc i.succ, hc i.castSucc, Fin.partialProd_succ]
      rw [mul_smul]
      exact smul_comm _ _ _

/-- Evaluation at zero identifies fixed tuples with torsion by monodromy minus one.
The inverse has the literal prefix-product coordinates. -/
def fixedEquivTorsion (a : Fin (n + 1) → A) :
    (linearMap a (M := M)).fixedSubmodule ≃ₗ[A]
      Submodule.torsionBy A M ((∏ i, a i) - 1) where
  toFun v := ⟨v.val 0, ((mem_fixedSubmodule_iff_partialProd a v.val).mp v.property).2⟩
  invFun t := ⟨fun i ↦ Fin.partialProd (Fin.init a) i • t.val,
    (mem_fixedSubmodule_iff_partialProd a _).mpr ⟨by simp, by simp⟩⟩
  left_inv v := Subtype.ext <| funext fun i ↦ (coeff_eq_partialProd_smul a v i).symm
  right_inv t := Subtype.ext <| by simp
  map_add' v w := rfl
  map_smul' r v := rfl

/-- The forward equivalence reads the initial coefficient. -/
@[simp]
theorem fixedEquivTorsion_apply (a : Fin (n + 1) → A)
    (v : (linearMap a (M := M)).fixedSubmodule) :
    (fixedEquivTorsion a v : M) = v.val 0 := by
  rfl

/-- The inverse equivalence multiplies by the prefix products. -/
@[simp]
theorem fixedEquivTorsion_symm_apply (a : Fin (n + 1) → A)
    (t : Submodule.torsionBy A M ((∏ i, a i) - 1)) (i : Fin (n + 1)) :
    ((fixedEquivTorsion a).symm t).val i = Fin.partialProd (Fin.init a) i • t.val := by
  rfl

/-- A cycle of monodromy minus one contributes the full `2`-torsion submodule. -/
def fixedEquivOfProdEqNegOne (a : Fin (n + 1) → A) (h : ∏ i, a i = -1) :
    (linearMap a (M := M)).fixedSubmodule ≃ₗ[A] Submodule.torsionBy A M 2 :=
  (fixedEquivTorsion a).trans <| LinearEquiv.ofEq _ _ (by
    ext t
    simp only [Submodule.mem_torsionBy_iff, h, sub_eq_add_neg, ← neg_add,
      neg_smul, neg_eq_zero, add_smul, one_smul, two_smul])

/-- Negative monodromy: the forward map reads a coefficient killed by two. -/
@[simp]
theorem fixedEquivOfProdEqNegOne_apply (a : Fin (n + 1) → A) (h : ∏ i, a i = -1)
    (v : (linearMap a (M := M)).fixedSubmodule) :
    (fixedEquivOfProdEqNegOne a h v : M) = v.val 0 := by
  rfl

/-- Negative monodromy: the inverse has the same prefix-product coordinates. -/
@[simp]
theorem fixedEquivOfProdEqNegOne_symm_apply (a : Fin (n + 1) → A) (h : ∏ i, a i = -1)
    (t : Submodule.torsionBy A M 2) (i : Fin (n + 1)) :
    ((fixedEquivOfProdEqNegOne a h).symm t).val i = Fin.partialProd (Fin.init a) i • t.val := by
  rfl

end CommRing

end TauCeti.WeightedCycle
