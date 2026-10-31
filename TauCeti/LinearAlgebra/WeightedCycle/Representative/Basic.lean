/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.WeightedCycle.Basic
public import TauCeti.LinearAlgebra.FixedSubmodule

/-!
# Changing the initial vertex of a weighted cycle

Cyclic reindexing conjugates the weighted shift and compares its fixed tuples.
On monodromy torsion, changing the initial vertex multiplies the parameter by
its prefix product. This is invertible on the torsion module even when the
weights are not units. Composition is expressed on underlying coordinates,
including cyclic wraparound.
-/

public section

namespace TauCeti.WeightedCycle

variable {A M : Type*} {n : ℕ}

section CommSemiring

variable [CommSemiring A] [AddCommMonoid M] [Module A M]

/-- Precomposition by a cyclic translation intertwines the two weighted shifts. -/
theorem funCongrLeft_comp_linearMap (a : Fin (n + 1) → A) (k : Fin (n + 1)) :
    (LinearEquiv.funCongrLeft A M (Equiv.addRight k)).toLinearMap ∘ₗ linearMap a =
      linearMap (fun i ↦ a (i + k)) ∘ₗ
        (LinearEquiv.funCongrLeft A M (Equiv.addRight k)).toLinearMap := by
  apply LinearMap.ext
  intro v
  funext j
  obtain ⟨i, rfl⟩ := (finRotate (n + 1)).surjective j
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Equiv.coe_addRight,
    finRotate_apply]
  rw [add_right_comm i 1 k, linearMap_apply_add_one, linearMap_apply_add_one,
    LinearMap.funLeft_apply]

/-- Changing the initial vertex restricts cyclic precomposition to fixed tuples. -/
def fixedRotateEquiv (a : Fin (n + 1) → A) (k : Fin (n + 1)) :
    (linearMap a (M := M)).fixedSubmodule ≃ₗ[A]
      (linearMap (fun i ↦ a (i + k)) (M := M)).fixedSubmodule :=
  (LinearEquiv.funCongrLeft A M (Equiv.addRight k)).fixedSubmoduleCongr
    (funCongrLeft_comp_linearMap a k)

/-- The new coordinate at `i` is the old coordinate at `i + k`. -/
@[simp]
theorem fixedRotateEquiv_apply (a : Fin (n + 1) → A) (k : Fin (n + 1))
    (v : (linearMap a (M := M)).fixedSubmodule) (i : Fin (n + 1)) :
    (fixedRotateEquiv a k v).val i = v.val (i + k) := by
  simp [fixedRotateEquiv]

/-- The inverse returns to the original enumeration. -/
@[simp]
theorem fixedRotateEquiv_symm_apply (a : Fin (n + 1) → A) (k : Fin (n + 1))
    (v : (linearMap (fun i ↦ a (i + k)) (M := M)).fixedSubmodule)
    (i : Fin (n + 1)) :
    ((fixedRotateEquiv a k).symm v).val i = v.val (i - k) := by
  simp [fixedRotateEquiv, sub_eq_add_neg]

/-- The zero rotation fixes every coordinate. -/
theorem fixedRotateEquiv_zero_apply (a : Fin (n + 1) → A)
    (v : (linearMap a (M := M)).fixedSubmodule) (i : Fin (n + 1)) :
    (fixedRotateEquiv a 0 v).val i = v.val i := by
  simp

/-- Successive changes of initial vertex add their cyclic offsets. -/
theorem fixedRotateEquiv_trans_apply (a : Fin (n + 1) → A) (k l : Fin (n + 1))
    (v : (linearMap a (M := M)).fixedSubmodule) (i : Fin (n + 1)) :
    (fixedRotateEquiv (fun j ↦ a (j + k)) l (fixedRotateEquiv a k v)).val i =
      (fixedRotateEquiv a (k + l) v).val i := by
  simp only [fixedRotateEquiv_apply, add_assoc, add_comm l k]

end CommSemiring

section CommRing

variable [CommRing A] [AddCommGroup M] [Module A M]

/-- Changing the representative acts invertibly on monodromy torsion.
This automorphism is induced by rotation of fixed tuples; no weight is inverted. -/
def torsionRotateEquiv (a : Fin (n + 1) → A) (k : Fin (n + 1)) :
    Submodule.torsionBy A M ((∏ i, a i) - 1) ≃ₗ[A]
      Submodule.torsionBy A M ((∏ i, a i) - 1) :=
  ((fixedEquivTorsion a).symm.trans (fixedRotateEquiv a k)).trans
    ((fixedEquivTorsion (fun i ↦ a (i + k))).trans (LinearEquiv.ofEq _ _ (by
      have hprod : (∏ i, a (i + k)) = ∏ i, a i :=
        Equiv.prod_comp (Equiv.addRight k) a
      rw [hprod])))

/-- The parameter changes by the prefix product at the new initial vertex. -/
@[simp]
theorem torsionRotateEquiv_apply (a : Fin (n + 1) → A) (k : Fin (n + 1))
    (t : Submodule.torsionBy A M ((∏ i, a i) - 1)) :
    (torsionRotateEquiv a k t : M) = Fin.partialProd (Fin.init a) k • t.val := by
  simp [torsionRotateEquiv]

/-- The inverse parameter change uses the rotated prefix at the opposite offset. -/
@[simp]
theorem torsionRotateEquiv_symm_apply (a : Fin (n + 1) → A) (k : Fin (n + 1))
    (t : Submodule.torsionBy A M ((∏ i, a i) - 1)) :
    ((torsionRotateEquiv a k).symm t : M) =
      Fin.partialProd (Fin.init (fun i ↦ a (i + k))) (-k) • t.val := by
  simp [torsionRotateEquiv]

/-- The zero change of representative is identity on the torsion module. -/
@[simp]
theorem torsionRotateEquiv_zero_apply (a : Fin (n + 1) → A)
    (t : Submodule.torsionBy A M ((∏ i, a i) - 1)) :
    torsionRotateEquiv a 0 t = t := by
  ext
  simp

/-- The cyclic prefix composition law holds on monodromy torsion, including wraparound. -/
theorem partialProd_rotate_smul (a : Fin (n + 1) → A) (k l : Fin (n + 1))
    (t : Submodule.torsionBy A M ((∏ i, a i) - 1)) :
    Fin.partialProd (Fin.init (fun i ↦ a (i + k))) l •
        (Fin.partialProd (Fin.init a) k • t.val) =
      Fin.partialProd (Fin.init a) (k + l) • t.val := by
  have h := coeff_eq_partialProd_smul (fun i ↦ a (i + k))
    (fixedRotateEquiv a k ((fixedEquivTorsion a).symm t)) l
  simpa only [fixedRotateEquiv_apply, fixedEquivTorsion_symm_apply,
    zero_add, add_comm l k] using h.symm

end CommRing

end TauCeti.WeightedCycle
