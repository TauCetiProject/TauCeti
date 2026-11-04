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

A cyclic change of enumeration carries the weighted cycle equations of any
family of vectors to the rotated equations. Cyclic reindexing conjugates the
weighted shift and compares its fixed tuples. On monodromy torsion, changing the initial vertex
multiplies the parameter by its prefix product and lands in the torsion module
of the rotated cycle. This is invertible even when the weights are not units.
Composition is expressed on underlying coordinates, including cyclic wraparound.
-/

public section

namespace TauCeti.WeightedCycle

variable {A M : Type*} {n : ℕ}

/-- A cyclic change of enumeration gives the rotated weighted cycle equations for any family
of vectors: the weights are read at the shifted index. -/
theorem apply_eq_smul_addRight_trans {ι V : Type*} [SMul A V] (x : ι → V)
    (e : Fin (n + 1) ≃ ι) (a : Fin (n + 1) → A) (f : V → V)
    (h : ∀ i, f (x (e i)) = a i • x (e (finRotate (n + 1) i))) (k : Fin (n + 1)) :
    ∀ i, f (x (((Equiv.addRight k).trans e) i)) =
      a (i + k) • x (((Equiv.addRight k).trans e) (finRotate (n + 1) i)) := by
  intro i
  simpa only [Equiv.trans_apply, Equiv.coe_addRight, finRotate_apply,
    add_right_comm i k 1] using h (i + k)

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

/-- Successive changes of initial vertex add their cyclic offsets. -/
theorem fixedRotateEquiv_fixedRotateEquiv_apply (a : Fin (n + 1) → A) (k l : Fin (n + 1))
    (v : (linearMap a (M := M)).fixedSubmodule) (i : Fin (n + 1)) :
    (fixedRotateEquiv (fun j ↦ a (j + k)) l (fixedRotateEquiv a k v)).val i =
      (fixedRotateEquiv a (k + l) v).val i := by
  simp only [fixedRotateEquiv_apply, add_assoc, add_comm l k]

end CommSemiring

section CommRing

variable [CommRing A] [AddCommGroup M] [Module A M]

/-- Changing the representative carries the monodromy torsion of a cycle to that of its
rotation. The equivalence is induced by rotation of fixed tuples; no weight is inverted. -/
def torsionRotateEquiv (a : Fin (n + 1) → A) (k : Fin (n + 1)) :
    Submodule.torsionBy A M ((∏ i, a i) - 1) ≃ₗ[A]
      Submodule.torsionBy A M ((∏ i, a (i + k)) - 1) :=
  ((fixedEquivTorsion a).symm.trans (fixedRotateEquiv a k)).trans
    (fixedEquivTorsion (fun i ↦ a (i + k)))

/-- The parameter changes by the prefix product at the new initial vertex. -/
@[simp]
theorem torsionRotateEquiv_apply (a : Fin (n + 1) → A) (k : Fin (n + 1))
    (t : Submodule.torsionBy A M ((∏ i, a i) - 1)) :
    (torsionRotateEquiv a k t : M) = Fin.partialProd (Fin.init a) k • t.val := by
  simp [torsionRotateEquiv]

/-- The inverse parameter change uses the rotated prefix at the opposite offset. -/
@[simp]
theorem torsionRotateEquiv_symm_apply (a : Fin (n + 1) → A) (k : Fin (n + 1))
    (t : Submodule.torsionBy A M ((∏ i, a (i + k)) - 1)) :
    ((torsionRotateEquiv a k).symm t : M) =
      Fin.partialProd (Fin.init (fun i ↦ a (i + k))) (-k) • t.val := by
  simp [torsionRotateEquiv]

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
