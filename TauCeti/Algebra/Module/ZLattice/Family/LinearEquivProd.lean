/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Basic
public import TauCeti.Algebra.Module.Submodule.OrbitRelQuotient

/-!
# Algebraic trivialization of a torus family

Linear identifications carrying each period lattice onto a fixed submodule induce an equivalence
from the orbit quotient of the family to a product with the fixed translation quotient.
No topology, fullness, or choice of lattice basis is required.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Chapter 8 (families of complex tori and period data).
-/

public section

namespace TauCeti

variable {Y Λ E F : Type*} [AddCommGroup Λ] [AddCommGroup E] [AddCommGroup F]
  (P : Y → Λ →ₗ[ℤ] E) (L : Submodule ℤ F) (A : Y → E ≃ₗ[ℤ] F)
  (hL : ∀ y, (LinearMap.range (P y)).map (A y).toLinearMap = L)

/-- A linear identification of each period lattice with `L` trivializes the underlying family
of tori: `[y,v] ↦ (y,[A y v])`. No regularity or fullness is required for this equivalence. -/
noncomputable def torusFamilyLinearEquivProd :
    letI := periodAddAction P
    AddAction.orbitRel.Quotient Λ (Y × E) ≃ Y × AddAction.orbitRel.Quotient L F := by
  let _ := periodAddAction P
  have hmem (y : Y) (v : E) : A y v ∈ L ↔ v ∈ LinearMap.range (P y) := by
    rw [← hL y, Submodule.mem_map_equiv]
    simp
  exact
    { toFun := Quotient.lift
        (fun p : Y × E ↦ (p.1, Quotient.mk (AddAction.orbitRel L F) (A p.1 p.2)))
        fun p q hpq ↦ by
          obtain ⟨hy, hv⟩ := (mem_orbit_periodAddAction_iff P).1 hpq
          refine Prod.ext hy (Quotient.sound ?_)
          apply (L.orbitRel_apply_iff_sub_mem).2
          rw [hy, ← map_sub]
          exact (hmem q.1 _).2 hv
      invFun := fun p ↦ Quotient.liftOn p.2 (fun v ↦ Quotient.mk _ (p.1, (A p.1).symm v))
        fun v w hvw ↦ by
          apply Quotient.sound
          apply (mem_orbit_periodAddAction_iff P).2
          refine ⟨rfl, ?_⟩
          apply (hmem p.1 _).1
          simpa using (L.orbitRel_apply_iff_sub_mem).1 hvw
      left_inv := by
        rintro ⟨y, v⟩
        exact congrArg (Quotient.mk _) (Prod.ext rfl ((A y).symm_apply_apply v))
      right_inv := by
        rintro ⟨y, ⟨v⟩⟩
        exact Prod.ext rfl (congrArg (Quotient.mk _) ((A y).apply_symm_apply v)) }

/-- On representatives the trivialization applies the chosen linear identification. -/
@[simp] theorem torusFamilyLinearEquivProd_mk (y : Y) (v : E) :
    letI := periodAddAction P
    torusFamilyLinearEquivProd P L A hL (Quotient.mk _ (y, v)) =
      (y, Quotient.mk _ (A y v)) := (rfl)

/-- On representatives the inverse trivialization applies the inverse linear identification. -/
@[simp] theorem torusFamilyLinearEquivProd_symm_mk (y : Y) (v : F) :
    letI := periodAddAction P
    (torusFamilyLinearEquivProd P L A hL).symm (y, Quotient.mk _ v) =
      Quotient.mk _ (y, (A y).symm v) := (rfl)

/-- The linear trivialization lies over the parameter space. -/
@[simp] theorem fst_torusFamilyLinearEquivProd
    (x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    (torusFamilyLinearEquivProd P L A hL x).1 = torusFamilyProjection P x := by
  let _ := periodAddAction P
  induction x using Quotient.inductionOn with
  | h p =>
      rw [torusFamilyProjection_mk]
      exact congrArg Prod.fst (torusFamilyLinearEquivProd_mk P L A hL p.1 p.2)

end TauCeti
