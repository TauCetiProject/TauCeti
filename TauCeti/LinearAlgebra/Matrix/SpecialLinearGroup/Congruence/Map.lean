/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Change of scalars for principal congruence subgroups

A ring isomorphism carries the kernel of reduction modulo an ideal to the kernel of reduction
modulo the transported ideal. This lets arithmetic matrix groups change their integral model
without changing the congruence condition.
-/

public section

namespace Matrix.SpecialLinearGroup

variable {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]

/-- A ring isomorphism transports a principal congruence subgroup by transporting its level. -/
@[simp] theorem map_ker_map_quotientMk (e : R ≃+* S) (I : Ideal R) :
    ((map (n := n) (Ideal.Quotient.mk I)).ker).map (map (e : R →+* S)) =
      (map (Ideal.Quotient.mk (I.map e))).ker := by
  rw [← toMonoidHom_mapEquiv (n := n) (e := e), ← MulEquiv.toMonoidHom_eq_coe]
  ext A
  rw [Subgroup.mem_map_equiv, mem_ker_map_quotientMk_iff, mem_ker_map_quotientMk_iff]
  simp_rw [← Ideal.symm_apply_mem_of_equiv_iff (f := e)]
  apply forall_congr' fun i ↦ forall_congr' fun j ↦ ?_
  by_cases hij : i = j <;>
    simp [mapEquiv, Matrix.one_apply, hij]

end Matrix.SpecialLinearGroup
