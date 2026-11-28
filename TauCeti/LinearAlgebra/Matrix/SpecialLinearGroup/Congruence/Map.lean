/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.RingTheory.Ideal.Quotient.Operations

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
  let q := Ideal.quotientEquiv I (I.map e) e rfl
  have hq : (q.symm : _ →+* _).comp (Ideal.Quotient.mk (I.map e)) =
      (Ideal.Quotient.mk I).comp (e.symm : S →+* R) := RingHom.ext fun x ↦ by
    simpa only [RingHom.comp_apply, RingEquiv.coe_toRingHom, q] using
      Ideal.quotientEquiv_symm_mk I (I.map e) e rfl x
  have hcomm :
      (map (n := n) (Ideal.Quotient.mk I)).comp (mapEquiv n e).symm =
        ((mapEquiv n q).symm : _ →* _).comp (map (n := n) (Ideal.Quotient.mk (I.map e))) := by
    simp only [symm_mapEquiv, toMonoidHom_mapEquiv, map_comp_map, hq]
  simpa only [MonoidHom.ker_comp_mulEquiv, MulEquiv.symm_symm, toMonoidHom_mapEquiv,
    MonoidHom.ker_mulEquiv_comp] using congrArg MonoidHom.ker hcomm

end Matrix.SpecialLinearGroup
