/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CohenMacaulay.RegularSequence
import TauCeti.RingTheory.LocalRing.Quotient

/-!
# Quotients of the expected dimension

In a Cohen–Macaulay local ring, equations cutting out the expected dimension form a regular
sequence. Consequently their quotient is again Cohen–Macaulay. This criterion applies to
local complete intersections without requiring a regular sequence as input. Also included is the
principal-ideal equivalence modulo a regular element
(`Module.isCohenMacaulay_quotient_span_singleton_iff`,
`Module.IsCohenMacaulay.quotient_span_singleton`).

## References

* The Stacks Project, Proposition 10.103.4 (Tag 00N6) and Lemma 10.103.5 (Tag 0C6G).
-/

public section

open IsLocalRing
open scoped Pointwise

namespace Module

section

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {w : R}
  [IsLocalRing (R ⧸ Ideal.span {w})]

/-- **Cohen–Macaulayness modulo a regular element.** For an `R`-regular element `w` of a Noetherian
local ring `R` with local quotient `R ⧸ (w)`, `R ⧸ (w)` is Cohen–Macaulay iff `R` is. -/
theorem isCohenMacaulay_quotient_span_singleton_iff (hw : IsSMulRegular R w) :
    IsCohenMacaulay (R ⧸ Ideal.span {w}) (R ⧸ Ideal.span {w}) ↔ IsCohenMacaulay R R := by
  have hwm : w ∈ maximalIdeal R :=
    (Ideal.span {w}).le_maximalIdeal_of_isLocalRing_quotient (Ideal.mem_span_singleton_self w)
  have hspan : w • (⊤ : Ideal R) = Ideal.span {w} := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  rw [← isCohenMacaulay_iff_isCohenMacaulay_of_surjective Ideal.Quotient.mk_surjective,
    ← (Submodule.quotEquivOfEq _ _ hspan).isCohenMacaulay_iff,
    isCohenMacaulay_quotSMulTop_iff hw hwm]

end

namespace IsCohenMacaulay

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The quotient of a Noetherian Cohen–Macaulay local ring by a regular element with local
quotient is Cohen–Macaulay. -/
theorem quotient_span_singleton {w : R} [IsLocalRing (R ⧸ Ideal.span {w})]
    (hR : IsCohenMacaulay R R) (hw : IsSMulRegular R w) :
    IsCohenMacaulay (R ⧸ Ideal.span {w}) (R ⧸ Ideal.span {w}) :=
  (isCohenMacaulay_quotient_span_singleton_iff hw).2 hR

/-- A quotient of a Cohen–Macaulay local ring is Cohen–Macaulay if its dimension drops by
the number of generators of the kernel. -/
theorem of_surjective_of_ringKrullDim_add_length_eq {S : Type*} [CommRing S] [IsLocalRing S]
    [Algebra R S] (h : Module.IsCohenMacaulay R R)
    (hsurj : Function.Surjective (algebraMap R S)) (rs : List R)
    (hker : RingHom.ker (algebraMap R S) = Ideal.ofList rs)
    (hdim : ringKrullDim S + rs.length = ringKrullDim R) :
    Module.IsCohenMacaulay S S := by
  let e := (Ideal.quotientEquivAlgOfEq R hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) hsurj)
  have : IsLocalRing (R ⧸ Ideal.ofList rs) := e.symm.toRingEquiv.isLocalRing
  have : IsNoetherianRing (R ⧸ Ideal.ofList rs) :=
    isNoetherianRing_of_surjective R _ _ Ideal.Quotient.mk_surjective
  have hle : Ideal.ofList rs ≤ maximalIdeal R :=
    le_maximalIdeal (by rw [← hker]; exact RingHom.ker_ne_top _)
  have hrs : ∀ r ∈ rs, r ∈ maximalIdeal R := fun r hr ↦
    hle (Ideal.subset_span hr)
  have hsmul : Ideal.ofList rs • (⊤ : Submodule R R) = Ideal.ofList rs := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  let e' := Submodule.quotEquivOfEq _ _ hsmul
  have hreg := (h.isRegular_iff_supportDim_add_length_eq_supportDim rs hrs).2 (by
    rw [Module.supportDim_eq_of_equiv e', Module.supportDim_self_eq_ringKrullDim,
      Module.supportDim_quotient_eq_ringKrullDim, ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
    exact hdim)
  have hquot := (Module.isCohenMacaulay_quotient_ofList_smul_iff rs hreg).2 h
  rw [e'.isCohenMacaulay_iff] at hquot
  exact e.toRingEquiv.isCohenMacaulay_self_iff.mp
    ((Module.isCohenMacaulay_iff_isCohenMacaulay_of_surjective
      Ideal.Quotient.mk_surjective).1 hquot)

end IsCohenMacaulay
end Module
