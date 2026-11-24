/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Basic

/-!
# Basic infrastructure for two-sided ideals

This file provides general-purpose utilities for `TwoSidedIdeal A` extending
`Mathlib.RingTheory.TwoSidedIdeal.Basic`:

* subsingleton characterization of `TwoSidedIdeal A`;
* bundling an `R`-invariant two-sided ideal `I : TwoSidedIdeal A` as an `R`-submodule
  `I.toSubmoduleOfSMulMem hsmul : Submodule R A` with the same underlying carrier `I`
  (exposed so that carrier subtypes `↥(I.toSubmoduleOfSMulMem hsmul)` and `↥I` agree
  definitionally for downstream module and quotient constructions).

## Main definitions and results

* `TwoSidedIdeal.instSubsingleton` and `TwoSidedIdeal.subsingleton_iff`: `TwoSidedIdeal A` is a
  subsingleton if and only if `A` is a subsingleton.
* `TwoSidedIdeal.toSubmoduleOfSMulMem`: bundles an `R`-invariant two-sided ideal as an
  `R`-submodule of `A`, with coercion, membership, order, and injectivity lemmas
  `coe_toSubmoduleOfSMulMem`, `mem_toSubmoduleOfSMulMem`,
  `toSubmoduleOfSMulMem_le_toSubmoduleOfSMulMem`, and `toSubmoduleOfSMulMem_inj`.
-/

public section

namespace TwoSidedIdeal

section Subsingleton

variable {A : Type*} [NonUnitalNonAssocRing A]

/-- If `A` is a subsingleton, then `TwoSidedIdeal A` is a subsingleton. -/
instance instSubsingleton [Subsingleton A] : Subsingleton (TwoSidedIdeal A) :=
  orderIsoRingCon.toEquiv.subsingleton_congr.mpr (RingCon.subsingleton_iff.mpr ‹_›)

/-- `TwoSidedIdeal A` is a subsingleton if and only if `A` is a subsingleton. -/
theorem subsingleton_iff : Subsingleton (TwoSidedIdeal A) ↔ Subsingleton A :=
  orderIsoRingCon.toEquiv.subsingleton_congr.trans RingCon.subsingleton_iff

end Subsingleton

section Submodule

variable {R A : Type*} [Semiring R] [NonUnitalNonAssocRing A] [Module R A]

/-- Bundle an `R`-invariant two-sided ideal `I : TwoSidedIdeal A` as an `R`-submodule of `A` with
the same underlying carrier. -/
@[expose]
def toSubmoduleOfSMulMem (I : TwoSidedIdeal A)
    (hsmul : ∀ (r : R) {x : A}, x ∈ I → r • x ∈ I) : Submodule R A where
  carrier := I
  add_mem' := I.add_mem
  zero_mem' := I.zero_mem
  smul_mem' r _ hx := hsmul r hx

@[simp]
theorem coe_toSubmoduleOfSMulMem (I : TwoSidedIdeal A)
    (hsmul : ∀ (r : R) {x : A}, x ∈ I → r • x ∈ I) :
    (I.toSubmoduleOfSMulMem hsmul : Set A) = I :=
  (rfl)

@[simp]
theorem mem_toSubmoduleOfSMulMem {I : TwoSidedIdeal A}
    {hsmul : ∀ (r : R) {x : A}, x ∈ I → r • x ∈ I} {a : A} :
    a ∈ I.toSubmoduleOfSMulMem hsmul ↔ a ∈ I :=
  (Iff.rfl)

@[simp]
theorem toSubmoduleOfSMulMem_le_toSubmoduleOfSMulMem {I J : TwoSidedIdeal A}
    {hI : ∀ (r : R) {x : A}, x ∈ I → r • x ∈ I}
    {hJ : ∀ (r : R) {x : A}, x ∈ J → r • x ∈ J} :
    I.toSubmoduleOfSMulMem hI ≤ J.toSubmoduleOfSMulMem hJ ↔ I ≤ J :=
  (Iff.rfl)

@[simp]
theorem toSubmoduleOfSMulMem_inj {I J : TwoSidedIdeal A}
    {hI : ∀ (r : R) {x : A}, x ∈ I → r • x ∈ I}
    {hJ : ∀ (r : R) {x : A}, x ∈ J → r • x ∈ J} :
    I.toSubmoduleOfSMulMem hI = J.toSubmoduleOfSMulMem hJ ↔ I = J :=
  ⟨fun h => le_antisymm
    (toSubmoduleOfSMulMem_le_toSubmoduleOfSMulMem.mp h.le)
    (toSubmoduleOfSMulMem_le_toSubmoduleOfSMulMem.mp h.ge),
   fun h => Submodule.ext fun x => by simp [h]⟩

end Submodule

end TwoSidedIdeal
