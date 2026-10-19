/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality

import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Finitely generated modules with finitely many elements

A module `M` over a commutative ring `A` is a module over `A ⧸ ann_A M`, on which it is faithful.
Hence the quotient `A ⧸ ann_A M` embeds into the additive endomorphisms of `M`, and is finite
when `M` is. Conversely a finitely generated module over a finite ring is finite. So a finitely
generated module is finite exactly when the quotient of the ring by its annihilator is.

## Main results

* `Module.finite_quotient_annihilator`: the quotient of the ring by the annihilator of a finite
  module is finite.
* `Module.finite_iff_finite_quotient_annihilator`: a finitely generated module is finite iff the
  quotient of the ring by its annihilator is finite.
-/

public section

namespace Module

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- The quotient of the ring by the annihilator of a finite module is finite: it embeds into the
additive endomorphisms of the module. -/
theorem finite_quotient_annihilator [Finite M] : Finite (A ⧸ annihilator A M) :=
  Finite.of_injective (fun x ↦ ⇑(RingHom.kerLift (toAddMonoidEnd A M) x))
    (DFunLike.coe_injective.comp (RingHom.kerLift_injective _))

/-- A finitely generated module is finite iff the quotient of the ring by its annihilator is
finite. -/
theorem finite_iff_finite_quotient_annihilator [Module.Finite A M] :
    Finite M ↔ Finite (A ⧸ annihilator A M) := by
  refine ⟨fun _ ↦ finite_quotient_annihilator, fun _ ↦ ?_⟩
  let := quotientAnnihilator (R := A) (M := M)
  have : Module.Finite (A ⧸ annihilator A M) M := .of_restrictScalars_finite A _ M
  exact finite_of_finite (A ⧸ annihilator A M)

end Module
