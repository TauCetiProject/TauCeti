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

A module `M` over a ring `A` is a module over `A ⧸ ann_A M`, on which it is faithful.
Hence the quotient `A ⧸ ann_A M` embeds into the additive endomorphisms of `M`, and is finite
when `M` is. Conversely a finitely generated module over a finite ring is finite. So a finitely
generated module is finite exactly when the quotient of the ring by its annihilator is.

## Main results

* `Module.finite_quotient_annihilator`: the quotient of the ring by the annihilator of a finite
  module is finite.
* `Module.finite_iff_finite_quotient_annihilator`: a finitely generated module is finite iff the
  quotient of the ring by its annihilator is finite.
* `Submodule.finite_quotient_smul_top`: a finitely generated module `M` has finite quotient
  `M ⧸ J • M` when `R ⧸ J` is finite.
-/

public section

namespace Module

variable {A M : Type*} [Ring A] [AddCommMonoid M] [Module A M]

/-- The quotient of the ring by the annihilator of a finite module is finite: it embeds into the
additive endomorphisms of the module. -/
theorem finite_quotient_annihilator [Finite M] : Finite (A ⧸ annihilator A M) :=
  -- `annihilator A M` is by definition the kernel of `toAddMonoidEnd A M`.
  Finite.of_injective (fun x ↦ ⇑(RingHom.kerLift (toAddMonoidEnd A M) x))
    (DFunLike.coe_injective.comp (RingHom.kerLift_injective _))

/-- A finitely generated module is finite iff the quotient of the ring by its annihilator is
finite. -/
theorem finite_iff_finite_quotient_annihilator [Module.Finite A M] :
    Finite M ↔ Finite (A ⧸ annihilator A M) := by
  refine ⟨fun _ ↦ finite_quotient_annihilator, fun _ ↦ ?_⟩
  -- Over a ring `M` is an additive group, which `quotientAnnihilator` needs.
  let := addCommMonoidToAddCommGroup A (M := M)
  let := quotientAnnihilator (R := A) (M := M)
  have : Module.Finite (A ⧸ annihilator A M) M := .of_restrictScalars_finite A _ M
  exact finite_of_finite (A ⧸ annihilator A M)

end Module

/-- A finite module over `R` has finite quotient by `J • M` when `R ⧸ J` is finite. -/
instance Submodule.finite_quotient_smul_top {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] (J : Ideal R) [Finite (R ⧸ J)] :
    Finite (M ⧸ (J • ⊤ : Submodule R M)) :=
  Module.finite_of_finite (R ⧸ J)
