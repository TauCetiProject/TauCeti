/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.LinearAlgebra.End.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas
import TauCeti.LinearAlgebra.Quotient.Nilpotent

/-!
# Unipotent operators on quotient representations

Let `p` be a subrepresentation of a representation `rho`. The operator `rho.quotient p hp g - 1`
on the quotient is induced by `rho g - 1` (`Representation.quotient_sub_one_eq_mapQ`).

## Main declarations

* `Representation.isNilpotent_quotient_sub_one`: unipotent operators stay unipotent on the
  quotient by an invariant submodule.
* `Representation.isNilpotent_sub_one_of_quotient`: an operator that is unipotent on the quotient
  by an invariant submodule fixed pointwise by that operator is unipotent.
-/

public section

namespace TauCeti

variable {R G V : Type*} [Ring R] [Monoid G] [AddCommGroup V] [Module R V]

/-- On the quotient by an invariant submodule `p`, the operator `rho.quotient p hp g - 1` is
induced by `rho g - 1` via `Submodule.mapQ`. -/
theorem _root_.Representation.quotient_sub_one_eq_mapQ (rho : Representation R G V)
    (p : Submodule R V) (hp : ∀ g, p ≤ p.comap (rho g)) (g : G) :
    rho.quotient p hp g - 1 = p.mapQ p (rho g - 1) ((Module.End.mem_invtSubmodule _).1
      (Module.End.invtSubmodule_inf_invtSubmodule_le_invtSubmodule_sub (rho g) 1
        ⟨hp g, fun _ hx ↦ hx⟩)) := by
  ext x
  simp [Representation.quotient_apply, Submodule.mapQ_apply]

/-- If `rho g - 1` is nilpotent, then so is the operator `rho.quotient p hp g - 1` induced on the
quotient of the representation `rho` by an invariant submodule `p`. -/
theorem _root_.Representation.isNilpotent_quotient_sub_one (rho : Representation R G V)
    (p : Submodule R V) (hp : ∀ g, p ≤ p.comap (rho g)) {g : G}
    (hg : IsNilpotent (rho g - 1)) : IsNilpotent (rho.quotient p hp g - 1) := by
  rw [rho.quotient_sub_one_eq_mapQ p hp g]
  exact Module.End.IsNilpotent.mapQ _ hg

/-- If an element acts unipotently on the quotient by an invariant submodule that it fixes
pointwise, then it acts unipotently on the whole space. -/
theorem _root_.Representation.isNilpotent_sub_one_of_quotient
    (rho : Representation R G V) (p : Submodule R V) (hp : ∀ g, p ≤ p.comap (rho g))
    {g : G} (hfix : ∀ y ∈ p, rho g y = y) (hn : IsNilpotent (rho.quotient p hp g - 1)) :
    IsNilpotent (rho g - 1) := by
  refine p.isNilpotent_of_isNilpotent_restrict_of_isNilpotent_mapQ (rho g - 1)
    ((Module.End.mem_invtSubmodule _).1
      (Module.End.invtSubmodule_inf_invtSubmodule_le_invtSubmodule_sub (rho g) 1
        ⟨hp g, fun _ hx ↦ hx⟩)) ?_ ?_
  · convert IsNilpotent.zero
    ext y
    simp [hfix y y.2]
  · rwa [rho.quotient_sub_one_eq_mapQ p hp g] at hn

end TauCeti
