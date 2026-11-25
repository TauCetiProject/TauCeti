/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Semisimple
public import TauCeti.RepresentationTheory.Subrepresentation

/-!
# Nontrivial extensions of trivial representations are not semisimple

If a monoid acts trivially on a subrepresentation `W` and on the quotient by `W`, and the
representation is semisimple, then the monoid acts trivially on the whole representation
(`Representation.apply_eq_self_of_isSemisimpleRepresentation`): an invariant complement of `W`
maps isomorphically onto the quotient, so the action on it is trivial too. A nontrivial extension
of a trivial representation by a trivial one, such as the action of `(1 a; 0 1)` with `a ≠ 0` on
`k²`, is therefore never semisimple (`Representation.not_isSemisimpleRepresentation_of_apply_ne`).

Both rest on `Subrepresentation.apply_eq_self_of_disjoint`: a vector `c` of a subrepresentation
`C` disjoint from `W` with `ρ g c - c ∈ W` is fixed by `ρ g`. The same step shows that the
regular representation in modular characteristic is not semisimple
(`Representation.not_isSemisimpleRepresentation_leftRegular`, in
`TauCeti.RepresentationTheory.Augmentation.Semisimple`).

These are the non-examples showing that the invertible-index hypotheses in the relative Maschke
theorem (`Representation.isSemisimpleRepresentation_of_comp_subtype`) and in the restriction
theorems of `TauCeti.RepresentationTheory.Semisimple.Restriction` cannot be dropped.
-/

public section

namespace Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- **A semisimple extension of trivial representations is trivial.** If `G` acts trivially on a
subrepresentation `W` of a semisimple representation `ρ` and on the quotient `V ⧸ W` (that is,
`ρ g v - v ∈ W` for all `g` and `v`), then `G` acts trivially on `V`. -/
theorem apply_eq_self_of_isSemisimpleRepresentation {ρ : Representation k G V}
    [ρ.IsSemisimpleRepresentation] (W : Subrepresentation ρ) (hW : ∀ g, ∀ w ∈ W, ρ g w = w)
    (hV : ∀ g v, ρ g v - v ∈ W) (g : G) (v : V) : ρ g v = v := by
  obtain ⟨C, hC⟩ := exists_isCompl W
  have hC' := Subrepresentation.isCompl_toSubmodule.2 hC
  obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.1 (hC'.sup_eq_top ▸ Submodule.mem_top (x := v))
  rw [map_add, hW g w hw, Subrepresentation.apply_eq_self_of_disjoint hC.disjoint hc (hV g c)]

/-- **A nontrivial extension of a trivial representation by a trivial one is not semisimple.**
If `G` acts trivially on a subrepresentation `W` and on `V ⧸ W`, but some `ρ g` moves some vector,
then `ρ` is not semisimple. -/
theorem not_isSemisimpleRepresentation_of_apply_ne {ρ : Representation k G V}
    (W : Subrepresentation ρ) (hW : ∀ g, ∀ w ∈ W, ρ g w = w)
    (hV : ∀ g v, ρ g v - v ∈ W) {g : G} {v : V} (hgv : ρ g v ≠ v) :
    ¬ ρ.IsSemisimpleRepresentation := fun _ ↦
  hgv (apply_eq_self_of_isSemisimpleRepresentation W hW hV g v)

end Representation
