/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Basic

/-!
# Weight spaces are invariants of a representation of `GL n k`

An equivalence of representations of `GL n k` carries the weight space of each weight
`l : Fin n → ℤ` onto the weight space of the same weight.  One inclusion holds for any equivariant
map and is `Representation.IntertwiningMap.apply_mem_weightSpace`, because a weight space is a
joint eigenspace of the diagonal torus and an equivariant map takes an eigenvector of
`ρ (diagGL t)` to an eigenvector of `σ (diagGL t)` with the same eigenvalue; an equivalence has an
inverse, so for it the inclusion is an equality.

Consequently a weight occurring in one of two equivalent representations occurs in the other,
which is what makes the set of weights — and so the highest weight — an invariant of the
equivalence class rather than of the chosen carrier.  The Lie-theoretic counterpart is
`LieModule.map_genWeightSpace_eq`.

## Main results

* `Representation.Equiv.apply_mem_weightSpace_iff`: an equivalence of representations reflects
  membership in a weight space.
* `Representation.Equiv.map_weightSpace`: it maps the weight space of `l` **onto** that of `l`.
* `Representation.Equiv.weightSpace_eq_bot_iff`: hence a weight occurs in one representation
  exactly when it occurs in the other.

## Implementation notes

`TauCeti.weightSpace` asks for an additive *group*, so the carriers below are additive groups,
while a subrepresentation carries the additive *monoid* structure of a submodule.  As for
`TauCeti.weightSpace` itself, an application to subrepresentations therefore has to name the
carriers, as in `Representation.Equiv.weightSpace_eq_bot_iff (V := _) (W := _) φ`: the elaborator
will not invert `AddCommGroup.toAddCommMonoid` while a carrier is still a metavariable, and naming
the carriers lets instance search produce the group structures first.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open Matrix TauCeti

namespace Representation

universe u v w

variable {k : Type u} [CommRing k] {n : ℕ}
variable {V : Type v} [AddCommGroup V] [Module k V]
variable {W : Type w} [AddCommGroup W] [Module k W]
variable {ρ : Representation k (GL (Fin n) k) V} {σ : Representation k (GL (Fin n) k) W}

namespace Equiv

/-- **An equivalence of representations of `GL n k` reflects weight spaces**: a vector lies in the
weight space of `l` exactly when its image does.  Preservation is
`Representation.IntertwiningMap.apply_mem_weightSpace`, applied to the equivalence and to its
inverse. -/
theorem apply_mem_weightSpace_iff (φ : ρ.Equiv σ) (l : Fin n → ℤ) (v : V) :
    φ v ∈ weightSpace σ l ↔ v ∈ weightSpace ρ l := by
  refine ⟨fun h ↦ ?_, fun h ↦ φ.toIntertwiningMap.apply_mem_weightSpace h⟩
  simpa only [coe_toIntertwiningMap, symm_apply_apply] using
    φ.symm.toIntertwiningMap.apply_mem_weightSpace h

/-- **An equivalence of representations of `GL n k` maps each weight space onto the weight space
of the same weight.** -/
@[simp]
theorem map_weightSpace (φ : ρ.Equiv σ) (l : Fin n → ℤ) :
    (weightSpace ρ l).map φ.toLinearMap = weightSpace σ l := by
  refine le_antisymm (φ.toIntertwiningMap.map_weightSpace_le l) fun w hw ↦ ?_
  have hsymm : φ.symm w ∈ weightSpace ρ l := by
    rw [← φ.apply_mem_weightSpace_iff l (φ.symm w)]
    simpa only [apply_symm_apply] using hw
  exact Submodule.mem_map.mpr ⟨φ.symm w, hsymm, by simp⟩

/-- **A weight occurs in one of two equivalent representations of `GL n k` exactly when it occurs
in the other.** -/
theorem weightSpace_eq_bot_iff (φ : ρ.Equiv σ) (l : Fin n → ℤ) :
    weightSpace σ l = ⊥ ↔ weightSpace ρ l = ⊥ := by
  rw [← φ.map_weightSpace l]
  exact Submodule.map_eq_bot_iff (e := φ.toLinearEquiv)

end Equiv

end Representation
