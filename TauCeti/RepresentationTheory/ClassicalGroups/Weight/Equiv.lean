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
`l : Fin n → ℤ` onto the weight space of the same weight, because a weight space is a joint
eigenspace of the diagonal torus and an equivariant map takes an eigenvector of `ρ (diagGL t)` to
an eigenvector of `σ (diagGL t)` with the same eigenvalue.

Consequently a weight occurring in one of two equivalent representations occurs in the other,
which is what makes the set of weights — and so the highest weight — an invariant of the
equivalence class rather than of the chosen carrier.  The Lie-theoretic counterpart is
`LieModule.map_weightSpace_eq`.

## Main results

* `Representation.Equiv.apply_mem_weightSpace` and
  `Representation.Equiv.apply_mem_weightSpace_iff`: an equivalence of representations preserves
  and reflects membership in a weight space.
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

/-- **An equivalence of representations of `GL n k` preserves weight spaces.** A weight vector is
an eigenvector of every `ρ (diagGL t)`, and an equivariant map sends it to an eigenvector of
`σ (diagGL t)` for the same eigenvalue. -/
theorem apply_mem_weightSpace (φ : ρ.Equiv σ) {l : Fin n → ℤ} {v : V}
    (hv : v ∈ weightSpace ρ l) : φ v ∈ weightSpace σ l := by
  rw [mem_weightSpace_iff]
  intro t
  have h := LinearMap.congr_fun (φ.isIntertwining' (diagGL t)) v
  simp only [LinearMap.coe_comp, Function.comp_apply, Equiv.coe_toLinearMap] at h
  rw [← h, apply_of_mem_weightSpace hv t, map_smul]

/-- **An equivalence of representations of `GL n k` reflects weight spaces**: a vector lies in the
weight space of `l` exactly when its image does. -/
theorem apply_mem_weightSpace_iff (φ : ρ.Equiv σ) (l : Fin n → ℤ) (v : V) :
    φ v ∈ weightSpace σ l ↔ v ∈ weightSpace ρ l := by
  refine ⟨fun h ↦ ?_, fun h ↦ φ.apply_mem_weightSpace h⟩
  simpa only [Equiv.symm_apply_apply] using φ.symm.apply_mem_weightSpace h

/-- **An equivalence of representations of `GL n k` maps each weight space onto the weight space
of the same weight.** -/
theorem map_weightSpace (φ : ρ.Equiv σ) (l : Fin n → ℤ) :
    (weightSpace ρ l).map φ.toLinearMap = weightSpace σ l := by
  refine le_antisymm ?_ fun w hw ↦ ?_
  · rintro w ⟨v, hv, rfl⟩
    exact φ.apply_mem_weightSpace hv
  · have hsymm : φ.symm w ∈ weightSpace ρ l := by
      rw [← φ.apply_mem_weightSpace_iff l (φ.symm w)]
      simpa only [Equiv.apply_symm_apply] using hw
    exact Submodule.mem_map.mpr ⟨φ.symm w, hsymm, by simp⟩

/-- **A weight occurs in one of two equivalent representations of `GL n k` exactly when it occurs
in the other.** -/
theorem weightSpace_eq_bot_iff (φ : ρ.Equiv σ) (l : Fin n → ℤ) :
    weightSpace σ l = ⊥ ↔ weightSpace ρ l = ⊥ := by
  rw [← φ.map_weightSpace l]
  exact Submodule.map_eq_bot_iff (e := φ.toLinearEquiv)

end Equiv

end Representation
