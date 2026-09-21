/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Group.Units
public import TauCeti.NumberTheory.NumberField.Global.Adeles.Discrete

/-!
# Topology of the idele class group

The idele group of a number field is the unit group of its adele ring, equipped with the units
topology induced by `x ↦ (x, x⁻¹)`.  Since the adele ring is locally compact and Hausdorff, the
idele group is also locally compact and Hausdorff.

This file identifies the principal ideles inside the idele group as the inverse image of the
diagonal copy of the number field in the adele ring.  The latter is closed by adelic discreteness,
so the principal ideles are closed.  It follows that the idele class group is a locally compact
Hausdorff topological group.  Local compactness comes from Mathlib's instances for units and
quotients; the closedness result supplies the separation instance for the quotient.

## Main results

* `NumberField.IdeleGroup.mem_principalSubgroup_iff`: an idele is principal exactly when its
  underlying adele lies in the diagonal copy of the number field.
* `NumberField.IdeleGroup.isClosed_principalSubgroup`: the principal ideles form a closed subgroup.
* `NumberField.IdeleClassGroup.instT3Space`: the idele class group is Hausdorff and regular.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §16.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section
noncomputable section

open IsDedekindDomain
open scoped NumberField.AdeleRing

namespace NumberField.IdeleGroup

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- An idele is principal exactly when its underlying adele belongs to the diagonal copy of the
fraction field.  In the reverse direction, invertibility of the adele forces the diagonal element
to be nonzero, hence a field unit. -/
theorem mem_principalSubgroup_iff (x : IdeleGroup R K) :
    x ∈ principalSubgroup R K ↔
      (x : AdeleRing R K) ∈ AdeleRing.principalSubgroup R K := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨(u : K), rfl⟩
  · rintro ⟨k, hk⟩
    rcases subsingleton_or_nontrivial (AdeleRing R K) with h | h
    · let _ := h
      exact ⟨1, Subsingleton.elim _ _⟩
    let _ := h
    have hk0 : k ≠ 0 := by
      intro h
      subst k
      exact x.ne_zero hk.symm
    exact ⟨Units.mk0 k hk0, Units.ext hk⟩

/-- The subgroup of principal ideles is closed in the idele group. -/
theorem isClosed_principalSubgroup {K : Type*} [Field K] [NumberField K] :
    IsClosed (principalSubgroup (𝓞 K) K : Set (IdeleGroup (𝓞 K) K)) := by
  have hpreimage :
      (principalSubgroup (𝓞 K) K : Set (IdeleGroup (𝓞 K) K)) =
        ((fun x : IdeleGroup (𝓞 K) K => (x : AdeleRing (𝓞 K) K)) ⁻¹'
          (AdeleRing.principalSubgroup (𝓞 K) K : Set (AdeleRing (𝓞 K) K))) := by
    ext x
    exact mem_principalSubgroup_iff x
  rw [hpreimage]
  exact (TauCeti.GlobalNumberFields.isClosed_principalSubgroup K).preimage Units.continuous_val

end NumberField.IdeleGroup

namespace NumberField.IdeleClassGroup

variable (K : Type*) [Field K] [NumberField K]

/-- The idele class group of a number field is Hausdorff and regular. -/
noncomputable instance instT3Space : T3Space (IdeleClassGroup (𝓞 K) K) := by
  let _ : IsClosed
      (IdeleGroup.principalSubgroup (𝓞 K) K : Set (IdeleGroup (𝓞 K) K)) :=
    IdeleGroup.isClosed_principalSubgroup
  infer_instance

end NumberField.IdeleClassGroup
