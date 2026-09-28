/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.InertiaDegree

/-!
# Total ramification of a local-field extension

An extension of nonarchimedean local fields is totally ramified when its ramification index is
its degree. The fundamental identity `e · f = [L : K]` identifies this with residue degree one.
The latter criterion makes total ramification usable in towers and in calculations with norms.

The residue extension of a totally ramified extension can still be nontrivial as a field map;
its degree is one, so the map is an isomorphism.

## Main results

* `TauCeti.IsTotallyRamified`: the intrinsic total-ramification predicate.
* `TauCeti.isTotallyRamified_iff_inertiaDegree_eq_one`: the residue-degree criterion.
* `TauCeti.isTotallyRamified_tower_iff`: total ramification is equivalent to total ramification
  of both steps of a tower.

## References

* J.-P. Serre, *Corps Locaux*, Chapter I, §4.
-/

public section
noncomputable section

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- A compatible extension of nonarchimedean local fields is totally ramified when its
residue degree is one. Equivalently, its ramification index equals its degree. Such an
extension is finite by `finite_of_valuativeExtension`. -/
def IsTotallyRamified (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] : Prop :=
  inertiaDegree K L = 1

/-- Total ramification is equivalent to the ramification index equaling the degree. -/
theorem isTotallyRamified_def :
    IsTotallyRamified K L ↔ ramificationIndex K L = Module.finrank K L := by
  constructor
  · intro h
    rw [← ramificationIndex_mul_inertiaDegree, show inertiaDegree K L = 1 from h, mul_one]
  · intro h
    rw [← ramificationIndex_mul_inertiaDegree] at h
    exact Nat.eq_of_mul_eq_mul_left ramificationIndex_pos (by simpa using h.symm)

/-- A finite local-field extension is totally ramified exactly when its residue degree is one. -/
theorem isTotallyRamified_iff_inertiaDegree_eq_one :
    IsTotallyRamified K L ↔ inertiaDegree K L = 1 := Iff.rfl

/-- The residue degree of a totally ramified extension is one. -/
@[simp]
theorem IsTotallyRamified.inertiaDegree_eq_one (h : IsTotallyRamified K L) :
    inertiaDegree K L = 1 :=
  isTotallyRamified_iff_inertiaDegree_eq_one.mp h

section Tower

variable (K L) (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension L M] [ValuativeExtension K M]

/-- A tower is totally ramified exactly when both of its steps are totally ramified. -/
theorem isTotallyRamified_tower_iff :
    IsTotallyRamified K M ↔ IsTotallyRamified K L ∧ IsTotallyRamified L M := by
  simp only [IsTotallyRamified, inertiaDegree_tower (K := K) (L := L) M, mul_eq_one]

/-- Total ramification is transitive in a tower. -/
theorem IsTotallyRamified.trans (hKL : IsTotallyRamified K L)
    (hLM : IsTotallyRamified L M) : IsTotallyRamified K M :=
  (isTotallyRamified_tower_iff K L M).2 ⟨hKL, hLM⟩

/-- The first step of a totally ramified tower is totally ramified. -/
theorem IsTotallyRamified.tower_bot (hKM : IsTotallyRamified K M) :
    IsTotallyRamified K L :=
  ((isTotallyRamified_tower_iff K L M).1 hKM).1

/-- The second step of a totally ramified tower is totally ramified. -/
theorem IsTotallyRamified.tower_top (hKM : IsTotallyRamified K M) :
    IsTotallyRamified L M :=
  ((isTotallyRamified_tower_iff K L M).1 hKM).2

end Tower

end TauCeti
