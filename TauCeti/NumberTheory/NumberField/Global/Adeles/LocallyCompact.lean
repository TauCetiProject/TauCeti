/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.ProperAction.Basic
public import TauCeti.NumberTheory.NumberField.Global.Adeles.Discrete
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.LocallyCompact

/-!
# Local compactness of adeles and ideles

The adele ring of a number field is locally compact: its archimedean part is a finite product of
local fields, while its finite part is a restricted product with compact open integer rings.  The
idele group has the topology induced by `x ↦ (x, x⁻¹)`, so it inherits local compactness as the
unit group of the adele ring.

The diagonal subgroup of principal ideles is closed.  Indeed, its underlying adeles are exactly
the units lying in the closed diagonal copy of the number field.  Consequently the idele class
group is both locally compact and Hausdorff.

## Main results

* `NumberField.AdeleRing.instLocallyCompactSpace`: the full adele ring is locally compact.
* `NumberField.IdeleGroup.instLocallyCompactSpace`: the idele group is locally compact.
* `NumberField.IdeleGroup.isClosed_principalSubgroup`: the principal ideles form a closed subgroup.
* `NumberField.IdeleClassGroup.instLocallyCompactSpace` and
  `NumberField.IdeleClassGroup.instT2Space`: the idele class group is locally compact Hausdorff.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §14.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section
noncomputable section

open IsDedekindDomain
open scoped NumberField.AdeleRing

namespace NumberField

section LocalCompact

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [NumberField K] [Algebra R K] [IsFractionRing R K]
variable [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]

/-- The adele ring of a number field is locally compact. -/
instance AdeleRing.instLocallyCompactSpace : LocallyCompactSpace (AdeleRing R K) :=
  inferInstanceAs <| LocallyCompactSpace
    (InfiniteAdeleRing K × FiniteAdeleRing R K)

/-- The idele group of a number field is locally compact in its units topology. -/
instance IdeleGroup.instLocallyCompactSpace : LocallyCompactSpace (IdeleGroup R K) :=
  inferInstance

/-- The idele class group of a number field is locally compact. -/
instance IdeleClassGroup.instLocallyCompactSpace : LocallyCompactSpace (IdeleClassGroup R K) :=
  inferInstance

end LocalCompact

variable (K : Type*) [Field K] [NumberField K]

namespace IdeleGroup

/-- An idele is principal exactly when its underlying adele lies in the diagonal copy of the
number field. -/
@[simp]
theorem mem_principalSubgroup_iff (x : IdeleGroup (𝓞 K) K) :
    (∃ y : Kˣ, unitEmbedding (𝓞 K) K y = x) ↔
      (x : AdeleRing (𝓞 K) K) ∈ AdeleRing.principalSubgroup (𝓞 K) K := by
  let _ : Nontrivial (AdeleRing (𝓞 K) K) :=
    Function.Injective.nontrivial (AdeleRing.algebraMap_injective (𝓞 K) K)
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      intro hyzero
      subst y
      exact x.ne_zero (by simpa using hy.symm)
    refine ⟨Units.mk0 y hy0, Units.ext ?_⟩
    exact hy

/-- The principal ideles form a closed subgroup of the idele group. -/
theorem isClosed_principalSubgroup :
    IsClosed (principalSubgroup (𝓞 K) K : Set (IdeleGroup (𝓞 K) K)) := by
  have hset : (principalSubgroup (𝓞 K) K : Set (IdeleGroup (𝓞 K) K)) =
      (fun x : IdeleGroup (𝓞 K) K ↦ (x : AdeleRing (𝓞 K) K)) ⁻¹'
        (AdeleRing.principalSubgroup (𝓞 K) K : Set (AdeleRing (𝓞 K) K)) := by
    ext x
    change (∃ y : Kˣ, unitEmbedding (𝓞 K) K y = x) ↔ _
    exact mem_principalSubgroup_iff K x
  rw [hset]
  exact (TauCeti.GlobalNumberFields.isClosed_principalSubgroup K).preimage Units.continuous_val

end IdeleGroup

/-- The idele class group of a number field is Hausdorff. -/
instance IdeleClassGroup.instT2Space : T2Space (IdeleClassGroup (𝓞 K) K) := by
  let _ : IsClosed (IdeleGroup.principalSubgroup (𝓞 K) K : Set (IdeleGroup (𝓞 K) K)) :=
    IdeleGroup.isClosed_principalSubgroup K
  infer_instance

end NumberField
