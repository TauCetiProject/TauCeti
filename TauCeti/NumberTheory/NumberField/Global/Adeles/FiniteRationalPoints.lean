/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Discrete
import TauCeti.Topology.Algebra.Group.Cocompact

/-!
# Rational points in compact sets of adeles

Let `K` be a number field with adele ring `𝔸[K]`. As the diagonal copy of `K` is a discrete
subgroup of `𝔸[K]` (`TauCeti.GlobalNumberFields.discreteTopology_principalSubgroup`), a compact
set of adeles contains only finitely many elements of `K`, and a compact set of adelic vectors
`ι → 𝔸[K]`, for a finite index type `ι`, contains only finitely many vectors of `K^ι`.

This is how lattice counts over a number field are shown to be finite: a condition at the finite
places that confines the finite adeles to a compact set, such as integrality with respect to an
adelic lattice, together with a bound at every infinite place, cuts out a compact set of adeles.

## Main results

* `TauCeti.GlobalNumberFields.finite_preimage_algebraMap_of_isCompact`: a compact set of adeles
  contains finitely many elements of `K`.
* `TauCeti.GlobalNumberFields.finite_setOf_comp_mem_of_isCompact`: a compact set of adelic
  vectors contains finitely many rational vectors.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §14.
-/

public section

open NumberField
open scoped NumberField.AdeleRing

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **A compact set of adeles contains finitely many elements of the number field**, as the
diagonal copy of `K` is a discrete subgroup of `𝔸[K]`. -/
theorem finite_preimage_algebraMap_of_isCompact {s : Set 𝔸[K]} (hs : IsCompact s) :
    (algebraMap K 𝔸[K] ⁻¹' s).Finite := by
  -- `x ↦ algebraMap x` is an injection `f` of `K` into the principal subgroup, whose points in
  -- `s` form a finite set; the preimage of that set under `f` is `algebraMap ⁻¹' s` by definition
  -- of `f`.
  let f : K → AdeleRing.principalSubgroup (𝓞 K) K := fun x ↦ ⟨algebraMap K 𝔸[K] x, x, rfl⟩
  have hf : Function.Injective f := fun x y h ↦
    AdeleRing.algebraMap_injective (𝓞 K) K (congrArg Subtype.val h)
  exact ((AdeleRing.principalSubgroup (𝓞 K) K).finite_preimage_coe_of_isCompact hs).preimage
    (f := f) hf.injOn

/-- **A compact set of adelic vectors contains finitely many rational vectors**: for a finite
index type `ι`, only finitely many `x : ι → K` have their diagonal image in a compact set
`s ⊆ ι → 𝔸[K]`. -/
theorem finite_setOf_comp_mem_of_isCompact {ι : Type*} [Finite ι] {s : Set (ι → 𝔸[K])}
    (hs : IsCompact s) : {x : ι → K | algebraMap K 𝔸[K] ∘ x ∈ s}.Finite := by
  refine (Set.Finite.pi' fun i ↦ finite_preimage_algebraMap_of_isCompact
    (hs.image (continuous_apply i))).subset fun x hx i ↦ ?_
  exact ⟨_, hx, rfl⟩

end TauCeti.GlobalNumberFields
