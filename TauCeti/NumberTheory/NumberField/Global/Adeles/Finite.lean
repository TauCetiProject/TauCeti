/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Discrete
import TauCeti.Topology.Algebra.Group.Cocompact

/-!
# Rational points in compact adelic sets

A compact set of adeles contains only finitely many elements of the diagonally embedded
number field. The same holds for tuples of any fixed finite size. This permits finiteness
arguments for rational lattices after applying an adelic change of coordinates.
-/

public section

open NumberField Set
open scoped NumberField.AdeleRing

namespace NumberField.AdeleRing

variable {K : Type*} [Field K] [NumberField K]

/-- A compact set of adeles contains only finitely many rational points. -/
theorem finite_preimage_algebraMap {S : Set 𝔸[K]} (hS : IsCompact S) :
    ((algebraMap K 𝔸[K]) ⁻¹' S).Finite := by
  let f : K → AdeleRing.principalSubgroup (𝓞 K) K :=
    fun x ↦ ⟨algebraMap K 𝔸[K] x, ⟨x, rfl⟩⟩
  have hf : Function.Injective f := fun x y h ↦
    (AdeleRing.algebraMap_injective (𝓞 K) K) (congrArg Subtype.val h)
  have h := (AdeleRing.principalSubgroup (𝓞 K) K).finite_preimage_coe_of_isCompact hS
  exact h.preimage (f := f) hf.injOn

/-- A compact set of adelic tuples contains only finitely many rational tuples. -/
theorem finite_preimage_algebraMap_pi {ι : Type*} [Finite ι] {S : Set (ι → 𝔸[K])}
    (hS : IsCompact S) : {x : ι → K | (fun i ↦ algebraMap K 𝔸[K] (x i)) ∈ S}.Finite := by
  have h (i : ι) : {x : K | algebraMap K 𝔸[K] x ∈ (fun z : ι → 𝔸[K] ↦ z i) '' S}.Finite :=
    finite_preimage_algebraMap (hS.image (continuous_apply i))
  exact (Set.Finite.pi h).subset fun x hx i _ ↦ ⟨_, hx, rfl⟩

end NumberField.AdeleRing
