/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.FieldTheory.PrimitiveElement

/-!
# Primitive elements inside a generating subspace

Let `E / F` be a finite separable extension and let `k` be an infinite subfield of `F`. If a
`k`-subspace `V` of `E` generates `E` over `F`, then some element of `V` alone generates `E` over
`F`: the primitive element can be chosen in `V`.

Indeed `E / F` has only finitely many intermediate fields, by the primitive element theorem. Each
proper one meets `V` in a proper `k`-subspace, since `V` generates `E`, and a vector space over an
infinite field is not a finite union of proper subspaces
(`Submodule.exists_forall_notMem_of_forall_ne_top`). An element of `V` outside all of them
generates `E`.

The typical use is a compositum `E = F F₂` of two subfields over a common infinite subfield `k`,
with `V` the image of `F₂`: some element of `F₂` is then a primitive element of `E / F`.

## Main results

* `Field.exists_mem_adjoin_simple_eq_top`: a primitive element of `E / F` can be chosen in any
  `k`-subspace that generates `E` over `F`.
-/

public section

open IntermediateField

namespace Field

variable (k : Type*) {F E : Type*} [Field k] [Field F] [Field E]
variable [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]

/-- **A primitive element inside a generating subspace.** If `E / F` is finite separable, `k ⊆ F`
is infinite, and the `k`-subspace `V` of `E` generates `E` over `F`, then `F⟮α⟯ = E` for some
`α ∈ V`. -/
theorem exists_mem_adjoin_simple_eq_top [Infinite k] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] {V : Submodule k E} (hV : adjoin F (V : Set E) = ⊤) :
    ∃ α ∈ V, F⟮α⟯ = ⊤ := by
  have : Finite (IntermediateField F E) :=
    finite_intermediateField_of_exists_primitive_element F E (exists_primitive_element F E)
  -- Each proper intermediate field meets `V` in a proper subspace.
  let p : {K : IntermediateField F E // K ≠ ⊤} → Submodule k V := fun K ↦
    ((K.1.restrictScalars k).toSubalgebra.toSubmodule).comap V.subtype
  have hp : ∀ K, p K ≠ ⊤ := fun K hK ↦ by
    refine K.2 (eq_top_iff.mpr (le_of_eq_of_le hV.symm (adjoin_le_iff.mpr fun x hx ↦ ?_)))
    have : (⟨x, hx⟩ : V) ∈ p K := by
      rw [hK]
      exact Submodule.mem_top
    exact this
  obtain ⟨α, hα⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  refine ⟨α, α.2, by_contra fun hne ↦ hα ⟨F⟮(α : E)⟯, hne⟩ ?_⟩
  exact mem_adjoin_simple_self F (α : E)

end Field
