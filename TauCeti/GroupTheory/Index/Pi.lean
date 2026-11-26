/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index

/-!
# Finite index for product subgroups

For a family of subgroups `H : ∀ i, Subgroup (G i)` and a finite set of coordinates `I : Set ι`, the
product subgroup `Subgroup.pi I H` (and its additive counterpart `AddSubgroup.pi I H`) has finite
index in `∀ i, G i` whenever `H i` has finite index for each `i ∈ I`. In particular, for a
finite-index subring `S ≤ R` and a finite type `ι`, the lattice `S^ι` has finite additive index in
`R^ι`.

## Main results

* `Subgroup.instFiniteIndexPi`, `AddSubgroup.instFiniteIndexPi`: `Subgroup.pi I H` has finite index
  whenever `I` is finite and `H i` has finite index for each `i ∈ I`.
-/

public section

namespace Subgroup

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]

/-- A product subgroup constrained on finitely many coordinates by finite-index subgroups has
finite index. -/
@[to_additive
/-- A product additive subgroup constrained on finitely many coordinates by finite-index additive
subgroups has finite index. -/]
instance instFiniteIndexPi (I : Set ι) [Finite I] (H : ∀ i, Subgroup (G i))
    [∀ i : I, (H i.val).FiniteIndex] : (Subgroup.pi I H).FiniteIndex := by
  have hpi : Subgroup.pi I H = ⨅ i : I, (H i.val).comap (Pi.evalMonoidHom G i.val) := by
    ext x
    simp [Subgroup.mem_pi]
  rw [hpi]
  exact finiteIndex_iInf fun i ↦ inferInstance

end Subgroup
