/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Basic
public import TauCeti.RingTheory.Subring.ResidueClass

/-!
# Topology of residue classes over a subring

Compactness passes from a subring `R` of a topological ring to each class
`R.residueClass g x₀ = x₀ + g R^ι`; for finite `ι`, openness passes as well.
-/

public section

namespace Subring

variable {A ι : Type*} [Ring A] (R : Subring A) [TopologicalSpace A] [IsTopologicalRing A]

/-- A class of a compact subring is compact. -/
theorem isCompact_residueClass (hR : IsCompact (R : Set A)) (g : Aˣ) (x₀ : ι → A) :
    IsCompact (R.residueClass g x₀) := by
  rw [R.residueClass_eq_pi]
  exact isCompact_univ_pi fun i ↦ hR.image (by fun_prop)

/-- A class of an open subring is open. -/
theorem isOpen_residueClass [Finite ι] (hR : IsOpen (R : Set A)) (g : Aˣ) (x₀ : ι → A) :
    IsOpen (R.residueClass g x₀) := by
  have heq : R.residueClass g x₀ =
      ⋂ i, (fun x : ι → A ↦ (↑g⁻¹ : A) * (x i - x₀ i)) ⁻¹' (R : Set A) := by
    ext x
    simp
  rw [heq]
  exact isOpen_iInter_of_finite fun i ↦ hR.preimage (by fun_prop)

end Subring
