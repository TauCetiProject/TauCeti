/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Delineation
import Mathlib.Topology.Connected.Clopen

/-!
# Continuous selections from a delineation

A continuous root of a non-nullified member of a delineated polynomial family on a connected
base chooses one fixed root section. Multiplicities and roots shared by different family
members cause no difficulty: the delineation labels distinct roots, not roots with multiplicity.
This is the root-selection step for semialgebraicity of continuous algebraic functions.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998, Section 8.1.
-/

public section

open Set Topology
open scoped Polynomial

namespace TauCeti.Delineation

variable {X ι : Type*} [TopologicalSpace X] [ConnectedSpace X]
  {P : ι → X → ℝ[X]}

/-- A continuous root of a member that is nowhere nullified on a connected base is one fixed
section of its delineation. Repeated roots are allowed. -/
theorem exists_eq_root_of_continuous (D : Delineation P) {k : ι} {f : X → ℝ}
    (hf : Continuous f) (hne : ∀ x, P k x ≠ 0) (hroot : ∀ x, (P k x).IsRoot (f x)) :
    ∃ i, f = D.root i := by
  classical
  have hcover (x : X) : ∃ i, D.root i x = f x := D.exists_root_eq k x (hne x) _ (hroot x)
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  obtain ⟨i, hi⟩ := hcover x₀
  have hclosed (j : Fin D.count) : IsClosed {x | D.root j x = f x} :=
    isClosed_eq (D.continuous_root j) hf
  have hcompl : {x | D.root i x = f x}ᶜ = ⋃ j : {j : Fin D.count // j ≠ i},
      {x | D.root j.1 x = f x} := by
    ext x
    simp only [mem_compl_iff, mem_ofPred_eq, mem_iUnion, Subtype.exists, exists_prop]
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := hcover x
      exact ⟨j, fun hji ↦ hx (hji ▸ hj), hj⟩
    · rintro ⟨j, hji, hj⟩ hi'
      exact hji ((D.strictMono_root x).injective (hj.trans hi'.symm))
  have hclopen : IsClopen {x | D.root i x = f x} := by
    refine ⟨hclosed i, ?_⟩
    rw [← isClosed_compl_iff, hcompl]
    exact isClosed_iUnion_of_finite fun j ↦ hclosed j.1
  have hall := hclopen.eq_univ ⟨x₀, hi⟩
  exact ⟨i, funext fun x ↦ (eq_univ_iff_forall.mp hall x).symm⟩

end TauCeti.Delineation
