/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Restrict.Basic
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Basic

/-!
# Root-orbit sums under scalar restriction

This file shows that root orbits, root-orbit sums, and the set of folded root-orbit sums under a
restricted automorphism `σ.restrictScalars' K` in `P.restrictScalars' K` coincide with those of
`σ` in `P`.

## Main results

* `RootPairing.orbitIndices_restrictScalars'`, `RootPairing.coe_orbitSum_restrictScalars'`, and
  `RootPairing.image_subtype_foldedIndices_restrictScalars'`: root orbits, root-orbit sums, and
  folded root-orbit sums under a restricted automorphism agree with those in the ambient pairing.

## References

* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, page 1.
-/

public section

namespace RootPairing

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  (P : RootPairing ι L M N) [Finite ι] (K : Type*) [Field K] [Algebra K L]
  [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  [P.IsBalanced] [P.IsValuedIn K] (σ : P.Aut)

/-- Root orbits under a restricted automorphism in `P.restrictScalars' K` coincide with those in
`P`. -/
@[simp]
theorem orbitIndices_restrictScalars' (i : ι) :
    (P.restrictScalars' K).orbitIndices (σ.restrictScalars' K) i =
      P.orbitIndices σ i := by
  ext j
  rw [mem_orbitIndices, mem_orbitIndices, Equiv.indexEquiv_restrictScalars']

/-- Each root-orbit sum in `P.restrictScalars' K` coerces to the corresponding root-orbit sum in
`P`. -/
@[simp]
theorem coe_orbitSum_restrictScalars' (i : ι) :
    ((P.restrictScalars' K).orbitSum (σ.restrictScalars' K) i : M) =
      P.orbitSum σ i := by
  simp only [orbitSum_def, orbitIndices_restrictScalars', Submodule.coe_sum,
    restrictScalars_coe_root]

/-- The set of folded root-orbit sums in `P.restrictScalars' K` maps under coercion onto
`P.foldedIndices σ`. -/
@[simp]
theorem image_subtype_foldedIndices_restrictScalars' :
    Subtype.val '' (P.restrictScalars' K).foldedIndices (σ.restrictScalars' K) =
      P.foldedIndices σ := by
  ext x
  simp only [Set.mem_image, mem_foldedIndices]
  refine ⟨?_, fun ⟨i, hi⟩ ↦ ⟨_, ⟨i, rfl⟩, (P.coe_orbitSum_restrictScalars' K σ i).trans hi⟩⟩
  rintro ⟨_, ⟨i, rfl⟩, rfl⟩
  exact ⟨i, (P.coe_orbitSum_restrictScalars' K σ i).symm⟩

end RootPairing
