/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Balanced.Basic
public import TauCeti.LinearAlgebra.RootSystem.Chamber

/-!
# Regular weights and dominant chambers under root-span projection

For a balanced root pairing `P`, projecting onto `P.rootSpan R` via `P.rootSpanProj` preserves and
reflects weight regularity and membership in the closed and open dominant chambers.

## Main results

* `RootPairing.isRegularWeight_coe_rootSpanProj_iff`,
  `RootPairing.coe_rootSpanProj_mem_dominantChamber_iff`, and
  `RootPairing.coe_rootSpanProj_mem_openDominantChamber_iff`: `rootSpanProj` preserves and reflects
  regularity and membership in the closed and open dominant chambers.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §§1, 6.
-/

public section

namespace RootPairing

open TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N) [P.IsBalanced]

/-- Projecting onto the root span preserves and reflects weight regularity. -/
@[simp]
theorem isRegularWeight_coe_rootSpanProj_iff (x : M) :
    P.IsRegularWeight (P.rootSpanProj x : M) ↔ P.IsRegularWeight x := by
  simp only [isRegularWeight_iff, LinearMap.flip_apply, toLinearMap_coe_rootSpanProj_coroot]

-- Not `@[simp]`: `mem_dominantChamber` is `@[simp]`, so `simp` unfolds the LHS to
-- `∀ i ∈ b.support, 0 ≤ P.toLinearMap (P.rootSpanProj x : M) (P.coroot i)` and closes the
-- equivalence via `toLinearMap_coe_rootSpanProj_coroot` (`simpNF`).
/-- Projecting onto the root span preserves and reflects membership in the closed dominant
chamber. -/
theorem coe_rootSpanProj_mem_dominantChamber_iff [Preorder R] (b : P.Base) (x : M) :
    (P.rootSpanProj x : M) ∈ dominantChamber P b ↔ x ∈ dominantChamber P b := by
  simp only [mem_dominantChamber, LinearMap.flip_apply, toLinearMap_coe_rootSpanProj_coroot]

-- Not `@[simp]`: `mem_openDominantChamber` is `@[simp]`, so `simp` unfolds the LHS and closes
-- the equivalence via `toLinearMap_coe_rootSpanProj_coroot` (`simpNF`).
/-- Projecting onto the root span preserves and reflects membership in the open dominant
chamber. -/
theorem coe_rootSpanProj_mem_openDominantChamber_iff [Preorder R] (b : P.Base) (x : M) :
    (P.rootSpanProj x : M) ∈ openDominantChamber P b ↔ x ∈ openDominantChamber P b := by
  simp only [mem_openDominantChamber, LinearMap.flip_apply, toLinearMap_coe_rootSpanProj_coroot]

end RootPairing
