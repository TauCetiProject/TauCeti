/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Balanced.Basic
public import TauCeti.LinearAlgebra.RootSystem.Dominance

/-!
# Integral root dominance under root-span projection

For a balanced root pairing `P`, the root-span projection `P.rootSpanProj` preserves integral root
dominance and reflects it on pairs with the same central component (`y - x ∈ P.rootSpan R`).

## Main results

* `RootPairing.rootLE_coe_rootSpanProj_of_rootLE` and
  `RootPairing.rootLE_coe_rootSpanProj_iff_of_sub_mem`: preservation and reflection of integral
  root dominance under `P.rootSpanProj`.

## References

* M. Rapoport, *A positivity property of the Satake isomorphism*, Manuscripta Math. 101 (2000),
  153–166, §1, equation (1.8), and §2.
-/

public section

namespace RootPairing

open TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N) [P.IsBalanced]

/-- Projecting onto the root span preserves integral root dominance. -/
theorem rootLE_coe_rootSpanProj_of_rootLE (b : P.Base) {x y : M} (h : P.rootLE b x y) :
    P.rootLE b (P.rootSpanProj x : M) (P.rootSpanProj y : M) := by
  have hmem := P.sub_mem_rootSpan_of_rootLE b h
  rw [rootLE_iff_sub_mem_posRootCone] at h ⊢
  simpa only [← Submodule.coe_sub, P.coe_rootSpanProj_sub_of_sub_mem hmem] using h

/-- For weights whose difference lies in the root span (that is, weights with the same central
component), integral root dominance after projecting onto the root span is equivalent to integral
root dominance of the original weights. -/
theorem rootLE_coe_rootSpanProj_iff_of_sub_mem (b : P.Base) {x y : M}
    (h : y - x ∈ P.rootSpan R) :
    P.rootLE b (P.rootSpanProj x : M) (P.rootSpanProj y : M) ↔ P.rootLE b x y := by
  rw [rootLE_iff_sub_mem_posRootCone, rootLE_iff_sub_mem_posRootCone, ← Submodule.coe_sub,
    P.coe_rootSpanProj_sub_of_sub_mem h]

end RootPairing
