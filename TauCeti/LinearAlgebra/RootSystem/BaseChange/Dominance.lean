/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Restrict.Base
public import TauCeti.LinearAlgebra.RootSystem.Dominance

/-!
# Integral root dominance under projection and scalar restriction

For a balanced root pairing `P`, the root-span projection `P.rootSpanProj` preserves integral root
dominance and reflects it on pairs with the same central component (`y - x ∈ P.rootSpan R`). Under
scalar restriction to a subfield `K`, membership in the positive root cone and integral root
dominance in `P.restrictScalars' K` agree with those in `P`.

## Main results

* `RootPairing.rootLE_coe_rootSpanProj_of_rootLE` and
  `RootPairing.rootLE_coe_rootSpanProj_iff_of_sub_mem`: preservation and reflection of integral
  root dominance under `P.rootSpanProj`.
* `RootPairing.mem_posRootCone_restrictScalars'_iff` and `RootPairing.rootLE_restrictScalars'_iff`:
  positive root cone and integral dominance in `P.restrictScalars' K` agree with those in `P`.
* `RootPairing.rootLE_restrictScalars'_self_rootSpanProj_of_rootLE` and
  `RootPairing.rootLE_restrictScalars'_self_rootSpanProj_iff_of_sub_mem`: the combined projection
  and same-field restriction compatibility.

## References

* M. Rapoport, *A positivity property of the Satake isomorphism*, Manuscripta Math. 101 (2000),
  153–166, §1, equation (1.8), and §2.
-/

public section

namespace RootPairing

open Set Submodule TauCeti

section RootSpanProj

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

end RootSpanProj

section RestrictScalars

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  (P : RootPairing ι L M N) (K : Type*) [Field K] [Algebra K L]
  [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  [P.IsBalanced] [P.IsValuedIn K]

/-- Membership in the positive root cone of `P.restrictScalars' K` agrees with membership in that
of `P`. -/
@[simp]
theorem mem_posRootCone_restrictScalars'_iff (b : P.Base) (x : span K (range P.root)) :
    x ∈ posRootCone (P.restrictScalars' K) (b.restrictScalars' K) ↔
      (x : M) ∈ posRootCone P b := by
  simp only [mem_posRootCone, Base.support_restrictScalars', Subtype.ext_iff,
    Submodule.coe_sum, AddSubmonoidClass.coe_nsmul, restrictScalars_coe_root]

/-- Integral root dominance in `P.restrictScalars' K` agrees with integral root dominance in `P`. -/
@[simp]
theorem rootLE_restrictScalars'_iff (b : P.Base) (x y : span K (range P.root)) :
    (P.restrictScalars' K).rootLE (b.restrictScalars' K) x y ↔
      P.rootLE b (x : M) (y : M) := by
  rw [rootLE_iff_sub_mem_posRootCone, rootLE_iff_sub_mem_posRootCone,
    mem_posRootCone_restrictScalars'_iff, Submodule.coe_sub]

end RestrictScalars

section SelfRestrictScalars

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  (P : RootPairing ι L M N) [P.IsBalanced] (b : P.Base)

/-- Integral root dominance in `P` implies integral root dominance of the root-span projections in
`P.restrictScalars' L`. -/
theorem rootLE_restrictScalars'_self_rootSpanProj_of_rootLE {x y : M} (h : P.rootLE b x y) :
    (P.restrictScalars' L).rootLE (b.restrictScalars' L) (P.rootSpanProj x) (P.rootSpanProj y) :=
  (P.rootLE_restrictScalars'_iff L b _ _).mpr (P.rootLE_coe_rootSpanProj_of_rootLE b h)

/-- For weights with the same central component (`y - x ∈ P.rootSpan L`), integral root dominance
of their projections in `P.restrictScalars' L` is equivalent to integral root dominance in `P`. -/
theorem rootLE_restrictScalars'_self_rootSpanProj_iff_of_sub_mem {x y : M}
    (h : y - x ∈ P.rootSpan L) :
    (P.restrictScalars' L).rootLE (b.restrictScalars' L) (P.rootSpanProj x) (P.rootSpanProj y) ↔
      P.rootLE b x y :=
  (P.rootLE_restrictScalars'_iff L b _ _).trans (P.rootLE_coe_rootSpanProj_iff_of_sub_mem b h)

end SelfRestrictScalars

end RootPairing
