/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Images of submodules in a quotient

A class `[x]` of `M ⧸ p` lies in the image of a submodule `p'` containing `p` exactly when
`x ∈ p'` (`Submodule.Quotient.mk_mem_map_mkQ_iff`). This is membership in the image of
`p'` under the quotient map, read off from Mathlib's `Submodule.comap_map_mkQ`; it identifies
subspaces of a quotient through their representatives, as in the linear symplectic reduction of
a subspace of a reduced space.

For an ideal `I`, the class `[x]` lies in `I (M ⧸ p)` exactly when `x ∈ p + I M`
(`Submodule.Quotient.mk_mem_smul_top_iff`), since `I (M ⧸ p)` is the image of `I M`.

For an `R ⧸ K`-module, membership in the image ideal times the module can be checked over `R`
(`Submodule.mem_map_quotient_mk_smul_top_iff`). In `M ⧸ K • M`, this also gives a criterion on
representatives when `K ≤ J` (`Submodule.Quotient.mk_mem_map_quotient_mk_smul_top_iff`).
-/

public section

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The class of `x` in `M ⧸ p` lies in the image of a submodule `p'` containing `p` exactly when
`x ∈ p'`. -/
theorem Quotient.mk_mem_map_mkQ_iff {p p' : Submodule R M} (h : p ≤ p') (x : M) :
    (Quotient.mk x : M ⧸ p) ∈ p'.map p.mkQ ↔ x ∈ p' := by
  rw [← mkQ_apply, ← mem_comap, comap_map_mkQ, sup_eq_right.2 h]

/-- The class of `x` in `M ⧸ p` lies in `I (M ⧸ p)` exactly when `x ∈ p + I M`. -/
@[simp]
theorem Quotient.mk_mem_smul_top_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {p : Submodule R M} {I : Ideal R} {x : M} :
    (Quotient.mk x : M ⧸ p) ∈ I • (⊤ : Submodule R (M ⧸ p)) ↔ x ∈ p ⊔ I • ⊤ := by
  rw [← map_top p.mkQ |>.trans (range_mkQ p), ← map_smul'', ← comap_map_mkQ, mem_comap,
    mkQ_apply]

/-- Multiples of the image of `J` in an `R ⧸ K`-module are the multiples of `J` under the
compatible `R`-action. -/
theorem mem_map_quotient_mk_smul_top_iff {S P : Type*} [CommRing S] [AddCommMonoid P]
    (J K : Ideal S) [Module S P] [Module (S ⧸ K) P] [IsScalarTower S (S ⧸ K) P] {y : P} :
    y ∈ J.map (Ideal.Quotient.mk K) • (⊤ : Submodule (S ⧸ K) P) ↔
      y ∈ J • (⊤ : Submodule S P) := by
  rw [← Submodule.restrictScalars_mem S, ← Ideal.Quotient.algebraMap_eq,
    Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]

/-- If `K ≤ J`, a class in `P ⧸ K • P` is a multiple of the image ideal of `J` exactly when
its representative belongs to `J • P`. -/
theorem Quotient.mk_mem_map_quotient_mk_smul_top_iff {S P : Type*} [CommRing S] [AddCommGroup P]
    [Module S P] {J K : Ideal S} (h : K ≤ J) (x : P) :
    Quotient.mk (p := (K • ⊤ : Submodule S P)) x ∈
      J.map (Ideal.Quotient.mk K) • (⊤ : Submodule (S ⧸ K) (P ⧸ (K • ⊤ : Submodule S P))) ↔
      x ∈ J • (⊤ : Submodule S P) := by
  rw [mem_map_quotient_mk_smul_top_iff, Quotient.mk_mem_smul_top_iff,
    sup_eq_right.mpr (smul_mono_left h)]

end Submodule
