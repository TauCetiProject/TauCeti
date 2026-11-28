/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Component.Basic
public import TauCeti.LinearAlgebra.RootSystem.PairingInvariance

/-!
# Root relations inside an irreducible component

Root strings stay in a single irreducible component. A bijection from that component to the
roots of a crystallographic root pairing which preserves integer Cartan pairings therefore
preserves integer root relations and root-string lengths via the existing pairing-invariance API.
`RootPairing.ambientComponentPairing` restricts root indices while retaining the ambient modules.
These comparisons do not require an integral splitting of the ambient weight or coweight lattice.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
-/

public section

open Set

namespace RootPairing

variable {ι R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The roots and coroots of one component, retaining the full ambient modules and pairing.
Unlike `RootPairing.componentPairing`, this construction needs no field or integral splitting. -/
noncomputable def ambientComponentPairing (P : RootPairing ι R M N) (C : P.Component) :
    RootPairing C.supp R M N where
  toLinearMap := P.toLinearMap
  root := (Function.Embedding.subtype _).trans P.root
  coroot := (Function.Embedding.subtype _).trans P.coroot
  root_coroot_two i := P.root_coroot_two i
  reflectionPerm i := (P.reflectionPerm i).subtypeEquiv fun j ↦ by
    simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, componentOf_reflectionPerm]
  reflectionPerm_root i j := P.reflectionPerm_root i j
  reflectionPerm_coroot i j := P.reflectionPerm_coroot i j

variable (P : RootPairing ι R M N) (C : P.Component)

@[simp] theorem ambientComponentPairing_root (i : C.supp) :
    (P.ambientComponentPairing C).root i = P.root i := (rfl)

@[simp] theorem ambientComponentPairing_coroot (i : C.supp) :
    (P.ambientComponentPairing C).coroot i = P.coroot i := (rfl)

@[simp] theorem ambientComponentPairing_toLinearMap :
    (P.ambientComponentPairing C).toLinearMap = P.toLinearMap := (rfl)

@[simp] theorem ambientComponentPairing_pairing (i j : C.supp) :
    (P.ambientComponentPairing C).pairing i j = P.pairing i j := (rfl)

@[simp] theorem coe_ambientComponentPairing_reflectionPerm (i j : C.supp) :
    ((P.ambientComponentPairing C).reflectionPerm i j : ι) = P.reflectionPerm i j := (rfl)

instance {S : Type*} [CommRing S] [Algebra S R] [P.IsValuedIn S] :
    (P.ambientComponentPairing C).IsValuedIn S where
  exists_value i j := P.exists_value i j

@[simp] theorem ambientComponentPairing_pairingIn {S : Type*} [CommRing S] [Algebra S R]
    [P.IsValuedIn S] (i j : C.supp) :
    (P.ambientComponentPairing C).pairingIn S i j = P.pairingIn S i j := (rfl)

section Components

variable {P} [NeZero (2 : R)]

/-- A root on an affine line through a root lies in the component of that root. -/
theorem componentOf_eq_of_root_eq_add_smul {i j k : ι} {r : R}
    (h : P.root k = P.root j + r • P.root i) : P.componentOf k = P.componentOf j := by
  by_cases hij : P.componentOf i = P.componentOf j
  · apply P.root_mem_componentSpace_iff.mp
    rw [h]
    exact add_mem (P.root_mem_componentSpace j)
      ((P.componentSpace (P.componentOf j)).smul_mem r
        (P.root_mem_componentSpace_iff.mpr hij))
  · have hpij := (P.isOrthogonal_of_componentOf_ne hij).1
    have hkj : P.pairing k j = 2 := by
      rw [← P.root_coroot'_eq_pairing, h, map_add, map_smul,
        P.root_coroot'_eq_pairing, P.root_coroot'_eq_pairing,
        P.pairing_same, hpij, smul_zero, add_zero]
    exact P.componentOf_eq_of_pairing_ne_zero (hkj ▸ two_ne_zero)

/-- Every root on an integer root string belongs to the component of the root it passes through. -/
theorem componentOf_eq_of_root_eq_add_zsmul {i j k : ι} {z : ℤ}
    (h : P.root k = P.root j + z • P.root i) : P.componentOf k = P.componentOf j :=
  componentOf_eq_of_root_eq_add_smul (i := i) (r := (z : R))
    (by simpa only [Int.cast_smul_eq_zsmul] using h)

/-- A root sum lies in the component of either summand. -/
theorem componentOf_eq_left_of_root_eq_add {i j k : ι}
    (h : P.root k = P.root i + P.root j) : P.componentOf k = P.componentOf i :=
  componentOf_eq_of_root_eq_add_smul (r := (1 : R)) (by simpa using h)

/-- Both summands of a root sum belong to the same irreducible component. -/
theorem componentOf_eq_of_root_eq_add {i j k : ι}
    (h : P.root k = P.root i + P.root j) : P.componentOf i = P.componentOf j :=
  (componentOf_eq_left_of_root_eq_add h).symm.trans
    (componentOf_eq_left_of_root_eq_add (h.trans (add_comm _ _)))

/-- Roots in different irreducible components cannot sum to a root. -/
theorem root_add_notMem_range_of_componentOf_ne {i j : ι}
    (h : P.componentOf i ≠ P.componentOf j) : P.root i + P.root j ∉ range P.root := by
  rintro ⟨k, hk⟩
  exact h (componentOf_eq_of_root_eq_add hk)

variable (P)

/-- Restricting root indices to a component preserves membership in its integer root strings. -/
theorem ambientComponentPairing_root_add_zsmul_mem_range_iff
    (i j : C.supp) (z : ℤ) :
    (P.ambientComponentPairing C).root j + z • (P.ambientComponentPairing C).root i ∈
        range (P.ambientComponentPairing C).root ↔
      P.root j + z • P.root i ∈ range P.root := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨⟨k, (componentOf_eq_of_root_eq_add_zsmul hk).trans j.property⟩, hk⟩

/-- Restricting root indices to a component preserves membership of root sums. -/
theorem ambientComponentPairing_root_add_mem_range_iff (i j : C.supp) :
    (P.ambientComponentPairing C).root i + (P.ambientComponentPairing C).root j ∈
        range (P.ambientComponentPairing C).root ↔ P.root i + P.root j ∈ range P.root := by
  simpa using P.ambientComponentPairing_root_add_zsmul_mem_range_iff C j i 1

end Components

section Crystallographic

variable [CharZero R] [IsDomain R] [Finite ι] [P.IsCrystallographic]

/-- Restricting root indices to a component preserves ascending string lengths. -/
@[simp] theorem ambientComponentPairing_chainTopCoeff (i j : C.supp) :
    (P.ambientComponentPairing C).chainTopCoeff i j = P.chainTopCoeff i j := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · rw [(P.ambientComponentPairing C).chainTopCoeff_eq_sSup h, P.chainTopCoeff_eq_sSup h]
    congr 1
    ext n
    simpa only [mem_ofPred_eq, ← natCast_zsmul] using
      P.ambientComponentPairing_root_add_zsmul_mem_range_iff C i j n
  · rw [(P.ambientComponentPairing C).chainTopCoeff_of_not_linearIndependent h,
      P.chainTopCoeff_of_not_linearIndependent h]

/-- Restricting root indices to a component preserves descending string lengths. -/
@[simp] theorem ambientComponentPairing_chainBotCoeff (i j : C.supp) :
    (P.ambientComponentPairing C).chainBotCoeff i j = P.chainBotCoeff i j := by
  rw [← (P.ambientComponentPairing C).chainTopCoeff_reflectionPerm_left,
    ambientComponentPairing_chainTopCoeff, coe_ambientComponentPairing_reflectionPerm,
    P.chainTopCoeff_reflectionPerm_left]

end Crystallographic

end RootPairing
