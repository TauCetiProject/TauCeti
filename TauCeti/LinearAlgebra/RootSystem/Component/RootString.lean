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
roots of an integral root pairing which preserves Cartan pairings therefore preserves integer
root relations and root-string lengths. These comparisons do not require an integral splitting
of the ambient weight or coweight lattice.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
-/

public section

open Set

namespace RootPairing

section Components

variable {ι R M N : Type*} [CommRing R] [NeZero (2 : R)]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- Both summands of a root sum belong to the same irreducible component. -/
theorem componentOf_eq_of_root_eq_add {i j k : ι}
    (h : P.root k = P.root i + P.root j) : P.componentOf i = P.componentOf j := by
  by_contra hij
  have hpij := (P.isOrthogonal_of_componentOf_ne hij).1
  have hpji := (P.isOrthogonal_of_componentOf_ne hij).2
  have hki : P.pairing k i = 2 := by
    rw [← P.root_coroot_eq_pairing, h, map_add, LinearMap.add_apply,
      P.root_coroot_eq_pairing, P.root_coroot_eq_pairing, P.pairing_same, hpji, add_zero]
  have hkj : P.pairing k j = 2 := by
    rw [← P.root_coroot_eq_pairing, h, map_add, LinearMap.add_apply,
      P.root_coroot_eq_pairing, P.root_coroot_eq_pairing, P.pairing_same, hpij, zero_add]
  exact hij ((P.componentOf_eq_of_pairing_ne_zero (hki ▸ two_ne_zero)).symm.trans
    (P.componentOf_eq_of_pairing_ne_zero (hkj ▸ two_ne_zero)))

/-- A root sum lies in the component of either summand. -/
theorem componentOf_eq_left_of_root_eq_add {i j k : ι}
    (h : P.root k = P.root i + P.root j) : P.componentOf k = P.componentOf i := by
  have hij := componentOf_eq_of_root_eq_add h
  apply P.root_mem_componentSpace_iff.mp
  rw [h]
  exact add_mem (P.root_mem_componentSpace i)
    (P.root_mem_componentSpace_iff.mpr hij.symm)

/-- Roots in different irreducible components cannot sum to a root. -/
theorem root_add_notMem_range_of_componentOf_ne {i j : ι}
    (h : P.componentOf i ≠ P.componentOf j) : P.root i + P.root j ∉ range P.root := by
  rintro ⟨k, hk⟩
  exact h (componentOf_eq_of_root_eq_add hk)

/-- Every root on an integer root string belongs to the component of the root it passes through. -/
theorem componentOf_eq_of_root_eq_add_zsmul {i j k : ι} {z : ℤ}
    (h : P.root k = P.root j + z • P.root i) : P.componentOf k = P.componentOf j := by
  by_cases hij : P.componentOf i = P.componentOf j
  · apply P.root_mem_componentSpace_iff.mp
    rw [h]
    exact add_mem (P.root_mem_componentSpace j) (by
      simpa only [Int.cast_smul_eq_zsmul] using
        (P.componentSpace (P.componentOf j)).smul_mem (z : R)
          (P.root_mem_componentSpace_iff.mpr hij))
  · have hpij := (P.isOrthogonal_of_componentOf_ne hij).1
    have hkj : P.pairing k j = 2 := by
      rw [← P.root_coroot'_eq_pairing, h, map_add, map_zsmul,
        P.root_coroot'_eq_pairing, P.root_coroot'_eq_pairing,
        P.pairing_same, hpij, smul_zero, add_zero]
    exact P.componentOf_eq_of_pairing_ne_zero (hkj ▸ two_ne_zero)

end Components

section Integral

variable {ι J X Y U V : Type*} [Finite ι]
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup U] [AddCommGroup V]
  (P : RootPairing ι ℤ X Y) {C : P.Component} {Q : RootPairing J ℤ U V}
  (e : C.supp ≃ J) (he : ∀ i j : C.supp, Q.pairing (e i) (e j) = P.pairing i j)

include he

/-- A Cartan-matching bijection on one component preserves all integral root relations. -/
theorem sum_zsmul_root_eq_zero_iff_of_component {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (idx : κ → C.supp) :
    ∑ t, a t • Q.root (e (idx t)) = 0 ↔ ∑ t, a t • P.root (idx t) = 0 := by
  have : Finite J := Finite.of_equiv C.supp e
  rw [Q.sum_zsmul_root_eq_zero_iff, P.sum_zsmul_root_eq_zero_iff]
  simp only [pairingIn_eq_pairing]
  constructor
  · intro h s
    by_cases hs : P.componentOf s = C
    · simpa only [he] using h (e ⟨s, hs⟩)
    · apply Finset.sum_eq_zero
      intro t _
      rw [(P.isOrthogonal_of_componentOf_ne
        (fun h ↦ hs (h.symm.trans (idx t).property))).1, mul_zero]
  · intro h s
    obtain ⟨s, rfl⟩ := e.surjective s
    simpa only [he] using h s

/-- A Cartan-matching bijection on one component preserves root addition. -/
theorem root_eq_add_iff_of_component (i j k : C.supp) :
    Q.root (e k) = Q.root (e i) + Q.root (e j) ↔
      P.root k = P.root i + P.root j := by
  have h := sum_zsmul_root_eq_zero_iff_of_component P e he ![-1, 1, 1] ![k, i, j]
  simpa [Fin.sum_univ_three, add_assoc, neg_add_eq_zero] using h

/-- A Cartan-matching bijection on one component preserves opposite roots. -/
theorem root_add_eq_zero_iff_of_component (i j : C.supp) :
    Q.root (e i) + Q.root (e j) = 0 ↔ P.root i + P.root j = 0 := by
  simpa [Fin.sum_univ_two] using
    sum_zsmul_root_eq_zero_iff_of_component P e he ![1, 1] ![i, j]

/-- A Cartan-matching bijection on one component preserves integer root-string relations. -/
theorem root_eq_add_zsmul_iff_of_component (i j k : C.supp) (z : ℤ) :
    Q.root (e k) = Q.root (e j) + z • Q.root (e i) ↔
      P.root k = P.root j + z • P.root i := by
  have h := sum_zsmul_root_eq_zero_iff_of_component P e he ![-1, 1, z] ![k, j, i]
  simpa [Fin.sum_univ_three, add_assoc, neg_add_eq_zero] using h

/-- A Cartan-matching bijection on one component preserves zero sums of three roots. -/
theorem root_add_add_eq_zero_iff_of_component (i j k : C.supp) :
    Q.root (e i) + Q.root (e j) + Q.root (e k) = 0 ↔
      P.root i + P.root j + P.root k = 0 := by
  simpa [Fin.sum_univ_three, add_assoc] using
    sum_zsmul_root_eq_zero_iff_of_component P e he ![1, 1, 1] ![i, j, k]

/-- A Cartan-matching bijection on one component preserves pairwise root independence. -/
theorem linearIndependent_root_iff_of_component (i j : C.supp) :
    LinearIndependent ℤ ![Q.root (e i), Q.root (e j)] ↔
      LinearIndependent ℤ ![P.root i, P.root j] := by
  have : Finite J := Finite.of_equiv C.supp e
  have : Module.IsReflexive ℤ X := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive ℤ U := .of_isPerfPair Q.toLinearMap
  simp [Q.linearIndependent_iff_coxeterWeightIn_ne_four ℤ,
    P.linearIndependent_iff_coxeterWeightIn_ne_four ℤ, coxeterWeightIn, pairingIn_eq_pairing, he]

/-- A component root bijection matching the Cartan pairings preserves root-string membership. -/
theorem root_add_zsmul_mem_range_iff_of_component (i j : C.supp) (z : ℤ) :
    Q.root (e j) + z • Q.root (e i) ∈ range Q.root ↔
      P.root j + z • P.root i ∈ range P.root := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨k, rfl⟩ := e.surjective k
    exact ⟨k, (root_eq_add_zsmul_iff_of_component P e he i j k z).mp hk⟩
  · rintro ⟨k, hk⟩
    have hkC := (componentOf_eq_of_root_eq_add_zsmul hk).trans j.property
    exact ⟨e ⟨k, hkC⟩, (root_eq_add_zsmul_iff_of_component P e he i j ⟨k, hkC⟩ z).mpr hk⟩

/-- A component root bijection matching the Cartan pairings preserves root sums. -/
theorem root_add_mem_range_iff_of_component (i j : C.supp) :
    Q.root (e i) + Q.root (e j) ∈ range Q.root ↔ P.root i + P.root j ∈ range P.root := by
  simpa using root_add_zsmul_mem_range_iff_of_component P e he j i 1

/-- A Cartan-matching component bijection intertwines reflection permutations. -/
theorem map_reflectionPerm_of_component (i j : C.supp) :
    e ⟨P.reflectionPerm i j, (P.componentOf_reflectionPerm i j).trans j.property⟩ =
      Q.reflectionPerm (e i) (e j) := by
  apply Q.root.injective
  have h : P.root (P.reflectionPerm i j) = P.root j + (-P.pairing j i) • P.root i := by
    rw [P.root_reflectionPerm, P.reflection_apply_root, neg_smul, sub_eq_add_neg]
  rw [(root_eq_add_zsmul_iff_of_component P e he i j _ _).mpr h, ← he j i,
    Q.root_reflectionPerm, Q.reflection_apply_root, neg_smul, sub_eq_add_neg]

/-- A component root bijection matching the Cartan pairings preserves ascending string lengths. -/
theorem chainTopCoeff_eq_of_component (i j : C.supp) :
    letI : Finite J := Finite.of_equiv C.supp e
    Q.chainTopCoeff (e i) (e j) = P.chainTopCoeff i j := by
  have : Finite J := Finite.of_equiv C.supp e
  by_cases h : LinearIndependent ℤ ![P.root i, P.root j]
  · have hQ := (linearIndependent_root_iff_of_component P e he i j).mpr h
    have hmem (n : ℕ) : Q.root (e j) + n • Q.root (e i) ∈ range Q.root ↔
        P.root j + n • P.root i ∈ range P.root := by
      simpa using root_add_zsmul_mem_range_iff_of_component P e he i j n
    exact le_antisymm
      ((P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h).mp
        ((hmem _).mp ((Q.root_add_nsmul_mem_range_iff_le_chainTopCoeff hQ).mpr le_rfl)))
      ((Q.root_add_nsmul_mem_range_iff_le_chainTopCoeff hQ).mp
        ((hmem _).mpr ((P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h).mpr le_rfl)))
  · rw [Q.chainTopCoeff_of_not_linearIndependent
      (mt (linearIndependent_root_iff_of_component P e he i j).mp h),
      P.chainTopCoeff_of_not_linearIndependent h]

/-- A component root bijection matching the Cartan pairings preserves descending string lengths. -/
theorem chainBotCoeff_eq_of_component (i j : C.supp) :
    letI : Finite J := Finite.of_equiv C.supp e
    Q.chainBotCoeff (e i) (e j) = P.chainBotCoeff i j := by
  have : Finite J := Finite.of_equiv C.supp e
  let i' : C.supp := ⟨P.reflectionPerm i i, (P.componentOf_reflectionPerm i i).trans i.property⟩
  rw [← Q.chainTopCoeff_reflectionPerm_left, ← map_reflectionPerm_of_component P e he i i]
  exact (chainTopCoeff_eq_of_component P e he i' j).trans
    (P.chainTopCoeff_reflectionPerm_left (i := i) (j := j))

/-- A Cartan-matching component bijection preserves integral relations among coroots. -/
theorem sum_zsmul_coroot_eq_zero_iff_of_component {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (idx : κ → C.supp) :
    ∑ t, a t • Q.coroot (e (idx t)) = 0 ↔ ∑ t, a t • P.coroot (idx t) = 0 := by
  have : Finite J := Finite.of_equiv C.supp e
  rw [Q.sum_zsmul_coroot_eq_zero_iff, P.sum_zsmul_coroot_eq_zero_iff]
  simp only [pairingIn_eq_pairing]
  constructor
  · intro h s
    by_cases hs : P.componentOf s = C
    · simpa only [he] using h (e ⟨s, hs⟩)
    · apply Finset.sum_eq_zero
      intro t _
      rw [(P.isOrthogonal_of_componentOf_ne
        (fun h ↦ hs (h.trans (idx t).property))).1, mul_zero]
  · intro h s
    obtain ⟨s, rfl⟩ := e.surjective s
    simpa only [he] using h s

end Integral

end RootPairing
