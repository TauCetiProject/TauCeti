/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Chevalley.Basic
public import TauCeti.LinearAlgebra.RootSystem.Component.RootString

/-!
# Assembly of Chevalley constants from irreducible components

`RootPairing.ChevalleyConstants.ofComponents` assembles integer Chevalley tables on integral
models of the irreducible components of a root datum. A Cartan-matching root bijection identifies
each model with its component; entries on different components are zero. The resulting table
lives on the original root indices and retains the full cocharacter lattice. In particular,
no integral splitting of the cocharacter lattice is needed.

The root-string and coroot-relation comparisons use the perfect ambient pairing. Mixed-component
terms in the root-coordinate Jacobi identity vanish individually.

## References

* C. Chevalley, *Sur certains groupes simples*, Tohoku Math. J. (2) **7** (1955), 14--66.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
-/

public section

open Set

namespace RootPairing.ChevalleyConstants

variable {ι X Y : Type*} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
  {P : RootPairing ι ℤ X Y}
  {J U V : P.Component → Type*}
  [∀ C, AddCommGroup (U C)] [∀ C, AddCommGroup (V C)] [∀ C, Finite (J C)]
  (Q : ∀ C, RootPairing (J C) ℤ (U C) (V C))
  (e : ∀ C, C.supp ≃ J C)
  (he : ∀ C (i j : C.supp), (Q C).pairing (e C i) (e C j) = P.pairing i j)

variable (c : ∀ C, (Q C).ChevalleyConstants)

open Classical in
private noncomputable def componentConst (i j : ι) : ℤ :=
  if h : P.componentOf j = P.componentOf i then
    (c (P.componentOf i)).structConst
      (e (P.componentOf i) ⟨i, rfl⟩) (e (P.componentOf i) ⟨j, h⟩)
  else 0

omit [Finite ι] in
private theorem componentConst_of_mem (C : P.Component) (i j : C.supp) :
    componentConst Q e c i j = (c C).structConst (e C i) (e C j) := by
  obtain ⟨i, hi⟩ := i
  revert j
  -- Membership in a component support is equality with the component of the root.
  change P.componentOf i = C at hi
  subst C
  rintro ⟨j, hj⟩
  have hj' : P.componentOf j = P.componentOf i := hj
  simp [componentConst, hj']

omit [Finite ι] in
private theorem componentConst_of_ne {i j : ι} (h : P.componentOf i ≠ P.componentOf j) :
    componentConst Q e c i j = 0 := by
  simp [componentConst, Ne.symm h]

include he in
private theorem componentConst_eq_zero_of_notMem {i j : ι}
    (h : P.root i + P.root j ∉ range P.root) : componentConst Q e c i j = 0 := by
  by_cases hij : P.componentOf j = P.componentOf i
  · let C := P.componentOf i
    let i' : C.supp := ⟨i, rfl⟩
    let j' : C.supp := ⟨j, hij⟩
    rw [componentConst_of_mem Q e c C i' j']
    exact (c C).structConst_eq_zero_of_notMem_range _ _
      (mt (root_add_mem_range_iff_of_component P (e C) (he C) i' j').mp h)
  · exact componentConst_of_ne Q e c (Ne.symm hij)

omit [Finite ι] in
private theorem componentConst_swap (i j : ι) :
    componentConst Q e c j i = -componentConst Q e c i j := by
  by_cases hij : P.componentOf j = P.componentOf i
  · let C := P.componentOf i
    let i' : C.supp := ⟨i, rfl⟩
    let j' : C.supp := ⟨j, hij⟩
    rw [componentConst_of_mem Q e c C j' i', componentConst_of_mem Q e c C i' j']
    exact (c C).structConst_swap _ _
  · rw [componentConst_of_ne Q e c hij, componentConst_of_ne Q e c (Ne.symm hij), neg_zero]

include he in
private theorem natAbs_componentConst {i j k : ι} (hk : P.root k = P.root i + P.root j) :
    (componentConst Q e c i j).natAbs = P.chainBotCoeff i j + 1 := by
  let C := P.componentOf i
  let i' : C.supp := ⟨i, rfl⟩
  let j' : C.supp := ⟨j, (P.componentOf_eq_of_root_eq_add hk).symm⟩
  let k' : C.supp := ⟨k, P.componentOf_eq_left_of_root_eq_add hk⟩
  rw [componentConst_of_mem Q e c C i' j',
    (c C).natAbs_structConst ((root_eq_add_iff_of_component P (e C) (he C) i' j' k').mpr hk),
    chainBotCoeff_eq_of_component P (e C) (he C) i' j']

include he in
private theorem componentConst_reflectionPerm (i j : ι) :
    componentConst Q e c (P.reflectionPerm i i) (P.reflectionPerm j j) =
      -componentConst Q e c i j := by
  by_cases hij : P.componentOf j = P.componentOf i
  · let C := P.componentOf i
    let i' : C.supp := ⟨i, rfl⟩
    let j' : C.supp := ⟨j, hij⟩
    let ni : C.supp := ⟨P.reflectionPerm i i, P.componentOf_reflectionPerm i i⟩
    let nj : C.supp := ⟨P.reflectionPerm j j, (P.componentOf_reflectionPerm j j).trans hij⟩
    rw [componentConst_of_mem Q e c C ni nj, componentConst_of_mem Q e c C i' j']
    rw [map_reflectionPerm_of_component P (e C) (he C) i' i',
      map_reflectionPerm_of_component P (e C) (he C) j' j', (c C).structConst_reflectionPerm]
  · rw [componentConst_of_ne Q e c (by
      simpa only [P.componentOf_reflectionPerm] using Ne.symm hij),
      componentConst_of_ne Q e c (Ne.symm hij), neg_zero]

include he in
private theorem componentConst_coroot_jacobi {i j k : ι}
    (h : P.root i + P.root j + P.root k = 0) :
    componentConst Q e c j k • P.coroot i + componentConst Q e c k i • P.coroot j +
      componentConst Q e c i j • P.coroot k = 0 := by
  have hsum := P.root_reflectionPerm_self_eq_add_of_add_add_eq_zero h
  have hjk := P.componentOf_eq_of_root_eq_add hsum
  have hji : P.componentOf j = P.componentOf i := by
    simpa using (P.componentOf_eq_left_of_root_eq_add hsum).symm
  let C := P.componentOf i
  let i' : C.supp := ⟨i, rfl⟩
  let j' : C.supp := ⟨j, hji⟩
  let k' : C.supp := ⟨k, hjk.symm.trans hji⟩
  have hQ := (c C).coroot_jacobi
    ((root_add_add_eq_zero_iff_of_component P (e C) (he C) i' j' k').mpr h)
  have htransfer := sum_zsmul_coroot_eq_zero_iff_of_component P (e C) (he C)
    ![(c C).structConst (e C j') (e C k'), (c C).structConst (e C k') (e C i'),
      (c C).structConst (e C i') (e C j')] ![i', j', k']
  rw [componentConst_of_mem Q e c C j' k', componentConst_of_mem Q e c C k' i',
    componentConst_of_mem Q e c C i' j']
  simpa [Fin.sum_univ_three, add_assoc] using htransfer.mp (by
    simpa [Fin.sum_univ_three, add_assoc] using hQ)

omit [Finite ι] in
private theorem tripleRootCoeff_componentConst_eq_zero {i j k : ι}
    (h : ¬ (P.componentOf i = P.componentOf j ∧ P.componentOf j = P.componentOf k)) (l : ι) :
    P.tripleRootCoeff (componentConst Q e c) i j k l = 0 := by
  classical
  by_cases hjk0 : P.root j + P.root k = 0
  · have hj : j = P.reflectionPerm k k :=
      P.root_eq_neg_iff.mp (add_eq_zero_iff_eq_neg.mp hjk0)
    have hjk : P.componentOf j = P.componentOf k := by simp [hj]
    have hij : P.componentOf i ≠ P.componentOf j := fun hij ↦ h ⟨hij, hjk⟩
    rw [P.tripleRootCoeff_of_add_eq_zero _ hjk0, (P.isOrthogonal_of_componentOf_ne hij).1]
    simp
  · by_cases hmem : P.root j + P.root k ∈ range P.root
    · obtain ⟨m, hm⟩ := hmem
      have hjk := P.componentOf_eq_of_root_eq_add hm
      have hmj := P.componentOf_eq_left_of_root_eq_add hm
      have him : P.componentOf i ≠ P.componentOf m := fun him ↦ h ⟨him.trans hmj, hjk⟩
      rw [P.tripleRootCoeff_of_root_eq_add _ hm, componentConst_of_ne Q e c him]
      simp
    · exact P.tripleRootCoeff_of_notMem_of_add_ne_zero _ hmem hjk0

include he in
private theorem tripleRootCoeff_componentConst (C : P.Component) (i j k l : C.supp) :
    P.tripleRootCoeff (componentConst Q e c) i j k l =
      (Q C).tripleRootCoeff (c C).structConst (e C i) (e C j) (e C k) (e C l) := by
  classical
  by_cases hjk0 : P.root j + P.root k = 0
  · rw [P.tripleRootCoeff_of_add_eq_zero _ hjk0,
      (Q C).tripleRootCoeff_of_add_eq_zero _
        ((root_add_eq_zero_iff_of_component P (e C) (he C) j k).mpr hjk0), he]
    simp only [Equiv.apply_eq_iff_eq, Subtype.ext_iff]
  · have hjkQ0 := mt (root_add_eq_zero_iff_of_component P (e C) (he C) j k).mp hjk0
    by_cases hmem : P.root j + P.root k ∈ range P.root
    · obtain ⟨m, hm⟩ := hmem
      have hmC := (P.componentOf_eq_left_of_root_eq_add hm).trans j.property
      let m' : C.supp := ⟨m, hmC⟩
      rw [P.tripleRootCoeff_of_root_eq_add _ hm,
        (Q C).tripleRootCoeff_of_root_eq_add _
          ((root_eq_add_iff_of_component P (e C) (he C) j k m').mpr hm),
        root_eq_add_iff_of_component P (e C) (he C) i m' l,
        componentConst_of_mem Q e c C i m', componentConst_of_mem Q e c C j k]
    · rw [P.tripleRootCoeff_of_notMem_of_add_ne_zero _ hmem hjk0,
        (Q C).tripleRootCoeff_of_notMem_of_add_ne_zero _
          (mt (root_add_mem_range_iff_of_component P (e C) (he C) j k).mp hmem) hjkQ0]

omit [Finite ι] in
private theorem tripleRootCoeff_componentConst_eq_zero_of_outside
    (C : P.Component) (i j k : C.supp) {l : ι} (hl : P.componentOf l ≠ C) :
    P.tripleRootCoeff (componentConst Q e c) i j k l = 0 := by
  apply P.tripleRootCoeff_eq_zero_of_ne_sum
  intro h
  apply hl
  apply P.root_mem_componentSpace_iff.mp
  rw [h]
  exact add_mem (add_mem (P.root_mem_componentSpace_of_mem_supp i.property)
    (P.root_mem_componentSpace_of_mem_supp j.property))
    (P.root_mem_componentSpace_of_mem_supp k.property)

include he in
private theorem componentConst_root_jacobi (i j k l : ι) :
    P.tripleRootCoeff (componentConst Q e c) i j k l +
      P.tripleRootCoeff (componentConst Q e c) j k i l +
      P.tripleRootCoeff (componentConst Q e c) k i j l = 0 := by
  by_cases h : P.componentOf i = P.componentOf j ∧ P.componentOf j = P.componentOf k
  · let C := P.componentOf i
    let i' : C.supp := ⟨i, rfl⟩
    let j' : C.supp := ⟨j, h.1.symm⟩
    let k' : C.supp := ⟨k, h.2.symm.trans h.1.symm⟩
    by_cases hl : P.componentOf l = C
    · let l' : C.supp := ⟨l, hl⟩
      rw [tripleRootCoeff_componentConst Q e he c C i' j' k' l',
        tripleRootCoeff_componentConst Q e he c C j' k' i' l',
        tripleRootCoeff_componentConst Q e he c C k' i' j' l']
      exact (c C).root_jacobi _ _ _ _
    · rw [tripleRootCoeff_componentConst_eq_zero_of_outside Q e c C i' j' k' hl,
        tripleRootCoeff_componentConst_eq_zero_of_outside Q e c C j' k' i' hl,
        tripleRootCoeff_componentConst_eq_zero_of_outside Q e c C k' i' j' hl]
      simp
  · have h' : ¬ (P.componentOf j = P.componentOf k ∧ P.componentOf k = P.componentOf i) :=
      fun h' ↦ h ⟨h'.2.symm.trans h'.1.symm, h'.1⟩
    have h'' : ¬ (P.componentOf k = P.componentOf i ∧ P.componentOf i = P.componentOf j) :=
      fun h' ↦ h ⟨h'.2, h'.2.symm.trans h'.1.symm⟩
    rw [tripleRootCoeff_componentConst_eq_zero Q e c h l,
      tripleRootCoeff_componentConst_eq_zero Q e c h' l,
      tripleRootCoeff_componentConst_eq_zero Q e c h'' l]
    simp

/-- Assemble Chevalley tables on Cartan-matching integral models of the irreducible components.
The toral coordinate remains the full ambient cocharacter lattice. -/
noncomputable def ofComponents : P.ChevalleyConstants where
  structConst := componentConst Q e c
  structConst_eq_zero_of_notMem_range _ _ := componentConst_eq_zero_of_notMem Q e he c
  structConst_swap := componentConst_swap Q e c
  natAbs_structConst := natAbs_componentConst Q e he c
  structConst_reflectionPerm := componentConst_reflectionPerm Q e he c
  coroot_jacobi := componentConst_coroot_jacobi Q e he c
  root_jacobi := componentConst_root_jacobi Q e he c

/-- On a component the assembled table is the pullback of its model table. -/
@[simp] theorem ofComponents_structConst_of_mem (C : P.Component) (i j : C.supp) :
    (ofComponents Q e he c).structConst i j = (c C).structConst (e C i) (e C j) :=
  componentConst_of_mem Q e c C i j

/-- Entries of the assembled table on different components are zero. -/
@[simp] theorem ofComponents_structConst_of_ne {i j : ι} (h : P.componentOf i ≠ P.componentOf j) :
    (ofComponents Q e he c).structConst i j = 0 :=
  componentConst_of_ne Q e c h

/-- The component tables are recovered uniquely from the assembled table. -/
theorem ofComponents_injective : Function.Injective (ofComponents Q e he) := by
  intro c d h
  funext C
  ext i j
  obtain ⟨i, rfl⟩ := (e C).surjective i
  obtain ⟨j, rfl⟩ := (e C).surjective j
  simpa only [ofComponents_structConst_of_mem] using
    congrArg (fun t : P.ChevalleyConstants ↦ t.structConst i j) h

end RootPairing.ChevalleyConstants
