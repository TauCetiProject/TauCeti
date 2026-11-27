/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Data.ZMod.Basic
import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Folding a bounded complex into a two-periodic complex

Let `C` be a `ℤ`-graded chain complex of modules, vanishing outside a finite set `S` of degrees.
Reading its degrees modulo two folds it into a two-periodic complex, the **parity fold**
`ChainComplex.parityFold C S`: its term of parity `r` is the product `∏ C.X j` over the degrees
`j ∈ S` of parity `r` (`ChainComplex.parityFoldDegrees S r`), and its differentials are those of
`C`. This is how the finite parity complex of a Floer–Novikov theory whose relative grading is an
integer grading relates to that integer complex.

The parity fold is exact in parity `r` exactly when `C` is exact in every degree of parity `r`
(`ChainComplex.parityFold_exactAt_iff`), so it is acyclic exactly when `C` is
(`ChainComplex.parityFold_acyclic_iff`).

The compression of cochain complexes `TauCeti.PeriodicComplex.compression` folds an
integer-indexed complex in any category through coproducts. The parity fold is the concrete form
of this construction for chain complexes of modules vanishing outside `S`, a finite product, whose
explicit product bases the torsion of the fold needs (see
`TauCeti.Algebra.Homology.ReidemeisterTorsion.Periodic.Fold`).

## Main definitions

* `ChainComplex.parityFold C S`: the two-periodic complex obtained by reading the degrees of `C`
  in `S` modulo two.

## Main results

* `ChainComplex.parityFold_exactAt_iff`: the parity fold is exact in parity `r` exactly when `C`
  is exact in every degree of parity `r`.
* `ChainComplex.parityFold_acyclic_iff`: the parity fold is acyclic exactly when `C` is.

## References

* M. Hutchings, Y.-J. Lee, *Circle-valued Morse theory, Reidemeister torsion, and Seiberg–Witten
  invariants of 3-manifolds*, Topology 38 (1999), §2.
* Y.-J. Lee, *Reidemeister torsion in Floer–Novikov theory and counting pseudo-holomorphic
  tori, I*, J. Symplectic Geom. 3 (2005), §2.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace ChainComplex

variable {R : Type*} [Ring R] (C : ChainComplex (ModuleCat R) ℤ) (S : Finset ℤ)

/-- The degrees in `S` of parity `r`. -/
abbrev parityFoldDegrees (r : ZMod 2) : Finset ℤ :=
  S.filter fun j ↦ (j : ZMod 2) = r

/-- A differential of `C` between degrees that are not consecutive vanishes. -/
private theorem d_eq_zero_of_ne {i k : ℤ} (h : i ≠ k + 1) : C.d i k = 0 :=
  C.shape _ _ fun h' ↦ h (by rw [ComplexShape.down_Rel] at h'; omega)

variable {S} in
/-- A differential of `C` between degrees whose parities are not consecutive vanishes. -/
private theorem d_eq_zero_of_parity {r s : ZMod 2} (hrs : r + 1 ≠ s) (i : parityFoldDegrees S r)
    (j : parityFoldDegrees S s) : C.d i j = 0 :=
  C.shape _ _ fun hij ↦ hrs <| by
    have hi := (Finset.mem_filter.1 i.property).2
    have hj := (Finset.mem_filter.1 j.property).2
    rw [ComplexShape.down_Rel] at hij
    have h : (((j : ℤ) + 1 : ℤ) : ZMod 2) = ((i : ℤ) : ZMod 2) := by
      rw [hij]
    push_cast at h
    rw [hi, hj] at h
    rw [← h, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The **parity fold** of a chain complex `C` along a finite set `S` of degrees: the two-periodic
complex whose term of parity `r` is the product of the terms `C.X j` for the degrees `j ∈ S` of
parity `r`, with the differentials of `C` between them. When `C` vanishes outside `S`, this is the
sum over each parity class of the terms of `C`. -/
-- Implicitly reducible so that its terms unfold to the products `∀ j, C.X j` when vectors of
-- these products are fed to its differentials.
@[expose, implicit_reducible]
def parityFold : HomologicalComplex (ModuleCat R) (ComplexShape.up (ZMod 2)) where
  X r := ModuleCat.of R (∀ j : parityFoldDegrees S r, C.X j)
  d r s := ModuleCat.ofHom (LinearMap.pi fun j ↦ ∑ i : parityFoldDegrees S r,
      (C.d i j).hom ∘ₗ
        (LinearMap.proj i : (∀ j : parityFoldDegrees S r, C.X j) →ₗ[R] C.X i))
  shape r s hrs := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ funext fun j ↦ ?_)
    simp only [ModuleCat.hom_ofHom, LinearMap.pi_apply, LinearMap.sum_apply,
      LinearMap.comp_apply, LinearMap.proj_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun i _ ↦ by
      rw [d_eq_zero_of_parity C hrs i j, ModuleCat.hom_zero, LinearMap.zero_apply]
  d_comp_d' r s t _ _ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ funext fun k ↦ ?_)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, LinearMap.pi_apply,
      LinearMap.sum_apply, LinearMap.proj_apply, map_sum, ModuleCat.hom_zero,
      LinearMap.zero_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦
      HomologicalComplex.d_comp_d_apply C _ _ _ _

/-- The component in degree `j` of the differential of the parity fold. -/
@[simp]
theorem parityFold_d_apply (r s : ZMod 2) (x : (C.parityFold S).X r) (j : parityFoldDegrees S s) :
    ((C.parityFold S).d r s).hom x j = ∑ i : parityFoldDegrees S r, (C.d i j).hom (x i) := by
  simp only [parityFold, ModuleCat.hom_ofHom]
  exact LinearMap.sum_apply _ _ x

/-- The component in degree `k` of the differential of the parity fold only sees the component of
`x` in degree `k + 1`. -/
theorem parityFold_d_apply_of_eq_add_one {r s : ZMod 2} (x : (C.parityFold S).X r)
    (i : parityFoldDegrees S r) (k : parityFoldDegrees S s) (hik : (i : ℤ) = k + 1) :
    ((C.parityFold S).d r s).hom x k = (C.d i k).hom (x i) := by
  rw [parityFold_d_apply, Finset.sum_eq_single i (fun i' _ hi' ↦ by
    rw [d_eq_zero_of_ne C fun h ↦ hi' (Subtype.ext (by omega)), ModuleCat.hom_zero,
      LinearMap.zero_apply]) (by simp)]

/-- The component in degree `k` of the differential of the parity fold vanishes when `k + 1 ∉ S`. -/
theorem parityFold_d_apply_of_add_one_notMem {r s : ZMod 2} (x : (C.parityFold S).X r)
    (k : parityFoldDegrees S s) (hk : (k : ℤ) + 1 ∉ S) :
    ((C.parityFold S).d r s).hom x k = 0 := by
  rw [parityFold_d_apply]
  exact Finset.sum_eq_zero fun i _ ↦ by
    rw [d_eq_zero_of_ne C fun h ↦ hk (h ▸ (Finset.mem_filter.1 i.property).1), ModuleCat.hom_zero,
      LinearMap.zero_apply]

/-- The component in degree `j` of the differential of the parity fold on a vector concentrated in
one degree `i`. -/
theorem parityFold_d_single_apply {r s : ZMod 2} (i : parityFoldDegrees S r) (z : C.X i)
    (j : parityFoldDegrees S s) :
    ((C.parityFold S).d r s).hom (Pi.single i z) j = (C.d i j).hom z := by
  refine (parityFold_d_apply C S r s _ j).trans ?_
  rw [Finset.sum_eq_single i (fun i' _ hi' ↦ by
    rw [Pi.single_eq_of_ne hi', map_zero]) (by simp), Pi.single_eq_same]

/-- The differential of the parity fold on a vector concentrated in degree `i` has no component in
a degree `j` with `i ≠ j + 1`. -/
theorem parityFold_d_single_apply_of_ne {r s : ZMod 2} (i : parityFoldDegrees S r) (z : C.X i)
    (j : parityFoldDegrees S s) (h : (i : ℤ) ≠ j + 1) :
    ((C.parityFold S).d r s).hom (Pi.single i z) j = 0 := by
  rw [parityFold_d_single_apply, d_eq_zero_of_ne C h, ModuleCat.hom_zero, LinearMap.zero_apply]

/-- The differential of the parity fold carries a vector concentrated in degree `k + 1` to the
vector concentrated in degree `k` given by the differential of `C`. -/
theorem parityFold_d_single {r s : ZMod 2} (i : parityFoldDegrees S r)
    (k : parityFoldDegrees S s) (hik : (i : ℤ) = k + 1) (z : C.X i) :
    ((C.parityFold S).d r s).hom (Pi.single i z) = Pi.single k ((C.d i k).hom z) := by
  funext j
  by_cases hj : j = k
  · subst hj
    rw [parityFold_d_single_apply, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hj, parityFold_d_single_apply_of_ne C S i z j fun h ↦
      hj (Subtype.ext (by omega))]

/-- The differential of the parity fold kills a vector concentrated in degree `i` whose component
is a cycle of `C`. -/
theorem parityFold_d_single_eq_zero {r s : ZMod 2} (i : parityFoldDegrees S r)
    (z : C.X i) (hz : (C.d i (i - 1)).hom z = 0) :
    ((C.parityFold S).d r s).hom (Pi.single i z) = 0 := by
  funext k
  by_cases hki : (k : ℤ) = i - 1
  · obtain ⟨k, hk⟩ := k
    dsimp only at hki
    subst hki
    rw [parityFold_d_single_apply]
    exact hz
  · rw [parityFold_d_single_apply_of_ne C S i z k (by omega), Pi.zero_apply]

section Acyclic

variable {C S}

/-- A degree of parity `r` shifted by one has parity `r + 1`. -/
theorem mem_parityFoldDegrees_add_one {r : ZMod 2} {j : ℤ}
    (hj : j ∈ parityFoldDegrees S r) (h : j + 1 ∈ S) : j + 1 ∈ parityFoldDegrees S (r + 1) :=
  Finset.mem_filter.2 ⟨h, by push_cast; rw [(Finset.mem_filter.1 hj).2]⟩

/-- A degree of parity `r` shifted by minus one has parity `r + 1`. -/
theorem mem_parityFoldDegrees_sub_one {r : ZMod 2} {j : ℤ}
    (hj : j ∈ parityFoldDegrees S r) (h : j - 1 ∈ S) : j - 1 ∈ parityFoldDegrees S (r + 1) :=
  Finset.mem_filter.2 ⟨h, by push_cast; rw [(Finset.mem_filter.1 hj).2, CharTwo.sub_eq_add]⟩

variable (S) in
/-- The vector of the parity fold concentrated in degree `j + 1` with component `z`, or `0` when
`j + 1 ∉ S`. -/
private def foldSingleSucc {r : ZMod 2} (j : parityFoldDegrees S r) (z : C.X (j + 1)) :
    (C.parityFold S).X (r + 1) :=
  if h : (j : ℤ) + 1 ∈ S then Pi.single ⟨j + 1, mem_parityFoldDegrees_add_one j.property h⟩ z
  else 0

/-- If `C` vanishes outside `S`, the differential of the parity fold carries
`foldSingleSucc S j z` to the vector concentrated in degree `j` given by the differential of `C`. -/
private theorem parityFold_d_foldSingleSucc (hS : ∀ j ∉ S, IsZero (C.X j)) {r : ZMod 2}
    (j : parityFoldDegrees S r) (z : C.X (j + 1)) :
    ((C.parityFold S).d (r + 1) r).hom (foldSingleSucc S j z) =
      Pi.single j ((C.d (j + 1) j).hom z) := by
  by_cases h : (j : ℤ) + 1 ∈ S
  · have : foldSingleSucc S j z = Pi.single ⟨j + 1, mem_parityFoldDegrees_add_one j.property h⟩ z :=
      dite_eq_left h
    rw [this]
    exact parityFold_d_single C S ⟨j + 1, mem_parityFoldDegrees_add_one j.property h⟩ j rfl z
  · have : foldSingleSucc S j z = 0 := dite_eq_right h
    rw [this, map_zero, (ModuleCat.subsingleton_of_isZero (hS _ h)).elim z 0, map_zero,
      Pi.single_zero]

/-- Exactness of the parity fold in parity `r`, on elements. -/
private theorem parityFold_exactAt_iff_forall (r : ZMod 2) :
    (C.parityFold S).ExactAt r ↔ ∀ x, ((C.parityFold S).d r (r + 1)).hom x = 0 →
      ∃ y, ((C.parityFold S).d (r + 1) r).hom y = x := by
  have hprev : (ComplexShape.up (ZMod 2)).prev r = r + 1 := by
    rw [CochainComplex.prev, CharTwo.sub_eq_add]
  rw [HomologicalComplex.exactAt_iff' _ (r + 1) r (r + 1) hprev (CochainComplex.next _ r),
    ShortComplex.moduleCat_exact_iff]
  -- The maps of the short complex are the differentials, and `ConcreteCategory.hom` is
  -- `ModuleCat.Hom.hom` for morphisms of modules.
  rfl

/-- If the parity fold is exact in parity `r`, then `C` is exact in every degree of `S` of
parity `r`. -/
private theorem exactAt_of_parityFold_exactAt {r : ZMod 2} (hP : (C.parityFold S).ExactAt r)
    {j : ℤ} (hj : j ∈ parityFoldDegrees S r) : C.ExactAt j := by
  rw [HomologicalComplex.exactAt_iff' _ (j + 1) j (j - 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro z hz
  -- The vector concentrated in degree `j` with component `z` is a cycle of the fold, hence a
  -- boundary, and `z` is the component in degree `j` of that boundary.
  obtain ⟨y, hy⟩ := (parityFold_exactAt_iff_forall r).1 hP (Pi.single ⟨j, hj⟩ z)
    (parityFold_d_single_eq_zero C S ⟨j, hj⟩ z hz)
  have hz' := congrFun hy ⟨j, hj⟩
  rw [Pi.single_eq_same] at hz'
  by_cases h : j + 1 ∈ S
  · rw [parityFold_d_apply_of_eq_add_one C S y ⟨j + 1, mem_parityFoldDegrees_add_one hj h⟩ ⟨j, hj⟩
      rfl] at hz'
    exact ⟨_, hz'⟩
  · rw [parityFold_d_apply_of_add_one_notMem C S y ⟨j, hj⟩ h] at hz'
    exact ⟨0, by rw [map_zero, hz']⟩

/-- If `C` vanishes outside `S` and is exact in every degree of `S` of parity `r`, then the parity
fold is exact in parity `r`. -/
private theorem parityFold_exactAt_of_exactAt (hS : ∀ j ∉ S, IsZero (C.X j)) {r : ZMod 2}
    (hC : ∀ j ∈ parityFoldDegrees S r, C.ExactAt j) : (C.parityFold S).ExactAt r := by
  rw [parityFold_exactAt_iff_forall]
  intro x hx
  -- Every component of `x` is a cycle of `C`.
  have hcyc (j : parityFoldDegrees S r) : (C.d j (j - 1)).hom (x j) = 0 := by
    by_cases hj : (j : ℤ) - 1 ∈ S
    · exact (parityFold_d_apply_of_eq_add_one C S x j
        ⟨j - 1, mem_parityFoldDegrees_sub_one j.property hj⟩ (sub_add_cancel _ _).symm).symm.trans
        (congrFun hx _)
    · exact (ModuleCat.subsingleton_of_isZero (hS _ hj)).elim _ _
  -- Hence a boundary of `C`, and `x` is the boundary of the sum of the vectors it comes from.
  have hlift (j : parityFoldDegrees S r) : ∃ w : C.X (j + 1), (C.d (j + 1) j).hom w = x j := by
    have hj := hC j j.property
    rw [HomologicalComplex.exactAt_iff' _ ((j : ℤ) + 1) j ((j : ℤ) - 1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff] at hj
    exact hj _ (hcyc j)
  choose w hw using hlift
  refine ⟨∑ j : parityFoldDegrees S r, foldSingleSucc S j (w j), ?_⟩
  rw [map_sum]
  conv_rhs => rw [← Finset.univ_sum_single x]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [parityFold_d_foldSingleSucc hS, hw]

/-- The parity fold is exact in parity `r` exactly when `C` is exact in every degree of `S` of
parity `r`, provided `C` vanishes outside `S`. -/
theorem parityFold_exactAt_iff (hS : ∀ j ∉ S, IsZero (C.X j)) (r : ZMod 2) :
    (C.parityFold S).ExactAt r ↔ ∀ j ∈ parityFoldDegrees S r, C.ExactAt j :=
  ⟨fun hP _ hj ↦ exactAt_of_parityFold_exactAt hP hj, parityFold_exactAt_of_exactAt hS⟩

/-- The parity fold of a complex vanishing outside `S` is acyclic exactly when the complex is. -/
theorem parityFold_acyclic_iff (hS : ∀ j ∉ S, IsZero (C.X j)) :
    (C.parityFold S).Acyclic ↔ C.Acyclic := by
  refine ⟨fun h j ↦ ?_, fun h r ↦ (parityFold_exactAt_iff hS r).2 fun j _ ↦ h j⟩
  by_cases hj : j ∈ S
  · exact (parityFold_exactAt_iff hS (j : ZMod 2)).1 (h _) j (Finset.mem_filter.2 ⟨hj, rfl⟩)
  · exact .of_isZero (hS j hj)

end Acyclic

end ChainComplex
