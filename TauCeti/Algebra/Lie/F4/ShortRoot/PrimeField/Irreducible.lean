/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.StandardComodule
import TauCeti.Data.List.Involutive

/-!
# Irreducibility of the short-root F₄ standard representation

The twenty-six-dimensional standard comodule of the short-root `F₄` carrier over a field of
characteristic two is simple. The weight torus separates its twenty-four nonzero-weight
coordinates, while the zero weight has multiplicity two. Numbered simple-root points connect all
twenty-four nonzero weights and connect each of the two zero-weight coordinates to them. Thus a
nonzero invariant subspace contains every coordinate vector.

The quadratic terms in the two short simple-root subgroups are essential: they exchange the two
weights opposite to a short simple root without requiring division by two.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.
* R. W. Carter, *Simple Groups of Lie Type*, §12.3.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII.
-/

public section

open CategoryTheory
open scoped Matrix

namespace TauCeti.F4ShortRoot.PrimeField

open DynkinType

universe u

noncomputable section

variable (k : Type u) [Field k] [Algebra (ZMod 2) k]

attribute [local instance] GeneralLinear.standardComodule standardComodule

/-! ## Root moves on nonzero weights -/

/-- The integral matrix of a numbered root-subgroup point at parameter one. -/
private def unitRootMatrix (j : Fin 4 ⊕ Fin 4) : Matrix (Fin 26) (Fin 26) ℤ :=
  1 + rootMatrix j + rootDividedSquareMatrix j

/-- At parameter one, the concrete root-subgroup point is the reduction of `unitRootMatrix`. -/
private theorem coe_rootSubgroupPoints_one (j : Fin 4 ⊕ Fin 4) :
    ((rootSubgroupPoints j k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 26) k) : Matrix (Fin 26) (Fin 26) k) =
      (unitRootMatrix j).map (Int.cast : ℤ → k) := by
  rw [coe_rootSubgroupPoints, _root_.TauCeti.F4ShortRoot.coe_rootSubgroupPoints_eq]
  simp [unitRootMatrix, Matrix.map_add]

/-- The simple reflection on the twenty-four nonzero-weight coordinates, read from the root
matrix tables. Divided-square moves take priority at the two short simple roots. -/
private def basisReflection (i : Fin 4) (a : Fin 26) : Fin 26 :=
  if raisingDividedSquareCoeff i a = 1 then raisingDividedSquareTarget i a
  else if loweringDividedSquareCoeff i a = 1 then loweringDividedSquareTarget i a
  else if raisingCoeff i a = 1 then raisingTarget i a
  else if loweringCoeff i a = 1 then loweringTarget i a
  else a

/-- A numbered root subgroup whose unit point has the `basisReflection` entry equal to one. -/
private def reflectionGenerator (i : Fin 4) (a : Fin 26) : Fin 4 ⊕ Fin 4 :=
  if raisingDividedSquareCoeff i a = 1 then .inl i
  else if loweringDividedSquareCoeff i a = 1 then .inr i
  else if raisingCoeff i a = 1 then .inl i
  else .inr i

/-- A simple reflection preserves the set of nonzero-weight coordinates. -/
private theorem basisReflection_weight_ne_zero (i : Fin 4) (a : Fin 26)
    (ha : f4ShortRootWeight a ≠ 0) : f4ShortRootWeight (basisReflection i a) ≠ 0 := by
  revert i a
  decide +kernel

/-- The chosen root point has coefficient one from a nonzero-weight coordinate to its simple
reflection. -/
private theorem unitRootMatrix_reflectionGenerator (i : Fin 4) (a : Fin 26)
    (ha : f4ShortRootWeight a ≠ 0) :
    unitRootMatrix (reflectionGenerator i a) (basisReflection i a) a = 1 := by
  fin_cases i <;> fin_cases a <;>
    simp_all [unitRootMatrix, reflectionGenerator, basisReflection, raisingTarget, raisingCoeff,
      loweringTarget, loweringCoeff, raisingDividedSquareTarget, raisingDividedSquareCoeff,
      loweringDividedSquareTarget, loweringDividedSquareCoeff, rootMatrix_inl, rootMatrix_inr,
      rootDividedSquareMatrix_inl, rootDividedSquareMatrix_inr]

/-- Simple reflections are involutions on the nonzero-weight coordinates. -/
private theorem basisReflection_involutive_of_weight_ne_zero (i : Fin 4) (a : Fin 26)
    (ha : f4ShortRootWeight a ≠ 0) : basisReflection i (basisReflection i a) = a := by
  revert i a
  decide +kernel

/-- Paths from coordinate zero to every nonzero-weight coordinate in the simple-reflection
graph. The entries at the two zero-weight coordinates are unused. -/
private def reflectionPath : Fin 26 → List (Fin 4) := ![
  [], [3], [3, 2], [3, 2, 1], [3, 2, 1, 0], [3, 2, 1, 2],
  [3, 2, 1, 0, 2], [3, 2, 1, 2, 3], [3, 2, 1, 0, 2, 1],
  [3, 2, 1, 0, 2, 3], [3, 2, 1, 0, 2, 1, 2],
  [3, 2, 1, 0, 2, 1, 3], [], [], [3, 2, 1, 0, 2, 1, 3, 2],
  [3, 2, 1, 0, 2, 1, 2, 3], [3, 2, 1, 0, 2, 1, 3, 2, 1],
  [3, 2, 1, 0, 2, 1, 2, 3, 2], [3, 2, 1, 0, 2, 1, 3, 2, 1, 0],
  [3, 2, 1, 0, 2, 1, 2, 3, 2, 1], [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0],
  [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 2],
  [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2],
  [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1],
  [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2],
  [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3]]

/-- The tabulated reflection paths reach every nonzero-weight coordinate. -/
private theorem foldl_reflectionPath (a : Fin 26) (ha : f4ShortRootWeight a ≠ 0) :
    (reflectionPath a).foldl (fun b i ↦ basisReflection i b) 0 = a := by
  revert a
  decide +kernel

/-! ## Invariant coordinate vectors -/

/-- A unit entry of a root point moves membership of a coordinate vector to a nonzero-weight
coordinate. Other entries in the image are discarded by the weight projection. -/
private theorem single_mem_of_unitRootMatrix
    (N : Subcomodule k (coordinateHopfAlgebra k) (Fin 26 → k))
    (j : Fin 4 ⊕ Fin 4) {a b : Fin 26} (hb : f4ShortRootWeight b ≠ 0)
    (hab : unitRootMatrix j b a = 1) (ha : Pi.single a (1 : k) ∈ N) :
    Pi.single b (1 : k) ∈ N := by
  have hact := points_mulVec_mem k N (rootSubgroupPoints j k (Multiplicative.ofAdd 1)) ha
  have hcomponent := single_smul_mem k N hact b hb
  rw [Matrix.mulVec_single_one, coe_rootSubgroupPoints_one] at hcomponent
  simp only [Matrix.col_apply, Matrix.map_apply, hab, Int.cast_one, one_smul] at hcomponent
  simpa using hcomponent

/-- Membership of nonzero-weight coordinate vectors is preserved by every simple reflection. -/
private theorem single_basisReflection_mem
    (N : Subcomodule k (coordinateHopfAlgebra k) (Fin 26 → k))
    (a : Fin 26) (ha : f4ShortRootWeight a ≠ 0) (i : Fin 4)
    (hmem : Pi.single a (1 : k) ∈ N) :
    Pi.single (basisReflection i a) (1 : k) ∈ N :=
  single_mem_of_unitRootMatrix k N (reflectionGenerator i a)
    (basisReflection_weight_ne_zero i a ha) (unitRootMatrix_reflectionGenerator i a ha) hmem

/-- A subcomodule containing one nonzero-weight coordinate vector contains all twenty-four of
them. -/
private theorem all_nonzeroWeight_single_mem
    (N : Subcomodule k (coordinateHopfAlgebra k) (Fin 26 → k))
    {a : Fin 26} (ha : f4ShortRootWeight a ≠ 0) (hmem : Pi.single a (1 : k) ∈ N) :
    ∀ b, f4ShortRootWeight b ≠ 0 → Pi.single b (1 : k) ∈ N := by
  let reflect : Fin 4 → {b : Fin 26 // f4ShortRootWeight b ≠ 0} →
      {b : Fin 26 // f4ShortRootWeight b ≠ 0} :=
    fun i b ↦ ⟨basisReflection i b, basisReflection_weight_ne_zero i b b.property⟩
  have hinvolutive (i : Fin 4) : Function.Involutive (reflect i) := by
    intro b
    apply Subtype.ext
    exact basisReflection_involutive_of_weight_ne_zero i b b.property
  have hreflect (b : {b : Fin 26 // f4ShortRootWeight b ≠ 0}) (i : Fin 4)
      (hb : Pi.single b.1 (1 : k) ∈ N) : Pi.single (reflect i b).1 (1 : k) ∈ N :=
    single_basisReflection_mem k N b b.property i hb
  have coe_foldl_reflect (l : List (Fin 4))
      (b : {b : Fin 26 // f4ShortRootWeight b ≠ 0}) :
      (l.foldl (fun c i ↦ reflect i c) b).1 =
        l.foldl (fun c i ↦ basisReflection i c) b.1 := by
    symm
    exact List.foldl_hom₂ l (fun c (_ : Unit) ↦ c.1) (fun c i ↦ reflect i c)
      (fun u _ ↦ u) (fun c i ↦ basisReflection i c) b () (by intros; rfl)
  have hseed : Pi.single 0 (1 : k) ∈ N := by
    have hpath : (reflectionPath a).foldl (fun b i ↦ reflect i b) ⟨0, by decide⟩ =
        ⟨a, ha⟩ := by
      apply Subtype.ext
      rw [coe_foldl_reflect]
      exact foldl_reflectionPath a ha
    apply (predicate_foldl_iff_of_involutive
      (fun b : {b : Fin 26 // f4ShortRootWeight b ≠ 0} ↦ Pi.single b.1 (1 : k) ∈ N)
      reflect hinvolutive hreflect (reflectionPath a) ⟨0, by decide⟩).mp
    rwa [hpath]
  intro b hb
  have hforward := (predicate_foldl_iff_of_involutive
    (fun c : {c : Fin 26 // f4ShortRootWeight c ≠ 0} ↦ Pi.single c.1 (1 : k) ∈ N)
    reflect hinvolutive hreflect (reflectionPath b) ⟨0, by decide⟩).mpr hseed
  have hpath : (reflectionPath b).foldl (fun c i ↦ reflect i c) ⟨0, by decide⟩ =
      ⟨b, hb⟩ := by
    apply Subtype.ext
    rw [coe_foldl_reflect]
    exact foldl_reflectionPath b hb
  rwa [hpath] at hforward

/-! ## The zero-weight plane -/

/-- The third positive simple-root point reads the first zero-weight coordinate into coordinate
ten; the second zero-weight coordinate has coefficient two and hence vanishes in characteristic
two. -/
private theorem rootSubgroupPoints_inl_three_mulVec_zeroWeight_apply_ten (x y : k) :
    (((rootSubgroupPoints (.inl 3) k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 26) k) : Matrix (Fin 26) (Fin 26) k) *ᵥ
          (x • Pi.single 12 1 + y • Pi.single 13 1)) 10 = x := by
  have htwo₂ : (2 : ZMod 2) = 0 := by decide
  have htwo : (2 : k) = 0 := by
    rw [← map_ofNat (algebraMap (ZMod 2) k) 2, htwo₂, map_zero]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    Matrix.mulVec_single_one, Matrix.mulVec_single_one, coe_rootSubgroupPoints_one]
  simp [unitRootMatrix, rootMatrix_inl, rootDividedSquareMatrix_inl, raisingTarget,
    raisingCoeff, raisingDividedSquareTarget, htwo]

/-- The second positive simple-root point reads the second zero-weight coordinate into coordinate
eleven. -/
private theorem rootSubgroupPoints_inl_two_mulVec_single_thirteen_apply_eleven (y : k) :
    (((rootSubgroupPoints (.inl 2) k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 26) k) : Matrix (Fin 26) (Fin 26) k) *ᵥ
          (y • Pi.single 13 1)) 11 = y := by
  rw [Matrix.mulVec_smul, Matrix.mulVec_single_one, coe_rootSubgroupPoints_one]
  simp [unitRootMatrix, rootMatrix_inl, rootDividedSquareMatrix_inl, raisingTarget,
    raisingCoeff, raisingDividedSquareTarget]

/-- The second positive simple-root point sends coordinate fourteen to the first zero-weight
coordinate, with no component in the second. -/
private theorem zeroWeightCoordinates_rootSubgroupPoints_inl_two_single_fourteen :
    let v :=
      ((rootSubgroupPoints (.inl 2) k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 26) k) : Matrix (Fin 26) (Fin 26) k) *ᵥ
          Pi.single 14 1
    v 12 = 1 ∧ v 13 = 0 := by
  simp [rootMatrix_inl, rootDividedSquareMatrix_inl, raisingTarget, raisingCoeff,
    raisingDividedSquareTarget]

/-- The third positive simple-root point sends coordinate fifteen to the second zero-weight
coordinate, with no component in the first. -/
private theorem zeroWeightCoordinates_rootSubgroupPoints_inl_three_single_fifteen :
    let v :=
      ((rootSubgroupPoints (.inl 3) k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 26) k) : Matrix (Fin 26) (Fin 26) k) *ᵥ
          Pi.single 15 1
    v 12 = 0 ∧ v 13 = 1 := by
  simp [rootMatrix_inl, rootDividedSquareMatrix_inl, raisingTarget, raisingCoeff,
    raisingDividedSquareTarget]

/-- Every nonzero subcomodule contains a coordinate vector of nonzero weight. If a nonzero vector
starts entirely in the two-dimensional zero-weight space, a simple-root point moves one of its
coordinates to a nonzero weight. -/
private theorem exists_nonzeroWeight_single_mem_of_ne_bot
    (N : Subcomodule k (coordinateHopfAlgebra k) (Fin 26 → k)) (hN : N ≠ ⊥) :
    ∃ a, f4ShortRootWeight a ≠ 0 ∧ Pi.single a (1 : k) ∈ N := by
  obtain ⟨v, hv, hv0⟩ := N.ne_bot_iff.mp hN
  by_cases hcoordinate : ∃ a, f4ShortRootWeight a ≠ 0 ∧ v a ≠ 0
  · obtain ⟨a, ha, hva⟩ := hcoordinate
    refine ⟨a, ha, ?_⟩
    have hscaled := N.toSubmodule.smul_mem (v a)⁻¹ (single_smul_mem k N hv a ha)
    rw [← Subcomodule.mem_toSubmodule]
    simpa only [inv_smul_smul₀ hva] using hscaled
  · push Not at hcoordinate
    have hv_eq : v = v 12 • Pi.single 12 1 + v 13 • Pi.single 13 1 := by
      ext a
      by_cases ha : f4ShortRootWeight a = 0
      · rcases (f4ShortRootWeight_eq_zero_iff a).mp ha with rfl | rfl <;> simp
      · have hva : v a = 0 := hcoordinate a ha
        have h12 : a ≠ 12 := fun h ↦ ha ((f4ShortRootWeight_eq_zero_iff a).mpr (Or.inl h))
        have h13 : a ≠ 13 := fun h ↦ ha ((f4ShortRootWeight_eq_zero_iff a).mpr (Or.inr h))
        simp [hva, h12, h13]
    by_cases h12 : v 12 = 0
    · have h13 : v 13 ≠ 0 := by
        intro h13
        apply hv0
        rw [hv_eq, h12, h13]
        simp
      refine ⟨11, by decide, ?_⟩
      have hzero : v 12 • Pi.single 12 1 + v 13 • Pi.single 13 1 ∈ N := hv_eq ▸ hv
      have hvin : v 13 • Pi.single 13 1 ∈ N := by simpa only [h12, zero_smul, zero_add] using hzero
      have hact := points_mulVec_mem k N
        (rootSubgroupPoints (.inl 2) k (Multiplicative.ofAdd 1)) hvin
      have hscaled := single_smul_mem k N hact 11 (by decide)
      rw [rootSubgroupPoints_inl_two_mulVec_single_thirteen_apply_eleven] at hscaled
      have hinv := N.toSubmodule.smul_mem (v 13)⁻¹ hscaled
      rw [← Subcomodule.mem_toSubmodule]
      simpa only [inv_smul_smul₀ h13] using hinv
    · refine ⟨10, by decide, ?_⟩
      have hvin : v 12 • Pi.single 12 1 + v 13 • Pi.single 13 1 ∈ N := hv_eq ▸ hv
      have hact := points_mulVec_mem k N
        (rootSubgroupPoints (.inl 3) k (Multiplicative.ofAdd 1)) hvin
      have hscaled := single_smul_mem k N hact 10 (by decide)
      rw [rootSubgroupPoints_inl_three_mulVec_zeroWeight_apply_ten] at hscaled
      have hinv := N.toSubmodule.smul_mem (v 12)⁻¹ hscaled
      rw [← Subcomodule.mem_toSubmodule]
      simpa only [inv_smul_smul₀ h12] using hinv

/-- Once all nonzero-weight coordinate vectors belong to a subcomodule, so do both zero-weight
coordinate vectors. -/
private theorem zeroWeight_singles_mem_of_nonzeroWeight_singles_mem
    (N : Subcomodule k (coordinateHopfAlgebra k) (Fin 26 → k))
    (h : ∀ a, f4ShortRootWeight a ≠ 0 → Pi.single a (1 : k) ∈ N) :
    Pi.single 12 (1 : k) ∈ N ∧ Pi.single 13 (1 : k) ∈ N := by
  constructor
  · have hact := points_mulVec_mem k N
      (rootSubgroupPoints (.inl 2) k (Multiplicative.ofAdd 1)) (h 14 (by decide))
    have hzero := zeroWeightComponent_mem k N hact
    have hcoordinates := zeroWeightCoordinates_rootSubgroupPoints_inl_two_single_fourteen k
    simpa only [hcoordinates.1, hcoordinates.2, one_smul, zero_smul, add_zero] using hzero
  · have hact := points_mulVec_mem k N
      (rootSubgroupPoints (.inl 3) k (Multiplicative.ofAdd 1)) (h 15 (by decide))
    have hzero := zeroWeightComponent_mem k N hact
    have hcoordinates := zeroWeightCoordinates_rootSubgroupPoints_inl_three_single_fifteen k
    simpa only [hcoordinates.1, hcoordinates.2, zero_smul, one_smul, zero_add] using hzero

/-- **The standard comodule of the short-root type-`F₄` carrier is simple over every field of
characteristic two.** -/
instance instIsSimpleOrderSubcomodule :
    IsSimpleOrder (Subcomodule k (coordinateHopfAlgebra k) (Fin 26 → k)) := by
  have hbot_ne_top :
      (⊥ : Subcomodule k (coordinateHopfAlgebra k) (Fin 26 → k)) ≠ ⊤ := by
    intro h
    have hmem : Pi.single 0 (1 : k) ∈
        (⊥ : Subcomodule k (coordinateHopfAlgebra k) (Fin 26 → k)) := h ▸ Submodule.mem_top
    simp at hmem
  let _ : Nontrivial (Subcomodule k (coordinateHopfAlgebra k) (Fin 26 → k)) :=
    ⟨⟨⊥, ⊤, hbot_ne_top⟩⟩
  constructor
  intro N
  by_cases hN : N = ⊥
  · exact Or.inl hN
  · right
    obtain ⟨a, ha, hseed⟩ := exists_nonzeroWeight_single_mem_of_ne_bot k N hN
    have hnonzero := all_nonzeroWeight_single_mem k N ha hseed
    obtain ⟨h12, h13⟩ := zeroWeight_singles_mem_of_nonzeroWeight_singles_mem k N hnonzero
    apply top_unique
    intro v _
    rw [← (Pi.basisFun k (Fin 26)).sum_repr v]
    apply N.toSubmodule.sum_mem
    intro b _
    apply N.toSubmodule.smul_mem
    by_cases hb : f4ShortRootWeight b = 0
    · rcases (f4ShortRootWeight_eq_zero_iff b).mp hb with rfl | rfl
      · simpa using h12
      · simpa using h13
    · simpa using hnonzero b hb

end

end TauCeti.F4ShortRoot.PrimeField
