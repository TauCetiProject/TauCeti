/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Grading.UnblockedChain
public import TauCeti.KnotTheory.Grid.Homology.Unblocked
import TauCeti.Algebra.DirectSum.Internal

/-!
# The bigrading of unblocked grid homology

The homogeneous cycles and their classes give an internal direct sum decomposition of `GH⁻`
by `(O-Maslov, Alexander)` degree. The differential has degree `(-1, 0)`, and each variable
has degree `(-2, -1)`. Homogeneous projection preserves both cycles and boundaries, so a class
has a homogeneous representative precisely when it belongs to the corresponding piece.

These pieces are modules over the ground ring, not over the polynomial coefficient ring.
As for the chain bigrading, an odd number of link components ensures integral Alexander degrees.
The decomposition allows degree-preserving homology comparisons to be restricted to each
bidegree without choosing cycle representatives.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3 and 4.6.
-/

public section

open MvPolynomial

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*)

section Cycles

variable [CommSemiring R]

/-- The cycles of `GC⁻` homogeneous of bidegree `g`. -/
noncomputable def bigradedUnblockedCyclesPiece (g : ℤ × ℤ) :
    Submodule R (LinearMap.ker (G.1.unblockedDifferential R)) :=
  (G.bigradedChainMinusPiece R g).comap
    ((LinearMap.ker (G.1.unblockedDifferential R)).subtype.restrictScalars R)

/-- Homogeneity of a cycle is homogeneity of its underlying chain. -/
@[simp]
theorem mem_bigradedUnblockedCyclesPiece {g : ℤ × ℤ}
    {z : LinearMap.ker (G.1.unblockedDifferential R)} :
    z ∈ G.bigradedUnblockedCyclesPiece R g ↔
      (z : GridChainMinus R n) ∈ G.bigradedChainMinusPiece R g := Iff.rfl

end Cycles

variable [CommRing R]

private noncomputable instance chainDecomposition :
    DirectSum.Decomposition (G.bigradedChainMinusPiece R) :=
  (G.isInternal_bigradedChainMinusPiece R).chooseDecomposition

private theorem differential_decompose (g : ℤ × ℤ) (c : GridChainMinus R n) :
    G.1.unblockedDifferential R (DirectSum.decompose (G.bigradedChainMinusPiece R) c g) =
      (DirectSum.decompose (G.bigradedChainMinusPiece R)
        (G.1.unblockedDifferential R c) (g - (1, 0)) : GridChainMinus R n) :=
  DirectSum.map_decompose_shift _ _ (G.1.unblockedDifferential R).toAddMonoidHom
    (· - (1, 0)) (fun _ _ h => sub_left_injective h) (fun _ _ hc =>
      G.unblockedDifferential_mem_bigradedChainMinusPiece hc) g c

/-- The homogeneous cycle modules form an internal direct sum. -/
theorem isInternal_bigradedUnblockedCyclesPiece :
    DirectSum.IsInternal (G.bigradedUnblockedCyclesPiece R) := by
  refine DirectSum.isInternal_comap (G.bigradedChainMinusPiece R) _
    ((LinearMap.ker (G.1.unblockedDifferential R)).subtype.restrictScalars R)
    Subtype.val_injective (fun _ _ => Iff.rfl) ?_
  intro g z
  refine ⟨⟨_, ?_⟩, rfl⟩
  rw [LinearMap.mem_ker, G.differential_decompose]
  simp only [LinearMap.restrictScalars_apply, Submodule.subtype_apply,
    LinearMap.mem_ker.mp z.2, DirectSum.decompose_zero, DirectSum.zero_apply,
    ZeroMemClass.coe_zero]

private theorem decompose_boundary {c : GridChainMinus R n}
    (hc : c ∈ LinearMap.range (G.1.unblockedDifferential R)) (g : ℤ × ℤ) :
    (DirectSum.decompose (G.bigradedChainMinusPiece R) c g : GridChainMinus R n) ∈
      LinearMap.range (G.1.unblockedDifferential R) := by
  obtain ⟨b, rfl⟩ := hc
  exact ⟨_, (G.differential_decompose R (g + (1, 0)) b).trans
    (by rw [add_sub_cancel_right])⟩

variable [CharP R 2]

/-- The bidegree-`g` piece of `GH⁻`: classes of cycles homogeneous of bidegree `g`. -/
noncomputable def bigradedUnblockedHomologyPiece (g : ℤ × ℤ) :
    Submodule R (G.1.unblockedHomology R) :=
  (G.bigradedUnblockedCyclesPiece R g).map
    ((G.1.unblockedHomologyClass R).restrictScalars R)

/-- A class has bidegree `g` exactly when it has a cycle representative of that bidegree. -/
theorem mem_bigradedUnblockedHomologyPiece_iff {g : ℤ × ℤ} {y : G.1.unblockedHomology R} :
    y ∈ G.bigradedUnblockedHomologyPiece R g ↔
      ∃ z : LinearMap.ker (G.1.unblockedDifferential R),
        (z : GridChainMinus R n) ∈ G.bigradedChainMinusPiece R g ∧
          G.1.unblockedHomologyClass R z = y := by
  simp only [bigradedUnblockedHomologyPiece, Submodule.mem_map,
    mem_bigradedUnblockedCyclesPiece, LinearMap.restrictScalars_apply]

/-- The class of a homogeneous cycle lies in the homology piece of the same bidegree. -/
theorem unblockedHomologyClass_mem_bigradedUnblockedHomologyPiece {g : ℤ × ℤ}
    {z : LinearMap.ker (G.1.unblockedDifferential R)}
    (hz : (z : GridChainMinus R n) ∈ G.bigradedChainMinusPiece R g) :
    G.1.unblockedHomologyClass R z ∈ G.bigradedUnblockedHomologyPiece R g :=
  (G.mem_bigradedUnblockedHomologyPiece_iff R).mpr ⟨z, hz, rfl⟩

/-- The bigraded homology pieces span `GH⁻`. -/
theorem iSup_bigradedUnblockedHomologyPiece_eq_top :
    ⨆ g, G.bigradedUnblockedHomologyPiece R g = ⊤ := by
  simp only [bigradedUnblockedHomologyPiece]
  rw [← Submodule.map_iSup,
    (G.isInternal_bigradedUnblockedCyclesPiece R).submodule_iSup_eq_top,
    Submodule.map_top, LinearMap.range_eq_top]
  exact G.1.unblockedHomologyClass_surjective R

/-- The bigraded homology pieces are independent: a homogeneous boundary can be detected in
its own bidegree. -/
theorem iSupIndep_bigradedUnblockedHomologyPiece :
    iSupIndep (G.bigradedUnblockedHomologyPiece R) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hv0 g hg
  have hlift : ∀ i : s, ∃ z : LinearMap.ker (G.1.unblockedDifferential R),
      (z : GridChainMinus R n) ∈ G.bigradedChainMinusPiece R i ∧
        G.1.unblockedHomologyClass R z = v i := fun i =>
    (G.mem_bigradedUnblockedHomologyPiece_iff R).mp (hv i i.2)
  choose z hz hzv using hlift
  have hb : ((∑ i : s, z i : LinearMap.ker (G.1.unblockedDifferential R)) :
      GridChainMinus R n) ∈ LinearMap.range (G.1.unblockedDifferential R) := by
    rw [← GridDiagram.unblockedHomologyClass_eq_zero_iff, map_sum]
    simpa only [hzv, Finset.sum_coe_sort] using hv0
  have hproj : (DirectSum.decompose (G.bigradedChainMinusPiece R)
      (((∑ i : s, z i : LinearMap.ker (G.1.unblockedDifferential R))) : GridChainMinus R n) g :
        GridChainMinus R n) = z ⟨g, hg⟩ := by
    calc
      _ = ∑ i : s, (DirectSum.decompose (G.bigradedChainMinusPiece R)
          (z i : GridChainMinus R n) g : GridChainMinus R n) := by
        simp only [Submodule.coe_sum, DirectSum.decompose_sum, DirectSum.sum_apply]
      _ = z ⟨g, hg⟩ := by
        rw [Finset.sum_eq_single (⟨g, hg⟩ : s)
          (fun i _ hi => DirectSum.decompose_of_mem_ne _ (hz i)
            (fun h => hi (Subtype.ext h))) (by simp)]
        exact DirectSum.decompose_of_mem_same _ (hz ⟨g, hg⟩)
  rw [← hzv ⟨g, hg⟩, GridDiagram.unblockedHomologyClass_eq_zero_iff]
  exact hproj ▸ G.decompose_boundary R hb g

/-- `GH⁻` is the internal direct sum of its `(O-Maslov, Alexander)` pieces. -/
theorem isInternal_bigradedUnblockedHomologyPiece :
    DirectSum.IsInternal (G.bigradedUnblockedHomologyPiece R) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (G.iSupIndep_bigradedUnblockedHomologyPiece R)
    (G.iSup_bigradedUnblockedHomologyPiece_eq_top R)

/-- Multiplication by a grid variable lowers homology bidegree by `(2, 1)`. -/
theorem X_smul_mem_bigradedUnblockedHomologyPiece (i : Fin n) {g : ℤ × ℤ}
    {y : G.1.unblockedHomology R} (hy : y ∈ G.bigradedUnblockedHomologyPiece R g) :
    (X i : MvPolynomial (Fin n) R) • y ∈ G.bigradedUnblockedHomologyPiece R (g - (2, 1)) := by
  obtain ⟨z, hz, rfl⟩ := (G.mem_bigradedUnblockedHomologyPiece_iff R).mp hy
  rw [← map_smul]
  exact G.unblockedHomologyClass_mem_bigradedUnblockedHomologyPiece R
    (G.X_smul_mem_bigradedChainMinusPiece i hz)

end TauCeti.OddComponentGridDiagram
