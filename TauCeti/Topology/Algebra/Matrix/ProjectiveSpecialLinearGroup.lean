/-
Copyright (c) 2026 The Tau Ceti authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti authors
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.FinTwo

import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Topology on `PSL(2, ℝ)`

The quotient topology on the projective special linear group `PSL(2, ℝ)` is Hausdorff
because the center of `SL(2, ℝ)` is finite, hence closed. Conjugation preserves discrete
subgroups. The natural injection `PSL(2, ℤ) → PSL(2, ℝ)` is a topological embedding, so its
range is discrete. Finally, the translations
`Matrix.ProjectiveSpecialLinearGroup.upperRightHom x` depend continuously on `x`.

## Main results

* `isEmbedding_psl2zToPSL2R`: the natural injection from the integral projective special linear
  group to the real one is a topological embedding.
* `Matrix.ProjectiveSpecialLinearGroup.continuous_upperRightHom`: projective translations depend
  continuously on their parameter.
-/

public section

open scoped MatrixGroups Pointwise

open Matrix.SpecialLinearGroup

namespace TauCeti

/-- The projective special linear group `PSL(2, ℝ)` is Hausdorff. -/
instance : T2Space PSL(2, ℝ) := by
  let _ : Finite (Subgroup.center SL(2, ℝ)) :=
    Matrix.SpecialLinearGroup.finite_center (R := ℝ)
  let _ : IsClosed ((Subgroup.center SL(2, ℝ) : Subgroup SL(2, ℝ)) : Set SL(2, ℝ)) :=
    Set.toFinite _ |>.isClosed
  infer_instance

/-- The natural injection `PSL(2, ℤ) → PSL(2, ℝ)` is a topological embedding.

This is the map induced on central quotients by the closed embedding
`SL(2, ℤ) → SL(2, ℝ)`. The image of the latter contains the full center `{ ±I }` of
`SL(2, ℝ)`, so passing to the two quotient topologies preserves the embedding. -/
theorem isEmbedding_psl2zToPSL2R :
    Topology.IsEmbedding (psl2zToPSL2R : PSL(2, ℤ) → PSL(2, ℝ)) := by
  let f : SL(2, ℤ) → SL(2, ℝ) :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)
  let p : SL(2, ℤ) → PSL(2, ℤ) :=
    QuotientGroup.mk
  let q : SL(2, ℝ) → PSL(2, ℝ) :=
    QuotientGroup.mk
  apply isEmbedding_of_isOpenQuotientMap_of_isInducing
    (f := f) (p := p) (q := q)
  · funext g
    dsimp only [Function.comp_apply, p, q, f]
    rw [psl2zToPSL2R_mk]
    exact sl2zToPSL2R_apply g
  · exact Real.isClosedEmbedding_intCast.specialLinearGroup_map.1.isInducing
  · exact QuotientGroup.isQuotientMap_mk _
  · exact QuotientGroup.isOpenQuotientMap_mk
  · exact psl2zToPSL2R_injective
  · dsimp only [q]
    have hf_range : Set.range f = ((Matrix.SpecialLinearGroup.map (n := Fin 2)
        (Int.castRingHom ℝ)).range : Set SL(2, ℝ)) := rfl
    rw [hf_range, QuotientGroup.preimage_image_mk_eq_mul]
    intro g hg
    rcases hg with ⟨a, ha, c, hc, rfl⟩
    apply Subgroup.mul_mem _ ha
    have hc' : c ∈ Subgroup.center SL(2, ℝ) := hc
    rw [Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one] at hc'
    rcases hc' with rfl | rfl
    · exact Subgroup.one_mem _
    · exact ⟨-1, by simp⟩

/-- The image of `PSL(2, ℤ)` in `PSL(2, ℝ)` is a discrete subgroup. -/
instance : DiscreteTopology psl2zToPSL2R.range := by
  let _ : DiscreteTopology PSL(2, ℤ) :=
    QuotientGroup.discreteTopology (by simp)
  exact isEmbedding_psl2zToPSL2R.toHomeomorph.discreteTopology

end TauCeti

namespace Matrix.ProjectiveSpecialLinearGroup

/-- The translation `upperRightHom x ∈ PSL(2, R)` depends continuously on `x`. -/
@[fun_prop]
theorem continuous_upperRightHom {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] : Continuous (upperRightHom : R → PSL(2, R)) := by
  have : Continuous fun x : R ↦ SpecialLinearGroup.transvection (zero_ne_one' (Fin 2)) x :=
    Continuous.subtype_mk (continuous_const.add (continuous_matrix fun i j ↦ by
      simp only [single_apply]
      split_ifs <;> fun_prop)) _
  exact (continuous_quot_mk.comp this).congr fun x ↦ (upperRightHom_apply x).symm

end Matrix.ProjectiveSpecialLinearGroup
