/-
Copyright (c) 2026 The Tau Ceti authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti authors
-/
module

public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.FinTwo
public import TauCeti.Topology.Algebra.Group.Subgroup

import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Topology on projective special linear groups

The quotient topology on a projective special linear group over a `T0` topological ring is
Hausdorff because the center of the special linear group is closed. The natural injection
`PSL(2, ℤ) → PSL(2, ℝ)` is a topological embedding, so its range is discrete. Finally, the
translations `Matrix.ProjectiveSpecialLinearGroup.upperRightHom x` depend continuously on `x`
for any topology on the coefficient ring.

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

/-- The natural injection `PSL(2, ℤ) → PSL(2, ℝ)` is a topological embedding.

Thus `PSL(2, ℤ)` has the topology induced from `PSL(2, ℝ)` on its image; in particular, the
projective integral image is a discrete subgroup. -/
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
  · dsimp only [q, f]
    rw [← MonoidHom.coe_range, QuotientGroup.preimage_image_mk_eq_mul]
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

/-- The translation `upperRightHom x ∈ PSL(2, R)` depends continuously on `x` for any topology
on `R`. -/
@[fun_prop]
theorem continuous_upperRightHom {R : Type*} [CommRing R] [TopologicalSpace R] :
    Continuous (upperRightHom : R → PSL(2, R)) := by
  have h : Continuous fun x : R ↦
      (SpecialLinearGroup.transvection (zero_ne_one' (Fin 2)) x : Matrix (Fin 2) (Fin 2) R) := by
    refine continuous_matrix fun i j ↦ ?_
    simp only [SpecialLinearGroup.transvection_coe, Matrix.add_apply]
    fin_cases i <;> fin_cases j <;> simp [continuous_const, continuous_id']
  exact (continuous_quot_mk.comp (Topology.IsInducing.subtypeVal.continuous_iff.mpr h)).congr
    fun x ↦ (upperRightHom_apply x).symm

end Matrix.ProjectiveSpecialLinearGroup
