/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection
-- Non-public: the elementary subgroup lies in the commutator subgroup, used only in a proof below.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary

/-!
# The commutator subgroup of the general linear group

Over a field with an element different from zero and one, the abstract commutator subgroup of
`GLₙ` is the determinant kernel. Conjugation by a diagonal matrix expresses every elementary
transvection as a commutator. The generation of `SLₙ` by transvections then supplies the reverse
inclusion to the one given by the determinant.

The hypothesis includes every field with more than two elements. It is needed in dimension two:
`GL₂(𝔽₂)` has a proper commutator subgroup, although its determinant is trivial. The statements
also include dimensions zero and one.

The proof uses `Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field`
and `TauCeti.elementarySubgroup_le_commutator_of_isUnit_sub_one`, which holds over any ring with a
unit `a` such that `a - 1` is a unit.
-/

public section

open Matrix
open scoped commutatorElement

namespace TauCeti

noncomputable section

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι}

/-- Over a field with more than two elements, the abstract commutator subgroup of `GLₙ` is
exactly the kernel of the unit-valued determinant. -/
theorem _root_.Matrix.GeneralLinearGroup.commutator_eq_ker_det {a : K}
    (ha₀ : a ≠ 0) (ha₁ : a ≠ 1) :
    commutator (GL ι K) = (GeneralLinearGroup.det : GL ι K →* Kˣ).ker := by
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro g _ h _
    simp [MonoidHom.mem_ker, commutatorElement_def]
  · intro g hg
    rw [← SpecialLinearGroup.range_toGL_eq_ker_det] at hg
    obtain ⟨s, rfl⟩ := hg
    have hgen := SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
      (ι := ι) (K := K)
    have hle : Subgroup.closure (Set.range (TransvectionStruct.toSpecialLinearGroup :
        TransvectionStruct ι K → SpecialLinearGroup ι K)) ≤
        (commutator (GL ι K)).comap SpecialLinearGroup.toGL := by
      rw [Subgroup.closure_le]
      rintro _ ⟨v, rfl⟩
      rcases v with ⟨i, j, hij, c⟩
      apply (Subgroup.mem_comap).mpr
      rw [TransvectionStruct.toSpecialLinearGroup_mk,
        toGL_transvection_eq_transvectionUnit]
      exact elementarySubgroup_le_commutator_of_isUnit_sub_one (Units.mk0 a ha₀)
        (sub_ne_zero.2 ha₁).isUnit (transvectionUnit_mem_elementarySubgroup hij c)
    rw [hgen] at hle
    exact hle (Subgroup.mem_top s)

end

end TauCeti
