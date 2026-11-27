/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.Iwasawa
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Perfect
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Primitive

/-!
# Simplicity of projective special unitary groups

Combining `MulAction.IwasawaStructure.isSimpleGroup_quotient_center` with
`Matrix.unitaryIwasawaStructure`, `Matrix.isPreprimitive_isotropicPoints`,
`Matrix.nontrivial_specialIsometryGroup`, and
`Matrix.mem_center_specialIsometryGroup_of_forall_smul_eq`, we prove
`Matrix.isSimpleGroup_quotient_center_specialIsometryGroup_of_commutator_eq_top` and
`Matrix.isSimpleGroup_quotient_center_specialIsometryGroup`.

## References

* K. Iwasawa, *Über die Einfachheit der speziellen projektiven Gruppen* (1941).
* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapter 10, Theorems 10.9 and 10.20.
-/

public section

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] {Q : Matrix n n K} {σ : K →+* K}
  {ε : K}

/-- **Iwasawa's theorem for projective special unitary groups**: for involutive `σ` and invertible
`ε`-Hermitian `Q` with surjective `ε`-trace, nonzero skew-trace, nonempty
`Matrix.isotropicPoints Q σ`, and either a `σ`-fixed scalar outside `{0, 1}`, `Fintype.card n ≤ 2`,
or Witt index at least two, if `Q.specialIsometryGroup σ` is perfect then its central quotient is
simple. -/
theorem isSimpleGroup_quotient_center_specialIsometryGroup_of_commutator_eq_top
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    [Nonempty (Q.isotropicPoints σ)]
    (hgen : (∃ a : K, a ≠ 0 ∧ a ≠ 1 ∧ σ a = a) ∨ Fintype.card n ≤ 2 ∨
      ∃ u w : n → K, u ≠ 0 ∧ w ∉ K ∙ u ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 ∧
        (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0)
    (hcomm : commutator (Q.specialIsometryGroup σ) = ⊤) :
    IsSimpleGroup (Q.specialIsometryGroup σ ⧸ Subgroup.center (Q.specialIsometryGroup σ)) := by
  have : Group.IsPerfect (Q.specialIsometryGroup σ) := ⟨hcomm⟩
  have := nontrivial_specialIsometryGroup hσ hQ hdet hadm
  have := isPreprimitive_isotropicPoints hσ hQ hdet htr hadm
  exact (Q.unitaryIwasawaStructure hσ hQ hdet htr hadm hgen).isSimpleGroup_quotient_center
    fun _ hg ↦ mem_center_specialIsometryGroup_of_forall_smul_eq hσ hQ hdet htr hadm hg

/-- **Simplicity of a projective special unitary group** under any of the three perfectness
hypotheses of `Matrix.commutator_specialIsometryGroup_eq_top`. -/
theorem isSimpleGroup_quotient_center_specialIsometryGroup
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    [Nonempty (Q.isotropicPoints σ)]
    (hperf : (∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1 ∧ σ c = c) ∨
      (∃ u w : n → K, u ≠ 0 ∧ w ∉ K ∙ u ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 ∧
        (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) ∨
      (3 ≤ Fintype.card n ∧ ∃ c : K, c ≠ 0 ∧ c * σ c ≠ 1)) :
    IsSimpleGroup (Q.specialIsometryGroup σ ⧸ Subgroup.center (Q.specialIsometryGroup σ)) :=
  isSimpleGroup_quotient_center_specialIsometryGroup_of_commutator_eq_top hσ hQ hdet htr hadm
    (exists_ne_one_and_apply_eq_self_or_card_le_two_or_exists_notMem_span hσ hperf)
    (commutator_specialIsometryGroup_eq_top hσ hQ hdet htr hadm hperf)

end Matrix

end
