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

Let `σ` be an involution of a field `K`, let `Q` be an invertible `ε`-Hermitian matrix,
`(Q.map σ)ᵀ = ε • Q`, whose trace `t ↦ t + ε σ(t)` is onto `{s : K | σ s = ε * s}` and has a
nonzero kernel element (`∃ d ≠ 0, d + ε * σ d = 0`), and suppose `Matrix.isotropicPoints Q σ` is
nonempty. Applying `MulAction.IwasawaStructure.isSimpleGroup_quotient_center` to
`Matrix.unitaryIwasawaStructure`, `Matrix.isPreprimitive_isotropicPoints`,
`Matrix.nontrivial_specialIsometryGroup`, and
`Matrix.mem_center_specialIsometryGroup_of_forall_smul_eq`, this file proves that the central
quotient `Q.specialIsometryGroup σ ⧸ Subgroup.center (Q.specialIsometryGroup σ)` is simple whenever
the three-way generation condition holds and `Q.specialIsometryGroup σ` is perfect, and in
particular whenever one of the three perfectness conditions of
`Matrix.commutator_specialIsometryGroup_eq_top` holds.

## Main results

* `Matrix.isSimpleGroup_quotient_center_specialIsometryGroup_of_commutator_eq_top`: simplicity of
  the central quotient from the three-way generation condition and
  `commutator (Q.specialIsometryGroup σ) = ⊤`.
* `Matrix.isSimpleGroup_quotient_center_specialIsometryGroup`: self-contained simplicity of the
  central quotient directly from the three-way perfectness condition `hperf`.

## References

* K. Iwasawa, *Über die Einfachheit der speziellen projektiven Gruppen* (1941); D. E. Taylor, *The
  Geometry of the Classical Groups* (1992), Theorem 11.29.
-/

public section

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] {Q : Matrix n n K} {σ : K →+* K}
  {ε : K}

/-- **Iwasawa's theorem for projective special unitary groups.** Let `σ` be an involution of `K`,
let `Q` be an invertible `ε`-Hermitian matrix whose trace `t ↦ t + ε σ(t)` is onto
`{s : K | σ s = ε * s}` and has a nonzero kernel element, and suppose `Q.isotropicPoints σ` is
nonempty. If either `σ` fixes a scalar outside `{0, 1}`, `Fintype.card n ≤ 2`, or `Q` has Witt
index at least two, and `Q.specialIsometryGroup σ` is perfect, then its quotient by its centre is
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

/-- **Simplicity of a projective special unitary group.** Let `σ` be an involution of `K`, let `Q`
be an invertible `ε`-Hermitian matrix whose trace `t ↦ t + ε σ(t)` is onto `{s : K | σ s = ε * s}`
and has a nonzero kernel element, and suppose `Q.isotropicPoints σ` is nonempty. If the fixed field
of `σ` contains a nonzero element whose square is not `1`, or `Q` has Witt index at least two, or
`3 ≤ Fintype.card n` and some nonzero `c : K` satisfies `c * σ c ≠ 1`, then the central quotient of
`Q.specialIsometryGroup σ` is simple. -/
theorem isSimpleGroup_quotient_center_specialIsometryGroup
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    [Nonempty (Q.isotropicPoints σ)]
    (hperf : (∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1 ∧ σ c = c) ∨
      (∃ u w : n → K, u ≠ 0 ∧ w ∉ K ∙ u ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 ∧
        (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) ∨
      (3 ≤ Fintype.card n ∧ ∃ c : K, c ≠ 0 ∧ c * σ c ≠ 1)) :
    IsSimpleGroup (Q.specialIsometryGroup σ ⧸ Subgroup.center (Q.specialIsometryGroup σ)) := by
  have hgen : (∃ a : K, a ≠ 0 ∧ a ≠ 1 ∧ σ a = a) ∨ Fintype.card n ≤ 2 ∨
      ∃ u w : n → K, u ≠ 0 ∧ w ∉ K ∙ u ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 ∧
        (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0 := by
    rcases hperf with ⟨c, hc0, hcsq, hσc⟩ | hwitt | ⟨_, c, hc0, hc1⟩
    · exact Or.inl ⟨c, hc0, fun h1 ↦ hcsq (by simp [h1]), hσc⟩
    · exact Or.inr (Or.inr hwitt)
    · exact Or.inl ⟨c * σ c, mul_ne_zero hc0 ((map_ne_zero σ).mpr hc0), hc1,
        by rw [map_mul, hσ c, mul_comm]⟩
  exact isSimpleGroup_quotient_center_specialIsometryGroup_of_commutator_eq_top hσ hQ hdet htr hadm
    hgen (commutator_specialIsometryGroup_eq_top hσ hQ hdet htr hadm hperf)

end Matrix

end
