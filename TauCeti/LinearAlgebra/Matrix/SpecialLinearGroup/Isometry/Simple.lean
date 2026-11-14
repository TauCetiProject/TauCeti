/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.Iwasawa
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Perfect

/-!
# Simplicity of projective special unitary groups

Applying `MulAction.IwasawaStructure.isSimpleGroup_quotient_center` to
`Matrix.unitaryIwasawaStructure`, `Matrix.isPreprimitive_isotropicPoints`, and
`Matrix.mem_center_specialIsometryGroup_of_forall_smul_eq`, this file proves that the central
quotient of a perfect special unitary group is simple.

## Main results

* `Matrix.nontrivial_specialIsometryGroup` and
  `Matrix.isSimpleGroup_quotient_center_specialIsometryGroup`.

## References

* K. Iwasawa, *Über die Einfachheit der speziellen projektiven Gruppen* (1941); Taylor, Thm. 11.29.
-/

public section
namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] {Q : Matrix n n K} {σ : K →+* K}
  {ε : K}
/-- A special unitary group with an isotropic point and a nonzero admissible transvection parameter
is nontrivial. -/
theorem nontrivial_specialIsometryGroup (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q)
    (hdet : Q.det ≠ 0) (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0) [Nonempty (Q.isotropicPoints σ)] :
    Nontrivial (Q.specialIsometryGroup σ) := by
  obtain ⟨e, f, he₀, -, he, -, hef, -, -, -⟩ :=
    exists_hyperbolic_pair_of_isotropicPoints hσ hQ hdet htr
  obtain ⟨d, hd, hdε⟩ := hadm
  obtain ⟨g, hg, hcg⟩ := exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ he hdε
  refine ⟨⟨g, hg⟩, 1, fun h1 ↦ ?_⟩
  have hf_eq := congrArg (fun x : Q.specialIsometryGroup σ ↦ (x : Matrix n n K) *ᵥ f) h1
  simp only [hcg, unitaryTransvection_mulVec, hef, mul_one, Subgroup.coe_one,
    SpecialLinearGroup.coe_one, one_mulVec, add_eq_left, smul_eq_zero] at hf_eq
  exact hf_eq.elim hd he₀
/-- **Iwasawa's theorem for projective special unitary groups.** When unitary transvections
generate `Q.specialIsometryGroup σ` and `Q.specialIsometryGroup σ` is perfect, its quotient by its
centre is simple. -/
theorem isSimpleGroup_quotient_center_specialIsometryGroup (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    [Nonempty (Q.isotropicPoints σ)]
    (hgen : (∃ a : K, a ≠ 0 ∧ a ≠ 1 ∧ σ a = a) ∨ Fintype.card n ≤ 2 ∨
      ∃ u w : n → K, u ≠ 0 ∧ w ∉ K ∙ u ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 ∧
        (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0)
    (hcomm : commutator (Q.specialIsometryGroup σ) = ⊤) :
    IsSimpleGroup (Q.specialIsometryGroup σ ⧸ Subgroup.center (Q.specialIsometryGroup σ)) := by
  have : Group.IsPerfect (Q.specialIsometryGroup σ) := ⟨hcomm⟩
  have := nontrivial_specialIsometryGroup hσ hQ hdet htr hadm
  have := isPreprimitive_isotropicPoints hσ hQ hdet htr hadm
  exact (Q.unitaryIwasawaStructure hσ hQ hdet htr hadm hgen).isSimpleGroup_quotient_center
    fun _ hg ↦ mem_center_specialIsometryGroup_of_forall_smul_eq hσ hQ hdet htr hadm hg
end Matrix

end
