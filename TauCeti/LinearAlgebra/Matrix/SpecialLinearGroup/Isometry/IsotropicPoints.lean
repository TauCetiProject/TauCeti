/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Elementary
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# The action of a special unitary group on its isotropic points

Let `σ` be an involution of a field `K`, let `Q` be an invertible `ε`-Hermitian matrix,
`(Q ^ σ)ᵀ = ε • Q` with `ε = ±1`, and let `h(x, y) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y)` be its sesquilinear
form. The special isometry group `Matrix.specialIsometryGroup Q σ` acts transitively on the
isotropic points `Matrix.isotropicPoints Q σ` of projective space, since its elementary
unitary subgroup already does (`Matrix.isPretransitive_elementaryUnitaryGroup`). When some
point is isotropic, the kernel of this action is central. Both statements use two conditions
on the trace `t ↦ t + ε σ(t)`:

* it is onto the elements `s` with `σ(s) = ε s`, the values `h(u, u)` of the form;
* it has a nonzero kernel element, so that nontrivial unitary transvections exist.

Over the field with `q²` elements, with `σ(x) = x ^ q`, both hold for `ε = ±1`
(`TauCeti.FiniteField.exists_add_neg_one_pow_mul_pow_eq` and
`TauCeti.FiniteField.exists_ne_zero_add_neg_one_pow_mul_pow_eq_zero`).

For the kernel, an element fixing every isotropic point scales each isotropic vector. Comparing
an isotropic `x₀` with an isotropic `x₀ + c v`, for isotropic `v` and `c ≠ 0`, shows that all
these scalars agree. Given a nonzero isotropic vector, the isotropic vectors span the space, so
the element is a scalar matrix. This scalar criterion,
`Matrix.exists_eq_scalar_of_forall_mulVec_eq_smul`, and the form identities used here are in
`TauCeti.LinearAlgebra.Matrix.SesquilinearForm`.

## Main results

* `Matrix.isPretransitive_isotropicPoints`: the special isometry group acts transitively on the
  isotropic points.
* `Matrix.mem_center_specialIsometryGroup_of_forall_smul_eq`: if some point is isotropic, an
  isometry fixing every isotropic point is central.

## References

* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapters 10 and 11.
* L. C. Grove, *Classical Groups and Geometric Algebra* (2002), Chapter 11.
-/

public section

open scoped LinearAlgebra.Projectivization

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] {Q : Matrix n n K} {σ : K →+* K}
  {ε : K}

/-- **The special unitary group is transitive on isotropic points.** Let `σ` be an involution,
`Q` an invertible `ε`-Hermitian matrix with `ε * ε = 1`, and suppose that the trace
`t ↦ t + ε σ(t)` is onto the elements `s` with `σ(s) = ε s` and has a nonzero kernel element.
Then the special isometry group of `Q` acts transitively on the isotropic points. -/
theorem isPretransitive_isotropicPoints (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0) :
    MulAction.IsPretransitive (Q.specialIsometryGroup σ) (Q.isotropicPoints σ) := by
  have := isPretransitive_elementaryUnitaryGroup hσ hQ hε hdet htr hadm
  refine ⟨fun p q ↦ ?_⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Q.elementaryUnitaryGroup σ) p q
  exact ⟨g.val, hg⟩

/-- **An isometry fixing every isotropic point is central.** Under the hypotheses of
`Matrix.isPretransitive_isotropicPoints` (here `ε * ε = 1` is not assumed, since it follows from
the surjectivity of the trace), if some point is isotropic, then an element of the special isometry
group fixing every isotropic point is a scalar matrix, hence central. -/
theorem mem_center_specialIsometryGroup_of_forall_smul_eq (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    [Nonempty (Q.isotropicPoints σ)] {g : Q.specialIsometryGroup σ}
    (hg : ∀ p : Q.isotropicPoints σ, g • p = p) :
    g ∈ Subgroup.center (Q.specialIsometryGroup σ) := by
  obtain ⟨p₀⟩ := ‹Nonempty (Q.isotropicPoints σ)›
  obtain ⟨c, hc⟩ := exists_eq_scalar_of_forall_mulVec_eq_smul hσ hQ hdet htr hadm
    (p₀ : ℙ K (n → K)).rep_ne_zero (comp_rep_dotProduct_mulVec_rep p₀)
    ((g : SpecialLinearGroup n K) : Matrix n n K) fun v hv ↦ by
      by_cases hv0 : v = 0
      · exact ⟨0, by simp [hv0]⟩
      have hgv := congrArg Subtype.val
        (hg ⟨_, (mk_mem_isotropicPoints_iff hv0).mpr hv⟩)
      rw [SubMulAction.val_smul, Subgroup.smul_def, Projectivization.smul_mk,
        Projectivization.mk_eq_mk_iff] at hgv
      obtain ⟨a, ha⟩ := hgv
      rw [Units.smul_def, SpecialLinearGroup.smul_def, smul_eq_mulVec] at ha
      exact ⟨a, ha.symm⟩
  refine Subgroup.mem_center_iff.mpr fun k ↦ Subtype.ext (Subtype.ext ?_)
  simp only [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, hc]
  exact ((scalar_commute c (fun r ↦ Commute.all c r) _).eq).symm

end Matrix
