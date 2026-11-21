/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Elementary
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# The action of a special unitary group on its isotropic points

Let `σ` be an involution of a field `K`, let `Q` be an invertible `ε`-Hermitian matrix,
`(Q ^ σ)ᵀ = ε • Q`, and let `h(x, y) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y)` be its sesquilinear
form. The special isometry group `Matrix.specialIsometryGroup Q σ` acts on the isotropic points
`Matrix.isotropicPoints Q σ` of projective space. Iwasawa's criterion needs this action to be
quasiprimitive with central kernel; this file proves that it is transitive, the first step towards
primitivity, and that, when some point is isotropic, its kernel is central. Both hold under two
conditions on the trace `t ↦ t + ε σ(t)`:

* it is onto the elements `s` with `σ(s) = ε s`, the values `h(u, u)` of the form;
* it has a nonzero kernel element, so that nontrivial unitary transvections exist.

Over the field with `q²` elements, with `σ(x) = x ^ q`, both hold for `ε = ±1`
(`TauCeti.FiniteField.exists_add_neg_one_pow_mul_pow_eq` and
`TauCeti.FiniteField.exists_ne_zero_add_neg_one_pow_mul_pow_eq_zero`).

Transitivity follows from the stronger elementary-group result in
`TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Elementary`, which also proves the
stabilizer-aware vector-joining result used in the primitivity argument.

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
* `Matrix.smul_eq_self_of_mem_center_specialIsometryGroup` and
  `Matrix.mem_center_specialIsometryGroup_iff_forall_smul_eq`: every central isometry fixes every
  isotropic point, so when an isotropic point exists the centre equals the isotropic-point action
  kernel.

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
`Q` an invertible `ε`-Hermitian matrix, and suppose that the trace
`t ↦ t + ε σ(t)` is onto the elements `s` with `σ(s) = ε s` and has a nonzero kernel element.
Then the special isometry group of `Q` acts transitively on the isotropic points. -/
theorem isPretransitive_isotropicPoints (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0) :
    MulAction.IsPretransitive (Q.specialIsometryGroup σ) (Q.isotropicPoints σ) := by
  have := isPretransitive_elementaryUnitaryGroup hσ hQ hdet htr hadm
  exact .of_smul_eq (fun g : Q.elementaryUnitaryGroup σ ↦ (g : Q.specialIsometryGroup σ))
    (Subgroup.smul_def _ _).symm

/-- **Every central special isometry fixes every isotropic point.** Let `σ` be an involution, let
`Q` be an invertible `ε`-Hermitian matrix, and suppose that `t ↦ t + ε σ(t)` has a nonzero kernel
element. Conjugating a nontrivial unitary transvection along an isotropic point `p` by a central
element `g` leaves the transvection invariant, forcing `g` to preserve the line `p`. -/
theorem smul_eq_self_of_mem_center_specialIsometryGroup (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    {g : Q.specialIsometryGroup σ} (hg : g ∈ Subgroup.center (Q.specialIsometryGroup σ))
    (p : Q.isotropicPoints σ) : g • p = p := by
  obtain ⟨d, hd0, hd⟩ := hadm
  set v := (p : ℙ K (n → K)).rep
  have hv0 : v ≠ 0 := (p : ℙ K (n → K)).rep_ne_zero
  obtain ⟨t, ht, hta⟩ := exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ
    (comp_rep_dotProduct_mulVec_rep p) hd
  let t' : Q.specialIsometryGroup σ := ⟨t, ht⟩
  have hconj : g * t' * g⁻¹ = t' := by
    rw [(Subgroup.mem_center_iff.mp hg t').symm, mul_inv_cancel_right]
  have hmat : Q.unitaryTransvection σ (((g : SpecialLinearGroup n K) : Matrix n n K) *ᵥ v) d =
      Q.unitaryTransvection σ v d := by
    calc Q.unitaryTransvection σ (((g : SpecialLinearGroup n K) : Matrix n n K) *ᵥ v) d
        = ((g : SpecialLinearGroup n K) : Matrix n n K) * Q.unitaryTransvection σ v d *
            (((g : SpecialLinearGroup n K)⁻¹ : SpecialLinearGroup n K) : Matrix n n K) :=
          (coe_mul_unitaryTransvection_mul_coe_inv g.property v d).symm
      _ = (((g * t' * g⁻¹ : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) :
            Matrix n n K) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, SpecialLinearGroup.coe_mul, t', hta, v]
      _ = Q.unitaryTransvection σ v d := by rw [hconj]; exact hta
  simp only [unitaryTransvection_def, add_right_inj, smul_right_inj hd0] at hmat
  obtain ⟨c, hc0, hsmul⟩ :=
    exists_eq_smul_of_vecMulVec_eq hv0 (comp_vecMul_ne_zero hdet σ hv0) hmat
  refine Subtype.ext ?_
  rw [SubMulAction.val_smul, Subgroup.smul_def, ← Projectivization.mk_rep (p : ℙ K (n → K)),
    Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  refine ⟨Units.mk0 c hc0, ?_⟩
  rw [Units.smul_def, Units.val_mk0, SpecialLinearGroup.smul_def, smul_eq_mulVec]
  exact hsmul.symm

/-- **An isometry fixing every isotropic point is central.** Under the hypotheses of
`Matrix.isPretransitive_isotropicPoints`, if some point is isotropic, then an element of the
special isometry group fixing every isotropic point is a scalar matrix, hence central. -/
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

/-- **The centre of a special unitary group is the kernel of its isotropic-point action.** Let
`σ` be an involution, let `Q` be an invertible `ε`-Hermitian matrix admitting an isotropic point,
and suppose that the trace `t ↦ t + ε σ(t)` is onto the elements `s` with `σ(s) = ε s` and has a
nonzero kernel element. Then an element of `Q.specialIsometryGroup σ` is central if and only if
it fixes every isotropic point. -/
theorem mem_center_specialIsometryGroup_iff_forall_smul_eq (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    [Nonempty (Q.isotropicPoints σ)] {g : Q.specialIsometryGroup σ} :
    g ∈ Subgroup.center (Q.specialIsometryGroup σ) ↔ ∀ p : Q.isotropicPoints σ, g • p = p :=
  ⟨smul_eq_self_of_mem_center_specialIsometryGroup hσ hQ hdet hadm,
    mem_center_specialIsometryGroup_of_forall_smul_eq hσ hQ hdet htr hadm⟩

end Matrix
