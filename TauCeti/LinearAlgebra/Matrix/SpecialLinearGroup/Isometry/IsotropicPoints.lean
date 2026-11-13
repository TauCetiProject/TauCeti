/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Transvection
import TauCeti.Algebra.Group.Hom.Defs
import TauCeti.Algebra.Group.Submonoid.Defs
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm
import TauCeti.LinearAlgebra.Projectivization.Action

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

The first condition lets one correct a vector `u` with `h(u, x) ≠ 0` to the isotropic vector
`u + c x`, for an isotropic `x`. The second turns isotropic `x`, `y` with `h(y, x) ≠ 0` into a
pair with `h(x, y) + h(y, x) = 0` after rescaling `y`, and then the unitary transvection along
`y - x` with parameter `h(y, x)⁻¹` sends `x` to `y`. Two isotropic vectors in `u^⊥` off `K ∙ u`
with `h(y, x) = 0` are joined while fixing `u` through a third isotropic vector in `u^⊥` paired
nontrivially with both; specializing `u = 0` gives transitivity on isotropic points.

For the kernel, an element fixing every isotropic point scales each isotropic vector. Comparing
an isotropic `x₀` with an isotropic `x₀ + c v`, for isotropic `v` and `c ≠ 0`, shows that all
these scalars agree. Given a nonzero isotropic vector, the isotropic vectors span the space, so
the element is a scalar matrix. This scalar criterion,
`Matrix.exists_eq_scalar_of_forall_mulVec_eq_smul`, and the form identities used here are in
`TauCeti.LinearAlgebra.Matrix.SesquilinearForm`.

## Main results

* `Matrix.exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection_sub_and_mulVec_eq`: when `σ`
  is an involution, `Q` is `ε`-Hermitian with `ε * ε = 1`, and `x` and `y` are isotropic with
  `h(y, x) ≠ 0` and `h(x, y) + h(y, x) = 0`, the unitary transvection along `y - x` with parameter
  `h(y, x)⁻¹` lies in `Q.specialIsometryGroup σ` and sends `x` to `y`.
* `Matrix.exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul_of_eq_zero`: under the
  two trace hypotheses, an element of `Q.specialIsometryGroup σ` fixes `u` and sends any isotropic
  `x ∈ u^⊥` off `K ∙ u` to a nonzero multiple of any isotropic `y ∈ u^⊥` off `K ∙ u`.
* `Matrix.isPretransitive_isotropicPoints`: the special isometry group acts transitively on the
  isotropic points.
* `Matrix.mem_center_specialIsometryGroup_of_forall_smul_eq`: if some point is isotropic, an
  isometry fixing every isotropic point is central.

## References

* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapters 10 and 11.
* L. C. Grove, *Classical Groups and Geometric Algebra* (2002), Chapter 11.

The transvection step follows the symplectic argument of
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Transitivity`, in particular
`TauCeti.GLSymplecticFin.coe_symplecticTransvection_sub_mulVec`.
-/

public section

open scoped LinearAlgebra.Projectivization

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] {Q : Matrix n n K} {σ : K →+* K}
  {ε : K}

/-! ### Transitivity -/

/-- **A unitary transvection joins two isotropic vectors.** If `σ` is an involution, `Q` is
`ε`-Hermitian with `ε * ε = 1`, and `x` and `y` are isotropic with `h(y, x) ≠ 0` and
`h(x, y) + h(y, x) = 0`, then the unitary transvection along `y - x` with parameter `h(y, x)⁻¹`
lies in `Q.specialIsometryGroup σ` and sends `x` to `y`. -/
theorem exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection_sub_and_mulVec_eq
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) {x y : n → K}
    (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0)
    (hyx : (σ ∘ y) ⬝ᵥ (Q *ᵥ x) ≠ 0)
    (hxy : (σ ∘ x) ⬝ᵥ (Q *ᵥ y) + (σ ∘ y) ⬝ᵥ (Q *ᵥ x) = 0) :
    ∃ g ∈ Q.specialIsometryGroup σ,
      (g : Matrix n n K) = Q.unitaryTransvection σ (y - x) ((σ ∘ y) ⬝ᵥ (Q *ᵥ x))⁻¹ ∧
        (g : Matrix n n K) *ᵥ x = y := by
  set b := (σ ∘ y) ⬝ᵥ (Q *ᵥ x) with hb
  have hw : (σ ∘ (y - x)) ⬝ᵥ (Q *ᵥ (y - x)) = 0 := by
    simp only [map_comp_sub, sub_dotProduct, mulVec_sub, dotProduct_sub, hx, hy]
    linear_combination -hxy
  -- `h(x, y) = ε σ(b)`, so the condition says `σ(b) = -ε b`, and `b⁻¹` is an admissible
  -- parameter.
  have hσb : σ b = -(ε * b) := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε y x] at hxy
    linear_combination ε * hxy - σ b * hε
  have ha : b⁻¹ + ε * σ b⁻¹ = 0 := by
    rw [map_inv₀, hσb, inv_neg, mul_inv, inv_eq_of_mul_eq_one_right hε, mul_neg, ← mul_assoc, hε,
      one_mul, add_neg_cancel]
  obtain ⟨g, hg, hga⟩ := exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ hw ha
  refine ⟨g, hg, hga, ?_⟩
  simp [hga, unitaryTransvection_mulVec, hx, ← hb, inv_mul_cancel₀ hyx]

/-- **Connecting two non-orthogonal isotropic vectors in `u^⊥`.** Let `σ` be an involution and let
`Q` be an `ε`-Hermitian matrix with `ε * ε = 1`. If `x` and `y` are isotropic vectors orthogonal to
`u` with `h(y, x) ≠ 0`, and some nonzero `d` satisfies `d + ε σ(d) = 0`, then some element of
`Q.specialIsometryGroup σ` fixes `u` and sends `x` to a nonzero multiple of `y`. -/
private theorem
    exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul_of_eq_zero_of_ne_zero
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0) {u x y : n → K}
    (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0)
    (hux : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0) (huy : (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0)
    (hyx : (σ ∘ y) ⬝ᵥ (Q *ᵥ x) ≠ 0) :
    ∃ g ∈ Q.specialIsometryGroup σ, ∃ c ≠ (0 : K),
      (g : Matrix n n K) *ᵥ u = u ∧ (g : Matrix n n K) *ᵥ x = c • y := by
  obtain ⟨d, hd, hdε⟩ := hadm
  set b := (σ ∘ y) ⬝ᵥ (Q *ᵥ x)
  -- Rescale `y` by `c = σ(d / b)`, so that `h(c y, x) = d`.
  set c := σ (d * b⁻¹)
  have hc : c ≠ 0 := (map_ne_zero σ).mpr (mul_ne_zero hd (inv_ne_zero hyx))
  have hcyx : (σ ∘ (c • y)) ⬝ᵥ (Q *ᵥ x) = d := by
    rw [TauCeti.map_comp_smul, smul_dotProduct, smul_eq_mul, hσ, mul_assoc, inv_mul_cancel₀ hyx,
      mul_one]
  have hcy : (σ ∘ (c • y)) ⬝ᵥ (Q *ᵥ (c • y)) = 0 := by
    rw [comp_smul_dotProduct_mulVec_smul, hy, mul_zero]
  have hxcy : (σ ∘ x) ⬝ᵥ (Q *ᵥ (c • y)) + (σ ∘ (c • y)) ⬝ᵥ (Q *ᵥ x) = 0 := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε (c • y) x, hcyx, add_comm]
    exact hdε
  obtain ⟨g, hg, hga, hgx⟩ :=
    exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection_sub_and_mulVec_eq
      hσ hQ hε hx hcy (hcyx ▸ hd) hxcy
  have hxu : (σ ∘ x) ⬝ᵥ (Q *ᵥ u) = 0 :=
    (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hux
  have hyu : (σ ∘ y) ⬝ᵥ (Q *ᵥ u) = 0 :=
    (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp huy
  refine ⟨g, hg, c, hc, ?_, hgx⟩
  simp [hga, unitaryTransvection_mulVec, hxu, hyu]

/-- **Connecting two isotropic vectors in `u^⊥` off `K ∙ u`.** Let `σ` be an involution, let `Q` be
an invertible `ε`-Hermitian matrix, and suppose that the trace `t ↦ t + ε σ(t)` is onto the
elements `s` with `σ(s) = ε s` and has a nonzero kernel element. If `x` and `y` are isotropic
vectors outside `K ∙ u` with `h(u, x) = 0` and `h(u, y) = 0`, then some element of
`Q.specialIsometryGroup σ` fixes `u` and sends `x` to a nonzero multiple of `y`. -/
theorem exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul_of_eq_zero
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    {u x y : n → K} (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0)
    (hx_span : x ∉ K ∙ u) (hy_span : y ∉ K ∙ u)
    (hux : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0) (huy : (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0) :
    ∃ g ∈ Q.specialIsometryGroup σ, ∃ c ≠ (0 : K),
      (g : Matrix n n K) *ᵥ u = u ∧ (g : Matrix n n K) *ᵥ x = c • y := by
  have : Nonempty n := let ⟨i, _⟩ := Function.ne_iff.mp (TauCeti.ne_zero_of_notMem hx_span); ⟨i⟩
  have hε := mul_self_eq_one_of_trace_of_det_ne_zero hσ hQ hdet htr
  by_cases hyx : (σ ∘ y) ⬝ᵥ (Q *ᵥ x) = 0
  swap
  · exact exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul_of_eq_zero_of_ne_zero
      hσ hQ hε hadm hx hy hux huy hyx
  -- Choose `v` orthogonal to `u` and paired nontrivially with both `x` and `y`, then correct
  -- `v` to an isotropic vector `z = v + a • x`.
  obtain ⟨v, hvu, hvx, hvy⟩ :=
    exists_comp_dotProduct_mulVec_eq_zero_and_ne_zero_pair hσ.surjective hdet hx_span hy_span
  obtain ⟨a, hz⟩ := exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero hσ hQ htr hx hvx
  set z := v + a • x
  have hxu : (σ ∘ x) ⬝ᵥ (Q *ᵥ u) = 0 := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hux
  have hxy : (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 0 := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hyx
  have huz : (σ ∘ u) ⬝ᵥ (Q *ᵥ z) = 0 := by
    rw [comp_dotProduct_mulVec_eq_zero_comm hσ hQ]
    simp [z, hvu, hxu]
  have hzx : (σ ∘ z) ⬝ᵥ (Q *ᵥ x) ≠ 0 := by
    simpa [z, hx] using hvx
  have hyz : (σ ∘ y) ⬝ᵥ (Q *ᵥ z) ≠ 0 := by
    rw [comp_dotProduct_mulVec_ne_zero_comm hσ hQ]
    simpa [z, hxy] using hvy
  obtain ⟨g₁, hg₁, c₁, hc₁, hg₁u, hg₁x⟩ :=
    exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul_of_eq_zero_of_ne_zero
      hσ hQ hε hadm hx hz hux huz hzx
  obtain ⟨g₂, hg₂, c₂, hc₂, hg₂u, hg₂z⟩ :=
    exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul_of_eq_zero_of_ne_zero
      hσ hQ hε hadm hz hy huz huy hyz
  refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, c₁ * c₂, mul_ne_zero hc₁ hc₂, ?_, ?_⟩
  · rw [SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hg₁u, hg₂u]
  · rw [SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hg₁x, mulVec_smul, hg₂z, smul_smul]

/-- **The special unitary group is transitive on isotropic points.** Let `σ` be an involution,
`Q` an invertible `ε`-Hermitian matrix, and suppose that the trace
`t ↦ t + ε σ(t)` is onto the elements `s` with `σ(s) = ε s` and has a nonzero kernel element.
Then the special isometry group of `Q` acts transitively on the isotropic points. -/
theorem isPretransitive_isotropicPoints (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0) :
    MulAction.IsPretransitive (Q.specialIsometryGroup σ) (Q.isotropicPoints σ) := by
  refine ⟨fun ⟨p, hp⟩ ⟨q, hq⟩ ↦ ?_⟩
  induction p using Projectivization.ind with | h x hx0 => ?_
  induction q using Projectivization.ind with | h y hy0 => ?_
  rw [mk_mem_isotropicPoints_iff] at hp hq
  obtain ⟨g, hg, c, -, -, hgx⟩ :=
    exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul_of_eq_zero
      hσ hQ hdet htr hadm (u := 0) hp hq (by simp [hx0]) (by simp [hy0]) (by simp) (by simp)
  refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
  exact TauCeti.Projectivization.smul_mk_eq_mk_of_smul_eq_smul hx0 hy0
    (by rwa [Subgroup.smul_def, SpecialLinearGroup.smul_def, smul_eq_mulVec])

/-! ### The kernel of the action -/

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

end Matrix
