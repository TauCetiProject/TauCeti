/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Transvection
import TauCeti.Algebra.Group.Hom.Defs
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
  is an involution, `Q` is `ε`-Hermitian, and `x` and `y` are isotropic with `h(y, x) ≠ 0` and
  `h(x, y) + h(y, x) = 0`, the unitary transvection along `y - x` with parameter `h(y, x)⁻¹` lies
  in `Q.specialIsometryGroup σ` and sends `x` to `y`.
*
  `Matrix.exists_mem_iSup_unitaryTransvectionSubgroup_mulVec_eq_self_and_mulVec_eq_smul_of_ne_zero`
  and
  `Matrix.exists_mem_iSup_unitaryTransvectionSubgroup_mulVec_eq_self_and_mulVec_eq_smul_of_eq_zero`:
  elements of the unitary transvection supremum join isotropic vectors up to nonzero scalar while
  fixing an orthogonal set or vector `u`.
* `Matrix.exists_mem_iSup_unitaryTransvectionSubgroup_mulVec_eq_smul` and
  `Matrix.isPretransitive_isotropicPoints`: the unitary transvection supremum is transitive up to
  scalar on nonzero isotropic vectors, and `Q.specialIsometryGroup σ` acts transitively on
  `Q.isotropicPoints σ`.
* `Matrix.mem_center_specialIsometryGroup_of_forall_smul_eq`: if some point is isotropic, an
  isometry fixing every isotropic point is central.
* `Matrix.exists_comp_dotProduct_mulVec_eq_zero_and_eq_one_of_nonempty_isotropicPoints` and
  `Matrix.nontrivial_specialIsometryGroup`: a nonempty isotropic-point set yields a hyperbolic pair
  under trace surjectivity and makes `Q.specialIsometryGroup σ` nontrivial whenever a nonzero
  admissible transvection parameter exists.

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
`ε`-Hermitian, and `x` and `y` are isotropic with `h(y, x) ≠ 0` and `h(x, y) + h(y, x) = 0`, then
the unitary transvection along `y - x` with parameter `h(y, x)⁻¹` lies in `Q.specialIsometryGroup σ`
and sends `x` to `y`. -/
theorem exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection_sub_and_mulVec_eq
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) {x y : n → K}
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
  -- `σ(b) = ε h(x, y) = -ε b`, so `b⁻¹` is an admissible parameter.
  have hσb : σ b = -(ε * b) := by
    have h := apply_comp_dotProduct_mulVec hσ hQ y x
    rw [← hb] at h
    linear_combination h + ε * hxy
  have hε0 : ε ≠ 0 := fun h ↦ (map_ne_zero σ).mpr hyx (by simp [hσb, h])
  have ha : b⁻¹ + ε * σ b⁻¹ = 0 := by
    simp only [map_inv₀, hσb, inv_neg, mul_neg]
    linear_combination -b⁻¹ * mul_inv_cancel₀ hε0
  obtain ⟨g, hg, hga⟩ := exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ hw ha
  refine ⟨g, hg, hga, ?_⟩
  simp [hga, unitaryTransvection_mulVec, hx, ← hb, inv_mul_cancel₀ hyx]

/-- **Connecting two non-orthogonal isotropic vectors while fixing an orthogonal set.** Let `σ` be
an involution and let `Q` be an `ε`-Hermitian matrix. If some nonzero `d` satisfies
`d + ε * σ d = 0` and `x, y` are isotropic vectors with `h(y, x) ≠ 0` that are orthogonal to every
vector in `U`, then some element of the unitary transvection supremum fixes every vector in `U` and
sends `x` to a nonzero scalar multiple of `y`. -/
theorem
    exists_mem_iSup_unitaryTransvectionSubgroup_mulVec_eq_self_and_mulVec_eq_smul_of_ne_zero
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0) {U : Set (n → K)} {x y : n → K}
    (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0)
    (hxU : ∀ u ∈ U, (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0) (hyU : ∀ u ∈ U, (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0)
    (hyx : (σ ∘ y) ⬝ᵥ (Q *ᵥ x) ≠ 0) :
    ∃ t ∈ ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p, ∃ c ≠ (0 : K),
      (∀ u ∈ U, (t : Matrix n n K) *ᵥ u = u) ∧ (t : Matrix n n K) *ᵥ x = c • y := by
  obtain ⟨d, hd, hdε⟩ := hadm
  set b := (σ ∘ y) ⬝ᵥ (Q *ᵥ x) with hb
  have hσb : σ b ≠ 0 := (map_ne_zero σ).mpr hyx
  have hσb_eq : σ b = ε * ((σ ∘ x) ⬝ᵥ (Q *ᵥ y)) := by
    rw [hb, apply_comp_dotProduct_mulVec hσ hQ]
  have hε0 : ε ≠ 0 := left_ne_zero_of_mul (hσb_eq ▸ hσb)
  -- Rescale `y` by `c = d / σ(b)`, so that `h(c y, x) = σ(d)` and `ε h(x, c y) = d`.
  set c := d * (σ b)⁻¹
  have hc : c ≠ 0 := mul_ne_zero hd (inv_ne_zero hσb)
  have hcyx : (σ ∘ (c • y)) ⬝ᵥ (Q *ᵥ x) = σ d := by
    simp [c, TauCeti.map_comp_smul, hσ b, ← hb, hyx]
  have hcy : (σ ∘ (c • y)) ⬝ᵥ (Q *ᵥ (c • y)) = 0 := by
    rw [comp_smul_dotProduct_mulVec_smul, hy, mul_zero]
  have hxcy : (σ ∘ x) ⬝ᵥ (Q *ᵥ (c • y)) + (σ ∘ (c • y)) ⬝ᵥ (Q *ᵥ x) = 0 := by
    refine mul_left_cancel₀ hε0 ?_
    have h1 : c * (ε * ((σ ∘ x) ⬝ᵥ (Q *ᵥ y))) = d := by
      rw [← hσb_eq]
      simp [c, hσb]
    rw [hcyx, mulVec_smul, dotProduct_smul, smul_eq_mul]
    linear_combination h1 + hdε
  obtain ⟨g, hg, hga, hgx⟩ :=
    exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection_sub_and_mulVec_eq
      hσ hQ hx hcy (hcyx ▸ (map_ne_zero σ).mpr hd) hxcy
  have hmem : (⟨g, hg⟩ : Q.specialIsometryGroup σ) ∈
      ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p := by
    have hw : (σ ∘ (c • y - x)) ⬝ᵥ (Q *ᵥ (c • y - x)) = 0 := by
      simp only [map_comp_sub, sub_dotProduct, mulVec_sub, dotProduct_sub, hcy, hx]
      linear_combination -hxcy
    exact unitaryTransvection_mem_iSup_unitaryTransvectionSubgroup hg hw hga
  refine ⟨⟨g, hg⟩, hmem, c, hc, fun u hu ↦ ?_,
    by rwa [Subgroup.coe_mk (Q.specialIsometryGroup σ)]⟩
  have hxu : (σ ∘ x) ⬝ᵥ (Q *ᵥ u) = 0 := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (hxU u hu)
  have hyu : (σ ∘ y) ⬝ᵥ (Q *ᵥ u) = 0 := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (hyU u hu)
  rw [Subgroup.coe_mk (Q.specialIsometryGroup σ), hga, unitaryTransvection_mulVec]
  simp [hxu, hyu]

/-- **Connecting two isotropic vectors in `u^⊥` off `K ∙ u`.** Let `σ` be an involution, let `Q` be
an invertible `ε`-Hermitian matrix, and suppose that the trace `t ↦ t + ε σ(t)` is onto the
elements `s` with `σ(s) = ε s` and has a nonzero kernel element. If `x` and `y` are isotropic
vectors outside `K ∙ u` with `h(u, x) = 0` and `h(u, y) = 0`, then some element of the unitary
transvection supremum fixes `u` and sends `x` to a nonzero scalar multiple of `y`. -/
theorem exists_mem_iSup_unitaryTransvectionSubgroup_mulVec_eq_self_and_mulVec_eq_smul_of_eq_zero
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    {u x y : n → K} (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0)
    (hx_span : x ∉ K ∙ u) (hy_span : y ∉ K ∙ u)
    (hux : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0) (huy : (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0) :
    ∃ t ∈ ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p, ∃ c ≠ (0 : K),
      (t : Matrix n n K) *ᵥ u = u ∧ (t : Matrix n n K) *ᵥ x = c • y := by
  by_cases hyx : (σ ∘ y) ⬝ᵥ (Q *ᵥ x) = 0
  swap
  · obtain ⟨t, ht, c, hc, htU, htx⟩ :=
      exists_mem_iSup_unitaryTransvectionSubgroup_mulVec_eq_self_and_mulVec_eq_smul_of_ne_zero
        hσ hQ hadm (U := {u}) hx hy (Set.forall_mem_singleton.mpr hux)
        (Set.forall_mem_singleton.mpr huy) hyx
    exact ⟨t, ht, c, hc, htU u (Set.mem_singleton u), htx⟩
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
  have hzx : (σ ∘ z) ⬝ᵥ (Q *ᵥ x) ≠ 0 := by simpa [z, hx] using hvx
  have hyz : (σ ∘ y) ⬝ᵥ (Q *ᵥ z) ≠ 0 := by
    rw [comp_dotProduct_mulVec_ne_zero_comm hσ hQ]
    simpa [z, hxy] using hvy
  obtain ⟨t₁, ht₁, c₁, hc₁, ht₁U, ht₁x⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_mulVec_eq_self_and_mulVec_eq_smul_of_ne_zero
      hσ hQ hadm (U := {u}) hx hz (Set.forall_mem_singleton.mpr hux)
      (Set.forall_mem_singleton.mpr huz) hzx
  obtain ⟨t₂, ht₂, c₂, hc₂, ht₂U, ht₂z⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_mulVec_eq_self_and_mulVec_eq_smul_of_ne_zero
      hσ hQ hadm (U := {u}) hz hy (Set.forall_mem_singleton.mpr huz)
      (Set.forall_mem_singleton.mpr huy) hyz
  refine ⟨t₂ * t₁, mul_mem ht₂ ht₁, c₁ * c₂, mul_ne_zero hc₁ hc₂, ?_, ?_⟩
  · rw [specialIsometryGroup_coe_mul_mulVec, ht₁U u (Set.mem_singleton u),
      ht₂U u (Set.mem_singleton u)]
  · rw [specialIsometryGroup_coe_mul_mulVec, ht₁x, mulVec_smul, ht₂z, smul_smul]

/-- **The unitary transvection supremum is transitive up to scalar on nonzero isotropic vectors.**
Let `σ` be an involution, let `Q` be an invertible `ε`-Hermitian matrix, and suppose that the trace
`t ↦ t + ε σ(t)` is onto the elements `s` with `σ(s) = ε s` and has a nonzero kernel element. For
any nonzero isotropic vectors `x` and `y`, some element of the unitary transvection supremum sends
`x` to a nonzero scalar multiple of `y`. -/
theorem exists_mem_iSup_unitaryTransvectionSubgroup_mulVec_eq_smul (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    {x y : n → K} (hx₀ : x ≠ 0) (hy₀ : y ≠ 0)
    (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0) :
    ∃ g ∈ ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p, ∃ c ≠ (0 : K),
      (g : Matrix n n K) *ᵥ x = c • y := by
  obtain ⟨g, hg, c, hc, -, hgx⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_mulVec_eq_self_and_mulVec_eq_smul_of_eq_zero
      hσ hQ hdet htr hadm (u := 0) hx hy (by simp [hx₀]) (by simp [hy₀]) (by simp) (by simp)
  exact ⟨g, hg, c, hc, hgx⟩

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
  obtain ⟨g, -, c, -, hgx⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_mulVec_eq_smul hσ hQ hdet htr hadm hx0 hy0 hp hq
  refine ⟨g, Subtype.ext ?_⟩
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
  refine Subgroup.mem_center_iff.mpr fun k ↦ specialIsometryGroup_ext ?_
  simp only [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, hc]
  exact ((scalar_commute c (fun r ↦ Commute.all c r) _).eq).symm

/-! ### Hyperbolic pairs and nontriviality -/

/-- **Constructing a hyperbolic pair from a nonempty isotropic-point set.** Let `σ` be an
involution, let `Q` be an invertible `ε`-Hermitian matrix, and suppose that the trace
`t ↦ t + ε σ(t)` is onto the elements `s` with `σ(s) = ε s`. If `Q.isotropicPoints σ` is nonempty,
then some nonzero vectors `e, f` satisfy `h(e, e) = h(f, f) = 0`, `h(e, f) = 1`, `h(f, e) = ε`,
`ε * ε = 1`, and `σ ε = ε`. -/
theorem exists_comp_dotProduct_mulVec_eq_zero_and_eq_one_of_nonempty_isotropicPoints
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) [Nonempty (Q.isotropicPoints σ)] :
    ∃ e f : n → K, e ≠ 0 ∧ f ≠ 0 ∧ (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0 ∧ (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0 ∧
      (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1 ∧ (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε ∧ ε * ε = 1 ∧ σ ε = ε := by
  obtain ⟨p₀⟩ := ‹Nonempty (Q.isotropicPoints σ)›
  have he₀ : (p₀ : ℙ K (n → K)).rep ≠ 0 := (p₀ : ℙ K (n → K)).rep_ne_zero
  have he : (σ ∘ (p₀ : ℙ K (n → K)).rep) ⬝ᵥ (Q *ᵥ (p₀ : ℙ K (n → K)).rep) = 0 :=
    comp_rep_dotProduct_mulVec_rep p₀
  obtain ⟨f, hf₀, hf, hef, hfe, hε, hσε⟩ :=
    exists_comp_dotProduct_mulVec_eq_zero_and_eq_one hσ hQ hdet htr he₀ he
  exact ⟨(p₀ : ℙ K (n → K)).rep, f, he₀, hf₀, he, hf, hef, hfe, hε, hσε⟩

/-- **Nontriviality of `Q.specialIsometryGroup σ` when an isotropic point exists.** Let `σ` be an
involution and let `Q` be an invertible `ε`-Hermitian matrix such that some nonzero `d` satisfies
`d + ε * σ d = 0`. If `Q.isotropicPoints σ` is nonempty, then `Q.specialIsometryGroup σ` is
nontrivial. -/
theorem nontrivial_specialIsometryGroup (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q)
    (hdet : Q.det ≠ 0) (hadm : ∃ d ≠ 0, d + ε * σ d = 0) [Nonempty (Q.isotropicPoints σ)] :
    Nontrivial (Q.specialIsometryGroup σ) := by
  obtain ⟨p₀⟩ := ‹Nonempty (Q.isotropicPoints σ)›
  set e := (p₀ : ℙ K (n → K)).rep
  have he₀ : e ≠ 0 := (p₀ : ℙ K (n → K)).rep_ne_zero
  have he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0 := comp_rep_dotProduct_mulVec_rep p₀
  obtain ⟨u, hue, -⟩ := exists_comp_dotProduct_mulVec_ne_zero_pair (σ := σ) hdet he₀ he₀
  have heu : (σ ∘ e) ⬝ᵥ (Q *ᵥ u) ≠ 0 := (comp_dotProduct_mulVec_ne_zero_comm hσ hQ).mp hue
  obtain ⟨d, hd, hdε⟩ := hadm
  obtain ⟨t, ht, hct⟩ := exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ he hdε
  refine ⟨⟨t, ht⟩, 1, fun h ↦ ?_⟩
  have htu := congrArg (fun g : Q.specialIsometryGroup σ ↦ (g : Matrix n n K) *ᵥ u) h
  rw [Subgroup.coe_mk (Q.specialIsometryGroup σ), hct, unitaryTransvection_mulVec,
    Subgroup.coe_one, SpecialLinearGroup.coe_one, one_mulVec] at htu
  exact smul_ne_zero (mul_ne_zero hd heu) he₀ (add_eq_left.mp htu)

end Matrix
