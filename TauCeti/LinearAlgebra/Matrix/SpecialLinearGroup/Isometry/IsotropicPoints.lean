/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Transvection
import TauCeti.Algebra.Ring.Hom
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# The action of a special unitary group on its isotropic points

Let `σ` be an involution of a field `K`, let `Q` be an invertible `ε`-Hermitian matrix,
`(Q ^ σ)ᵀ = ε • Q` with `ε = ±1`, and let `h(x, y) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y)` be its sesquilinear
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
`y - x` with parameter `h(y, x)⁻¹` sends `x` to `y`. Two isotropic points with `h(y, x) = 0` are
joined through a third isotropic point paired nontrivially with both.

For the kernel, an element fixing every isotropic point scales each isotropic vector. Comparing
an isotropic `x₀` with an isotropic `x₀ + c v`, for isotropic `v` and `c ≠ 0`, shows that all
these scalars agree. Given a nonzero isotropic vector, the isotropic vectors span the space, so
the element is a scalar matrix. This scalar criterion,
`Matrix.exists_eq_scalar_of_forall_mulVec_eq_smul`, and the form identities used here are in
`TauCeti.LinearAlgebra.Matrix.SesquilinearForm`.

## Main results

* `Matrix.exists_mem_specialIsometryGroup_mulVec_eq`: a special isometry, a unitary transvection,
  sends an isotropic `x` to an isotropic `y` when `h(y, x) ≠ 0` and `h(x, y) + h(y, x) = 0`.
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

/-- **A unitary transvection joins two isotropic vectors.** If `x` and `y` are isotropic,
`h(y, x) ≠ 0` and `h(x, y) + h(y, x) = 0`, then the unitary transvection along `y - x` with
parameter `h(y, x)⁻¹` is a special isometry sending `x` to `y`. -/
theorem exists_mem_specialIsometryGroup_mulVec_eq (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) {x y : n → K}
    (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0)
    (hyx : (σ ∘ y) ⬝ᵥ (Q *ᵥ x) ≠ 0)
    (hxy : (σ ∘ x) ⬝ᵥ (Q *ᵥ y) + (σ ∘ y) ⬝ᵥ (Q *ᵥ x) = 0) :
    ∃ g ∈ Q.specialIsometryGroup σ, (g : Matrix n n K) *ᵥ x = y := by
  set b := (σ ∘ y) ⬝ᵥ (Q *ᵥ x)
  have hcomp : σ ∘ (y - x) = σ ∘ y - σ ∘ x := funext fun i ↦ map_sub σ _ _
  have hw : (σ ∘ (y - x)) ⬝ᵥ (Q *ᵥ (y - x)) = 0 := by
    rw [hcomp, mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hx, hy]
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
  refine ⟨g, hg, ?_⟩
  rw [hga, unitaryTransvection_mulVec, hcomp, sub_dotProduct, hx, sub_zero, inv_mul_cancel₀ hyx,
    one_smul, add_sub_cancel]

/-- A special isometry sends an isotropic `x` to a nonzero multiple of an isotropic `y` whenever
`h(y, x) ≠ 0`, provided some nonzero `d` satisfies `d + ε σ(d) = 0`. -/
private theorem exists_mem_specialIsometryGroup_mulVec_eq_smul (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    {x y : n → K} (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0)
    (hyx : (σ ∘ y) ⬝ᵥ (Q *ᵥ x) ≠ 0) :
    ∃ g ∈ Q.specialIsometryGroup σ, ∃ c ≠ (0 : K), (g : Matrix n n K) *ᵥ x = c • y := by
  obtain ⟨d, hd, hdε⟩ := hadm
  set b := (σ ∘ y) ⬝ᵥ (Q *ᵥ x)
  -- Rescale `y` by `c = σ(d / b)`, so that `h(c y, x) = d`.
  set c := σ (d * b⁻¹)
  have hσc : σ c = d * b⁻¹ := hσ _
  have hc : c ≠ 0 := (map_ne_zero σ).mpr (mul_ne_zero hd (inv_ne_zero hyx))
  have hcyx : (σ ∘ (c • y)) ⬝ᵥ (Q *ᵥ x) = d := by
    rw [RingHom.comp_smul, smul_dotProduct, smul_eq_mul, hσc, mul_assoc, inv_mul_cancel₀ hyx,
      mul_one]
  have hcy : (σ ∘ (c • y)) ⬝ᵥ (Q *ᵥ (c • y)) = 0 := by
    rw [comp_smul_dotProduct_mulVec_smul, hy, mul_zero]
  have hxcy : (σ ∘ x) ⬝ᵥ (Q *ᵥ (c • y)) + (σ ∘ (c • y)) ⬝ᵥ (Q *ᵥ x) = 0 := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε (c • y) x, hcyx, add_comm]
    exact hdε
  obtain ⟨g, hg, hgx⟩ :=
    exists_mem_specialIsometryGroup_mulVec_eq hσ hQ hε hx hcy (hcyx ▸ hd) hxcy
  exact ⟨g, hg, c, hc, hgx⟩

/-- A special isometry `g` sending `x` to a nonzero multiple of `y` sends the point of `x` to
the point of `y`. -/
private theorem smul_mk_eq_mk_of_mulVec_eq_smul {g : Q.specialIsometryGroup σ} {x y : n → K}
    (hx : x ≠ 0) (hy : y ≠ 0) {c : K} (hc : c ≠ 0)
    (h : ((g : SpecialLinearGroup n K) : Matrix n n K) *ᵥ x = c • y) :
    g • Projectivization.mk K x hx = Projectivization.mk K y hy := by
  rw [Subgroup.smul_def, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  exact ⟨Units.mk0 c hc, by
    rw [Units.smul_def, Units.val_mk0, SpecialLinearGroup.smul_def, smul_eq_mulVec, h]⟩

/-- **The special unitary group is transitive on isotropic points.** Let `σ` be an involution,
`Q` an invertible `ε`-Hermitian matrix with `ε * ε = 1`, and suppose that the trace
`t ↦ t + ε σ(t)` is onto the elements `s` with `σ(s) = ε s` and has a nonzero kernel element.
Then the special isometry group of `Q` acts transitively on the isotropic points. -/
theorem isPretransitive_isotropicPoints (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0) :
    MulAction.IsPretransitive (Q.specialIsometryGroup σ) (Q.isotropicPoints σ) := by
  -- One step joins the points of isotropic `x`, `y` with `h(y, x) ≠ 0`.
  have hstep {x y : n → K} (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0)
      (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0) (hyx : (σ ∘ y) ⬝ᵥ (Q *ᵥ x) ≠ 0) :
      ∃ g : Q.specialIsometryGroup σ,
        g • Projectivization.mk K x hx0 = Projectivization.mk K y hy0 := by
    obtain ⟨g, hg, c, hc, hgx⟩ :=
      exists_mem_specialIsometryGroup_mulVec_eq_smul hσ hQ hε hadm hx hy hyx
    exact ⟨⟨g, hg⟩, smul_mk_eq_mk_of_mulVec_eq_smul hx0 hy0 hc hgx⟩
  refine ⟨fun p q ↦ ?_⟩
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  induction p using Projectivization.ind with | h x hx0 => ?_
  induction q using Projectivization.ind with | h y hy0 => ?_
  rw [mk_mem_isotropicPoints_iff] at hp hq
  suffices ∃ g : Q.specialIsometryGroup σ,
      g • Projectivization.mk K x hx0 = Projectivization.mk K y hy0 from
    this.imp fun g hg ↦ Subtype.ext hg
  by_cases hyx : (σ ∘ y) ⬝ᵥ (Q *ᵥ x) = 0
  · -- Pass through an isotropic `z = u + c x` with `h(z, x) ≠ 0` and `h(z, y) ≠ 0`.
    have hxy : (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 0 := by
      rw [← map_eq_zero σ, apply_comp_dotProduct_mulVec hσ hQ, hyx, mul_zero]
    obtain ⟨u, hux, huy⟩ := exists_comp_dotProduct_mulVec_ne_zero_pair (σ := σ) hdet hx0 hy0
    obtain ⟨c, hz⟩ :=
      exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero hσ hQ hε htr hp hux
    have hpair (w : n → K) : (σ ∘ (u + c • x)) ⬝ᵥ (Q *ᵥ w) =
        (σ ∘ u) ⬝ᵥ (Q *ᵥ w) + σ c * ((σ ∘ x) ⬝ᵥ (Q *ᵥ w)) := by
      rw [comp_add_dotProduct_mulVec, RingHom.comp_smul, smul_dotProduct, smul_eq_mul]
    have hzx : (σ ∘ (u + c • x)) ⬝ᵥ (Q *ᵥ x) ≠ 0 := by rwa [hpair, hp, mul_zero, add_zero]
    have hzy : (σ ∘ (u + c • x)) ⬝ᵥ (Q *ᵥ y) ≠ 0 := by rwa [hpair, hxy, mul_zero, add_zero]
    have hyz : (σ ∘ y) ⬝ᵥ (Q *ᵥ (u + c • x)) ≠ 0 := by
      rw [comp_dotProduct_mulVec_swap hσ hQ hε]
      exact mul_ne_zero (left_ne_zero_of_mul_eq_one hε) ((map_ne_zero σ).mpr hzy)
    have hz0 : u + c • x ≠ 0 := fun h ↦ hzx (by rw [h]; simp)
    obtain ⟨g, hg⟩ := hstep hx0 hz0 hp hz hzx
    obtain ⟨g', hg'⟩ := hstep hz0 hy0 hz hq hyz
    exact ⟨g' * g, by rw [mul_smul, hg, hg']⟩
  · exact hstep hx0 hy0 hp hq hyx

/-! ### The kernel of the action -/

/-- **An isometry fixing every isotropic point is central.** Under the hypotheses of
`Matrix.isPretransitive_isotropicPoints`, if some point is isotropic, then an element of the
special isometry group fixing every isotropic point is a scalar matrix, hence central. -/
theorem mem_center_specialIsometryGroup_of_forall_smul_eq (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    [Nonempty (Q.isotropicPoints σ)] {g : Q.specialIsometryGroup σ}
    (hg : ∀ p : Q.isotropicPoints σ, g • p = p) :
    g ∈ Subgroup.center (Q.specialIsometryGroup σ) := by
  obtain ⟨p₀⟩ := ‹Nonempty (Q.isotropicPoints σ)›
  obtain ⟨c, hc⟩ := exists_eq_scalar_of_forall_mulVec_eq_smul hσ hQ hε hdet htr hadm
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
