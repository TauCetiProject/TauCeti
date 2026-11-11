/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import TauCeti.LinearAlgebra.Matrix.SiegelTransvection
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.IsotropicPoints
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Group.Hom.Defs
import TauCeti.Algebra.Ring.Hom
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm
import TauCeti.LinearAlgebra.Projectivization.Basic

/-!
# Primitivity of a special unitary group on its isotropic points

Let `σ` be an involution of a field `K`, let `Q` be an invertible `ε`-Hermitian matrix,
`(Q ^ σ)ᵀ = ε • Q`, and write `B(x, y) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y)` for its sesquilinear form. The
special isometry group `Matrix.specialIsometryGroup Q σ` acts on the isotropic points
`Matrix.isotropicPoints Q σ` of projective space; under the two trace hypotheses of
`Matrix.isPretransitive_isotropicPoints` (`t ↦ t + ε σ(t)` is onto `{s | σ(s) = ε s}` and has a
nonzero kernel element), this action is transitive and has central kernel when nonempty. This file
proves that it is **primitive** (`Matrix.isPreprimitive_isotropicPoints`). Through
`MulAction.IsPreprimitive.isQuasiPreprimitive`, this supplies the quasiprimitivity input of
Iwasawa's simplicity criterion `MulAction.IwasawaStructure.isSimpleGroup` for the projective
special unitary groups.

The stabilizer in `SU(Q)` of an isotropic point `[u]` preserves orthogonality to `[u]`, so on the
remaining isotropic points it has at most two orbits: those `[x] ≠ [u]` with `B(u, x) = 0` and
those with `B(u, x) ≠ 0`. Unlike in the symplectic case, unitary transvections alone do not exhaust
the second orbit: in Witt index one (for instance `SU_3(q)`), `u^⊥ / K ∙ u` is anisotropic, so the
only unitary transvections fixing `u` are those along `u`, which cannot act transitively on the
isotropic points outside `u^⊥`. Instead, the two stabilizer orbits come from two families of
special isometries:

* **Non-orthogonal orbit (`B(u, x) ≠ 0` and `B(u, y) ≠ 0`).** After normalizing `u` to `u'` with
  `B(u', x) = 1` and rescaling `y` so that `B(u', y) = 1`, the Siegel transformation
  `Matrix.siegelTransvection Q σ ε u' (y - x - c • u') c` with `c = ε B(x, y)` fixes `u` and sends
  `x` to `y` (`Matrix.exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq`), without using
  either trace hypothesis or nondegeneracy of `Q`.
* **Orthogonal orbit (`B(u, x) = 0` and `B(u, y) = 0`, off `K ∙ u`).** When `B(y, x) ≠ 0`, a
  unitary transvection along `c • y - x` fixes `u` (since `c • y - x ∈ u^⊥`) and sends `x` to
  `c • y`; when `B(y, x) = 0`, two such steps pass through an isotropic vector `v + a • x ∈ u^⊥`
  paired nontrivially with both `x` and `y`.

Together these give `Matrix.exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul`: the
stabilizer of `u` connects `[x]` to `[y]` whenever both lie off `K ∙ u` and `B(u, x) = 0` holds
for both or for neither. Any block containing two distinct isotropic points `[u] ≠ [x]` is
therefore invariant under the stabilizer of each of its points, meets both orbits when both are
nonempty (via an isotropic vector `v + c • u ∈ x^⊥ \ u^⊥` if `B(u, x) = 0`, or `[y]` / `[y + u]` if
`B(u, x) ≠ 0`), and so equals the whole space of isotropic points. No rank or Witt-index hypothesis
is needed.

The block-closure argument is modeled on the symplectic case in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Primitive`.

## Main results

* `Matrix.exists_mem_specialIsometryGroup_coe_eq_siegelTransvection`: an admissible Siegel
  transformation `S(u, w, c)` lies in `Q.specialIsometryGroup σ`.
* `Matrix.coe_mul_siegelTransvection_mul_coe_inv`: a special isometry `g` conjugates `S(u, w, c)`
  to `S(g u, g w, c)`.
* `Matrix.exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq`: a Siegel transformation in
  `Q.specialIsometryGroup σ` fixes an isotropic `u` and sends an isotropic `x` to an isotropic `y`
  whenever `B(u, x) = B(u, y) ≠ 0`.
* `Matrix.exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul`: the stabilizer of an
  isotropic `u` sends an isotropic `x ∉ K ∙ u` to a nonzero multiple of an isotropic `y ∉ K ∙ u`
  whenever `B(u, x) = 0 ↔ B(u, y) = 0`.
* `Matrix.isPreprimitive_isotropicPoints`: `Q.specialIsometryGroup σ` acts primitively on
  `Q.isotropicPoints σ`.

## References

* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapters 10 and 11.
* L. C. Grove, *Classical Groups and Geometric Algebra* (2002), Chapter 11.
* M. Eichler, *Quadratische Formen und orthogonale Gruppen*, Springer (1952).
-/

public section

open MulAction
open scoped LinearAlgebra.Projectivization Pointwise

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable {R : Type*} [CommRing R] {Q : Matrix n n R} {σ : R →+* R}

/-- **A special isometry conjugates `S(u, w, c)` to `S(g u, g w, c)`.** -/
theorem coe_mul_siegelTransvection_mul_coe_inv {g : SpecialLinearGroup n R}
    (hg : g ∈ Q.specialIsometryGroup σ) (ε : R) (u w : n → R) (c : R) :
    (g : Matrix n n R) * Q.siegelTransvection σ ε u w c *
      ((g⁻¹ : SpecialLinearGroup n R) : Matrix n n R) =
      Q.siegelTransvection σ ε ((g : Matrix n n R) *ᵥ u) ((g : Matrix n n R) *ᵥ w) c := by
  rw [mul_siegelTransvection (mem_specialIsometryGroup_iff.mp hg), Matrix.mul_assoc,
    ← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one, Matrix.mul_one]

/-- **Admissible Siegel transformations belong to the special isometry group.** -/
theorem exists_mem_specialIsometryGroup_coe_eq_siegelTransvection (hσ : Function.Involutive σ)
    {ε : R} (hQ : (Q.map σ)ᵀ = ε • Q) {u w : n → R} (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0)
    (huw : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) (hwu : (σ ∘ w) ⬝ᵥ (Q *ᵥ u) = 0) {c : R}
    (hc : c + ε * σ c + ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ w)) = 0) :
    ∃ g ∈ Q.specialIsometryGroup σ,
      (g : Matrix n n R) = Q.siegelTransvection σ ε u w c :=
  ⟨⟨_, det_siegelTransvection hu huw hwu c⟩,
    mem_specialIsometryGroup_iff.mpr
      (transpose_map_siegelTransvection_mul_mul_self hσ hQ hu huw hwu hc),
    rfl⟩

end CommRing

section Field

variable {K : Type*} [Field K] {Q : Matrix n n K} {σ : K →+* K} {ε : K}

/-! ### Stabilizer orbits on isotropic vectors -/

/-- **A Siegel transformation joins two isotropic vectors at a given nonzero pairing with `u`.**
If `u`, `x`, `y` are isotropic and `B(u, x) = B(u, y) ≠ 0`, then a Siegel transformation along a
scalar multiple of `u` lies in the special isometry group, fixes `u`, and sends `x` to `y`. -/
theorem exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1)
    {u x y : n → K} (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0)
    (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0)
    (hux : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) ≠ 0)
    (hxy : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = (σ ∘ u) ⬝ᵥ (Q *ᵥ y)) :
    ∃ g ∈ Q.specialIsometryGroup σ,
      (g : Matrix n n K) *ᵥ u = u ∧ (g : Matrix n n K) *ᵥ x = y := by
  have hσε : σ ε = ε := by
    rcases mul_self_eq_one_iff.mp hε with rfl | rfl <;> simp
  -- Normalize `u` to `u' = σ(b)⁻¹ • u` so that `B(u', x) = B(u', y) = 1`.
  set b := (σ ∘ u) ⬝ᵥ (Q *ᵥ x)
  set u' := (σ b)⁻¹ • u
  set c := ε * ((σ ∘ x) ⬝ᵥ (Q *ᵥ y))
  set w := y - x - c • u'
  have hu'pair (v : n → K) : (σ ∘ u') ⬝ᵥ (Q *ᵥ v) = b⁻¹ * ((σ ∘ u) ⬝ᵥ (Q *ᵥ v)) := by
    rw [comp_smul_dotProduct_mulVec, map_inv₀, hσ]
  have hu' : (σ ∘ u') ⬝ᵥ (Q *ᵥ u') = 0 := by rw [comp_smul_dotProduct_mulVec_smul, hu, mul_zero]
  have hu'x : (σ ∘ u') ⬝ᵥ (Q *ᵥ x) = 1 := by rw [hu'pair, inv_mul_cancel₀ hux]
  have hu'y : (σ ∘ u') ⬝ᵥ (Q *ᵥ y) = 1 := by rw [hu'pair, ← hxy, inv_mul_cancel₀ hux]
  have hu'w : (σ ∘ u') ⬝ᵥ (Q *ᵥ w) = 0 := by
    rw [mulVec_sub, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_sub, dotProduct_smul,
      hu'y, hu'x, hu', smul_zero, sub_self, sub_zero]
  have hwu' : (σ ∘ w) ⬝ᵥ (Q *ᵥ u') = 0 := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε, hu'w, map_zero, mul_zero]
  have hxu' : (σ ∘ x) ⬝ᵥ (Q *ᵥ u') = ε := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε, hu'x, map_one, mul_one]
  have hxw : (σ ∘ x) ⬝ᵥ (Q *ᵥ w) = 0 := by
    rw [mulVec_sub, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_sub, dotProduct_smul,
      hx, hxu', smul_eq_mul, sub_zero]
    linear_combination -((σ ∘ x) ⬝ᵥ (Q *ᵥ y)) * hε
  have hwx : (σ ∘ w) ⬝ᵥ (Q *ᵥ x) = 0 := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε, hxw, map_zero, mul_zero]
  -- Isotropy of `y = (x + w) + c • u'` gives `c + ε σ(c) + ε B(w, w) = 0`.
  have hc : c + ε * σ c + ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ w)) = 0 := by
    have hy_eq : (x + w) + c • u' = y := by dsimp [w]; abel
    have hxwu' : (σ ∘ (x + w)) ⬝ᵥ (Q *ᵥ u') = ε := by
      rw [comp_add_dotProduct_mulVec, hxu', hwu', add_zero]
    have hxw_self : (σ ∘ (x + w)) ⬝ᵥ (Q *ᵥ (x + w)) = (σ ∘ w) ⬝ᵥ (Q *ᵥ w) := by
      rw [comp_add_dotProduct_mulVec, mulVec_add, dotProduct_add, dotProduct_add, hx, hxw, hwx,
        add_zero, zero_add, zero_add]
    have h0 := comp_add_smul_dotProduct_mulVec_add_smul hσ hQ hε hu' (x + w) c
    rw [hy_eq, hy, hxw_self, hxwu', map_mul, hσε, mul_left_comm ε (σ c) ε, hε, mul_one] at h0
    linear_combination -ε * h0 - c * hε
  obtain ⟨g, hg, hS⟩ :=
    exists_mem_specialIsometryGroup_coe_eq_siegelTransvection hσ hQ hu' hu'w hwu' hc
  refine ⟨g, hg, ?_, ?_⟩
  · have hσb : σ b ≠ 0 := (map_ne_zero σ).mpr hux
    have hu_eq : σ b • u' = u := smul_inv_smul₀ hσb u
    rw [← hu_eq, mulVec_smul, hS, siegelTransvection_mulVec_self hu' hwu']
  · rw [hS, siegelTransvection_mulVec, hu'x, hwx, one_smul, mul_zero, zero_smul, sub_zero]
    dsimp [w]
    abel

/-- **One orthogonal transvection step.** If `x` and `y` are isotropic vectors orthogonal to `u`
with `B(y, x) ≠ 0`, and some nonzero `d` satisfies `d + ε σ(d) = 0`, then a unitary transvection
fixes `u` and sends `x` to a nonzero multiple of `y`. -/
private theorem exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul_of_ne_zero
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0) {u x y : n → K}
    (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0)
    (hux : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0) (huy : (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0)
    (hyx : (σ ∘ y) ⬝ᵥ (Q *ᵥ x) ≠ 0) :
    ∃ g ∈ Q.specialIsometryGroup σ, ∃ c ≠ (0 : K),
      (g : Matrix n n K) *ᵥ u = u ∧ (g : Matrix n n K) *ᵥ x = c • y := by
  obtain ⟨d, hd, hdε⟩ := hadm
  have hσε : σ ε = ε := by
    rcases mul_self_eq_one_iff.mp hε with rfl | rfl <;> simp
  set b := (σ ∘ y) ⬝ᵥ (Q *ᵥ x)
  set c := σ (d * b⁻¹)
  have hc : c ≠ 0 := (map_ne_zero σ).mpr (mul_ne_zero hd (inv_ne_zero hyx))
  have hcyx : (σ ∘ (c • y)) ⬝ᵥ (Q *ᵥ x) = d := by
    rw [comp_smul_dotProduct_mulVec, hσ, mul_assoc, inv_mul_cancel₀ hyx, mul_one]
  have hw : (σ ∘ (c • y - x)) ⬝ᵥ (Q *ᵥ (c • y - x)) = 0 := by
    rw [comp_sub_dotProduct_mulVec, mulVec_sub, dotProduct_sub, dotProduct_sub,
      comp_smul_dotProduct_mulVec_smul, hy, hx, mul_zero, zero_sub, sub_zero,
      comp_dotProduct_mulVec_swap hσ hQ hε (c • y) x, hcyx]
    linear_combination -hdε
  have ha : d⁻¹ + ε * σ d⁻¹ = 0 := by
    have hσd : σ d ≠ 0 := (map_ne_zero σ).mpr hd
    have hσdε : σ d + ε * d = 0 := by
      have h := congrArg σ hdε
      rwa [map_add, map_mul, hσ, map_zero, hσε] at h
    rw [map_inv₀]
    field_simp
    linear_combination hσdε
  obtain ⟨g, hg, hga⟩ := exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ hw ha
  refine ⟨g, hg, c, hc, ?_, ?_⟩
  · have hyu : (σ ∘ y) ⬝ᵥ (Q *ᵥ u) = 0 := by
      rw [comp_dotProduct_mulVec_swap hσ hQ hε, huy, map_zero, mul_zero]
    have hxu : (σ ∘ x) ⬝ᵥ (Q *ᵥ u) = 0 := by
      rw [comp_dotProduct_mulVec_swap hσ hQ hε, hux, map_zero, mul_zero]
    rw [hga, unitaryTransvection_mulVec, comp_sub_dotProduct_mulVec, comp_smul_dotProduct_mulVec,
      hyu, hxu, mul_zero, sub_zero, mul_zero, zero_smul, add_zero]
  · rw [hga, unitaryTransvection_mulVec, comp_sub_dotProduct_mulVec, hcyx, hx, sub_zero,
      inv_mul_cancel₀ hd, one_smul, add_sub_cancel]

/-- Given two vectors `x, y ∉ K ∙ u` over an invertible matrix `Q` and surjective `σ`, some `v`
satisfies `B(v, u) = 0`, `B(v, x) ≠ 0`, and `B(v, y) ≠ 0`. -/
private theorem exists_comp_dotProduct_mulVec_eq_zero_and_ne_zero_pair
    (hσ : Function.Surjective σ) (hdet : Q.det ≠ 0) {u x y : n → K}
    (hx : x ∉ K ∙ u) (hy : y ∉ K ∙ u) :
    ∃ v : n → K, (σ ∘ v) ⬝ᵥ (Q *ᵥ u) = 0 ∧ (σ ∘ v) ⬝ᵥ (Q *ᵥ x) ≠ 0 ∧
      (σ ∘ v) ⬝ᵥ (Q *ᵥ y) ≠ 0 := by
  obtain ⟨v₁, hv₁u, hv₁x⟩ := exists_comp_dotProduct_mulVec_eq_zero_and_ne_zero hσ hdet hx
  obtain ⟨v₂, hv₂u, hv₂y⟩ := exists_comp_dotProduct_mulVec_eq_zero_and_ne_zero hσ hdet hy
  by_cases h₁ : (σ ∘ v₁) ⬝ᵥ (Q *ᵥ y) = 0
  · by_cases h₂ : (σ ∘ v₂) ⬝ᵥ (Q *ᵥ x) = 0
    · exact ⟨v₁ + v₂, by rw [comp_add_dotProduct_mulVec, hv₁u, hv₂u, add_zero],
        by rwa [comp_add_dotProduct_mulVec, h₂, add_zero],
        by rwa [comp_add_dotProduct_mulVec, h₁, zero_add]⟩
    · exact ⟨v₂, hv₂u, h₂, hv₂y⟩
  · exact ⟨v₁, hv₁u, hv₁x, h₁⟩

/-- **Two orthogonal transvection steps.** The stabilizer of `u` connects any two isotropic vectors
orthogonal to `u` off `K ∙ u`. -/
private theorem exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul_of_eq_zero
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    {u x y : n → K} (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0)
    (hx_span : x ∉ K ∙ u) (hy_span : y ∉ K ∙ u)
    (hux : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0) (huy : (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0) :
    ∃ g ∈ Q.specialIsometryGroup σ, ∃ c ≠ (0 : K),
      (g : Matrix n n K) *ᵥ u = u ∧ (g : Matrix n n K) *ᵥ x = c • y := by
  have hx₀ : x ≠ 0 := (ne_of_mem_of_not_mem (Submodule.zero_mem _) hx_span).symm
  have hε : ε * ε = 1 := by
    refine mul_self_eq_one_of_trace hσ hQ htr ?_
    have : Nonempty n := ⟨(Function.ne_iff.mp hx₀).choose⟩
    rintro rfl
    exact hdet det_zero
  by_cases hyx : (σ ∘ y) ⬝ᵥ (Q *ᵥ x) = 0
  swap
  · exact exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul_of_ne_zero
      hσ hQ hε hadm hx hy hux huy hyx
  -- Choose `v` orthogonal to `u` and paired nontrivially with both `x` and `y`, then correct
  -- `v` to an isotropic vector `z = v + a • x`.
  obtain ⟨v, hvu, hvx, hvy⟩ :=
    exists_comp_dotProduct_mulVec_eq_zero_and_ne_zero_pair hσ.surjective hdet hx_span hy_span
  obtain ⟨a, hz⟩ := exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero hσ hQ htr hx hvx
  set z := v + a • x
  have hxu : (σ ∘ x) ⬝ᵥ (Q *ᵥ u) = 0 := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε, hux, map_zero, mul_zero]
  have hxy : (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 0 := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε, hyx, map_zero, mul_zero]
  have huz : (σ ∘ u) ⬝ᵥ (Q *ᵥ z) = 0 := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε, comp_add_dotProduct_mulVec,
      comp_smul_dotProduct_mulVec, hvu, hxu, mul_zero, add_zero, map_zero, mul_zero]
  have hzx : (σ ∘ z) ⬝ᵥ (Q *ᵥ x) ≠ 0 := by
    rwa [comp_add_dotProduct_mulVec, comp_smul_dotProduct_mulVec, hx, mul_zero, add_zero]
  have hyz : (σ ∘ y) ⬝ᵥ (Q *ᵥ z) ≠ 0 := by
    have hzy : (σ ∘ z) ⬝ᵥ (Q *ᵥ y) ≠ 0 := by
      rwa [comp_add_dotProduct_mulVec, comp_smul_dotProduct_mulVec, hxy, mul_zero, add_zero]
    rw [comp_dotProduct_mulVec_swap hσ hQ hε]
    exact mul_ne_zero (left_ne_zero_of_mul_eq_one hε) ((map_ne_zero σ).mpr hzy)
  obtain ⟨g₁, hg₁, c₁, hc₁, hg₁u, hg₁x⟩ :=
    exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul_of_ne_zero
      hσ hQ hε hadm hx hz hux huz hzx
  obtain ⟨g₂, hg₂, c₂, hc₂, hg₂u, hg₂z⟩ :=
    exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul_of_ne_zero
      hσ hQ hε hadm hz hy huz huy hyz
  refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, c₁ * c₂, mul_ne_zero hc₁ hc₂, ?_, ?_⟩
  · rw [SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hg₁u, hg₂u]
  · rw [SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hg₁x, mulVec_smul, hg₂z, smul_smul]

/-- **The stabilizer of an isotropic vector `u` is projectively transitive on both orthogonality
classes off `K ∙ u`.** Let `u`, `x`, `y` be isotropic vectors with `x ∉ K ∙ u`, `y ∉ K ∙ u`, and
`B(u, x) = 0 ↔ B(u, y) = 0`. Then an element of `Q.specialIsometryGroup σ` fixes `u` and sends `x`
to a nonzero scalar multiple of `y`. -/
theorem exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    {u x y : n → K} (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0)
    (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0)
    (hx_span : x ∉ K ∙ u) (hy_span : y ∉ K ∙ u)
    (h : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0 ↔ (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0) :
    ∃ g ∈ Q.specialIsometryGroup σ, ∃ c ≠ (0 : K),
      (g : Matrix n n K) *ᵥ u = u ∧ (g : Matrix n n K) *ᵥ x = c • y := by
  by_cases hux : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0
  · exact exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul_of_eq_zero
      hσ hQ hdet htr hadm hx hy hx_span hy_span hux (h.mp hux)
  · have huy : (σ ∘ u) ⬝ᵥ (Q *ᵥ y) ≠ 0 := mt h.mpr hux
    have hε : ε * ε = 1 := by
      refine mul_self_eq_one_of_trace hσ hQ htr ?_
      rintro rfl
      simp at hux
    set c := ((σ ∘ u) ⬝ᵥ (Q *ᵥ x)) / ((σ ∘ u) ⬝ᵥ (Q *ᵥ y))
    have hc : c ≠ 0 := div_ne_zero hux huy
    have hcy : (σ ∘ (c • y)) ⬝ᵥ (Q *ᵥ (c • y)) = 0 := by
      rw [comp_smul_dotProduct_mulVec_smul, hy, mul_zero]
    have hucy : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = (σ ∘ u) ⬝ᵥ (Q *ᵥ (c • y)) := by
      rw [mulVec_smul, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ huy]
    obtain ⟨g, hg, hgu, hgx⟩ :=
      exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq hσ hQ hε hu hx hcy hux hucy
    exact ⟨g, hg, c, hc, hgu, hgx⟩

/-! ### Block closure and primitivity -/

/-- Package a nonzero isotropic vector as an element of `Q.isotropicPoints σ`. -/
private def isotropicPointMk {v : n → K} (hv₀ : v ≠ 0) (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) :
    Q.isotropicPoints σ :=
  ⟨Projectivization.mk K v hv₀, (mk_mem_isotropicPoints_iff hv₀).mpr hv⟩

omit [Fintype n] [DecidableEq n] in
private theorem ne_zero_of_notMem_span {u x : n → K} (hx : x ∉ K ∙ u) : x ≠ 0 :=
  (ne_of_mem_of_not_mem (Submodule.zero_mem _) hx).symm

omit [DecidableEq n] in
private theorem notMem_span_of_comp_dotProduct_mulVec {u a z : n → K}
    (ha : (σ ∘ u) ⬝ᵥ (Q *ᵥ a) = 0) (hz : (σ ∘ u) ⬝ᵥ (Q *ᵥ z) ≠ 0) : z ∉ K ∙ a := fun hza ↦ by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hza
  simp [mulVec_smul, ha] at hz

/-- **A block contains each stabilizer orbit that it meets.** -/
private theorem isotropicPointMk_mem_of_isBlock (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    {B : Set (Q.isotropicPoints σ)} (hB : IsBlock (Q.specialIsometryGroup σ) B)
    {u x y : n → K} (hu₀ : u ≠ 0) (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0)
    (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0)
    (hx_span : x ∉ K ∙ u) (hy_span : y ∉ K ∙ u)
    (huB : isotropicPointMk hu₀ hu ∈ B)
    (hxB : isotropicPointMk (ne_zero_of_notMem_span hx_span) hx ∈ B)
    (h : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0 ↔ (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0) :
    isotropicPointMk (ne_zero_of_notMem_span hy_span) hy ∈ B := by
  obtain ⟨g, hg, c, hc, hgu, hgx⟩ :=
    exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul
      hσ hQ hdet htr hadm hu hx hy hx_span hy_span h
  let g' : Q.specialIsometryGroup σ := ⟨g, hg⟩
  have hgu_pt : g' • isotropicPointMk hu₀ hu = isotropicPointMk hu₀ hu := by
    apply Subtype.ext
    rw [isotropicPointMk, SubMulAction.val_smul, Subgroup.smul_def, Projectivization.smul_mk,
      Projectivization.mk_eq_mk_iff']
    exact ⟨1, by rw [SpecialLinearGroup.smul_def, smul_eq_mulVec, one_smul]; exact hgu.symm⟩
  have hgy_pt :
      isotropicPointMk (ne_zero_of_notMem_span hy_span) hy =
        g' • isotropicPointMk (ne_zero_of_notMem_span hx_span) hx := by
    apply Subtype.ext
    rw [isotropicPointMk, isotropicPointMk, SubMulAction.val_smul, Subgroup.smul_def,
      Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    exact ⟨c⁻¹, by rw [SpecialLinearGroup.smul_def, smul_eq_mulVec, hgx, inv_smul_smul₀ hc]⟩
  have hgB : g' • B = B := hB.smul_eq_of_mem huB (by rwa [hgu_pt])
  rw [hgy_pt, ← hgB]
  exact Set.smul_mem_smul_set hxB

/-- Given an isotropic `u` and a vector `x` with `u ∉ K ∙ x` and `B(u, x) = 0`, some isotropic `s`
satisfies `B(x, s) = 0` and `B(u, s) ≠ 0`. -/
private theorem exists_isotropic_ortho_and_not_ortho (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) {u x : n → K}
    (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hu_span : u ∉ K ∙ x)
    (hux : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0) :
    ∃ s : n → K, (σ ∘ s) ⬝ᵥ (Q *ᵥ s) = 0 ∧ (σ ∘ x) ⬝ᵥ (Q *ᵥ s) = 0 ∧
      (σ ∘ u) ⬝ᵥ (Q *ᵥ s) ≠ 0 := by
  obtain ⟨v, hvx, hvu⟩ :=
    exists_comp_dotProduct_mulVec_eq_zero_and_ne_zero hσ.surjective hdet hu_span
  obtain ⟨c, hs⟩ := exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero hσ hQ htr hu hvu
  refine ⟨v + c • u, hs, ?_, ?_⟩
  · rw [comp_dotProduct_mulVec_swap hσ hQ hε, comp_add_dotProduct_mulVec,
      comp_smul_dotProduct_mulVec, hvx, hux, mul_zero, add_zero, map_zero, mul_zero]
  · rw [comp_dotProduct_mulVec_swap hσ hQ hε, comp_add_dotProduct_mulVec,
      comp_smul_dotProduct_mulVec, hu, mul_zero, add_zero]
    exact mul_ne_zero (left_ne_zero_of_mul_eq_one hε) ((map_ne_zero σ).mpr hvu)

/-- **Non-orthogonal block closure.** If a block `B` contains two isotropic points `[u]` and `[x]`
with `B(u, x) ≠ 0`, then `B` contains every isotropic point `[y]` off `K ∙ u`. -/
private theorem isotropicPointMk_mem_of_isBlock_of_ne_zero (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    {B : Set (Q.isotropicPoints σ)} (hB : IsBlock (Q.specialIsometryGroup σ) B)
    {u x y : n → K} (hu₀ : u ≠ 0) (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0)
    (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0)
    (hu_span : u ∉ K ∙ x) (hx_span : x ∉ K ∙ u) (hy_span : y ∉ K ∙ u)
    (huB : isotropicPointMk hu₀ hu ∈ B)
    (hxB : isotropicPointMk (ne_zero_of_notMem_span hx_span) hx ∈ B)
    (hux : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) ≠ 0) :
    isotropicPointMk (ne_zero_of_notMem_span hy_span) hy ∈ B := by
  by_cases huy : (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0
  swap
  · exact isotropicPointMk_mem_of_isBlock hσ hQ hdet htr hadm hB hu₀ hu hx hy hx_span hy_span
      huB hxB (iff_of_false hux huy)
  have hxu : (σ ∘ x) ⬝ᵥ (Q *ᵥ u) ≠ 0 := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε]
    exact mul_ne_zero (left_ne_zero_of_mul_eq_one hε) ((map_ne_zero σ).mpr hux)
  have hnot_x : ∀ z, (σ ∘ u) ⬝ᵥ (Q *ᵥ z) = 0 → z ∉ K ∙ u → z ∉ K ∙ x := fun z hz hzu hzx ↦ by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hzx
    obtain rfl : c = 0 := by simpa [mulVec_smul, hux] using hz
    simp at hzu
  have hx₀ := ne_zero_of_notMem_span hx_span
  by_cases hxy : (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 0
  swap
  · exact isotropicPointMk_mem_of_isBlock hσ hQ hdet htr hadm hB hx₀ hx hu hy hu_span
      (hnot_x y huy hy_span) hxB huB (iff_of_false hxu hxy)
  -- Both `u` and `x` are orthogonal to `y`, so `[y + u]` is isotropic, orthogonal to `u`, and
  -- paired nontrivially with `x`.
  have hyu : (σ ∘ y) ⬝ᵥ (Q *ᵥ u) = 0 := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε, huy, map_zero, mul_zero]
  have hs : (σ ∘ (y + u)) ⬝ᵥ (Q *ᵥ (y + u)) = 0 := by
    simpa [hy, hyu] using comp_add_smul_dotProduct_mulVec_add_smul hσ hQ hε hu y 1
  have hsu : (σ ∘ u) ⬝ᵥ (Q *ᵥ (y + u)) = 0 := by
    rw [mulVec_add, dotProduct_add, huy, hu, add_zero]
  have hs_span : y + u ∉ K ∙ u := fun hs_mem ↦
    hy_span (by simpa using Submodule.sub_mem _ hs_mem (Submodule.mem_span_singleton_self u))
  have hxs : (σ ∘ x) ⬝ᵥ (Q *ᵥ (y + u)) ≠ 0 := by
    rwa [mulVec_add, dotProduct_add, hxy, zero_add]
  have hsB := isotropicPointMk_mem_of_isBlock hσ hQ hdet htr hadm hB hx₀ hx hu hs hu_span
    (hnot_x _ hsu hs_span) hxB huB (iff_of_false hxu hxs)
  exact isotropicPointMk_mem_of_isBlock hσ hQ hdet htr hadm hB hu₀ hu hs hy hs_span hy_span
    huB hsB (iff_of_true hsu huy)

/-- **The special unitary group acts primitively on its isotropic points.** Let `σ` be an
involution, let `Q` be an invertible `ε`-Hermitian matrix, and suppose that the trace
`t ↦ t + ε σ(t)` is onto the elements `s` with `σ(s) = ε s` and has a nonzero kernel element.
Then `Matrix.specialIsometryGroup Q σ` acts primitively on `Matrix.isotropicPoints Q σ`. -/
theorem isPreprimitive_isotropicPoints (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0) :
    IsPreprimitive (Q.specialIsometryGroup σ) (Q.isotropicPoints σ) := by
  rcases subsingleton_or_nontrivial (Q.isotropicPoints σ) with _ | ⟨p₀, -, -⟩
  · exact IsPreprimitive.of_subsingleton
  have hε : ε * ε = 1 := by
    refine mul_self_eq_one_of_trace hσ hQ htr ?_
    have : Nonempty n := ⟨(Function.ne_iff.mp (p₀ : ℙ K (n → K)).rep_ne_zero).choose⟩
    rintro rfl
    exact hdet det_zero
  have := isPretransitive_isotropicPoints hσ hQ hε hdet htr hadm
  refine { isTrivialBlock_of_isBlock := fun {B} hB ↦ ?_ }
  rcases B.subsingleton_or_nontrivial with hB₁ | ⟨p, hpB, q, hqB, hpq⟩
  · exact Or.inl hB₁
  refine Or.inr (Set.eq_univ_of_forall fun r ↦ ?_)
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  obtain ⟨r, hr⟩ := r
  induction p using Projectivization.ind with | h u hu₀ => ?_
  induction q using Projectivization.ind with | h x hx₀ => ?_
  induction r using Projectivization.ind with | h y hy₀ => ?_
  have hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 := (mk_mem_isotropicPoints_iff hu₀).mp hp
  have hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0 := (mk_mem_isotropicPoints_iff hx₀).mp hq
  have hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0 := (mk_mem_isotropicPoints_iff hy₀).mp hr
  have hpq' : Projectivization.mk K u hu₀ ≠ Projectivization.mk K x hx₀ :=
    Subtype.ext_iff.not.mp hpq
  have hx_span : x ∉ K ∙ u := (Projectivization.mk_eq_mk_iff_mem_span hx₀ hu₀).not.mp hpq'.symm
  by_cases hy_span : y ∈ K ∙ u
  · have hyu_mk : (⟨Projectivization.mk K y hy₀, hr⟩ : Q.isotropicPoints σ) =
        ⟨Projectivization.mk K u hu₀, hp⟩ :=
      Subtype.ext ((Projectivization.mk_eq_mk_iff_mem_span hy₀ hu₀).mpr hy_span)
    rwa [hyu_mk]
  have hu_span : u ∉ K ∙ x := (Projectivization.mk_eq_mk_iff_mem_span hu₀ hx₀).not.mp hpq'
  by_cases hux : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0
  · by_cases huy : (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0
    · exact isotropicPointMk_mem_of_isBlock hσ hQ hdet htr hadm hB hu₀ hu hx hy hx_span hy_span
        hpB hqB (iff_of_true hux huy)
    have hxu : (σ ∘ x) ⬝ᵥ (Q *ᵥ u) = 0 := by
      rw [comp_dotProduct_mulVec_swap hσ hQ hε, hux, map_zero, mul_zero]
    obtain ⟨s, hs, hxs, hus⟩ :=
      exists_isotropic_ortho_and_not_ortho hσ hQ hε hdet htr hu hu_span hux
    have hsB := isotropicPointMk_mem_of_isBlock hσ hQ hdet htr hadm hB hx₀ hx hu hs hu_span
      (notMem_span_of_comp_dotProduct_mulVec hux hus) hqB hpB (iff_of_true hxu hxs)
    exact isotropicPointMk_mem_of_isBlock hσ hQ hdet htr hadm hB hu₀ hu hs hy
      (notMem_span_of_comp_dotProduct_mulVec hu hus) hy_span hpB hsB (iff_of_false hus huy)
  · exact isotropicPointMk_mem_of_isBlock_of_ne_zero hσ hQ hε hdet htr hadm hB hu₀ hu hx hy
      hu_span hx_span hy_span hpB hqB hux

end Field

end Matrix

end
