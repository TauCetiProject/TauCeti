/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Primitive
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.Algebra.Group.Hom.Defs
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Hyperbolic rescalings and Siegel transformations from unitary transvections

For an involution `σ` of `K` and an invertible `ε`-Hermitian matrix `Q`, this file shows that
`T = ⨆ p, Q.unitaryTransvectionSubgroup σ p` is normal in `Q.specialIsometryGroup σ`, acts
transitively up to scalar on nonzero isotropic vectors, contains all `σ`-fixed hyperbolic
rescalings, and contains every admissible Siegel transformation away from `SU₃(2)`.

## Main results

* `Matrix.exists_mem_iSup_unitaryTransvectionSubgroup_hyperbolic_rescale`: hyperbolic rescalings.
* `Matrix.siegelTransvection_mem_iSup_unitaryTransvectionSubgroup`: Siegel transformations in `T`.

## References

* D. E. Taylor, *The Geometry of the Classical Groups* (1992), §10.4 and Theorem 11.27.
-/

public section

open scoped LinearAlgebra.Projectivization Pointwise

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] {Q : Matrix n n K} {σ : K →+* K}
  {ε : K}
/-- The supremum of the unitary transvection groups over all isotropic points is normal in
`Q.specialIsometryGroup σ`, since conjugation permutes the summands along the action. -/
instance normal_iSup_unitaryTransvectionSubgroup :
    (⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p).Normal := by
  refine ⟨fun x hx g ↦ ?_⟩
  suffices ⨆ p, Q.unitaryTransvectionSubgroup σ p ≤
      (⨆ p, Q.unitaryTransvectionSubgroup σ p).comap (MulAut.conj g).toMonoidHom by
    simpa [Subgroup.mem_comap, MulAut.conj_apply] using this hx
  refine iSup_le fun p y hy ↦ Subgroup.mem_comap.mpr ?_
  refine le_iSup (Q.unitaryTransvectionSubgroup σ) (g • p) ?_
  rw [unitaryTransvectionSubgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  exact ⟨y, hy, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
/-- Any unitary transvection along an isotropic vector (zero or nonzero) that belongs to
`Q.specialIsometryGroup σ` lies in the supremum of the point transvection subgroups. -/
theorem unitaryTransvection_mem_iSup_unitaryTransvectionSubgroup {g : SpecialLinearGroup n K}
    (hg : g ∈ Q.specialIsometryGroup σ) {v : n → K} (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) {a : K}
    (hga : (g : Matrix n n K) = Q.unitaryTransvection σ v a) :
    (⟨g, hg⟩ : Q.specialIsometryGroup σ) ∈
      ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p := by
  by_cases hv0 : v = 0
  · have h1 : (⟨g, hg⟩ : Q.specialIsometryGroup σ) = 1 :=
      Subtype.ext (Subtype.ext (by simpa [hv0] using hga))
    rw [h1]; exact one_mem _
  · let p : Q.isotropicPoints σ :=
      ⟨Projectivization.mk K v hv0, (mk_mem_isotropicPoints_iff hv0).mpr hv⟩
    exact Subgroup.mem_iSup_of_mem p ((mem_unitaryTransvectionSubgroup_mk_iff hv0 p.2).mpr ⟨a, hga⟩)
/-- An admissible unitary transvection along an isotropic vector `v` gives an element of the
transvection supremum with matrix `Q.unitaryTransvection σ v a`. -/
theorem exists_mem_iSup_unitaryTransvectionSubgroup_coe_eq_unitaryTransvection
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) {v : n → K}
    (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) {a : K} (ha : a + ε * σ a = 0) :
    ∃ t ∈ ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p,
      (t : Matrix n n K) = Q.unitaryTransvection σ v a := by
  obtain ⟨g, hg, hga⟩ := exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ hv ha
  exact ⟨⟨g, hg⟩, unitaryTransvection_mem_iSup_unitaryTransvectionSubgroup hg hv hga, hga⟩
/-- A single unitary transvection in the supremum connects two non-orthogonal isotropic vectors
`x` and `y` while fixing every vector orthogonal to both. -/
theorem exists_mem_iSup_unitaryTransvectionSubgroup_fixes_and_mulVec_eq_smul_of_ne_zero
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    {U : Set (n → K)} {x y : n → K} (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0)
    (hUx : ∀ u ∈ U, (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0) (hUy : ∀ u ∈ U, (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0)
    (hyx : (σ ∘ y) ⬝ᵥ (Q *ᵥ x) ≠ 0) :
    ∃ t ∈ ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p, ∃ c ≠ (0 : K),
      (∀ u ∈ U, (t : Matrix n n K) *ᵥ u = u) ∧ (t : Matrix n n K) *ᵥ x = c • y := by
  obtain ⟨d, hd, hdε⟩ := hadm
  set b := (σ ∘ y) ⬝ᵥ (Q *ᵥ x) with hb; have hσb : σ b ≠ 0 := (map_ne_zero σ).mpr hyx
  have hσb_eq : σ b = ε * ((σ ∘ x) ⬝ᵥ (Q *ᵥ y)) := by rw [hb, apply_comp_dotProduct_mulVec hσ hQ]
  have hε0 : ε ≠ 0 := left_ne_zero_of_mul (hσb_eq ▸ hσb); set c := d * (σ b)⁻¹
  have hc : c ≠ 0 := mul_ne_zero hd (inv_ne_zero hσb)
  have hcyx : (σ ∘ (c • y)) ⬝ᵥ (Q *ᵥ x) = σ d := by
    simp [c, TauCeti.map_comp_smul, hσ b, ← hb, hyx]
  have hcy : (σ ∘ (c • y)) ⬝ᵥ (Q *ᵥ (c • y)) = 0 := by
    rw [comp_smul_dotProduct_mulVec_smul, hy, mul_zero]
  have hxcy : (σ ∘ x) ⬝ᵥ (Q *ᵥ (c • y)) + (σ ∘ (c • y)) ⬝ᵥ (Q *ᵥ x) = 0 := by
    refine mul_left_cancel₀ hε0 ?_
    have h1 : c * (ε * ((σ ∘ x) ⬝ᵥ (Q *ᵥ y))) = d := by rw [← hσb_eq]; simp [c, hσb]
    rw [hcyx, mulVec_smul, dotProduct_smul, smul_eq_mul]; linear_combination h1 + hdε
  have hw : (σ ∘ (c • y - x)) ⬝ᵥ (Q *ᵥ (c • y - x)) = 0 := by
    simp only [map_comp_sub, sub_dotProduct, mulVec_sub, dotProduct_sub, hx, hcy]
    linear_combination -hxcy
  obtain ⟨g, hg, hga, hgx⟩ :=
    exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection_sub_and_mulVec_eq
      hσ hQ hx hcy (hcyx ▸ (map_ne_zero σ).mpr hd) hxcy
  refine ⟨⟨g, hg⟩, unitaryTransvection_mem_iSup_unitaryTransvectionSubgroup hg hw hga, c, hc,
    fun u hu ↦ ?_, hgx⟩
  have hxu : (σ ∘ x) ⬝ᵥ (Q *ᵥ u) = 0 := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (hUx u hu)
  have hyu : (σ ∘ y) ⬝ᵥ (Q *ᵥ u) = 0 := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (hUy u hu)
  simp [hga, unitaryTransvection_mulVec, hxu, hyu]
/-- The transvection supremum acts transitively up to nonzero scalar on nonzero isotropic
vectors. -/
theorem exists_mem_iSup_unitaryTransvectionSubgroup_mulVec_eq_smul (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0) (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0) {x y : n → K} (hx₀ : x ≠ 0) (hy₀ : y ≠ 0)
    (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0) :
    ∃ t ∈ ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p, ∃ c ≠ (0 : K),
      (t : Matrix n n K) *ᵥ x = c • y := by
  by_cases hyx : (σ ∘ y) ⬝ᵥ (Q *ᵥ x) = 0
  swap
  · obtain ⟨t, ht, c, hc, -, htx⟩ :=
      exists_mem_iSup_unitaryTransvectionSubgroup_fixes_and_mulVec_eq_smul_of_ne_zero (U := ∅)
        hσ hQ hadm hx hy (by simp) (by simp) hyx
    exact ⟨t, ht, c, hc, htx⟩
  obtain ⟨v, hvx, hvy⟩ := exists_comp_dotProduct_mulVec_ne_zero_pair (σ := σ) hdet hx₀ hy₀
  obtain ⟨a, hz⟩ := exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero hσ hQ htr hx hvx
  set z := v + a • x
  have hxy : (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 0 := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hyx
  have hzx : (σ ∘ z) ⬝ᵥ (Q *ᵥ x) ≠ 0 := by simpa [z, hx] using hvx
  have hyz : (σ ∘ y) ⬝ᵥ (Q *ᵥ z) ≠ 0 :=
    (comp_dotProduct_mulVec_ne_zero_comm hσ hQ).mpr (by simpa [z, hxy] using hvy)
  obtain ⟨t₁, ht₁, c₁, hc₁, -, ht₁x⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_fixes_and_mulVec_eq_smul_of_ne_zero (U := ∅)
      hσ hQ hadm hx hz (by simp) (by simp) hzx
  obtain ⟨t₂, ht₂, c₂, hc₂, -, ht₂z⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_fixes_and_mulVec_eq_smul_of_ne_zero (U := ∅)
      hσ hQ hadm hz hy (by simp) (by simp) hyz
  refine ⟨t₂ * t₁, mul_mem ht₂ ht₁, c₁ * c₂, mul_ne_zero hc₁ hc₂, ?_⟩
  rw [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, ← mulVec_mulVec, ht₁x, mulVec_smul, ht₂z,
    smul_smul]
/-- From a nonempty isotropic-point set, construct a hyperbolic pair `(e, f)` with
`B(e, e) = B(f, f) = 0`, `B(e, f) = 1`, `B(f, e) = ε`, `ε * ε = 1`, and `σ ε = ε`. -/
theorem exists_hyperbolic_pair_of_isotropicPoints (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0) (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
    [Nonempty (Q.isotropicPoints σ)] :
    ∃ e f : n → K, e ≠ 0 ∧ f ≠ 0 ∧ (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0 ∧ (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0 ∧
      (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1 ∧ (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε ∧ ε * ε = 1 ∧ σ ε = ε := by
  obtain ⟨p₀⟩ := ‹Nonempty (Q.isotropicPoints σ)›
  set e := (p₀ : ℙ K (n → K)).rep; have he₀ : e ≠ 0 := (p₀ : ℙ K (n → K)).rep_ne_zero
  have he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0 := comp_rep_dotProduct_mulVec_rep p₀
  have : Nonempty n := let ⟨i, _⟩ := Function.ne_iff.mp he₀; ⟨i⟩
  have hε : ε * ε = 1 := mul_self_eq_one_of_trace_of_det_ne_zero hσ hQ hdet htr
  obtain ⟨u, hue, -⟩ := exists_comp_dotProduct_mulVec_ne_zero_pair (σ := σ) hdet he₀ he₀
  obtain ⟨c, hf₀⟩ := exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero hσ hQ htr he hue
  set f₀ := u + c • e
  have hef₀ : (σ ∘ e) ⬝ᵥ (Q *ᵥ f₀) ≠ 0 :=
    (comp_dotProduct_mulVec_ne_zero_comm hσ hQ).mpr (by simpa [f₀, he] using hue)
  set f := ((σ ∘ e) ⬝ᵥ (Q *ᵥ f₀))⁻¹ • f₀
  have hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0 := by rw [comp_smul_dotProduct_mulVec_smul, hf₀, mul_zero]
  have hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1 := by
    rw [mulVec_smul, dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hef₀]
  have hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε, hef, map_one, mul_one]
  have hσε : σ ε = ε := by
    have h := apply_comp_dotProduct_mulVec hσ hQ f e; rwa [hfe, hef, mul_one] at h
  have hf_ne : f ≠ 0 := fun h0 ↦ (one_ne_zero (α := K)) (by simpa [h0] using hef.symm)
  exact ⟨e, f, he₀, hf_ne, he, hf, hef, hfe, hε, hσε⟩
private theorem exists_mem_iSup_w_hyperbolic (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q)
    (hε : ε * ε = 1) (hσε : σ ε = ε) {d : K} (hd : d ≠ 0) (hdε : d + ε * σ d = 0) {e f : n → K}
    (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0) (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0) (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1)
    (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε) {u : K} (hu : u ≠ 0) (hσu : σ u = u) :
    ∃ w ∈ ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p,
      (w : Matrix n n K) *ᵥ e = -(u⁻¹ * d⁻¹) • f ∧ (w : Matrix n n K) *ᵥ f = (u * d) • e ∧
      ∀ x : n → K, (σ ∘ e) ⬝ᵥ (Q *ᵥ x) = 0 → (σ ∘ f) ⬝ᵥ (Q *ᵥ x) = 0 →
        (w : Matrix n n K) *ᵥ x = x := by
  have ha₁ : u * d + ε * σ (u * d) = 0 := by rw [map_mul, hσu]; linear_combination u * hdε
  have hσd_eq : σ d = -(ε * d) := by linear_combination ε * hdε - σ d * hε
  have hε_inv : ε⁻¹ = ε := inv_eq_of_mul_eq_one_right hε
  have ha₂ : -(ε * u⁻¹ * d⁻¹) + ε * σ (-(ε * u⁻¹ * d⁻¹)) = 0 := by
    rw [map_neg, map_mul, map_mul, map_inv₀, map_inv₀, hσε, hσu, hσd_eq, inv_neg, mul_inv, hε_inv]
    linear_combination (ε * u⁻¹ * d⁻¹) * hε
  obtain ⟨t₁, ht₁, hc₁⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_coe_eq_unitaryTransvection hσ hQ he ha₁
  obtain ⟨t₂, ht₂, hc₂⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_coe_eq_unitaryTransvection hσ hQ hf ha₂
  have ht₁e : (t₁ : Matrix n n K) *ᵥ e = e := by simp [hc₁, unitaryTransvection_mulVec, he]
  have ht₁f : (t₁ : Matrix n n K) *ᵥ f = f + (u * d) • e := by
    simp [hc₁, unitaryTransvection_mulVec, hef]
  have ht₂f : (t₂ : Matrix n n K) *ᵥ f = f := by simp [hc₂, unitaryTransvection_mulVec, hf]
  have ht₂e : (t₂ : Matrix n n K) *ᵥ e = e - (u⁻¹ * d⁻¹) • f := by
    have hε' : -(ε * u⁻¹ * d⁻¹) * ε = -(u⁻¹ * d⁻¹) := by linear_combination -u⁻¹ * d⁻¹ * hε
    rw [hc₂, unitaryTransvection_mulVec, hfe, hε', neg_smul, ← sub_eq_add_neg]
  have hud₁ : (u⁻¹ * d⁻¹) * (u * d) = 1 := by field_simp
  have hud₂ : (u * d) * (u⁻¹ * d⁻¹) = 1 := by field_simp
  refine ⟨t₁ * t₂ * t₁, mul_mem (mul_mem ht₁ ht₂) ht₁, ?_, ?_, fun x hex hfx ↦ ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul,
      ← mulVec_mulVec, ← mulVec_mulVec, ht₁e, ht₂e, mulVec_sub, mulVec_smul, ht₁e, ht₁f, smul_add,
      smul_smul, hud₁]
    module
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul,
      ← mulVec_mulVec, ← mulVec_mulVec, ht₁f, mulVec_add, mulVec_smul, ht₂f, ht₂e]
    have hmid : f + (u * d) • (e - (u⁻¹ * d⁻¹) • f) = (u * d) • e := by
      rw [smul_sub, smul_smul, hud₂]; module
    rw [hmid, mulVec_smul, ht₁e]
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul,
      ← mulVec_mulVec, ← mulVec_mulVec, hc₁, hc₂]
    simp [unitaryTransvection_mulVec, hex, hfx]
/-- **Hyperbolic rescaling lies in the transvection supremum.** For any hyperbolic pair `(e, f)` and
any nonzero `a` fixed by `σ`, some element of the transvection supremum sends `e ↦ a • e`,
`f ↦ a⁻¹ • f`, and fixes `{e, f}ᗮ` pointwise. -/
theorem exists_mem_iSup_unitaryTransvectionSubgroup_hyperbolic_rescale (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) (hσε : σ ε = ε) {d : K} (hd : d ≠ 0)
    (hdε : d + ε * σ d = 0) {e f : n → K} (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0)
    (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0) (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1) (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε)
    {a : K} (ha : a ≠ 0) (hσa : σ a = a) :
    ∃ h ∈ ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p,
      (h : Matrix n n K) *ᵥ e = a • e ∧ (h : Matrix n n K) *ᵥ f = a⁻¹ • f ∧
      ∀ x : n → K, (σ ∘ e) ⬝ᵥ (Q *ᵥ x) = 0 → (σ ∘ f) ⬝ᵥ (Q *ᵥ x) = 0 →
        (h : Matrix n n K) *ᵥ x = x := by
  obtain ⟨w₁, hw₁, hw₁e, hw₁f, hw₁x⟩ :=
    exists_mem_iSup_w_hyperbolic hσ hQ hε hσε hd hdε he hf hef hfe ha hσa
  obtain ⟨w₂, hw₂, hw₂e, hw₂f, hw₂x⟩ :=
    exists_mem_iSup_w_hyperbolic hσ hQ hε hσε hd hdε he hf hef hfe (neg_ne_zero.mpr one_ne_zero)
      (by simp)
  refine ⟨w₁ * w₂, mul_mem hw₁ hw₂, ?_, ?_, fun x hex hfx ↦ ?_⟩
  · rw [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hw₂e, mulVec_smul, hw₁f,
      smul_smul]
    congr 1; field_simp
  · rw [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hw₂f, mulVec_smul, hw₁e,
      smul_smul]
    congr 1; field_simp
  · rw [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hw₂x x hex hfx,
      hw₁x x hex hfx]
private theorem exists_mem_iSup_unitaryTransvectionSubgroup_siegelTransvection_zero_of_isotropic
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) {d : K} (hd : d ≠ 0)
    (hdε : d + ε * σ d = 0) {e x : n → K} (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0)
    (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hex : (σ ∘ e) ⬝ᵥ (Q *ᵥ x) = 0) :
    ∃ t ∈ ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p,
      (t : Matrix n n K) = Q.siegelTransvection σ ε e x 0 := by
  have hxe : (σ ∘ x) ⬝ᵥ (Q *ᵥ e) = 0 := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hex
  have hndε : -d + ε * σ (-d) = 0 := by rw [map_neg]; linear_combination -hdε
  set u' := d⁻¹ • x
  have hu' : (σ ∘ u') ⬝ᵥ (Q *ᵥ u') = 0 := by rw [comp_smul_dotProduct_mulVec_smul, hx, mul_zero]
  have heu' : (σ ∘ e) ⬝ᵥ (Q *ᵥ u') = 0 := by rw [mulVec_smul, dotProduct_smul, hex, smul_zero]
  have hu'e : (σ ∘ u') ⬝ᵥ (Q *ᵥ e) = 0 := by simp [u', TauCeti.map_comp_smul, hxe]
  have hsum : (σ ∘ (e + u')) ⬝ᵥ (Q *ᵥ (e + u')) = 0 := by
    simp [map_comp_add, add_dotProduct, mulVec_add, dotProduct_add, he, hu', heu', hu'e]
  obtain ⟨t₁, ht₁, hc₁⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_coe_eq_unitaryTransvection hσ hQ hsum hdε
  obtain ⟨t₂, ht₂, hc₂⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_coe_eq_unitaryTransvection hσ hQ he hndε
  obtain ⟨t₃, ht₃, hc₃⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_coe_eq_unitaryTransvection hσ hQ hu' hndε
  have hσd : σ d ≠ 0 := (map_ne_zero σ).mpr hd
  have hd_ratio : d * (σ d)⁻¹ = -ε := mul_right_cancel₀ hσd <| by
    rw [mul_assoc, inv_mul_cancel₀ hσd, mul_one]; linear_combination hdε
  refine ⟨t₁ * t₂ * t₃, mul_mem (mul_mem ht₁ ht₂) ht₃, mulVec_injective (funext fun v ↦ ?_)⟩
  set α := (σ ∘ e) ⬝ᵥ (Q *ᵥ v); set β := (σ ∘ u') ⬝ᵥ (Q *ᵥ v)
  have hv₃ : (t₃ : Matrix n n K) *ᵥ v = v + (-d * β) • u' := by rw [hc₃, unitaryTransvection_mulVec]
  have hv₂ : (t₂ : Matrix n n K) *ᵥ ((t₃ : Matrix n n K) *ᵥ v) =
      v + (-d * β) • u' + (-d * α) • e := by
    rw [hv₃, hc₂, unitaryTransvection_mulVec, mulVec_add, mulVec_smul, dotProduct_add,
      dotProduct_smul, heu', smul_zero, add_zero]
  rw [Subgroup.coe_mul, Subgroup.coe_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul,
    ← mulVec_mulVec, ← mulVec_mulVec, hv₂, hc₁, unitaryTransvection_mulVec]
  have hpair₁ : (σ ∘ (e + u')) ⬝ᵥ (Q *ᵥ (v + (-d * β) • u' + (-d * α) • e)) = α + β := by
    simp only [comp_add_dotProduct_mulVec, mulVec_add, mulVec_smul, dotProduct_add,
      dotProduct_smul, smul_eq_mul, he, hu', heu', hu'e, α, β]; ring
  have hlin : v + (-d * β) • u' + (-d * α) • e + (d * (α + β)) • (e + u') =
      v + (d * β) • e + (d * α) • u' := by module
  rw [hpair₁, hlin, siegelTransvection_mulVec]
  simp only [u', β, TauCeti.map_comp_smul, smul_dotProduct, smul_eq_mul, map_inv₀, smul_smul,
    zero_smul, add_zero]
  have h1 : (d * α) * d⁻¹ = α := by rw [mul_right_comm, mul_inv_cancel₀ hd, one_mul]
  have h2 : d * ((σ d)⁻¹ * ((σ ∘ x) ⬝ᵥ (Q *ᵥ v))) = -(ε * ((σ ∘ x) ⬝ᵥ (Q *ᵥ v))) := by
    rw [← mul_assoc, hd_ratio, neg_mul]
  rw [h1, h2]; module
private theorem exists_isotropic_ne_zero_in_ortho (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0) (hε : ε * ε = 1)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0) {e f : n → K}
    (he₀ : e ≠ 0) (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0) (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε) {u w : n → K}
    (hu₀ : u ≠ 0) (hw_span : w ∉ K ∙ u) (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0)
    (hw : (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0) (huw : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) :
    ∃ u₀ : n → K, u₀ ≠ 0 ∧ (σ ∘ e) ⬝ᵥ (Q *ᵥ u₀) = 0 ∧ (σ ∘ f) ⬝ᵥ (Q *ᵥ u₀) = 0 ∧
      (σ ∘ u₀) ⬝ᵥ (Q *ᵥ u₀) = 0 := by
  obtain ⟨g, -, c, hc, hgu⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_mulVec_eq_smul hσ hQ hdet htr hadm hu₀ he₀ hu he
  set w₁ := (g : Matrix n n K) *ᵥ w
  have hw₁ : (σ ∘ w₁) ⬝ᵥ (Q *ᵥ w₁) = 0 := by
    rw [comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g.2), hw]
  have hew₁ : (σ ∘ e) ⬝ᵥ (Q *ᵥ w₁) = 0 := by
    have hpair : (σ ∘ (c • e)) ⬝ᵥ (Q *ᵥ w₁) = 0 := by
      rw [← hgu, comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g.2), huw]
    rw [TauCeti.map_comp_smul, smul_dotProduct, smul_eq_mul] at hpair
    exact (mul_eq_zero.mp hpair).resolve_left ((map_ne_zero σ).mpr hc)
  have hw₁_span : w₁ ∉ K ∙ e := fun hmem ↦ hw_span <| by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have hlin : (g : Matrix n n K) *ᵥ ((a * c⁻¹) • u) = w₁ := by
      rw [mulVec_smul, hgu, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one, ha]
    exact Submodule.mem_span_singleton.mpr ⟨a * c⁻¹,
      (SpecialLinearGroup.toLin' (g : SpecialLinearGroup n K)).injective hlin⟩
  set u₀ := w₁ - (ε * ((σ ∘ f) ⬝ᵥ (Q *ᵥ w₁))) • e
  have heu₀ : (σ ∘ e) ⬝ᵥ (Q *ᵥ u₀) = 0 := by
    simp [u₀, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hew₁, he]
  have hfu₀ : (σ ∘ f) ⬝ᵥ (Q *ᵥ u₀) = 0 := by
    simp only [u₀, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, hfe]
    linear_combination -((σ ∘ f) ⬝ᵥ (Q *ᵥ w₁)) * hε
  have hw₁e : (σ ∘ w₁) ⬝ᵥ (Q *ᵥ e) = 0 := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hew₁
  exact ⟨u₀, fun h0 ↦ hw₁_span <| Submodule.mem_span_singleton.mpr
    ⟨ε * ((σ ∘ f) ⬝ᵥ (Q *ᵥ w₁)), (sub_eq_zero.mp h0).symm⟩, heu₀, hfu₀,
    by simp [u₀, map_comp_sub, TauCeti.map_comp_smul, sub_dotProduct, smul_dotProduct, mulVec_sub,
      mulVec_smul, dotProduct_sub, dotProduct_smul, hw₁, he, hew₁, hw₁e]⟩
/-- In Witt index at least two, `{e, f}ᗮ` contains a hyperbolic pair `(u₀, y₀)` with
`B(u₀, y₀) = 1` and `B(y₀, u₀) = ε`. -/
theorem exists_hyperbolic_pair_in_ortho (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q)
    (hdet : Q.det ≠ 0) (hε : ε * ε = 1) (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0) {e f : n → K} (he₀ : e ≠ 0) (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0)
    (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0) (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1) (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε)
    {u w : n → K} (hu₀ : u ≠ 0) (hw_span : w ∉ K ∙ u) (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0)
    (hw : (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0) (huw : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) :
    ∃ u₀ y₀ : n → K, (σ ∘ e) ⬝ᵥ (Q *ᵥ u₀) = 0 ∧ (σ ∘ f) ⬝ᵥ (Q *ᵥ u₀) = 0 ∧
      (σ ∘ e) ⬝ᵥ (Q *ᵥ y₀) = 0 ∧ (σ ∘ f) ⬝ᵥ (Q *ᵥ y₀) = 0 ∧
      (σ ∘ u₀) ⬝ᵥ (Q *ᵥ u₀) = 0 ∧ (σ ∘ y₀) ⬝ᵥ (Q *ᵥ y₀) = 0 ∧
      (σ ∘ u₀) ⬝ᵥ (Q *ᵥ y₀) = 1 ∧ (σ ∘ y₀) ⬝ᵥ (Q *ᵥ u₀) = ε := by
  obtain ⟨u₀, hu₀_ne, heu₀, hfu₀, hu₀_iso⟩ :=
    exists_isotropic_ne_zero_in_ortho hσ hQ hdet hε htr hadm he₀ he hfe hu₀ hw_span hu hw huw
  obtain ⟨z, hzu₀, -⟩ := exists_comp_dotProduct_mulVec_ne_zero_pair (σ := σ) hdet hu₀_ne hu₀_ne
  set z₀ := z - (ε * ((σ ∘ f) ⬝ᵥ (Q *ᵥ z))) • e - ((σ ∘ e) ⬝ᵥ (Q *ᵥ z)) • f
  have hez₀ : (σ ∘ e) ⬝ᵥ (Q *ᵥ z₀) = 0 := by
    simp [z₀, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, he, hef]
  have hfz₀ : (σ ∘ f) ⬝ᵥ (Q *ᵥ z₀) = 0 := by
    simp only [z₀, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, hfe, hf]
    linear_combination -((σ ∘ f) ⬝ᵥ (Q *ᵥ z)) * hε
  have hz₀u₀ : (σ ∘ z₀) ⬝ᵥ (Q *ᵥ u₀) ≠ 0 := by
    simpa [z₀, map_comp_sub, TauCeti.map_comp_smul, sub_dotProduct, smul_dotProduct, heu₀, hfu₀]
      using hzu₀
  obtain ⟨t, hy₁⟩ :=
    exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero hσ hQ htr hu₀_iso hz₀u₀
  set y₁ := z₀ + t • u₀
  have hy₁u₀ : (σ ∘ y₁) ⬝ᵥ (Q *ᵥ u₀) ≠ 0 := by
    simpa [y₁, map_comp_add, TauCeti.map_comp_smul, add_dotProduct, smul_dotProduct, hu₀_iso] using
      hz₀u₀
  have hu₀y₁ : (σ ∘ u₀) ⬝ᵥ (Q *ᵥ y₁) ≠ 0 := (comp_dotProduct_mulVec_ne_zero_comm hσ hQ).mpr hy₁u₀
  set y₀ := ((σ ∘ u₀) ⬝ᵥ (Q *ᵥ y₁))⁻¹ • y₁
  have hu₀y₀ : (σ ∘ u₀) ⬝ᵥ (Q *ᵥ y₀) = 1 := by
    rw [mulVec_smul, dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hu₀y₁]
  have hy₀u₀ : (σ ∘ y₀) ⬝ᵥ (Q *ᵥ u₀) = ε := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε, hu₀y₀, map_one, mul_one]
  exact ⟨u₀, y₀, heu₀, hfu₀,
    by simp [y₀, y₁, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, hez₀, heu₀],
    by simp [y₀, y₁, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, hfz₀, hfu₀],
    hu₀_iso, by rw [comp_smul_dotProduct_mulVec_smul, hy₁, mul_zero], hu₀y₀, hy₀u₀⟩
section SiegelGen

variable (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
  (hε : ε * ε = 1) (hσε : σ ε = ε) (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
  {d : K} (hd : d ≠ 0) (hdε : d + ε * σ d = 0)
  {e f : n → K} (he₀ : e ≠ 0) (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0)
  (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0) (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1)
  (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε)
include hσ hQ hε he hef hfe in
private theorem admissible_of_siegelTransvection_mem {w₀ : n → K} (hew₀ : (σ ∘ e) ⬝ᵥ (Q *ᵥ w₀) = 0)
    {c : K} {s : Q.specialIsometryGroup σ}
    (hcs : (s : Matrix n n K) = Q.siegelTransvection σ ε e w₀ c) :
    c + ε * σ c + ε * ((σ ∘ w₀) ⬝ᵥ (Q *ᵥ w₀)) = 0 := by
  have hdef := (mem_specialIsometryGroup_iff.mp s.2).symm
  rw [hcs, transpose_map_siegelTransvection_mul_mul hσ hQ he hew₀] at hdef
  have hQe : Q *ᵥ e ≠ 0 := fun h0 ↦
    left_ne_zero_of_mul (hε ▸ one_ne_zero) (by simpa [h0] using hfe.symm)
  have heQ : (σ ∘ e) ᵥ* Q ≠ 0 := fun h0 ↦ one_ne_zero <| by
    have hef' := hef; rw [dotProduct_mulVec, h0, zero_dotProduct] at hef'; exact hef'.symm
  have h0 : (c + ε * σ c + ε * ((σ ∘ w₀) ⬝ᵥ (Q *ᵥ w₀))) • vecMulVec (Q *ᵥ e) ((σ ∘ e) ᵥ* Q) = 0 :=
    by simpa [add_eq_left] using hdef.symm
  exact (smul_eq_zero.mp h0).resolve_right (not_or.mpr ⟨hQe, heQ⟩ ∘ vecMulVec_eq_zero.mp)
include hσ hQ hε he hef hfe in
private theorem siegelTransvection_mem_iSup_of_exists_param {w₀ : n → K}
    (hew₀ : (σ ∘ e) ⬝ᵥ (Q *ᵥ w₀) = 0) {c c₀ : K}
    (hc : c + ε * σ c + ε * ((σ ∘ w₀) ⬝ᵥ (Q *ᵥ w₀)) = 0) {s₀ : Q.specialIsometryGroup σ}
    (hs₀ : s₀ ∈ ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p)
    (hcs₀ : (s₀ : Matrix n n K) = Q.siegelTransvection σ ε e w₀ c₀) {s : SpecialLinearGroup n K}
    (hs : s ∈ Q.specialIsometryGroup σ)
    (hcs : (s : Matrix n n K) = Q.siegelTransvection σ ε e w₀ c) :
    (⟨s, hs⟩ : Q.specialIsometryGroup σ) ∈
      ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p := by
  have hc₀ := admissible_of_siegelTransvection_mem hσ hQ hε he hef hfe hew₀ hcs₀
  have hc_diff : (c - c₀) + ε * σ (c - c₀) = 0 := by rw [map_sub]; linear_combination hc - hc₀
  obtain ⟨t₀, ht₀, hct₀⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_coe_eq_unitaryTransvection hσ hQ he hc_diff
  have heq : (⟨s, hs⟩ : Q.specialIsometryGroup σ) = t₀ * s₀ := Subtype.ext (Subtype.ext (by
    rw [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, hcs, hct₀, hcs₀,
      ← siegelTransvection_zero_eq_unitaryTransvection (ε := ε),
      siegelTransvection_mul_siegelTransvection he hew₀ (by simp)]
    simp))
  rw [heq]; exact mul_mem ht₀ hs₀
include hσ hQ hε hσε htr hd hdε he hf hef hfe in
private theorem siegelTransvection_mem_iSup_of_fixed_ne {a : K} (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hσa : σ a = a) {w₀ : n → K} (hew₀ : (σ ∘ e) ⬝ᵥ (Q *ᵥ w₀) = 0)
    (hfw₀ : (σ ∘ f) ⬝ᵥ (Q *ᵥ w₀) = 0) {c : K} (hc : c + ε * σ c + ε * ((σ ∘ w₀) ⬝ᵥ (Q *ᵥ w₀)) = 0)
    {s : SpecialLinearGroup n K} (hs : s ∈ Q.specialIsometryGroup σ)
    (hcs : (s : Matrix n n K) = Q.siegelTransvection σ ε e w₀ c) :
    (⟨s, hs⟩ : Q.specialIsometryGroup σ) ∈
      ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p := by
  have ha_sub : a - 1 ≠ 0 := sub_ne_zero.mpr ha1; set w' := (a - 1)⁻¹ • w₀
  have hew' : (σ ∘ e) ⬝ᵥ (Q *ᵥ w') = 0 := by simp [w', mulVec_smul, dotProduct_smul, hew₀]
  have hfw' : (σ ∘ f) ⬝ᵥ (Q *ᵥ w') = 0 := by simp [w', mulVec_smul, dotProduct_smul, hfw₀]
  have hw'e : (σ ∘ w') ⬝ᵥ (Q *ᵥ e) = 0 := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hew'
  obtain ⟨c', hc'⟩ := htr (-(ε * ((σ ∘ w') ⬝ᵥ (Q *ᵥ w')))) <| by
    rw [map_neg, map_mul, hσε, apply_comp_dotProduct_mulVec hσ hQ, mul_neg]
  have hc'_adm : c' + ε * σ c' + ε * ((σ ∘ w') ⬝ᵥ (Q *ᵥ w')) = 0 := by linear_combination hc'
  obtain ⟨s', hs', hcs'⟩ :=
    exists_mem_specialIsometryGroup_coe_eq_siegelTransvection hσ hQ he hew' hc'_adm
  obtain ⟨h, hh, hhe, -, hhx⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_hyperbolic_rescale hσ hQ hε hσε hd hdε he hf hef
      hfe ha0 hσa
  let s₁ : Q.specialIsometryGroup σ := ⟨s', hs'⟩
  let s₂ : Q.specialIsometryGroup σ := h * (s₁ * h⁻¹ * s₁⁻¹)
  have hs'_inv : (↑(s₁⁻¹) : Matrix n n K) =
      Q.siegelTransvection σ ε e (-w') (-c' - ε * ((σ ∘ w') ⬝ᵥ (Q *ᵥ w'))) := by
    have hmul := siegelTransvection_mul_siegelTransvection_neg_eq_one (ε := ε) he hew' hw'e c'
    have hmul' : (s₁ : Matrix n n K) * (↑(s₁⁻¹) : Matrix n n K) = 1 := by
      rw [← SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
        SpecialLinearGroup.coe_one]
    rw [← hcs'] at hmul; exact (inv_eq_right_inv hmul').symm.trans (inv_eq_right_inv hmul)
  have hconj : (↑(h * s₁ * h⁻¹) : Matrix n n K) =
      Q.siegelTransvection σ ε e (a • w') (c' * a * a) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul,
      Subgroup.coe_inv, hcs', coe_mul_siegelTransvection_mul_coe_inv h.2, hhe, hhx w' hew' hfw',
      siegelTransvection_smul_left hσ, hσa]
  have hw_sum : a • w' + -w' = w₀ := by
    have hlin : a • w' + -w' = (a - 1) • w' := by module
    rw [hlin]
    exact smul_inv_smul₀ ha_sub w₀
  have hcs₂ : (s₂ : Matrix n n K) = Q.siegelTransvection σ ε e w₀
      (c' * a * a + (-c' - ε * ((σ ∘ w') ⬝ᵥ (Q *ᵥ w'))) -
        ε * ((σ ∘ (a • w')) ⬝ᵥ (Q *ᵥ (-w')))) := by
    have hs₂_eq : s₂ = (h * s₁ * h⁻¹) * s₁⁻¹ := by simp [s₂, mul_assoc]
    rw [hs₂_eq, Subgroup.coe_mul, SpecialLinearGroup.coe_mul, hconj, hs'_inv,
      siegelTransvection_mul_siegelTransvection he (by simp [mulVec_neg, hew'])
        (by simp [TauCeti.map_comp_smul, hw'e]), hw_sum]
  exact siegelTransvection_mem_iSup_of_exists_param hσ hQ hε he hef hfe hew₀ hc
    (mul_mem hh (normal_iSup_unitaryTransvectionSubgroup.conj_mem _ (inv_mem hh) s₁)) hcs₂ hs hcs
include hε he hf hef hfe in
private theorem siegelTransvection_mem_iSup_of_card_le_two (hcard : Fintype.card n ≤ 2)
    {w₀ : n → K} (hew₀ : (σ ∘ e) ⬝ᵥ (Q *ᵥ w₀) = 0) (hfw₀ : (σ ∘ f) ⬝ᵥ (Q *ᵥ w₀) = 0) {c : K}
    {s : SpecialLinearGroup n K} (hs : s ∈ Q.specialIsometryGroup σ)
    (hcs : (s : Matrix n n K) = Q.siegelTransvection σ ε e w₀ c) :
    (⟨s, hs⟩ : Q.specialIsometryGroup σ) ∈
      ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p := by
  have hw₀ : w₀ = 0 := by
    by_contra hw₀_ne
    have hli : LinearIndependent K ![e, f, w₀] := Fintype.linearIndependent_iff.mpr fun g hg ↦ by
      rw [Fin.sum_univ_three] at hg
      have hg1 : g 1 = 0 := by
        simpa [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, he, hef, hew₀] using
          congrArg (fun v ↦ (σ ∘ e) ⬝ᵥ (Q *ᵥ v)) hg
      have hg0 : g 0 = 0 := by
        have h0 := congrArg (fun v ↦ (σ ∘ f) ⬝ᵥ (Q *ᵥ v)) hg
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
          Matrix.head_cons, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul,
          hfe, hf, hfw₀, mul_zero, add_zero, mulVec_zero, dotProduct_zero] at h0
        linear_combination ε * h0 - g 0 * hε
      have hg2 : g 2 • w₀ = 0 := by simpa [hg0, hg1] using hg
      intro i; fin_cases i; · exact hg0
      · exact hg1
      · exact (smul_eq_zero.mp hg2).resolve_right hw₀_ne
    have hle := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at hle; omega
  subst hw₀; rw [siegelTransvection_zero_eq_unitaryTransvection] at hcs
  exact unitaryTransvection_mem_iSup_unitaryTransvectionSubgroup hs he hcs
include hσ hQ hdet hε htr hd hdε he₀ he hf hef hfe in
private theorem siegelTransvection_mem_iSup_of_witt_two {u w : n → K} (hu₀ : u ≠ 0)
    (hw_span : w ∉ K ∙ u) (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hw : (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0)
    (huw : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) {w₀ : n → K} (hew₀ : (σ ∘ e) ⬝ᵥ (Q *ᵥ w₀) = 0) {c : K}
    (hc : c + ε * σ c + ε * ((σ ∘ w₀) ⬝ᵥ (Q *ᵥ w₀)) = 0) {s : SpecialLinearGroup n K}
    (hs : s ∈ Q.specialIsometryGroup σ)
    (hcs : (s : Matrix n n K) = Q.siegelTransvection σ ε e w₀ c) :
    (⟨s, hs⟩ : Q.specialIsometryGroup σ) ∈
      ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p := by
  obtain ⟨u₀, y₀, heu₀, -, hey₀, -, hu₀_iso, hy₀_iso, -, hy₀u₀⟩ :=
    exists_hyperbolic_pair_in_ortho hσ hQ hdet hε htr ⟨d, hd, hdε⟩ he₀ he hf hef hfe hu₀ hw_span hu
      hw huw
  obtain ⟨x₁, x₂, x₃, hx₁, hx₂, hx₃, hex₁, hex₂, hex₃, hsum⟩ : ∃ x₁ x₂ x₃ : n → K,
      (σ ∘ x₁) ⬝ᵥ (Q *ᵥ x₁) = 0 ∧ (σ ∘ x₂) ⬝ᵥ (Q *ᵥ x₂) = 0 ∧ (σ ∘ x₃) ⬝ᵥ (Q *ᵥ x₃) = 0 ∧
      (σ ∘ e) ⬝ᵥ (Q *ᵥ x₁) = 0 ∧ (σ ∘ e) ⬝ᵥ (Q *ᵥ x₂) = 0 ∧ (σ ∘ e) ⬝ᵥ (Q *ᵥ x₃) = 0 ∧
      x₁ + x₂ + x₃ = w₀ := by
    by_cases hwu₀ : (σ ∘ w₀) ⬝ᵥ (Q *ᵥ u₀) = 0
    · have hwy : (σ ∘ (w₀ + y₀)) ⬝ᵥ (Q *ᵥ u₀) ≠ 0 := by
        rw [comp_add_dotProduct_mulVec, hwu₀, zero_add, hy₀u₀]
        exact left_ne_zero_of_mul (hε ▸ one_ne_zero)
      obtain ⟨t, ht⟩ := exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero hσ hQ htr hu₀_iso
        hwy
      exact ⟨w₀ + y₀ + t • u₀, (-t) • u₀, (-1 : K) • y₀, ht,
        by rw [comp_smul_dotProduct_mulVec_smul, hu₀_iso, mul_zero],
        by rw [comp_smul_dotProduct_mulVec_smul, hy₀_iso, mul_zero],
        by simp [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, hew₀, hey₀, heu₀],
        by rw [mulVec_smul, dotProduct_smul, heu₀, smul_zero],
        by rw [mulVec_smul, dotProduct_smul, hey₀, smul_zero], by module⟩
    · obtain ⟨t, ht⟩ := exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero hσ hQ htr hu₀_iso
        hwu₀
      exact ⟨w₀ + t • u₀, (-t) • u₀, (0 : K) • u₀, ht,
        by rw [comp_smul_dotProduct_mulVec_smul, hu₀_iso, mul_zero],
        by rw [comp_smul_dotProduct_mulVec_smul, hu₀_iso, mul_zero],
        by simp [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, hew₀, heu₀],
        by rw [mulVec_smul, dotProduct_smul, heu₀, smul_zero],
        by rw [mulVec_smul, dotProduct_smul, heu₀, smul_zero], by module⟩
  obtain ⟨t₁, ht₁, hc₁⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_siegelTransvection_zero_of_isotropic hσ hQ hd hdε
      he hx₁ hex₁
  obtain ⟨t₂, ht₂, hc₂⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_siegelTransvection_zero_of_isotropic hσ hQ hd hdε
      he hx₂ hex₂
  obtain ⟨t₃, ht₃, hc₃⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_siegelTransvection_zero_of_isotropic hσ hQ hd hdε
      he hx₃ hex₃
  have hx₁e := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hex₁
  have hx₂e := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hex₂
  have hx₁₂e : (σ ∘ (x₁ + x₂)) ⬝ᵥ (Q *ᵥ e) = 0 := by
    rw [comp_add_dotProduct_mulVec, hx₁e, hx₂e, add_zero]
  have hcs₀ : (↑(t₁ * t₂ * t₃) : Matrix n n K) = Q.siegelTransvection σ ε e w₀
        (0 + 0 - ε * ((σ ∘ x₁) ⬝ᵥ (Q *ᵥ x₂)) + 0 - ε * ((σ ∘ (x₁ + x₂)) ⬝ᵥ (Q *ᵥ x₃))) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul,
      hc₁, hc₂, hc₃, siegelTransvection_mul_siegelTransvection he hex₂ hx₁e,
      siegelTransvection_mul_siegelTransvection he hex₃ hx₁₂e, hsum]
  exact siegelTransvection_mem_iSup_of_exists_param hσ hQ hε he hef hfe hew₀ hc
    (mul_mem (mul_mem ht₁ ht₂) ht₃) hcs₀ hs hcs
include hσ hQ hdet hε hσε htr hd hdε he₀ he hf hef hfe in
private theorem siegelTransvection_mem_iSup_of_ortho_left
    (hgen : (∃ a : K, a ≠ 0 ∧ a ≠ 1 ∧ σ a = a) ∨ Fintype.card n ≤ 2 ∨
      ∃ u w : n → K, u ≠ 0 ∧ w ∉ K ∙ u ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 ∧
        (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0)
    {w' : n → K} (hew' : (σ ∘ e) ⬝ᵥ (Q *ᵥ w') = 0) {c' : K}
    (hc' : c' + ε * σ c' + ε * ((σ ∘ w') ⬝ᵥ (Q *ᵥ w')) = 0) {s' : SpecialLinearGroup n K}
    (hs' : s' ∈ Q.specialIsometryGroup σ)
    (hcs' : (s' : Matrix n n K) = Q.siegelTransvection σ ε e w' c') :
    (⟨s', hs'⟩ : Q.specialIsometryGroup σ) ∈
      ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p := by
  set α := ε * ((σ ∘ f) ⬝ᵥ (Q *ᵥ w')); set w₀ := w' - α • e
  have hew₀ : (σ ∘ e) ⬝ᵥ (Q *ᵥ w₀) = 0 := by
    simp [w₀, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hew', he]
  have hfw₀ : (σ ∘ f) ⬝ᵥ (Q *ᵥ w₀) = 0 := by
    simp only [w₀, α, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, hfe]
    linear_combination -((σ ∘ f) ⬝ᵥ (Q *ᵥ w')) * hε
  set c₀ := c' + α - ε * σ α
  have hcs₀ : (s' : Matrix n n K) = Q.siegelTransvection σ ε e w₀ c₀ := by
    rw [hcs', ← sub_add_cancel w' (α • e), siegelTransvection_add_smul]
  have hw₀w₀ : (σ ∘ w₀) ⬝ᵥ (Q *ᵥ w₀) = (σ ∘ w') ⬝ᵥ (Q *ᵥ w') := by
    have hw'e := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hew'
    simp [w₀, map_comp_sub, TauCeti.map_comp_smul, sub_dotProduct, smul_dotProduct, mulVec_sub,
      mulVec_smul, dotProduct_sub, dotProduct_smul, he, hew', hw'e]
  have hc₀ : c₀ + ε * σ c₀ + ε * ((σ ∘ w₀) ⬝ᵥ (Q *ᵥ w₀)) = 0 := by
    rw [hw₀w₀]; simp only [c₀, map_add, map_sub, map_mul, hσε, hσ α]
    linear_combination hc' - α * hε
  rcases hgen with ⟨a, ha0, ha1, hσa⟩ | hcard | ⟨u₁, w₁, hu₁0, hw₁s, hu₁, hw₁, hu₁w₁⟩
  · exact siegelTransvection_mem_iSup_of_fixed_ne hσ hQ hε hσε htr hd hdε he hf hef hfe ha0 ha1
      hσa hew₀ hfw₀ hc₀ hs' hcs₀
  · exact siegelTransvection_mem_iSup_of_card_le_two hε he hf hef hfe hcard hew₀ hfw₀ hs' hcs₀
  · exact siegelTransvection_mem_iSup_of_witt_two hσ hQ hdet hε htr hd hdε he₀ he hf hef hfe hu₁0
      hw₁s hu₁ hw₁ hu₁w₁ hew₀ hc₀ hs' hcs₀
include hσ hQ hdet hε hσε htr hd hdε he₀ he hf hef hfe in
/-- **Every admissible Siegel transformation lies in the transvection supremum.** -/
theorem siegelTransvection_mem_iSup_unitaryTransvectionSubgroup
    (hgen : (∃ a : K, a ≠ 0 ∧ a ≠ 1 ∧ σ a = a) ∨ Fintype.card n ≤ 2 ∨
      ∃ u w : n → K, u ≠ 0 ∧ w ∉ K ∙ u ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 ∧
        (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0)
    {u w : n → K} (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (huw : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0)
    {c : K} (hc : c + ε * σ c + ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ w)) = 0)
    {s : SpecialLinearGroup n K} (hs : s ∈ Q.specialIsometryGroup σ)
    (hcs : (s : Matrix n n K) = Q.siegelTransvection σ ε u w c) :
    (⟨s, hs⟩ : Q.specialIsometryGroup σ) ∈
      ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p := by
  by_cases hu0 : u = 0
  · rw [show (⟨s, hs⟩ : Q.specialIsometryGroup σ) = 1 from
      Subtype.ext (Subtype.ext (by simpa [hu0] using hcs))]
    exact one_mem _
  obtain ⟨g, -, a, ha, hgu⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_mulVec_eq_smul hσ hQ hdet htr ⟨d, hd, hdε⟩ hu0 he₀
      hu he
  let s_g : Q.specialIsometryGroup σ := g * ⟨s, hs⟩ * g⁻¹
  have hcs_g : (s_g : Matrix n n K) =
      Q.siegelTransvection σ ε e (σ a • ((g : Matrix n n K) *ᵥ w)) (c * a * σ a) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul,
      Subgroup.coe_inv, hcs, coe_mul_siegelTransvection_mul_coe_inv g.2, hgu,
      siegelTransvection_smul_left hσ]
  have hew_g : (σ ∘ e) ⬝ᵥ (Q *ᵥ (σ a • ((g : Matrix n n K) *ᵥ w))) = 0 := by
    have hpair : (σ ∘ (a • e)) ⬝ᵥ (Q *ᵥ ((g : Matrix n n K) *ᵥ w)) = 0 := by
      rw [← hgu, comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g.2), huw]
    rw [TauCeti.map_comp_smul, smul_dotProduct, smul_eq_mul] at hpair
    rw [mulVec_smul, dotProduct_smul, (mul_eq_zero.mp hpair).resolve_left ((map_ne_zero σ).mpr ha),
      smul_zero]
  have hc_g : c * a * σ a + ε * σ (c * a * σ a) + ε * ((σ ∘ (σ a • ((g : Matrix n n K) *ᵥ w))) ⬝ᵥ
        (Q *ᵥ (σ a • ((g : Matrix n n K) *ᵥ w)))) = 0 := by
    rw [comp_smul_dotProduct_mulVec_smul, hσ a,
      comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g.2), map_mul, map_mul,
      hσ a]
    linear_combination (a * σ a) * hc
  have hmem_g := siegelTransvection_mem_iSup_of_ortho_left hσ hQ hdet hε hσε htr hd hdε he₀ he hf
    hef hfe hgen hew_g hc_g s_g.2 hcs_g
  have hs_eq : (⟨s, hs⟩ : Q.specialIsometryGroup σ) = g⁻¹ * s_g * (g⁻¹)⁻¹ := by
    dsimp only [s_g]; group
  rw [hs_eq]; exact normal_iSup_unitaryTransvectionSubgroup.conj_mem _ hmem_g g⁻¹
end SiegelGen
end Matrix

end
