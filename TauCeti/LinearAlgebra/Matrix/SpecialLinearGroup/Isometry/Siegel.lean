/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Elementary
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.Algebra.Group.Hom.Defs
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Hyperbolic rescalings and Siegel transformations from unitary transvections

Let `σ` be an involution of a field `K`, let `Q` be an invertible `ε`-Hermitian matrix,
`(Q.map σ)ᵀ = ε • Q`, and write `B(x, y) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y)`. When `ε * ε = 1` and
`∃ d ≠ 0, d + ε * σ d = 0`, `Matrix.elementaryUnitaryGroup Q σ` contains hyperbolic rescalings by
nonzero `σ`-fixed scalars
(`Matrix.exists_mem_elementaryUnitaryGroup_mulVec_eq_smul_and_inv_smul_and_eq_self`). When in
addition `t ↦ t + ε σ(t)` is onto `{s : K | σ s = ε * s}` (giving a hyperbolic pair in `{e, f}ᗮ` in
Witt index at least two via `Matrix.exists_comp_dotProduct_mulVec_eq_zero_and_eq_one_of_notMem_span`
and `Matrix.exists_mem_elementaryUnitaryGroup_mulVec_eq_smul` from
`TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Elementary`) and either `σ` fixes a scalar
outside `{0, 1}`, `Fintype.card n ≤ 2`, or `Q` has Witt index at least two, every
`Matrix.siegelTransvection Q σ ε u w c` in `Q.specialIsometryGroup σ` lies in
`Q.elementaryUnitaryGroup σ` (`Matrix.siegelTransvection_mem_elementaryUnitaryGroup`), feeding
`TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Iwasawa`.

## References

* D. E. Taylor, *The Geometry of the Classical Groups* (1992), §10.4 and Theorem 11.27.
-/

public section

open scoped LinearAlgebra.Projectivization Pointwise

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] {Q : Matrix n n K} {σ : K →+* K}
  {ε : K}

private theorem exists_mem_elementary_w_hyperbolic (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) (hσε : σ ε = ε) {d : K} (hd : d ≠ 0)
    (hdε : d + ε * σ d = 0) {e f : n → K} (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0)
    (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0) (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1) (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε)
    {u : K} (hu : u ≠ 0) (hσu : σ u = u) :
    ∃ w ∈ Q.elementaryUnitaryGroup σ, (w : Matrix n n K) *ᵥ e = -(u⁻¹ * d⁻¹) • f ∧
      (w : Matrix n n K) *ᵥ f = (u * d) • e ∧ ∀ x : n → K, (σ ∘ e) ⬝ᵥ (Q *ᵥ x) = 0 →
        (σ ∘ f) ⬝ᵥ (Q *ᵥ x) = 0 → (w : Matrix n n K) *ᵥ x = x := by
  have ha₂ : -(ε * u⁻¹ * d⁻¹) + ε * σ (-(ε * u⁻¹ * d⁻¹)) = 0 := by
    rw [map_neg, map_mul, map_mul, map_inv₀, map_inv₀, hσε, hσu,
      show σ d = -(ε * d) by linear_combination ε * hdε - σ d * hε, inv_neg, mul_inv,
      inv_eq_of_mul_eq_one_right hε]; linear_combination (ε * u⁻¹ * d⁻¹) * hε
  obtain ⟨t₁, ht₁, hc₁⟩ := exists_mem_elementaryUnitaryGroup_coe_eq_unitaryTransvection hσ hQ he
    (a := u * d) (by rw [map_mul, hσu]; linear_combination u * hdε)
  obtain ⟨t₂, ht₂, hc₂⟩ := exists_mem_elementaryUnitaryGroup_coe_eq_unitaryTransvection hσ hQ hf ha₂
  have ht₁e : (t₁ : Matrix n n K) *ᵥ e = e := by simp [hc₁, unitaryTransvection_mulVec, he]
  have ht₁f : (t₁ : Matrix n n K) *ᵥ f = f + (u * d) • e := by
    simp [hc₁, unitaryTransvection_mulVec, hef]
  have ht₂f : (t₂ : Matrix n n K) *ᵥ f = f := by simp [hc₂, unitaryTransvection_mulVec, hf]
  have ht₂e : (t₂ : Matrix n n K) *ᵥ e = e - (u⁻¹ * d⁻¹) • f := by
    rw [hc₂, unitaryTransvection_mulVec, hfe,
      show -(ε * u⁻¹ * d⁻¹) * ε = -(u⁻¹ * d⁻¹) by linear_combination -u⁻¹ * d⁻¹ * hε,
      neg_smul, ← sub_eq_add_neg]
  have hud : (u⁻¹ * d⁻¹) * (u * d) = 1 := by field_simp
  refine ⟨t₁ * t₂ * t₁, mul_mem (mul_mem ht₁ ht₂) ht₁, ?_, ?_, fun x hex hfx ↦ ?_⟩
  · rw [specialIsometryGroup_coe_mul_mulVec, specialIsometryGroup_coe_mul_mulVec, ht₁e, ht₂e,
      mulVec_sub, mulVec_smul, ht₁e, ht₁f, smul_add, smul_smul, hud]; module
  · rw [specialIsometryGroup_coe_mul_mulVec, specialIsometryGroup_coe_mul_mulVec, ht₁f, mulVec_add,
      mulVec_smul, ht₂f, ht₂e, show f + (u * d) • (e - (u⁻¹ * d⁻¹) • f) = (u * d) • e by
        rw [smul_sub, smul_smul, mul_comm (u * d), hud]; module, mulVec_smul, ht₁e]
  · simp [← mulVec_mulVec, hc₁, hc₂, unitaryTransvection_mulVec, hex, hfx]

/-- **Hyperbolic rescaling lies in the elementary unitary group.** Let `σ` be an involution and let
`Q` be an `ε`-Hermitian matrix with `ε * ε = 1` such that some nonzero `d` satisfies
`d + ε * σ d = 0`. For any isotropic vectors `e, f` with `B(e, f) = 1` and any nonzero `a` fixed by
`σ`, some element of `Q.elementaryUnitaryGroup σ` sends `e ↦ a • e`, `f ↦ a⁻¹ • f`, and fixes
pointwise every vector orthogonal to both `e` and `f`. -/
theorem exists_mem_elementaryUnitaryGroup_mulVec_eq_smul_and_inv_smul_and_eq_self
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0) {e f : n → K} (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0)
    (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0) (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1)
    {a : K} (ha : a ≠ 0) (hσa : σ a = a) :
    ∃ h ∈ Q.elementaryUnitaryGroup σ,
      (h : Matrix n n K) *ᵥ e = a • e ∧ (h : Matrix n n K) *ᵥ f = a⁻¹ • f ∧
      ∀ x : n → K, (σ ∘ e) ⬝ᵥ (Q *ᵥ x) = 0 → (σ ∘ f) ⬝ᵥ (Q *ᵥ x) = 0 →
        (h : Matrix n n K) *ᵥ x = x := by
  obtain ⟨d, hd, hdε⟩ := hadm
  have hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε := by rw [comp_dotProduct_mulVec_swap hσ hQ hε, hef]; simp
  have hσε : σ ε = ε := by simpa [hfe, hef] using apply_comp_dotProduct_mulVec hσ hQ f e
  have hw {u : K} := exists_mem_elementary_w_hyperbolic (u := u) hσ hQ hε hσε hd hdε he hf hef hfe
  obtain ⟨w₁, hw₁, he₁, hf₁, hx₁⟩ := hw ha hσa
  obtain ⟨w₂, hw₂, he₂, hf₂, hx₂⟩ := hw (neg_ne_zero.mpr one_ne_zero) (by simp)
  refine ⟨w₁ * w₂, mul_mem hw₁ hw₂, ?_, ?_, fun x hex hfx ↦ ?_⟩
  · rw [specialIsometryGroup_coe_mul_mulVec, he₂, mulVec_smul, hf₁, smul_smul]; congr 1; field_simp
  · rw [specialIsometryGroup_coe_mul_mulVec, hf₂, mulVec_smul, he₁, smul_smul]; congr 1; field_simp
  · rw [specialIsometryGroup_coe_mul_mulVec, hx₂ x hex hfx, hx₁ x hex hfx]

private theorem exists_mem_elementaryUnitaryGroup_siegelTransvection_zero_of_isotropic
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) {d : K} (hd : d ≠ 0)
    (hdε : d + ε * σ d = 0) {e x : n → K} (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0)
    (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hex : (σ ∘ e) ⬝ᵥ (Q *ᵥ x) = 0) :
    ∃ t ∈ Q.elementaryUnitaryGroup σ, (t : Matrix n n K) = Q.siegelTransvection σ ε e x 0 := by
  have hndε : -d + ε * σ (-d) = 0 := by rw [map_neg]; linear_combination -hdε
  set u' := d⁻¹ • x
  have hu' : (σ ∘ u') ⬝ᵥ (Q *ᵥ u') = 0 := by rw [comp_smul_dotProduct_mulVec_smul, hx, mul_zero]
  have heu' : (σ ∘ e) ⬝ᵥ (Q *ᵥ u') = 0 := by rw [mulVec_smul, dotProduct_smul, hex, smul_zero]
  have hu'e := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp heu'
  have htrv {v : n → K} {a : K} :=
    exists_mem_elementaryUnitaryGroup_coe_eq_unitaryTransvection (v := v) (a := a) hσ hQ
  obtain ⟨t₁, ht₁, hc₁⟩ := htrv (v := e + u')
    (by simp [map_comp_add, add_dotProduct, mulVec_add, dotProduct_add, he, hu', heu', hu'e]) hdε
  obtain ⟨t₂, ht₂, hc₂⟩ := htrv he hndε
  obtain ⟨t₃, ht₃, hc₃⟩ := htrv hu' hndε
  have hσd : σ d ≠ 0 := (map_ne_zero σ).mpr hd
  have hd_ratio : d * (σ d)⁻¹ = -ε := mul_right_cancel₀ hσd <| by
    rw [mul_assoc, inv_mul_cancel₀ hσd, mul_one]; linear_combination hdε
  refine ⟨t₁ * t₂ * t₃, mul_mem (mul_mem ht₁ ht₂) ht₃, mulVec_injective <| funext fun v ↦ ?_⟩
  set α := (σ ∘ e) ⬝ᵥ (Q *ᵥ v); set β := (σ ∘ u') ⬝ᵥ (Q *ᵥ v)
  have hv₂ : (t₂ : Matrix n n K) *ᵥ ((t₃ : Matrix n n K) *ᵥ v) =
      v + (-d * β) • u' + (-d * α) • e := by
    rw [hc₃, unitaryTransvection_mulVec, hc₂, unitaryTransvection_mulVec, mulVec_add, mulVec_smul,
      dotProduct_add, dotProduct_smul, heu', smul_zero, add_zero]
  have hpair₁ : (σ ∘ (e + u')) ⬝ᵥ (Q *ᵥ (v + (-d * β) • u' + (-d * α) • e)) = α + β := by
    simp only [comp_add_dotProduct_mulVec, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul,
      smul_eq_mul, he, hu', heu', hu'e, α, β]; ring
  rw [specialIsometryGroup_coe_mul_mulVec, specialIsometryGroup_coe_mul_mulVec, hv₂, hc₁,
    unitaryTransvection_mulVec, hpair₁,
    show v + (-d * β) • u' + (-d * α) • e + (d * (α + β)) • (e + u') =
      v + (d * β) • e + (d * α) • u' by module, siegelTransvection_mulVec]
  have h1 : d * α * d⁻¹ = α := by field_simp
  simp only [u', β, TauCeti.map_comp_smul, smul_dotProduct, smul_eq_mul, map_inv₀, smul_smul,
    zero_smul, add_zero, ← mul_assoc, h1, hd_ratio, neg_mul]; module

private theorem exists_isotropic_ne_zero_in_ortho (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0) (hε : ε * ε = 1)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0) {e f : n → K}
    (he₀ : e ≠ 0) (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0) (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε) {u w : n → K}
    (hu₀ : u ≠ 0) (hw_span : w ∉ K ∙ u) (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0)
    (hw : (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0) (huw : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) :
    ∃ u₀ : n → K, u₀ ≠ 0 ∧ (σ ∘ e) ⬝ᵥ (Q *ᵥ u₀) = 0 ∧ (σ ∘ f) ⬝ᵥ (Q *ᵥ u₀) = 0 ∧
      (σ ∘ u₀) ⬝ᵥ (Q *ᵥ u₀) = 0 := by
  obtain ⟨g, -, c, hc, hgu⟩ :=
    exists_mem_elementaryUnitaryGroup_mulVec_eq_smul hσ hQ hdet htr hadm hu₀ he₀ hu he
  have hgQ := mem_specialIsometryGroup_iff.mp g.2
  set w₁ := (g : Matrix n n K) *ᵥ w
  have hw₁ : (σ ∘ w₁) ⬝ᵥ (Q *ᵥ w₁) = 0 := by rw [comp_mulVec_dotProduct_mulVec_mulVec hgQ, hw]
  have hew₁ : (σ ∘ e) ⬝ᵥ (Q *ᵥ w₁) = 0 :=
    comp_dotProduct_mulVec_mulVec_eq_zero_of_mulVec_eq_smul hgQ hc hgu huw
  have hw₁_span : w₁ ∉ K ∙ e := fun hmem ↦ hw_span <| by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    refine Submodule.mem_span_singleton.mpr ⟨a * c⁻¹, sub_eq_zero.mp <|
      eq_zero_of_mulVec_eq_zero (M := (g : Matrix n n K)) (by simp) ?_⟩
    rw [mulVec_sub, mulVec_smul, hgu, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one, ha,
      sub_self]
  set u₀ := w₁ - (ε * ((σ ∘ f) ⬝ᵥ (Q *ᵥ w₁))) • e
  have hw₁e := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hew₁
  exact ⟨u₀, fun h0 ↦ hw₁_span <| Submodule.mem_span_singleton.mpr ⟨_, (sub_eq_zero.mp h0).symm⟩,
    by simp [u₀, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hew₁, he],
    comp_dotProduct_mulVec_sub_smul_eq_zero hε hfe w₁,
    by simp [u₀, map_comp_sub, TauCeti.map_comp_smul, sub_dotProduct, smul_dotProduct, mulVec_sub,
      mulVec_smul, dotProduct_sub, dotProduct_smul, hw₁, he, hew₁, hw₁e]⟩

/-- **A hyperbolic pair orthogonal to `(e, f)` in Witt index at least two.** Let `σ` be an
involution, let `Q` be an invertible `ε`-Hermitian matrix whose trace `t ↦ t + ε σ(t)` is onto
`{s | σ(s) = ε s}` and has a nonzero kernel element, and let `(e, f)` be isotropic vectors with
`B(e, f) = 1`. If `u` and `w` are orthogonal isotropic vectors with `u ≠ 0` and `w ∉ K ∙ u`, then
some isotropic vectors `u₀, y₀` orthogonal to both `e` and `f` satisfy `B(u₀, y₀) = 1` and
`B(y₀, u₀) = ε`. -/
theorem exists_comp_dotProduct_mulVec_eq_zero_and_eq_one_of_notMem_span
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    {e f : n → K} (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0) (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0)
    (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1) {u w : n → K} (hu₀ : u ≠ 0) (hw_span : w ∉ K ∙ u)
    (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hw : (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0)
    (huw : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) :
    ∃ u₀ y₀ : n → K, (σ ∘ e) ⬝ᵥ (Q *ᵥ u₀) = 0 ∧ (σ ∘ f) ⬝ᵥ (Q *ᵥ u₀) = 0 ∧
      (σ ∘ e) ⬝ᵥ (Q *ᵥ y₀) = 0 ∧ (σ ∘ f) ⬝ᵥ (Q *ᵥ y₀) = 0 ∧
      (σ ∘ u₀) ⬝ᵥ (Q *ᵥ u₀) = 0 ∧ (σ ∘ y₀) ⬝ᵥ (Q *ᵥ y₀) = 0 ∧
      (σ ∘ u₀) ⬝ᵥ (Q *ᵥ y₀) = 1 ∧ (σ ∘ y₀) ⬝ᵥ (Q *ᵥ u₀) = ε := by
  have he₀ : e ≠ 0 := fun h0 ↦ (one_ne_zero : (1 : K) ≠ 0) (by simpa [h0] using hef.symm)
  obtain ⟨_, -, -, -, -, hε, hσε⟩ :=
    exists_comp_dotProduct_mulVec_eq_zero_and_eq_one hσ hQ hdet htr he₀ he
  have hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε, hef, map_one, mul_one]
  obtain ⟨u₀, hu₀_ne, heu₀, hfu₀, hu₀_iso⟩ :=
    exists_isotropic_ne_zero_in_ortho hσ hQ hdet hε htr hadm he₀ he hfe hu₀ hw_span hu hw huw
  obtain ⟨z, -, -, -, hzu₀, -, -⟩ :=
    exists_comp_dotProduct_mulVec_eq_zero_and_eq_one hσ hQ hdet htr hu₀_ne hu₀_iso
  obtain ⟨z₀, hez₀, hfz₀, hz_eq⟩ :=
    exists_eq_add_and_comp_dotProduct_mulVec_eq_zero hε he hf hef hfe z
  have hz₀u₀ : (σ ∘ z₀) ⬝ᵥ (Q *ᵥ u₀) = ε := by
    rw [hz_eq] at hzu₀
    simpa [TauCeti.map_comp_smul, smul_dotProduct, heu₀, hfu₀] using hzu₀
  obtain ⟨t, hy₀⟩ := exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero hσ hQ htr hu₀_iso
    (hz₀u₀ ▸ left_ne_zero_of_mul (hε ▸ one_ne_zero))
  exact ⟨u₀, z₀ + t • u₀, heu₀, hfu₀,
    by simp [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, hez₀, heu₀],
    by simp [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, hfz₀, hfu₀], hu₀_iso, hy₀,
    by rw [comp_dotProduct_mulVec_swap hσ hQ hε]; simp [TauCeti.map_comp_smul, smul_dotProduct,
      hz₀u₀, hu₀_iso, hσε, hε],
    by simp [TauCeti.map_comp_smul, smul_dotProduct, hz₀u₀, hu₀_iso]⟩

section SiegelGen

private abbrev MemElemSiegel (Q : Matrix n n K) (σ : K →+* K) (ε : K) (e w₀ : n → K) (c : K) :
    Prop :=
  ∀ {s} (hs : s ∈ Q.specialIsometryGroup σ),
    (s : Matrix n n K) = Q.siegelTransvection σ ε e w₀ c →
    (⟨s, hs⟩ : Q.specialIsometryGroup σ) ∈ Q.elementaryUnitaryGroup σ

variable (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
  (hε : ε * ε = 1) (hσε : σ ε = ε) (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
  {d : K} (hd : d ≠ 0) (hdε : d + ε * σ d = 0) {e f : n → K} (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0)
  (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0) (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1) (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε)
  {w₀ : n → K} (hew₀ : (σ ∘ e) ⬝ᵥ (Q *ᵥ w₀) = 0)

include hσ hQ hε he hef hfe hew₀ in
private theorem admissible_of_siegelTransvection_mem {c : K} {s : Q.specialIsometryGroup σ}
    (hcs : (s : Matrix n n K) = Q.siegelTransvection σ ε e w₀ c) :
    c + ε * σ c + ε * ((σ ∘ w₀) ⬝ᵥ (Q *ᵥ w₀)) = 0 := by
  have hdef := (mem_specialIsometryGroup_iff.mp s.2).symm
  rw [hcs, transpose_map_siegelTransvection_mul_mul hσ hQ he hew₀] at hdef
  have h0 : (c + ε * σ c + ε * ((σ ∘ w₀) ⬝ᵥ (Q *ᵥ w₀))) • vecMulVec (Q *ᵥ e) ((σ ∘ e) ᵥ* Q) = 0 :=
    by simpa [add_eq_left] using hdef.symm
  exact (smul_eq_zero.mp h0).resolve_right (not_or.mpr
    ⟨fun h ↦ left_ne_zero_of_mul (hε ▸ one_ne_zero) (by simpa [h] using hfe.symm),
      fun h ↦ (one_ne_zero : (1 : K) ≠ 0) (by simpa [dotProduct_mulVec, h] using hef.symm)⟩ ∘
      vecMulVec_eq_zero.mp)

include hσ hQ hε he hef hfe hew₀ in
private theorem siegelTransvection_mem_elementary_of_exists_param {c c₀ : K}
    (hc : c + ε * σ c + ε * ((σ ∘ w₀) ⬝ᵥ (Q *ᵥ w₀)) = 0) {s₀ : Q.specialIsometryGroup σ}
    (hs₀ : s₀ ∈ Q.elementaryUnitaryGroup σ)
    (hcs₀ : (s₀ : Matrix n n K) = Q.siegelTransvection σ ε e w₀ c₀) :
    MemElemSiegel Q σ ε e w₀ c := fun {s} hs hcs ↦ by
  have hc₀ := admissible_of_siegelTransvection_mem hσ hQ hε he hef hfe hew₀ hcs₀
  obtain ⟨t₀, ht₀, hct₀⟩ := exists_mem_elementaryUnitaryGroup_coe_eq_unitaryTransvection hσ hQ he
    (a := c - c₀) (by rw [map_sub]; linear_combination hc - hc₀)
  rw [specialIsometryGroup_ext (g₁ := ⟨s, hs⟩) (g₂ := t₀ * s₀) (by
    rw [Subgroup.coe_mk (Q.specialIsometryGroup σ), Subgroup.coe_mul, SpecialLinearGroup.coe_mul,
      hcs, hct₀, hcs₀, ← siegelTransvection_zero_eq_unitaryTransvection (ε := ε),
      siegelTransvection_mul_siegelTransvection he hew₀ (by simp)]; simp)]
  exact mul_mem ht₀ hs₀

include hσ hQ hε hσε htr hd hdε he hf hef hfe hew₀ in
private theorem siegelTransvection_mem_elementary_of_fixed_ne {a : K} (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hσa : σ a = a) (hfw₀ : (σ ∘ f) ⬝ᵥ (Q *ᵥ w₀) = 0) {c : K}
    (hc : c + ε * σ c + ε * ((σ ∘ w₀) ⬝ᵥ (Q *ᵥ w₀)) = 0) :
    MemElemSiegel Q σ ε e w₀ c := fun hs hcs ↦ by
  set w' := (a - 1)⁻¹ • w₀
  have hew' : (σ ∘ e) ⬝ᵥ (Q *ᵥ w') = 0 := by simp [w', mulVec_smul, dotProduct_smul, hew₀]
  have hfw' : (σ ∘ f) ⬝ᵥ (Q *ᵥ w') = 0 := by simp [w', mulVec_smul, dotProduct_smul, hfw₀]
  have hw'e := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hew'
  obtain ⟨c', hc'⟩ := htr (-(ε * ((σ ∘ w') ⬝ᵥ (Q *ᵥ w')))) <| by
    rw [map_neg, map_mul, hσε, apply_comp_dotProduct_mulVec hσ hQ, mul_neg]
  obtain ⟨s', hs', hcs'⟩ := exists_mem_specialIsometryGroup_coe_eq_siegelTransvection hσ hQ he hew'
    (c := c') (by linear_combination hc')
  obtain ⟨h, hh, hhe, -, hhx⟩ :=
    exists_mem_elementaryUnitaryGroup_mulVec_eq_smul_and_inv_smul_and_eq_self
      hσ hQ hε ⟨d, hd, hdε⟩ he hf hef ha0 hσa
  let s₁ : Q.specialIsometryGroup σ := ⟨s', hs'⟩
  have hcs₁ : (s₁ : Matrix n n K) = Q.siegelTransvection σ ε e w' c' := by simpa [s₁] using hcs'
  have hconj : (↑(h * s₁ * h⁻¹) : Matrix n n K) =
      Q.siegelTransvection σ ε e (a • w') (c' * a * a) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul,
      Subgroup.coe_inv, hcs₁, coe_mul_siegelTransvection_mul_coe_inv h.2, hhe, hhx w' hew' hfw',
      siegelTransvection_smul_left hσ, hσa]
  have hw_sum : a • w' + -w' = w₀ := by
    rw [show a • w' + -w' = (a - 1) • w' by module, smul_inv_smul₀ (sub_ne_zero.mpr ha1)]
  have hcs₂ : (↑((h * s₁ * h⁻¹) * s₁⁻¹) : Matrix n n K) = Q.siegelTransvection σ ε e w₀
      (c' * a * a + (-c' - ε * ((σ ∘ w') ⬝ᵥ (Q *ᵥ w'))) -
        ε * ((σ ∘ (a • w')) ⬝ᵥ (Q *ᵥ (-w')))) := by
    rw [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, hconj,
      coe_inv_specialIsometryGroup_eq_siegelTransvection he hew' hw'e hcs₁,
      siegelTransvection_mul_siegelTransvection he (by simp [mulVec_neg, hew'])
        (by simp [TauCeti.map_comp_smul, hw'e]), hw_sum]
  exact siegelTransvection_mem_elementary_of_exists_param hσ hQ hε he hef hfe hew₀ hc
    ((show (h * s₁ * h⁻¹) * s₁⁻¹ = h * (s₁ * h⁻¹ * s₁⁻¹) by group) ▸
      mul_mem hh (normal_elementaryUnitaryGroup.conj_mem _ (inv_mem hh) s₁)) hcs₂ hs hcs

include hε he hf hef hfe hew₀ in
private theorem siegelTransvection_mem_elementary_of_card_le_two (hcard : Fintype.card n ≤ 2)
    (hfw₀ : (σ ∘ f) ⬝ᵥ (Q *ᵥ w₀) = 0) {c : K} : MemElemSiegel Q σ ε e w₀ c := fun hs hcs ↦ by
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
      intro i
      fin_cases i <;> [exact hg0; exact hg1; exact (smul_eq_zero.mp hg2).resolve_right hw₀_ne]
    have hle := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at hle; omega
  exact unitaryTransvection_mem_elementaryUnitaryGroup hs he
    (by rwa [hw₀, siegelTransvection_zero_eq_unitaryTransvection] at hcs)

include hσ hQ hdet hε htr hd hdε he hf hef hfe hew₀ in
private theorem siegelTransvection_mem_elementary_of_witt_two {u w : n → K} (hu₀ : u ≠ 0)
    (hw_span : w ∉ K ∙ u) (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hw : (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0)
    (huw : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) {c : K}
    (hc : c + ε * σ c + ε * ((σ ∘ w₀) ⬝ᵥ (Q *ᵥ w₀)) = 0) :
    MemElemSiegel Q σ ε e w₀ c := fun hs hcs ↦ by
  classical
  obtain ⟨u₀, y₀, heu₀, -, hey₀, -, hu₀_iso, hy₀_iso, -, hy₀u₀⟩ :=
    exists_comp_dotProduct_mulVec_eq_zero_and_eq_one_of_notMem_span hσ hQ hdet htr ⟨d, hd, hdε⟩
      he hf hef hu₀ hw_span hu hw huw
  let y' : n → K := if (σ ∘ w₀) ⬝ᵥ (Q *ᵥ u₀) = 0 then y₀ else 0
  have hy'_iso : (σ ∘ y') ⬝ᵥ (Q *ᵥ y') = 0 := by dsimp [y']; split_ifs <;> simp [hy₀_iso]
  have hey' : (σ ∘ e) ⬝ᵥ (Q *ᵥ y') = 0 := by dsimp [y']; split_ifs <;> simp [hey₀]
  have hwy' : (σ ∘ (w₀ + y')) ⬝ᵥ (Q *ᵥ u₀) ≠ 0 := by
    dsimp [y']; split_ifs with h0
    · rw [comp_add_dotProduct_mulVec, h0, zero_add, hy₀u₀]
      exact left_ne_zero_of_mul (hε ▸ one_ne_zero)
    · simpa using h0
  obtain ⟨t, ht⟩ := exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero hσ hQ htr hu₀_iso hwy'
  set x₁ := w₀ + y' + t • u₀; set x₂ := (-t) • u₀; set x₃ := -y'
  have hex₁ : (σ ∘ e) ⬝ᵥ (Q *ᵥ x₁) = 0 := by
    simp [x₁, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, hew₀, hey', heu₀]
  have hex₂ : (σ ∘ e) ⬝ᵥ (Q *ᵥ x₂) = 0 := by rw [mulVec_smul, dotProduct_smul, heu₀, smul_zero]
  have hex₃ : (σ ∘ e) ⬝ᵥ (Q *ᵥ x₃) = 0 := by simp [x₃, mulVec_neg, hey']
  have hs0 {x : n → K} :=
    exists_mem_elementaryUnitaryGroup_siegelTransvection_zero_of_isotropic (x := x) hσ hQ hd hdε he
  obtain ⟨t₁, ht₁, hc₁⟩ := hs0 ht hex₁
  obtain ⟨t₂, ht₂, hc₂⟩ := hs0 (by rw [comp_smul_dotProduct_mulVec_smul, hu₀_iso, mul_zero]) hex₂
  obtain ⟨t₃, ht₃, hc₃⟩ := hs0 (by simp [x₃, map_comp_neg, mulVec_neg, hy'_iso]) hex₃
  have hx₁e := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hex₁
  have hx₂e := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hex₂
  have hcs₀ : (↑(t₁ * t₂ * t₃) : Matrix n n K) = Q.siegelTransvection σ ε e w₀
      (0 + 0 - ε * ((σ ∘ x₁) ⬝ᵥ (Q *ᵥ x₂)) + 0 - ε * ((σ ∘ (x₁ + x₂)) ⬝ᵥ (Q *ᵥ x₃))) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul,
      hc₁, hc₂, hc₃, siegelTransvection_mul_siegelTransvection he hex₂ hx₁e,
      siegelTransvection_mul_siegelTransvection he hex₃
        (by rw [comp_add_dotProduct_mulVec, hx₁e, hx₂e, add_zero]),
      show x₁ + x₂ + x₃ = w₀ by dsimp [x₁, x₂, x₃]; module]
  exact siegelTransvection_mem_elementary_of_exists_param hσ hQ hε he hef hfe hew₀ hc
    (mul_mem (mul_mem ht₁ ht₂) ht₃) hcs₀ hs hcs

end SiegelGen

/-- **Every Siegel transformation in `Q.specialIsometryGroup σ` lies in the elementary unitary
group.** Let `σ` be an involution, let `Q` be an invertible `ε`-Hermitian matrix whose trace
`t ↦ t + ε σ(t)` is onto `{s | σ(s) = ε s}` and has a nonzero kernel element, and suppose either
`σ` fixes a scalar outside `{0, 1}`, `Fintype.card n ≤ 2`, or `Q` admits two linearly independent
orthogonal isotropic vectors. Then any `s ∈ Q.specialIsometryGroup σ` of the form
`Q.siegelTransvection σ ε u w c` with `u` isotropic and `B(u, w) = 0` belongs to
`Q.elementaryUnitaryGroup σ`. -/
theorem siegelTransvection_mem_elementaryUnitaryGroup
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    (hgen : (∃ a : K, a ≠ 0 ∧ a ≠ 1 ∧ σ a = a) ∨ Fintype.card n ≤ 2 ∨
      ∃ u w : n → K, u ≠ 0 ∧ w ∉ K ∙ u ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 ∧
        (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0)
    {u w : n → K} (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (huw : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0)
    {c : K} {s : SpecialLinearGroup n K} (hs : s ∈ Q.specialIsometryGroup σ)
    (hcs : (s : Matrix n n K) = Q.siegelTransvection σ ε u w c) :
    (⟨s, hs⟩ : Q.specialIsometryGroup σ) ∈ Q.elementaryUnitaryGroup σ := by
  by_cases hu0 : u = 0
  · rw [specialIsometryGroup_ext (g₁ := ⟨s, hs⟩) (g₂ := 1) (by simp [hu0, hcs])]; exact one_mem _
  obtain ⟨d, hd, hdε⟩ := hadm
  obtain ⟨f, -, hf, huf, hfu, hε, hσε⟩ :=
    exists_comp_dotProduct_mulVec_eq_zero_and_eq_one hσ hQ hdet htr hu0 hu
  have hc := admissible_of_siegelTransvection_mem hσ hQ hε hu huf hfu huw (s := ⟨s, hs⟩)
    (by rwa [Subgroup.coe_mk (Q.specialIsometryGroup σ)])
  set α := ε * ((σ ∘ f) ⬝ᵥ (Q *ᵥ w)); set w₀ := w - α • u; set c₀ := c + α - ε * σ α
  have huw₀ : (σ ∘ u) ⬝ᵥ (Q *ᵥ w₀) = 0 := by
    simp [w₀, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, huw, hu]
  have hfw₀ : (σ ∘ f) ⬝ᵥ (Q *ᵥ w₀) = 0 := comp_dotProduct_mulVec_sub_smul_eq_zero hε hfu w
  have hcs₀ : (s : Matrix n n K) = Q.siegelTransvection σ ε u w₀ c₀ := by
    rw [hcs, ← sub_add_cancel w (α • u), siegelTransvection_add_smul]
  have hw₀w₀ : (σ ∘ w₀) ⬝ᵥ (Q *ᵥ w₀) = (σ ∘ w) ⬝ᵥ (Q *ᵥ w) := by
    have hwu := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp huw
    simp [w₀, map_comp_sub, TauCeti.map_comp_smul, sub_dotProduct, smul_dotProduct, mulVec_sub,
      mulVec_smul, dotProduct_sub, dotProduct_smul, hu, huw, hwu]
  have hc₀ : c₀ + ε * σ c₀ + ε * ((σ ∘ w₀) ⬝ᵥ (Q *ᵥ w₀)) = 0 := by
    rw [hw₀w₀]; simp only [c₀, map_add, map_sub, map_mul, hσε, hσ α]; linear_combination hc - α * hε
  rcases hgen with ⟨a, ha0, ha1, hσa⟩ | hcard | ⟨u₁, w₁, hu₁0, hw₁s, hu₁, hw₁, hu₁w₁⟩
  · exact siegelTransvection_mem_elementary_of_fixed_ne hσ hQ hε hσε htr hd hdε hu hf huf hfu huw₀
      ha0 ha1 hσa hfw₀ hc₀ hs hcs₀
  · exact siegelTransvection_mem_elementary_of_card_le_two hε hu hf huf hfu huw₀ hcard hfw₀ hs hcs₀
  · exact siegelTransvection_mem_elementary_of_witt_two hσ hQ hdet hε htr hd hdε hu hf huf hfu huw₀
      hu₁0 hw₁s hu₁ hw₁ hu₁w₁ hc₀ hs hcs₀

end Matrix

end
