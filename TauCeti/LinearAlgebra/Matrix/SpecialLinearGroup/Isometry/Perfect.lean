/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Iwasawa
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.Algebra.Group.Hom.Defs
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Perfectness of special unitary groups

This file proves that `Matrix.specialIsometryGroup Q σ` is perfect whenever the fixed field of `σ`
contains a nonzero `c` with `c ^ 2 ≠ 1`, or the form has Witt index at least two, or
`3 ≤ Fintype.card n` and some nonzero `c : K` satisfies `c * σ c ≠ 1`.

## Main results

* `Matrix.commutator_specialIsometryGroup_eq_top`: perfectness of `Matrix.specialIsometryGroup Q σ`.

## References

* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Theorem 11.28.
-/

public section

open scoped LinearAlgebra.Projectivization Pointwise commutatorElement

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] {Q : Matrix n n K} {σ : K →+* K}
  {ε : K}
private theorem coe_inv_unitaryTransvection {t : Q.specialIsometryGroup σ} {e : n → K} {b : K}
    (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0) (hct : (t : Matrix n n K) = Q.unitaryTransvection σ e b) :
    ((t⁻¹ : Q.specialIsometryGroup σ) : Matrix n n K) = Q.unitaryTransvection σ e (-b) := by
  have h1 : (t : Matrix n n K) * Q.unitaryTransvection σ e (-b) = 1 := by
    rw [hct, unitaryTransvection_mul_unitaryTransvection he, add_neg_cancel,
      unitaryTransvection_zero]
  have h2 : (t : Matrix n n K) * ((t⁻¹ : Q.specialIsometryGroup σ) : Matrix n n K) = 1 := by
    rw [← SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      SpecialLinearGroup.coe_one]
  exact (inv_eq_right_inv h2).symm.trans (inv_eq_right_inv h1)
private theorem coe_inv_siegelTransvection_zero {s : Q.specialIsometryGroup σ} {e w : n → K}
    (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0) (hew : (σ ∘ e) ⬝ᵥ (Q *ᵥ w) = 0) (hwe : (σ ∘ w) ⬝ᵥ (Q *ᵥ e) = 0)
    (hw : (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0) (hcs : (s : Matrix n n K) = Q.siegelTransvection σ ε e w 0) :
    ((s⁻¹ : Q.specialIsometryGroup σ) : Matrix n n K) = Q.siegelTransvection σ ε e (-w) 0 := by
  have h1 := siegelTransvection_mul_siegelTransvection_neg_eq_one (ε := ε) he hew hwe 0
  rw [← hcs, hw, mul_zero, neg_zero, sub_zero] at h1
  have h2 : (s : Matrix n n K) * ((s⁻¹ : Q.specialIsometryGroup σ) : Matrix n n K) = 1 := by
    rw [← SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      SpecialLinearGroup.coe_one]
  exact (inv_eq_right_inv h2).symm.trans (inv_eq_right_inv h1)
omit [DecidableEq n] in
private theorem transpose_map_mul_mul_eq_self {A : Matrix n n K}
    (h : ∀ x y : n → K, (σ ∘ (A *ᵥ x)) ⬝ᵥ (Q *ᵥ (A *ᵥ y)) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y)) :
    (A.map σ)ᵀ * Q * A = Q := by
  classical
  exact mulVec_injective (funext fun y ↦ funext fun i ↦ by
    have hi := h (Pi.single i 1) y
    rw [(funext (σ.map_mulVec A _) : σ ∘ (A *ᵥ _) = _), ← vecMul_transpose, dotProduct_mulVec,
      dotProduct_mulVec, vecMul_vecMul, vecMul_vecMul, ← Matrix.mul_assoc,
      ← dotProduct_mulVec] at hi
    have hs : σ ∘ Pi.single i (1 : K) = Pi.single i 1 := funext fun j ↦ by
      by_cases hij : j = i <;> simp [hij]
    simpa [hs] using hi)
section Helpers

variable (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
  (hε : ε * ε = 1) (hσε : σ ε = ε) (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
  (hadm : ∃ d ≠ 0, d + ε * σ d = 0) {e f : n → K} (he₀ : e ≠ 0) (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0)
  (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0) (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1) (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε)
include hσ hQ he in
private theorem unitaryTransvection_mem_commutator_of_mulVec_eq_smul {g : Q.specialIsometryGroup σ}
    {c : K} (hc1 : c * σ c ≠ 1) (hge : (g : Matrix n n K) *ᵥ e = c • e) {a : K}
    (ha : a + ε * σ a = 0) :
    ∃ t ∈ commutator (Q.specialIsometryGroup σ),
      (t : Matrix n n K) = Q.unitaryTransvection σ e a := by
  have hsub : c * σ c - 1 ≠ 0 := sub_ne_zero.mpr hc1; set b := a * (c * σ c - 1)⁻¹
  have hb : b + ε * σ b = 0 := by
    simp only [b, map_mul, map_inv₀, map_sub, hσ c, map_one, mul_comm (σ c) c]
    linear_combination (c * σ c - 1)⁻¹ * ha
  obtain ⟨tb, htb, hctb⟩ := exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ he hb
  let t₀ : Q.specialIsometryGroup σ := ⟨tb, htb⟩
  have hct₀ : (t₀ : Matrix n n K) = Q.unitaryTransvection σ e b := hctb
  refine ⟨⁅g, t₀⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _), ?_⟩
  rw [commutatorElement_def, Subgroup.coe_mul, SpecialLinearGroup.coe_mul,
    coe_inv_unitaryTransvection he hct₀, Subgroup.coe_mul, Subgroup.coe_mul,
    SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, Subgroup.coe_inv, hct₀,
    coe_mul_unitaryTransvection_mul_coe_inv g.2, hge, unitaryTransvection_smul,
    unitaryTransvection_mul_unitaryTransvection he]
  congr 1; simp only [b]; field_simp; ring
include hσ hQ hdet hε htr hadm he₀ he hf hef hfe in
private theorem unitaryTransvection_mem_commutator_of_witt_two {u w : n → K} (hu₀ : u ≠ 0)
    (hw_span : w ∉ K ∙ u) (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hw : (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0)
    (huw : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) {a : K} (ha : a + ε * σ a = 0) :
    ∃ t ∈ commutator (Q.specialIsometryGroup σ),
      (t : Matrix n n K) = Q.unitaryTransvection σ e a := by
  obtain ⟨u₀, y₀, heu₀, -, hey₀, -, hu₀, hy₀, hu₀y₀, hy₀u₀⟩ :=
    exists_hyperbolic_pair_in_ortho hσ hQ hdet hε htr hadm he₀ he hf hef hfe hu₀ hw_span hu hw huw
  obtain ⟨b, hb⟩ : ∃ b : K, b - ε * σ b = a := by
    by_cases h2 : (2 : K) = 0
    · obtain ⟨b, hb⟩ := htr a (by linear_combination ε * ha - σ a * hε - (ε * a) * h2)
      exact ⟨b, by linear_combination hb - (ε * σ b) * h2⟩
    · exact ⟨2⁻¹ * a, by rw [map_mul, map_inv₀, map_ofNat]; field_simp; linear_combination -ha⟩
  set w₁ := b • u₀
  have hw₁ : (σ ∘ w₁) ⬝ᵥ (Q *ᵥ w₁) = 0 := by rw [comp_smul_dotProduct_mulVec_smul, hu₀, mul_zero]
  have hew₁ : (σ ∘ e) ⬝ᵥ (Q *ᵥ w₁) = 0 := by rw [mulVec_smul, dotProduct_smul, heu₀, smul_zero]
  have hw₁e := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hew₁
  have hy₀e := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hey₀
  obtain ⟨s₁, hs₁, hcs₁⟩ := exists_mem_specialIsometryGroup_coe_eq_siegelTransvection hσ hQ he hew₁
    (c := 0) (by simp [hw₁])
  obtain ⟨s₂, hs₂, hcs₂⟩ := exists_mem_specialIsometryGroup_coe_eq_siegelTransvection hσ hQ he hey₀
    (c := 0) (by simp [hy₀])
  let g₁ : Q.specialIsometryGroup σ := ⟨s₁, hs₁⟩; let g₂ : Q.specialIsometryGroup σ := ⟨s₂, hs₂⟩
  have hcs₁' : (g₁ : Matrix n n K) = Q.siegelTransvection σ ε e w₁ 0 := hcs₁
  have hcs₂' : (g₂ : Matrix n n K) = Q.siegelTransvection σ ε e y₀ 0 := hcs₂
  refine ⟨⁅g₁, g₂⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _),
    ?_⟩
  rw [commutatorElement_def, Subgroup.coe_mul, SpecialLinearGroup.coe_mul,
    coe_inv_siegelTransvection_zero (ε := ε) he hey₀ hy₀e hy₀ hcs₂', Subgroup.coe_mul,
    SpecialLinearGroup.coe_mul, coe_inv_siegelTransvection_zero (ε := ε) he hew₁ hw₁e hw₁ hcs₁',
    Subgroup.coe_mul, SpecialLinearGroup.coe_mul, hcs₁', hcs₂',
    siegelTransvection_mul_siegelTransvection he hey₀ hw₁e,
    siegelTransvection_mul_siegelTransvection he (by simp [mulVec_neg, hew₁]) (by simp [hw₁e,
      hy₀e]),
    siegelTransvection_mul_siegelTransvection he (by simp [mulVec_neg, hey₀]) (by simp [hy₀e])]
  have hw_zero : w₁ + y₀ + -w₁ + -y₀ = 0 := by abel
  rw [hw_zero, siegelTransvection_zero_eq_unitaryTransvection]; congr 1
  simp only [w₁, map_comp_add, map_comp_neg, TauCeti.map_comp_smul, add_dotProduct, neg_dotProduct,
    smul_dotProduct, mulVec_neg, mulVec_smul, dotProduct_neg, dotProduct_smul, smul_eq_mul, hu₀,
    hy₀, hu₀y₀, hy₀u₀]
  linear_combination b * hε + hb
include hσ hQ hε hσε he hf hef hfe in
private theorem exists_mem_specialIsometryGroup_mulVec_eq_smul_of_anisotropic {v : n → K}
    (hev : (σ ∘ e) ⬝ᵥ (Q *ᵥ v) = 0) (hvv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) ≠ 0) {c : K} (hc : c ≠ 0) :
    ∃ g : Q.specialIsometryGroup σ, (g : Matrix n n K) *ᵥ e = c • e := by
  have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
  have hve := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hev
  let M₁ : Matrix n n K := 1 + ((c - 1) * ε) • vecMulVec e ((σ ∘ f) ᵥ* Q) +
    ((σ c)⁻¹ - 1) • vecMulVec f ((σ ∘ e) ᵥ* Q)
  let M₂ : Matrix n n K := Q.unitaryTransvection σ v ((σ c * c⁻¹ - 1) * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v))⁻¹)
  have hM₁x (x : n → K) : M₁ *ᵥ x = x + (((c - 1) * ε) * ((σ ∘ f) ⬝ᵥ (Q *ᵥ x))) • e +
      (((σ c)⁻¹ - 1) * ((σ ∘ e) ⬝ᵥ (Q *ᵥ x))) • f := by
    simp [M₁, add_mulVec, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec, smul_smul]
  have hM₁e : M₁ *ᵥ e = c • e := by
    rw [hM₁x, hfe, he, mul_zero, zero_smul, add_zero, mul_assoc, hε, mul_one]; module
  have hd₁ : M₁.det = c * (σ c)⁻¹ := det_eq_of_mulVec_hyperbolic hε he hf hef hfe hM₁e
    (by rw [hM₁x, hf, hef, mul_zero, zero_smul, add_zero, mul_one]; module)
    fun w hew hfw ↦ by simp [hM₁x, hew, hfw]
  have hd₂ : M₂.det = σ c * c⁻¹ := by
    have heq : M₂ = 1 - vecMulVec (-(((σ c * c⁻¹ - 1) * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v))⁻¹)) • v)
        ((σ ∘ v) ᵥ* Q) := by simp [M₂, unitaryTransvection_def, sub_eq_add_neg, smul_vecMulVec]
    rw [heq, TauCeti.det_one_sub_vecMulVec, dotProduct_smul, ← dotProduct_mulVec, smul_eq_mul]
    field_simp; ring
  have hB₁ (x y : n → K) : (σ ∘ (M₁ *ᵥ x)) ⬝ᵥ (Q *ᵥ (M₁ *ᵥ y)) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y) := by
    rw [hM₁x x, hM₁x y]
    simp only [map_comp_add, TauCeti.map_comp_smul, map_mul, map_sub, map_inv₀, map_one, hσ c, hσε,
      apply_comp_dotProduct_mulVec hσ hQ, add_dotProduct, smul_dotProduct, mulVec_add, mulVec_smul,
      dotProduct_add, dotProduct_smul, smul_eq_mul, he, hf, hef, hfe]
    rcases mul_self_eq_one_iff.mp hε with rfl | rfl <;> (field_simp; ring)
  have hB₂ (x y : n → K) : (σ ∘ (M₂ *ᵥ x)) ⬝ᵥ (Q *ᵥ (M₂ *ᵥ y)) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y) := by
    have hσv := apply_comp_dotProduct_mulVec hσ hQ v v
    rw [unitaryTransvection_mulVec, unitaryTransvection_mulVec]
    simp only [map_comp_add, TauCeti.map_comp_smul, map_mul, map_sub, map_inv₀, map_one, hσ c, hσv,
      apply_comp_dotProduct_mulVec hσ hQ v x, add_dotProduct, smul_dotProduct, mulVec_add,
      mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul]
    rcases mul_self_eq_one_iff.mp hε with rfl | rfl <;> (field_simp; ring)
  refine ⟨⟨⟨M₁ * M₂, by rw [det_mul, hd₁, hd₂]; field_simp⟩,
    mem_specialIsometryGroup_iff.mpr (transpose_map_mul_mul_eq_self fun x y ↦ by
      rw [← mulVec_mulVec, ← mulVec_mulVec, hB₁, hB₂])⟩, ?_⟩
  change (M₁ * M₂) *ᵥ e = c • e
  rwa [← mulVec_mulVec, unitaryTransvection_mulVec, hve, mul_zero, zero_smul, add_zero]
include hσ hQ hdet hε hσε htr hadm he₀ he hf hef hfe in
private theorem unitaryTransvection_mem_commutator_of_card_three_le (hcard : 3 ≤ Fintype.card n)
    {c : K} (hc : c ≠ 0) (hc1 : c * σ c ≠ 1) {a : K} (ha : a + ε * σ a = 0) :
    ∃ t ∈ commutator (Q.specialIsometryGroup σ),
      (t : Matrix n n K) = Q.unitaryTransvection σ e a := by
  let φ : (n → K) →ₗ[K] K × K := (toBilin' Q (σ ∘ e)).prod (toBilin' Q (σ ∘ f))
  have hrk := LinearMap.finrank_range_add_finrank_ker φ
  have hle : Module.finrank K (LinearMap.range φ) ≤ 2 := by
    have h := Submodule.finrank_le (LinearMap.range φ)
    rwa [Module.finrank_prod, Module.finrank_self] at h
  rw [Module.finrank_fintype_fun_eq_card] at hrk
  obtain ⟨v, hv_mem, hv0⟩ := (Submodule.ne_bot_iff (LinearMap.ker φ)).mp fun hbot ↦ by
    rw [hbot, finrank_bot] at hrk; omega
  have hφv : (σ ∘ e) ⬝ᵥ (Q *ᵥ v) = 0 ∧ (σ ∘ f) ⬝ᵥ (Q *ᵥ v) = 0 := by
    simpa [φ, LinearMap.mem_ker, Prod.ext_iff, toBilin'_apply'] using hv_mem
  by_cases hvv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0
  · have hv_span : v ∉ K ∙ e := fun hmem ↦ hv0 <| by
      obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp hmem
      have h0 : α * ε = 0 := by simpa [mulVec_smul, dotProduct_smul, hfe] using hφv.2
      simp [(mul_eq_zero.mp h0).resolve_right (left_ne_zero_of_mul (hε ▸ one_ne_zero))]
    exact unitaryTransvection_mem_commutator_of_witt_two hσ hQ hdet hε htr hadm he₀ he hf hef hfe
      he₀ hv_span he hvv hφv.1 ha
  · obtain ⟨g, hge⟩ := exists_mem_specialIsometryGroup_mulVec_eq_smul_of_anisotropic hσ hQ hε hσε
      he hf hef hfe hφv.1 hvv hc
    exact unitaryTransvection_mem_commutator_of_mulVec_eq_smul hσ hQ he hc1 hge ha
end Helpers
/-- **Perfectness of a special unitary group.** Let `σ` be an involution of `K`, let `Q` be an
invertible `ε`-Hermitian matrix whose trace `t ↦ t + ε σ(t)` is onto `{s | σ(s) = ε s}` and has a
nonzero kernel element, and suppose `Q.isotropicPoints σ` is nonempty. If the fixed field of `σ`
contains a nonzero element whose square is not `1`, or the form has Witt index at least two, or
`3 ≤ Fintype.card n` and some nonzero `c : K` satisfies `c * σ c ≠ 1`, then
`Q.specialIsometryGroup σ` is perfect. -/
theorem commutator_specialIsometryGroup_eq_top (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0) (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0) [Nonempty (Q.isotropicPoints σ)]
    (hperf : (∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1 ∧ σ c = c) ∨
      (∃ u w : n → K, u ≠ 0 ∧ w ∉ K ∙ u ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 ∧
        (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) ∨
      (3 ≤ Fintype.card n ∧ ∃ c : K, c ≠ 0 ∧ c * σ c ≠ 1)) :
    commutator (Q.specialIsometryGroup σ) = ⊤ := by
  obtain ⟨e, f, he₀, -, he, hf, hef, hfe, hε, hσε⟩ :=
    exists_hyperbolic_pair_of_isotropicPoints hσ hQ hdet htr
  obtain ⟨d, hd, hdε⟩ := hadm
  have hgen : (∃ a : K, a ≠ 0 ∧ a ≠ 1 ∧ σ a = a) ∨ Fintype.card n ≤ 2 ∨
      ∃ u w : n → K, u ≠ 0 ∧ w ∉ K ∙ u ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 ∧
        (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0 := by
    rcases hperf with ⟨c, hc0, hcsq, hσc⟩ | hwitt | ⟨_, c, hc0, hc1⟩
    · exact Or.inl ⟨c, hc0, fun h1 ↦ hcsq (by simp [h1]), hσc⟩
    · exact Or.inr (Or.inr hwitt)
    · exact Or.inl ⟨c * σ c, mul_ne_zero hc0 ((map_ne_zero σ).mpr hc0), hc1,
        by rw [map_mul, hσ c, mul_comm]⟩
  have hmem (a : K) (ha : a + ε * σ a = 0) : ∃ t ∈ commutator (Q.specialIsometryGroup σ),
      (t : Matrix n n K) = Q.unitaryTransvection σ e a := by
    rcases hperf with ⟨c, hc0, hcsq, hσc⟩ | ⟨u, w, hu0, hws, hu, hw, huw⟩ | ⟨hcard, c, hc0, hc1⟩
    · obtain ⟨h, -, hhe, -, -⟩ :=
        exists_mem_iSup_unitaryTransvectionSubgroup_hyperbolic_rescale hσ hQ hε hσε hd hdε he hf
          hef hfe hc0 hσc
      exact unitaryTransvection_mem_commutator_of_mulVec_eq_smul hσ hQ he
        (by rwa [hσc, ← sq]) hhe ha
    · exact unitaryTransvection_mem_commutator_of_witt_two hσ hQ hdet hε htr ⟨d, hd, hdε⟩ he₀ he hf
        hef hfe hu0 hws hu hw huw ha
    · exact unitaryTransvection_mem_commutator_of_card_three_le hσ hQ hdet hε hσε htr ⟨d, hd, hdε⟩
        he₀ he hf hef hfe hcard hc0 hc1 ha
  let p₀ : Q.isotropicPoints σ :=
    ⟨Projectivization.mk K e he₀, (mk_mem_isotropicPoints_iff he₀).mpr he⟩
  have hp₀ : Q.unitaryTransvectionSubgroup σ p₀ ≤ commutator (Q.specialIsometryGroup σ) := by
    intro g hg; obtain ⟨a, hga⟩ := (mem_unitaryTransvectionSubgroup_mk_iff he₀ p₀.2).mp hg
    have hiso := (comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g.2) f
      f).trans hf
    rw [hga, unitaryTransvection_mulVec, hef, mul_one] at hiso
    simp only [map_comp_add, TauCeti.map_comp_smul, add_dotProduct, smul_dotProduct, mulVec_add,
      mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, hf, hef, hfe, he] at hiso
    obtain ⟨t, ht_comm, hct⟩ := hmem a (by linear_combination ε * hiso - a * hε)
    rwa [show g = t from Subtype.ext (Subtype.ext (hga.trans hct.symm))]
  have := isPretransitive_isotropicPoints hσ hQ hdet htr ⟨d, hd, hdε⟩
  rw [eq_top_iff, ← iSup_unitaryTransvectionSubgroup hσ hQ hdet htr ⟨d, hd, hdε⟩ hgen, iSup_le_iff]
  intro p; obtain ⟨k, rfl⟩ := MulAction.exists_smul_eq (Q.specialIsometryGroup σ) p₀ p
  rw [unitaryTransvectionSubgroup_smul]
  intro x hx; rw [Subgroup.mem_smul_pointwise_iff_exists] at hx; obtain ⟨g, hg, rfl⟩ := hx
  simpa [MulAut.smul_def, MulAut.conj_apply] using
    (inferInstance : (commutator _).Normal).conj_mem _ (hp₀ hg) k
end Matrix

end
