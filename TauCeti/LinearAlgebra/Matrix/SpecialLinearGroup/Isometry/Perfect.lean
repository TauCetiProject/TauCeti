/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Iwasawa
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Group.Hom.Defs
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.Matrix.Nondegenerate
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.IsotropicPoints
import TauCeti.Logic.Function.Basic

/-!
# Perfectness of special unitary groups

For involutive `σ` on `K` and invertible `ε`-Hermitian `Q` with surjective `ε`-trace, nonzero
skew-trace, and nonempty `Matrix.isotropicPoints Q σ`, we prove `Matrix.specialIsometryGroup Q σ`
perfect (`Matrix.commutator_specialIsometryGroup_eq_top`) when `σ` fixes `c ≠ 0` with `c ^ 2 ≠ 1`,
Witt index is at least two, or `3 ≤ Fintype.card n` and `∃ c ≠ 0, c * σ c ≠ 1`. Each of these three
cases yields a `σ`-fixed scalar outside `{0, 1}`, `Fintype.card n ≤ 2`, or Witt index at least two
(`Matrix.exists_ne_one_and_apply_eq_self_or_card_le_two_or_exists_notMem_span`), which with the
remaining hypotheses gives transvection generation via `Matrix.iSup_unitaryTransvectionSubgroup`.

## References

* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapter 10 (§10.4, Theorem 10.20).
* L. C. Grove, *Classical Groups and Geometric Algebra* (2002), Chapter 11.
-/

public section

open scoped LinearAlgebra.Projectivization Pointwise commutatorElement

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] {Q : Matrix n n K} {σ : K →+* K}
  {ε : K}

section Helpers

private abbrev MemCommTransv (Q : Matrix n n K) (σ : K →+* K) (e : n → K) (a : K) : Prop :=
  ∃ t ∈ commutator (Q.specialIsometryGroup σ), (t : Matrix n n K) = Q.unitaryTransvection σ e a

variable (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
  (hε : ε * ε = 1) (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
  {e f : n → K} (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0) (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0)
  (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1) (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε)

include hσ hQ he in
private theorem unitaryTransvection_mem_commutator_of_mulVec_eq_smul {g : Q.specialIsometryGroup σ}
    {c : K} (hc1 : c * σ c ≠ 1) (hge : (g : Matrix n n K) *ᵥ e = c • e) {a : K}
    (ha : a + ε * σ a = 0) : MemCommTransv Q σ e a := by
  have hsub := sub_ne_zero.mpr hc1; set b := a * (c * σ c - 1)⁻¹
  obtain ⟨tb, htb, hctb⟩ := exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ he
    (a := b) (by simp only [b, map_mul, map_inv₀, map_sub, hσ c, map_one, mul_comm (σ c) c]
                 linear_combination (c * σ c - 1)⁻¹ * ha)
  let t₀ : Q.specialIsometryGroup σ := ⟨tb, htb⟩
  refine ⟨⁅g, t₀⁆, Subgroup.commutator_mem_commutator (by simp) (by simp), ?_⟩
  rw [coe_commutatorElement_eq_unitaryTransvection_of_mulVec_eq_smul he hge hctb]
  simp only [b, inv_mul_cancel_right₀ hsub]

include hσ hQ hdet hε htr he hf hef in
private theorem unitaryTransvection_mem_commutator_of_witt_two {u w : n → K} (hu₀ : u ≠ 0)
    (hw_span : w ∉ K ∙ u) (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hw : (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0)
    (huw : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) {a : K} (ha : a + ε * σ a = 0) : MemCommTransv Q σ e a := by
  obtain ⟨u₀, y₀, heu₀, -, hey₀, -, hu₀, hy₀, hu₀y₀, hy₀u₀⟩ :=
    exists_comp_dotProduct_mulVec_eq_zero_and_eq_one_of_notMem_span hσ hQ hdet htr he hf hef hu₀
      hw_span hu hw huw
  obtain ⟨b, hb⟩ : ∃ b : K, b - ε * σ b = a := by
    by_cases h2 : (2 : K) = 0
    · obtain ⟨b, hb⟩ := htr a (by linear_combination ε * ha - σ a * hε - (ε * a) * h2)
      exact ⟨b, by linear_combination hb - (ε * σ b) * h2⟩
    · exact ⟨2⁻¹ * a, by rw [map_mul, map_inv₀, map_ofNat]; field_simp; linear_combination -ha⟩
  set w₁ := b • u₀
  have hew₁ : (σ ∘ e) ⬝ᵥ (Q *ᵥ w₁) = 0 := by rw [mulVec_smul, dotProduct_smul, heu₀, smul_zero]
  have hw₁e := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hew₁
  have hy₀e := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hey₀
  obtain ⟨s₁, hs₁, hcs₁⟩ := exists_mem_specialIsometryGroup_coe_eq_siegelTransvection hσ hQ he hew₁
    (c := 0) (by simp [w₁, mulVec_smul, hu₀])
  obtain ⟨s₂, hs₂, hcs₂⟩ := exists_mem_specialIsometryGroup_coe_eq_siegelTransvection hσ hQ he hey₀
    (c := 0) (by simp [hy₀])
  let g₁ : Q.specialIsometryGroup σ := ⟨s₁, hs₁⟩; let g₂ : Q.specialIsometryGroup σ := ⟨s₂, hs₂⟩
  refine ⟨⁅g₁, g₂⁆, Subgroup.commutator_mem_commutator (by simp) (by simp), ?_⟩
  rw [coe_commutatorElement_eq_unitaryTransvection_of_coe_eq_siegelTransvection he hew₁ hw₁e hey₀
    hy₀e hcs₁ hcs₂]
  congr 1; simp only [w₁, TauCeti.map_comp_smul, smul_dotProduct, mulVec_smul, dotProduct_smul,
    smul_eq_mul, hu₀y₀, hy₀u₀]; linear_combination b * hε + hb

include hσ hQ hε he hf hef hfe in
private theorem exists_mem_specialIsometryGroup_mulVec_eq_smul_of_anisotropic {v : n → K}
    (hev : (σ ∘ e) ⬝ᵥ (Q *ᵥ v) = 0) (hvv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) ≠ 0) {c : K} (hc : c ≠ 0) :
    ∃ g : Q.specialIsometryGroup σ, (g : Matrix n n K) *ᵥ e = c • e := by
  have hσc := (map_ne_zero σ).mpr hc; have hε0 := left_ne_zero_of_mul_eq_one hε
  let M₁ := Q.hyperbolicRescaling σ ε e f c (σ c)⁻¹
  set a := (σ c * c⁻¹ - 1) * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v))⁻¹
  let M₂ := Q.unitaryTransvection σ v a
  have hM₁e : M₁ *ᵥ e = c • e := hyperbolicRescaling_mulVec_left hε he hfe c (σ c)⁻¹
  have hd₁ : M₁.det = c * (σ c)⁻¹ := det_hyperbolicRescaling hε hf hef hfe c (σ c)⁻¹
  have hd₂ : M₂.det = σ c * c⁻¹ := by rw [det_unitaryTransvection_eq]; dsimp [a]; field_simp; ring
  have hM₁Q := transpose_map_hyperbolicRescaling_mul_mul_self hσ hQ hε he hf hef
    (c₁ := c) (c₂ := (σ c)⁻¹) (by rw [map_inv₀, hσ c, mul_inv_cancel₀ hc])
  have hM₂Q : (M₂.map σ)ᵀ * Q * M₂ = Q := transpose_map_unitaryTransvection_mul_mul_self_of_eq_zero
    (v := v) (a := a) hσ hQ (by simp only [a, map_mul, map_sub, map_inv₀, map_one, hσ c,
      apply_comp_dotProduct_mulVec hσ hQ v v]; field_simp; ring)
  refine ⟨⟨.mk (M₁ * M₂) (by rw [det_mul, hd₁, hd₂, mul_assoc, inv_mul_cancel_left₀ hσc,
      mul_inv_cancel₀ hc]), mem_specialIsometryGroup_iff.mpr (transpose_map_mul_mul_eq_self
      fun x y ↦ by rw [SpecialLinearGroup.coe_mk, ← mulVec_mulVec, ← mulVec_mulVec,
        comp_mulVec_dotProduct_mulVec_mulVec hM₁Q, comp_mulVec_dotProduct_mulVec_mulVec hM₂Q])⟩, ?_⟩
  simpa [M₂, ← mulVec_mulVec, unitaryTransvection_mulVec,
    (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hev] using hM₁e

include hσ hQ hdet hε htr he hf hef hfe in
private theorem unitaryTransvection_mem_commutator_of_card_three_le (hcard : 3 ≤ Fintype.card n)
    {c : K} (hc : c ≠ 0) (hc1 : c * σ c ≠ 1) {a : K} (ha : a + ε * σ a = 0) :
    MemCommTransv Q σ e a := by
  have he₀ := left_ne_zero_of_comp_dotProduct_mulVec_eq_one hef
  let φ : (n → K) →ₗ[K] K × K := (toBilin' Q (σ ∘ e)).prod (toBilin' Q (σ ∘ f))
  have hrk := LinearMap.finrank_range_add_finrank_ker φ
  have hle : Module.finrank K (LinearMap.range φ) ≤ 2 := by
    simpa [Module.finrank_prod, Module.finrank_self] using Submodule.finrank_le (LinearMap.range φ)
  obtain ⟨v, hv_mem, hv0⟩ := (Submodule.ne_bot_iff (LinearMap.ker φ)).mp fun hbot ↦ by
    rw [Module.finrank_fintype_fun_eq_card, hbot, finrank_bot] at hrk; omega
  obtain ⟨hev, hfv⟩ : (σ ∘ e) ⬝ᵥ (Q *ᵥ v) = 0 ∧ (σ ∘ f) ⬝ᵥ (Q *ᵥ v) = 0 := by
    simpa [φ, LinearMap.mem_ker, Prod.ext_iff, toBilin'_apply'] using hv_mem
  by_cases hvv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0
  · exact unitaryTransvection_mem_commutator_of_witt_two hσ hQ hdet hε htr he hf hef he₀
      (notMem_span_of_dotProduct_mulVec_of_ne_zero hfv
        (hfe ▸ left_ne_zero_of_mul_eq_one hε) hv0) he hvv hev ha
  · obtain ⟨g, hge⟩ := exists_mem_specialIsometryGroup_mulVec_eq_smul_of_anisotropic hσ hQ hε he hf
      hef hfe hev hvv hc
    exact unitaryTransvection_mem_commutator_of_mulVec_eq_smul hσ hQ he hc1 hge ha

end Helpers

omit [DecidableEq n] in
/-- For involutive `σ`, each of `∃ c ≠ 0, c ^ 2 ≠ 1 ∧ σ c = c`, Witt index at least two, or
`3 ≤ Fintype.card n ∧ ∃ c ≠ 0, c * σ c ≠ 1` yields a `σ`-fixed scalar outside `{0, 1}`,
`Fintype.card n ≤ 2`, or Witt index at least two. -/
theorem exists_ne_one_and_apply_eq_self_or_card_le_two_or_exists_notMem_span
    (hσ : Function.Involutive σ) (hperf : (∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1 ∧ σ c = c) ∨
      (∃ u w : n → K, u ≠ 0 ∧ w ∉ K ∙ u ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 ∧
        (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) ∨
      (3 ≤ Fintype.card n ∧ ∃ c : K, c ≠ 0 ∧ c * σ c ≠ 1)) :
    (∃ a : K, a ≠ 0 ∧ a ≠ 1 ∧ σ a = a) ∨ Fintype.card n ≤ 2 ∨
      ∃ u w : n → K, u ≠ 0 ∧ w ∉ K ∙ u ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 ∧
        (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0 := by
  rcases hperf with ⟨c, hc0, hcsq, hσc⟩ | h | ⟨_, c, hc0, hc1⟩
  · exact .inl ⟨c, hc0, fun h1 ↦ hcsq (by simp [h1]), hσc⟩
  · exact .inr (.inr h)
  · exact .inl ⟨c * σ c, mul_ne_zero hc0 ((map_ne_zero σ).mpr hc0), hc1, by simp [hσ c, mul_comm]⟩

/-- **Perfectness of a special unitary group.** -/
theorem commutator_specialIsometryGroup_eq_top (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0) (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0) [Nonempty (Q.isotropicPoints σ)]
    (hperf : (∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1 ∧ σ c = c) ∨
      (∃ u w : n → K, u ≠ 0 ∧ w ∉ K ∙ u ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 ∧
        (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) ∨
      (3 ≤ Fintype.card n ∧ ∃ c : K, c ≠ 0 ∧ c * σ c ≠ 1)) :
    commutator (Q.specialIsometryGroup σ) = ⊤ := by
  obtain ⟨e, f, he₀, -, he, hf, hef, hfe⟩ :=
    exists_comp_dotProduct_mulVec_eq_zero_and_eq_one_of_nonempty_isotropicPoints hσ hQ hdet htr
  have := Function.nonempty_of_ne he₀; have hgen :=
    exists_ne_one_and_apply_eq_self_or_card_le_two_or_exists_notMem_span hσ hperf
  have hε := mul_self_eq_one_of_trace_of_det_ne_zero hσ hQ hdet htr
  have hmem (a : K) (ha : a + ε * σ a = 0) : MemCommTransv Q σ e a := by
    rcases hperf with ⟨c, hc0, hcsq, hσc⟩ | ⟨u, w, hu0, hws, hu, hw, huw⟩ | ⟨hcard, c, hc0, hc1⟩
    · obtain ⟨h, -, hhe, -, -⟩ :=
        exists_mem_elementaryUnitaryGroup_mulVec_eq_smul_and_inv_smul_and_eq_self hσ hQ hε hadm he
          hf hef hc0 hσc
      exact unitaryTransvection_mem_commutator_of_mulVec_eq_smul hσ hQ he (by rwa [hσc, ← sq])
        hhe ha
    · exact unitaryTransvection_mem_commutator_of_witt_two hσ hQ hdet hε htr he hf hef hu0 hws hu hw
        huw ha
    · exact unitaryTransvection_mem_commutator_of_card_three_le hσ hQ hdet hε htr he hf hef hfe
        hcard hc0 hc1 ha
  let p₀ : Q.isotropicPoints σ := ⟨_, (mk_mem_isotropicPoints_iff he₀).mpr he⟩
  have hp₀ : Q.unitaryTransvectionSubgroup σ p₀ ≤ commutator (Q.specialIsometryGroup σ) := by
    intro g hg; obtain ⟨a, hga⟩ := (mem_unitaryTransvectionSubgroup_mk_iff he₀ p₀.property).mp hg
    have hiso := (comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g.property)
      f f).trans hf
    rw [hga, unitaryTransvection_mulVec, hef, mul_one] at hiso
    simp only [map_comp_add, TauCeti.map_comp_smul, add_dotProduct, smul_dotProduct, mulVec_add,
      mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, hf, hef, hfe, he] at hiso
    obtain ⟨t, ht_comm, hct⟩ := hmem a (by linear_combination ε * hiso - a * hε)
    exact specialIsometryGroup_ext (hga.trans hct.symm) ▸ ht_comm
  have := isPretransitive_isotropicPoints hσ hQ hdet htr hadm
  rw [eq_top_iff, ← iSup_unitaryTransvectionSubgroup hσ hQ hdet htr hadm hgen, iSup_le_iff]
  intro p; obtain ⟨k, rfl⟩ := MulAction.exists_smul_eq (Q.specialIsometryGroup σ) p₀ p
  rw [unitaryTransvectionSubgroup_smul]; rintro _ ⟨g, hg, rfl⟩
  simpa [MulAut.smul_def, MulAut.conj_apply] using
    (inferInstance : (commutator _).Normal).conj_mem _ (hp₀ hg) k

end Matrix

end
