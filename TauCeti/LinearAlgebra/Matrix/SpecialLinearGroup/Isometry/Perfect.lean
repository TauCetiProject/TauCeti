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
import TauCeti.LinearAlgebra.Matrix.Nondegenerate
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.IsotropicPoints

/-!
# Perfectness of special unitary groups

Let `σ` be an involution of a field `K`, let `Q` be an invertible `ε`-Hermitian matrix,
`(Q.map σ)ᵀ = ε • Q`, whose trace `t ↦ t + ε σ(t)` is onto `{s : K | σ s = ε * s}` and has a
nonzero kernel element (`∃ d ≠ 0, d + ε * σ d = 0`), and suppose `Matrix.isotropicPoints Q σ` is
nonempty. This file proves `Matrix.commutator_specialIsometryGroup_eq_top`:
`Matrix.specialIsometryGroup Q σ` is perfect whenever the fixed field of `σ` contains a nonzero `c`
with `c ^ 2 ≠ 1`, `Q` has Witt index at least two, or `3 ≤ Fintype.card n` and some nonzero `c : K`
satisfies `c * σ c ≠ 1` (each branch also implying the generation disjunction via
`Matrix.exists_ne_one_and_apply_eq_self_or_card_le_two_or_exists_notMem_span`). This supplies the
commutator hypothesis in `TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Simple` and feeds
`TauCeti.DerivedCentralQuotient.quotientCenterEquivOfPerfect`.

## References

* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapter 10 (§10.4 and Theorem 10.20).
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
  (hε : ε * ε = 1) (hσε : σ ε = ε) (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
  {e f : n → K} (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0) (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0)
  (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1) (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε)

include hσ hQ he in
private theorem unitaryTransvection_mem_commutator_of_mulVec_eq_smul {g : Q.specialIsometryGroup σ}
    {c : K} (hc1 : c * σ c ≠ 1) (hge : (g : Matrix n n K) *ᵥ e = c • e) {a : K}
    (ha : a + ε * σ a = 0) : MemCommTransv Q σ e a := by
  have hsub := sub_ne_zero.mpr hc1; set b := a * (c * σ c - 1)⁻¹
  obtain ⟨tb, htb, hctb⟩ := exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ he
    (a := b) (by
      simp only [b, map_mul, map_inv₀, map_sub, hσ c, map_one, mul_comm (σ c) c]
      linear_combination (c * σ c - 1)⁻¹ * ha)
  let t₀ : Q.specialIsometryGroup σ := ⟨tb, htb⟩; have hct₀ : (t₀ : Matrix n n K) = _ := hctb
  refine ⟨⁅g, t₀⁆, Subgroup.commutator_mem_commutator (by simp) (by simp), ?_⟩
  rw [commutatorElement_def, Subgroup.coe_mul, SpecialLinearGroup.coe_mul,
    coe_inv_specialIsometryGroup_eq_unitaryTransvection he hct₀, Subgroup.coe_mul,
    Subgroup.coe_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, Subgroup.coe_inv,
    hct₀, coe_mul_unitaryTransvection_mul_coe_inv g.2, hge, unitaryTransvection_smul,
    unitaryTransvection_mul_unitaryTransvection he]
  congr 1; simp only [b]; field_simp; ring

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
  have hsiegel {v : n → K} (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) (hev : (σ ∘ e) ⬝ᵥ (Q *ᵥ v) = 0) :
      ∃ g : Q.specialIsometryGroup σ, (g : Matrix n n K) = Q.siegelTransvection σ ε e v 0 ∧
        ((g⁻¹ : Q.specialIsometryGroup σ) : Matrix n n K) = Q.siegelTransvection σ ε e (-v) 0 := by
    obtain ⟨s, hs, hcs⟩ := exists_mem_specialIsometryGroup_coe_eq_siegelTransvection hσ hQ he hev
      (c := 0) (by simp [hv])
    exact ⟨⟨s, hs⟩, hcs, by
      simpa [hv] using coe_inv_specialIsometryGroup_eq_siegelTransvection (s := ⟨s, hs⟩) he hev
        ((comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hev) hcs⟩
  obtain ⟨g₁, hcs₁', hg₁_inv⟩ :=
    hsiegel (by rw [comp_smul_dotProduct_mulVec_smul, hu₀, mul_zero]) hew₁
  obtain ⟨g₂, hcs₂', hg₂_inv⟩ := hsiegel hy₀ hey₀
  refine ⟨⁅g₁, g₂⁆, Subgroup.commutator_mem_commutator (by simp) (by simp), ?_⟩
  rw [commutatorElement_def, Subgroup.coe_mul, SpecialLinearGroup.coe_mul, hg₂_inv,
    Subgroup.coe_mul, SpecialLinearGroup.coe_mul, hg₁_inv, Subgroup.coe_mul,
    SpecialLinearGroup.coe_mul, hcs₁', hcs₂',
    siegelTransvection_mul_siegelTransvection he hey₀ hw₁e,
    siegelTransvection_mul_siegelTransvection he (by simp [mulVec_neg, hew₁])
      (by simp [hw₁e, hy₀e]),
    siegelTransvection_mul_siegelTransvection he (by simp [mulVec_neg, hey₀]) (by simp [hy₀e]),
    show w₁ + y₀ + -w₁ + -y₀ = 0 by abel, siegelTransvection_zero_eq_unitaryTransvection]
  congr 1; simp only [w₁, map_comp_add, map_comp_neg, TauCeti.map_comp_smul, add_dotProduct,
    neg_dotProduct, smul_dotProduct, mulVec_neg, mulVec_smul, dotProduct_neg, dotProduct_smul,
    smul_eq_mul, hu₀, hy₀, hu₀y₀, hy₀u₀]; linear_combination b * hε + hb

include hσ hQ hε hσε he hf hef hfe in
private theorem exists_mem_specialIsometryGroup_mulVec_eq_smul_of_anisotropic {v : n → K}
    (hev : (σ ∘ e) ⬝ᵥ (Q *ᵥ v) = 0) (hvv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) ≠ 0) {c : K} (hc : c ≠ 0) :
    ∃ g : Q.specialIsometryGroup σ, (g : Matrix n n K) *ᵥ e = c • e := by
  have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
  let M₁ : Matrix n n K := 1 + ((c - 1) * ε) • vecMulVec e ((σ ∘ f) ᵥ* Q) +
    ((σ c)⁻¹ - 1) • vecMulVec f ((σ ∘ e) ᵥ* Q)
  let M₂ : Matrix n n K := Q.unitaryTransvection σ v ((σ c * c⁻¹ - 1) * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v))⁻¹)
  have hM₁x (x : n → K) : M₁ *ᵥ x = x + (((c - 1) * ε) * ((σ ∘ f) ⬝ᵥ (Q *ᵥ x))) • e +
      (((σ c)⁻¹ - 1) * ((σ ∘ e) ⬝ᵥ (Q *ᵥ x))) • f := by
    simp [M₁, add_mulVec, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec, smul_smul]
  have hM₁e : M₁ *ᵥ e = c • e := by
    rw [hM₁x, hfe, he, mul_zero, zero_smul, add_zero, mul_assoc, hε, mul_one]; module
  have hd₁ : M₁.det = c * (σ c)⁻¹ := det_eq_mul_of_mulVec_eq_smul hε he hf hef hfe hM₁e
    (by rw [hM₁x, hf, hef, mul_zero, zero_smul, add_zero, mul_one]; module)
    fun w hew hfw ↦ by simp [hM₁x, hew, hfw]
  have hd₂ : M₂.det = σ c * c⁻¹ := by
    rw [show M₂ = 1 - vecMulVec (-(((σ c * c⁻¹ - 1) * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v))⁻¹)) • v)
        ((σ ∘ v) ᵥ* Q) by simp [M₂, unitaryTransvection_def, sub_eq_add_neg, smul_vecMulVec],
      TauCeti.det_one_sub_vecMulVec, dotProduct_smul, ← dotProduct_mulVec, smul_eq_mul]
    field_simp; ring
  have hB₁ (x y : n → K) : (σ ∘ (M₁ *ᵥ x)) ⬝ᵥ (Q *ᵥ (M₁ *ᵥ y)) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y) := by
    rw [hM₁x x, hM₁x y]; simp only [map_comp_add, TauCeti.map_comp_smul, map_mul, map_sub,
      map_inv₀, map_one, hσ c, hσε, apply_comp_dotProduct_mulVec hσ hQ, add_dotProduct,
      smul_dotProduct, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, he,
      hf, hef, hfe]; rcases mul_self_eq_one_iff.mp hε with rfl | rfl <;> (field_simp; ring)
  have hB₂ (x y : n → K) : (σ ∘ (M₂ *ᵥ x)) ⬝ᵥ (Q *ᵥ (M₂ *ᵥ y)) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y) := by
    rw [unitaryTransvection_mulVec, unitaryTransvection_mulVec]; simp only [map_comp_add,
      TauCeti.map_comp_smul, map_mul, map_sub, map_inv₀, map_one, hσ c,
      apply_comp_dotProduct_mulVec hσ hQ v v, apply_comp_dotProduct_mulVec hσ hQ v x,
      add_dotProduct, smul_dotProduct, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul,
      smul_eq_mul]; rcases mul_self_eq_one_iff.mp hε with rfl | rfl <;> (field_simp; ring)
  refine ⟨⟨⟨M₁ * M₂, by rw [det_mul, hd₁, hd₂]; field_simp⟩,
    mem_specialIsometryGroup_iff.mpr (transpose_map_mul_mul_eq_self fun x y ↦ by
      rw [SpecialLinearGroup.coe_mk, ← mulVec_mulVec, ← mulVec_mulVec, hB₁, hB₂])⟩, ?_⟩
  simpa [M₂, Subgroup.coe_mk (Q.specialIsometryGroup σ), ← mulVec_mulVec,
    unitaryTransvection_mulVec, (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hev] using hM₁e

include hσ hQ hdet hε hσε htr he hf hef hfe in
private theorem unitaryTransvection_mem_commutator_of_card_three_le (hcard : 3 ≤ Fintype.card n)
    {c : K} (hc : c ≠ 0) (hc1 : c * σ c ≠ 1) {a : K} (ha : a + ε * σ a = 0) :
    MemCommTransv Q σ e a := by
  have he₀ : e ≠ 0 := fun h0 ↦ (one_ne_zero : (1 : K) ≠ 0) (by simpa [h0] using hef.symm)
  let φ : (n → K) →ₗ[K] K × K := (toBilin' Q (σ ∘ e)).prod (toBilin' Q (σ ∘ f))
  have hrk := LinearMap.finrank_range_add_finrank_ker φ
  have hle : Module.finrank K (LinearMap.range φ) ≤ 2 := by
    simpa [Module.finrank_prod, Module.finrank_self] using Submodule.finrank_le (LinearMap.range φ)
  obtain ⟨v, hv_mem, hv0⟩ := (Submodule.ne_bot_iff (LinearMap.ker φ)).mp fun hbot ↦ by
    rw [Module.finrank_fintype_fun_eq_card, hbot, finrank_bot] at hrk; omega
  have hφv : (σ ∘ e) ⬝ᵥ (Q *ᵥ v) = 0 ∧ (σ ∘ f) ⬝ᵥ (Q *ᵥ v) = 0 := by
    simpa [φ, LinearMap.mem_ker, Prod.ext_iff, toBilin'_apply'] using hv_mem
  by_cases hvv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0
  · exact unitaryTransvection_mem_commutator_of_witt_two hσ hQ hdet hε htr he hf hef he₀
      (notMem_span_of_dotProduct_mulVec_of_ne_zero hφv.2
        (hfe ▸ left_ne_zero_of_mul (hε ▸ one_ne_zero)) hv0) he hvv hφv.1 ha
  · obtain ⟨g, hge⟩ := exists_mem_specialIsometryGroup_mulVec_eq_smul_of_anisotropic hσ hQ hε hσε
      he hf hef hfe hφv.1 hvv hc
    exact unitaryTransvection_mem_commutator_of_mulVec_eq_smul hσ hQ he hc1 hge ha

end Helpers

omit [DecidableEq n] in
/-- Each of the three non-solvability hypotheses for a special unitary group implies the three-way
transvection-generation hypothesis of `Matrix.elementaryUnitaryGroup_eq_top`. -/
theorem exists_ne_one_and_apply_eq_self_or_card_le_two_or_exists_notMem_span
    (hσ : Function.Involutive σ)
    (hperf : (∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1 ∧ σ c = c) ∨
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

/-- **Perfectness of a special unitary group.** Let `σ` be an involution of `K`, let `Q` be an
invertible `ε`-Hermitian matrix whose trace `t ↦ t + ε σ(t)` is onto `{s | σ(s) = ε s}` and has a
nonzero kernel element, and suppose `Q.isotropicPoints σ` is nonempty. If `σ` fixes a nonzero `c`
with `c ^ 2 ≠ 1`, `Q` has Witt index at least two, or `3 ≤ Fintype.card n` and some nonzero `c : K`
satisfies `c * σ c ≠ 1`, then `Q.specialIsometryGroup σ` is perfect. -/
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
  have : Nonempty n := let ⟨i, _⟩ := Function.ne_iff.mp he₀; ⟨i⟩
  have hε := mul_self_eq_one_of_trace_of_det_ne_zero hσ hQ hdet htr
  have hσε := map_eq_self_of_mul_self_eq_one_of_det_ne_zero hσ hQ hdet hε
  have hgen := exists_ne_one_and_apply_eq_self_or_card_le_two_or_exists_notMem_span hσ hperf
  have hmem (a : K) (ha : a + ε * σ a = 0) : MemCommTransv Q σ e a := by
    rcases hperf with ⟨c, hc0, hcsq, hσc⟩ | ⟨u, w, hu0, hws, hu, hw, huw⟩ | ⟨hcard, c, hc0, hc1⟩
    · obtain ⟨h, -, hhe, -, -⟩ :=
        exists_mem_elementaryUnitaryGroup_mulVec_eq_smul_and_inv_smul_and_eq_self
          hσ hQ hε hadm he hf hef hc0 hσc
      exact unitaryTransvection_mem_commutator_of_mulVec_eq_smul hσ hQ he (by rwa [hσc, ← sq])
        hhe ha
    · exact unitaryTransvection_mem_commutator_of_witt_two hσ hQ hdet hε htr he hf hef hu0 hws
        hu hw huw ha
    · exact unitaryTransvection_mem_commutator_of_card_three_le hσ hQ hdet hε hσε htr he hf hef
        hfe hcard hc0 hc1 ha
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
    exact specialIsometryGroup_ext (hga.trans hct.symm) ▸ ht_comm
  have := isPretransitive_isotropicPoints hσ hQ hdet htr hadm
  rw [eq_top_iff, ← iSup_unitaryTransvectionSubgroup hσ hQ hdet htr hadm hgen, iSup_le_iff]
  intro p; obtain ⟨k, rfl⟩ := MulAction.exists_smul_eq (Q.specialIsometryGroup σ) p₀ p
  rw [unitaryTransvectionSubgroup_smul]; rintro _ ⟨g, hg, rfl⟩
  simpa [MulAut.smul_def, MulAut.conj_apply] using
    (inferInstance : (commutator _).Normal).conj_mem _ (hp₀ hg) k

end Matrix

end
