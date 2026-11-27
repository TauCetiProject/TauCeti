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
import TauCeti.Logic.Function.Basic

/-!
# Hyperbolic rescalings and Siegel transformations from unitary transvections

For an involution `σ` of a field `K` and an invertible `ε`-Hermitian `Q` (`(Q.map σ)ᵀ = ε • Q`)
with `B(x, y) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y)`, when `ε * ε = 1` and `∃ d ≠ 0, d + ε * σ d = 0`,
`Matrix.elementaryUnitaryGroup Q σ` contains hyperbolic rescalings by nonzero `σ`-fixed scalars
(`Matrix.exists_mem_elementaryUnitaryGroup_mulVec_eq_smul_and_inv_smul_and_eq_self`). When in
addition `t ↦ t + ε σ(t)` is onto `{s : K | σ s = ε * s}` and either `σ` fixes a scalar outside
`{0, 1}`, `Fintype.card n ≤ 2`, or `Q` has Witt index at least two, every admissible
`Matrix.siegelTransvection Q σ ε u w c` in `Q.specialIsometryGroup σ` along isotropic `u` with
`B(u, w) = 0` lies in `Q.elementaryUnitaryGroup σ`
(`Matrix.mk_mem_elementaryUnitaryGroup_of_coe_eq_siegelTransvection`), feeding
`TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Iwasawa`.

## References

* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapters 10 and 11 (§10.4, §11.4).
* L. C. Grove, *Classical Groups and Geometric Algebra* (2002), Chapter 11.
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
    have hσd := (map_ne_zero σ).mpr hd; rw [map_neg, map_mul, map_mul, map_inv₀, map_inv₀, hσε, hσu]
    field_simp; linear_combination -hdε - d * hε
  obtain ⟨t₁, ht₁, hc₁⟩ := exists_mem_elementaryUnitaryGroup_coe_eq_unitaryTransvection hσ hQ he
    (a := u * d) (by rw [map_mul, hσu]; linear_combination u * hdε)
  obtain ⟨t₂, ht₂, hc₂⟩ := exists_mem_elementaryUnitaryGroup_coe_eq_unitaryTransvection hσ hQ hf ha₂
  have ht₁e : (t₁ : Matrix n n K) *ᵥ e = e := by simp [hc₁, unitaryTransvection_mulVec, he]
  have ht₁f : (t₁ : Matrix n n K) *ᵥ f = f + (u * d) • e := by
    simp [hc₁, unitaryTransvection_mulVec, hef]
  have ht₂f : (t₂ : Matrix n n K) *ᵥ f = f := by simp [hc₂, unitaryTransvection_mulVec, hf]
  have hεud : -(ε * u⁻¹ * d⁻¹) * ε = -(u⁻¹ * d⁻¹) := by linear_combination -u⁻¹ * d⁻¹ * hε
  have ht₂e : (t₂ : Matrix n n K) *ᵥ e = e - (u⁻¹ * d⁻¹) • f := by
    rw [hc₂, unitaryTransvection_mulVec, hfe, hεud, neg_smul, ← sub_eq_add_neg]
  have hud : (u⁻¹ * d⁻¹) * (u * d) = 1 := by field_simp
  refine ⟨t₁ * t₂ * t₁, mul_mem (mul_mem ht₁ ht₂) ht₁, ?_, ?_, fun x hex hfx ↦ ?_⟩
  · simp [← mulVec_mulVec, mulVec_sub, mulVec_smul, ht₁e, ht₂e, ht₁f, smul_add, smul_smul, hud]
  · simp [← mulVec_mulVec, mulVec_add, mulVec_sub, mulVec_smul, ht₁f, ht₂f, ht₂e, ht₁e, smul_smul,
      mul_comm (u * d), hud]
  · simp [← mulVec_mulVec, hc₁, hc₂, unitaryTransvection_mulVec, hex, hfx]

/-- **Hyperbolic rescaling lies in the elementary unitary group.** For involutive `σ`, `ε`-Hermitian
`Q` with `ε * ε = 1` and `∃ d ≠ 0, d + ε * σ d = 0`, isotropic `e, f` with `B(e, f) = 1`, and
`a ≠ 0` fixed by `σ`, some `h ∈ Q.elementaryUnitaryGroup σ` sends `e ↦ a • e`, `f ↦ a⁻¹ • f`, and
fixes `{e, f}ᗮ`. -/
theorem exists_mem_elementaryUnitaryGroup_mulVec_eq_smul_and_inv_smul_and_eq_self
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0) {e f : n → K} (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0)
    (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0) (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1) {a : K} (ha : a ≠ 0)
    (hσa : σ a = a) : ∃ h ∈ Q.elementaryUnitaryGroup σ, (h : Matrix n n K) *ᵥ e = a • e ∧
      (h : Matrix n n K) *ᵥ f = a⁻¹ • f ∧ ∀ x : n → K, (σ ∘ e) ⬝ᵥ (Q *ᵥ x) = 0 →
        (σ ∘ f) ⬝ᵥ (Q *ᵥ x) = 0 → (h : Matrix n n K) *ᵥ x = x := by
  obtain ⟨d, hd, hdε⟩ := hadm; have hfe := comp_dotProduct_mulVec_eq_of_eq_one hσ hQ hε hef
  have hw {u : K} := exists_mem_elementary_w_hyperbolic (u := u) hσ hQ hε
    (by simpa [hfe, hef] using apply_comp_dotProduct_mulVec hσ hQ f e) hd hdε he hf hef hfe
  obtain ⟨w₁, hw₁, he₁, hf₁, hx₁⟩ := hw ha hσa
  obtain ⟨w₂, hw₂, he₂, hf₂, hx₂⟩ := hw (neg_ne_zero.mpr one_ne_zero) (by simp)
  refine ⟨w₁ * w₂, mul_mem hw₁ hw₂, ?_, ?_, fun x hex hfx ↦ ?_⟩
  · rw [coe_mul_specialIsometryGroup_mulVec, he₂, mulVec_smul, hf₁, smul_smul]; congr 1; field_simp
  · rw [coe_mul_specialIsometryGroup_mulVec, hf₂, mulVec_smul, he₁, smul_smul]; congr 1; field_simp
  · rw [coe_mul_specialIsometryGroup_mulVec, hx₂ x hex hfx, hx₁ x hex hfx]

private theorem exists_mem_elementaryUnitaryGroup_siegelTransvection_zero_of_isotropic
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) {d : K} (hd : d ≠ 0)
    (hdε : d + ε * σ d = 0) {e x : n → K} (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0)
    (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hex : (σ ∘ e) ⬝ᵥ (Q *ᵥ x) = 0) :
    ∃ t ∈ Q.elementaryUnitaryGroup σ, (t : Matrix n n K) = Q.siegelTransvection σ ε e x 0 := by
  have hndε : -d + ε * σ (-d) = 0 := by rw [map_neg]; linear_combination -hdε
  set u' := d⁻¹ • x; have hσd : σ d ≠ 0 := (map_ne_zero σ).mpr hd
  have hu' : (σ ∘ u') ⬝ᵥ (Q *ᵥ u') = 0 := by rw [comp_smul_dotProduct_mulVec_smul, hx, mul_zero]
  have heu' : (σ ∘ e) ⬝ᵥ (Q *ᵥ u') = 0 := by rw [mulVec_smul, dotProduct_smul, hex, smul_zero]
  have hu'e := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp heu'
  have htrv {v : n → K} {a : K} :=
    exists_mem_elementaryUnitaryGroup_coe_eq_unitaryTransvection (v := v) (a := a) hσ hQ
  obtain ⟨t₁, ht₁, hc₁⟩ := htrv (v := e + u')
    (by simp [map_comp_add, add_dotProduct, mulVec_add, dotProduct_add, he, hu', heu', hu'e]) hdε
  obtain ⟨t₂, ht₂, hc₂⟩ := htrv he hndε; obtain ⟨t₃, ht₃, hc₃⟩ := htrv hu' hndε
  have hd_ratio : d * (σ d)⁻¹ = -ε := mul_right_cancel₀ hσd <| by
    rw [mul_assoc, inv_mul_cancel₀ hσd, mul_one]; linear_combination hdε
  refine ⟨t₁ * t₂ * t₃, mul_mem (mul_mem ht₁ ht₂) ht₃, mulVec_injective <| funext fun v ↦ ?_⟩
  set α := (σ ∘ e) ⬝ᵥ (Q *ᵥ v); set β := (σ ∘ u') ⬝ᵥ (Q *ᵥ v)
  have hv₂ : (t₂ : Matrix n n K) *ᵥ ((t₃ : Matrix n n K) *ᵥ v) = v + (-d * β) • u' + (-d * α) • e :=
    by rw [hc₃, unitaryTransvection_mulVec, hc₂, unitaryTransvection_mulVec, mulVec_add,
      mulVec_smul, dotProduct_add, dotProduct_smul, heu', smul_zero, add_zero]
  have hpair₁ : (σ ∘ (e + u')) ⬝ᵥ (Q *ᵥ (v + (-d * β) • u' + (-d * α) • e)) = α + β := by
    simp only [comp_add_dotProduct_mulVec, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul,
      smul_eq_mul, he, hu', heu', hu'e, α, β]; ring
  have hv₁ : v + (-d * β) • u' + (-d * α) • e + (d * (α + β)) • (e + u') =
      v + (d * β) • e + (d * α) • u' := by module
  have hdα : d * α * d⁻¹ = α := by field_simp
  rw [coe_mul_specialIsometryGroup_mulVec, coe_mul_specialIsometryGroup_mulVec, hv₂, hc₁,
    unitaryTransvection_mulVec, hpair₁, hv₁, siegelTransvection_mulVec]
  simp only [u', β, TauCeti.map_comp_smul, smul_dotProduct, smul_eq_mul, map_inv₀, smul_smul,
    zero_smul, add_zero, ← mul_assoc, hdα, hd_ratio, neg_mul]; module

section SiegelGen

private abbrev MemElemSiegel (Q : Matrix n n K) (σ : K →+* K) (ε : K) (e w₀ : n → K) (c : K) :=
  ∀ {s} (hs : s ∈ Q.specialIsometryGroup σ), (s : Matrix n n K) = Q.siegelTransvection σ ε e w₀ c →
    (⟨s, hs⟩ : Q.specialIsometryGroup σ) ∈ Q.elementaryUnitaryGroup σ

variable (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
  (hε : ε * ε = 1) (hσε : σ ε = ε) (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
  {d : K} (hd : d ≠ 0) (hdε : d + ε * σ d = 0) {e f : n → K} (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0)
  (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0) (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1) (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε)
  {w₀ : n → K} (hew₀ : (σ ∘ e) ⬝ᵥ (Q *ᵥ w₀) = 0)

include hσ hQ hdet he hef hew₀ in
private theorem siegelTransvection_mem_elementary_of_exists_param {c c₀ : K}
    (hc : c + ε * σ c + ε * ((σ ∘ w₀) ⬝ᵥ (Q *ᵥ w₀)) = 0) {s₀ : Q.specialIsometryGroup σ}
    (hs₀ : s₀ ∈ Q.elementaryUnitaryGroup σ) (hcs₀ : ↑s₀ = Q.siegelTransvection σ ε e w₀ c₀) :
    MemElemSiegel Q σ ε e w₀ c := fun {s} hs hcs ↦ by
  have he₀ := left_ne_zero_of_comp_dotProduct_mulVec_eq_one hef
  have hc₀ := (exists_mem_specialIsometryGroup_coe_eq_siegelTransvection_iff hσ hQ hdet he₀ he
    hew₀ c₀).mp ⟨s₀, s₀.property, hcs₀⟩
  obtain ⟨t₀, ht₀, hct₀⟩ := exists_mem_elementaryUnitaryGroup_coe_eq_unitaryTransvection hσ hQ he
    (a := c - c₀) (by rw [map_sub]; linear_combination hc - hc₀)
  exact specialIsometryGroup_ext (g₁ := ⟨s, hs⟩) (g₂ := t₀ * s₀) (by
    rw [coe_mul_specialIsometryGroup, hcs, hct₀, hcs₀,
      ← siegelTransvection_zero_eq_unitaryTransvection (ε := ε),
      siegelTransvection_mul_siegelTransvection he hew₀ (by simp)]; simp) ▸ mul_mem ht₀ hs₀

include hσ hQ hdet hε hσε htr hd hdε he hf hef hew₀ in
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
    exists_mem_elementaryUnitaryGroup_mulVec_eq_smul_and_inv_smul_and_eq_self hσ hQ hε ⟨d, hd, hdε⟩
      he hf hef ha0 hσa
  let s₁ : Q.specialIsometryGroup σ := ⟨s', hs'⟩; have hcs₁ : (s₁ : Matrix n n K) = _ := hcs'
  have hconj : (↑(h * s₁ * h⁻¹) : Matrix n n K) =
      Q.siegelTransvection σ ε e (a • w') (c' * a * a) := by
    rw [coe_mul_specialIsometryGroup, coe_mul_specialIsometryGroup, Subgroup.coe_inv, hcs₁,
      coe_mul_siegelTransvection_mul_coe_inv h.property, hhe, hhx w' hew' hfw',
      siegelTransvection_smul_left hσ, hσa]
  have hw'_sub : a • w' + -w' = (a - 1) • w' := by module
  have hcs₂ : (↑((h * s₁ * h⁻¹) * s₁⁻¹) : Matrix n n K) = Q.siegelTransvection σ ε e w₀
      (c' * (a ^ 2 - 1) + ε * (a - 1) * ((σ ∘ w') ⬝ᵥ (Q *ᵥ w'))) := by
    rw [coe_mul_specialIsometryGroup, hconj,
      coe_inv_specialIsometryGroup_eq_siegelTransvection he hew' hw'e hcs₁,
      siegelTransvection_mul_siegelTransvection he (by simp [mulVec_neg, hew'])
        (by simp [TauCeti.map_comp_smul, hw'e]), hw'_sub,
      smul_inv_smul₀ (sub_ne_zero.mpr ha1)]
    congr 1; simp [TauCeti.map_comp_smul, smul_dotProduct, mulVec_neg, hσa]; ring
  refine siegelTransvection_mem_elementary_of_exists_param hσ hQ hdet he hef hew₀ hc ?_ hcs₂ hs hcs
  simpa [mul_assoc] using mul_mem hh (normal_elementaryUnitaryGroup.conj_mem _ (inv_mem hh) s₁)

include hε he hf hef hfe hew₀ in
private theorem siegelTransvection_mem_elementary_of_card_le_two (hcard : Fintype.card n ≤ 2)
    (hfw₀ : (σ ∘ f) ⬝ᵥ (Q *ᵥ w₀) = 0) {c : K} : MemElemSiegel Q σ ε e w₀ c := fun hs hcs ↦ by
  have hw₀ : w₀ = 0 := by
    by_contra hw₀_ne
    have hli : LinearIndependent K ![e, f, w₀] := Fintype.linearIndependent_iff.mpr fun g hg ↦ by
      rw [Fin.sum_univ_three] at hg
      have hg1 : g 1 = 0 := by
        simpa [mulVec_add, mulVec_smul, he, hef, hew₀] using
          congrArg (fun v ↦ (σ ∘ e) ⬝ᵥ (Q *ᵥ v)) hg
      have hg0 : g 0 = 0 := by
        have h0 := congrArg (fun v ↦ (σ ∘ f) ⬝ᵥ (Q *ᵥ v)) hg
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
          Matrix.head_cons, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul,
          hfe, hf, hfw₀, mul_zero, add_zero, mulVec_zero, dotProduct_zero] at h0
        linear_combination ε * h0 - g 0 * hε
      have hg2 : g 2 = 0 := (smul_eq_zero.mp (by simpa [hg0, hg1] using hg)).resolve_right hw₀_ne
      intro i; fin_cases i <;> assumption
    exact absurd hli.fintype_card_le_finrank (by simp [Module.finrank_fintype_fun_eq_card]; omega)
  exact mk_mem_elementaryUnitaryGroup_of_coe_eq_unitaryTransvection hs he
    (by rwa [hw₀, siegelTransvection_zero_eq_unitaryTransvection] at hcs)

include hσ hQ hdet hε htr hd hdε he hf hef hew₀ in
private theorem siegelTransvection_mem_elementary_of_witt_two {u w : n → K} (hu₀ : u ≠ 0)
    (hw_span : w ∉ K ∙ u) (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hw : (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0)
    (huw : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) {c : K}
    (hc : c + ε * σ c + ε * ((σ ∘ w₀) ⬝ᵥ (Q *ᵥ w₀)) = 0) :
    MemElemSiegel Q σ ε e w₀ c := fun hs hcs ↦ by
  classical
  obtain ⟨u₀, y₀, heu₀, -, hey₀, -, hu₀_iso, hy₀_iso, -, hy₀u₀⟩ :=
    exists_comp_dotProduct_mulVec_eq_zero_and_eq_one_of_notMem_span hσ hQ hdet htr he hf hef hu₀
      hw_span hu hw huw
  let y' : n → K := if (σ ∘ w₀) ⬝ᵥ (Q *ᵥ u₀) = 0 then y₀ else 0
  have hy'_iso : (σ ∘ y') ⬝ᵥ (Q *ᵥ y') = 0 := by dsimp [y']; split_ifs <;> simp [hy₀_iso]
  have hey' : (σ ∘ e) ⬝ᵥ (Q *ᵥ y') = 0 := by dsimp [y']; split_ifs <;> simp [hey₀]
  have hwy' : (σ ∘ (w₀ + y')) ⬝ᵥ (Q *ᵥ u₀) ≠ 0 := by
    dsimp [y']; split_ifs with h0
    · simpa [comp_add_dotProduct_mulVec, h0, hy₀u₀] using left_ne_zero_of_mul_eq_one hε
    · simpa using h0
  obtain ⟨t, ht⟩ := exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero hσ hQ htr hu₀_iso hwy'
  set x₁ := w₀ + y' + t • u₀; set x₂ := (-t) • u₀; set x₃ := -y'
  have hex₁ : (σ ∘ e) ⬝ᵥ (Q *ᵥ x₁) = 0 := by simp [x₁, mulVec_add, mulVec_smul, hew₀, hey', heu₀]
  have hex₂ : (σ ∘ e) ⬝ᵥ (Q *ᵥ x₂) = 0 := by rw [mulVec_smul, dotProduct_smul, heu₀, smul_zero]
  have hex₃ : (σ ∘ e) ⬝ᵥ (Q *ᵥ x₃) = 0 := by simp [x₃, mulVec_neg, hey']
  have hs0 {x : n → K} :=
    exists_mem_elementaryUnitaryGroup_siegelTransvection_zero_of_isotropic (x := x) hσ hQ hd hdε he
  obtain ⟨t₁, ht₁, hc₁⟩ := hs0 ht hex₁; obtain ⟨t₃, ht₃, hc₃⟩ :=
    hs0 (by simp [x₃, map_comp_neg, mulVec_neg, hy'_iso]) hex₃
  obtain ⟨t₂, ht₂, hc₂⟩ := hs0 (by rw [comp_smul_dotProduct_mulVec_smul, hu₀_iso, mul_zero]) hex₂
  have hx₁e := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hex₁
  have hx₂e := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hex₂
  have hx_sum : x₁ + x₂ + x₃ = w₀ := by dsimp [x₁, x₂, x₃]; module
  have hcs₀ : (↑(t₁ * t₂ * t₃) : Matrix n n K) = Q.siegelTransvection σ ε e w₀
      (-(ε * ((σ ∘ x₁) ⬝ᵥ (Q *ᵥ x₂) + (σ ∘ (x₁ + x₂)) ⬝ᵥ (Q *ᵥ x₃)))) := by
    rw [coe_mul_specialIsometryGroup, coe_mul_specialIsometryGroup, hc₁, hc₂, hc₃,
      siegelTransvection_mul_siegelTransvection he hex₂ hx₁e,
      siegelTransvection_mul_siegelTransvection he hex₃
        (by rw [comp_add_dotProduct_mulVec, hx₁e, hx₂e, add_zero]), hx_sum]
    congr 1; ring
  exact siegelTransvection_mem_elementary_of_exists_param hσ hQ hdet he hef hew₀ hc
    (mul_mem (mul_mem ht₁ ht₂) ht₃) hcs₀ hs hcs

end SiegelGen

/-- **Every Siegel transformation in `Q.specialIsometryGroup σ` lies in the elementary unitary
group.** For involutive `σ` and invertible `ε`-Hermitian `Q` with surjective `ε`-trace, nonzero
skew-trace, and either a `σ`-fixed scalar outside `{0, 1}`, `Fintype.card n ≤ 2`, or Witt index at
least two, any `s ∈ Q.specialIsometryGroup σ` equal to `Q.siegelTransvection σ ε u w c` with `u`
isotropic and `B(u, w) = 0` belongs to `Q.elementaryUnitaryGroup σ`. -/
theorem mk_mem_elementaryUnitaryGroup_of_coe_eq_siegelTransvection
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
  have := Function.nonempty_of_ne hu0
  have hε := mul_self_eq_one_of_trace_of_det_ne_zero hσ hQ hdet htr
  have hσε := map_eq_self_of_mul_self_eq_one_of_det_ne_zero hσ hQ hdet hε
  obtain ⟨d, hd, hdε⟩ := hadm; obtain ⟨f, -, hf, huf, hfu⟩ :=
    exists_comp_dotProduct_mulVec_eq_zero_and_eq_one hσ hQ hdet htr hu0 hu
  have hc := (exists_mem_specialIsometryGroup_coe_eq_siegelTransvection_iff hσ hQ hdet hu0 hu
    huw c).mp ⟨s, hs, hcs⟩
  set α := ε * ((σ ∘ f) ⬝ᵥ (Q *ᵥ w)); set w₀ := w - α • u; set c₀ := c + α - ε * σ α
  have huw₀ : (σ ∘ u) ⬝ᵥ (Q *ᵥ w₀) = 0 := by simp [w₀, mulVec_sub, mulVec_smul, huw, hu]
  have hfw₀ : (σ ∘ f) ⬝ᵥ (Q *ᵥ w₀) = 0 := comp_dotProduct_mulVec_sub_smul_eq_zero hε hfu w
  have hcs₀ : (s : Matrix n n K) = Q.siegelTransvection σ ε u w₀ c₀ := by
    rw [hcs, ← sub_add_cancel w (α • u), siegelTransvection_add_smul]
  have hw₀w₀ : (σ ∘ w₀) ⬝ᵥ (Q *ᵥ w₀) = (σ ∘ w) ⬝ᵥ (Q *ᵥ w) := by
    simp [w₀, map_comp_sub, TauCeti.map_comp_smul, sub_dotProduct, smul_dotProduct, mulVec_sub,
      mulVec_smul, hu, huw, (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp huw]
  have hc₀ : c₀ + ε * σ c₀ + ε * ((σ ∘ w₀) ⬝ᵥ (Q *ᵥ w₀)) = 0 := by
    rw [hw₀w₀]; simp only [c₀, map_add, map_sub, map_mul, hσε, hσ α]; linear_combination hc - α * hε
  rcases hgen with ⟨a, ha0, ha1, hσa⟩ | hcard | ⟨u₁, w₁, hu₁0, hw₁s, hu₁, hw₁, hu₁w₁⟩
  · exact siegelTransvection_mem_elementary_of_fixed_ne hσ hQ hdet hε hσε htr hd hdε hu hf huf huw₀
      ha0 ha1 hσa hfw₀ hc₀ hs hcs₀
  · exact siegelTransvection_mem_elementary_of_card_le_two hε hu hf huf hfu huw₀ hcard hfw₀ hs hcs₀
  · exact siegelTransvection_mem_elementary_of_witt_two hσ hQ hdet hε htr hd hdε hu hf huf huw₀
      hu₁0 hw₁s hu₁ hw₁ hu₁w₁ hc₀ hs hcs₀

end Matrix

end
