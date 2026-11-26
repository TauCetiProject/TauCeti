/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Iwasawa
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Siegel
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.Algebra.Group.Hom.Defs
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Primitive
import TauCeti.LinearAlgebra.Span.Basic
import TauCeti.Logic.Function.Basic

/-!
# Transvection generation and the Iwasawa structure of a special unitary group

For involutive `σ` on `K` and invertible `ε`-Hermitian `Q` with surjective `ε`-trace, nonzero
skew-trace, nonempty `Matrix.isotropicPoints Q σ`, and either a `σ`-fixed scalar outside `{0, 1}`,
`Fintype.card n ≤ 2`, or Witt index at least two, we prove `Matrix.elementaryUnitaryGroup_eq_top`
and `Matrix.iSup_unitaryTransvectionSubgroup` and construct `Matrix.unitaryIwasawaStructure`.

## References

* K. Iwasawa, *Über die Einfachheit der speziellen projektiven Gruppen*, Proc. Imp. Acad. Tokyo
  **17** (1941), 57--59.
* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapters 10 and 11 (§10.4, §11.4).
* L. C. Grove, *Classical Groups and Geometric Algebra* (2002), Chapter 11.
-/

public section

open scoped LinearAlgebra.Projectivization Pointwise

namespace Matrix

variable {n K : Type*} [Fintype n] [Field K] {Q : Matrix n n K} {σ : K →+* K} {ε : K}

omit [Fintype n] in
private abbrev extSet (e f : n → K) (S : Submodule K (n → K)) : Set (n → K) := insert e (insert f S)
private abbrev OrthoSet (Q : Matrix n n K) (σ : K →+* K) (U : Set (n → K)) (w : n → K) : Prop :=
  ∀ u ∈ U, (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0
private abbrev OrthoNondegen (Q : Matrix n n K) (σ : K →+* K) (U : Set (n → K)) : Prop :=
  ∀ w, OrthoSet Q σ U w → (∀ w', OrthoSet Q σ U w' → (σ ∘ w') ⬝ᵥ (Q *ᵥ w) = 0) → w = 0
private abbrev HasOrthoProj (Q : Matrix n n K) (σ : K →+* K) (S : Submodule K (n → K)) : Prop :=
  ∀ v : n → K, ∃ s ∈ S, ∀ s' ∈ S, (σ ∘ s') ⬝ᵥ (Q *ᵥ (v - s)) = 0

private theorem ortho_proj_sup_anisotropic {S : Submodule K (n → K)} {x : n → K}
    (hSx : OrthoSet Q σ S x) (hxx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) ≠ 0) (hproj : HasOrthoProj Q σ S) :
    HasOrthoProj Q σ (S ⊔ (K ∙ x)) := fun v ↦ by
  obtain ⟨s₀, hs₀, hsv₀⟩ := hproj v; set α := ((σ ∘ x) ⬝ᵥ (Q *ᵥ x))⁻¹ * ((σ ∘ x) ⬝ᵥ (Q *ᵥ (v - s₀)))
  refine ⟨s₀ + α • x, Submodule.add_mem_sup hs₀ (Submodule.mem_span_singleton.mpr ⟨α, rfl⟩), ?_⟩
  rw [sub_add_eq_sub_sub]; exact S.forall_mem_sup_span_singleton (fun s hs ↦ by
      rw [mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hsv₀ s hs, hSx s hs,
        smul_zero, sub_zero]) (comp_dotProduct_mulVec_sub_inv_mul_smul_eq_zero hxx (v - s₀))
    fun _ _ _ h₁ h₂ ↦ by simp [TauCeti.map_comp_smul, smul_dotProduct, h₁, h₂]

private theorem ortho_proj_sup_hyperbolic (hε : ε * ε = 1) {S : Submodule K (n → K)} {x y : n → K}
    (hSx : OrthoSet Q σ S x) (hSy : OrthoSet Q σ S y) (hxx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0)
    (hyy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0) (hxy : (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 1)
    (hyx : (σ ∘ y) ⬝ᵥ (Q *ᵥ x) = ε) (hproj : HasOrthoProj Q σ S) :
    HasOrthoProj Q σ ((S ⊔ (K ∙ x)) ⊔ (K ∙ y)) := fun v ↦ by
  obtain ⟨s₀, hs₀, hsv₀⟩ := hproj v; obtain ⟨w, hxw, hyw, hr⟩ :=
    exists_eq_add_and_comp_dotProduct_mulVec_eq_zero hε hxx hyy hxy hyx (v - s₀)
  have hlin {u z : n → K} (a : K) (h₁ : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) (h₂ : (σ ∘ z) ⬝ᵥ (Q *ᵥ w) = 0) :
      (σ ∘ (u + a • z)) ⬝ᵥ (Q *ᵥ w) = 0 := by simp [TauCeti.map_comp_smul, smul_dotProduct, h₁, h₂]
  set s₁ := (s₀ + (ε * ((σ ∘ y) ⬝ᵥ (Q *ᵥ (v - s₀)))) • x) + ((σ ∘ x) ⬝ᵥ (Q *ᵥ (v - s₀))) • y
  have hsub : v - s₁ = w := by dsimp [s₁]; linear_combination (norm := module) hr
  refine ⟨s₁, Submodule.add_mem_sup (Submodule.add_mem_sup hs₀
    (Submodule.mem_span_singleton.mpr ⟨_, rfl⟩)) (Submodule.mem_span_singleton.mpr ⟨_, rfl⟩),
    hsub ▸ (S ⊔ (K ∙ x)).forall_mem_sup_span_singleton (S.forall_mem_sup_span_singleton
      (fun s hs ↦ by have h := hsv₀ s hs; rw [hr] at h
                     simpa [mulVec_add, mulVec_smul, hSx s hs, hSy s hs] using h)
      hxw fun _ _ ↦ hlin) hyw fun _ _ ↦ hlin⟩

variable [DecidableEq n]

private abbrev RescalesPair {Q : Matrix n n K} (e f : n → K) (σ : K →+* K)
    (g : Q.specialIsometryGroup σ) (c : K) : Prop :=
  (g : Matrix n n K) *ᵥ e = c • e ∧ (g : Matrix n n K) *ᵥ f = (σ c)⁻¹ • f
private abbrev RescalesAndFixes {Q : Matrix n n K} (e f : n → K) (S : Submodule K (n → K))
    (σ : K →+* K) (g : Q.specialIsometryGroup σ) (c : K) : Prop :=
  (g : Matrix n n K) *ᵥ e = c • e ∧ (g : Matrix n n K) *ᵥ f = (σ c)⁻¹ • f ∧
    ∀ s ∈ S, (g : Matrix n n K) *ᵥ s = s

section Generation

variable (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
  (hε : ε * ε = 1) (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
  {d : K} (hd : d ≠ 0) (hdε : d + ε * σ d = 0) {e f : n → K} (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0)
  (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0) (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1) (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε)
  (hgen : (∃ a : K, a ≠ 0 ∧ a ≠ 1 ∧ σ a = a) ∨ Fintype.card n ≤ 2 ∨
    ∃ u w : n → K, u ≠ 0 ∧ w ∉ K ∙ u ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 ∧
      (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0)
include hσ hQ hdet hε htr hd hdε he hf hef hfe hgen

omit hdet hε htr he hf hef hfe hgen in
private theorem exists_mem_iSup_totally_isotropic_smul {U : Set (n → K)}
    (hW_nd : OrthoNondegen Q σ U) (hW_iso : ∀ w, OrthoSet Q σ U w → (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0)
    {x y x' : n → K} (hx'0 : x' ≠ 0) (hxy : (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 1)
    (hxU : OrthoSet Q σ U x) (hyU : OrthoSet Q σ U y) (hx'U : OrthoSet Q σ U x') :
    ∃ t₂ ∈ Q.elementaryUnitaryGroup σ, ∃ c₂ ≠ (0 : K),
      (∀ u ∈ U, (t₂ : Matrix n n K) *ᵥ u = u) ∧ (t₂ : Matrix n n K) *ᵥ x' = c₂ • x := by
  have hjoin {u v : n → K} (hu : OrthoSet Q σ U u) (hv : OrthoSet Q σ U v) :=
    exists_mem_elementaryUnitaryGroup_mulVec_eq_self_and_mulVec_eq_smul_of_ne_zero hσ hQ
      ⟨d, hd, hdε⟩ (hW_iso u hu) (hW_iso v hv) hu hv
  by_cases hxx' : (σ ∘ x) ⬝ᵥ (Q *ᵥ x') = 0
  swap; · exact hjoin hx'U hxU hxx'
  obtain ⟨v₁, hv₁U, hv₁x'⟩ : ∃ v₁, OrthoSet Q σ U v₁ ∧ (σ ∘ v₁) ⬝ᵥ (Q *ᵥ x') ≠ 0 := by
    by_contra! hall; exact hx'0 (hW_nd x' hx'U hall)
  obtain ⟨z, hzU, hzx', hxz⟩ :
      ∃ z, OrthoSet Q σ U z ∧ (σ ∘ z) ⬝ᵥ (Q *ᵥ x') ≠ 0 ∧ (σ ∘ x) ⬝ᵥ (Q *ᵥ z) ≠ 0 := by
    by_cases hxv₁ : (σ ∘ x) ⬝ᵥ (Q *ᵥ v₁) = 0
    · by_cases hyx' : (σ ∘ y) ⬝ᵥ (Q *ᵥ x') = 0
      · exact ⟨v₁ + y, fun u hu ↦ by simp [mulVec_add, hv₁U u hu, hyU u hu],
          by rwa [comp_add_dotProduct_mulVec, hyx', add_zero], by simp [mulVec_add, hxv₁, hxy]⟩
      · exact ⟨y, hyU, hyx', hxy ▸ one_ne_zero⟩
    · exact ⟨v₁, hv₁U, hv₁x', hxv₁⟩
  obtain ⟨t₂a, ht₂a, c₂a, hc₂a, ht₂aU, ht₂ax'⟩ := hjoin hx'U hzU hzx'
  obtain ⟨t₂b, ht₂b, c₂b, hc₂b, ht₂bU, ht₂bz⟩ := hjoin hzU hxU hxz
  exact ⟨t₂b * t₂a, mul_mem ht₂b ht₂a, c₂a * c₂b, mul_ne_zero hc₂a hc₂b,
    fun u hu ↦ by rw [coe_mul_specialIsometryGroup_mulVec, ht₂aU u hu, ht₂bU u hu],
    by rw [coe_mul_specialIsometryGroup_mulVec, ht₂ax', mulVec_smul, ht₂bz, smul_smul]⟩

omit [DecidableEq n] hdet htr hd hdε he hf hef hfe hgen in
private theorem exists_hyperbolic_partner_of_totally_isotropic {U : Set (n → K)}
    (hW_nd : OrthoNondegen Q σ U) (hW_iso : ∀ w, OrthoSet Q σ U w → (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0)
    {x : n → K} (hx0 : x ≠ 0) (hxU : OrthoSet Q σ U x) :
    ∃ y, OrthoSet Q σ U y ∧ (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 1 ∧ (σ ∘ y) ⬝ᵥ (Q *ᵥ x) = ε ∧ ∀ a, σ a = a := by
  obtain ⟨y₀, hy₀U, hy₀x⟩ : ∃ y₀, OrthoSet Q σ U y₀ ∧ (σ ∘ y₀) ⬝ᵥ (Q *ᵥ x) ≠ 0 := by
    by_contra! hall; exact hx0 (hW_nd x hxU hall)
  set y := ((σ ∘ x) ⬝ᵥ (Q *ᵥ y₀))⁻¹ • y₀
  have hyU : OrthoSet Q σ U y := fun u hu ↦ by simp [y, mulVec_smul, hy₀U u hu]
  have hxy : (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 1 := by
    simp [y, mulVec_smul, inv_mul_cancel₀ ((comp_dotProduct_mulVec_ne_zero_comm hσ hQ).mpr hy₀x)]
  have hyx := comp_dotProduct_mulVec_eq_of_eq_one hσ hQ hε hxy
  have htr_zero (a : K) : a + ε * σ a = 0 := by
    have hiso := hW_iso (x + a • y) fun u hu ↦ by simp [mulVec_add, mulVec_smul, hxU u hu, hyU u hu]
    simp only [map_comp_add, TauCeti.map_comp_smul, add_dotProduct, smul_dotProduct, mulVec_add,
      mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, hW_iso x hxU, hW_iso y hyU, hxy,
      hyx, mul_zero, mul_one, add_zero, zero_add] at hiso; linear_combination hiso
  refine ⟨y, hyU, hxy, hyx, fun a ↦ ?_⟩
  have h1 := htr_zero 1; rw [map_one, mul_one] at h1; linear_combination h1 * σ a - htr_zero a

omit hσ hQ htr hd hdε hgen in
private theorem ortho_nondegenerate_of_proj {S : Submodule K (n → K)}
    (hSe : ∀ s ∈ S, (σ ∘ e) ⬝ᵥ (Q *ᵥ s) = 0) (hSf : ∀ s ∈ S, (σ ∘ f) ⬝ᵥ (Q *ᵥ s) = 0)
    (hproj : HasOrthoProj Q σ S) : OrthoNondegen Q σ (extSet e f S) := fun w hwU hall ↦ by
  by_contra hw0; obtain ⟨v, hvw, -⟩ := exists_comp_dotProduct_mulVec_ne_zero_pair (σ := σ) hdet hw0
    hw0
  obtain ⟨v₁, hev₁, hfv₁, hv_eq⟩ := exists_eq_add_and_comp_dotProduct_mulVec_eq_zero hε he hf hef
    hfe v
  obtain ⟨s, hsS, hsv₁⟩ := hproj v₁
  have hw' := hall (v₁ - s) fun u hu ↦ hu.elim (by rintro rfl; simp [mulVec_sub, hev₁, hSe s hsS])
    fun h ↦ h.elim (by rintro rfl; simp [mulVec_sub, hfv₁, hSf s hsS]) (hsv₁ u)
  have hv₁w : (σ ∘ v₁) ⬝ᵥ (Q *ᵥ w) = 0 := by
    rw [← sub_add_cancel v₁ s, comp_add_dotProduct_mulVec, hw', hwU s (by simp [hsS]), add_zero]
  exact hvw (hv_eq ▸ by simp [TauCeti.map_comp_smul, smul_dotProduct, hv₁w, hwU e (by simp),
    hwU f (by simp)])

omit hdet htr hgen in
private theorem mem_iSup_of_ortho_eq_zero {S : Submodule K (n → K)}
    (hSe : ∀ s ∈ S, (σ ∘ e) ⬝ᵥ (Q *ᵥ s) = 0) (hSf : ∀ s ∈ S, (σ ∘ f) ⬝ᵥ (Q *ᵥ s) = 0)
    (hproj : HasOrthoProj Q σ S) (hW_zero : ¬∃ x ≠ 0, OrthoSet Q σ (extSet e f S) x)
    {g : Q.specialIsometryGroup σ} {c : K} (hc : c ≠ 0) (hg : RescalesAndFixes e f S σ g c) :
    g ∈ Q.elementaryUnitaryGroup σ := by
  rcases hg with ⟨hge, hgf, hgS⟩
  have hg_ortho (w : n → K) (hew : (σ ∘ e) ⬝ᵥ (Q *ᵥ w) = 0) (hfw : (σ ∘ f) ⬝ᵥ (Q *ᵥ w) = 0) :
      (g : Matrix n n K) *ᵥ w = w := by
    obtain ⟨s, hsS, hsw⟩ := hproj w; refine sub_eq_zero.mp (by_contra fun hne ↦ hW_zero ⟨w - s, hne,
      fun u hu ↦ hu.elim (by rintro rfl; simp [mulVec_sub, hew, hSe s hsS]) fun h ↦ h.elim
        (by rintro rfl; simp [mulVec_sub, hfw, hSf s hsS]) (hsw u)⟩) ▸ hgS s hsS
  have hdet1 := (det_eq_mul_of_mulVec_eq_smul hε he hf hef hfe hge hgf hg_ortho).symm.trans
    g.val.prop
  have hmul : σ c = c := by
    simpa [inv_mul_cancel_right₀ ((map_ne_zero σ).mpr hc)] using (congrArg (· * σ c) hdet1).symm
  obtain ⟨h, hh, hhe, hhf, hhw⟩ :=
    exists_mem_elementaryUnitaryGroup_mulVec_eq_smul_and_inv_smul_and_eq_self hσ hQ hε ⟨d, hd, hdε⟩
      he hf hef hc hmul
  exact specialIsometryGroup_ext (eq_of_mulVec_eq_of_comp_dotProduct_mulVec_eq_zero hε he hf hef
    hfe (hge.trans hhe.symm) (by rw [hgf, hmul, hhf])
    fun w hew hfw ↦ (hg_ortho w hew hfw).trans (hhw w hew hfw).symm) ▸ hh

omit htr hd hdε hgen in
private theorem mulVec_anisotropic_eq_smul_of_fixes_ortho {v : n → K}
    (hev : (σ ∘ e) ⬝ᵥ (Q *ᵥ v) = 0) (hfv : (σ ∘ f) ⬝ᵥ (Q *ᵥ v) = 0) (hvv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) ≠ 0)
    {r₀ : Q.specialIsometryGroup σ} {c₁ c₂ : K} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hr₀e : (r₀ : Matrix n n K) *ᵥ e = c₁ • e) (hr₀f : (r₀ : Matrix n n K) *ᵥ f = c₂ • f)
    (hr₀w : ∀ w : n → K, (σ ∘ e) ⬝ᵥ (Q *ᵥ w) = 0 → (σ ∘ f) ⬝ᵥ (Q *ᵥ w) = 0 →
      (σ ∘ v) ⬝ᵥ (Q *ᵥ w) = 0 → (r₀ : Matrix n n K) *ᵥ w = w) :
    ∃ μ' : K, (r₀ : Matrix n n K) *ᵥ v = μ' • v := by
  have hr₀Q := mem_specialIsometryGroup_iff.mp r₀.property
  have herv := comp_dotProduct_mulVec_mulVec_eq_zero_of_mulVec_eq_smul hr₀Q hc₁ hr₀e hev
  have hfrv := comp_dotProduct_mulVec_mulVec_eq_zero_of_mulVec_eq_smul hr₀Q hc₂ hr₀f hfv
  set rv := (r₀ : Matrix n n K) *ᵥ v; refine ⟨((σ ∘ v) ⬝ᵥ (Q *ᵥ v))⁻¹ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ rv)), ?_⟩
  by_contra hne; obtain ⟨y, hy, -⟩ := exists_comp_dotProduct_mulVec_ne_zero_pair (σ := σ) hdet
    (sub_ne_zero.mpr hne) (sub_ne_zero.mpr hne)
  obtain ⟨y₀, hey₀, hfy₀, hy_eq⟩ := exists_eq_add_and_comp_dotProduct_mulVec_eq_zero hε he hf hef
    hfe y
  obtain ⟨w, hvw, hw_ortho, hy₀_eq⟩ := exists_comp_dotProduct_mulVec_eq_zero_and_eq_add_smul hvv y₀
  have hwrv : (σ ∘ w) ⬝ᵥ (Q *ᵥ rv) = 0 := by
    rw [← hr₀w w (hw_ortho _ hev hey₀) (hw_ortho _ hfv hfy₀) hvw,
      comp_mulVec_dotProduct_mulVec_mulVec hr₀Q, (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hvw]
  rw [hy_eq, hy₀_eq] at hy; simp only [map_comp_add, TauCeti.map_comp_smul, add_dotProduct,
    smul_dotProduct, comp_dotProduct_mulVec_sub_inv_mul_smul_eq_zero hvv rv] at hy
  exact hy (by simp [mulVec_sub, mulVec_smul, herv, hev, hfrv, hfv, hwrv,
    (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hvw])

omit [DecidableEq n] hdet htr hgen in
private theorem compensated_reflection_isotropic_pair {v : n → K} (hev : (σ ∘ e) ⬝ᵥ (Q *ᵥ v) = 0)
    (hfv : (σ ∘ f) ⬝ᵥ (Q *ᵥ v) = 0) {τ : K}
    (hτ : τ + ε * σ τ + ε * τ * σ τ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v)) = 0) :
    let z := e + (σ τ + d) • f + τ • v; let u₂ := e + d • f
    (σ ∘ z) ⬝ᵥ (Q *ᵥ z) = 0 ∧ (σ ∘ u₂) ⬝ᵥ (Q *ᵥ u₂) = 0 ∧
      (σ ∘ u₂) ⬝ᵥ (Q *ᵥ z) = σ τ ∧ (σ ∘ u₂) ⬝ᵥ (Q *ᵥ ((-(d⁻¹ * σ τ)) • e)) = σ τ := by
  have hve := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hev
  have hvf := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hfv
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [map_comp_add, TauCeti.map_comp_smul, map_add, hσ τ, add_dotProduct, smul_dotProduct,
      mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, he, hf, hef, hfe, hev,
      hfv, hve, hvf, mul_zero, add_zero, mul_one]
  · linear_combination ε * hτ - (σ τ + τ * σ τ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v))) * hε + hdε
  · linear_combination hdε
  · linear_combination hdε
  · linear_combination -d⁻¹ * σ τ * hdε + σ τ * inv_mul_cancel₀ hd

omit hε hfe in
private theorem exists_mem_iSup_siegel_restore_f {g₁ : Q.specialIsometryGroup σ} {c : K}
    (hc : c ≠ 0) (hg₁e : (g₁ : Matrix n n K) *ᵥ e = c • e) :
    ∃ r ∈ Q.elementaryUnitaryGroup σ, (r : Matrix n n K) *ᵥ e = e ∧
      (r : Matrix n n K) *ᵥ ((g₁ : Matrix n n K) *ᵥ f) = (σ c)⁻¹ • f ∧
      ∀ w : n → K, (σ ∘ e) ⬝ᵥ (Q *ᵥ w) = 0 → (σ ∘ f) ⬝ᵥ (Q *ᵥ w) = 0 →
        (σ ∘ ((g₁ : Matrix n n K) *ᵥ f)) ⬝ᵥ (Q *ᵥ w) = 0 → (r : Matrix n n K) *ᵥ w = w := by
  have hg₁Q := mem_specialIsometryGroup_iff.mp g₁.property
  have hef' : (σ ∘ e) ⬝ᵥ (Q *ᵥ ((g₁ : Matrix n n K) *ᵥ f)) = (σ c)⁻¹ := eq_inv_of_mul_eq_one_right
    (by simpa [hg₁e, TauCeti.map_comp_smul, smul_dotProduct] using
      (comp_mulVec_dotProduct_mulVec_mulVec hg₁Q e f).trans hef)
  have hne := hef' ▸ inv_ne_zero ((map_ne_zero σ).mpr hc)
  obtain ⟨s, hs, w₀, c₀, hew₀, -, hcs, hse, hsf⟩ :=
    exists_mem_specialIsometryGroup_coe_eq_siegelTransvection_mulVec_eq_self_and_mulVec_eq
      (y := (σ c)⁻¹ • f) hσ hQ he ((comp_mulVec_dotProduct_mulVec_mulVec hg₁Q f f).trans hf)
      (by rw [comp_smul_dotProduct_mulVec_smul, hf, mul_zero]) hne
      (by rw [hef', mulVec_smul, dotProduct_smul, hef, smul_eq_mul, mul_one])
  refine ⟨⟨s, hs⟩, mk_mem_elementaryUnitaryGroup_of_coe_eq_siegelTransvection hσ hQ hdet htr
    ⟨d, hd, hdε⟩ hgen he hew₀ hs hcs, hse, hsf, fun w hew hfw hg₁fw ↦ ?_⟩
  simpa [hcs] using siegelTransvection_mulVec_eq_self_of_mulVec_eq hne (hcs ▸ hsf) hew hg₁fw
    (by simp [TauCeti.map_comp_smul, hfw])

private theorem exists_mem_iSup_compensated_reflection_aux {v : n → K}
    (hev : (σ ∘ e) ⬝ᵥ (Q *ᵥ v) = 0) (hfv : (σ ∘ f) ⬝ᵥ (Q *ᵥ v) = 0) {τ : K} (hτ0 : τ ≠ 0)
    (hτ : τ + ε * σ τ + ε * τ * σ τ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v)) = 0) :
    ∃ r₀ ∈ Q.elementaryUnitaryGroup σ, RescalesPair e f σ r₀ (-(d⁻¹ * σ τ)) ∧
      ∀ w : n → K, (σ ∘ e) ⬝ᵥ (Q *ᵥ w) = 0 → (σ ∘ f) ⬝ᵥ (Q *ᵥ w) = 0 →
        (σ ∘ v) ⬝ᵥ (Q *ᵥ w) = 0 → (r₀ : Matrix n n K) *ᵥ w = w := by
  have hε0 := left_ne_zero_of_mul_eq_one hε; have hστ0 := (map_ne_zero σ).mpr hτ0
  set c₀ := -(d⁻¹ * σ τ); have hc₀ := neg_ne_zero.mpr (mul_ne_zero (inv_ne_zero hd) hστ0)
  set z := e + (σ τ + d) • f + τ • v; set u₂ := e + d • f
  obtain ⟨hz, hu₂, hu₂z, hu₂ce⟩ :=
    compensated_reflection_isotropic_pair hσ hQ hε hd hdε he hf hef hfe hev hfv hτ
  obtain ⟨s₁, hs₁, w₁, c₁, hfw₁, -, hcs₁, -, hs₁e⟩ :=
    exists_mem_specialIsometryGroup_coe_eq_siegelTransvection_mulVec_eq_self_and_mulVec_eq hσ hQ hf
      he hz (hfe ▸ hε0) (by simp [mulVec_add, mulVec_smul, hfe, hf, hfv])
  obtain ⟨s₂, hs₂, w₂, c₂, hu₂w₂, -, hcs₂, -, hs₂z⟩ :=
    exists_mem_specialIsometryGroup_coe_eq_siegelTransvection_mulVec_eq_self_and_mulVec_eq
      (y := c₀ • e) hσ hQ hu₂ hz (by rw [comp_smul_dotProduct_mulVec_smul, he, mul_zero])
      (by rw [hu₂z]; exact hστ0) (hu₂z.trans hu₂ce.symm)
  let r₂₁ : Q.specialIsometryGroup σ := ⟨s₂, hs₂⟩ * ⟨s₁, hs₁⟩
  have hr₂₁e : (r₂₁ : Matrix n n K) *ᵥ e = c₀ • e := by
    simp only [r₂₁, coe_mul_specialIsometryGroup_mulVec, hs₁e, hs₂z]
  obtain ⟨r₃, hr₃, hr₃e, hr₃f, hr₃w⟩ :=
    exists_mem_iSup_siegel_restore_f hσ hQ hdet htr hd hdε he hf hef hgen hc₀ hr₂₁e
  have hmem {u w : n → K} := mk_mem_elementaryUnitaryGroup_of_coe_eq_siegelTransvection
    (u := u) (w := w) hσ hQ hdet htr ⟨d, hd, hdε⟩ hgen
  refine ⟨r₃ * r₂₁, mul_mem hr₃ (mul_mem (hmem hu₂ hu₂w₂ hs₂ hcs₂) (hmem hf hfw₁ hs₁ hcs₁)),
    ⟨by rw [coe_mul_specialIsometryGroup_mulVec, hr₂₁e, mulVec_smul, hr₃e],
      by rw [coe_mul_specialIsometryGroup_mulVec, hr₃f]⟩, fun w hew hfw hvw ↦ ?_⟩
  have hzw : (σ ∘ z) ⬝ᵥ (Q *ᵥ w) = 0 := by
    simp [z, map_comp_add, TauCeti.map_comp_smul, add_dotProduct, smul_dotProduct, hew, hfw, hvw]
  have hw₂₁ : (r₂₁ : Matrix n n K) *ᵥ w = w := by
    simp only [r₂₁, coe_mul_specialIsometryGroup_mulVec, hcs₁, hcs₂]
    rw [siegelTransvection_mulVec_eq_self_of_mulVec_eq (hfe ▸ hε0) (hcs₁ ▸ hs₁e) hfw hew hzw]
    exact siegelTransvection_mulVec_eq_self_of_mulVec_eq (by rw [hu₂z]; exact hστ0) (hcs₂ ▸ hs₂z)
      (by simp [map_comp_add, TauCeti.map_comp_smul, add_dotProduct, smul_dotProduct, hew, hfw])
      hzw (by simp [TauCeti.map_comp_smul, hew])
  rw [coe_mul_specialIsometryGroup_mulVec, hw₂₁]; exact hr₃w w hew hfw (by rw [← hw₂₁,
    comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp r₂₁.property), hfw])

private theorem exists_mem_iSup_compensated_reflection {v : n → K} (hev : (σ ∘ e) ⬝ᵥ (Q *ᵥ v) = 0)
    (hfv : (σ ∘ f) ⬝ᵥ (Q *ᵥ v) = 0) (hvv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) ≠ 0) {τ : K} (hτ0 : τ ≠ 0)
    (hτ : τ + ε * σ τ + ε * τ * σ τ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v)) = 0) :
    ∃ r ∈ Q.elementaryUnitaryGroup σ, ∃ c₀ ≠ (0 : K), RescalesPair e f σ r c₀ ∧
      ∀ x : n → K, (σ ∘ e) ⬝ᵥ (Q *ᵥ x) = 0 → (σ ∘ f) ⬝ᵥ (Q *ᵥ x) = 0 →
        (r : Matrix n n K) *ᵥ x = x + (τ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ x))) • v := by
  obtain ⟨r₀, hr₀_mem, ⟨hr₀e, hr₀f⟩, hr₀w⟩ := exists_mem_iSup_compensated_reflection_aux hσ hQ
    hdet hε htr hd hdε he hf hef hfe hgen hev hfv hτ0 hτ
  set c₀ := -(d⁻¹ * σ τ); set μ := 1 + τ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v))
  have hc₀ : c₀ ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (inv_ne_zero hd) ((map_ne_zero σ).mpr hτ0))
  have hσc₀ : σ c₀ ≠ 0 := (map_ne_zero σ).mpr hc₀
  obtain ⟨μ', hrv_eq⟩ := mulVec_anisotropic_eq_smul_of_fixes_ortho hσ hQ hdet hε he hf hef hfe hev
    hfv hvv hc₀ (inv_ne_zero hσc₀) hr₀e hr₀f hr₀w
  have hdet1 := (det_eq_mul_mul_of_mulVec_eq_smul hσ hQ hε he hf hef hev hfv hvv hr₀e hr₀f
    hrv_eq hr₀w).symm.trans r₀.val.prop
  have hσc₀_eq : σ c₀ = c₀ * μ := by
    have hσd := (map_ne_zero σ).mpr hd; simp only [c₀, μ, map_neg, map_mul, map_inv₀, hσ τ]
    field_simp; linear_combination -τ * hdε + ε * σ d * hτ -
      σ d * (σ τ + τ * σ τ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v))) * hε
  have hμ0 : μ ≠ 0 := right_ne_zero_of_mul (hσc₀_eq ▸ hσc₀)
  have hc₀μ : c₀ * (σ c₀)⁻¹ * μ = 1 := by rw [hσc₀_eq]; field_simp
  have hrv' : (r₀ : Matrix n n K) *ᵥ v = μ • v := hrv_eq.trans
    (mul_left_cancel₀ (mul_ne_zero hc₀ (inv_ne_zero hσc₀)) (hdet1.trans hc₀μ.symm) ▸ rfl)
  refine ⟨r₀, hr₀_mem, c₀, hc₀, ⟨hr₀e, hr₀f⟩, fun x hex hfx ↦ ?_⟩
  obtain ⟨w, hvw, hw_ortho, hx_eq⟩ := exists_comp_dotProduct_mulVec_eq_zero_and_eq_add_smul hvv x
  set α := ((σ ∘ v) ⬝ᵥ (Q *ᵥ v))⁻¹ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ x))
  have hαμ : α * μ = α + τ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ x)) := by dsimp [α, μ]; field_simp
  calc (r₀ : Matrix n n K) *ᵥ x
      = (r₀ : Matrix n n K) *ᵥ (w + α • v) := by rw [hx_eq]
    _ = w + (α + τ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ x))) • v := by
        rw [mulVec_add, mulVec_smul, hr₀w w (hw_ortho _ hev hex) (hw_ortho _ hfv hfx) hvw,
          hrv', smul_smul, hαμ]
    _ = x + (τ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ x))) • v := by linear_combination (norm := module) -hx_eq

private theorem exists_mem_iSup_anisotropic_pair_ne {S : Submodule K (n → K)}
    (hSe : ∀ s ∈ S, (σ ∘ e) ⬝ᵥ (Q *ᵥ s) = 0) (hSf : ∀ s ∈ S, (σ ∘ f) ⬝ᵥ (Q *ᵥ s) = 0)
    {g : Q.specialIsometryGroup σ} {c : K} (hc : c ≠ 0) (hg : RescalesAndFixes e f S σ g c)
    {x : n → K} (hxU : OrthoSet Q σ (extSet e f S) x) (hxx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) ≠ 0) :
    ∃ t₁ ∈ Q.elementaryUnitaryGroup σ, ∃ c₁ ≠ (0 : K), RescalesAndFixes e f S σ (t₁ * g) c₁ ∧
      (σ ∘ ((↑(t₁ * g) : Matrix n n K) *ᵥ x)) ⬝ᵥ (Q *ᵥ x) ≠ (σ ∘ x) ⬝ᵥ (Q *ᵥ x) := by
  rcases hg with ⟨hge, hgf, hgS⟩
  by_cases hgx : (σ ∘ ((g : Matrix n n K) *ᵥ x)) ⬝ᵥ (Q *ᵥ x) = (σ ∘ x) ⬝ᵥ (Q *ᵥ x)
  swap; · exact ⟨1, one_mem _, c, hc, (one_mul g).symm ▸ ⟨hge, hgf, hgS⟩, by simpa using hgx⟩
  obtain ⟨β, hβ⟩ := htr ((σ ∘ x) ⬝ᵥ (Q *ᵥ x)) (apply_comp_dotProduct_mulVec hσ hQ x x)
  have hβ0 : β ≠ 0 := fun h0 ↦ hxx (by simpa [h0] using hβ.symm)
  have hσβ0 := (map_ne_zero σ).mpr hβ0; set τ₁ := -β⁻¹
  have hτ₁0 : τ₁ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hβ0); have hex := hxU e (by simp)
  have hfx := hxU f (by simp); have hgQ := mem_specialIsometryGroup_iff.mp g.property
  obtain ⟨r₁, hr₁, c₁', hc₁', ⟨hr₁e, hr₁f⟩, hr₁w⟩ := exists_mem_iSup_compensated_reflection hσ
    hQ hdet hε htr hd hdε he hf hef hfe hgen hex hfx hxx hτ₁0
    (by simp only [τ₁, ← hβ, map_neg, map_inv₀]; field_simp; linear_combination σ β * hε)
  have he_gx := comp_dotProduct_mulVec_mulVec_eq_zero_of_mulVec_eq_smul hgQ hc hge hex
  have hf_gx := comp_dotProduct_mulVec_mulVec_eq_zero_of_mulVec_eq_smul hgQ
    (inv_ne_zero ((map_ne_zero σ).mpr hc)) hgf hfx
  refine ⟨r₁, hr₁, c₁' * c, mul_ne_zero hc₁' hc,
    ⟨by rw [coe_mul_specialIsometryGroup_mulVec, hge, mulVec_smul, hr₁e, smul_smul, mul_comm],
      by rw [coe_mul_specialIsometryGroup_mulVec, hgf, mulVec_smul, hr₁f, smul_smul, map_mul,
        mul_inv, mul_comm],
      fun s hs ↦ by rw [coe_mul_specialIsometryGroup_mulVec, hgS s hs, hr₁w s (hSe s hs) (hSf s hs),
        (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (hxU s (by simp [hs])), mul_zero, zero_smul,
        add_zero]⟩, ?_⟩
  have h1 := congrArg σ hgx; simp only [apply_comp_dotProduct_mulVec hσ hQ] at h1
  rw [coe_mul_specialIsometryGroup_mulVec, hr₁w _ he_gx hf_gx, comp_add_dotProduct_mulVec,
    TauCeti.map_comp_smul, smul_dotProduct, smul_eq_mul, hgx,
    mul_left_cancel₀ (left_ne_zero_of_mul_eq_one hε) h1]
  exact fun h_eq ↦ mul_ne_zero ((map_ne_zero σ).mpr (mul_ne_zero hτ₁0 hxx)) hxx
    (by linear_combination h_eq)

private theorem exists_mem_iSup_anisotropic_step_two {v : n → K} (hev : (σ ∘ e) ⬝ᵥ (Q *ᵥ v) = 0)
    (hfv : (σ ∘ f) ⬝ᵥ (Q *ᵥ v) = 0) {α : K} (hα0 : α ≠ 0)
    (hbvv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = -(α + ε * σ α)) :
    ∃ r₂ ∈ Q.elementaryUnitaryGroup σ, ∃ c₂' ≠ (0 : K), RescalesPair e f σ r₂ c₂' ∧
      ∀ x : n → K, (σ ∘ e) ⬝ᵥ (Q *ᵥ x) = 0 → (σ ∘ f) ⬝ᵥ (Q *ᵥ x) = 0 →
        (r₂ : Matrix n n K) *ᵥ x = x + (α⁻¹ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ x))) • v := by
  have hσα0 := (map_ne_zero σ).mpr hα0
  by_cases hvv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0
  · obtain ⟨r₂, hr₂, hcr₂⟩ := exists_mem_elementaryUnitaryGroup_coe_eq_unitaryTransvection hσ hQ hvv
      (a := α⁻¹) (by rw [map_inv₀]; field_simp; linear_combination ε * (hbvv - hvv) - σ α * hε)
    have hcomm {w : n → K} := (comp_dotProduct_mulVec_eq_zero_comm (x := e) (y := w) hσ hQ).mp
    exact ⟨r₂, hr₂, 1, one_ne_zero, ⟨by simp [hcr₂, unitaryTransvection_mulVec, hcomm hev], by
      simp [hcr₂, unitaryTransvection_mulVec, (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hfv]⟩,
      fun x _ _ ↦ by rw [hcr₂, unitaryTransvection_mulVec]⟩
  · exact exists_mem_iSup_compensated_reflection hσ hQ hdet hε htr hd hdε he hf hef hfe hgen hev
      hfv hvv (inv_ne_zero hα0) (by rw [hbvv, map_inv₀]; field_simp; linear_combination -σ α * hε)

private theorem exists_mem_iSup_fixes_anisotropic {S : Submodule K (n → K)}
    (hSe : ∀ s ∈ S, (σ ∘ e) ⬝ᵥ (Q *ᵥ s) = 0) (hSf : ∀ s ∈ S, (σ ∘ f) ⬝ᵥ (Q *ᵥ s) = 0)
    {g : Q.specialIsometryGroup σ} {c : K} (hc : c ≠ 0) (hg : RescalesAndFixes e f S σ g c)
    {x : n → K} (hxU : OrthoSet Q σ (extSet e f S) x) (hxx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) ≠ 0) :
    ∃ t ∈ Q.elementaryUnitaryGroup σ, ∃ c' ≠ (0 : K),
      RescalesAndFixes e f S σ (t * g) c' ∧ (↑(t * g) : Matrix n n K) *ᵥ x = x := by
  obtain ⟨t₁, ht₁, c₁, hc₁, ⟨hge₁, hgf₁, hgS₁⟩, hne₁⟩ := exists_mem_iSup_anisotropic_pair_ne hσ
    hQ hdet hε htr hd hdε he hf hef hfe hgen hSe hSf hc hg hxU hxx
  let g₁ := t₁ * g; have hg₁Q := mem_specialIsometryGroup_iff.mp g₁.property
  have hex := hxU e (by simp); have hfx := hxU f (by simp)
  set y := (g₁ : Matrix n n K) *ᵥ x; set v := y - x; set α := (σ ∘ v) ⬝ᵥ (Q *ᵥ x)
  have hev : (σ ∘ e) ⬝ᵥ (Q *ᵥ v) = 0 := by rw [mulVec_sub, dotProduct_sub,
    comp_dotProduct_mulVec_mulVec_eq_zero_of_mulVec_eq_smul hg₁Q hc₁ hge₁ hex, hex, sub_zero]
  have hfv : (σ ∘ f) ⬝ᵥ (Q *ᵥ v) = 0 := by rw [mulVec_sub, dotProduct_sub,
    comp_dotProduct_mulVec_mulVec_eq_zero_of_mulVec_eq_smul hg₁Q
      (inv_ne_zero ((map_ne_zero σ).mpr hc₁)) hgf₁ hfx, hfx, sub_zero]
  have hvs (s : n → K) (hs : s ∈ S) : (σ ∘ v) ⬝ᵥ (Q *ᵥ s) = 0 := by
    have hys := comp_mulVec_dotProduct_mulVec_mulVec hg₁Q x s
    rw [hgS₁ s hs] at hys
    rw [map_comp_sub, sub_dotProduct, hys, sub_self]
  have hα0 : α ≠ 0 := by simpa [α, v, map_comp_sub, sub_dotProduct, sub_ne_zero] using hne₁
  have hbvv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = -(α + ε * σ α) := by
    have hσα : ε * σ α = (σ ∘ x) ⬝ᵥ (Q *ᵥ y) - (σ ∘ x) ⬝ᵥ (Q *ᵥ x) := by
      simp only [α, v, map_comp_sub, sub_dotProduct, map_sub, apply_comp_dotProduct_mulVec hσ hQ]
      linear_combination (((σ ∘ x) ⬝ᵥ (Q *ᵥ y)) - ((σ ∘ x) ⬝ᵥ (Q *ᵥ x))) * hε
    simp only [v, y, α, map_comp_sub, sub_dotProduct, mulVec_sub, dotProduct_sub,
      comp_mulVec_dotProduct_mulVec_mulVec hg₁Q x x] at hσα ⊢; linear_combination hσα
  obtain ⟨r₂, hr₂, c₂', hc₂', ⟨hr₂e, hr₂f⟩, hr₂w⟩ := exists_mem_iSup_anisotropic_step_two hσ hQ
    hdet hε htr hd hdε he hf hef hfe hgen hev hfv hα0 hbvv
  have hinv {u w : n → K} (hu : (↑(t₁ * g) : Matrix n n K) *ᵥ u = (r₂ : Matrix n n K) *ᵥ w) :
      (↑(r₂⁻¹ * t₁ * g) : Matrix n n K) *ᵥ u = w := by
    rw [mul_assoc, coe_mul_specialIsometryGroup_mulVec]
    exact coe_inv_specialIsometryGroup_mulVec_of_mulVec_eq hu.symm
  exact ⟨r₂⁻¹ * t₁, mul_mem (inv_mem hr₂) ht₁, c₂'⁻¹ * c₁, mul_ne_zero (inv_ne_zero hc₂') hc₁,
    ⟨hinv (by rw [hge₁]; simp [mulVec_smul, hr₂e, smul_smul]; congr 1; field_simp),
      hinv (by rw [hgf₁]; simp [mulVec_smul, hr₂f, smul_smul]; congr 1
               field_simp [(map_ne_zero σ).mpr hc₂']),
      fun s hs ↦ hinv (by rw [hgS₁ s hs]; simp [hr₂w s (hSe s hs) (hSf s hs), hvs s hs])⟩,
    hinv (by rw [hr₂w x hex hfx, inv_mul_cancel₀ hα0, one_smul]; dsimp [v, y, g₁]; abel)⟩

omit hfe in
private theorem exists_mem_iSup_fixes_totally_isotropic {S : Submodule K (n → K)}
    (hSe : ∀ s ∈ S, (σ ∘ e) ⬝ᵥ (Q *ᵥ s) = 0) (hSf : ∀ s ∈ S, (σ ∘ f) ⬝ᵥ (Q *ᵥ s) = 0)
    (hW_nd : OrthoNondegen Q σ (extSet e f S))
    (hW_iso : ∀ w, OrthoSet Q σ (extSet e f S) w → (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0)
    {g : Q.specialIsometryGroup σ} {c : K} (hc : c ≠ 0) (hg : RescalesAndFixes e f S σ g c)
    {x : n → K} (hx0 : x ≠ 0) (hxU : OrthoSet Q σ (extSet e f S) x) :
    ∃ y : n → K, OrthoSet Q σ (extSet e f S) y ∧ (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 1 ∧
      (σ ∘ y) ⬝ᵥ (Q *ᵥ x) = ε ∧ ∃ t ∈ Q.elementaryUnitaryGroup σ,
        (∀ u ∈ extSet e f S, (↑(t * g) : Matrix n n K) *ᵥ u = u) ∧
        (↑(t * g) : Matrix n n K) *ᵥ x = x ∧ (↑(t * g) : Matrix n n K) *ᵥ y = y := by
  rcases hg with ⟨hge, hgf, hgS⟩; obtain ⟨y, hyU, hxy, hyx, hσ_id⟩ :=
    exists_hyperbolic_partner_of_totally_isotropic hσ hQ hε hW_nd hW_iso hx0 hxU
  have hxx := hW_iso x hxU; have hyy := hW_iso y hyU
  obtain ⟨h₁, hh₁, hh₁e, hh₁f, hh₁w⟩ :=
    exists_mem_elementaryUnitaryGroup_mulVec_eq_smul_and_inv_smul_and_eq_self hσ hQ hε ⟨d, hd, hdε⟩
      he hf hef hc (hσ_id c)
  let g₀ := h₁⁻¹ * g
  have hg₀U (u : n → K) (hu : u ∈ extSet e f S) : (g₀ : Matrix n n K) *ᵥ u = u := by
    rw [coe_mul_specialIsometryGroup_mulVec]
    refine coe_inv_specialIsometryGroup_mulVec_of_mulVec_eq (hu.elim ?_ fun h ↦ h.elim ?_ ?_)
    · rintro rfl; exact hh₁e.trans hge.symm
    · rintro rfl; exact hh₁f.trans (by rw [hgf, hσ_id])
    · exact fun huS ↦ (hh₁w u (hSe u huS) (hSf u huS)).trans (hgS u huS).symm
  obtain ⟨t₂, ht₂, c₂, hc₂, ht₂U, ht₂x'⟩ := exists_mem_iSup_totally_isotropic_smul hσ hQ hd hdε
    hW_nd hW_iso (fun h0 ↦ hx0 (eq_zero_of_mulVec_eq_zero (M := (g₀ : Matrix n n K)) (by simp) h0))
    hxy hxU hyU fun u hu ↦ by rw [← hg₀U u hu,
      comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g₀.property), hxU u hu]
  obtain ⟨h₂, hh₂, hh₂x, -, hh₂w⟩ :=
    exists_mem_elementaryUnitaryGroup_mulVec_eq_smul_and_inv_smul_and_eq_self hσ hQ hε ⟨d, hd, hdε⟩
      hxx hyy hxy hc₂ (hσ_id c₂)
  let g₂ := h₂⁻¹ * (t₂ * g₀)
  have hg₂U (u : n → K) (hu : u ∈ extSet e f S) : (g₂ : Matrix n n K) *ᵥ u = u := by
    rw [coe_mul_specialIsometryGroup_mulVec, coe_mul_specialIsometryGroup_mulVec, hg₀U u hu,
      ht₂U u hu]; exact coe_inv_specialIsometryGroup_mulVec_of_mulVec_eq (hh₂w u
      ((comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (hxU u hu))
      ((comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (hyU u hu)))
  have hg₂x : (g₂ : Matrix n n K) *ᵥ x = x := by
    rw [coe_mul_specialIsometryGroup_mulVec, coe_mul_specialIsometryGroup_mulVec, ht₂x']
    exact coe_inv_specialIsometryGroup_mulVec_of_mulVec_eq hh₂x
  obtain ⟨r₃, hr₃, hr₃x, hr₃y, hr₃w⟩ := exists_mem_iSup_siegel_restore_f hσ hQ hdet htr hd hdε
    hxx hyy hxy hgen one_ne_zero (g₁ := g₂) (by rw [hg₂x, one_smul])
  have heq_prod : (r₃ * (h₂⁻¹ * t₂ * h₁⁻¹)) * g = r₃ * g₂ := by dsimp [g₂, g₀]; group
  refine ⟨y, hyU, hxy, hyx, r₃ * (h₂⁻¹ * t₂ * h₁⁻¹),
    mul_mem hr₃ (mul_mem (mul_mem (inv_mem hh₂) ht₂) (inv_mem hh₁)), fun u hu ↦ ?_,
    by rw [heq_prod, coe_mul_specialIsometryGroup_mulVec, hg₂x, hr₃x],
    by rw [heq_prod, coe_mul_specialIsometryGroup_mulVec, hr₃y, map_one, inv_one, one_smul]⟩
  rw [heq_prod, coe_mul_specialIsometryGroup_mulVec, hg₂U u hu]
  have hcomm {z : n → K} := (comp_dotProduct_mulVec_eq_zero_comm (x := u) (y := z) hσ hQ).mp
  exact hr₃w u (hcomm (hxU u hu)) (hcomm (hyU u hu)) (by rw [← hg₂U u hu,
    comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g₂.property),
    hcomm (hyU u hu)])

omit [DecidableEq n] hσ hQ hdet htr hd hdε he hf hef hgen in
private theorem finrank_lt_card_of_ortho {S : Submodule K (n → K)}
    (hSf : ∀ s ∈ S, (σ ∘ f) ⬝ᵥ (Q *ᵥ s) = 0) : Module.finrank K S < Fintype.card n := by
  have he_notMem : e ∉ S := fun heS ↦ left_ne_zero_of_mul_eq_one hε (hfe ▸ hSf e heS)
  simpa [Module.finrank_fintype_fun_eq_card] using
    Submodule.finrank_lt (s := S) fun htop ↦ he_notMem (htop ▸ Submodule.mem_top)

private theorem mem_iSup_of_fixes_submodule :
    ∀ (k : ℕ) (S : Submodule K (n → K)) (g : Q.specialIsometryGroup σ) (c : K),
      (∀ s ∈ S, (σ ∘ e) ⬝ᵥ (Q *ᵥ s) = 0) → (∀ s ∈ S, (σ ∘ f) ⬝ᵥ (Q *ᵥ s) = 0) →
      HasOrthoProj Q σ S → c ≠ 0 → RescalesAndFixes e f S σ g c →
      Fintype.card n - Module.finrank K S ≤ k → g ∈ Q.elementaryUnitaryGroup σ
  | 0, S, _, _, _, hSf, _, _, _, hk => absurd (finrank_lt_card_of_ortho hε hfe hSf) (by omega)
  | k + 1, S, g, c, hSe, hSf, hproj, hc, hg, hk => by
    have hS_lt := finrank_lt_card_of_ortho hε hfe hSf
    have hsup {u : n → K} {T : Submodule K (n → K)} {z : n → K} :=
      forall_mem_sup_span_singleton_comp_dotProduct_mulVec_eq_zero (Q := Q) (σ := σ) (S := T)
        (u := u) (x := z)
    have hfix {T : Submodule K (n → K)} {A : Matrix n n K} {z : n → K} :=
      forall_mem_sup_span_singleton_mulVec_eq_self (S := T) (A := A) (x := z)
    by_cases hW_aniso : ∃ x, OrthoSet Q σ (extSet e f S) x ∧ (σ ∘ x) ⬝ᵥ (Q *ᵥ x) ≠ 0
    · -- Case 1: anisotropic vector in `(extSet e f S)ᗮ`.
      obtain ⟨x, hxU, hxx⟩ := hW_aniso; have hSx s (hs : s ∈ S) := hxU s (by simp [hs])
      obtain ⟨t, ht, c', hc', ⟨hge', hgf', hgS'⟩, hgx'⟩ := exists_mem_iSup_fixes_anisotropic hσ hQ
        hdet hε htr hd hdε he hf hef hfe hgen hSe hSf hc hg hxU hxx
      have hfin := Submodule.finrank_sup_span_singleton (K := K) (p := S) (v := x)
        fun hxS ↦ hxx (hSx x hxS)
      simpa using mul_mem (inv_mem ht) (mem_iSup_of_fixes_submodule k (S ⊔ (K ∙ x)) (t * g) c'
        (hsup hSe (hxU e (by simp))) (hsup hSf (hxU f (by simp)))
        (ortho_proj_sup_anisotropic hSx hxx hproj) hc' ⟨hge', hgf', hfix hgS' hgx'⟩ (by omega))
    · push Not at hW_aniso; by_cases hW_ne : ∃ x ≠ 0, OrthoSet Q σ (extSet e f S) x
      · -- Case 2: nonzero totally isotropic `(extSet e f S)ᗮ`.
        obtain ⟨x, hx0, hxU⟩ := hW_ne; obtain ⟨y, hyU, hxy, hyx, t, ht, hgU', hgx', hgy'⟩ :=
          exists_mem_iSup_fixes_totally_isotropic hσ hQ hdet hε htr hd hdε he hf hef hgen hSe hSf
            (ortho_nondegenerate_of_proj hdet hε he hf hef hfe hSe hSf hproj) hW_aniso hc hg hx0 hxU
        have hSx s (hs : s ∈ S) := hxU s (by simp [hs])
        have hSy s (hs : s ∈ S) := hyU s (by simp [hs])
        set S' : Submodule K (n → K) := (S ⊔ (K ∙ x)) ⊔ (K ∙ y)
        have hx_notMem : x ∉ S := fun hxS ↦ left_ne_zero_of_mul_eq_one hε
          (hyx ▸ (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (hSy x hxS))
        have hfin : Module.finrank K S < Module.finrank K S' := (Nat.lt_succ_self _).trans_le
          ((Submodule.finrank_sup_span_singleton hx_notMem).symm.trans_le
            (Submodule.finrank_mono le_sup_left))
        simpa using mul_mem (inv_mem ht) (mem_iSup_of_fixes_submodule k S' (t * g) 1
          (hsup (hsup hSe (hxU e (by simp))) (hyU e (by simp)))
          (hsup (hsup hSf (hxU f (by simp))) (hyU f (by simp)))
          (ortho_proj_sup_hyperbolic hε hSx hSy (hW_aniso x hxU) (hW_aniso y hyU) hxy hyx hproj)
          one_ne_zero ⟨by simpa using hgU' e (by simp), by simpa using hgU' f (by simp),
            hfix (hfix (fun s hs ↦ hgU' s (by simp [hs])) hgx') hgy'⟩ (by omega))
      · -- Case 3: zero orthogonal complement `(extSet e f S)ᗮ = 0`.
        exact mem_iSup_of_ortho_eq_zero hσ hQ hε hd hdε he hf hef hfe hSe hSf hproj hW_ne hc hg

end Generation

section MainTheorems

variable (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
  (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
  [Nonempty (Q.isotropicPoints σ)]
  (hgen : (∃ a : K, a ≠ 0 ∧ a ≠ 1 ∧ σ a = a) ∨ Fintype.card n ≤ 2 ∨
    ∃ u w : n → K, u ≠ 0 ∧ w ∉ K ∙ u ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 ∧
      (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0)
include hσ hQ hdet htr hadm hgen in
/-- **The elementary unitary group is the full special unitary group.** -/
theorem elementaryUnitaryGroup_eq_top : Q.elementaryUnitaryGroup σ = ⊤ := by
  obtain ⟨e, f, he₀, -, he, hf, hef, hfe⟩ :=
    exists_comp_dotProduct_mulVec_eq_zero_and_eq_one_of_nonempty_isotropicPoints hσ hQ hdet htr
  have := Function.nonempty_of_ne he₀; obtain ⟨d, hd, hdε⟩ := hadm; rw [eq_top_iff]; intro g _
  have hε := mul_self_eq_one_of_trace_of_det_ne_zero hσ hQ hdet htr
  obtain ⟨t₁, ht₁, c, hc, ht₁ge⟩ := exists_mem_elementaryUnitaryGroup_mulVec_eq_smul hσ hQ hdet htr
    ⟨d, hd, hdε⟩ (fun h0 ↦ he₀ (eq_zero_of_mulVec_eq_zero (M := (g : Matrix n n K)) (by simp) h0))
    he₀ ((comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g.property) e e
      |>.trans he)) he
  obtain ⟨r₂, hr₂, hr₂e, hr₂f, -⟩ := exists_mem_iSup_siegel_restore_f hσ hQ hdet htr hd hdε he hf
    hef hgen hc (g₁ := t₁ * g) (by rwa [coe_mul_specialIsometryGroup_mulVec])
  simpa [mul_assoc] using mul_mem (mul_mem (inv_mem ht₁) (inv_mem hr₂))
    (mem_iSup_of_fixes_submodule hσ hQ hdet hε htr hd hdε he hf hef hfe hgen
      (Fintype.card n - Module.finrank K (⊥ : Submodule K (n → K))) ⊥ (r₂ * (t₁ * g)) c (by simp)
      (by simp) (fun _ ↦ ⟨0, Submodule.zero_mem ⊥, by simp⟩) hc
      ⟨by rw [coe_mul_specialIsometryGroup_mulVec, coe_mul_specialIsometryGroup_mulVec, ht₁ge,
        mulVec_smul, hr₂e], by rw [coe_mul_specialIsometryGroup_mulVec, hr₂f], by simp⟩ le_rfl)

include hσ hQ hdet htr hadm hgen in
/-- **Unitary transvections generate the special unitary group.** -/
theorem iSup_unitaryTransvectionSubgroup :
    ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p = ⊤ :=
  elementaryUnitaryGroup_eq_iSup.symm.trans (elementaryUnitaryGroup_eq_top hσ hQ hdet htr hadm hgen)

/-- **The Iwasawa structure of a special unitary group on its isotropic points.** -/
def unitaryIwasawaStructure :
    MulAction.IwasawaStructure (Q.specialIsometryGroup σ) (Q.isotropicPoints σ) where
  T := Q.unitaryTransvectionSubgroup σ
  is_comm _ := inferInstance
  is_conj := unitaryTransvectionSubgroup_smul
  is_generator := iSup_unitaryTransvectionSubgroup hσ hQ hdet htr hadm hgen

/-- The subgroups of `Matrix.unitaryIwasawaStructure` are `Matrix.unitaryTransvectionSubgroup`. -/
@[simp]
theorem unitaryIwasawaStructure_T (p : Q.isotropicPoints σ) :
    (Q.unitaryIwasawaStructure hσ hQ hdet htr hadm hgen).T p = Q.unitaryTransvectionSubgroup σ p :=
  (rfl)

end MainTheorems

end Matrix

end
