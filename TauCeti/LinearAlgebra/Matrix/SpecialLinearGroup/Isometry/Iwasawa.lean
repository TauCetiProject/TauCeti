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

/-!
# Transvection generation and the Iwasawa structure of a special unitary group

Building on `TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Siegel`, this file proves via
compensated unitary reflections and orthogonal-projection induction on `{e, f}ᗮ` that the unitary
transvection subgroups generate `Q.specialIsometryGroup σ` away from `SU₃(2)`, and packages the
resulting `MulAction.IwasawaStructure` on `Q.isotropicPoints σ`.

## Main definitions and results

* `Matrix.iSup_unitaryTransvectionSubgroup`: transvections generate `Matrix.specialIsometryGroup`.
* `Matrix.unitaryIwasawaStructure`: `MulAction.IwasawaStructure` on `Matrix.isotropicPoints Q σ`.

## References

* D. E. Taylor, *The Geometry of the Classical Groups* (1992), §10.4 and Theorem 11.27.
-/

public section

open scoped LinearAlgebra.Projectivization Pointwise

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] {Q : Matrix n n K} {σ : K →+* K}
  {ε : K}
private theorem coe_mul_mulVec (g₁ g₂ : Q.specialIsometryGroup σ) (x : n → K) :
    (↑(g₁ * g₂) : Matrix n n K) *ᵥ x = (g₁ : Matrix n n K) *ᵥ ((g₂ : Matrix n n K) *ᵥ x) := by
  rw [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, mulVec_mulVec]
private theorem coe_inv_mulVec_of_mulVec_eq {g : Q.specialIsometryGroup σ} {x y : n → K}
    (h : (g : Matrix n n K) *ᵥ x = y) :
    (↑(g⁻¹) : Matrix n n K) *ᵥ y = x := by
  rw [← h, ← coe_mul_mulVec, inv_mul_cancel, Subgroup.coe_one, SpecialLinearGroup.coe_one,
    one_mulVec]
private theorem comp_dotProduct_mulVec_mulVec_eq_zero_of_smul {g : Q.specialIsometryGroup σ}
    {u x : n → K} {c : K} (hc : c ≠ 0) (hgu : (g : Matrix n n K) *ᵥ u = c • u)
    (hux : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0) : (σ ∘ u) ⬝ᵥ (Q *ᵥ ((g : Matrix n n K) *ᵥ x)) = 0 := by
  have h : (σ ∘ (c • u)) ⬝ᵥ (Q *ᵥ ((g : Matrix n n K) *ᵥ x)) = 0 := by
    rw [← hgu, comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g.2), hux]
  rw [TauCeti.map_comp_smul, smul_dotProduct, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left ((map_ne_zero σ).mpr hc)
private theorem one_sub_vecMulVec_mulVec (u r x : n → K) :
    (1 - vecMulVec u r) *ᵥ x = x - (r ⬝ᵥ x) • u := by
  rw [sub_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
omit [DecidableEq n] in
private theorem ortho_sup_span_singleton {u x : n → K} {S : Submodule K (n → K)}
    (hS : ∀ s ∈ S, (σ ∘ u) ⬝ᵥ (Q *ᵥ s) = 0) (hx : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0) :
    ∀ s ∈ S ⊔ (K ∙ x), (σ ∘ u) ⬝ᵥ (Q *ᵥ s) = 0 := fun _ hs ↦ by
  obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := Submodule.mem_sup.mp hs
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hs₂
  simp [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, hS s₁ hs₁, hx]
omit [DecidableEq n] in
private theorem fixes_sup_span_singleton {A : Matrix n n K} {x : n → K} {S : Submodule K (n → K)}
    (hS : ∀ s ∈ S, A *ᵥ s = s) (hx : A *ᵥ x = x) :
    ∀ s ∈ S ⊔ (K ∙ x), A *ᵥ s = s := fun _ hs ↦ by
  obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := Submodule.mem_sup.mp hs
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hs₂
  rw [mulVec_add, mulVec_smul, hS s₁ hs₁, hx]
private theorem siegelTransvection_mulVec_eq_self_of_ortho {u w x y z : n → K} {c : K}
    (hux : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) ≠ 0) (hgx : Q.siegelTransvection σ ε u w c *ᵥ x = y)
    (huz : (σ ∘ u) ⬝ᵥ (Q *ᵥ z) = 0) (hxz : (σ ∘ x) ⬝ᵥ (Q *ᵥ z) = 0) (hyz : (σ ∘ y) ⬝ᵥ (Q *ᵥ z) = 0)
    :
    Q.siegelTransvection σ ε u w c *ᵥ z = z := by
  have hbw : ((σ ∘ u) ⬝ᵥ (Q *ᵥ x)) • w =
      y - x + (ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ x)) - c * ((σ ∘ u) ⬝ᵥ (Q *ᵥ x))) • u := by
    rw [← hgx, siegelTransvection_mulVec]; module
  have hpair := congrArg (fun t ↦ (σ ∘ t) ⬝ᵥ (Q *ᵥ z)) hbw
  simp only [TauCeti.map_comp_smul, map_comp_add, map_comp_sub, smul_dotProduct, add_dotProduct,
    sub_dotProduct, smul_eq_mul, huz, hxz, hyz, mul_zero, sub_zero, add_zero] at hpair
  have hwz : (σ ∘ w) ⬝ᵥ (Q *ᵥ z) = 0 :=
    (mul_eq_zero.mp hpair).resolve_left ((map_ne_zero σ).mpr hux)
  simp [siegelTransvection_mulVec, huz, hwz]
/-- Two-factor rank-one determinant formula on a hyperbolic pair `(e, f)`: if `A *ᵥ e = c₁ • e`,
`A *ᵥ f = c₂ • f`, and `A` fixes `{e, f}ᗮ` pointwise, then `A.det = c₁ * c₂`. -/
theorem det_eq_of_mulVec_hyperbolic (hε : ε * ε = 1) {e f : n → K} (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0)
    (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0) (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1) (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε)
    {A : Matrix n n K} {c₁ c₂ : K} (hAe : A *ᵥ e = c₁ • e) (hAf : A *ᵥ f = c₂ • f)
    (hAw : ∀ w : n → K, (σ ∘ e) ⬝ᵥ (Q *ᵥ w) = 0 → (σ ∘ f) ⬝ᵥ (Q *ᵥ w) = 0 → A *ᵥ w = w) :
    A.det = c₁ * c₂ := by
  let M₁ : Matrix n n K := 1 - vecMulVec ((1 - c₁) • e) (ε • ((σ ∘ f) ᵥ* Q))
  let M₂ : Matrix n n K := 1 - vecMulVec ((1 - c₂) • f) ((σ ∘ e) ᵥ* Q)
  have hM₂e : M₂ *ᵥ e = e := by
    rw [one_sub_vecMulVec_mulVec, ← dotProduct_mulVec, he, zero_smul, sub_zero]
  have hM₂f : M₂ *ᵥ f = c₂ • f := by
    rw [one_sub_vecMulVec_mulVec, ← dotProduct_mulVec, hef, one_smul]; module
  have hM₁e : M₁ *ᵥ e = c₁ • e := by
    rw [one_sub_vecMulVec_mulVec, smul_dotProduct, ← dotProduct_mulVec, hfe, smul_eq_mul, hε,
      one_smul]; module
  have hM₁f : M₁ *ᵥ f = f := by
    rw [one_sub_vecMulVec_mulVec, smul_dotProduct, ← dotProduct_mulVec, hf, smul_zero, zero_smul,
      sub_zero]
  have hA : A = M₁ * M₂ := mulVec_injective (funext fun x ↦ by
    set w := x - (ε * ((σ ∘ f) ⬝ᵥ (Q *ᵥ x))) • e - ((σ ∘ e) ⬝ᵥ (Q *ᵥ x)) • f
    have hew : (σ ∘ e) ⬝ᵥ (Q *ᵥ w) = 0 := by
      simp [w, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, he, hef]
    have hfw : (σ ∘ f) ⬝ᵥ (Q *ᵥ w) = 0 := by
      simp only [w, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, hfe, hf]
      linear_combination -((σ ∘ f) ⬝ᵥ (Q *ᵥ x)) * hε
    have hM₂w : M₂ *ᵥ w = w := by
      rw [one_sub_vecMulVec_mulVec, ← dotProduct_mulVec, hew, zero_smul, sub_zero]
    have hM₁w : M₁ *ᵥ w = w := by
      rw [one_sub_vecMulVec_mulVec, smul_dotProduct, ← dotProduct_mulVec, hfw, smul_zero, zero_smul,
        sub_zero]
    have hx_eq : x = (ε * ((σ ∘ f) ⬝ᵥ (Q *ᵥ x))) • e + ((σ ∘ e) ⬝ᵥ (Q *ᵥ x)) • f + w := by
      dsimp [w]; module
    rw [hx_eq, ← mulVec_mulVec]
    simp only [mulVec_add, mulVec_smul, hAe, hAf, hAw w hew hfw, hM₂e, hM₂f, hM₂w, hM₁e, hM₁f,
      hM₁w, smul_smul])
  have hd₁ : M₁.det = c₁ := by
    rw [TauCeti.det_one_sub_vecMulVec, smul_dotProduct, dotProduct_smul, ← dotProduct_mulVec, hfe,
      smul_eq_mul, smul_eq_mul]
    linear_combination -(1 - c₁) * hε
  have hd₂ : M₂.det = c₂ := by
    rw [TauCeti.det_one_sub_vecMulVec, dotProduct_smul, ← dotProduct_mulVec, hef, smul_eq_mul]
    ring
  rw [hA, det_mul, hd₁, hd₂]
private theorem det_eq_of_mulVec_hyperbolic_anisotropic (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) {e f v : n → K} (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0)
    (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0) (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1) (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε)
    (hev : (σ ∘ e) ⬝ᵥ (Q *ᵥ v) = 0) (hfv : (σ ∘ f) ⬝ᵥ (Q *ᵥ v) = 0) (hvv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) ≠ 0)
    {A : Matrix n n K} {c₁ c₂ c₃ : K} (hAe : A *ᵥ e = c₁ • e) (hAf : A *ᵥ f = c₂ • f)
    (hAv : A *ᵥ v = c₃ • v)
    (hAw : ∀ w : n → K, (σ ∘ e) ⬝ᵥ (Q *ᵥ w) = 0 → (σ ∘ f) ⬝ᵥ (Q *ᵥ w) = 0 →
      (σ ∘ v) ⬝ᵥ (Q *ᵥ w) = 0 → A *ᵥ w = w) : A.det = c₁ * c₂ * c₃ := by
  have hve := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hev
  have hvf := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hfv
  by_cases hc₃ : c₃ = 0
  · subst hc₃
    have hv0 : v ≠ 0 := fun h0 ↦ hvv (by simp [h0])
    simp [exists_mulVec_eq_zero_iff.mp ⟨v, hv0, by simpa using hAv⟩]
  let M₃ : Matrix n n K :=
    1 - vecMulVec ((1 - c₃⁻¹) • v) (((σ ∘ v) ⬝ᵥ (Q *ᵥ v))⁻¹ • ((σ ∘ v) ᵥ* Q))
  have hd₃ : M₃.det = c₃⁻¹ := by
    rw [TauCeti.det_one_sub_vecMulVec, smul_dotProduct, dotProduct_smul, ← dotProduct_mulVec,
      smul_eq_mul, smul_eq_mul]; field_simp; ring
  have hAM₃_v : (A * M₃) *ᵥ v = v := by
    rw [← mulVec_mulVec, one_sub_vecMulVec_mulVec, smul_dotProduct, ← dotProduct_mulVec,
      smul_eq_mul, inv_mul_cancel₀ hvv, one_smul, mulVec_sub, mulVec_smul, hAv, smul_smul]
    have hc₃' : (1 - c₃⁻¹) * c₃ = c₃ - 1 := by field_simp
    rw [hc₃']; module
  have hAM₃_w (w : n → K) (hew : (σ ∘ e) ⬝ᵥ (Q *ᵥ w) = 0) (hfw : (σ ∘ f) ⬝ᵥ (Q *ᵥ w) = 0) :
      (A * M₃) *ᵥ w = w := by
    set w₀ := w - (((σ ∘ v) ⬝ᵥ (Q *ᵥ v))⁻¹ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ w))) • v
    have hvw₀ : (σ ∘ v) ⬝ᵥ (Q *ᵥ w₀) = 0 := by
      simp only [w₀, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      field_simp; ring
    have hw_eq : w = (((σ ∘ v) ⬝ᵥ (Q *ᵥ v))⁻¹ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ w))) • v + w₀ := by
      dsimp [w₀]; module
    rw [hw_eq, mulVec_add, mulVec_smul, hAM₃_v, ← mulVec_mulVec, one_sub_vecMulVec_mulVec,
      smul_dotProduct, ← dotProduct_mulVec, hvw₀, smul_zero, zero_smul, sub_zero, hAw w₀
        (by simp [w₀, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hew, hev])
        (by simp [w₀, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hfw, hfv]) hvw₀]
  have hdet_prod := det_eq_of_mulVec_hyperbolic hε he hf hef hfe
    (by rw [← mulVec_mulVec, one_sub_vecMulVec_mulVec, smul_dotProduct, ← dotProduct_mulVec, hve,
      smul_zero, zero_smul, sub_zero, hAe])
    (by rw [← mulVec_mulVec, one_sub_vecMulVec_mulVec, smul_dotProduct, ← dotProduct_mulVec, hvf,
      smul_zero, zero_smul, sub_zero, hAf]) hAM₃_w
  rw [det_mul, hd₃] at hdet_prod
  calc A.det = A.det * c₃⁻¹ * c₃ := by rw [inv_mul_cancel_right₀ hc₃]
    _ = c₁ * c₂ * c₃ := by rw [hdet_prod]
private theorem ortho_nondegenerate_of_proj (hdet : Q.det ≠ 0) (hε : ε * ε = 1) {e f : n → K}
    (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0) (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0) (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1)
    (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε) {S : Submodule K (n → K)}
    (hSe : ∀ s ∈ S, (σ ∘ e) ⬝ᵥ (Q *ᵥ s) = 0) (hSf : ∀ s ∈ S, (σ ∘ f) ⬝ᵥ (Q *ᵥ s) = 0)
    (hproj : ∀ v : n → K, ∃ s ∈ S, ∀ s' ∈ S, (σ ∘ s') ⬝ᵥ (Q *ᵥ (v - s)) = 0) {w : n → K}
    (hwU : ∀ u ∈ insert e (insert f (S : Set (n → K))), (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0)
    (hall : ∀ w' : n → K, (∀ u ∈ insert e (insert f (S : Set (n → K))), (σ ∘ u) ⬝ᵥ (Q *ᵥ w') = 0) →
      (σ ∘ w') ⬝ᵥ (Q *ᵥ w) = 0) : w = 0 := by
  by_contra hw0
  obtain ⟨v, hvw, -⟩ := exists_comp_dotProduct_mulVec_ne_zero_pair (σ := σ) hdet hw0 hw0
  set v₁ := v - (ε * ((σ ∘ f) ⬝ᵥ (Q *ᵥ v))) • e - ((σ ∘ e) ⬝ᵥ (Q *ᵥ v)) • f
  obtain ⟨s, hsS, hsv₁⟩ := hproj v₁
  have hw' : (σ ∘ (v₁ - s)) ⬝ᵥ (Q *ᵥ w) = 0 := hall (v₁ - s) fun u hu ↦ by
    rcases hu with heu | hfu
    · rw [heu]; simp [v₁, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, he, hef,
        hSe s hsS]
    · rcases hfu with hfu | huS
      · rw [hfu]; simp only [v₁, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul,
          smul_eq_mul, hfe, hf, hSf s hsS]
        linear_combination -((σ ∘ f) ⬝ᵥ (Q *ᵥ v)) * hε
      · exact hsv₁ u huS
  have hv_eq : v = (v₁ - s) + s + (ε * ((σ ∘ f) ⬝ᵥ (Q *ᵥ v))) • e + ((σ ∘ e) ⬝ᵥ (Q *ᵥ v)) • f := by
    dsimp [v₁]; module
  rw [hv_eq, comp_add_dotProduct_mulVec, comp_add_dotProduct_mulVec, comp_add_dotProduct_mulVec,
    TauCeti.map_comp_smul, TauCeti.map_comp_smul, smul_dotProduct, smul_dotProduct, hw',
    hwU s (by simp [hsS]), hwU e (by simp), hwU f (by simp)] at hvw
  exact hvw (by simp)
omit [DecidableEq n] in
private theorem ortho_proj_sup_anisotropic {S : Submodule K (n → K)} {x : n → K}
    (hSx : ∀ s ∈ S, (σ ∘ s) ⬝ᵥ (Q *ᵥ x) = 0) (hxx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) ≠ 0)
    (hproj : ∀ v : n → K, ∃ s ∈ S, ∀ s' ∈ S, (σ ∘ s') ⬝ᵥ (Q *ᵥ (v - s)) = 0) (v : n → K) :
    ∃ s ∈ S ⊔ (K ∙ x), ∀ s' ∈ S ⊔ (K ∙ x), (σ ∘ s') ⬝ᵥ (Q *ᵥ (v - s)) = 0 := by
  obtain ⟨s₀, hs₀, hsv₀⟩ := hproj v
  set r := v - s₀; set α := ((σ ∘ x) ⬝ᵥ (Q *ᵥ x))⁻¹ * ((σ ∘ x) ⬝ᵥ (Q *ᵥ r))
  refine ⟨s₀ + α • x,
    Submodule.add_mem_sup hs₀ (Submodule.smul_mem _ α (Submodule.mem_span_singleton_self x)),
    fun s' hs' ↦ ?_⟩
  obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := Submodule.mem_sup.mp hs'
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hs₂
  have heq_sub : v - (s₀ + α • x) = r - α • x := by dsimp [r]; module
  rw [heq_sub, comp_add_dotProduct_mulVec, TauCeti.map_comp_smul, smul_dotProduct]
  simp only [α, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, hsv₀ s₁ hs₁,
    hSx s₁ hs₁]
  field_simp; ring
omit [DecidableEq n] in
private theorem ortho_proj_sup_hyperbolic (hε : ε * ε = 1) {S : Submodule K (n → K)} {x y : n → K}
    (hSx : ∀ s ∈ S, (σ ∘ s) ⬝ᵥ (Q *ᵥ x) = 0) (hSy : ∀ s ∈ S, (σ ∘ s) ⬝ᵥ (Q *ᵥ y) = 0)
    (hxx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hyy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0) (hxy : (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 1)
    (hyx : (σ ∘ y) ⬝ᵥ (Q *ᵥ x) = ε)
    (hproj : ∀ v : n → K, ∃ s ∈ S, ∀ s' ∈ S, (σ ∘ s') ⬝ᵥ (Q *ᵥ (v - s)) = 0) (v : n → K) :
    ∃ s ∈ (S ⊔ (K ∙ x)) ⊔ (K ∙ y),
      ∀ s' ∈ (S ⊔ (K ∙ x)) ⊔ (K ∙ y), (σ ∘ s') ⬝ᵥ (Q *ᵥ (v - s)) = 0 := by
  obtain ⟨s₀, hs₀, hsv₀⟩ := hproj v
  set r := v - s₀; set α := ε * ((σ ∘ y) ⬝ᵥ (Q *ᵥ r)); set β := (σ ∘ x) ⬝ᵥ (Q *ᵥ r)
  refine ⟨(s₀ + α • x) + β • y, Submodule.add_mem_sup
    (Submodule.add_mem_sup hs₀ (Submodule.smul_mem _ α (Submodule.mem_span_singleton_self x)))
    (Submodule.smul_mem _ β (Submodule.mem_span_singleton_self y)), fun s' hs' ↦ ?_⟩
  obtain ⟨s₁₂, hs₁₂, s₃, hs₃, rfl⟩ := Submodule.mem_sup.mp hs'
  obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := Submodule.mem_sup.mp hs₁₂
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hs₂
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hs₃
  have heq_sub : v - ((s₀ + α • x) + β • y) = r - α • x - β • y := by dsimp [r]; module
  rw [heq_sub, comp_add_dotProduct_mulVec, comp_add_dotProduct_mulVec, TauCeti.map_comp_smul,
    TauCeti.map_comp_smul, smul_dotProduct, smul_dotProduct]
  simp only [α, β, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    hsv₀ s₁ hs₁, hSx s₁ hs₁, hSy s₁ hs₁, hxx, hyy, hxy, hyx]
  linear_combination -σ b * ((σ ∘ y) ⬝ᵥ (Q *ᵥ r)) * hε
private theorem mem_iSup_of_ortho_eq_zero (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q)
    (hε : ε * ε = 1) (hσε : σ ε = ε) {d : K} (hd : d ≠ 0) (hdε : d + ε * σ d = 0) {e f : n → K}
    (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0) (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0) (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1)
    (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε) {S : Submodule K (n → K)}
    (hSe : ∀ s ∈ S, (σ ∘ e) ⬝ᵥ (Q *ᵥ s) = 0) (hSf : ∀ s ∈ S, (σ ∘ f) ⬝ᵥ (Q *ᵥ s) = 0)
    (hproj : ∀ v : n → K, ∃ s ∈ S, ∀ s' ∈ S, (σ ∘ s') ⬝ᵥ (Q *ᵥ (v - s)) = 0)
    (hW_zero : ¬∃ x : n → K, x ≠ 0 ∧ (σ ∘ e) ⬝ᵥ (Q *ᵥ x) = 0 ∧ (σ ∘ f) ⬝ᵥ (Q *ᵥ x) = 0 ∧
      ∀ s ∈ S, (σ ∘ s) ⬝ᵥ (Q *ᵥ x) = 0)
    {g : Q.specialIsometryGroup σ} {c : K} (hc : c ≠ 0)
    (hge : (g : Matrix n n K) *ᵥ e = c • e) (hgf : (g : Matrix n n K) *ᵥ f = (σ c)⁻¹ • f)
    (hgS : ∀ s ∈ S, (g : Matrix n n K) *ᵥ s = s) :
    g ∈ ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p := by
  have hg_ortho (w : n → K) (hew : (σ ∘ e) ⬝ᵥ (Q *ᵥ w) = 0) (hfw : (σ ∘ f) ⬝ᵥ (Q *ᵥ w) = 0) :
      (g : Matrix n n K) *ᵥ w = w := by
    obtain ⟨s, hsS, hsw⟩ := hproj w
    have hw_sub : w - s = 0 := by
      by_contra hne
      exact hW_zero ⟨w - s, hne, by simp [mulVec_sub, dotProduct_sub, hew, hSe s hsS],
        by simp [mulVec_sub, dotProduct_sub, hfw, hSf s hsS], hsw⟩
    rw [sub_eq_zero.mp hw_sub]; exact hgS s hsS
  have hdet1 : (g : Matrix n n K).det = 1 := (g : SpecialLinearGroup n K).prop
  rw [det_eq_of_mulVec_hyperbolic hε he hf hef hfe hge hgf hg_ortho] at hdet1
  have hσc : σ c = c := by
    have hmul := congrArg (· * σ c) hdet1
    rw [inv_mul_cancel_right₀ ((map_ne_zero σ).mpr hc), one_mul] at hmul; exact hmul.symm
  obtain ⟨h, hh, hhe, hhf, hhw⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_hyperbolic_rescale hσ hQ hε hσε hd hdε he hf hef
      hfe hc hσc
  have hg_eq : g = h := Subtype.ext (Subtype.ext (mulVec_injective (funext fun x ↦ by
    set w := x - (ε * ((σ ∘ f) ⬝ᵥ (Q *ᵥ x))) • e - ((σ ∘ e) ⬝ᵥ (Q *ᵥ x)) • f
    have hew : (σ ∘ e) ⬝ᵥ (Q *ᵥ w) = 0 := by
      simp [w, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, he, hef]
    have hfw : (σ ∘ f) ⬝ᵥ (Q *ᵥ w) = 0 := by
      simp only [w, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, hfe, hf]
      linear_combination -((σ ∘ f) ⬝ᵥ (Q *ᵥ x)) * hε
    have hx_eq : x = (ε * ((σ ∘ f) ⬝ᵥ (Q *ᵥ x))) • e + ((σ ∘ e) ⬝ᵥ (Q *ᵥ x)) • f + w := by
      dsimp [w]; module
    rw [hx_eq]; simp only [mulVec_add, mulVec_smul, hge, hgf, hσc, hhe, hhf, hg_ortho w hew hfw,
      hhw w hew hfw])))
  rwa [hg_eq]
private theorem exists_mem_iSup_totally_isotropic_smul (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hadm : ∃ d ≠ 0, d + ε * σ d = 0) {U : Set (n → K)}
    (hW_nd : ∀ w : n → K, (∀ u ∈ U, (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) →
      (∀ w' : n → K, (∀ u ∈ U, (σ ∘ u) ⬝ᵥ (Q *ᵥ w') = 0) → (σ ∘ w') ⬝ᵥ (Q *ᵥ w) = 0) → w = 0)
    (hW_iso : ∀ w : n → K, (∀ u ∈ U, (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) → (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0)
    {x y x' : n → K} (hx'0 : x' ≠ 0) (hxy : (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 1)
    (hxU : ∀ u ∈ U, (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0) (hyU : ∀ u ∈ U, (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0)
    (hx'U : ∀ u ∈ U, (σ ∘ u) ⬝ᵥ (Q *ᵥ x') = 0) :
    ∃ t₂ ∈ ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p, ∃ c₂ ≠ (0 : K),
      (∀ u ∈ U, (t₂ : Matrix n n K) *ᵥ u = u) ∧ (t₂ : Matrix n n K) *ᵥ x' = c₂ • x := by
  by_cases hxx' : (σ ∘ x) ⬝ᵥ (Q *ᵥ x') = 0
  swap
  · exact exists_mem_iSup_unitaryTransvectionSubgroup_fixes_and_mulVec_eq_smul_of_ne_zero
      hσ hQ hadm (hW_iso x' hx'U) (hW_iso x hxU) hx'U hxU hxx'
  obtain ⟨v₁, hv₁U, hv₁x'⟩ :
      ∃ v₁, (∀ u ∈ U, (σ ∘ u) ⬝ᵥ (Q *ᵥ v₁) = 0) ∧ (σ ∘ v₁) ⬝ᵥ (Q *ᵥ x') ≠ 0 := by
    by_contra! hall; exact hx'0 (hW_nd x' hx'U hall)
  obtain ⟨z, hzU, hzx', hxz⟩ :
      ∃ z, (∀ u ∈ U, (σ ∘ u) ⬝ᵥ (Q *ᵥ z) = 0) ∧ (σ ∘ z) ⬝ᵥ (Q *ᵥ x') ≠ 0 ∧
        (σ ∘ x) ⬝ᵥ (Q *ᵥ z) ≠ 0 := by
    by_cases hxv₁ : (σ ∘ x) ⬝ᵥ (Q *ᵥ v₁) = 0
    · by_cases hyx' : (σ ∘ y) ⬝ᵥ (Q *ᵥ x') = 0
      · exact ⟨v₁ + y, fun u hu ↦ by rw [mulVec_add, dotProduct_add, hv₁U u hu, hyU u hu, add_zero],
          by rwa [comp_add_dotProduct_mulVec, hyx', add_zero],
          by rw [mulVec_add, dotProduct_add, hxv₁, zero_add, hxy]; exact one_ne_zero⟩
      · exact ⟨y, hyU, hyx', hxy ▸ one_ne_zero⟩
    · exact ⟨v₁, hv₁U, hv₁x', hxv₁⟩
  obtain ⟨t₂a, ht₂a, c₂a, hc₂a, ht₂aU, ht₂ax'⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_fixes_and_mulVec_eq_smul_of_ne_zero hσ hQ hadm
      (hW_iso x' hx'U) (hW_iso z hzU) hx'U hzU hzx'
  obtain ⟨t₂b, ht₂b, c₂b, hc₂b, ht₂bU, ht₂bz⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_fixes_and_mulVec_eq_smul_of_ne_zero hσ hQ hadm
      (hW_iso z hzU) (hW_iso x hxU) hzU hxU hxz
  exact ⟨t₂b * t₂a, mul_mem ht₂b ht₂a, c₂a * c₂b, mul_ne_zero hc₂a hc₂b,
    fun u hu ↦ by rw [coe_mul_mulVec, ht₂aU u hu, ht₂bU u hu],
    by rw [coe_mul_mulVec, ht₂ax', mulVec_smul, ht₂bz, smul_smul]⟩
omit [DecidableEq n] in
private theorem exists_hyperbolic_partner_of_totally_isotropic (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) {U : Set (n → K)}
    (hW_nd : ∀ w : n → K, (∀ u ∈ U, (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) →
      (∀ w' : n → K, (∀ u ∈ U, (σ ∘ u) ⬝ᵥ (Q *ᵥ w') = 0) → (σ ∘ w') ⬝ᵥ (Q *ᵥ w) = 0) → w = 0)
    (hW_iso : ∀ w : n → K, (∀ u ∈ U, (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) → (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0)
    {x : n → K} (hx0 : x ≠ 0) (hxU : ∀ u ∈ U, (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0) :
    ∃ y : n → K, (∀ u ∈ U, (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0) ∧
      (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 1 ∧ (σ ∘ y) ⬝ᵥ (Q *ᵥ x) = ε ∧ ∀ a : K, σ a = a := by
  obtain ⟨y₀, hy₀U, hy₀x⟩ : ∃ y₀, (∀ u ∈ U, (σ ∘ u) ⬝ᵥ (Q *ᵥ y₀) = 0) ∧ (σ ∘ y₀) ⬝ᵥ (Q *ᵥ x) ≠ 0 :=
    by by_contra! hall; exact hx0 (hW_nd x hxU hall)
  have hxy₀ : (σ ∘ x) ⬝ᵥ (Q *ᵥ y₀) ≠ 0 := (comp_dotProduct_mulVec_ne_zero_comm hσ hQ).mpr hy₀x
  set y := ((σ ∘ x) ⬝ᵥ (Q *ᵥ y₀))⁻¹ • y₀
  have hyU (u : n → K) (hu : u ∈ U) : (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0 := by
    rw [mulVec_smul, dotProduct_smul, hy₀U u hu, smul_zero]
  have hxx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0 := hW_iso x hxU
  have hyy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0 := hW_iso y hyU
  have hxy : (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 1 := by
    rw [mulVec_smul, dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hxy₀]
  have hyx : (σ ∘ y) ⬝ᵥ (Q *ᵥ x) = ε := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε, hxy, map_one, mul_one]
  have htr_zero (a : K) : a + ε * σ a = 0 := by
    have hiso := hW_iso (x + a • y) fun u hu ↦ by
      simp [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, hxU u hu, hyU u hu]
    simp only [map_comp_add, TauCeti.map_comp_smul, add_dotProduct, smul_dotProduct, mulVec_add,
      mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, hxx, hyy, hxy, hyx, mul_zero,
      mul_one, add_zero, zero_add] at hiso
    linear_combination hiso
  exact ⟨y, hyU, hxy, hyx, fun a ↦ by
    have h1 := htr_zero 1; rw [map_one, mul_one] at h1
    linear_combination h1 * σ a - htr_zero a⟩
private theorem mulVec_anisotropic_eq_smul_of_fixes_ortho (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0) (hε : ε * ε = 1) {e f v : n → K}
    (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0) (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0) (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1)
    (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε) (hev : (σ ∘ e) ⬝ᵥ (Q *ᵥ v) = 0) (hfv : (σ ∘ f) ⬝ᵥ (Q *ᵥ v) = 0)
    (hvv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) ≠ 0) {r₀ : Q.specialIsometryGroup σ} {c₁ c₂ : K} (hc₁ : c₁ ≠ 0)
    (hc₂ : c₂ ≠ 0) (hr₀e : (r₀ : Matrix n n K) *ᵥ e = c₁ • e)
    (hr₀f : (r₀ : Matrix n n K) *ᵥ f = c₂ • f)
    (hr₀w : ∀ w : n → K, (σ ∘ e) ⬝ᵥ (Q *ᵥ w) = 0 → (σ ∘ f) ⬝ᵥ (Q *ᵥ w) = 0 →
      (σ ∘ v) ⬝ᵥ (Q *ᵥ w) = 0 → (r₀ : Matrix n n K) *ᵥ w = w) :
    ∃ μ' : K, (r₀ : Matrix n n K) *ᵥ v = μ' • v := by
  have hve := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hev
  have hvf := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hfv
  set rv := (r₀ : Matrix n n K) *ᵥ v
  have herv : (σ ∘ e) ⬝ᵥ (Q *ᵥ rv) = 0 := comp_dotProduct_mulVec_mulVec_eq_zero_of_smul hc₁ hr₀e hev
  have hfrv : (σ ∘ f) ⬝ᵥ (Q *ᵥ rv) = 0 := comp_dotProduct_mulVec_mulVec_eq_zero_of_smul hc₂ hr₀f hfv
  set μ' := ((σ ∘ v) ⬝ᵥ (Q *ᵥ v))⁻¹ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ rv))
  refine ⟨μ', ?_⟩
  by_contra hne
  have hd_ne : rv - μ' • v ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨y, hy, -⟩ := exists_comp_dotProduct_mulVec_ne_zero_pair (σ := σ) hdet hd_ne hd_ne
  set w := y - (ε * ((σ ∘ f) ⬝ᵥ (Q *ᵥ y))) • e - ((σ ∘ e) ⬝ᵥ (Q *ᵥ y)) • f -
    (((σ ∘ v) ⬝ᵥ (Q *ᵥ v))⁻¹ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ y))) • v
  have hew : (σ ∘ e) ⬝ᵥ (Q *ᵥ w) = 0 := by
    simp [w, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, he, hef, hev]
  have hfw : (σ ∘ f) ⬝ᵥ (Q *ᵥ w) = 0 := by
    simp only [w, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, hfe, hf,
      hfv]
    linear_combination -((σ ∘ f) ⬝ᵥ (Q *ᵥ y)) * hε
  have hvw : (σ ∘ v) ⬝ᵥ (Q *ᵥ w) = 0 := by
    simp only [w, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, hve, hvf]
    field_simp; ring
  have hwrv : (σ ∘ w) ⬝ᵥ (Q *ᵥ rv) = 0 := by
    rw [← hr₀w w hew hfw hvw,
      comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp r₀.2),
      (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hvw]
  have hwv := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hvw
  have hvd : (σ ∘ v) ⬝ᵥ (Q *ᵥ rv) - μ' * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v)) = 0 := by
    simp only [μ']; field_simp; ring
  have hy_eq : y = w + (ε * ((σ ∘ f) ⬝ᵥ (Q *ᵥ y))) • e + ((σ ∘ e) ⬝ᵥ (Q *ᵥ y)) • f +
      (((σ ∘ v) ⬝ᵥ (Q *ᵥ v))⁻¹ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ y))) • v := by dsimp [w]; module
  refine hy ?_
  rw [hy_eq]
  simp only [map_comp_add, TauCeti.map_comp_smul, add_dotProduct, smul_dotProduct, mulVec_sub,
    mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, herv, hev, hfrv, hfv, hwrv, hwv,
    mul_zero, add_zero, zero_add]
  linear_combination σ (((σ ∘ v) ⬝ᵥ (Q *ᵥ v))⁻¹ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ y))) * hvd
private theorem mulVec_eq_self_of_three_siegel {e f v z u₂ w₁ w₂ w₃ : n → K}
    (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε) {d τ c₀ c₁ c₂ c₃ : K} (hε0 : ε ≠ 0) (hστ0 : σ τ ≠ 0)
    (hσc₀ : σ c₀ ≠ 0) (hz_def : z = e + (σ τ + d) • f + τ • v) (hu₂_def : u₂ = e + d • f)
    {s₁ s₂ s₃ : SpecialLinearGroup n K} (hs₂ : s₂ ∈ Q.specialIsometryGroup σ)
    (hcs₁ : (s₁ : Matrix n n K) = Q.siegelTransvection σ ε f w₁ c₁)
    (hcs₂ : (s₂ : Matrix n n K) = Q.siegelTransvection σ ε u₂ w₂ c₂)
    (hcs₃ : (s₃ : Matrix n n K) = Q.siegelTransvection σ ε e w₃ c₃)
    (hs₁e : (s₁ : Matrix n n K) *ᵥ e = z) (hs₂z : (s₂ : Matrix n n K) *ᵥ z = c₀ • e)
    (hs₃f : (s₃ : Matrix n n K) *ᵥ ((s₂ : Matrix n n K) *ᵥ f) = (σ c₀)⁻¹ • f)
    (hu₂z : (σ ∘ u₂) ⬝ᵥ (Q *ᵥ z) = σ τ)
    (hes₂f : (σ ∘ e) ⬝ᵥ (Q *ᵥ ((s₂ : Matrix n n K) *ᵥ f)) = (σ c₀)⁻¹) {w : n → K}
    (hew : (σ ∘ e) ⬝ᵥ (Q *ᵥ w) = 0) (hfw : (σ ∘ f) ⬝ᵥ (Q *ᵥ w) = 0) (hvw : (σ ∘ v) ⬝ᵥ (Q *ᵥ w) = 0)
    :
    (s₃ : Matrix n n K) *ᵥ ((s₂ : Matrix n n K) *ᵥ ((s₁ : Matrix n n K) *ᵥ w)) = w := by
  have hzw : (σ ∘ z) ⬝ᵥ (Q *ᵥ w) = 0 := by
    simp [hz_def, map_comp_add, TauCeti.map_comp_smul, add_dotProduct, smul_dotProduct, hew, hfw,
      hvw]
  have hw₁ : (s₁ : Matrix n n K) *ᵥ w = w := by
    rw [hcs₁]
    exact siegelTransvection_mulVec_eq_self_of_ortho (hfe ▸ hε0) (hcs₁ ▸ hs₁e) hfw hew hzw
  have hw₂ : (s₂ : Matrix n n K) *ᵥ w = w := by
    rw [hcs₂]; exact siegelTransvection_mulVec_eq_self_of_ortho (hu₂z ▸ hστ0) (hcs₂ ▸ hs₂z)
      (by simp [hu₂_def, map_comp_add, TauCeti.map_comp_smul, add_dotProduct, smul_dotProduct, hew,
        hfw]) hzw (by simp [TauCeti.map_comp_smul, hew])
  have hw₃ : (s₃ : Matrix n n K) *ᵥ w = w := by
    rw [hcs₃]
    exact siegelTransvection_mulVec_eq_self_of_ortho (hes₂f ▸ inv_ne_zero hσc₀) (hcs₃ ▸ hs₃f) hew
      (by rw [← hw₂, comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp hs₂),
        hfw]) (by simp [TauCeti.map_comp_smul, hfw])
  rw [hw₁, hw₂, hw₃]
section Generation

variable (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
  (hε : ε * ε = 1) (hσε : σ ε = ε) (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
  {d : K} (hd : d ≠ 0) (hdε : d + ε * σ d = 0)
  {e f : n → K} (he₀ : e ≠ 0) (he : (σ ∘ e) ⬝ᵥ (Q *ᵥ e) = 0)
  (hf : (σ ∘ f) ⬝ᵥ (Q *ᵥ f) = 0) (hef : (σ ∘ e) ⬝ᵥ (Q *ᵥ f) = 1)
  (hfe : (σ ∘ f) ⬝ᵥ (Q *ᵥ e) = ε)
  (hgen : (∃ a : K, a ≠ 0 ∧ a ≠ 1 ∧ σ a = a) ∨ Fintype.card n ≤ 2 ∨
    ∃ u w : n → K, u ≠ 0 ∧ w ∉ K ∙ u ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 ∧
      (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0)
include hσ hQ hdet hε hσε htr hd hdε he₀ he hf hef hfe hgen
private theorem exists_mem_iSup_compensated_reflection_aux {v : n → K}
    (hev : (σ ∘ e) ⬝ᵥ (Q *ᵥ v) = 0) (hfv : (σ ∘ f) ⬝ᵥ (Q *ᵥ v) = 0) {τ : K} (hτ0 : τ ≠ 0)
    (hτ : τ + ε * σ τ + ε * τ * σ τ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v)) = 0) :
    ∃ r₀ ∈ ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p,
      (r₀ : Matrix n n K) *ᵥ e = (-(d⁻¹ * σ τ)) • e ∧
      (r₀ : Matrix n n K) *ᵥ f = (σ (-(d⁻¹ * σ τ)))⁻¹ • f ∧
      ∀ w : n → K, (σ ∘ e) ⬝ᵥ (Q *ᵥ w) = 0 → (σ ∘ f) ⬝ᵥ (Q *ᵥ w) = 0 →
        (σ ∘ v) ⬝ᵥ (Q *ᵥ w) = 0 → (r₀ : Matrix n n K) *ᵥ w = w := by
  have hve := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hev
  have hvf := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hfv
  have hε0 : ε ≠ 0 := left_ne_zero_of_mul (hε ▸ one_ne_zero)
  have hστ0 : σ τ ≠ 0 := (map_ne_zero σ).mpr hτ0; set c₀ := -(d⁻¹ * σ τ)
  have hσc₀ : σ c₀ ≠ 0 := (map_ne_zero σ).mpr (neg_ne_zero.mpr (mul_ne_zero (inv_ne_zero hd) hστ0))
  set z := e + (σ τ + d) • f + τ • v
  have hz : (σ ∘ z) ⬝ᵥ (Q *ᵥ z) = 0 := by
    simp only [z, map_comp_add, TauCeti.map_comp_smul, map_add, hσ τ, add_dotProduct,
      smul_dotProduct, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, he,
      hf, hef, hfe, hev, hfv, hve, hvf, mul_zero, add_zero, mul_one]
    linear_combination ε * hτ - (σ τ + τ * σ τ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v))) * hε + hdε
  set u₂ := e + d • f
  have hu₂ : (σ ∘ u₂) ⬝ᵥ (Q *ᵥ u₂) = 0 := by
    simp only [u₂, map_comp_add, TauCeti.map_comp_smul, add_dotProduct, smul_dotProduct, mulVec_add,
      mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, he, hf, hef, hfe]
    linear_combination hdε
  have hu₂z : (σ ∘ u₂) ⬝ᵥ (Q *ᵥ z) = σ τ := by
    simp only [u₂, z, map_comp_add, TauCeti.map_comp_smul, add_dotProduct, smul_dotProduct,
      mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, he, hf, hef, hfe, hev,
      hfv]; linear_combination hdε
  have hu₂ce : (σ ∘ u₂) ⬝ᵥ (Q *ᵥ (c₀ • e)) = σ τ := by
    simp only [u₂, c₀, map_comp_add, TauCeti.map_comp_smul, add_dotProduct, smul_dotProduct,
      mulVec_smul, dotProduct_smul, smul_eq_mul, he, hfe]
    linear_combination -d⁻¹ * σ τ * hdε + σ τ * inv_mul_cancel₀ hd
  obtain ⟨s₁, hs₁, w₁, c₁, hfw₁, hc₁, hcs₁, hs₁f, hs₁e⟩ :=
    exists_mem_specialIsometryGroup_coe_eq_siegelTransvection_mulVec_eq_self_and_mulVec_eq hσ hQ hf
      he hz (hfe ▸ hε0) (by simp [z, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, hfe,
        hf, hfv])
  obtain ⟨s₂, hs₂, w₂, c₂, hu₂w₂, hc₂, hcs₂, -, hs₂z⟩ :=
    exists_mem_specialIsometryGroup_coe_eq_siegelTransvection_mulVec_eq_self_and_mulVec_eq
      (y := c₀ • e) hσ hQ hu₂ hz (by rw [comp_smul_dotProduct_mulVec_smul, he, mul_zero])
      (hu₂z ▸ hστ0) (hu₂z.trans hu₂ce.symm)
  have hes₂f : (σ ∘ e) ⬝ᵥ (Q *ᵥ ((s₂ : Matrix n n K) *ᵥ f)) = (σ c₀)⁻¹ := by
    have hpair := (comp_mulVec_dotProduct_mulVec_mulVec
      (mem_specialIsometryGroup_iff.mp (mul_mem hs₂ hs₁)) e f).trans hef
    rw [SpecialLinearGroup.coe_mul, ← mulVec_mulVec, ← mulVec_mulVec, hs₁e, hs₂z, hs₁f,
      TauCeti.map_comp_smul, smul_dotProduct, smul_eq_mul] at hpair
    exact eq_inv_of_mul_eq_one_right hpair
  obtain ⟨s₃, hs₃, w₃, c₃, hew₃, hc₃, hcs₃, hs₃e, hs₃f⟩ :=
    exists_mem_specialIsometryGroup_coe_eq_siegelTransvection_mulVec_eq_self_and_mulVec_eq
      (y := (σ c₀)⁻¹ • f) hσ hQ he ((comp_mulVec_dotProduct_mulVec_mulVec
        (mem_specialIsometryGroup_iff.mp hs₂) f f).trans hf)
      (by rw [comp_smul_dotProduct_mulVec_smul, hf, mul_zero]) (hes₂f ▸ inv_ne_zero hσc₀)
      (by rw [hes₂f, mulVec_smul, dotProduct_smul, hef, smul_eq_mul, mul_one])
  have hmem := @siegelTransvection_mem_iSup_unitaryTransvectionSubgroup n K _ _ _ Q σ ε hσ hQ hdet
    hε hσε htr d hd hdε e f he₀ he hf hef hfe hgen
  refine ⟨⟨s₃, hs₃⟩ * ⟨s₂, hs₂⟩ * ⟨s₁, hs₁⟩, mul_mem (mul_mem (hmem he hew₃ hc₃ hs₃ hcs₃)
    (hmem hu₂ hu₂w₂ hc₂ hs₂ hcs₂)) (hmem hf hfw₁ hc₁ hs₁ hcs₁),
    by rw [coe_mul_mulVec, coe_mul_mulVec, hs₁e, hs₂z, mulVec_smul, hs₃e],
    by rw [coe_mul_mulVec, coe_mul_mulVec, hs₁f, hs₃f], fun w hew hfw hvw ↦ ?_⟩
  rw [coe_mul_mulVec, coe_mul_mulVec]; exact mulVec_eq_self_of_three_siegel hfe hε0 hστ0 hσc₀ rfl
    rfl hs₂ hcs₁ hcs₂ hcs₃ hs₁e hs₂z hs₃f hu₂z hes₂f hew hfw hvw
private theorem exists_mem_iSup_compensated_reflection {v : n → K} (hev : (σ ∘ e) ⬝ᵥ (Q *ᵥ v) = 0)
    (hfv : (σ ∘ f) ⬝ᵥ (Q *ᵥ v) = 0) (hvv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) ≠ 0) {τ : K} (hτ0 : τ ≠ 0)
    (hτ : τ + ε * σ τ + ε * τ * σ τ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v)) = 0) :
    ∃ r ∈ ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p, ∃ c₀ ≠ (0 : K),
      (r : Matrix n n K) *ᵥ e = c₀ • e ∧ (r : Matrix n n K) *ᵥ f = (σ c₀)⁻¹ • f ∧
      ∀ x : n → K, (σ ∘ e) ⬝ᵥ (Q *ᵥ x) = 0 → (σ ∘ f) ⬝ᵥ (Q *ᵥ x) = 0 →
        (r : Matrix n n K) *ᵥ x = x + (τ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ x))) • v := by
  obtain ⟨r₀, hr₀_mem, hr₀e, hr₀f, hr₀w⟩ :=
    exists_mem_iSup_compensated_reflection_aux hσ hQ hdet hε hσε htr hd hdε he₀ he hf hef hfe hgen
      hev hfv hτ0 hτ
  set c₀ := -(d⁻¹ * σ τ)
  have hc₀ : c₀ ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (inv_ne_zero hd) ((map_ne_zero σ).mpr hτ0))
  have hσc₀ : σ c₀ ≠ 0 := (map_ne_zero σ).mpr hc₀
  obtain ⟨μ', hrv_eq⟩ := mulVec_anisotropic_eq_smul_of_fixes_ortho hσ hQ hdet hε he hf hef hfe hev
    hfv hvv hc₀ (inv_ne_zero hσc₀) hr₀e hr₀f hr₀w
  set μ := 1 + τ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v))
  have hdet1 : (r₀ : Matrix n n K).det = 1 := (r₀ : SpecialLinearGroup n K).prop
  rw [det_eq_of_mulVec_hyperbolic_anisotropic hσ hQ hε he hf hef hfe hev hfv hvv hr₀e hr₀f hrv_eq
    hr₀w] at hdet1
  have hσc₀_eq : σ c₀ = c₀ * μ := by
    have hσd_eq : σ d = -(ε * d) := by linear_combination ε * hdε - σ d * hε
    have hε_inv : ε⁻¹ = ε := inv_eq_of_mul_eq_one_right hε
    simp only [c₀, μ, map_neg, map_mul, map_inv₀, hσ τ, hσd_eq, inv_neg, mul_inv, hε_inv]
    field_simp; linear_combination ε * hτ - (σ τ + τ * σ τ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v))) * hε
  have hμ0 : μ ≠ 0 := right_ne_zero_of_mul (hσc₀_eq ▸ hσc₀)
  have hc₀μ : c₀ * (σ c₀)⁻¹ * μ = 1 := by rw [hσc₀_eq]; field_simp
  have hμ_eq : μ' = μ :=
    mul_left_cancel₀ (mul_ne_zero hc₀ (inv_ne_zero hσc₀)) (hdet1.trans hc₀μ.symm)
  have hrv' : (r₀ : Matrix n n K) *ᵥ v = μ • v := hrv_eq.trans (hμ_eq ▸ rfl)
  refine ⟨r₀, hr₀_mem, c₀, hc₀, hr₀e, hr₀f, fun x hex hfx ↦ ?_⟩
  set w := x - (((σ ∘ v) ⬝ᵥ (Q *ᵥ v))⁻¹ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ x))) • v
  have hrw := hr₀w w
    (by simp [w, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hex, hev])
    (by simp [w, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hfx, hfv])
    (by simp only [w, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
        field_simp; ring)
  have hx_eq : x = (((σ ∘ v) ⬝ᵥ (Q *ᵥ v))⁻¹ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ x))) • v + w := by
    dsimp [w]; module
  conv_lhs => rw [hx_eq, mulVec_add, mulVec_smul, hrv', hrw]
  simp only [μ, w, smul_smul]
  have hcancel : ((σ ∘ v) ⬝ᵥ (Q *ᵥ v))⁻¹ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ x)) *
      (1 + τ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v))) =
      ((σ ∘ v) ⬝ᵥ (Q *ᵥ v))⁻¹ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ x)) + τ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ x)) := by field_simp
  rw [hcancel]; module
private theorem exists_mem_iSup_anisotropic_pair_ne {S : Submodule K (n → K)}
    (hSe : ∀ s ∈ S, (σ ∘ e) ⬝ᵥ (Q *ᵥ s) = 0) (hSf : ∀ s ∈ S, (σ ∘ f) ⬝ᵥ (Q *ᵥ s) = 0)
    {g : Q.specialIsometryGroup σ} {c : K} (hc : c ≠ 0) (hge : (g : Matrix n n K) *ᵥ e = c • e)
    (hgf : (g : Matrix n n K) *ᵥ f = (σ c)⁻¹ • f) (hgS : ∀ s ∈ S, (g : Matrix n n K) *ᵥ s = s)
    {x : n → K} (hex : (σ ∘ e) ⬝ᵥ (Q *ᵥ x) = 0) (hfx : (σ ∘ f) ⬝ᵥ (Q *ᵥ x) = 0)
    (hSx : ∀ s ∈ S, (σ ∘ s) ⬝ᵥ (Q *ᵥ x) = 0) (hxx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) ≠ 0) :
    ∃ t₁ ∈ ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p, ∃ c₁ ≠ (0 : K),
      (↑(t₁ * g) : Matrix n n K) *ᵥ e = c₁ • e ∧ (↑(t₁ * g) : Matrix n n K) *ᵥ f = (σ c₁)⁻¹ • f ∧
      (∀ s ∈ S, (↑(t₁ * g) : Matrix n n K) *ᵥ s = s) ∧
      (σ ∘ ((↑(t₁ * g) : Matrix n n K) *ᵥ x)) ⬝ᵥ (Q *ᵥ x) ≠
        (σ ∘ x) ⬝ᵥ (Q *ᵥ x) := by
  by_cases hgx : (σ ∘ ((g : Matrix n n K) *ᵥ x)) ⬝ᵥ (Q *ᵥ x) = (σ ∘ x) ⬝ᵥ (Q *ᵥ x)
  swap
  · exact ⟨1, one_mem _, c, hc, by simpa using hge, by simpa using hgf,
      fun s hs ↦ by simpa using hgS s hs, by simpa using hgx⟩
  obtain ⟨β, hβ⟩ := htr ((σ ∘ x) ⬝ᵥ (Q *ᵥ x)) (apply_comp_dotProduct_mulVec hσ hQ x x)
  have hβ0 : β ≠ 0 := fun h0 ↦ hxx (by simpa [h0] using hβ.symm)
  have hσβ0 : σ β ≠ 0 := (map_ne_zero σ).mpr hβ0; set τ₁ := -β⁻¹
  have hτ₁0 : τ₁ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hβ0)
  have hτ₁ : τ₁ + ε * σ τ₁ + ε * τ₁ * σ τ₁ * ((σ ∘ x) ⬝ᵥ (Q *ᵥ x)) = 0 := by
    simp only [τ₁, ← hβ, map_neg, map_inv₀]; field_simp; linear_combination σ β * hε
  obtain ⟨r₁, hr₁, c₁', hc₁', hr₁e, hr₁f, hr₁w⟩ :=
    exists_mem_iSup_compensated_reflection hσ hQ hdet hε hσε htr hd hdε he₀ he hf hef hfe hgen
      hex hfx hxx hτ₁0 hτ₁
  have he_gx := comp_dotProduct_mulVec_mulVec_eq_zero_of_smul hc hge hex
  have hf_gx := comp_dotProduct_mulVec_mulVec_eq_zero_of_smul (inv_ne_zero ((map_ne_zero σ).mpr hc))
    hgf hfx
  refine ⟨r₁, hr₁, c₁' * c, mul_ne_zero hc₁' hc,
    by rw [coe_mul_mulVec, hge, mulVec_smul, hr₁e, smul_smul, mul_comm],
    by rw [coe_mul_mulVec, hgf, mulVec_smul, hr₁f, smul_smul, map_mul, mul_inv, mul_comm],
    fun s hs ↦ by rw [coe_mul_mulVec, hgS s hs, hr₁w s (hSe s hs) (hSf s hs),
      (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (hSx s hs), mul_zero, zero_smul, add_zero],
    ?_⟩
  rw [coe_mul_mulVec, hr₁w _ he_gx hf_gx, comp_add_dotProduct_mulVec, TauCeti.map_comp_smul,
    smul_dotProduct, smul_eq_mul, hgx]
  have hxgx : (σ ∘ x) ⬝ᵥ (Q *ᵥ ((g : Matrix n n K) *ᵥ x)) = (σ ∘ x) ⬝ᵥ (Q *ᵥ x) := by
    have h1 := congrArg σ hgx
    rw [apply_comp_dotProduct_mulVec hσ hQ, apply_comp_dotProduct_mulVec hσ hQ] at h1
    exact mul_left_cancel₀ (left_ne_zero_of_mul (hε ▸ one_ne_zero)) h1
  rw [hxgx]; exact fun h_eq ↦ mul_ne_zero ((map_ne_zero σ).mpr (mul_ne_zero hτ₁0 hxx)) hxx
    (by linear_combination h_eq)
private theorem exists_mem_iSup_anisotropic_step_two {v : n → K} (hev : (σ ∘ e) ⬝ᵥ (Q *ᵥ v) = 0)
    (hfv : (σ ∘ f) ⬝ᵥ (Q *ᵥ v) = 0) {α : K} (hα0 : α ≠ 0)
    (hbvv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = -(α + ε * σ α)) :
    ∃ r₂ ∈ ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p, ∃ c₂' ≠ (0 : K),
      (r₂ : Matrix n n K) *ᵥ e = c₂' • e ∧ (r₂ : Matrix n n K) *ᵥ f = (σ c₂')⁻¹ • f ∧
      ∀ x : n → K, (σ ∘ e) ⬝ᵥ (Q *ᵥ x) = 0 → (σ ∘ f) ⬝ᵥ (Q *ᵥ x) = 0 →
        (r₂ : Matrix n n K) *ᵥ x = x + (α⁻¹ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ x))) • v := by
  have hσα0 : σ α ≠ 0 := (map_ne_zero σ).mpr hα0
  by_cases hvv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0
  · have hα_adm : α⁻¹ + ε * σ α⁻¹ = 0 := by
      have h1 : α + ε * σ α = 0 := by linear_combination hbvv - hvv
      rw [map_inv₀]; field_simp; linear_combination ε * h1 - σ α * hε
    obtain ⟨r₂, hr₂, hcr₂⟩ :=
      exists_mem_iSup_unitaryTransvectionSubgroup_coe_eq_unitaryTransvection hσ hQ hvv hα_adm
    exact ⟨r₂, hr₂, 1, one_ne_zero, by simp [hcr₂, unitaryTransvection_mulVec,
        (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hev],
      by simp [hcr₂, unitaryTransvection_mulVec,
        (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hfv],
      fun x _ _ ↦ by rw [hcr₂, unitaryTransvection_mulVec]⟩
  · have hτ₂ : α⁻¹ + ε * σ α⁻¹ + ε * α⁻¹ * σ α⁻¹ * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v)) = 0 := by
      rw [hbvv, map_inv₀]; field_simp; linear_combination -σ α * hε
    exact exists_mem_iSup_compensated_reflection hσ hQ hdet hε hσε htr hd hdε he₀ he hf hef hfe hgen
      hev hfv hvv (inv_ne_zero hα0) hτ₂
private theorem exists_mem_iSup_fixes_anisotropic {S : Submodule K (n → K)}
    (hSe : ∀ s ∈ S, (σ ∘ e) ⬝ᵥ (Q *ᵥ s) = 0) (hSf : ∀ s ∈ S, (σ ∘ f) ⬝ᵥ (Q *ᵥ s) = 0)
    {g : Q.specialIsometryGroup σ} {c : K} (hc : c ≠ 0) (hge : (g : Matrix n n K) *ᵥ e = c • e)
    (hgf : (g : Matrix n n K) *ᵥ f = (σ c)⁻¹ • f) (hgS : ∀ s ∈ S, (g : Matrix n n K) *ᵥ s = s)
    {x : n → K} (hex : (σ ∘ e) ⬝ᵥ (Q *ᵥ x) = 0) (hfx : (σ ∘ f) ⬝ᵥ (Q *ᵥ x) = 0)
    (hSx : ∀ s ∈ S, (σ ∘ s) ⬝ᵥ (Q *ᵥ x) = 0) (hxx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) ≠ 0) :
    ∃ t ∈ ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p, ∃ c' ≠ (0 : K),
      (↑(t * g) : Matrix n n K) *ᵥ e = c' • e ∧ (↑(t * g) : Matrix n n K) *ᵥ f = (σ c')⁻¹ • f ∧
      (∀ s ∈ S, (↑(t * g) : Matrix n n K) *ᵥ s = s) ∧ (↑(t * g) : Matrix n n K) *ᵥ x = x := by
  obtain ⟨t₁, ht₁, c₁, hc₁, hge₁, hgf₁, hgS₁, hne₁⟩ :=
    exists_mem_iSup_anisotropic_pair_ne hσ hQ hdet hε hσε htr hd hdε he₀ he hf hef hfe hgen hSe hSf
      hc hge hgf hgS hex hfx hSx hxx
  let g₁ := t₁ * g; set y := (g₁ : Matrix n n K) *ᵥ x; set v := y - x
  have hyy := comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g₁.2) x x
  have hev : (σ ∘ e) ⬝ᵥ (Q *ᵥ v) = 0 := by
    rw [mulVec_sub, dotProduct_sub, comp_dotProduct_mulVec_mulVec_eq_zero_of_smul hc₁ hge₁ hex, hex,
      sub_zero]
  have hfv : (σ ∘ f) ⬝ᵥ (Q *ᵥ v) = 0 := by
    rw [mulVec_sub, dotProduct_sub, comp_dotProduct_mulVec_mulVec_eq_zero_of_smul
      (inv_ne_zero ((map_ne_zero σ).mpr hc₁)) hgf₁ hfx, hfx, sub_zero]
  have hvs (s : n → K) (hs : s ∈ S) : (σ ∘ v) ⬝ᵥ (Q *ᵥ s) = 0 := by
    have hsy : (σ ∘ s) ⬝ᵥ (Q *ᵥ y) = 0 := by
      rw [← hgS₁ s hs, comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g₁.2),
        hSx s hs]
    exact (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp
      (by simp [v, mulVec_sub, dotProduct_sub, hsy, hSx s hs])
  set α := (σ ∘ v) ⬝ᵥ (Q *ᵥ x)
  have hα0 : α ≠ 0 := by simpa [α, v, map_comp_sub, sub_dotProduct, sub_ne_zero] using hne₁
  have hbvv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = -(α + ε * σ α) := by
    have hσα : ε * σ α = (σ ∘ x) ⬝ᵥ (Q *ᵥ y) - (σ ∘ x) ⬝ᵥ (Q *ᵥ x) := by
      simp only [α, v, map_comp_sub, sub_dotProduct, map_sub, apply_comp_dotProduct_mulVec hσ hQ]
      linear_combination (((σ ∘ x) ⬝ᵥ (Q *ᵥ y)) - ((σ ∘ x) ⬝ᵥ (Q *ᵥ x))) * hε
    simp only [v, y, α, map_comp_sub, sub_dotProduct, mulVec_sub, dotProduct_sub, hyy] at hσα ⊢
    linear_combination hσα
  obtain ⟨r₂, hr₂, c₂', hc₂', hr₂e, hr₂f, hr₂w⟩ :=
    exists_mem_iSup_anisotropic_step_two hσ hQ hdet hε hσε htr hd hdε he₀ he hf hef hfe hgen hev hfv
      hα0 hbvv
  have hr₂x : (r₂ : Matrix n n K) *ᵥ x = y := by
    rw [hr₂w x hex hfx, inv_mul_cancel₀ hα0, one_smul]; dsimp [v]; abel
  refine ⟨r₂⁻¹ * t₁, mul_mem (inv_mem hr₂) ht₁, c₂'⁻¹ * c₁, mul_ne_zero (inv_ne_zero hc₂') hc₁,
    ?_, ?_, fun s hs ↦ ?_,
    by rw [mul_assoc, coe_mul_mulVec]; exact coe_inv_mulVec_of_mulVec_eq hr₂x⟩
  · rw [mul_assoc, coe_mul_mulVec, hge₁]
    exact coe_inv_mulVec_of_mulVec_eq
      (by rw [mulVec_smul, hr₂e, smul_smul, mul_right_comm, inv_mul_cancel₀ hc₂', one_mul])
  · rw [mul_assoc, coe_mul_mulVec, hgf₁]
    exact coe_inv_mulVec_of_mulVec_eq (by
      rw [mulVec_smul, hr₂f, smul_smul, map_mul, map_inv₀, mul_inv, inv_inv, mul_right_comm,
        mul_inv_cancel₀ ((map_ne_zero σ).mpr hc₂'), one_mul])
  · rw [mul_assoc, coe_mul_mulVec, hgS₁ s hs]
    exact coe_inv_mulVec_of_mulVec_eq
      (by rw [hr₂w s (hSe s hs) (hSf s hs), hvs s hs, mul_zero, zero_smul, add_zero])
private theorem exists_mem_iSup_fixes_totally_isotropic {S : Submodule K (n → K)}
    (hSe : ∀ s ∈ S, (σ ∘ e) ⬝ᵥ (Q *ᵥ s) = 0) (hSf : ∀ s ∈ S, (σ ∘ f) ⬝ᵥ (Q *ᵥ s) = 0)
    (hW_nd : ∀ w : n → K, (∀ u ∈ insert e (insert f (S : Set (n → K))), (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) →
      (∀ w' : n → K, (∀ u ∈ insert e (insert f (S : Set (n → K))), (σ ∘ u) ⬝ᵥ (Q *ᵥ w') = 0) →
        (σ ∘ w') ⬝ᵥ (Q *ᵥ w) = 0) → w = 0)
    (hW_iso : ∀ w : n → K, (∀ u ∈ insert e (insert f (S : Set (n → K))), (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) →
      (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0)
    {g : Q.specialIsometryGroup σ} {c : K} (hc : c ≠ 0)
    (hge : (g : Matrix n n K) *ᵥ e = c • e) (hgf : (g : Matrix n n K) *ᵥ f = (σ c)⁻¹ • f)
    (hgS : ∀ s ∈ S, (g : Matrix n n K) *ᵥ s = s) {x : n → K} (hx0 : x ≠ 0)
    (hxU : ∀ u ∈ insert e (insert f (S : Set (n → K))), (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0) :
    ∃ y : n → K, (∀ u ∈ insert e (insert f (S : Set (n → K))), (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0) ∧
      (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 1 ∧ (σ ∘ y) ⬝ᵥ (Q *ᵥ x) = ε ∧
      ∃ t ∈ ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p,
        (∀ u ∈ insert e (insert f (S : Set (n → K))),
          (↑(t * g) : Matrix n n K) *ᵥ u = u) ∧ (↑(t * g) : Matrix n n K) *ᵥ x = x ∧
        (↑(t * g) : Matrix n n K) *ᵥ y = y := by
  set U : Set (n → K) := insert e (insert f (S : Set (n → K)))
  obtain ⟨y, hyU, hxy, hyx, hσ_id⟩ :=
    exists_hyperbolic_partner_of_totally_isotropic hσ hQ hε hW_nd hW_iso hx0 hxU
  have hxx := hW_iso x hxU; have hyy := hW_iso y hyU
  obtain ⟨h₁, hh₁, hh₁e, hh₁f, hh₁w⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_hyperbolic_rescale hσ hQ hε hσε hd hdε he hf hef
      hfe hc (hσ_id c)
  let g₀ := h₁⁻¹ * g
  have hg₀U (u : n → K) (hu : u ∈ U) : (g₀ : Matrix n n K) *ᵥ u = u := by
    rcases hu with rfl | rfl | huS
    · rw [coe_mul_mulVec, hge]; exact coe_inv_mulVec_of_mulVec_eq hh₁e
    · rw [coe_mul_mulVec, hgf, hσ_id]; exact coe_inv_mulVec_of_mulVec_eq hh₁f
    · rw [coe_mul_mulVec, hgS u huS]
      exact coe_inv_mulVec_of_mulVec_eq (hh₁w u (hSe u huS) (hSf u huS))
  have hx'0 : (g₀ : Matrix n n K) *ᵥ x ≠ 0 :=
    (smul_ne_zero_iff_ne (g₀ : SpecialLinearGroup n K)).mpr hx0
  obtain ⟨t₂, ht₂, c₂, hc₂, ht₂U, ht₂x'⟩ :=
    exists_mem_iSup_totally_isotropic_smul hσ hQ ⟨d, hd, hdε⟩ hW_nd hW_iso hx'0 hxy hxU hyU
      fun u hu ↦ by
        rw [← hg₀U u hu,
          comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g₀.2), hxU u hu]
  obtain ⟨h₂, hh₂, hh₂x, -, hh₂w⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_hyperbolic_rescale hσ hQ hε hσε hd hdε hxx hyy hxy
      hyx hc₂ (hσ_id c₂)
  let g₂ := h₂⁻¹ * (t₂ * g₀)
  have hg₂U (u : n → K) (hu : u ∈ U) : (g₂ : Matrix n n K) *ᵥ u = u := by
    rw [coe_mul_mulVec, coe_mul_mulVec, hg₀U u hu, ht₂U u hu]
    exact coe_inv_mulVec_of_mulVec_eq (hh₂w u ((comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp
      (hxU u hu)) ((comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (hyU u hu)))
  have hg₂x : (g₂ : Matrix n n K) *ᵥ x = x := by
    rw [coe_mul_mulVec, coe_mul_mulVec, ht₂x']; exact coe_inv_mulVec_of_mulVec_eq hh₂x
  have hxy' : (σ ∘ x) ⬝ᵥ (Q *ᵥ ((g₂ : Matrix n n K) *ᵥ y)) = 1 := by
    rw [← hg₂x, comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g₂.2), hxy]
  obtain ⟨s₃, hs₃, w₃, c₃, hxw₃, hc₃, hcs₃, hs₃x, hs₃y'⟩ :=
    exists_mem_specialIsometryGroup_coe_eq_siegelTransvection_mulVec_eq_self_and_mulVec_eq hσ hQ hxx
      ((comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g₂.2) y y).trans hyy)
      hyy (ne_of_eq_of_ne hxy' one_ne_zero) (hxy'.trans hxy.symm)
  have heq_prod : (⟨s₃, hs₃⟩ * (h₂⁻¹ * t₂ * h₁⁻¹)) * g = ⟨s₃, hs₃⟩ * g₂ := by dsimp [g₂, g₀]; group
  refine ⟨y, hyU, hxy, hyx, ⟨s₃, hs₃⟩ * (h₂⁻¹ * t₂ * h₁⁻¹), mul_mem
    (siegelTransvection_mem_iSup_unitaryTransvectionSubgroup hσ hQ hdet hε hσε htr hd hdε he₀ he hf
      hef hfe hgen hxx hxw₃ hc₃ hs₃ hcs₃) (mul_mem (mul_mem (inv_mem hh₂) ht₂) (inv_mem hh₁)),
    fun u hu ↦ ?_, by rw [heq_prod, coe_mul_mulVec, hg₂x]; exact hs₃x,
    by rw [heq_prod, coe_mul_mulVec]; exact hs₃y'⟩
  rw [heq_prod, coe_mul_mulVec, hg₂U u hu,
    show ((⟨s₃, hs₃⟩ : Q.specialIsometryGroup σ) : Matrix n n K) = _ from hcs₃]
  exact siegelTransvection_mulVec_eq_self_of_ortho (ne_of_eq_of_ne hxy' one_ne_zero) (hcs₃ ▸ hs₃y')
    ((comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (hxU u hu))
    (by rw [← hg₂U u hu, comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp
      g₂.2), (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (hyU u hu)])
    ((comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (hyU u hu))
omit [DecidableEq n] hσ hQ hdet hσε htr hd hdε he₀ he hf hef hgen in
private theorem finrank_lt_card_of_ortho {S : Submodule K (n → K)}
    (hSf : ∀ s ∈ S, (σ ∘ f) ⬝ᵥ (Q *ᵥ s) = 0) : Module.finrank K S < Fintype.card n := by
  have he_notMem : e ∉ S := fun heS ↦ left_ne_zero_of_mul (hε ▸ one_ne_zero) (hfe ▸ hSf e heS)
  have h := Submodule.finrank_lt_finrank_of_lt
    ((lt_top_iff_ne_top (a := S)).mpr fun htop ↦ he_notMem (htop ▸ Submodule.mem_top))
  rwa [finrank_top, Module.finrank_fintype_fun_eq_card] at h
private theorem mem_iSup_of_fixes_submodule :
    ∀ (k : ℕ) (S : Submodule K (n → K)) (g : Q.specialIsometryGroup σ) (c : K),
      (∀ s ∈ S, (σ ∘ e) ⬝ᵥ (Q *ᵥ s) = 0) → (∀ s ∈ S, (σ ∘ f) ⬝ᵥ (Q *ᵥ s) = 0) →
      (∀ v : n → K, ∃ s ∈ S, ∀ s' ∈ S, (σ ∘ s') ⬝ᵥ (Q *ᵥ (v - s)) = 0) → c ≠ 0 →
      (g : Matrix n n K) *ᵥ e = c • e → (g : Matrix n n K) *ᵥ f = (σ c)⁻¹ • f →
      (∀ s ∈ S, (g : Matrix n n K) *ᵥ s = s) → Fintype.card n - Module.finrank K S ≤ k →
      g ∈ ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p
  | 0, S, _, _, _, hSf, _, _, _, _, _, hk => by
    have := finrank_lt_card_of_ortho hε hfe hSf; omega
  | k + 1, S, g, c, hSe, hSf, hproj, hc, hge, hgf, hgS, hk => by
    have hS_lt := finrank_lt_card_of_ortho hε hfe hSf
    by_cases hW_aniso : ∃ x : n → K, (σ ∘ e) ⬝ᵥ (Q *ᵥ x) = 0 ∧ (σ ∘ f) ⬝ᵥ (Q *ᵥ x) = 0 ∧
        (∀ s ∈ S, (σ ∘ s) ⬝ᵥ (Q *ᵥ x) = 0) ∧ (σ ∘ x) ⬝ᵥ (Q *ᵥ x) ≠ 0
    · obtain ⟨x, hex, hfx, hSx, hxx⟩ := hW_aniso
      obtain ⟨t, ht, c', hc', hge', hgf', hgS', hgx'⟩ :=
        exists_mem_iSup_fixes_anisotropic hσ hQ hdet hε hσε htr hd hdε he₀ he hf hef hfe hgen hSe
          hSf hc hge hgf hgS hex hfx hSx hxx
      set S' : Submodule K (n → K) := S ⊔ (K ∙ x)
      have hx_notMem : x ∉ S := fun hxS ↦ hxx (hSx x hxS)
      have hfin : Module.finrank K S < Module.finrank K S' :=
        Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne le_sup_left
          fun heq ↦ hx_notMem (heq ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)))
      exact by simpa using mul_mem (inv_mem ht) (mem_iSup_of_fixes_submodule k S' (t * g) c'
        (ortho_sup_span_singleton hSe hex) (ortho_sup_span_singleton hSf hfx)
        (ortho_proj_sup_anisotropic hSx hxx hproj) hc' hge' hgf'
        (fixes_sup_span_singleton hgS' hgx') (by omega))
    · push Not at hW_aniso
      by_cases hW_ne : ∃ x : n → K, x ≠ 0 ∧ (σ ∘ e) ⬝ᵥ (Q *ᵥ x) = 0 ∧ (σ ∘ f) ⬝ᵥ (Q *ᵥ x) = 0 ∧
          ∀ s ∈ S, (σ ∘ s) ⬝ᵥ (Q *ᵥ x) = 0
      · obtain ⟨x, hx0, hex, hfx, hSx⟩ := hW_ne
        obtain ⟨y, hyU, hxy, hyx, t, ht, hgU', hgx', hgy'⟩ :=
          exists_mem_iSup_fixes_totally_isotropic hσ hQ hdet hε hσε htr hd hdε he₀ he hf hef hfe
            hgen hSe hSf (fun _ ↦ ortho_nondegenerate_of_proj hdet hε he hf hef hfe hSe hSf hproj)
            (fun w hw ↦ hW_aniso w (hw e (by simp)) (hw f (by simp)) fun s hs ↦ hw s (by simp [hs]))
            hc hge hgf hgS hx0 fun u hu ↦ by
              rcases hu with rfl | rfl | huS <;> [exact hex; exact hfx; exact hSx u huS]
        have hey := hyU e (by simp); have hfy := hyU f (by simp)
        have hSy (s : n → K) (hs : s ∈ S) : (σ ∘ s) ⬝ᵥ (Q *ᵥ y) = 0 := hyU s (by simp [hs])
        set S' : Submodule K (n → K) := (S ⊔ (K ∙ x)) ⊔ (K ∙ y)
        have hx_notMem : x ∉ S := fun hxS ↦ left_ne_zero_of_mul (hε ▸ one_ne_zero)
          (hyx ▸ (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (hSy x hxS))
        have hfin : Module.finrank K S < Module.finrank K S' :=
          lt_of_lt_of_le (Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne le_sup_left fun heq ↦
            hx_notMem (heq ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))))
            (Submodule.finrank_mono le_sup_left)
        exact by simpa using mul_mem (inv_mem ht) (mem_iSup_of_fixes_submodule k S' (t * g) 1
          (ortho_sup_span_singleton (ortho_sup_span_singleton hSe hex) hey)
          (ortho_sup_span_singleton (ortho_sup_span_singleton hSf hfx) hfy)
          (ortho_proj_sup_hyperbolic hε hSx hSy (hW_aniso x hex hfx hSx) (hW_aniso y hey hfy hSy)
            hxy hyx hproj) one_ne_zero (by simpa using hgU' e (by simp))
          (by simpa using hgU' f (by simp)) (fixes_sup_span_singleton
            (fixes_sup_span_singleton (fun s hs ↦ hgU' s (by simp [hs])) hgx') hgy') (by omega))
      · exact mem_iSup_of_ortho_eq_zero hσ hQ hε hσε hd hdε he hf hef hfe hSe hSf hproj hW_ne hc
          hge hgf hgS
end Generation
section MainTheorems

variable (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
  (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
  [Nonempty (Q.isotropicPoints σ)]
  (hgen : (∃ a : K, a ≠ 0 ∧ a ≠ 1 ∧ σ a = a) ∨ Fintype.card n ≤ 2 ∨
    ∃ u w : n → K, u ≠ 0 ∧ w ∉ K ∙ u ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 ∧
      (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0)
include hσ hQ hdet htr hadm hgen in
/-- **Unitary transvections generate the special unitary group.** Let `σ` be an involution of a
field `K`, let `Q` be an invertible `ε`-Hermitian matrix whose trace `t ↦ t + ε σ(t)` is onto
`{s | σ(s) = ε s}` and has a nonzero kernel element, and suppose `Q.isotropicPoints σ` is nonempty.
If the fixed field of `σ` has an element outside `{0, 1}`, or `Fintype.card n ≤ 2`, or the form has
Witt index at least two, then the unitary transvection groups along the isotropic points generate
`Q.specialIsometryGroup σ`. -/
theorem iSup_unitaryTransvectionSubgroup :
    ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p = ⊤ := by
  obtain ⟨e, f, he₀, -, he, hf, hef, hfe, hε, hσε⟩ :=
    exists_hyperbolic_pair_of_isotropicPoints hσ hQ hdet htr
  obtain ⟨d, hd, hdε⟩ := hadm; rw [eq_top_iff]; intro g _
  have hge_ne : (g : Matrix n n K) *ᵥ e ≠ 0 :=
    (smul_ne_zero_iff_ne (g : SpecialLinearGroup n K)).mpr he₀
  have hge_iso : (σ ∘ ((g : Matrix n n K) *ᵥ e)) ⬝ᵥ (Q *ᵥ ((g : Matrix n n K) *ᵥ e)) = 0 := by
    rw [comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g.2), he]
  obtain ⟨t₁, ht₁, c, hc, ht₁ge⟩ :=
    exists_mem_iSup_unitaryTransvectionSubgroup_mulVec_eq_smul hσ hQ hdet htr ⟨d, hd, hdε⟩ hge_ne
      he₀ hge_iso he
  let g₁ := t₁ * g
  have hg₁f_iso : (σ ∘ ((g₁ : Matrix n n K) *ᵥ f)) ⬝ᵥ (Q *ᵥ ((g₁ : Matrix n n K) *ᵥ f)) = 0 := by
    rw [comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g₁.2), hf]
  have heg₁f : (σ ∘ e) ⬝ᵥ (Q *ᵥ ((g₁ : Matrix n n K) *ᵥ f)) = (σ c)⁻¹ := by
    have hpair : (σ ∘ ((g₁ : Matrix n n K) *ᵥ e)) ⬝ᵥ (Q *ᵥ ((g₁ : Matrix n n K) *ᵥ f)) = 1 := by
      rw [comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp g₁.2), hef]
    have hg₁e : (g₁ : Matrix n n K) *ᵥ e = c • e := by rwa [coe_mul_mulVec]
    rw [hg₁e, TauCeti.map_comp_smul, smul_dotProduct, smul_eq_mul] at hpair
    exact eq_inv_of_mul_eq_one_right hpair
  have hσc0 : σ c ≠ 0 := (map_ne_zero σ).mpr hc
  obtain ⟨s₂, hs₂, w₂, c₂, hew₂, hc₂, hcs₂, hs₂e, hs₂f⟩ :=
    exists_mem_specialIsometryGroup_coe_eq_siegelTransvection_mulVec_eq_self_and_mulVec_eq
      (y := (σ c)⁻¹ • f) hσ hQ he hg₁f_iso (by rw [comp_smul_dotProduct_mulVec_smul, hf, mul_zero])
      (heg₁f ▸ inv_ne_zero hσc0)
      (by rw [heg₁f, mulVec_smul, dotProduct_smul, hef, smul_eq_mul, mul_one])
  have hs₂_mem := siegelTransvection_mem_iSup_unitaryTransvectionSubgroup hσ hQ hdet hε hσε htr hd
    hdε he₀ he hf hef hfe hgen he hew₂ hc₂ hs₂ hcs₂
  let g₂ : Q.specialIsometryGroup σ := ⟨s₂, hs₂⟩ * g₁
  have hs₂e' : ((⟨s₂, hs₂⟩ : Q.specialIsometryGroup σ) : Matrix n n K) *ᵥ e = e := hs₂e
  have hg₂_mem := mem_iSup_of_fixes_submodule hσ hQ hdet hε hσε htr hd hdε he₀ he hf hef hfe hgen
    (Fintype.card n - Module.finrank K (⊥ : Submodule K (n → K))) ⊥ g₂ c
    (by simp) (by simp) (fun v ↦ ⟨0, Submodule.zero_mem ⊥, by simp⟩) hc
    (by rw [coe_mul_mulVec, coe_mul_mulVec, ht₁ge, mulVec_smul, hs₂e'])
    (by rw [coe_mul_mulVec]; exact hs₂f) (by simp) le_rfl
  have hg_eq : g = t₁⁻¹ * ⟨s₂, hs₂⟩⁻¹ * g₂ := by dsimp only [g₂, g₁]; group
  rw [hg_eq]; exact mul_mem (mul_mem (inv_mem ht₁) (inv_mem hs₂_mem)) hg₂_mem
/-- **The Iwasawa structure of a special unitary group on its isotropic points.** Under the
hypotheses of `Matrix.iSup_unitaryTransvectionSubgroup`, the unitary transvection groups
`Matrix.unitaryTransvectionSubgroup Q σ p` are abelian, conjugate-equivariant, and generate
`Q.specialIsometryGroup σ`. -/
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
