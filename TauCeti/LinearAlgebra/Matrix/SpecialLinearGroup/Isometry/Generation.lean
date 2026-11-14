/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.SiegelGeneration
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.Algebra.Group.Hom.Defs
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Generation of the special unitary group by unitary transvections

Let `σ` be a nontrivial involution of a field `K` (`∃ a, σ(a) ≠ a`), let `Q` be an invertible
`ε`-Hermitian matrix over `K`, and assume that the `ε`-trace `t ↦ t + ε σ(t)` is onto
`{s | σ(s) = ε s}` with a nonzero kernel element and the norm `b ↦ b σ(b)` is onto the fixed field
`K^σ`. By `Matrix.eq_top_of_siegelTransvection_mem`, the admissible Siegel transformations
`S(u, w, c)` generate `Matrix.specialIsometryGroup Q σ`.

This file expresses every admissible Siegel transformation `S(u, w, c)` as a product of admissible
unitary transvections `τ_{v,a}`, except in the single classical exception `SU₃(2)` where both `K^σ`
has only two elements and the dimension is `3`. Concretely, generation by unitary transvections
holds whenever either:

* `K^σ` has an element `t ∉ {0, 1}` (`∃ t, t ≠ 0 ∧ t ≠ 1 ∧ σ(t) = t`), in which case a
  hyperbolic scaling `u ↦ t u` constructed from Whitehead's identity along `(u, v)` combined with
  its inverse along `(u, S(u, (t - 1)⁻¹ w, c₁) v)` produces `S(u, w, c₀)` for every `w` orthogonal
  to `(u, v)`; or
* the ambient dimension is at least `4` (`4 ≤ Fintype.card n`), in which case the orthogonal
  complement `W` of a hyperbolic plane `(u, v)` has dimension at least `2`, contains nonzero
  isotropic vectors, is spanned by its isotropic vectors, and each `S(u, y, 0)` for isotropic
  `y ∈ W` is a product of three unitary transvections `τ_{u,-d} τ_{y,-d r σ(r)} τ_{u + r y,d}`
  with `r = d⁻¹`.

Adjusting the scalar parameter `c₀` to any admissible `c` multiplies by the unitary transvection
`τ_{u, c - c₀}`. Together with `Matrix.eq_top_of_siegelTransvection_mem`, this yields
`Matrix.eq_top_of_unitaryTransvection_mem` and `Matrix.iSup_unitaryTransvectionSubgroup_eq_top`.

## Main results

* `Matrix.eq_top_of_unitaryTransvection_mem`: any subgroup of `Q.specialIsometryGroup σ` containing
  all admissible unitary transvections is the whole group, provided `K^σ` has at least three
  elements or `4 ≤ Fintype.card n`.
* `Matrix.iSup_unitaryTransvectionSubgroup_eq_top`: under the same hypotheses, the unitary
  transvection subgroups `Matrix.unitaryTransvectionSubgroup Q σ p` of isotropic points generate
  `Q.specialIsometryGroup σ`.

## References

* J. Dieudonné, *On the structure of unitary groups*, Trans. Amer. Math. Soc. **72** (1952),
  367--385.
* D. E. Taylor, *The Geometry of the Classical Groups* (1992), §10.4 and §11.4--11.5.
* L. C. Grove, *Classical Groups and Geometric Algebra* (2002), Chapter 11.
-/

public section

open scoped LinearAlgebra.Projectivization

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] {Q : Matrix n n K} {σ : K →+* K}
  {ε : K}

/-! ### Extending an isotropic vector and adjusting the Siegel scalar -/

/-- Any nonzero isotropic vector `u` of an invertible `ε`-Hermitian form extends to a hyperbolic
pair `(u, v)` (`B(u, u) = B(v, v) = 0`, `B(u, v) = 1`). -/
private theorem exists_hyperbolic_partner (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q)
    (hdet : Q.det ≠ 0) (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
    {u : n → K} (hu0 : u ≠ 0) (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) :
    ∃ v : n → K, (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ v) = 1 := by
  obtain ⟨y, huy⟩ : ∃ y : n → K, (σ ∘ u) ⬝ᵥ (Q *ᵥ y) ≠ 0 := by
    by_contra! h0
    exact hu0 (eq_zero_of_forall_comp_dotProduct_mulVec_eq_zero hdet h0)
  have hyu : (σ ∘ y) ⬝ᵥ (Q *ᵥ u) ≠ 0 := (comp_dotProduct_mulVec_ne_zero_comm hσ hQ).mp huy
  obtain ⟨c, hc⟩ := exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero hσ hQ htr hu hyu
  refine ⟨((σ ∘ u) ⬝ᵥ (Q *ᵥ y))⁻¹ • (y + c • u), ?_, ?_⟩
  · rw [comp_smul_dotProduct_mulVec_smul, hc, mul_zero]
  · simp [mulVec_smul, mulVec_add, hu, inv_mul_cancel₀ huy]

/-- If `τ_{u,a}` lies in `Q.specialIsometryGroup σ` for `u` part of a hyperbolic pair `(u, v)`,
then `a + ε σ(a) = 0`. -/
private theorem admissible_of_coe_eq_unitaryTransvection (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) {u v : n → K}
    (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0)
    (huv : (σ ∘ u) ⬝ᵥ (Q *ᵥ v) = 1) {a : K} {k : Q.specialIsometryGroup σ}
    (hk : ((k : SpecialLinearGroup n K) : Matrix n n K) = Q.unitaryTransvection σ u a) :
    a + ε * σ a = 0 := by
  have hpres := comp_mulVec_dotProduct_mulVec_mulVec (mem_specialIsometryGroup_iff.mp k.2) v v
  have hvu : (σ ∘ v) ⬝ᵥ (Q *ᵥ u) = ε := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε u v, huv, map_one, mul_one]
  simp only [hk, unitaryTransvection_mulVec, huv, mul_one, comp_add_dotProduct_mulVec, mulVec_add,
    dotProduct_add, TauCeti.map_comp_smul, smul_dotProduct, mulVec_smul, dotProduct_smul,
    smul_eq_mul, hv, hvu, hu, mul_zero, add_zero, zero_add] at hpres
  linear_combination ε * hpres - a * hε

/-- Once `H` contains `S(u, w, c₀)` for some `c₀` and all admissible unitary transvections along
`u`, it contains every isometry of the form `S(u, w, c)`. -/
private theorem mem_of_exists_siegelTransvection_same_vec (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1)
    {H : Subgroup (Q.specialIsometryGroup σ)} {u v w : n → K}
    (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0)
    (huv : (σ ∘ u) ⬝ᵥ (Q *ᵥ v) = 1) (huw : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0)
    (hHu : ∀ a, a + ε * σ a = 0 → ∀ g : Q.specialIsometryGroup σ,
      ((g : SpecialLinearGroup n K) : Matrix n n K) = Q.unitaryTransvection σ u a → g ∈ H)
    {c₀ : K} {h₀ : Q.specialIsometryGroup σ} (hh₀H : h₀ ∈ H)
    (hh₀ : ((h₀ : SpecialLinearGroup n K) : Matrix n n K) = Q.siegelTransvection σ ε u w c₀)
    {c : K} {g : Q.specialIsometryGroup σ}
    (hg : ((g : SpecialLinearGroup n K) : Matrix n n K) = Q.siegelTransvection σ ε u w c) :
    g ∈ H := by
  have hwu : (σ ∘ w) ⬝ᵥ (Q *ᵥ u) = 0 := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp huw
  have hinv_mat : (((h₀⁻¹ : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) : Matrix n n K) =
      Q.siegelTransvection σ ε u (-w) (-c₀ - ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ w))) := by
    have h₁ := hh₀ ▸ siegelTransvection_mul_siegelTransvection_neg_eq_one hu huw hwu c₀
    have h₂ : ((h₀ : SpecialLinearGroup n K) : Matrix n n K) *
        (((h₀⁻¹ : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) : Matrix n n K) = 1 := by
      rw [← SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
        SpecialLinearGroup.coe_one]
    rw [← inv_eq_right_inv h₂, inv_eq_right_inv h₁]
  have hprod : (((g * h₀⁻¹ : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) : Matrix n n K) =
      Q.unitaryTransvection σ u (c - c₀) := by
    have hu_negw : (σ ∘ u) ⬝ᵥ (Q *ᵥ (-w)) = 0 := by rw [mulVec_neg, dotProduct_neg, huw, neg_zero]
    rw [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, hg, hinv_mat,
      siegelTransvection_mul_siegelTransvection hu hu_negw hwu, add_neg_cancel,
      siegelTransvection_zero_eq_unitaryTransvection, mulVec_neg, dotProduct_neg]
    exact congrArg (Q.unitaryTransvection σ u) (by ring)
  have hadm := admissible_of_coe_eq_unitaryTransvection hσ hQ hε hu hv huv hprod
  have hgh₀ : g * h₀⁻¹ ∈ H := hHu (c - c₀) hadm (g * h₀⁻¹) hprod
  simpa [mul_assoc] using mul_mem hgh₀ hh₀H

/-! ### Case 1: Fixed field has at least three elements -/

omit [DecidableEq n] in
private theorem matrix_eq_of_hyperbolic_complement {u v : n → K} {W : Submodule K (n → K)}
    (hPW : ((K ∙ u) ⊔ (K ∙ v)) ⊔ W = ⊤) {M₁ M₂ : Matrix n n K}
    (hu : M₁ *ᵥ u = M₂ *ᵥ u) (hv : M₁ *ᵥ v = M₂ *ᵥ v)
    (hW : ∀ y ∈ W, M₁ *ᵥ y = M₂ *ᵥ y) : M₁ = M₂ := by
  refine mulVec_injective (funext fun x ↦ ?_)
  obtain ⟨p, hpP, y, hyW, rfl⟩ := Submodule.mem_sup.mp (hPW ▸ (Submodule.mem_top : x ∈ ⊤))
  obtain ⟨u', hu', v', hv', rfl⟩ := Submodule.mem_sup.mp hpP
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu'
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hv'
  simp [mulVec_add, mulVec_smul, hu, hv, hW y hyW]

omit [DecidableEq n] in
private theorem scaling_product_mulVec_on_W (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (ht : σ t = t)
    {u v w : n → K} {W : Submodule K (n → K)} (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0)
    (horth_u : ∀ y ∈ W, (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0)
    (horth_v : ∀ y ∈ W, (σ ∘ v) ⬝ᵥ (Q *ᵥ y) = 0)
    {c₁ : K} {M₁ M₂ : Matrix n n K}
    (h₁u : M₁ *ᵥ u = t • u) (h₁W : ∀ y ∈ W, M₁ *ᵥ y = y)
    (h₂u : M₂ *ᵥ u = t⁻¹ • u)
    (h₂_orth : ∀ y : n → K, (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0 →
      (σ ∘ (v + ((t - 1)⁻¹ • w + c₁ • u))) ⬝ᵥ (Q *ᵥ y) = 0 → M₂ *ᵥ y = y)
    (huz : (σ ∘ u) ⬝ᵥ (Q *ᵥ (v + ((t - 1)⁻¹ • w + c₁ • u))) = 1)
    {y : n → K} (hyW : y ∈ W) :
    (M₁ * M₂) *ᵥ y = y - (ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ y))) • u := by
  set z := v + ((t - 1)⁻¹ • w + c₁ • u)
  set w' := (t - 1)⁻¹ • w
  set α := ε * ((σ ∘ w') ⬝ᵥ (Q *ᵥ y))
  have hzu : (σ ∘ z) ⬝ᵥ (Q *ᵥ u) = ε := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε u z, huz, map_one, mul_one]
  have hzy : (σ ∘ z) ⬝ᵥ (Q *ᵥ y) = (σ ∘ w') ⬝ᵥ (Q *ᵥ y) := by
    simp [z, w', map_comp_add, TauCeti.map_comp_smul, add_dotProduct, smul_dotProduct,
      horth_v y hyW, horth_u y hyW]
  have hy_u : (σ ∘ u) ⬝ᵥ (Q *ᵥ (y - α • u)) = 0 := by
    simp [mulVec_sub, mulVec_smul, horth_u y hyW, hu]
  have hy_z : (σ ∘ z) ⬝ᵥ (Q *ᵥ (y - α • u)) = 0 := by
    rw [mulVec_sub, dotProduct_sub, mulVec_smul, dotProduct_smul, smul_eq_mul, hzy, hzu]
    linear_combination -((σ ∘ w') ⬝ᵥ (Q *ᵥ y)) * hε
  have hM₂y : M₂ *ᵥ y = y + (α * (t⁻¹ - 1)) • u := by
    have hfix := h₂_orth (y - α • u) hy_u hy_z
    rw [mulVec_sub, mulVec_smul, h₂u, sub_eq_iff_eq_add] at hfix
    rw [hfix]; module
  have hht : σ (t - 1)⁻¹ = (t - 1)⁻¹ := by rw [map_inv₀, map_sub, map_one, ht]
  have hcoeff : α * (t⁻¹ - 1) * t = -(ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ y))) := by
    have ht_sub : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
    have h₁ : (t⁻¹ - 1) * t = -(t - 1) := by rw [sub_mul, inv_mul_cancel₀ ht0]; ring
    simp only [α, w', TauCeti.map_comp_smul, smul_dotProduct, smul_eq_mul, hht, mul_assoc, h₁]
    calc ε * ((t - 1)⁻¹ * (((σ ∘ w) ⬝ᵥ (Q *ᵥ y)) * -(t - 1)))
        = -((t - 1)⁻¹ * (t - 1)) * (ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ y))) := by ring
      _ = -(ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ y))) := by rw [inv_mul_cancel₀ ht_sub]; ring
  rw [← mulVec_mulVec, hM₂y, mulVec_add, mulVec_smul, h₁W y hyW, h₁u, smul_smul, hcoeff, neg_smul,
    ← sub_eq_add_neg]

private theorem scaling_product_mulVec_on_v {t c₁ : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    {u v w : n → K} (huv : (σ ∘ u) ⬝ᵥ (Q *ᵥ v) = 1) (hwv : (σ ∘ w) ⬝ᵥ (Q *ᵥ v) = 0)
    {M₁ M₂ : Matrix n n K} (h₁u : M₁ *ᵥ u = t • u) (h₁v : M₁ *ᵥ v = t⁻¹ • v)
    (h₁w' : M₁ *ᵥ ((t - 1)⁻¹ • w) = (t - 1)⁻¹ • w) (h₂u : M₂ *ᵥ u = t⁻¹ • u)
    (h₂z : M₂ *ᵥ (v + ((t - 1)⁻¹ • w + c₁ • u)) = t • (v + ((t - 1)⁻¹ • w + c₁ • u)))
    (hMw' : (M₁ * M₂) *ᵥ ((t - 1)⁻¹ • w) =
      (t - 1)⁻¹ • w - (ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ ((t - 1)⁻¹ • w)))) • u) :
    (M₁ * M₂) *ᵥ v = Q.siegelTransvection σ ε u w
      (t * c₁ * t + ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ ((t - 1)⁻¹ • w))) - c₁) *ᵥ v := by
  set w' := (t - 1)⁻¹ • w
  set z := v + (w' + c₁ • u)
  set c₀ := t * c₁ * t + ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ w')) - c₁
  have hv_decomp : v = z - w' - c₁ • u := by simp [z]; abel
  have hMz : (M₁ * M₂) *ᵥ z = v + t • w' + (t * c₁ * t) • u := by
    rw [← mulVec_mulVec, h₂z, smul_add, smul_add, mulVec_add, mulVec_add,
      mulVec_smul M₁ t v, h₁v, mulVec_smul M₁ t w', h₁w',
      mulVec_smul M₁ t (c₁ • u), mulVec_smul M₁ c₁ u, h₁u]
    simp [smul_smul, mul_inv_cancel₀ ht0, add_assoc, mul_assoc]
  have hMu : (M₁ * M₂) *ᵥ u = u := by
    rw [← mulVec_mulVec, h₂u, mulVec_smul, h₁u, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  conv_lhs => rw [hv_decomp]
  rw [mulVec_sub, mulVec_sub, hMz, hMw', mulVec_smul (M₁ * M₂) c₁ u, hMu,
    siegelTransvection_mulVec, huv, hwv, mul_zero, zero_smul, sub_zero, one_smul]
  have htw' : (t - 1) • w' = w := by
    rw [smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr ht1), one_smul]
  rw [show v + t • w' + (t * c₁ * t) • u - (w' - (ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ w'))) • u) - c₁ • u =
    v + ((t - 1) • w' + c₀ • u) by simp [c₀]; module, htw']

private theorem exists_siegelTransvection_of_fixed_scalar (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) (hσ_eps : σ ε = ε)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (ht : σ t = t)
    {H : Subgroup (Q.specialIsometryGroup σ)}
    (hH : ∀ {x : n → K} {a : K}, (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0 → a + ε * σ a = 0 →
      ∀ g : Q.specialIsometryGroup σ,
        ((g : SpecialLinearGroup n K) : Matrix n n K) = Q.unitaryTransvection σ x a → g ∈ H)
    {u v : n → K} (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0)
    (huv : (σ ∘ u) ⬝ᵥ (Q *ᵥ v) = 1) {W : Submodule K (n → K)}
    (hPW : ((K ∙ u) ⊔ (K ∙ v)) ⊔ W = ⊤)
    (horth_u : ∀ y ∈ W, (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0)
    (horth_v : ∀ y ∈ W, (σ ∘ v) ⬝ᵥ (Q *ᵥ y) = 0)
    {w : n → K} (hwW : w ∈ W) :
    ∃ c₀ : K, ∃ h ∈ H,
      ((h : SpecialLinearGroup n K) : Matrix n n K) = Q.siegelTransvection σ ε u w c₀ := by
  obtain ⟨d, hd0, hd⟩ := hadm
  set w' := (t - 1)⁻¹ • w
  have hw'W : w' ∈ W := W.smul_mem _ hwW
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : K, c₁ + ε * σ c₁ + ε * ((σ ∘ w') ⬝ᵥ (Q *ᵥ w')) = 0 := by
    obtain ⟨c₁, hc₁⟩ := htr (-(ε * ((σ ∘ w') ⬝ᵥ (Q *ᵥ w')))) (by
      rw [map_neg, map_mul, hσ_eps, apply_comp_dotProduct_mulVec hσ hQ w' w']; ring)
    exact ⟨c₁, by linear_combination hc₁⟩
  set S := Q.siegelTransvection σ ε u w' c₁
  have hS_iso := transpose_map_siegelTransvection_mul_mul_self hσ hQ hu (horth_u w' hw'W) hc₁
  have hw'u : (σ ∘ w') ⬝ᵥ (Q *ᵥ u) = 0 :=
    (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (horth_u w' hw'W)
  have hw'v : (σ ∘ w') ⬝ᵥ (Q *ᵥ v) = 0 :=
    (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (horth_v w' hw'W)
  set z := S *ᵥ v
  have hz_eq : z = v + (w' + c₁ • u) := by simp [z, S, siegelTransvection_mulVec, huv, hw'v]
  have hz : (σ ∘ z) ⬝ᵥ (Q *ᵥ z) = 0 := by
    rw [comp_mulVec_dotProduct_mulVec_mulVec hS_iso v v, hv]
  have huz : (σ ∘ u) ⬝ᵥ (Q *ᵥ z) = 1 := by
    rw [← siegelTransvection_mulVec_self hu hw'u c₁,
      comp_mulVec_dotProduct_mulVec_mulVec hS_iso u v, huv]
  obtain ⟨h₁, hh₁H, h₁u, h₁v, h₁_orth⟩ := exists_unitaryTransvection_hyperbolic_scaling hσ hQ hε
    hσ_eps hd0 hd hu hv huv ht0 ht (fun _ ↦ hH hu) (fun _ ↦ hH hv)
  obtain ⟨h₂, hh₂H, h₂u, h₂z, h₂_orth⟩ := exists_unitaryTransvection_hyperbolic_scaling hσ hQ hε
    hσ_eps hd0 hd hu hz huz (inv_ne_zero ht0) (by rw [map_inv₀, ht]) (fun _ ↦ hH hu) (fun _ ↦ hH hz)
  set M₁ : Matrix n n K := ((h₁ : SpecialLinearGroup n K) : Matrix n n K)
  set M₂ : Matrix n n K := ((h₂ : SpecialLinearGroup n K) : Matrix n n K)
  rw [inv_inv] at h₂z
  have h₁W : ∀ y ∈ W, M₁ *ᵥ y = y := fun y hyW ↦ h₁_orth y (horth_u y hyW) (horth_v y hyW)
  have hMW (y : n → K) (hyW : y ∈ W) := scaling_product_mulVec_on_W hσ hQ hε ht0 ht1 ht hu horth_u
    horth_v h₁u h₁W h₂u (hz_eq ▸ h₂_orth) (hz_eq ▸ huz) hyW
  refine ⟨t * c₁ * t + ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ w')) - c₁, h₁ * h₂, mul_mem hh₁H hh₂H, ?_⟩
  rw [show (((h₁ * h₂ : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) : Matrix n n K) =
    M₁ * M₂ by rw [Subgroup.coe_mul, SpecialLinearGroup.coe_mul]]
  have hwu : (σ ∘ w) ⬝ᵥ (Q *ᵥ u) = 0 :=
    (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (horth_u w hwW)
  have hwv : (σ ∘ w) ⬝ᵥ (Q *ᵥ v) = 0 :=
    (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp (horth_v w hwW)
  refine matrix_eq_of_hyperbolic_complement hPW ?_ ?_ fun y hyW ↦ ?_
  · rw [← mulVec_mulVec, h₂u, mulVec_smul, h₁u, smul_smul, inv_mul_cancel₀ ht0, one_smul,
      siegelTransvection_mulVec_self hu hwu]
  · exact scaling_product_mulVec_on_v ht0 ht1 huv hwv h₁u h₁v (h₁W w' hw'W) h₂u (hz_eq ▸ h₂z)
      (hMW w' hw'W)
  · rw [hMW y hyW, siegelTransvection_mulVec, horth_u y hyW, zero_smul, add_zero]

/-! ### Case 2: Ambient dimension at least four -/

/-- When `u` and `y` are orthogonal isotropic vectors and `d ≠ 0` satisfies `d + ε σ(d) = 0`,
`S(u, y, 0)` is the product of three admissible unitary transvections along `u`, `y`, and
`u + d⁻¹ y`. -/
private theorem siegelTransvection_zero_mem_of_isotropic (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) {d : K} (hd0 : d ≠ 0) (hd : d + ε * σ d = 0)
    {H : Subgroup (Q.specialIsometryGroup σ)}
    (hH : ∀ {x : n → K} {a : K}, (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0 → a + ε * σ a = 0 →
      ∀ g : Q.specialIsometryGroup σ,
        ((g : SpecialLinearGroup n K) : Matrix n n K) = Q.unitaryTransvection σ x a → g ∈ H)
    {u y : n → K} (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0)
    (huy : (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0) :
    ∃ c₀ : K, ∃ h ∈ H,
      ((h : SpecialLinearGroup n K) : Matrix n n K) = Q.siegelTransvection σ ε u y c₀ := by
  have hyu : (σ ∘ y) ⬝ᵥ (Q *ᵥ u) = 0 := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp huy
  set r := d⁻¹
  have hury : (σ ∘ (u + r • y)) ⬝ᵥ (Q *ᵥ (u + r • y)) = 0 := by
    simp [map_comp_add, TauCeti.map_comp_smul, add_dotProduct, smul_dotProduct, mulVec_add,
      mulVec_smul, hu, hy, huy, hyu]
  have ha₁ : -d + ε * σ (-d) = 0 := by rw [map_neg]; linear_combination -hd
  have ha₂ : -(d * (r * σ r)) + ε * σ (-(d * (r * σ r))) = 0 := by
    rw [map_neg, map_mul, map_mul, hσ r]; linear_combination -(r * σ r) * hd
  obtain ⟨g₁, hg₁, hM₁⟩ := exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ hu ha₁
  obtain ⟨g₂, hg₂, hM₂⟩ := exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ hy ha₂
  obtain ⟨g₃, hg₃, hM₃⟩ := exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ hury hd
  let k₁ : Q.specialIsometryGroup σ := ⟨g₁, hg₁⟩
  let k₂ : Q.specialIsometryGroup σ := ⟨g₂, hg₂⟩
  let k₃ : Q.specialIsometryGroup σ := ⟨g₃, hg₃⟩
  refine ⟨0, k₁ * k₂ * k₃, mul_mem (mul_mem (hH hu ha₁ k₁ hM₁) (hH hy ha₂ k₂ hM₂))
    (hH hury hd k₃ hM₃), ?_⟩
  simp only [k₁, k₂, k₃, Subgroup.coe_mul, SpecialLinearGroup.coe_mul, hM₁, hM₂, hM₃]
  have hdr : d * σ r = -ε := mul_right_cancel₀ ((map_ne_zero σ).mpr hd0) <| by
    rw [mul_assoc, show σ r = (σ d)⁻¹ from map_inv₀ σ d, inv_mul_cancel₀ ((map_ne_zero σ).mpr hd0),
      mul_one]
    linear_combination hd
  refine mulVec_injective (funext fun x ↦ ?_)
  rw [← mulVec_mulVec, ← mulVec_mulVec, unitaryTransvection_mulVec, unitaryTransvection_mulVec,
    unitaryTransvection_mulVec, siegelTransvection_mulVec]
  simp only [map_comp_add, TauCeti.map_comp_smul, add_dotProduct, smul_dotProduct, mulVec_add,
    mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, hu, hy, huy, hyu, mul_zero,
    add_zero, zero_smul]
  have hdr_inv : d * r = 1 := mul_inv_cancel₀ hd0
  rw [show (d * (((σ ∘ u) ⬝ᵥ (Q *ᵥ x)) + σ r * ((σ ∘ y) ⬝ᵥ (Q *ᵥ x)))) • (u + r • y) =
    (d * ((σ ∘ u) ⬝ᵥ (Q *ᵥ x)) + (d * σ r) * ((σ ∘ y) ⬝ᵥ (Q *ᵥ x))) • u +
      ((d * r) * ((σ ∘ u) ⬝ᵥ (Q *ᵥ x)) + d * (r * σ r) * ((σ ∘ y) ⬝ᵥ (Q *ᵥ x))) • y by module,
    hdr, hdr_inv]
  module

private theorem exists_siegelTransvection_add (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) {H : Subgroup (Q.specialIsometryGroup σ)}
    {u y₁ y₂ : n → K} (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0)
    (huy₂ : (σ ∘ u) ⬝ᵥ (Q *ᵥ y₂) = 0) (huy₁ : (σ ∘ u) ⬝ᵥ (Q *ᵥ y₁) = 0)
    (h₁ : ∃ c₁ : K, ∃ k₁ ∈ H,
      ((k₁ : SpecialLinearGroup n K) : Matrix n n K) = Q.siegelTransvection σ ε u y₁ c₁)
    (h₂ : ∃ c₂ : K, ∃ k₂ ∈ H,
      ((k₂ : SpecialLinearGroup n K) : Matrix n n K) = Q.siegelTransvection σ ε u y₂ c₂) :
    ∃ c₀ : K, ∃ h ∈ H,
      ((h : SpecialLinearGroup n K) : Matrix n n K) = Q.siegelTransvection σ ε u (y₁ + y₂) c₀ := by
  obtain ⟨c₁, k₁, hk₁H, hk₁⟩ := h₁
  obtain ⟨c₂, k₂, hk₂H, hk₂⟩ := h₂
  have hy₁u : (σ ∘ y₁) ⬝ᵥ (Q *ᵥ u) = 0 := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp huy₁
  refine ⟨c₁ + c₂ - ε * ((σ ∘ y₁) ⬝ᵥ (Q *ᵥ y₂)), k₁ * k₂, mul_mem hk₁H hk₂H, ?_⟩
  rw [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, hk₁, hk₂,
    siegelTransvection_mul_siegelTransvection hu huy₂ hy₁u]

private theorem exists_siegelTransvection_of_card_ge_four (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    (hnorm : ∀ t, σ t = t → ∃ b, b * σ b = t)
    {H : Subgroup (Q.specialIsometryGroup σ)}
    (hH : ∀ {x : n → K} {a : K}, (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0 → a + ε * σ a = 0 →
      ∀ g : Q.specialIsometryGroup σ,
        ((g : SpecialLinearGroup n K) : Matrix n n K) = Q.unitaryTransvection σ x a → g ∈ H)
    {u : n → K} (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0)
    {W : Submodule K (n → K)} (hdimW : 2 ≤ Module.finrank K W)
    (horth_u : ∀ y ∈ W, (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0)
    (hW : ∀ x ∈ W, (∀ y ∈ W, (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 0) → x = 0)
    {w : n → K} (hwW : w ∈ W) :
    ∃ c₀ : K, ∃ h ∈ H,
      ((h : SpecialLinearGroup n K) : Matrix n n K) = Q.siegelTransvection σ ε u w c₀ := by
  obtain ⟨d, hd0, hd⟩ := hadm
  obtain ⟨w₀, hw₀W, hw₀_ne, hw₀_iso⟩ :=
    exists_mem_ne_zero_comp_dotProduct_mulVec_self_eq_zero hσ hQ hε hnorm hW hdimW
  have hpair (y : n → K) (hyW : y ∈ W) (hyw₀ : (σ ∘ y) ⬝ᵥ (Q *ᵥ w₀) ≠ 0) :
      ∃ c₀ : K, ∃ h ∈ H,
        ((h : SpecialLinearGroup n K) : Matrix n n K) = Q.siegelTransvection σ ε u y c₀ := by
    obtain ⟨a, ha⟩ :=
      exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero hσ hQ htr hw₀_iso hyw₀
    have hy₁W : y + a • w₀ ∈ W := W.add_mem hyW (W.smul_mem a hw₀W)
    have hy₂W : -(a • w₀) ∈ W := W.neg_mem (W.smul_mem a hw₀W)
    have hy₂_iso : (σ ∘ (-(a • w₀))) ⬝ᵥ (Q *ᵥ (-(a • w₀))) = 0 := by
      rw [← neg_one_smul K (a • w₀), comp_smul_dotProduct_mulVec_smul,
        comp_smul_dotProduct_mulVec_smul, hw₀_iso, mul_zero, mul_zero]
    have hsum := exists_siegelTransvection_add hσ hQ hu (horth_u _ hy₂W) (horth_u _ hy₁W)
      (siegelTransvection_zero_mem_of_isotropic hσ hQ hd0 hd hH hu ha (horth_u _ hy₁W))
      (siegelTransvection_zero_mem_of_isotropic hσ hQ hd0 hd hH hu hy₂_iso (horth_u _ hy₂W))
    rwa [add_neg_cancel_right] at hsum
  by_cases hww₀ : (σ ∘ w) ⬝ᵥ (Q *ᵥ w₀) = 0
  · obtain ⟨y, hyW, hw₀y⟩ : ∃ y ∈ W, (σ ∘ w₀) ⬝ᵥ (Q *ᵥ y) ≠ 0 := by
      by_contra! h0
      exact hw₀_ne (hW w₀ hw₀W h0)
    have hyw₀ : (σ ∘ y) ⬝ᵥ (Q *ᵥ w₀) ≠ 0 := (comp_dotProduct_mulVec_ne_zero_comm hσ hQ).mp hw₀y
    have hwy_w₀ : (σ ∘ (w + y)) ⬝ᵥ (Q *ᵥ w₀) ≠ 0 := by
      rwa [map_comp_add, add_dotProduct, hww₀, zero_add]
    have hnegy_w₀ : (σ ∘ (-y)) ⬝ᵥ (Q *ᵥ w₀) ≠ 0 := by
      rwa [map_comp_neg, neg_dotProduct, neg_ne_zero]
    have hsum := exists_siegelTransvection_add hσ hQ hu (horth_u _ (W.neg_mem hyW))
      (horth_u _ (W.add_mem hwW hyW)) (hpair (w + y) (W.add_mem hwW hyW) hwy_w₀)
      (hpair (-y) (W.neg_mem hyW) hnegy_w₀)
    rwa [add_neg_cancel_right] at hsum
  · exact hpair w hwW hww₀

/-! ### Main generation theorems -/

/-- **Unitary transvections generate the special unitary group.** Let `σ` be a nontrivial
involution of `K`, let `Q` be an invertible `ε`-Hermitian matrix, and assume trace surjectivity,
existence of a nonzero admissible parameter, and norm surjectivity onto `K^σ`. If either `K^σ` has
at least three elements (`∃ t, t ≠ 0 ∧ t ≠ 1 ∧ σ(t) = t`) or `4 ≤ Fintype.card n`, then any
subgroup of `Q.specialIsometryGroup σ` containing all admissible unitary transvections is `⊤`. -/
theorem eq_top_of_unitaryTransvection_mem (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    (hnorm : ∀ t, σ t = t → ∃ b, b * σ b = t)
    (hσ_ne : ∃ a : K, σ a ≠ a)
    (hgen : (∃ t : K, t ≠ 0 ∧ t ≠ 1 ∧ σ t = t) ∨ 4 ≤ Fintype.card n)
    (H : Subgroup (Q.specialIsometryGroup σ))
    (hH : ∀ {v : n → K} {a : K}, (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0 → a + ε * σ a = 0 →
      ∀ g : Q.specialIsometryGroup σ,
        ((g : SpecialLinearGroup n K) : Matrix n n K) = Q.unitaryTransvection σ v a → g ∈ H) :
    H = ⊤ := by
  refine eq_top_of_siegelTransvection_mem hσ hQ hdet htr hadm hnorm hσ_ne H
    fun {u w c} hu huw _ g hg ↦ ?_
  by_cases hu0 : u = 0
  · have hg1 : g = 1 := by
      refine Subtype.ext (SpecialLinearGroup.ext _ _ (Matrix.ext_iff.mpr ?_))
      rw [hg, hu0, siegelTransvection_zero_left, Subgroup.coe_one, SpecialLinearGroup.coe_one]
    exact hg1 ▸ one_mem H
  rcases isEmpty_or_nonempty n with _ | _
  · exact absurd (funext isEmptyElim) hu0
  have hε : ε * ε = 1 := mul_self_eq_one_of_trace_of_det_ne_zero hσ hQ hdet htr
  have hσ_eps : σ ε = ε := map_eq_self_of_mul_self_eq_one_of_det_ne_zero hσ hQ hdet hε
  obtain ⟨v, hv, huv⟩ := exists_hyperbolic_partner hσ hQ hdet htr hu0 hu
  obtain ⟨W, -, -, hPW, -, hfinW, hmemW, -, -, hW⟩ :=
    exists_hyperbolic_complement (U := ⊤) hσ hQ hε
      (fun x _ hx ↦
        eq_zero_of_forall_comp_dotProduct_mulVec_eq_zero hdet fun y ↦ hx y trivial)
      trivial trivial hu hv huv
  obtain ⟨p, hpP, w_W, hwW, hw_eq⟩ := Submodule.mem_sup.mp (hPW ▸ (Submodule.mem_top : w ∈ ⊤))
  obtain ⟨u', hu', v', hv', rfl⟩ := Submodule.mem_sup.mp hpP
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu'
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hv'
  have hb0 : b = 0 := by
    have := huw
    rw [← hw_eq, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, dotProduct_add, dotProduct_add,
      dotProduct_smul, dotProduct_smul, hu, huv, ((hmemW w_W).mp hwW).2.1] at this
    simpa using this
  have hg' : ((g : SpecialLinearGroup n K) : Matrix n n K) =
      Q.siegelTransvection σ ε u w_W (c + a - ε * σ a) := by
    rw [hg, show w = w_W + a • u by rw [← hw_eq, hb0, zero_smul, add_zero, add_comm],
      siegelTransvection_add_smul]
  have horth_u : ∀ y ∈ W, (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0 := fun y hy ↦ ((hmemW y).mp hy).2.1
  have horth_v : ∀ y ∈ W, (σ ∘ v) ⬝ᵥ (Q *ᵥ y) = 0 := fun y hy ↦ ((hmemW y).mp hy).2.2
  obtain ⟨c₀, h₀, hh₀H, hh₀⟩ :
      ∃ c₀ : K, ∃ h ∈ H,
        ((h : SpecialLinearGroup n K) : Matrix n n K) = Q.siegelTransvection σ ε u w_W c₀ := by
    rcases hgen with ⟨t, ht0, ht1, ht⟩ | hcard
    · exact exists_siegelTransvection_of_fixed_scalar hσ hQ hε hσ_eps htr hadm ht0 ht1 ht hH
        hu hv huv hPW horth_u horth_v hwW
    · have hdimW : 2 ≤ Module.finrank K W := by
        rw [finrank_top, Module.finrank_pi] at hfinW; omega
      exact exists_siegelTransvection_of_card_ge_four hσ hQ hε htr hadm hnorm hH hu hdimW horth_u
        hW hwW
  exact mem_of_exists_siegelTransvection_same_vec hσ hQ hε hu hv huv (horth_u w_W hwW)
    (fun _ ↦ hH hu) hh₀H hh₀ hg'

/-- **The unitary transvection groups of isotropic points generate the special unitary group.** -/
theorem iSup_unitaryTransvectionSubgroup_eq_top (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    (hnorm : ∀ t, σ t = t → ∃ b, b * σ b = t)
    (hσ_ne : ∃ a : K, σ a ≠ a)
    (hgen : (∃ t : K, t ≠ 0 ∧ t ≠ 1 ∧ σ t = t) ∨ 4 ≤ Fintype.card n) :
    ⨆ p : Q.isotropicPoints σ, Q.unitaryTransvectionSubgroup σ p = ⊤ := by
  refine eq_top_of_unitaryTransvection_mem hσ hQ hdet htr hadm hnorm hσ_ne hgen _
    fun {v a} hv _ g hg ↦ ?_
  by_cases hv0 : v = 0
  · have hg1 : g = 1 := by
      refine Subtype.ext (SpecialLinearGroup.ext _ _ (Matrix.ext_iff.mpr ?_))
      rw [hg, hv0, unitaryTransvection_zero_left, Subgroup.coe_one, SpecialLinearGroup.coe_one]
    exact hg1 ▸ one_mem _
  · have hp : Projectivization.mk K v hv0 ∈ Q.isotropicPoints σ :=
      (mk_mem_isotropicPoints_iff hv0).mpr hv
    exact Subgroup.mem_iSup_of_mem ⟨_, hp⟩
      ((mem_unitaryTransvectionSubgroup_mk_iff hv0 hp).mpr ⟨a, hg⟩)

end Matrix
