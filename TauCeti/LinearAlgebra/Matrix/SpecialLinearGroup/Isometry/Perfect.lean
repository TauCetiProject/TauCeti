/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Commutator.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Generation
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Group.Hom.Defs
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Perfectness of the special unitary group

Let `σ` be an involution of a field `K`, let `Q` be an invertible `ε`-Hermitian matrix on an index
type `n` with `3 ≤ Fintype.card n`, and assume that the `ε`-trace `t ↦ t + ε σ(t)` is onto
`{s | σ(s) = ε s}`. For an isotropic vector `u ≠ 0`, extending `u` to a hyperbolic pair `(u, v)`
leaves a nondegenerate orthogonal complement `W` of dimension `Fintype.card n - 2 ≥ 1`, which
therefore contains vectors `w₁, w₂ ∈ W` with `B(w₁, w₂) ≠ 0`.

By the Heisenberg law `Matrix.siegelTransvection_mul_siegelTransvection`, the commutator of two
admissible Siegel transformations `S(u, y₁, c₁)` and `S(u, y₂, c₂)` with `y₁, y₂ ∈ u^⊥` is the
unitary transvection `τ_{u, σ(B(y₁, y₂)) - ε B(y₁, y₂)}`. Every admissible parameter `a`
(`a + ε σ(a) = 0`) has the form `σ(s) - ε s`—via `s = -(2⁻¹ ε a)` when `2 ≠ 0`, and via trace
surjectivity when `2 = 0`—so rescaling `w₁` realizes `τ_{u, a}` as a commutator in
`Matrix.specialIsometryGroup Q σ`.

Combined with `Matrix.eq_top_of_unitaryTransvection_mem`, this proves that
`Matrix.specialIsometryGroup Q σ` is perfect whenever `3 ≤ Fintype.card n` and either `K^σ` has at
least three elements or `4 ≤ Fintype.card n` (excluding only the solvable group `SU₃(2)`).

## Main results

* `Matrix.unitaryTransvection_mem_commutator`: when `3 ≤ Fintype.card n`, every admissible unitary
  transvection lies in `commutator (Q.specialIsometryGroup σ)`.
* `Matrix.unitaryTransvectionSubgroup_le_commutator`: when `3 ≤ Fintype.card n`, every point
  transvection group `Q.unitaryTransvectionSubgroup σ p` lies in
  `commutator (Q.specialIsometryGroup σ)`.
* `Matrix.commutator_specialIsometryGroup_eq_top`: under the generation hypotheses and
  `3 ≤ Fintype.card n`, `commutator (Q.specialIsometryGroup σ) = ⊤`.

## References

* J. Dieudonné, *On the structure of unitary groups*, Trans. Amer. Math. Soc. **72** (1952),
  367--385.
* D. E. Taylor, *The Geometry of the Classical Groups* (1992), §10.4 and §11.5.
* L. C. Grove, *Classical Groups and Geometric Algebra* (2002), Chapter 11.
-/

public section

open scoped commutatorElement LinearAlgebra.Projectivization

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] {Q : Matrix n n K} {σ : K →+* K}
  {ε : K}

/-- Every `a` with `a + ε σ(a) = 0` can be written as `σ(s) - ε s` under trace surjectivity. -/
private theorem exists_map_sub_mul_eq_of_admissible (hε : ε * ε = 1) (hσ_eps : σ ε = ε)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) {a : K} (ha : a + ε * σ a = 0) :
    ∃ s : K, σ s - ε * s = a := by
  by_cases h2 : (2 : K) = 0
  · obtain ⟨t, ht⟩ := htr a (by linear_combination ε * ha - σ a * hε - ε * a * h2)
    refine ⟨-(ε * t), ?_⟩
    rw [map_neg, map_mul, hσ_eps]
    linear_combination ht - ε * σ t * h2 + t * hε
  · refine ⟨-(2⁻¹ * ε * a), ?_⟩
    have hσa : σ a = -(ε * a) := by linear_combination ε * ha - σ a * hε
    rw [map_neg, map_mul, map_mul, map_inv₀, map_ofNat, hσ_eps, hσa]
    calc -(2⁻¹ * ε * -(ε * a)) - ε * -(2⁻¹ * ε * a)
        = (2 * 2⁻¹) * (ε * ε) * a := by ring
      _ = a := by rw [mul_inv_cancel₀ h2, hε]; ring

/-- The commutator of two Siegel transformations along `u` with vectors `y₁, y₂ ∈ u^⊥` is the
unitary transvection `τ_{u, σ(B(y₁, y₂)) - ε B(y₁, y₂)}`. -/
private theorem coe_commutatorElement_siegelTransvection (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) {u y₁ y₂ : n → K} {c₁ c₂ : K}
    (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (huy₁ : (σ ∘ u) ⬝ᵥ (Q *ᵥ y₁) = 0)
    (huy₂ : (σ ∘ u) ⬝ᵥ (Q *ᵥ y₂) = 0) {s₁ s₂ : Q.specialIsometryGroup σ}
    (hs₁ : ((s₁ : SpecialLinearGroup n K) : Matrix n n K) = Q.siegelTransvection σ ε u y₁ c₁)
    (hs₂ : ((s₂ : SpecialLinearGroup n K) : Matrix n n K) = Q.siegelTransvection σ ε u y₂ c₂) :
    (((⁅s₁, s₂⁆ : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) : Matrix n n K) =
      Q.unitaryTransvection σ u (σ ((σ ∘ y₁) ⬝ᵥ (Q *ᵥ y₂)) - ε * ((σ ∘ y₁) ⬝ᵥ (Q *ᵥ y₂))) := by
  have hy₁u : (σ ∘ y₁) ⬝ᵥ (Q *ᵥ u) = 0 := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp huy₁
  have hy₂u : (σ ∘ y₂) ⬝ᵥ (Q *ᵥ u) = 0 := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp huy₂
  set z := y₁ + y₂
  have huz : (σ ∘ u) ⬝ᵥ (Q *ᵥ z) = 0 := by simp [z, mulVec_add, huy₁, huy₂]
  have hzu : (σ ∘ z) ⬝ᵥ (Q *ᵥ u) = 0 := (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp huz
  set γ₁ := c₁ + c₂ - ε * ((σ ∘ y₁) ⬝ᵥ (Q *ᵥ y₂))
  set γ₂ := c₂ + c₁ - ε * ((σ ∘ y₂) ⬝ᵥ (Q *ᵥ y₁))
  have h₁₂ : (((s₁ * s₂ : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) : Matrix n n K) =
      Q.siegelTransvection σ ε u z γ₁ := by
    rw [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, hs₁, hs₂,
      siegelTransvection_mul_siegelTransvection hu huy₂ hy₁u]
  have h₂₁ : (((s₂ * s₁ : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) : Matrix n n K) =
      Q.siegelTransvection σ ε u z γ₂ := by
    rw [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, hs₂, hs₁,
      siegelTransvection_mul_siegelTransvection hu huy₁ hy₂u, add_comm y₂ y₁]
  have h₂₁_inv : ((((s₂ * s₁)⁻¹ : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) :
      Matrix n n K) = Q.siegelTransvection σ ε u (-z) (-γ₂ - ε * ((σ ∘ z) ⬝ᵥ (Q *ᵥ z))) := by
    have hR := h₂₁ ▸ siegelTransvection_mul_siegelTransvection_neg_eq_one hu huz hzu γ₂
    have hL : (((s₂ * s₁ : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) : Matrix n n K) *
        ((((s₂ * s₁)⁻¹ : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) :
          Matrix n n K) = 1 := by
      rw [← SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
        SpecialLinearGroup.coe_one]
    rw [← inv_eq_right_inv hL, inv_eq_right_inv hR]
  have hcomm : ⁅s₁, s₂⁆ = (s₁ * s₂) * (s₂ * s₁)⁻¹ :=
    eq_mul_inv_of_mul_eq (by simp [commutatorElement_def, mul_assoc])
  have hu_negz : (σ ∘ u) ⬝ᵥ (Q *ᵥ (-z)) = 0 := by rw [mulVec_neg, dotProduct_neg, huz, neg_zero]
  rw [hcomm, Subgroup.coe_mul, SpecialLinearGroup.coe_mul, h₁₂, h₂₁_inv,
    siegelTransvection_mul_siegelTransvection hu hu_negz hzu, add_neg_cancel,
    siegelTransvection_zero_eq_unitaryTransvection, mulVec_neg, dotProduct_neg]
  refine congrArg (Q.unitaryTransvection σ u) ?_
  have hswap := comp_dotProduct_mulVec_swap hσ hQ hε y₁ y₂
  simp only [γ₁, γ₂, hswap]
  linear_combination σ ((σ ∘ y₁) ⬝ᵥ (Q *ᵥ y₂)) * hε

/-- **Every admissible unitary transvection is a commutator in dimension at least three.** -/
theorem unitaryTransvection_mem_commutator (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
    (hn : 3 ≤ Fintype.card n) {u : n → K} {a : K}
    (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (ha : a + ε * σ a = 0)
    (g : Q.specialIsometryGroup σ)
    (hg : ((g : SpecialLinearGroup n K) : Matrix n n K) = Q.unitaryTransvection σ u a) :
    g ∈ commutator (Q.specialIsometryGroup σ) := by
  by_cases hu0 : u = 0
  · have hg1 : g = 1 := by
      refine Subtype.ext (SpecialLinearGroup.ext _ _ (Matrix.ext_iff.mpr ?_))
      rw [hg, hu0, unitaryTransvection_zero_left, Subgroup.coe_one, SpecialLinearGroup.coe_one]
    exact hg1 ▸ one_mem _
  have : Nonempty n := Fintype.card_pos_iff.mp (by omega)
  have hε : ε * ε = 1 := mul_self_eq_one_of_trace_of_det_ne_zero hσ hQ hdet htr
  have hσ_eps : σ ε = ε := map_eq_self_of_mul_self_eq_one_of_det_ne_zero hσ hQ hdet hε
  obtain ⟨y, huy⟩ : ∃ y : n → K, (σ ∘ u) ⬝ᵥ (Q *ᵥ y) ≠ 0 := by
    by_contra! h0
    exact hu0 (eq_zero_of_forall_comp_dotProduct_mulVec_eq_zero hdet h0)
  obtain ⟨c, hc⟩ := exists_comp_add_smul_dotProduct_mulVec_add_smul_eq_zero hσ hQ htr hu
    ((comp_dotProduct_mulVec_ne_zero_comm hσ hQ).mp huy)
  set v := ((σ ∘ u) ⬝ᵥ (Q *ᵥ y))⁻¹ • (y + c • u)
  have hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0 := by rw [comp_smul_dotProduct_mulVec_smul, hc, mul_zero]
  have huv : (σ ∘ u) ⬝ᵥ (Q *ᵥ v) = 1 := by
    simp [v, mulVec_smul, mulVec_add, hu, inv_mul_cancel₀ huy]
  obtain ⟨W, -, -, -, -, hfinW, hmemW, -, -, hW⟩ := exists_hyperbolic_complement (U := ⊤) hσ hQ hε
    (fun x _ hx ↦ eq_zero_of_forall_comp_dotProduct_mulVec_eq_zero hdet fun z ↦ hx z trivial)
    trivial trivial hu hv huv
  have hW_ne : W ≠ ⊥ := by
    intro hbot; rw [hbot, finrank_bot, finrank_top, Module.finrank_pi] at hfinW; omega
  obtain ⟨w₁, hw₁W, hw₁_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW_ne
  obtain ⟨w₂, hw₂W, hw₁₂⟩ : ∃ w₂ ∈ W, (σ ∘ w₁) ⬝ᵥ (Q *ᵥ w₂) ≠ 0 := by
    by_contra! h0; exact hw₁_ne (hW w₁ hw₁W h0)
  obtain ⟨s, hs⟩ := exists_map_sub_mul_eq_of_admissible hε hσ_eps htr ha
  set y₁ := σ (s * ((σ ∘ w₁) ⬝ᵥ (Q *ᵥ w₂))⁻¹) • w₁
  have hy₁W : y₁ ∈ W := W.smul_mem _ hw₁W
  have hy₁₂ : (σ ∘ y₁) ⬝ᵥ (Q *ᵥ w₂) = s := by
    simp [y₁, TauCeti.map_comp_smul, hσ _, inv_mul_cancel_right₀ hw₁₂]
  obtain ⟨c₁, hc₁⟩ := htr (-(ε * ((σ ∘ y₁) ⬝ᵥ (Q *ᵥ y₁)))) (by
    rw [map_neg, map_mul, hσ_eps, apply_comp_dotProduct_mulVec hσ hQ y₁ y₁]; ring)
  obtain ⟨c₂, hc₂⟩ := htr (-(ε * ((σ ∘ w₂) ⬝ᵥ (Q *ᵥ w₂)))) (by
    rw [map_neg, map_mul, hσ_eps, apply_comp_dotProduct_mulVec hσ hQ w₂ w₂]; ring)
  obtain ⟨k₁, hk₁, hM₁⟩ := exists_mem_specialIsometryGroup_coe_eq_siegelTransvection (c := c₁)
    hσ hQ hu (((hmemW y₁).mp hy₁W).2.1) (by linear_combination hc₁)
  obtain ⟨k₂, hk₂, hM₂⟩ := exists_mem_specialIsometryGroup_coe_eq_siegelTransvection (c := c₂)
    hσ hQ hu (((hmemW w₂).mp hw₂W).2.1) (by linear_combination hc₂)
  have hcomm_mat := coe_commutatorElement_siegelTransvection hσ hQ hε hu (((hmemW y₁).mp hy₁W).2.1)
    (((hmemW w₂).mp hw₂W).2.1) (s₁ := ⟨k₁, hk₁⟩) (s₂ := ⟨k₂, hk₂⟩) hM₁ hM₂
  rw [hy₁₂, hs, ← hg] at hcomm_mat
  have hg_eq : g = ⁅(⟨k₁, hk₁⟩ : Q.specialIsometryGroup σ), ⟨k₂, hk₂⟩⁆ :=
    Subtype.ext (SpecialLinearGroup.ext _ _ (Matrix.ext_iff.mpr hcomm_mat.symm))
  exact hg_eq ▸ Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- **The transvection subgroup of each isotropic point lies in the commutator subgroup** when
`3 ≤ Fintype.card n`. -/
theorem unitaryTransvectionSubgroup_le_commutator (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
    (hn : 3 ≤ Fintype.card n) (p : Q.isotropicPoints σ) :
    Q.unitaryTransvectionSubgroup σ p ≤ commutator (Q.specialIsometryGroup σ) := by
  intro g hg
  obtain ⟨a, ha⟩ := mem_unitaryTransvectionSubgroup_iff.mp hg
  have hadm : a + ε * σ a = 0 :=
    (exists_coe_eq_unitaryTransvection_iff hσ hQ hdet p a).mp ⟨⟨g, hg⟩, ha⟩
  exact unitaryTransvection_mem_commutator hσ hQ hdet htr hn (comp_rep_dotProduct_mulVec_rep p)
    hadm g ha

/-- **The special unitary group is perfect** when `3 ≤ Fintype.card n` and either `K^σ` has at
least three elements or `4 ≤ Fintype.card n`. -/
theorem commutator_specialIsometryGroup_eq_top (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    (hnorm : ∀ t, σ t = t → ∃ b, b * σ b = t)
    (hσ_ne : ∃ a : K, σ a ≠ a)
    (hn : 3 ≤ Fintype.card n)
    (hgen : (∃ t : K, t ≠ 0 ∧ t ≠ 1 ∧ σ t = t) ∨ 4 ≤ Fintype.card n) :
    commutator (Q.specialIsometryGroup σ) = ⊤ :=
  eq_top_of_unitaryTransvection_mem hσ hQ hdet htr hadm hnorm hσ_ne hgen _
    (unitaryTransvection_mem_commutator hσ hQ hdet htr hn)

end Matrix
