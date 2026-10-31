/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Orientation
public import TauCeti.Geometry.Symplectic.Prod.Basic
public import TauCeti.Geometry.Symplectic.Rescale
public import TauCeti.Geometry.Symplectic.SymplecticTransport
public import TauCeti.LinearAlgebra.Orientation.Prod

import Mathlib.LinearAlgebra.SymplecticGroup
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# Darboux bases and the symplectic orientation

Let `ω` be a symplectic form on a finite-dimensional real vector space `V`. A **Darboux basis** of
`(V, ω)` (`TauCeti.SymplecticForm.IsDarbouxBasis`) is a basis `(q₁, p₁, …, qₙ, pₙ)`, indexed by
`Fin n × Fin 2` with `qᵢ = b (i, 0)` and `pᵢ = b (i, 1)`, in which

`ω(qᵢ, qⱼ) = 0`, `ω(pᵢ, pⱼ) = 0`, `ω(qᵢ, pⱼ) = δᵢⱼ`,

so that `ω = ∑ dqᵢ ∧ dpᵢ` in the dual coordinates. Darboux bases exist
(`TauCeti.SymplecticForm.exists_isDarbouxBasis`), from the symplectic bases of nondegenerate
alternating forms. The change of basis between two Darboux bases is a symplectic matrix, so it has
determinant `1` by Mathlib's `SymplecticGroup.det_eq_one`
(`TauCeti.SymplecticForm.IsDarbouxBasis.det_eq_one`). Consequently every linear symplectomorphism
of `(V, ω)` has determinant `1` (`TauCeti.SymplecticForm.IsSymplectomorphism.det_eq_one`).

All Darboux bases, listed in the interleaved order `(q₁, p₁, q₂, p₂, …, qₙ, pₙ)` (the reindexing
by `finProdFinEquiv`), therefore induce one orientation of `V`: the **symplectic orientation**
`TauCeti.SymplecticForm.orientation` (`TauCeti.SymplecticForm.IsDarbouxBasis.orientation_reindex`).
Classically it is described as the orientation in which the top form `ωⁿ`, which takes the
value `n!` on `(q₁, p₁, …, qₙ, pₙ)`, is positive; this file characterizes it through Darboux
bases only and does not use exterior powers of `ω`.

The symplectic orientation is natural: a linear symplectomorphism carries the symplectic
orientation of its source to that of its target
(`TauCeti.SymplecticForm.IsSymplectomorphism.map_orientation`). Rescaling `ω` by `c ≠ 0` changes
it by the sign of `cⁿ` (`TauCeti.SymplecticForm.orientation_rescale`), so positive rescaling
preserves it, while `-ω` has the opposite orientation exactly when `n` is odd. The symplectic
orientation of a direct sum `ω₁ ⊕ ω₂` is the product of the symplectic orientations of the
summands (`TauCeti.SymplecticForm.orientation_prod`).

This is the linear model for the orientation of a symplectic manifold, read on each tangent
space, and the product law computes the orientation of a product such as
`(ℝ², ds ∧ dt) × (V, ω)`.

## Main definitions

* `TauCeti.SymplecticForm.IsDarbouxBasis ω b`: `b` is a Darboux basis of `(V, ω)`.
* `TauCeti.SymplecticForm.orientation ω hk`: the symplectic orientation of `V`, indexed by
  `Fin k` where `finrank ℝ V = k`.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 2.1 (symplectic bases and the symplectic volume form `ωⁿ`).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 1.1 and Homework 1.
-/

public section

open Module

namespace TauCeti

namespace SymplecticForm

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-! ### Darboux bases -/

/-- A **Darboux basis** of a symplectic vector space `(V, ω)`: a basis `(q₁, p₁, …, qₙ, pₙ)`,
with `qᵢ = b (i, 0)` and `pᵢ = b (i, 1)`, satisfying `ω(qᵢ, qⱼ) = 0`, `ω(pᵢ, pⱼ) = 0` and
`ω(qᵢ, pⱼ) = δᵢⱼ`. -/
structure IsDarbouxBasis (ω : SymplecticForm V) {n : ℕ} (b : Basis (Fin n × Fin 2) ℝ V) :
    Prop where
  /-- The vectors `qᵢ` pair trivially with each other. -/
  apply_fst_fst : ∀ i j, ω (b (i, 0)) (b (j, 0)) = 0
  /-- The vectors `pᵢ` pair trivially with each other. -/
  apply_snd_snd : ∀ i j, ω (b (i, 1)) (b (j, 1)) = 0
  /-- `ω(qᵢ, pⱼ) = δᵢⱼ`. -/
  apply_fst_snd : ∀ i j, ω (b (i, 0)) (b (j, 1)) = if i = j then 1 else 0

variable {ω : SymplecticForm V} {n : ℕ} {b c : Basis (Fin n × Fin 2) ℝ V}

/-- In a Darboux basis, `ω(pᵢ, qⱼ) = -δᵢⱼ`. -/
theorem IsDarbouxBasis.apply_snd_fst (hb : ω.IsDarbouxBasis b) (i j : Fin n) :
    ω (b (i, 1)) (b (j, 0)) = if i = j then -1 else 0 := by
  rw [← ω.neg_eq, hb.apply_fst_snd j i]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd h₁.symm h₂
  · exact absurd h₂.symm h₁
  · exact neg_zero

/-- The relabelling `(i, 0) ↦ inr i`, `(i, 1) ↦ inl i`, under which a Darboux basis becomes a
basis in which `ω` has Mathlib's standard symplectic matrix `Matrix.J`. -/
private def darbouxIndexEquiv (n : ℕ) : Fin n × Fin 2 ≃ Fin n ⊕ Fin n where
  toFun p := if p.2 = 0 then Sum.inr p.1 else Sum.inl p.1
  invFun := Sum.elim (fun i ↦ (i, 1)) (fun i ↦ (i, 0))
  left_inv := by
    rintro ⟨i, a⟩
    fin_cases a <;> simp
  right_inv := by
    rintro (i | i) <;> simp

private theorem darbouxIndexEquiv_symm_inl (i : Fin n) :
    (darbouxIndexEquiv n).symm (Sum.inl i) = (i, 1) := rfl

private theorem darbouxIndexEquiv_symm_inr (i : Fin n) :
    (darbouxIndexEquiv n).symm (Sum.inr i) = (i, 0) := rfl

/-- A Darboux basis, relabelled by `darbouxIndexEquiv`, is a basis in which the matrix of `ω` is
`Matrix.J`. -/
private theorem IsDarbouxBasis.toMatrix_reindex (hb : ω.IsDarbouxBasis b) :
    LinearMap.BilinForm.toMatrix (b.reindex (darbouxIndexEquiv n)) ω.toBilinForm =
      Matrix.J (Fin n) ℝ := by
  ext (i | i) (j | j) <;>
    simp only [LinearMap.BilinForm.toMatrix_apply, Basis.reindex_apply, darbouxIndexEquiv_symm_inl,
      darbouxIndexEquiv_symm_inr, Matrix.J, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply,
      Matrix.one_apply]
  · exact hb.apply_snd_snd i j
  · exact (hb.apply_snd_fst i j).trans (by split_ifs <;> simp)
  · exact hb.apply_fst_snd i j
  · exact hb.apply_fst_fst i j

/-- Conversely, relabelling a basis in which `ω` has matrix `Matrix.J` gives a Darboux basis. -/
private theorem isDarbouxBasis_reindex_symm_of_toMatrix {b : Basis (Fin n ⊕ Fin n) ℝ V}
    (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = Matrix.J (Fin n) ℝ) :
    ω.IsDarbouxBasis (b.reindex (darbouxIndexEquiv n).symm) := by
  have h (x y) : ω (b x) (b y) = Matrix.J (Fin n) ℝ x y := by
    rw [← hb, LinearMap.BilinForm.toMatrix_apply]
  refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩ <;>
    simp only [Basis.reindex_apply, Equiv.symm_symm] <;>
    simp [darbouxIndexEquiv, h, Matrix.J, Matrix.one_apply]

/-- **Darboux bases exist**: every finite-dimensional symplectic vector space has a Darboux
basis. -/
theorem exists_isDarbouxBasis [FiniteDimensional ℝ V] (ω : SymplecticForm V) :
    ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V), ω.IsDarbouxBasis b := by
  obtain ⟨n, b, hb⟩ := ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate
  exact ⟨n, _, isDarbouxBasis_reindex_symm_of_toMatrix hb⟩

/-- A Darboux basis exists for any prescribed number `n` of pairs with `finrank ℝ V = n * 2`. -/
theorem exists_isDarbouxBasis_of_finrank_eq [FiniteDimensional ℝ V] (ω : SymplecticForm V)
    (hn : finrank ℝ V = n * 2) : ∃ b : Basis (Fin n × Fin 2) ℝ V, ω.IsDarbouxBasis b := by
  obtain ⟨m, b, hb⟩ := ω.exists_isDarbouxBasis
  obtain rfl : m = n := by
    have := finrank_eq_card_basis b
    simp only [Fintype.card_prod, Fintype.card_fin] at this
    omega
  exact ⟨b, hb⟩

/-- **Darboux bases have unit relative determinant**: the change of basis between two Darboux
bases of `(V, ω)` is a symplectic matrix, of determinant `1`. -/
theorem IsDarbouxBasis.det_eq_one (hb : ω.IsDarbouxBasis b) (hc : ω.IsDarbouxBasis c) :
    b.det c = 1 := by
  set e := darbouxIndexEquiv n
  have hdet : b.det c = (b.reindex e).det (c.reindex e) := by
    rw [Basis.det_reindex, Basis.coe_reindex, Function.comp_assoc, Equiv.symm_comp_self,
      Function.comp_id]
  have hmem : (b.reindex e).toMatrix (c.reindex e) ∈ Matrix.symplecticGroup (Fin n) ℝ := by
    have h := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (b.reindex e) (c.reindex e)
      ω.toBilinForm
    rwa [hb.toMatrix_reindex, hc.toMatrix_reindex, ← SymplecticGroup.mem_iff'] at h
  rw [hdet, Basis.det_apply, SymplecticGroup.det_eq_one hmem]

/-- A linear symplectomorphism carries Darboux bases to Darboux bases. -/
theorem IsDarbouxBasis.map {ω' : SymplecticForm W} {e : V ≃ₗ[ℝ] W}
    (he : IsSymplectomorphism ω ω' e) (hb : ω.IsDarbouxBasis b) : ω'.IsDarbouxBasis (b.map e) := by
  refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩ <;> simp only [Basis.map_apply, he.apply]
  exacts [hb.apply_fst_fst i j, hb.apply_snd_snd i j, hb.apply_fst_snd i j]

/-- **Linear symplectomorphisms have determinant one.** -/
theorem IsSymplectomorphism.det_eq_one [FiniteDimensional ℝ V] {e : V ≃ₗ[ℝ] V}
    (he : IsSymplectomorphism ω ω e) : LinearMap.det (e : V →ₗ[ℝ] V) = 1 := by
  obtain ⟨n, b, hb⟩ := ω.exists_isDarbouxBasis
  have h := hb.det_eq_one (hb.map he)
  rwa [Basis.coe_map, ← LinearEquiv.coe_coe, Basis.det_comp, Basis.det_self, mul_one] at h

/-! ### The symplectic orientation -/

/-- A symplectic vector space has even dimension. -/
private theorem finrank_eq_div_two_mul_two [FiniteDimensional ℝ V] (ω : SymplecticForm V)
    {k : ℕ} (hk : finrank ℝ V = k) : finrank ℝ V = k / 2 * 2 := by
  obtain ⟨r, hr⟩ := ω.isAlt.even_finrank ω.nondegenerate
  omega

variable [FiniteDimensional ℝ V] {k : ℕ}

/-- The **symplectic orientation** of a finite-dimensional symplectic vector space `(V, ω)` with
`finrank ℝ V = k`: the orientation of the Darboux bases `(q₁, p₁, …, qₙ, pₙ)`, listed in this
interleaved order (`TauCeti.SymplecticForm.IsDarbouxBasis.orientation_reindex`). -/
noncomputable def orientation (ω : SymplecticForm V) (hk : finrank ℝ V = k) :
    Orientation ℝ V (Fin k) :=
  ((ω.exists_isDarbouxBasis_of_finrank_eq (ω.finrank_eq_div_two_mul_two hk)).choose.reindex
    (finProdFinEquiv.trans
      (finCongr (by have := ω.finrank_eq_div_two_mul_two hk; omega)))).orientation

/-- **Every Darboux basis is positively oriented** for the symplectic orientation: the basis
`(q₁, p₁, …, qₙ, pₙ)`, listed in this interleaved order, induces `ω.orientation`. -/
theorem IsDarbouxBasis.orientation_reindex (hb : ω.IsDarbouxBasis b) (hk : finrank ℝ V = k)
    (h : n * 2 = k) :
    (b.reindex (finProdFinEquiv.trans (finCongr h))).orientation = ω.orientation hk := by
  obtain rfl : n = k / 2 := by omega
  have hb₀ :=
    (ω.exists_isDarbouxBasis_of_finrank_eq (ω.finrank_eq_div_two_mul_two hk)).choose_spec
  rw [orientation, Basis.orientation_reindex, Basis.orientation_reindex,
    (Basis.orientation_eq_iff_det_pos _ _).2 (by rw [hb.det_eq_one hb₀]; exact one_pos)]

/-- The symplectic orientation is natural: a linear symplectomorphism `e : (V, ω₁) → (W, ω₂)`
carries the symplectic orientation of `ω₁` to that of `ω₂`. -/
theorem IsSymplectomorphism.map_orientation [FiniteDimensional ℝ W] {ω₁ : SymplecticForm V}
    {ω₂ : SymplecticForm W} {e : V ≃ₗ[ℝ] W} (he : IsSymplectomorphism ω₁ ω₂ e)
    (hk : finrank ℝ V = k) :
    Orientation.map (Fin k) e (ω₁.orientation hk) =
      ω₂.orientation (e.finrank_eq.symm.trans hk) := by
  obtain ⟨b, hb⟩ := ω₁.exists_isDarbouxBasis_of_finrank_eq (ω₁.finrank_eq_div_two_mul_two hk)
  have h : k / 2 * 2 = k := by have := ω₁.finrank_eq_div_two_mul_two hk; omega
  rw [← hb.orientation_reindex hk h, ← Basis.orientation_map,
    ← (hb.map he).orientation_reindex _ h]
  congr 1

/-- **Rescaling the symplectic orientation.** For `c ≠ 0` and `finrank ℝ V = k`, the symplectic
orientation of `c • ω` is that of `ω` acted on by the unit `c ^ (k / 2)`, that is, by the sign of
`c ^ (k / 2)`. -/
theorem orientation_rescale (ω : SymplecticForm V) {c : ℝ} (hc : c ≠ 0) (hk : finrank ℝ V = k) :
    (ω.rescale c hc).orientation hk = Units.mk0 c hc ^ (k / 2) • ω.orientation hk := by
  obtain ⟨b, hb⟩ := ω.exists_isDarbouxBasis_of_finrank_eq (ω.finrank_eq_div_two_mul_two hk)
  have h : k / 2 * 2 = k := by have := ω.finrank_eq_div_two_mul_two hk; omega
  set u := Units.mk0 c hc
  -- Rescale the momenta `pᵢ` by `c⁻¹`; the result is a Darboux basis of `c • ω`.
  let w : Fin (k / 2) × Fin 2 → ℝˣ := fun p ↦ if p.2 = 0 then 1 else u⁻¹
  have hbw : (ω.rescale c hc).IsDarbouxBasis (b.unitsSMul w) := by
    refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩
    · simp [w, Basis.unitsSMul_apply, hb.apply_fst_fst]
    · simp [w, Basis.unitsSMul_apply, Units.smul_def, hb.apply_snd_snd]
    · simp [w, u, Basis.unitsSMul_apply, Units.smul_def, hb.apply_fst_snd, hc]
  set E := finProdFinEquiv.trans (finCongr h)
  have hE : (b.unitsSMul w).reindex E = (b.reindex E).unitsSMul (w ∘ E.symm) :=
    Basis.eq_of_apply_eq fun x ↦ by
      simp only [Basis.reindex_apply, Basis.unitsSMul_apply, Function.comp_apply]
  have hw : ∏ x, (w ∘ E.symm) x = u⁻¹ ^ (k / 2) := by
    rw [Fintype.prod_equiv E.symm (w ∘ E.symm) w fun _ ↦ rfl]
    simp [w, Fintype.prod_prod_type, Fin.prod_univ_two]
  rw [← hb.orientation_reindex hk h, ← hbw.orientation_reindex hk h, hE,
    Basis.orientation_unitsSMul, hw, inv_pow, inv_inv]

/-- Positive rescaling preserves the symplectic orientation. -/
theorem orientation_rescale_of_pos (ω : SymplecticForm V) {c : ℝ} (hc : 0 < c)
    (hk : finrank ℝ V = k) : (ω.rescale c hc.ne').orientation hk = ω.orientation hk := by
  rw [orientation_rescale, Module.Ray.units_smul_of_pos]
  simpa using pow_pos hc _

/-- **The symplectic orientation of a direct sum** `ω₁ ⊕ ω₂` is the product of the symplectic
orientations of `ω₁` and `ω₂`. -/
theorem orientation_prod [FiniteDimensional ℝ W] (ω₁ : SymplecticForm V) (ω₂ : SymplecticForm W)
    {m k : ℕ} (hm : finrank ℝ V = m) (hk : finrank ℝ W = k) (hmk : finrank ℝ (V × W) = m + k) :
    (ω₁.prod ω₂).orientation hmk =
      Orientation.prod (ω₁.orientation hm) (ω₂.orientation hk) hm hk := by
  obtain ⟨b, hb⟩ := ω₁.exists_isDarbouxBasis_of_finrank_eq (ω₁.finrank_eq_div_two_mul_two hm)
  obtain ⟨c, hc⟩ := ω₂.exists_isDarbouxBasis_of_finrank_eq (ω₂.finrank_eq_div_two_mul_two hk)
  have h₁ : m / 2 * 2 = m := by have := ω₁.finrank_eq_div_two_mul_two hm; omega
  have h₂ : k / 2 * 2 = k := by have := ω₂.finrank_eq_div_two_mul_two hk; omega
  have h : (m / 2 + k / 2) * 2 = m + k := by omega
  -- The concatenation of the two Darboux bases, as a Darboux basis of `ω₁ ⊕ ω₂`.
  set e : (Fin (m / 2) × Fin 2) ⊕ (Fin (k / 2) × Fin 2) ≃ Fin (m / 2 + k / 2) × Fin 2 :=
    (Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _))
  have hl (i : Fin (m / 2)) (a : Fin 2) :
      (b.prod c).reindex e (Fin.castAdd (k / 2) i, a) = (b (i, a), 0) := by
    ext <;> simp [e, Basis.reindex_apply]
  have hr (i : Fin (k / 2)) (a : Fin 2) :
      (b.prod c).reindex e (Fin.natAdd (m / 2) i, a) = (0, c (i, a)) := by
    ext <;> simp [e, Basis.reindex_apply]
  have hne (i : Fin (m / 2)) (j : Fin (k / 2)) :
      Fin.castAdd (k / 2) i ≠ Fin.natAdd (m / 2) j := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
    omega
  have hd : (ω₁.prod ω₂).IsDarbouxBasis ((b.prod c).reindex e) := by
    refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩ <;>
      induction i using Fin.addCases <;> induction j using Fin.addCases <;>
      simp [hl, hr, hne, (hne _ _).symm, hb.apply_fst_fst, hb.apply_snd_snd, hb.apply_fst_snd,
        hc.apply_fst_fst, hc.apply_snd_snd, hc.apply_fst_snd]
  rw [← hb.orientation_reindex hm h₁, ← hc.orientation_reindex hk h₂,
    Orientation.prod_basis_orientation, ← hd.orientation_reindex hmk h]
  congr 1
  -- Both bases list `(q₁, p₁, …)` of `ω₁` followed by `(q'₁, p'₁, …)` of `ω₂`.
  set F := (Equiv.sumCongr (finProdFinEquiv.trans (finCongr h₁))
    (finProdFinEquiv.trans (finCongr h₂))).trans finSumFinEquiv
  have hF (p) : F p = finProdFinEquiv.trans (finCongr h) (e p) := by
    rcases p with ⟨i, a⟩ | ⟨i, a⟩
    · ext
      simp [F, e, finProdFinEquiv]
    · ext
      simp [F, e, finProdFinEquiv]
      omega
  refine Basis.eq_of_apply_eq fun x ↦ ?_
  obtain ⟨p, rfl⟩ := F.surjective x
  conv_lhs => rw [Basis.reindex_apply, Basis.reindex_apply, hF, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  rcases p with p | p <;> simp [F, Basis.reindex_apply, Basis.prod_apply]

end SymplecticForm

end TauCeti
