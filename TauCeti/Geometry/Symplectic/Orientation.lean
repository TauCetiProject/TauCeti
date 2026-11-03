/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Orientation
public import TauCeti.Geometry.Symplectic.Darboux.Basis
public import TauCeti.Geometry.Symplectic.Rescale
public import TauCeti.LinearAlgebra.Orientation.Prod

import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# The symplectic orientation

Let `ω` be a symplectic form on a finite-dimensional real vector space `V`. Any two Darboux bases
(`TauCeti.SymplecticForm.IsDarbouxBasis`, in `TauCeti.Geometry.Symplectic.Darboux.Basis`) have
relative determinant `1` (`TauCeti.SymplecticForm.IsDarbouxBasis.det_eq_one`).

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

* `TauCeti.SymplecticForm.orientation ω hk`: the symplectic orientation of `V`, indexed by
  `Fin k` where `finrank ℝ V = k`.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 2.1 (the symplectic volume form `ωⁿ`).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 1.1 and Homework 1.
-/

public section

open Module

namespace TauCeti

namespace SymplecticForm

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  {ω : SymplecticForm V} {n : ℕ} {b : Basis (Fin n × Fin 2) ℝ V}

/-! ### The symplectic orientation -/

/-- A symplectic vector space has even dimension `k`, so `k / 2 * 2 = k`. -/
private theorem div_two_mul_two [FiniteDimensional ℝ V] (ω : SymplecticForm V) {k : ℕ}
    (hk : finrank ℝ V = k) : k / 2 * 2 = k :=
  Nat.div_two_mul_two_of_even (hk ▸ ω.isAlt.even_finrank ω.nondegenerate)

variable [FiniteDimensional ℝ V] {k : ℕ}

/-- The **symplectic orientation** of a finite-dimensional symplectic vector space `(V, ω)` with
`finrank ℝ V = k`: the orientation of the Darboux bases `(q₁, p₁, …, qₙ, pₙ)`, listed in this
interleaved order (`TauCeti.SymplecticForm.IsDarbouxBasis.orientation_reindex`). -/
noncomputable def orientation (ω : SymplecticForm V) (hk : finrank ℝ V = k) :
    Orientation ℝ V (Fin k) :=
  ((ω.exists_isDarbouxBasis_of_finrank_eq (hk.trans (ω.div_two_mul_two hk).symm)).choose.reindex
    (finProdFinEquiv.trans (finCongr (ω.div_two_mul_two hk)))).orientation

/-- **Every Darboux basis is positively oriented** for the symplectic orientation: the basis
`(q₁, p₁, …, qₙ, pₙ)`, listed in this interleaved order, induces `ω.orientation`. -/
theorem IsDarbouxBasis.orientation_reindex (hb : ω.IsDarbouxBasis b) (hk : finrank ℝ V = k)
    (h : n * 2 = k) :
    (b.reindex (finProdFinEquiv.trans (finCongr h))).orientation = ω.orientation hk := by
  obtain rfl : n = k / 2 := by omega
  have hb₀ :=
    (ω.exists_isDarbouxBasis_of_finrank_eq (hk.trans (ω.div_two_mul_two hk).symm)).choose_spec
  rw [orientation, Basis.orientation_reindex, Basis.orientation_reindex,
    (Basis.orientation_eq_iff_det_pos _ _).2 (by rw [hb.det_eq_one hb₀]; exact one_pos)]

/-- The symplectic orientation is natural: a linear symplectomorphism `e : (V, ω₁) → (W, ω₂)`
carries the symplectic orientation of `ω₁` to that of `ω₂`. -/
theorem IsSymplectomorphism.map_orientation [FiniteDimensional ℝ W] {ω₁ : SymplecticForm V}
    {ω₂ : SymplecticForm W} {e : V ≃ₗ[ℝ] W} (he : IsSymplectomorphism ω₁ ω₂ e)
    (hk : finrank ℝ V = k) :
    Orientation.map (Fin k) e (ω₁.orientation hk) =
      ω₂.orientation (e.finrank_eq.symm.trans hk) := by
  have h := ω₁.div_two_mul_two hk
  obtain ⟨b, hb⟩ := ω₁.exists_isDarbouxBasis_of_finrank_eq (hk.trans h.symm)
  rw [← hb.orientation_reindex hk h, ← Basis.orientation_map,
    ← (hb.map he).orientation_reindex _ h]
  exact congrArg Basis.orientation <| Basis.eq_of_apply_eq fun x ↦ by
    simp only [Basis.map_apply, Basis.reindex_apply]

/-- **Rescaling the symplectic orientation.** For `c ≠ 0` and `finrank ℝ V = k`, the symplectic
orientation of `c • ω` is that of `ω` acted on by the unit `c ^ (k / 2)`, that is, by the sign of
`c ^ (k / 2)`. -/
theorem orientation_rescale (ω : SymplecticForm V) {c : ℝ} (hc : c ≠ 0) (hk : finrank ℝ V = k) :
    (ω.rescale c hc).orientation hk = Units.mk0 c hc ^ (k / 2) • ω.orientation hk := by
  have h := ω.div_two_mul_two hk
  obtain ⟨b, hb⟩ := ω.exists_isDarbouxBasis_of_finrank_eq (hk.trans h.symm)
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
  have h₁ := ω₁.div_two_mul_two hm
  have h₂ := ω₂.div_two_mul_two hk
  have h : (m / 2 + k / 2) * 2 = m + k := by rw [add_mul, h₁, h₂]
  obtain ⟨b, hb⟩ := ω₁.exists_isDarbouxBasis_of_finrank_eq (hm.trans h₁.symm)
  obtain ⟨c, hc⟩ := ω₂.exists_isDarbouxBasis_of_finrank_eq (hk.trans h₂.symm)
  rw [← hb.orientation_reindex hm h₁, ← hc.orientation_reindex hk h₂,
    Orientation.prod_basis_orientation, ← (hb.prod hc).orientation_reindex hmk h]
  congr 1
  -- Both bases list `(q₁, p₁, …)` of `ω₁` followed by `(q'₁, p'₁, …)` of `ω₂`.
  set e : (Fin (m / 2) × Fin 2) ⊕ (Fin (k / 2) × Fin 2) ≃ Fin (m / 2 + k / 2) × Fin 2 :=
    (Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _))
  set F := (Equiv.sumCongr (finProdFinEquiv.trans (finCongr h₁))
    (finProdFinEquiv.trans (finCongr h₂))).trans finSumFinEquiv
  have hF (p) : F p = finProdFinEquiv.trans (finCongr h) (e p) := by
    rcases p with ⟨i, a⟩ | ⟨i, a⟩
    · ext
      simp [F, e]
    · ext
      simp [F, e]
      omega
  refine Basis.eq_of_apply_eq fun x ↦ ?_
  obtain ⟨p, rfl⟩ := F.surjective x
  conv_lhs => rw [Basis.reindex_apply, Basis.reindex_apply, hF, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  rcases p with p | p <;> simp [F, Basis.reindex_apply, Basis.prod_apply]

end SymplecticForm

end TauCeti
