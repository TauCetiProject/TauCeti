/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Alternating.HermitianForm
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Pow.Trace
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# The trace identity for a Hermitian reference form

Let `E` be a complex vector space of dimension `n = m + 1` and `ω` a real two-form on it that is
invariant under multiplication by `i` and whose Hermitian form `H_ω(u, v) = ω(u, i v) + i·ω(u, v)`
(`ContinuousAlternatingMap.hermitianForm`) admits an orthonormal family `b₁, …, bₙ`: for
instance a Hermitian metric at a point of a complex manifold. For every real two-form `α`,

`n α ∧ ω ^ (n - 1) = (∑ᵢ α(bᵢ, i bᵢ)) ω ^ n`

(`ContinuousAlternatingMap.nsmul_pairedWedge_wedgePow_eq_sum_smul`), that is
`n α ∧ ω ^ (n - 1) = (tr_ω α) ω ^ n`, where `∑ᵢ α(bᵢ, i bᵢ) = ∑ᵢ Re H_α(bᵢ, bᵢ)` is the trace of
`H_α` relative to `H_ω`.

The vectors `bᵢ, i bᵢ` form a real basis of `E`
(`ContinuousAlternatingMap.linearIndependent_hermitianForm_frame`): applying `H_ω(bⱼ, ·)`, which
is complex linear, to a vanishing real combination `∑ᵢ (aᵢ bᵢ + aᵢ' i bᵢ)` gives
`aⱼ + i aⱼ' = 0`. On this basis `ω` is in standard symplectic form, `ω(bᵢ, bⱼ) = 0`,
`ω(bᵢ, i bⱼ) = δᵢⱼ` and `ω(i bᵢ, i bⱼ) = 0`, so both sides take the value
`(m + 1)! · ∑ᵢ α(bᵢ, i bᵢ)` there
(`ContinuousAlternatingMap.pairedWedge_wedgePow_apply_finProdFinEquiv`), and two forms of top
degree that agree on a basis are equal.

This is the statement of `TauCeti.AlmostComplexStructure.nsmul_wedge_wedgePow_ofComplexModule`
without an inner product on `E`: the reference form `ω` is arbitrary, as on a Hermitian manifold,
where the metric varies from point to point on a fixed model space.

## Main results

* `ContinuousAlternatingMap.linearIndependent_hermitianForm_frame`: an `H_ω`-orthonormal family
  `b` gives a real linearly independent family `(bᵢ, i bᵢ)`.
* `ContinuousAlternatingMap.nsmul_pairedWedge_wedgePow_eq_sum_smul`: the trace identity.

## References

* G. Székelyhidi, *Fully non-linear elliptic equations on compact Hermitian manifolds*,
  J. Differential Geom. 109 (2018), Section 2.
-/

public section

open Complex Module

namespace ContinuousAlternatingMap

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- The real frame `(b₀, i b₀, b₁, i b₁, …)` of a family `b`, indexed by `Fin k × Fin 2`. -/
def hermitianFrame {k : ℕ} (b : Fin k → E) (p : Fin k × Fin 2) : E :=
  ![b p.1, I • b p.1] p.2

@[simp]
theorem hermitianFrame_zero {k : ℕ} (b : Fin k → E) (i : Fin k) : hermitianFrame b (i, 0) = b i :=
  (rfl)

@[simp]
theorem hermitianFrame_one {k : ℕ} (b : Fin k → E) (i : Fin k) :
    hermitianFrame b (i, 1) = I • b i :=
  (rfl)

variable [TopologicalSpace E] {ω : E [⋀^Fin 2]→L[ℝ] ℝ}

/-- **An `H_ω`-orthonormal family gives a real basis.** If `H_ω(bᵢ, bⱼ) = δᵢⱼ`, the family
`(bᵢ, i bᵢ)` is linearly independent over `ℝ`. -/
theorem linearIndependent_hermitianForm_frame {k : ℕ} {b : Fin k → E}
    (hb : ∀ i j, ω.hermitianForm (b i) (b j) = if i = j then 1 else 0) :
    LinearIndependent ℝ (hermitianFrame b) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg p
  -- Pair the vanishing combination with `bⱼ` through `H_ω`, an additive map in the second slot.
  let L : E →+ ℂ := AddMonoidHom.mk' (ω.hermitianForm (b p.1)) (hermitianForm_add_right _)
  have h : ∑ q, L (g q • hermitianFrame b q) = 0 := by rw [← _root_.map_sum, hg, _root_.map_zero]
  rw [Fintype.sum_prod_type] at h
  simp only [Fin.sum_univ_two, hermitianFrame_zero, hermitianFrame_one, L,
    AddMonoidHom.mk'_apply, hermitianForm_real_smul_right, hermitianForm_smul_right, hb] at h
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [Finset.sum_eq_single p.1 (fun j _ hj ↦ by simp [Ne.symm hj]) (by simp)] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp at hre him
  obtain ⟨i, r⟩ := p
  fin_cases r
  · simpa using hre
  · simpa using him

/-- **The trace identity** `n α ∧ ω ^ (n - 1) = (tr_ω α) ω ^ n` for a Hermitian reference form:
on a complex vector space of dimension `m + 1`, if `ω` is invariant under multiplication by `i`
and `b` is orthonormal for its Hermitian form `H_ω`, then every real two-form `α` satisfies
`(m + 1) α ∧ ω ^ m = (∑ᵢ α(bᵢ, i bᵢ)) ω ^ (m + 1)`. -/
theorem nsmul_pairedWedge_wedgePow_eq_sum_smul {m : ℕ} (hm : finrank ℂ E = m + 1)
    (hω : ∀ u v : E, ω ![I • u, I • v] = ω ![u, v])
    {b : Fin (m + 1) → E} (hb : ∀ i j, ω.hermitianForm (b i) (b j) = if i = j then 1 else 0)
    (α : E [⋀^Fin 2]→L[ℝ] ℝ) :
    ((m + 1 : ℕ) : ℝ) • pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (ω.wedgePow m) α =
      (∑ i, α ![b i, I • b i]) • ω.wedgePow (m + 1) := by
  -- The real frame `(bᵢ, i bᵢ)`, ordered as `b₀, i b₀, b₁, i b₁, …`, is a basis.
  let e : Fin (2 * (m + 1)) ≃ Fin (m + 1) × Fin 2 :=
    (finCongr (Nat.mul_comm 2 (m + 1))).trans finProdFinEquiv.symm
  have hli : LinearIndependent ℝ (hermitianFrame b ∘ e) :=
    (linearIndependent_hermitianForm_frame hb).comp e e.injective
  have hcard : Fintype.card (Fin (2 * (m + 1))) = finrank ℝ E := by
    rw [Fintype.card_fin, finrank_real_of_complex, hm]
  let B : Basis (Fin (2 * (m + 1))) ℝ E := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hB : (B : Fin (2 * (m + 1)) → E) = hermitianFrame b ∘ e :=
    coe_basisOfLinearIndependentOfCardEqFinrank _ _
  -- On the frame, `ω` is in standard symplectic form.
  have h₀₀ (i j : Fin (m + 1)) : ω ![hermitianFrame b (i, 0), hermitianFrame b (j, 0)] = 0 := by
    have := congrArg Complex.im (hb i j)
    split_ifs at this <;> simpa using this
  have h₀₁ (i j : Fin (m + 1)) : ω ![hermitianFrame b (i, 0), hermitianFrame b (j, 1)] =
      if i = j then 1 else 0 := by
    have := congrArg Complex.re (hb i j)
    split_ifs at this ⊢ <;> simpa using this
  have h₁₁ (i j : Fin (m + 1)) : ω ![hermitianFrame b (i, 1), hermitianFrame b (j, 1)] = 0 := by
    rw [hermitianFrame_one, hermitianFrame_one, hω]
    exact h₀₀ i j
  have e₁ : pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
      (ω.wedgePow m) α B = m.factorial * ∑ i, α ![b i, I • b i] := by
    rw [hB]
    exact pairedWedge_wedgePow_apply_finProdFinEquiv ω α (hermitianFrame b) h₀₀ h₀₁ h₁₁
  have e₂ : ω.wedgePow (m + 1) B = m.factorial * (m + 1) := by
    rw [wedgePow_succ, hB]
    refine (pairedWedge_wedgePow_apply_finProdFinEquiv ω ω (hermitianFrame b) h₀₀ h₀₁ h₁₁).trans ?_
    have h1 (i : Fin (m + 1)) : ω ![b i, I • b i] = 1 := by simpa using h₀₁ i i
    simp [h1]
  ext v
  rw [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply,
    apply_eq_det_mul _ B v, apply_eq_det_mul (ω.wedgePow (m + 1)) B v, e₁, e₂, smul_eq_mul,
    smul_eq_mul]
  push_cast
  ring

end ContinuousAlternatingMap
