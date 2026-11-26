/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Alternating.HermitianForm
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Pow.Trace
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.LinearAlgebra.Complex.Orientation
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

The vectors `bᵢ, i bᵢ` form a real basis of `E`: since `ω` is invariant under `i`, `H_ω` is
sesquilinear, so the `H_ω`-orthonormal family `b` is complex linearly independent
(`LinearMap.linearIndependent_of_isOrthoᵢ`), hence a complex basis, and its underlying real basis
is `(bᵢ, i bᵢ)` (`Module.Basis.complexToReal`). On this basis `ω` is in standard symplectic
form, `ω(bᵢ, bⱼ) = 0`, `ω(bᵢ, i bⱼ) = δᵢⱼ` and `ω(i bᵢ, i bⱼ) = 0`, so both sides take the value
`(m + 1)! · ∑ᵢ α(bᵢ, i bᵢ)` there
(`ContinuousAlternatingMap.pairedWedge_wedgePow_apply_finProdFinEquiv` and
`ContinuousAlternatingMap.wedgePow_apply_finProdFinEquiv`), and two forms of top degree that
agree on a basis are equal.

This is the statement of `TauCeti.AlmostComplexStructure.nsmul_wedge_wedgePow_ofComplexModule`
without an inner product on `E`: the reference form `ω` is arbitrary, as on a Hermitian manifold,
where the metric varies from point to point on a fixed model space.

## Main results

* `ContinuousAlternatingMap.nsmul_pairedWedge_wedgePow_eq_sum_smul`: the trace identity.

## References

* G. Székelyhidi, *Fully non-linear elliptic equations on compact Hermitian manifolds*,
  J. Differential Geom. 109 (2018), Section 2.
-/

public section

open Complex Module

namespace ContinuousAlternatingMap

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] {ω : E [⋀^Fin 2]→L[ℝ] ℝ}

/-- **The trace identity** `n α ∧ ω ^ (n - 1) = (tr_ω α) ω ^ n` for a Hermitian reference form:
on a complex vector space of dimension `m + 1`, if `ω` is invariant under multiplication by `i`
and `b` is orthonormal for its Hermitian form `H_ω`, then every real two-form `α` satisfies
`(m + 1) α ∧ ω ^ m = (∑ᵢ α(bᵢ, i bᵢ)) ω ^ (m + 1)`. -/
theorem nsmul_pairedWedge_wedgePow_eq_sum_smul {m : ℕ} (hm : finrank ℂ E = m + 1)
    (hω : ∀ u v : E, ω ![I • u, I • v] = ω ![u, v])
    {b : Fin (m + 1) → E} (hb : ∀ i j, ω.hermitianForm (b i) (b j) = if i = j then 1 else 0)
    (α : E [⋀^Fin 2]→L[ℝ] ℝ) :
    (m + 1) • pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (ω.wedgePow m) α =
      (∑ i, α ![b i, I • b i]) • ω.wedgePow (m + 1) := by
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  -- The real frame `(bᵢ, i bᵢ)`, ordered as `b₀, i b₀, b₁, i b₁, …`, is a basis: `b` is
  -- orthonormal for the sesquilinear form `H_ω`, hence a complex basis, whose underlying real
  -- basis is `(bᵢ, i bᵢ)`.
  let f : Fin (m + 1) × Fin 2 → E := fun p ↦ ![b p.1, I • b p.1] p.2
  have hC : LinearIndependent ℂ b :=
    LinearMap.linearIndependent_of_isOrthoᵢ (B := ω.hermitianSesqForm hω)
      (fun i j hij ↦ by simp [Function.onFun, hb, hij]) (fun i ↦ by simp [hb])
  let B : Basis (Fin (2 * (m + 1))) ℝ E :=
    (basisOfLinearIndependentOfCardEqFinrank hC (by simp [hm])).complexToReal.reindex
      (TauCeti.complexRealIndexEquiv (m + 1))
  -- `B` in the form of the evaluation lemmas below.
  have hB : (B : Fin (2 * (m + 1)) → E) =
      fun r ↦ f (finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 (m + 1)) r)) := by
    ext r
    obtain ⟨⟨i, k⟩, rfl⟩ := (TauCeti.complexRealIndexEquiv (m + 1)).surjective r
    rw [show Fin.cast _ (TauCeti.complexRealIndexEquiv (m + 1) (i, k)) = finProdFinEquiv (i, k)
      from Fin.ext (by simp [Nat.add_comm])]
    fin_cases k <;> simp [B, f]
  -- On the frame, `ω` is in standard symplectic form.
  have h₀₀ (i j : Fin (m + 1)) : ω ![f (i, 0), f (j, 0)] = 0 := by
    have := congrArg Complex.im (hb i j)
    split_ifs at this <;> simpa [f] using this
  have h₀₁ (i j : Fin (m + 1)) : ω ![f (i, 0), f (j, 1)] =
      if i = j then 1 else 0 := by
    have := congrArg Complex.re (hb i j)
    split_ifs at this ⊢ <;> simpa [f] using this
  have h₁₁ (i j : Fin (m + 1)) : ω ![f (i, 1), f (j, 1)] = 0 := by
    simpa [f, hω] using h₀₀ i j
  have e₁ : pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
      (ω.wedgePow m) α B = m.factorial * ∑ i, α ![b i, I • b i] := by
    rw [hB, pairedWedge_wedgePow_apply_finProdFinEquiv ω α f h₀₀ h₀₁ h₁₁]
    simp [f]
  have e₂ : ω.wedgePow (m + 1) B = (m + 1).factorial := by
    rw [hB, wedgePow_apply_finProdFinEquiv ω f h₀₀ h₀₁]
  ext v
  rw [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply,
    apply_eq_det_mul _ B v, apply_eq_det_mul (ω.wedgePow (m + 1)) B v, e₁, e₂, smul_eq_mul,
    smul_eq_mul, Nat.factorial_succ]
  push_cast
  ring

end ContinuousAlternatingMap
