/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.Analysis.Normed.Module.DoubleDual
import TauCeti.Analysis.InnerProductSpace.Frame
import TauCeti.Analysis.InnerProductSpace.JohnEllipsoid

/-!
# The Kadec–Snobar and Garling–Gordon projection theorems

Over `ℝ` or `ℂ`, finite-dimensional subspaces of a normed space are complemented, and so are closed
subspaces of finite codimension. This file bounds the norm of the projections by the square root
of the dimension or codimension, independently of the ambient space:

* **Kadec–Snobar:** an `n`-dimensional subspace `M` of a normed space `X` is the range of a
  projection of norm at most `√n`. Equivalently, there is a continuous linear map `P : X → M`
  restricting to the identity of `M` with `‖P‖ ≤ √n`.
* **Garling–Gordon:** a closed subspace `M` of codimension `n` is, for every `ε > 0`, the kernel of
  a projection of norm at most `√n + ε`.

Both come from John's theorem. For Kadec–Snobar, put `M` in John's position by a maximal-volume
ellipsoid `T : ℓ²ₙ → M`, with contact points `uᵢ` and weights `cᵢ` decomposing the identity of
`ℓ²ₙ` as `x = ∑ cᵢ ⟪uᵢ, x⟫ uᵢ`. The contact functionals `y ↦ ⟪uᵢ, T⁻¹ y⟫` have norm at most one
on `M`; extend them to functionals `ψᵢ` on `X` of norm at most one by Hahn–Banach and set
`P y = ∑ cᵢ ψᵢ(y) T uᵢ`. Then `P` is the identity on `M`, and since `T` is a contraction,
`‖P y‖ ≤ ‖∑ cᵢ ψᵢ(y) uᵢ‖ ≤ (∑ cᵢ ‖ψᵢ(y)‖²)^(1/2) ≤ √n ‖y‖`.

For Garling–Gordon, apply John's theorem to the dual `(X/M)*` instead
(`TauCeti.exists_sum_smul_eq_of_finiteDimensional`), through a maximal-volume ellipsoid
`S : ℓ²ₙ → (X/M)*`. The contact functionals on `(X/M)*` are evaluations at vectors `wᵢ ∈ X/M` of
norm at most one, because `X/M` is finite-dimensional and hence reflexive; lift them
to vectors `xᵢ ∈ X` of norm less than `1 + δ`. Then `P y = ∑ cᵢ (S uᵢ)(π y) xᵢ`, where
`π : X → X/M` is the quotient map, satisfies `π ∘ P = π`, so `P` is a projection with kernel `M`.
Pairing with a functional `g` on `X` gives
`‖g (P y)‖ = ‖∑ cᵢ g(xᵢ) (S uᵢ)(π y)‖ ≤ ‖∑ cᵢ g(xᵢ) uᵢ‖ ‖π y‖ ≤ √n (1 + δ) ‖g‖ ‖y‖`. The lift of
the quotient norm is the only source of `ε`.

## Main statements

* `Submodule.exists_projection_norm_le_sqrt_finrank`: the Kadec–Snobar theorem.
* `Submodule.exists_isIdempotentElem_ker_eq_norm_le_sqrt_finrank_add`: the Garling–Gordon theorem.

## References

* M. I. Kadec and M. G. Snobar, *Certain functionals on the Minkowski compactum*, Mat. Zametki
  **10** (1971), 453–457.
* D. J. H. Garling and Y. Gordon, *Relations between some constants associated with finite
  dimensional Banach spaces*, Israel J. Math. **9** (1971), 346–361.
* A. Pietsch, *Eigenvalues and s-Numbers*, 1.5.5 and 1.7.17.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Theorem 13.1.7.
-/

open Module
open scoped InnerProductSpace

public section

namespace Submodule

open TauCeti

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- **The Kadec–Snobar theorem.** Over `ℝ` or `ℂ`, every finite-dimensional subspace `M` of a
normed space is the range of a projection of norm at most `√(dim M)`: there is a continuous linear
map `P : X → M` restricting to the identity of `M` with `‖P‖ ≤ √(dim M)`, so that
`M.subtypeL ∘L P` is a projection of `X` onto `M` of the same norm. -/
theorem exists_projection_norm_le_sqrt_finrank (M : Submodule 𝕜 X) [FiniteDimensional 𝕜 M] :
    ∃ P : X →L[𝕜] M, (∀ x : M, P x = x) ∧ ‖P‖ ≤ √(finrank 𝕜 M) := by
  set m := finrank 𝕜 M
  obtain ⟨T, hT⟩ := exists_isMaxVolumeEllipsoid (𝕜 := 𝕜) (E := EuclideanSpace 𝕜 (Fin m)) (F := M)
    (by simp [m])
  obtain ⟨k, u, c, hu, hc, hcsum, hid⟩ := hT.exists_sum_rankOne_eq_id
  have hdec (x : EuclideanSpace 𝕜 (Fin m)) : ∑ i, (c i : 𝕜) • ⟪u i, x⟫_𝕜 • u i = x := by
    simpa using congr($hid x)
  -- Extend the contact functionals `y ↦ ⟪uᵢ, T⁻¹ y⟫` from `M` to `X` by Hahn–Banach.
  choose ψ hψ hψn using fun i ↦ exists_extension_norm_eq M
    ((innerSL 𝕜 (u i)).comp (T.symm : M →L[𝕜] EuclideanSpace 𝕜 (Fin m)))
  let P : X →L[𝕜] M := ∑ i, (c i : 𝕜) • (ψ i).smulRight (T (u i))
  have hP (y : X) : P y = T (∑ i, ((c i : 𝕜) * ψ i y) • u i) := by
    simp only [P, _root_.sum_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
      map_sum, map_smul, smul_smul]
  refine ⟨P, fun y ↦ ?_, ?_⟩
  · have h := hdec (T.symm y)
    simp only [smul_smul] at h
    simp [hP, hψ, h]
  · refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y ↦ ?_
    rw [hP]
    refine ((T : EuclideanSpace 𝕜 (Fin m) →L[𝕜] M).le_of_opNorm_le hT.norm_le_one _).trans ?_
    rw [one_mul, show (m : ℝ) = ∑ i, c i by simp [hcsum]]
    refine norm_sum_mul_smul_le_sqrt_mul (fun i ↦ (hc i).le) hdec fun i ↦
      ((ψ i).le_opNorm y).trans ?_
    rw [hψn i]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (hT.norm_innerSL_comp_symm_le_one (hu i).1 (hu i).2)

/-- **The Garling–Gordon theorem.** Over `ℝ` or `ℂ`, every closed subspace `M` of finite
codimension in a normed space `X` is, for every `ε > 0`, the kernel of a projection of norm at
most `√(dim (X ⧸ M)) + ε`. -/
theorem exists_isIdempotentElem_ker_eq_norm_le_sqrt_finrank_add (M : Submodule 𝕜 X)
    (hM : IsClosed (M : Set X)) [FiniteDimensional 𝕜 (X ⧸ M)] {ε : ℝ} (hε : 0 < ε) :
    ∃ P : X →L[𝕜] X, IsIdempotentElem P ∧ P.ker = M ∧ ‖P‖ ≤ √(finrank 𝕜 (X ⧸ M)) + ε := by
  have : IsClosed (M : Set X) := hM
  set m := finrank 𝕜 (X ⧸ M)
  obtain ⟨k, c, φ, w, hwn, hdec, hbound⟩ := exists_sum_smul_eq_of_finiteDimensional (𝕜 := 𝕜)
    (F := X ⧸ M)
  -- Lift the `wᵢ` to vectors `xᵢ` of norm less than `1 + δ`, where `√m δ ≤ ε`.
  set δ := ε / (√m + 1) with hδ
  have hδ₀ : 0 < δ := div_pos hε (by positivity)
  have hδm : √m * δ ≤ ε := by
    rw [hδ, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [Real.sqrt_nonneg (m : ℝ)]
  choose x hx hxn using fun i ↦ Submodule.Quotient.norm_mk_lt (w i) hδ₀
  let P : X →L[𝕜] X := ∑ i, (c i : 𝕜) • ((φ i).comp M.mkQL).smulRight (x i)
  have hP (y : X) : P y = ∑ i, ((c i : 𝕜) * φ i (M.mkQ y)) • x i := by
    simp [P, smul_smul]
  have hPq (y : X) : M.mkQ (P y) = M.mkQ y := by
    simpa [hP, hx] using hdec (M.mkQ y)
  refine ⟨P, ContinuousLinearMap.ext fun y ↦ by rw [mul_apply_eq_comp, hP (P y), hPq, ← hP],
    ?_, ?_⟩
  · ext y
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    refine ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩
    · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, ← hPq, hy, map_zero]
    · simp [hP, (Submodule.Quotient.mk_eq_zero M).2 hy]
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y ↦ ?_
    refine NormedSpace.norm_le_dual_bound 𝕜 (P y) (by positivity) fun g ↦ ?_
    have hg := hbound (M.mkQ y) (fun i ↦ g (x i)) (B := ‖g‖ * (1 + δ))
      fun i ↦ (g.le_opNorm (x i)).trans
        (mul_le_mul_of_nonneg_left (by linarith [hxn i, hwn i]) (norm_nonneg g))
    calc ‖g (P y)‖ = ‖∑ i, (c i : 𝕜) * g (x i) * φ i (M.mkQ y)‖ := by
          simp only [hP, map_sum, map_smul, smul_eq_mul]
          exact congrArg norm (Finset.sum_congr rfl fun i _ ↦ by ring)
      _ ≤ √m * (‖g‖ * (1 + δ)) * ‖y‖ :=
          hg.trans (mul_le_mul_of_nonneg_left (Submodule.Quotient.norm_mk_le M y) (by positivity))
      _ ≤ (√m + ε) * ‖y‖ * ‖g‖ := by
        nlinarith [mul_le_mul_of_nonneg_left hδm (mul_nonneg (norm_nonneg y) (norm_nonneg g))]

end Submodule
