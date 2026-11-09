/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import TauCeti.Analysis.InnerProductSpace.Frame
import TauCeti.Analysis.InnerProductSpace.JohnEllipsoid
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.Basic

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

For Garling–Gordon, apply John's theorem to the dual `(X/M)*` instead, through a maximal-volume
ellipsoid `S : ℓ²ₙ → (X/M)*`. The contact functionals on `(X/M)*` are evaluations at vectors
`wᵢ ∈ X/M` of norm at most one, because `X/M` is finite-dimensional and hence reflexive; lift them
to vectors `xᵢ ∈ X` of norm less than `1 + δ`. Then `P y = ∑ cᵢ (S uᵢ)(π y) xᵢ`, where
`π : X → X/M` is the quotient map, satisfies `π ∘ P = π`, so `P` is a projection with kernel `M`.
Pairing with a functional `g` on `X` gives
`g (P y) = ∑ cᵢ g(xᵢ) (S uᵢ)(π y) ≤ ‖∑ cᵢ g(xᵢ) uᵢ‖ ‖π y‖ ≤ √n (1 + δ) ‖g‖ ‖y‖`. The lift of the
quotient norm is the only source of `ε`.

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

namespace Submodule

open TauCeti

variable {𝕜 Q : Type*} [RCLike 𝕜] [NormedAddCommGroup Q] [NormedSpace 𝕜 Q]

/-- John's theorem on the dual of a finite-dimensional space `Q`, read back in `Q`: there are
functionals `φᵢ`, vectors `wᵢ` of norm at most one and weights `cᵢ` with `∑ cᵢ φᵢ(z) wᵢ = z`, such
that `‖∑ cᵢ bᵢ φᵢ(z)‖ ≤ √n B ‖z‖` whenever all `‖bᵢ‖ ≤ B`, where `n` is the dimension. -/
private theorem exists_sum_smul_eq_of_finiteDimensional [FiniteDimensional 𝕜 Q] :
    ∃ (k : ℕ) (c : Fin k → ℝ) (φ : Fin k → StrongDual 𝕜 Q) (w : Fin k → Q),
      (∀ i, ‖w i‖ ≤ 1) ∧ (∀ z, ∑ i, ((c i : 𝕜) * φ i z) • w i = z) ∧
      ∀ (z : Q) (b : Fin k → 𝕜) {B : ℝ}, (∀ i, ‖b i‖ ≤ B) →
        ‖∑ i, (c i : 𝕜) * b i * φ i z‖ ≤ √(finrank 𝕜 Q) * B * ‖z‖ := by
  set m := finrank 𝕜 Q
  have hD : finrank 𝕜 (StrongDual 𝕜 Q) = m := by
    rw [← LinearMap.toContinuousLinearMap.finrank_eq, Subspace.dual_finrank_eq]
  obtain ⟨S, hS⟩ := exists_isMaxVolumeEllipsoid (𝕜 := 𝕜) (E := EuclideanSpace 𝕜 (Fin m))
    (F := StrongDual 𝕜 Q) (by simp [hD])
  obtain ⟨k, u, c, hu, hc, hcsum, hid⟩ := hS.exists_sum_rankOne_eq_id
  have hdec (x : EuclideanSpace 𝕜 (Fin m)) : ∑ i, (c i : 𝕜) • ⟪u i, x⟫_𝕜 • u i = x := by
    simpa using congr($hid x)
  -- The contact functionals on `Q*` are evaluations at vectors `wᵢ` of norm at most one.
  choose w hw using fun i ↦ surjective_inclusionInDoubleDual_of_finiteDimensional
    ((innerSL 𝕜 (u i)).comp (S.symm : StrongDual 𝕜 Q →L[𝕜] EuclideanSpace 𝕜 (Fin m)))
  have hwf (i : Fin k) (f : StrongDual 𝕜 Q) : f (w i) = ⟪u i, S.symm f⟫_𝕜 := by
    simpa using congr($(hw i) f)
  refine ⟨k, c, fun i ↦ S (u i), w, fun i ↦ ?_, fun z ↦ ?_, fun z b B hb ↦ ?_⟩
  · rw [← (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := Q)).norm_map]
    exact (congrArg norm (hw i)).trans_le (hS.norm_innerSL_comp_symm_le_one (hu i).1 (hu i).2)
  · refine (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).2 fun f ↦ ?_
    calc f (∑ i, ((c i : 𝕜) * S (u i) z) • w i)
        = S (∑ i, (c i : 𝕜) • ⟪u i, S.symm f⟫_𝕜 • u i) z := by
          simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, hwf]
          exact Finset.sum_congr rfl fun i _ ↦ by ring
      _ = f z := by rw [hdec, ContinuousLinearEquiv.apply_symm_apply]
  · -- The sum is `h (∑ cᵢ bᵢ uᵢ)` for the functional `h x = S x z` of norm at most `‖z‖`.
    let h : StrongDual 𝕜 (EuclideanSpace 𝕜 (Fin m)) :=
      (ContinuousLinearMap.apply 𝕜 𝕜 z).comp (S : EuclideanSpace 𝕜 (Fin m) →L[𝕜] StrongDual 𝕜 Q)
    have hh : ‖h‖ ≤ ‖z‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg z) fun x ↦ ?_
      have hSx : ‖S x‖ ≤ ‖x‖ := by
        simpa using (S : EuclideanSpace 𝕜 (Fin m) →L[𝕜] StrongDual 𝕜 Q).le_of_opNorm_le
          hS.norm_le_one x
      calc ‖S x z‖ ≤ ‖S x‖ * ‖z‖ := (S x).le_opNorm z
        _ ≤ ‖z‖ * ‖x‖ := by rw [mul_comm]; gcongr
    have hsum := norm_sum_mul_smul_le_sqrt_mul (fun i ↦ (hc i).le) hdec hb
    rw [hcsum, finrank_euclideanSpace_fin] at hsum
    calc ‖∑ i, (c i : 𝕜) * b i * S (u i) z‖ = ‖h (∑ i, ((c i : 𝕜) * b i) • u i)‖ := by
          simp [h, map_sum]
      _ ≤ ‖z‖ * (√m * B) := (h.le_opNorm _).trans (mul_le_mul hh hsum (norm_nonneg _)
          (norm_nonneg _))
      _ = √m * B * ‖z‖ := mul_comm _ _

end Submodule

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
    (Q := X ⧸ M)
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
