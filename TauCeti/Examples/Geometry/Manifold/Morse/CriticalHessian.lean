/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Model
public import TauCeti.Geometry.Manifold.ModelTransport.Boundaryless
public import TauCeti.Geometry.Manifold.Morse.Examples.QuadraticWell
public import TauCeti.Geometry.Manifold.Morse.NormalizedChart

/-!
# Checks for model transport, critical Hessians and normalized Morse charts

Examples on `ℝ` and on the plane `ℝ × ℝ` of the conventions behind the critical Hessian, the Morse
index and the normalized Morse chart of a function on a manifold.

* *Model transport.* For the plane with its self-model `𝓘(ℝ, ℝ × ℝ)`, the transport
  `TauCeti.BoundarylessModel` of a boundaryless model to its vector space changes nothing: the
  charts of the copy are the identity, and the derivative `(1, 0)` of the first coordinate, read
  through the source-side comparison `TauCeti.BoundarylessModel.mfderiv_source`, stays `(1, 0)`.
  The same holds for the target-side comparison `TauCeti.BoundarylessModel.mfderiv_target`. The
  half-line model `𝓡∂ 1` has range the half-line `[0, ∞)` of `ℝ¹`, not all of `ℝ¹`, so it is not
  boundaryless (`TauCeti.not_boundaryless_modelWithCornersEuclideanHalfSpace`) and the transport
  does not apply to it.
* *Complementary indices need nondegeneracy.* At a nondegenerate critical point the Morse indices
  of `f` and `-f` add to the dimension (`manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank`,
  in the namespace `TauCeti.IsManifoldNondegenerateCriticalPoint`).
  For `f = 0` on `ℝ` both indices are `0`, so their sum is `0 ≠ 1`, and the critical point `0` of
  `f` is degenerate. For `f = x²` they are `0` and `1`, with sum `1`.
* *The normalization of the Hessian and of the Morse chart.* The critical Hessian is the second
  derivative, with no factor `1 / 2`: for `f = x²` it is `(u, v) ↦ 2 u v`
  (`TauCeti.criticalHessian_sq_real_apply`). A normalized Morse chart writes
  `f = f(p) - Σ_{i<λ} yᵢ² + Σ_{i≥λ} yᵢ²`, so `x²` reads `y²` in it rather than `y² / 2`, and the
  coordinate is not rescaled: every normalized Morse chart `ψ` of `x²` at `0` has `‖ψ x‖ = |x|`
  (`norm_eq_abs_of_normalized_morseChart_sq`), and one exists
  (`exists_normalized_morseChart_sq`). The halved normal form `y² / 2` would need `y = ±√2 x`.

## References

* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 5.3 (the Morse lemma in the normalization used here).
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §2, Lemma 2.2.
-/

public section

open Filter Module Set
open scoped ContDiff Manifold

namespace TauCeti.Examples.MorseCriticalHessian

open TauCeti

/-! ### Model transport -/

/-- For the plane with its self-model, the charts of the transported copy are the identity. -/
example (x y : BoundarylessModel 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ)) :
    chartAt (ℝ × ℝ) x y = (BoundarylessModel.homeomorph 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ)).symm y := by
  rw [BoundarylessModel.chartAt_apply, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    id_eq]

/-- The derivative `(1, 0)` of the first coordinate of the plane stays `(1, 0)` under the
source-side transport to the self-modelled copy. -/
example (x : BoundarylessModel 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ)) (v : ℝ × ℝ) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ)
      (Prod.fst ∘ (BoundarylessModel.homeomorph 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ)).symm) x v = v.1 := by
  rw [BoundarylessModel.mfderiv_source, mfderiv_eq_fderiv, fderiv_fst]
  -- The tangent spaces of the plane are the plane itself, so both identifications are the identity.
  rfl

/-- The derivative `(1, 0)` of the curve `t ↦ (t, 0)` in the plane stays `(1, 0)` under the
target-side transport to the self-modelled copy. -/
example (t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (BoundarylessModel.homeomorph 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ∘ fun s : ℝ ↦ (s, (0 : ℝ))) t 1 =
      ((1 : ℝ), (0 : ℝ)) := by
  have hd : fderiv ℝ (fun s : ℝ ↦ (s, (0 : ℝ))) t = (ContinuousLinearMap.id ℝ ℝ).prod 0 :=
    ((hasFDerivAt_id t).prodMk (hasFDerivAt_const (0 : ℝ) t)).fderiv
  rw [BoundarylessModel.mfderiv_target, mfderiv_eq_fderiv, hd]
  -- The tangent spaces of the plane are the plane itself, so both identifications are the identity.
  rfl

/-- The half-line model `𝓡∂ 1` has range the half-line `[0, ∞)` of `ℝ¹`. -/
example : range (𝓡∂ 1) = {y | 0 ≤ y 0} :=
  range_modelWithCornersEuclideanHalfSpace 1

/-- The half-line model is not boundaryless, so it has no transport to its vector space. -/
example : ¬(𝓡∂ 1).Boundaryless :=
  not_boundaryless_modelWithCornersEuclideanHalfSpace 1

/-! ### Complementary indices -/

/-- For `f = 0` on `ℝ`, the Morse indices of `f` and `-f` at `0` are `0`, and their sum `0` is not
the dimension `1`. -/
example : manifoldMorseIndex 𝓘(ℝ, ℝ) (-fun _ : ℝ ↦ (0 : ℝ)) 0 = 0 ∧
    manifoldMorseIndex 𝓘(ℝ, ℝ) (fun _ : ℝ ↦ (0 : ℝ)) 0 = 0 ∧
    manifoldMorseIndex 𝓘(ℝ, ℝ) (-fun _ : ℝ ↦ (0 : ℝ)) 0 +
      manifoldMorseIndex 𝓘(ℝ, ℝ) (fun _ : ℝ ↦ (0 : ℝ)) 0 ≠ finrank ℝ ℝ := by
  simp [Pi.neg_def]

/-- The critical point `0` of `f = 0` on `ℝ` is degenerate: otherwise the complementary-index
identity would hold there. -/
example : ¬IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, ℝ) (fun _ : ℝ ↦ (0 : ℝ)) 0 := fun h ↦ by
  simpa [Pi.neg_def] using h.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank

/-- For `f = x²` on `ℝ`, the Morse indices of `-f` and `f` at `0` are `1` and `0`, with sum the
dimension `1`. -/
example : manifoldMorseIndex 𝓘(ℝ, ℝ) (fun x : ℝ ↦ -x ^ 2) 0 +
    manifoldMorseIndex 𝓘(ℝ, ℝ) (fun x : ℝ ↦ x ^ 2) 0 = finrank ℝ ℝ := by
  rw [manifoldMorseIndex_neg_sq_real, manifoldMorseIndex_sq_real_zero, finrank_self]

/-! ### The normalization of the Hessian and of the Morse chart -/

/-- The Hessian of `x²` at its critical point `0` is `2`, not `1`. -/
example : criticalHessian 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2) 0 1 1 = 2 :=
  (criticalHessian_sq_real_apply 0 1 1).trans (by norm_num)

/-- **A normalized Morse chart of `x²` at `0` does not rescale.** The Morse index of `x²` at `0`
is `0`, so the normal form `x² = 0² + Σ_{i<λ} -(yᵢ)² + Σ_{i≥λ} (yᵢ)²` of
`TauCeti.IsManifoldNondegenerateCriticalPoint.exists_normalized_morseChart` reads `x² = ‖y‖²`, and
the coordinate `y = ψ x` has `‖ψ x‖ = |x|`. -/
theorem norm_eq_abs_of_normalized_morseChart_sq
    {ψ : ℝ → EuclideanSpace ℝ (Fin (finrank ℝ ℝ))} {x : ℝ}
    (h : x ^ 2 = (0 : ℝ) ^ 2 + ∑ i, (if i.val < manifoldMorseIndex 𝓘(ℝ, ℝ)
      (fun y : ℝ ↦ y ^ 2) 0 then -1 else 1) * ψ x i ^ 2) :
    ‖ψ x‖ = |x| := by
  simp only [manifoldMorseIndex_sq_real_zero, Nat.not_lt_zero, ite_false, one_mul,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at h
  rw [← sq_eq_sq₀ (norm_nonneg _) (abs_nonneg x), sq_abs, h, EuclideanSpace.norm_sq_eq]
  simp

/-- **The normalized Morse chart of `x²` at its minimum.** There is a normalized Morse chart `ψ`
of `x ↦ x²` at `0` in which `x² = ‖ψ x‖²` on the whole source, so that `‖ψ x‖ = |x|`: the
function reads `y²`, not `y² / 2`. -/
theorem exists_normalized_morseChart_sq :
    ∃ ψ : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ ℝ))) ℝ
        (EuclideanSpace ℝ (Fin (finrank ℝ ℝ))) ∞,
      0 ∈ ψ.source ∧ ψ 0 = 0 ∧ ∀ x ∈ ψ.source, x ^ 2 = ‖ψ x‖ ^ 2 ∧ ‖ψ x‖ = |x| := by
  obtain ⟨ψ, h0, hψ0, hψ⟩ :=
    (isMorse_sq_real.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
      mfderiv_sq_real_zero).exists_normalized_morseChart
      (Eventually.of_forall fun _ ↦ (contDiff_id.pow 2).contMDiff.contMDiffAt)
  refine ⟨ψ, h0, hψ0, fun x hx ↦ ?_⟩
  -- The smoothness witness writes the function as `fun y ↦ id y ^ 2`.
  have habs := norm_eq_abs_of_normalized_morseChart_sq (by simpa only [id] using hψ x hx)
  exact ⟨by rw [habs, sq_abs], habs⟩

end TauCeti.Examples.MorseCriticalHessian
