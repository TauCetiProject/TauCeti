/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Gauge.Action
public import TauCeti.Geometry.Symplectic.AtiyahBott.TrivialBundle

/-!
# Equivariance of the Atiyah–Bott moment map under the gauge group

Let `M` be a closed oriented surface, `𝔸` a normed real algebra, for instance a matrix algebra,
and consider the connections `d + A` of the trivial bundle over `M`, for the `𝔸`-valued
`1`-forms `A`. The gauge group `C^∞(M, 𝔸)ˣ` acts on them by
`g · A = g A g⁻¹ - (dg) g⁻¹` (`TauCeti.mgaugeAction`), an affine action whose linear part is the
conjugation `Ad_g a = g a g⁻¹` of `𝔸`-valued forms (`TauCeti.gaugeConj`). The Atiyah–Bott form
`Ω(a, b) = ∫_M B(a ∧ b)` (`TauCeti.atiyahBottFormWith`) and the curvature moment map
`⟨μ(A), ξ⟩ = ∫_M B(F_A, ξ)` (`TauCeti.atiyahBottMomentWith`), with the commutator of `𝔸` as
bracket, are defined from a bilinear form `B` on `𝔸`. This file shows that when `B` is invariant
under conjugation by the values of a gauge transformation `g`, as the trace form
`B(a, b) = -Re tr(a b)` of a matrix algebra is under every invertible matrix, then:

* `g` preserves the Atiyah–Bott form: `Ω(Ad_g a, Ad_g b) = Ω(a, b)`
  (`TauCeti.atiyahBottFormWith_gaugeConj_gaugeConj`). Since the gauge action is affine with linear
  part `Ad_g` (`TauCeti.mgaugeAction_add`), this says that `g` acts on the space of connections by
  a symplectomorphism.
* the moment map is equivariant for the coadjoint action of the gauge group:
  `⟨μ(g · A), ξ⟩ = ⟨μ(A), g⁻¹ ξ g⟩`, that is `μ(g · A) = Ad*_g μ(A)` with
  `(Ad*_g ν)(ξ) = ν(Ad_(g⁻¹) ξ)` (`TauCeti.atiyahBottMomentWith_mgaugeAction`). This follows from
  the transformation law `F_(g · A) = g F_A g⁻¹` of the curvature
  (`TauCeti.gaugeCurvature_mgaugeAction`).
* the zero level of the moment map is gauge invariant: `μ(g · A) = 0` exactly when `μ(A) = 0`
  (`TauCeti.atiyahBottMomentWith_mgaugeAction_eq_zero_iff`), so the gauge group acts on it. When
  `B` is moreover nondegenerate, it is the set of flat connections
  (`TauCeti.atiyahBottMomentWith_eq_zero_iff`), and its quotient is the moduli space of flat
  connections.

The infinitesimal versions of these statements, for the generators `ξ_A = -d_A ξ` of the gauge
action (`TauCeti.hasDerivAt_mgaugeAction_gaugeExp_smul_apply`), are the moment map equation and
the vanishing of the moment cocycle in `TauCeti.Geometry.Symplectic.AtiyahBott.TrivialBundle`.

## Main results

* `TauCeti.atiyahBottFormWith_gaugeConj_gaugeConj`: gauge transformations preserve the
  Atiyah–Bott form.
* `TauCeti.atiyahBottMomentWith_mgaugeAction`: the curvature moment map is equivariant.
* `TauCeti.atiyahBottMomentWith_mgaugeAction_eq_zero_iff`: the zero level is gauge invariant.

## References

* M. F. Atiyah and R. Bott, *The Yang–Mills equations over Riemann surfaces*, Philos. Trans.
  Roy. Soc. London Ser. A 308 (1983), 523–615 (the curvature as an equivariant moment map for the
  gauge group).
* E. Meinrenken, *Symplectic geometry*, lecture notes, 2000, Theorem 7.46 (the trivial bundle
  over a surface).
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M 𝔸 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [ContMDiffRing 𝓘(ℝ, 𝔸) ∞ 𝔸]
  (B : 𝔸 →L[ℝ] 𝔸 →L[ℝ] ℝ) [FiniteDimensional ℝ E] [CompactSpace M]
  (o : Manifold.Orientation I M (Fin 2)) (g : (C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯)ˣ)

/-- **Gauge transformations preserve the Atiyah–Bott form.** If `B` is invariant under
conjugation by the values of the gauge transformation `g`, then
`Ω(g a g⁻¹, g b g⁻¹) = Ω(a, b)`. -/
theorem atiyahBottFormWith_gaugeConj_gaugeConj
    (hB : ∀ x a b, B ((g : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x * a * (↑g⁻¹ : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x)
      ((g : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x * b * (↑g⁻¹ : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x) = B a b)
    (a b : SmoothForm I M 𝔸 1) :
    atiyahBottFormWith B o (gaugeConj g a) (gaugeConj g b) = atiyahBottFormWith B o a b := by
  have h : SmoothForm.wedgeWith B (gaugeConj g a) (gaugeConj g b) =
      SmoothForm.wedgeWith B a b :=
    SmoothBundleForm.ext_eval₂ fun x v w ↦ by
      simp only [SmoothBundleForm.eval₂_apply, SmoothForm.wedgeWith_apply_one_one, gaugeConj_val,
        hB]
  rw [atiyahBottFormWith_apply, atiyahBottFormWith_apply, ← SmoothForm.coe_wedgeWith,
    ← SmoothForm.coe_wedgeWith, h]

/-- **The Atiyah–Bott moment map is equivariant** for the coadjoint action of the gauge group.
If `B` is invariant under conjugation by the values of the gauge transformation `g`, then
`⟨μ(g · A), ξ⟩ = ⟨μ(A), g⁻¹ ξ g⟩`, that is `μ(g · A) = Ad*_g μ(A)`. -/
theorem atiyahBottMomentWith_mgaugeAction
    (hB : ∀ x a b, B ((g : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x * a * (↑g⁻¹ : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x)
      ((g : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x * b * (↑g⁻¹ : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x) = B a b)
    (A : SmoothForm I M 𝔸 1) (ξ : SmoothForm I M 𝔸 0) :
    atiyahBottMomentWith (ContinuousLinearMap.mul ℝ 𝔸 - (ContinuousLinearMap.mul ℝ 𝔸).flip) B o
        (mgaugeAction g A) ξ =
      atiyahBottMomentWith (ContinuousLinearMap.mul ℝ 𝔸 - (ContinuousLinearMap.mul ℝ 𝔸).flip) B o
        A (gaugeConj g⁻¹ ξ) := by
  have h : SmoothForm.wedgeWith B (gaugeConj g (gaugeCurvature
      (ContinuousLinearMap.mul ℝ 𝔸 - (ContinuousLinearMap.mul ℝ 𝔸).flip) A))
        (gaugeConj g (gaugeConj g⁻¹ ξ)) =
      SmoothForm.wedgeWith B (gaugeCurvature
        (ContinuousLinearMap.mul ℝ 𝔸 - (ContinuousLinearMap.mul ℝ 𝔸).flip) A) (gaugeConj g⁻¹ ξ) :=
    SmoothBundleForm.ext_eval₂ fun x v w ↦ by
      simp only [SmoothBundleForm.eval₂_apply, SmoothForm.wedgeWith_apply_zero_right,
        gaugeConj_val _ (gaugeConj g⁻¹ ξ), gaugeConj_val _ (gaugeCurvature _ A), hB]
  rw [gaugeConj_gaugeConj_inv] at h
  rw [atiyahBottMomentWith_apply, atiyahBottMomentWith_apply, ← SmoothForm.coe_wedgeWith,
    ← SmoothForm.coe_wedgeWith, gaugeCurvature_mgaugeAction, h]

/-- **The zero level of the moment map is gauge invariant**: if `B` is invariant under
conjugation by the values of the gauge transformation `g`, then `μ(g · A) = 0` exactly when
`μ(A) = 0`. -/
theorem atiyahBottMomentWith_mgaugeAction_eq_zero_iff
    (hB : ∀ x a b, B ((g : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x * a * (↑g⁻¹ : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x)
      ((g : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x * b * (↑g⁻¹ : C^∞⟮I, M; 𝓘(ℝ, 𝔸), 𝔸⟯) x) = B a b)
    (A : SmoothForm I M 𝔸 1) :
    atiyahBottMomentWith (ContinuousLinearMap.mul ℝ 𝔸 - (ContinuousLinearMap.mul ℝ 𝔸).flip) B o
        (mgaugeAction g A) = 0 ↔
      atiyahBottMomentWith (ContinuousLinearMap.mul ℝ 𝔸 - (ContinuousLinearMap.mul ℝ 𝔸).flip) B o
        A = 0 := by
  refine ⟨fun h ↦ LinearMap.ext fun ξ ↦ ?_, fun h ↦ LinearMap.ext fun ξ ↦ ?_⟩
  · have hξ := LinearMap.congr_fun h (gaugeConj g ξ)
    rwa [atiyahBottMomentWith_mgaugeAction B o g hB, gaugeConj_inv_gaugeConj] at hξ
  · rw [atiyahBottMomentWith_mgaugeAction B o g hB, h, LinearMap.zero_apply, LinearMap.zero_apply]

end TauCeti
