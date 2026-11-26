/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.GaugeCurvature.Transformation
public import TauCeti.Geometry.Symplectic.AtiyahBott.TrivialBundle

/-!
# Gauge invariance of the Atiyah–Bott form and equivariance of the curvature moment map

Let `M` be a closed oriented surface, let `𝔄` be a complete normed real algebra, and let
`P = M × 𝔄ˣ` be the trivial principal bundle. Its connections `d + A` form the affine space
`Ω¹(M; 𝔄)`, on which the gauge group `C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯` acts by
`g · A = g A g⁻¹ - (dg) g⁻¹` (`TauCeti.SmoothForm.gaugeAction`). The Atiyah–Bott form
`Ω(a, b) = ∫_M B(a ∧ b)` (`TauCeti.atiyahBottFormWith`) and the curvature moment map
`⟨μ(A), ξ⟩ = ∫_M B(F_A, ξ)` (`TauCeti.atiyahBottMomentWith`) of
`TauCeti.Geometry.Symplectic.AtiyahBott.TrivialBundle` are taken here for the commutator bracket
of `𝔄` and a bilinear form `B` on `𝔄` invariant under conjugation by the values of `g`,
`B(k u k⁻¹, k v k⁻¹) = B(u, v)`. A trace form `B(u, v) = -tr(u v)` on real matrices is invariant
under all of `𝔄ˣ`, and the inner product `B(u, v) = Re tr(u v*)` on complex matrices is invariant
under the unitary group, so the hypothesis holds for gauge transformations with values in `U(n)`.
The connections and the arguments of the moment map stay `𝔄`-valued even then: the setup with
values in the Lie algebra `𝔲(n)` is not developed here.

* **The symplectic form is gauge invariant.** The gauge action is affine over the conjugation
  `b ↦ g b g⁻¹` of tangent vectors (`TauCeti.SmoothForm.gaugeAction_add`), and this conjugation
  preserves `Ω` when `B` is invariant under conjugation by the values of `g`
  (`TauCeti.atiyahBottFormWith_gaugeConj`). So every gauge transformation whose values preserve
  `B` is a symplectomorphism of the affine space of connections.
* **The moment map is equivariant.** Since the curvature transforms by
  `F_(g · A) = g F_A g⁻¹` (`TauCeti.gaugeCurvature_gaugeAction`), the invariance of `B` gives
  `⟨μ(g · A), ξ⟩ = ⟨μ(A), g⁻¹ ξ g⟩`, that is, `μ(g · A) = Ad*_g μ(A)` for the coadjoint action of
  the gauge group on the dual of its Lie algebra `C^∞(M, 𝔄)`
  (`TauCeti.atiyahBottMomentWith_gaugeAction`). This is the group-level form of the infinitesimal
  equivariance `TauCeti.atiyahBottFormWith_neg_gaugeCovariantDeriv_neg_gaugeCovariantDeriv`.
* **The zero level is gauge invariant.** In particular `μ(g · A) = 0` exactly when `μ(A) = 0`
  (`TauCeti.atiyahBottMomentWith_gaugeAction_eq_zero_iff`), so the gauge group acts on the zero
  level. When `B` is moreover nondegenerate, the zero level is the set of flat connections
  (`TauCeti.atiyahBottMomentWith_eq_zero_iff`), and its quotient is the moduli space of flat
  connections.

## Main results

* `TauCeti.atiyahBottFormWith_gaugeConj`: `Ω(g a g⁻¹, g b g⁻¹) = Ω(a, b)`.
* `TauCeti.atiyahBottMomentWith_gaugeAction`: `μ(g · A) = μ(A) ∘ Ad_(g⁻¹)`.
* `TauCeti.atiyahBottMomentWith_gaugeAction_eq_zero_iff`: the zero level is gauge invariant.

## References

* M. F. Atiyah and R. Bott, *The Yang–Mills equations over Riemann surfaces*, Philos. Trans.
  Roy. Soc. London Ser. A 308 (1983), 523–615 (the curvature as an equivariant moment map for the
  gauge group).
* E. Meinrenken, *Symplectic geometry*, lecture notes (2000), Theorem 7.46 (the trivial bundle).
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M 𝔄 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄]
  (B : 𝔄 →L[ℝ] 𝔄 →L[ℝ] ℝ) (o : Manifold.Orientation I M (Fin 2))
  {g : C^∞⟮I, M; 𝓘(ℝ, 𝔄), 𝔄ˣ⟯}

/-- **The Atiyah–Bott form is gauge invariant.** If `B` is invariant under conjugation by the
values of a gauge transformation `g`, the conjugation `b ↦ g b g⁻¹`, which is the differential of
the gauge action of `g` (`TauCeti.SmoothForm.gaugeAction_add`), preserves
`Ω(a, b) = ∫_M B(a ∧ b)`. -/
theorem atiyahBottFormWith_gaugeConj
    (hB : ∀ x u v, B ((g x).val * u * ((g x)⁻¹ : 𝔄ˣ).val) ((g x).val * v * ((g x)⁻¹ : 𝔄ˣ).val) =
      B u v)
    (a b : SmoothForm I M 𝔄 1) :
    atiyahBottFormWith B o (gaugeConj g a) (gaugeConj g b) = atiyahBottFormWith B o a b := by
  have h : SmoothForm.wedgeWith B (gaugeConj g a) (gaugeConj g b) =
      SmoothForm.wedgeWith B a b :=
    SmoothBundleForm.ext_eval₂ fun x v w ↦ by
      simp only [SmoothBundleForm.eval₂_apply, SmoothForm.wedgeWith_apply_one_one, gaugeConj_val,
        hB]
  rw [atiyahBottFormWith_apply, atiyahBottFormWith_apply, ← SmoothForm.coe_wedgeWith,
    ← SmoothForm.coe_wedgeWith, h]

/-- **The curvature moment map is equivariant for the gauge group.** For the commutator bracket
of `𝔄` and a bilinear form `B` invariant under conjugation by the values of `g`, the moment map
`⟨μ(A), ξ⟩ = ∫_M B(F_A, ξ)` satisfies `⟨μ(g · A), ξ⟩ = ⟨μ(A), g⁻¹ ξ g⟩`: it intertwines the
gauge action on connections with the coadjoint action on the dual of `C^∞(M, 𝔄)`. -/
theorem atiyahBottMomentWith_gaugeAction {β : 𝔄 →L[ℝ] 𝔄 →L[ℝ] 𝔄}
    (hβ : ∀ a b, β a b = a * b - b * a)
    (hB : ∀ x u v, B ((g x).val * u * ((g x)⁻¹ : 𝔄ˣ).val) ((g x).val * v * ((g x)⁻¹ : 𝔄ˣ).val) =
      B u v)
    (A : SmoothForm I M 𝔄 1) :
    atiyahBottMomentWith β B o (SmoothForm.gaugeAction g A) =
      atiyahBottMomentWith β B o A ∘ₗ gaugeConj g⁻¹ := by
  refine LinearMap.ext fun ξ ↦ ?_
  rw [LinearMap.comp_apply, atiyahBottMomentWith_apply, atiyahBottMomentWith_apply,
    gaugeCurvature_gaugeAction hβ]
  congr 1
  refine funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [RoughForm.wedgeWith_apply_zero_right, RoughForm.wedgeWith_apply_zero_right, gaugeConj_val,
    gaugeConj_val, ← hB x ((gaugeCurvature β A).val x v)]
  simp [ContMDiffMap.coe_inv, mul_assoc]

/-- **The zero level of the moment map is gauge invariant**: `μ(g · A) = 0` exactly when
`μ(A) = 0`, for the commutator bracket and a bilinear form invariant under conjugation by the
values of `g`. -/
theorem atiyahBottMomentWith_gaugeAction_eq_zero_iff {β : 𝔄 →L[ℝ] 𝔄 →L[ℝ] 𝔄}
    (hβ : ∀ a b, β a b = a * b - b * a)
    (hB : ∀ x u v, B ((g x).val * u * ((g x)⁻¹ : 𝔄ˣ).val) ((g x).val * v * ((g x)⁻¹ : 𝔄ˣ).val) =
      B u v)
    (A : SmoothForm I M 𝔄 1) :
    atiyahBottMomentWith β B o (SmoothForm.gaugeAction g A) = 0 ↔
      atiyahBottMomentWith β B o A = 0 := by
  rw [atiyahBottMomentWith_gaugeAction B o hβ hB]
  refine ⟨fun h ↦ LinearMap.ext fun ξ ↦ ?_, fun h ↦ by rw [h, LinearMap.zero_comp]⟩
  have h' := LinearMap.congr_fun h (gaugeConj g ξ)
  rwa [LinearMap.comp_apply, gaugeConj_inv_gaugeConj] at h'

end TauCeti
