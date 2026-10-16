/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Acceleration
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Surface

/-!
# The transverse derivatives of the metric pairings along a variation

A *variation* of a curve `γ` in a manifold is a two-parameter family `F : ℝ → ℝ → M` with
`F 0 = γ`, whose first argument is the variation parameter `s` and whose second argument is the
curve parameter `t`.  Its *variation field* `V = TauCeti.Manifold.variationField I F`, defined in
`TauCeti.Geometry.Manifold.MFDeriv.Curve`, is the transverse velocity `V(t) = ∂F/∂s (0, t)`, a
tangent vector at `γ t`.  Hypotheses on a variation are stated on the uncurried map
`fun z : ℝ × ℝ ↦ F z.1 z.2`.

In a Riemannian manifold with its Levi-Civita connection, this file records the two pointwise
derivative formulas that variational arguments consume, valid at every parameter where the family
is `C²`: the transverse derivative of the squared speed of the curves `F s`, and the product rule
for `⟪V, γ'⟫` along `γ`.  They are the pointwise content of the Gauss lemma
(`TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Basic`) and of the first variation of energy
(`TauCeti.Geometry.Manifold.Riemannian.FirstVariation`).

## Main results

* `TauCeti.Manifold.hasDerivAt_norm_sq_curveVelocity`: the transverse derivative of the squared
  speed is `2 ⟪D_t V, γ'⟫`.
* `TauCeti.Manifold.hasDerivAt_inner_variationField_curveVelocity`: the product rule
  `d/dt ⟪V, γ'⟫ = ⟪D_t V, γ'⟫ + ⟪V, D_t γ'⟫`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §3, Lemma 3.5 and Ch. 9, §2,
  Proposition 2.4, whose proofs are the two derivative formulas.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2nd ed., 2018, Ch. 6, variations
  of curves and their variation fields.
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : ℝ → ℝ → M}

variable [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **The transverse derivative of the squared speed.** At a parameter `t` where the family is
`C²`, the function `s ↦ ‖∂_t F (s, t)‖²` has derivative `2 ⟪D_t V(t), γ'(t)⟫` at `s = 0`, where
`V` is the variation field and `γ = F 0`.  Integrated over `[a, b]`, this is the derivative of
the energy of the curves `F s` in the first variation formula. -/
theorem hasDerivAt_norm_sq_curveVelocity {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    HasDerivAt (fun s ↦ ‖curveVelocity I (F s) t‖ ^ 2)
      (2 * inner ℝ (alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t)
        (curveVelocity I (F 0) t)) 0 := by
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hbase : F 0 t ∈ (trivializationAt E (TangentSpace I) (F 0 t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (F 0 t)
  have hPcoord := hf.differentiableAt_sectionCoord_curveVelocity_snd (f := F) hbase
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun q ↦ F q t) 0 :=
    (hf.comp 0 (contMDiff_iff_contDiff.mpr (contDiff_prodMk_left (n := 2) t)).contMDiffAt)
      |>.mdifferentiableAt two_ne_zero
  have hprod := (isMetricCompatible_leviCivitaConnection (I := I) (M := M))
    |>.hasDerivAt_inner_alongCurve hcurve hPcoord hPcoord
  have hswap := alongCurve_curveVelocity_comm (leviCivitaConnection I M)
    ((isTorsionFree_iff_torsion_eq_zero _).2 (torsion_leviCivitaConnection_eq_zero I))
    (f := F) (u := 0) (v := t) (hf.of_le (by simp))
  rw [← hswap, real_inner_comm (curveVelocity I (F 0) t), ← two_mul, real_inner_comm] at hprod
  rw [variationField_def]
  exact hprod.congr_of_eventuallyEq
    (Eventually.of_forall fun s ↦ (real_inner_self_eq_norm_sq _).symm)

/-- **The product rule for the variation field against the velocity.** At a parameter where the
family is `C²`, the function `t ↦ ⟪V(t), γ'(t)⟫` has derivative `⟪D_t V, γ'⟫ + ⟪V, D_t γ'⟫`.
Integrated over `[a, b]`, this is the integration by parts in the first variation formula. -/
theorem hasDerivAt_inner_variationField_curveVelocity {t : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    HasDerivAt (fun r ↦ inner ℝ (variationField I F r) (curveVelocity I (F 0) r))
      (inner ℝ (alongCurve (leviCivitaConnection I M) (F 0) (variationField I F) t)
          (curveVelocity I (F 0) t) +
        inner ℝ (variationField I F t)
          (acceleration (leviCivitaConnection I M) (F 0) t)) t := by
  have hbase : F 0 t ∈ (trivializationAt E (TangentSpace I) (F 0 t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (F 0 t)
  have hVcoord := hf.differentiableAt_sectionCoord_curveVelocity_fst (f := F) hbase
  have hγt : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (F 0) t :=
    hf.comp t (contMDiff_iff_contDiff.mpr (contDiff_prodMk_right (n := 2) (0 : ℝ))).contMDiffAt
  obtain ⟨u, hu, hγu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp hγt
  have hγcoord := differentiableAt_sectionCoord_curveVelocity (I := I) (E := E) (γ := F 0)
    (hγu.mono interior_subset) isOpen_interior (mem_interior_iff_mem_nhds.mpr hu)
  rw [variationField_def, acceleration_def]
  exact (isMetricCompatible_leviCivitaConnection (I := I) (M := M))
    |>.hasDerivAt_inner_alongCurve (hγt.mdifferentiableAt two_ne_zero) hVcoord hγcoord

end TauCeti.Manifold

end
