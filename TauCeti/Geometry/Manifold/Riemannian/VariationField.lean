/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Surface

/-!
# The variation field of a family of curves

A *variation* of a curve `γ` in a manifold is a two-parameter family `F : ℝ → ℝ → M` with
`F 0 = γ`, whose first argument is the variation parameter `s` and whose second argument is the
curve parameter `t`.  Its *variation field* is the transverse velocity `V(t) = ∂F/∂s (0, t)`, a
tangent vector at `γ t`.  Hypotheses on a variation are stated on the uncurried map
`fun z : ℝ × ℝ ↦ F z.1 z.2`.

In a Riemannian manifold, metric compatibility of the Levi-Civita connection along the transverse
curves and along `γ`, together with the symmetry lemma for the mixed covariant derivatives of a
parametrized surface, give the two pointwise derivative formulas that variational arguments
consume: the transverse derivative of the squared speed of the curves `F s`, and the product rule
for `⟪V, γ'⟫` along `γ`.  They are the pointwise content of the Gauss lemma and of the first
variation of energy.

## Main definitions and results

* `TauCeti.Manifold.variationField`: the variation field of a two-parameter family.
* `TauCeti.Manifold.variationField_eq_mfderiv`: the variation field is the differential of the
  uncurried family in the direction of the first parameter.
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

variable (I) in
/-- The **variation field** of a two-parameter family `F`: the velocity at `s = 0` of the
transverse curve `s ↦ F s t`, a tangent vector at `F 0 t`.  In the classical notation it is
`V(t) = ∂F/∂s (0, t)`. -/
def variationField (F : ℝ → ℝ → M) (t : ℝ) : TangentSpace I (F 0 t) :=
  curveVelocity I (fun s ↦ F s t) 0

/-- The defining formula for the variation field. -/
theorem variationField_apply (F : ℝ → ℝ → M) (t : ℝ) :
    variationField I F t = curveVelocity I (fun s ↦ F s t) 0 :=
  (rfl)

/-- The variation field as a function of the curve parameter: the unapplied form of
`variationField_apply`. -/
theorem variationField_def (F : ℝ → ℝ → M) :
    variationField I F = fun t ↦ curveVelocity I (fun s ↦ F s t) 0 :=
  (rfl)

/-- At a parameter where every curve of the family passes through the same point, the variation
field vanishes. -/
theorem variationField_eq_zero {t : ℝ} (h : ∀ s, F s t = F 0 t) :
    variationField I F t = 0 := by
  have hfun : (fun s ↦ F s t) = fun _ ↦ F 0 t := funext h
  rw [variationField_apply, hfun, curveVelocity_const]

/-- The variation field is the differential of the uncurried family in the direction of the
first parameter. -/
theorem variationField_eq_mfderiv {t : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t)) :
    variationField I F t =
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, t) ((1 : ℝ), (0 : ℝ)) := by
  rw [variationField_apply, curveVelocity_eq_mfderiv_fst hf]

/-! ### The transverse derivatives of the metric pairings -/

variable [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **The transverse derivative of the squared speed.** At a parameter where the family is `C²`,
the derivative at `s = 0` of the squared speed of `F s` at `t` is `2 ⟪D_t V, γ'⟫`, where `V` is
the variation field and `γ = F 0`: metric compatibility along the transverse curve gives
`2 ⟪D_s ∂_t F, ∂_t F⟫`, and the symmetry lemma exchanges the two covariant derivatives. -/
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
          (alongCurve (leviCivitaConnection I M) (F 0) (curveVelocity I (F 0)) t)) t := by
  have hbase : F 0 t ∈ (trivializationAt E (TangentSpace I) (F 0 t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (F 0 t)
  have hVcoord := hf.differentiableAt_sectionCoord_curveVelocity_fst (f := F) hbase
  have hγt : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (F 0) t :=
    hf.comp t (contMDiff_iff_contDiff.mpr (contDiff_prodMk_right (n := 2) (0 : ℝ))).contMDiffAt
  obtain ⟨u, hu, hγu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp hγt
  have hγcoord := differentiableAt_sectionCoord_curveVelocity (I := I) (E := E) (γ := F 0)
    (hγu.mono interior_subset) isOpen_interior (mem_interior_iff_mem_nhds.mpr hu)
  rw [variationField_def]
  exact (isMetricCompatible_leviCivitaConnection (I := I) (M := M))
    |>.hasDerivAt_inner_alongCurve (hγt.mdifferentiableAt two_ne_zero) hVcoord hγcoord

end TauCeti.Manifold

end
