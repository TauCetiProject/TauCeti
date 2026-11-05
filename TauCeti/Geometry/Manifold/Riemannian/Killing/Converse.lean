/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Killing.Basic
public import TauCeti.Geometry.Manifold.Flow.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
import TauCeti.Geometry.Manifold.Riemannian.VariationField

/-!
# Infinitesimal generators of metric-preserving flows

A smooth vector field whose local flow preserves tangent norms is Killing. It suffices that,
for each point and tangent vector, norm preservation holds for times in a neighbourhood of zero;
neither the field nor the metric needs to be complete.

The proof differentiates the squared length of a transported transverse velocity at time zero.
Metric compatibility and the symmetry lemma identify its derivative with
`2 ⟪∇_u X, u⟫`. Polarization gives the Killing equation.

The central formal inputs are `hasDerivAt_norm_sq_curveVelocity`, the covariant derivative
pullback formula, and the native maximal flow's smooth dependence on initial points.
See Petersen, *Riemannian Geometry*, third edition, Chapter 8, for the local-flow
characterization of Killing fields.
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {X : Π x : M, TangentSpace I x}

/-- Norm preservation near time zero in one tangent direction forces the diagonal
Killing equation in that direction. -/
theorem inner_leviCivitaConnection_self_eq_zero_of_eventually_norm_mfderiv_flowOf
    (hX : CMDiff ∞ (T% X)) (p : M) (u : TangentSpace I p)
    (hflow : ∀ᶠ t : ℝ in 𝓝 0, ‖mfderiv I I (flowOf X t) p u‖ = ‖u‖) :
    inner ℝ (leviCivitaConnection I M X p u) u = 0 := by
  have hX₁ : CMDiff 1 (T% X) := hX.of_le (by simp)
  -- A radial geodesic realizes the arbitrary tangent vector without global completeness.
  let γ : ℝ → M := fun q ↦ riemannianExp I M p (q • u)
  have hγ₀ : γ 0 = p := by simp [γ]
  have hγ : ContMDiffAt 𝓘(ℝ) I 2 γ 0 :=
    (contMDiffAt_riemannianExp_smul_zero p u).of_le (by simp)
  have hvel : curveVelocity I γ 0 = u := curveVelocity_riemannianExp_smul_zero p u
  let F : ℝ → ℝ → M := fun q t ↦ flowOf X t (γ q)
  have hF₀ : (fun q ↦ F q 0) = γ := funext fun q ↦ flowOf_zero hX₁ (γ q)
  have hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2
      (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, 0) :=
    contMDiffAt_flowOf_comp (by norm_num) (hX.of_le (by simp))
      (contMDiff_iff_contDiff.mpr
        (by fun_prop : ContDiff ℝ 2 (Prod.snd : ℝ × ℝ → ℝ))).contMDiffAt
      (hγ.comp (f := Prod.fst) (g := γ) (0, 0)
        (contMDiff_iff_contDiff.mpr (by fun_prop)).contMDiffAt)
      (mem_flowDomain_zero hX₁ (γ 0))
  let U : ∀ t, TangentSpace I (F 0 t) :=
    fun t ↦ curveVelocity I (fun q ↦ F q t) 0
  -- Regard time as the variation parameter and use the transverse squared-speed formula.
  have hd := hasDerivAt_norm_sq_curveVelocity (F := fun t q ↦ F q t) (t := 0)
    (hF.comp (f := Prod.swap) (0, 0)
      (contMDiff_iff_contDiff.mpr (contDiff_snd.prodMk contDiff_fst)).contMDiffAt)
  have htime (q : ℝ) : curveVelocity I (F q) 0 = X (F q 0) :=
    curveVelocity_flowOf hX₁ (mem_flowDomain_zero hX₁ (γ q))
  have hfield : (fun q ↦ X (F q 0)) = (fun q ↦ X (γ q)) :=
    funext fun q ↦ congrArg X (congrFun hF₀ q)
  rw [variationField_def, funext htime, hfield, hF₀] at hd
  have hpull := alongCurve_pullback (leviCivitaConnection I M) γ X (hasMFDerivAt_curveVelocity
    (hγ.mdifferentiableAt (by norm_num))) (hX.mdifferentiable (by simp) (γ 0))
  rw [hpull, hvel, hγ₀] at hd
  -- Norm preservation makes that scalar function locally constant, on the actual flow domain.
  have hconst : (fun t ↦ ‖U t‖ ^ 2) =ᶠ[𝓝 0] fun _ ↦ ‖u‖ ^ 2 := by
    have hdom : ∀ᶠ t : ℝ in 𝓝 0, (t, p) ∈ flowDomain X :=
      ((isOpen_flowDomain hX₁).preimage
        (by fun_prop : Continuous fun t : ℝ ↦ (t, p))).mem_nhds
          (mem_flowDomain_zero hX₁ p)
    filter_upwards [hflow, hdom] with t hn htd
    have hslice := contMDiffAt_flowOf_comp (n := 1) (by norm_num) hX₁
      contMDiffAt_const contMDiffAt_id htd
    have hmap := curveVelocityWithin_map (s := univ)
      (by simpa only [hγ₀] using hslice.mdifferentiableAt one_ne_zero)
      uniqueDiffWithinAt_univ (hγ.mdifferentiableAt (by norm_num)).mdifferentiableWithinAt
    simp only [curveVelocityWithin_univ, Function.comp_def, id_eq, hvel] at hmap
    have hnorm : ‖U t‖ = ‖mfderiv I I (flowOf X t) p u‖ := by
      have hFt : F 0 t = flowOf X t p := by simp only [F, hγ₀]
      rw [hFt]
      exact congrArg (fun w : TangentSpace I (flowOf X t p) ↦ ‖w‖)
        (hmap.trans (by rw [hγ₀]))
    rw [hnorm, hn]
  have heq := hd.deriv.symm.trans hconst.deriv_eq
  have hF₀₀ : F 0 0 = p := (congrFun hF₀ 0).trans hγ₀
  rw [deriv_const, hF₀₀] at heq
  exact (mul_eq_zero.mp heq).resolve_left two_ne_zero

/-- A smooth vector field is Killing if its local flow preserves tangent norms near time zero.
The neighbourhood may depend on both the point and the tangent vector. -/
theorem isKillingField_of_eventually_norm_mfderiv_flowOf
    (hX : CMDiff ∞ (T% X))
    (hflow : ∀ (x : M) (u : TangentSpace I x), ∀ᶠ t : ℝ in 𝓝 0,
      ‖mfderiv I I (flowOf X t) x u‖ = ‖u‖) :
    IsKillingField I X := by
  refine ((isMetricCompatible_leviCivitaConnection (M := M) I).isKillingField_iff_inner_self
    (torsion_leviCivitaConnection_eq_zero (M := M) I)).2 ⟨hX, fun p u ↦ ?_⟩
  exact inner_leviCivitaConnection_self_eq_zero_of_eventually_norm_mfderiv_flowOf hX p u
    (hflow p u)

end TauCeti.Manifold
