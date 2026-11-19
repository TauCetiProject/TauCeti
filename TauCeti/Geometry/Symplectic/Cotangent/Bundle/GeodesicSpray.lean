/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Spray
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Basic
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Hyperregular
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.LagrangianVectorField
public import TauCeti.Geometry.Symplectic.Hamiltonian.GeodesicFlow
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Christoffel
import TauCeti.Geometry.Manifold.VectorBundle.Submersion
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# The geodesic flow is the Lagrangian flow of the kinetic energy

Let `g` be a smooth symmetric nondegenerate metric on a finite-dimensional boundaryless manifold
`M`, of any signature, and let `L(v) = ½ g(v, v)` be its **kinetic Lagrangian** on the tangent
bundle, the mechanical Lagrangian of `g` with zero potential (`TauCeti.mechanicalLagrangian g 0`).
Its Lagrangian vector field `X_E` is the Hamiltonian vector field of the energy `E_L` for the
Cartan two-form `ω_L = FL^* ω`. All declarations below are in the namespace `TauCeti.Manifold`.
Read in the tangent-bundle chart at a tangent vector `v` at `x`,

`X_E(v) = (v, -Γ_x(v, v))`

(`ContMDiffNondegenerateMetric.hamiltonianVectorField_lagrangianEnergy_mechanicalLagrangian`),
where `Γ` is the Christoffel symbol of the second kind of the metric read in the chart at `x`
(`TauCeti.Manifold.christoffelSecondKind`). In the chart at `v` the local Lagrangian is the
kinetic Lagrangian `(q, u) ↦ ½ G_q(u, u)` of the chart metric `G`
(`ContMDiffNondegenerateMetric.mechanicalLagrangian_extChartAt_symm`), so the equation
`ι_(X_E) ω_L = dE_L` becomes the corresponding equation for that kinetic Lagrangian, which is the
geodesic equation (`TauCeti.snd_eq_neg_christoffelSecondKind_of_symplecticForm`).

For a Riemannian metric, the Christoffel symbols of the chart metric are those of the Levi-Civita
connection, so **the Lagrangian vector field of `½ |v|²` is the geodesic spray**
(`hamiltonianVectorField_lagrangianEnergy_eq_geodesicSpray`). Consequently the velocity lift of a
`C²` curve is an integral curve of the Lagrangian vector field exactly when the curve is a geodesic
(`isMIntegralCurve_curveVelocityLift_hamiltonianVectorField_iff`).

The kinetic Lagrangian of a nondegenerate metric on a finite-dimensional manifold is hyperregular
(`ContMDiffNondegenerateMetric.isHyperregularLagrangian_mechanicalLagrangian`): its Legendre map
`v ↦ g(v, ·)` is a diffeomorphism `TM ≃ T*M`, and its Hamiltonian is the kinetic energy of
covectors `H(p) = ½ p(g_x⁻¹ p)`
(`TauCeti.IsHyperregularLagrangian.hamiltonian_mechanicalLagrangian`). The Legendre map
conjugates the two flows, so **a `C²` curve is a geodesic exactly when the Legendre transform of
its velocity is an integral curve of the Hamiltonian vector field of the kinetic energy**
(`isMIntegralCurve_legendreMap_comp_curveVelocityLift_iff`): the metric geodesic flow is the
kinetic Hamiltonian flow on `T*M`.

## Main results

* `ContMDiffNondegenerateMetric.hamiltonianVectorField_lagrangianEnergy_mechanicalLagrangian`:
  the Lagrangian vector field of the kinetic Lagrangian of a nondegenerate metric is
  `(v, -Γ(v, v))` in the tangent-bundle chart at `v`.
* `hamiltonianVectorField_lagrangianEnergy_eq_geodesicSpray`: for a Riemannian metric it is the
  geodesic spray.
* `isMIntegralCurve_curveVelocityLift_hamiltonianVectorField_iff`: geodesics are the base curves
  of the Lagrangian flow of the kinetic energy.
* `isMIntegralCurve_legendreMap_comp_curveVelocityLift_iff`: geodesics are the base curves of the
  Hamiltonian flow of the kinetic energy on `T*M`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 45 (geodesics as motions of a free particle).
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Section 7.5 (the geodesic spray of a metric Lagrangian).
-/

public section

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace TauCeti.Manifold

namespace ContMDiffNondegenerateMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (g : ContMDiffNondegenerateMetric (I := I) (M := M))

/-! ### The kinetic Lagrangian of a nondegenerate metric -/

/-- The kinetic Lagrangian `v ↦ ½ g(v, v)` of a smooth metric is smooth. -/
theorem contMDiff_mechanicalLagrangian :
    ContMDiff I.tangent 𝓘(ℝ) ∞ (mechanicalLagrangian (⇑g) 0) :=
  TauCeti.contMDiff_mechanicalLagrangian g.contMDiff contMDiff_const

/-- **A nondegenerate metric gives a hyperregular mechanical Lagrangian.** On a finite-dimensional
manifold, the Legendre map `v ↦ g(v, ·)` of `L(v) = ½ g(v, v) - V(x)` is a bijection `TM → T*M`,
for every potential `V`. -/
theorem isHyperregularLagrangian_mechanicalLagrangian [FiniteDimensional ℝ E] (V : M → ℝ) :
    IsHyperregularLagrangian (mechanicalLagrangian (⇑g) V) :=
  (isHyperregularLagrangian_mechanicalLagrangian_iff g.apply_comm V).2 fun x ↦
    ContinuousLinearMap.isInvertible_iff_nondegenerate_toBilinForm.2 (g.nondegenerate x)

/-- **The kinetic Lagrangian in a tangent-bundle chart.** Read in the tangent-bundle chart at `v`,
the kinetic Lagrangian `½ g(w, w)` is the kinetic Lagrangian `(q, u) ↦ ½ G_q(u, u)` of the metric
`G` read in the chart at the base point of `v`. -/
theorem mechanicalLagrangian_extChartAt_symm (v : TangentBundle I M) {y : E × E}
    (hy : y ∈ (extChartAt I.tangent v).target) :
    mechanicalLagrangian (⇑g) 0 ((extChartAt I.tangent v).symm y) =
      kineticLagrangian (g.chartMetric v.proj) y := by
  obtain ⟨hb, h2⟩ := extChartAt_tangent_symm_mem_baseSet_and_snd v hy
  set w := (extChartAt I.tangent v).symm y
  have hproj : w.proj = (extChartAt I v.proj).symm y.1 := Bundle.proj_extChartAt_symm v hy
  -- The fibre coordinate of `w` in the trivialization at `v.proj` is `y.2`.
  have hw : (trivializationAt E (TangentSpace I) v.proj).symm w.proj y.2 = w.2 := by
    rw [← h2]
    exact (trivializationAt E (TangentSpace I) v.proj).symm_apply_apply_mk hb w.2
  rw [mechanicalLagrangian_apply, kineticLagrangian_apply,
    g.chartMetric_apply (Bundle.fst_mem_extChartAt_target v hy), ← hproj, hw, Pi.zero_apply]
  ring

variable [FiniteDimensional ℝ E] [I.Boundaryless]

/-- **The Lagrangian vector field of the kinetic energy, pointwise.** Let `g` be a smooth
nondegenerate metric on a finite-dimensional boundaryless manifold and `L = ½ g(v, v)` its kinetic
Lagrangian. A tangent vector `X` of `TM` at `v` solving `ι_X ω_L = dE_L` there is, read in the
tangent-bundle chart at `v`, the vector `(v, -Γ(v, v))`, where `Γ` is the Christoffel symbol of the
second kind of the chart metric at the base point of `v`. -/
theorem eq_of_eval₂_cartanTwoForm_mechanicalLagrangian {v : TangentBundle I M}
    {X : TangentSpace I.tangent v}
    (hX : ∀ W, SmoothBundleForm.eval₂ (cartanTwoForm _ g.contMDiff_mechanicalLagrangian) v X W =
      mvfderiv I.tangent (lagrangianEnergy (mechanicalLagrangian (⇑g) 0)) v W) :
    X = (v.2, -christoffelSecondKind (g.chartMetric v.proj) (extChartAt I v.proj v.proj)
      v.2 v.2) := by
  set L := mechanicalLagrangian (⇑g) 0
  have hL := g.contMDiff_mechanicalLagrangian
  set G := g.chartMetric v.proj
  set x₀ := extChartAt I v.proj v.proj
  -- The fibre coordinate of `v` and the vector `X`, read on the model spaces.
  set w₀ : E := v.2
  set Y : E × E := X
  have hΦv : extChartAt I.tangent v v = (x₀, w₀) := by
    refine Prod.ext ?_ (extChartAt_tangent_self_snd v)
    rw [Bundle.extChartAt_apply_of_mem_baseSet v (FiberBundle.mem_baseSet_trivializationAt' _)]
  -- The base component of `X` is `v`, as the fibre Hessian of `L` is the invertible form `g`.
  have hY₁ : Y.1 = w₀ := by
    have h := mfderiv_proj_eq_snd_of_eval₂_cartanTwoForm hL
      (isRegularLagrangian_iff.1 (g.isHyperregularLagrangian_mechanicalLagrangian 0).1 v) hX
    rw [Bundle.mfderiv_proj] at h
    exact h
  -- Near the coordinates of `v` the local Lagrangian is the kinetic Lagrangian of `G`, so the two
  -- have the same Legendre map and energy there.
  have hℓ : L ∘ (extChartAt I.tangent v).symm =ᶠ[𝓝 (x₀, w₀)] kineticLagrangian G := by
    rw [← hΦv]
    filter_upwards [extChartAt_target_mem_nhds (I := I.tangent) v] with y hy
    exact g.mechanicalLagrangian_extChartAt_symm v hy
  have hFL : linearLegendreMap (L ∘ (extChartAt I.tangent v).symm) =ᶠ[𝓝 (x₀, w₀)]
      linearLegendreMap (kineticLagrangian G) := by
    filter_upwards [hℓ.eventually_nhds] with y hy
    refine Prod.ext (by rw [linearLegendreMap_fst, linearLegendreMap_fst]) ?_
    rw [linearLegendreMap_snd, linearLegendreMap_snd]
    exact Filter.EventuallyEq.fderiv_eq
      (((continuous_const.prodMk continuous_id).tendsto y.2).eventually hy)
  have hE : (fun y ↦ (linearLegendreMap (L ∘ (extChartAt I.tangent v).symm) y).2 y.2 -
      (L ∘ (extChartAt I.tangent v).symm) y) =ᶠ[𝓝 (x₀, w₀)]
      fun y ↦ (linearLegendreMap (kineticLagrangian G) y).2 y.2 - kineticLagrangian G y :=
    (hFL.and hℓ).mono fun y hy ↦ by dsimp only; rw [hy.1, hy.2]
  -- The equation `ι_X ω_L = dE_L`, read in the chart, is that of the kinetic Lagrangian of `G`.
  have htarget : (extChartAt I v.proj).target ∈ 𝓝 x₀ := extChartAt_target_mem_nhds v.proj
  have key := snd_eq_neg_christoffelSecondKind_of_symplecticForm (x := (x₀, w₀)) (X := Y)
    (by filter_upwards [htarget] with y hy
        exact LinearMap.BilinForm.isSymm_iff.mpr (g.isSymm_chartMetric hy))
    (g.nondegenerate_chartMetric (mem_extChartAt_target v.proj))
    (((g.contDiffOn_chartMetric v.proj).contDiffAt htarget).of_le (by simp)) hY₁ fun W ↦ by
      rw [← hFL.fderiv_eq, ← hE.fderiv_eq, ← hΦv]
      exact (eval₂_cartanTwoForm_eq_fderiv_linearLegendreMap hL v _ W).symm.trans
        ((hX W).trans
          (DFunLike.congr_fun (mvfderiv_lagrangianEnergy_eq_fderiv hL (by simp) v) W))
  exact Prod.ext hY₁ key

/-- **The Lagrangian vector field of the kinetic energy.** For a smooth nondegenerate metric `g`
on a finite-dimensional boundaryless manifold, the Hamiltonian vector field of the energy of the
kinetic Lagrangian `L = ½ g(v, v)` for its Cartan two-form is, in the tangent-bundle chart at `v`,
the second-order vector `(v, -Γ(v, v))`, where `Γ` is the Christoffel symbol of the second kind of
the chart metric at the base point of `v`. -/
theorem hamiltonianVectorField_lagrangianEnergy_mechanicalLagrangian (v : TangentBundle I M) :
    (cartanTwoForm _ g.contMDiff_mechanicalLagrangian).hamiltonianVectorField
        (lagrangianEnergy (mechanicalLagrangian (⇑g) 0)) v =
      (v.2, -christoffelSecondKind (g.chartMetric v.proj) (extChartAt I v.proj v.proj)
        v.2 v.2) :=
  g.eq_of_eval₂_cartanTwoForm_mechanicalLagrangian
    (SmoothTwoForm.isHamiltonianVectorField_iff.1
      (((g.isHyperregularLagrangian_mechanicalLagrangian 0).1.isSymplectic_cartanTwoForm
        g.contMDiff_mechanicalLagrangian).isNondegenerate
          |>.isHamiltonianVectorField_hamiltonianVectorField _) v)

end ContMDiffNondegenerateMetric

/-! ### Riemannian metrics: the geodesic spray -/

section Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

local notation "g" => ContMDiffNondegenerateMetric.ofRiemannianBundle I M

/-- **The Lagrangian vector field of `½ |v|²` is the geodesic spray.** On a finite-dimensional
boundaryless Riemannian manifold, the Hamiltonian vector field of the energy of the kinetic
Lagrangian `L(v) = ½ ⟨v, v⟩` for its Cartan two-form `ω_L = FL^* ω` is the geodesic spray
`(x, v) ↦ (v, -Γ_x(v, v))` of the Levi-Civita connection. -/
theorem hamiltonianVectorField_lagrangianEnergy_eq_geodesicSpray :
    (cartanTwoForm _ (g).contMDiff_mechanicalLagrangian).hamiltonianVectorField
        (lagrangianEnergy (mechanicalLagrangian (⇑(g)) 0)) = geodesicSpray I M := by
  funext v
  rw [ContMDiffNondegenerateMetric.hamiltonianVectorField_lagrangianEnergy_mechanicalLagrangian,
    geodesicSpray_apply]
  -- The Christoffel symbols of the chart metric are those of the Levi-Civita connection.
  have hint : extChartAt I v.proj v.proj ∈ interior (range I) := by
    rw [I.range_eq_univ, interior_univ]
    exact mem_univ _
  have h :=
    (ContMDiffNondegenerateMetric.isLeviCivitaConnection_ofRiemannianBundle_leviCivitaConnection
      I M).christoffelMap_apply_eq_christoffelSecondKind (Module.finBasis ℝ E)
      (mem_extChartAt_source v.proj) hint v.2 v.2
  exact congrArg (fun w : E ↦ ((v.2 : E), -w)) h.symm

/-- **Geodesics are the motions of a free particle.** On a finite-dimensional boundaryless
Riemannian manifold, the velocity lift `t ↦ (γ t, γ' t)` of a `C²` curve is an integral curve of
the Lagrangian vector field of the kinetic Lagrangian `½ |v|²` exactly when `γ` is a geodesic. -/
theorem isMIntegralCurve_curveVelocityLift_hamiltonianVectorField_iff {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ) :
    IsMIntegralCurve (curveVelocityLift I γ)
        ((cartanTwoForm _ (g).contMDiff_mechanicalLagrangian).hamiltonianVectorField
          (lagrangianEnergy (mechanicalLagrangian (⇑(g)) 0))) ↔
      IsGeodesicCurve I γ := by
  rw [hamiltonianVectorField_lagrangianEnergy_eq_geodesicSpray]
  exact isMIntegralCurve_curveVelocityLift_iff hγ

/-- **The geodesic flow is the kinetic Hamiltonian flow.** On a finite-dimensional boundaryless
Riemannian manifold, a `C²` curve `γ` is a geodesic exactly when the Legendre transform
`t ↦ ⟨γ' t, ·⟩` of its velocity is an integral curve of the Hamiltonian vector field, for the
canonical symplectic form of `T*M`, of the Hamiltonian `H = E_L ∘ FL⁻¹` of the kinetic Lagrangian
`½ |v|²`, that is of the kinetic energy of covectors `H(p) = ½ p(g_x⁻¹ p)`
(`TauCeti.IsHyperregularLagrangian.hamiltonian_mechanicalLagrangian`). -/
theorem isMIntegralCurve_legendreMap_comp_curveVelocityLift_iff {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ) :
    IsMIntegralCurve (legendreMap (mechanicalLagrangian (⇑(g)) 0) ∘ curveVelocityLift I γ)
        ((CotangentBundle.symplecticForm I M).hamiltonianVectorField
          ((g).isHyperregularLagrangian_mechanicalLagrangian 0).hamiltonian) ↔
      IsGeodesicCurve I γ := by
  rw [((g).isHyperregularLagrangian_mechanicalLagrangian 0).isMIntegralCurve_legendreMap_comp_iff
    (g).contMDiff_mechanicalLagrangian]
  exact isMIntegralCurve_curveVelocityLift_hamiltonianVectorField_iff hγ

end Riemannian

end TauCeti.Manifold
