/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Perturbation.Manifold
import TauCeti.Geometry.Manifold.VectorBundle.Translate
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap

/-!
# Joint first variation of the intrinsic Floer operator

Differentiate the Floer operator while varying the map, both Hamiltonian coefficients,
and the endomorphism field simultaneously. For the affine coefficient paths
`J + r Y`, `Ks + r δKs`, `Kt + r δKt`, and a map family with velocity `ξ` at zero,
the covariant derivative is

`D_u ξ + Y(u)(u_t - X_Kt) - X_δKs - J(u) X_δKt`.

The exact affine expansion also records the quadratic mixed term
`-r² Y(u) X_δKt`. In particular, the formula does not discard mixed terms before
differentiating. All vectors belong to the actual target tangent fibre.

The endomorphism paths need not be almost complex away from zero: the operator extends
to arbitrary endomorphisms, and its derivative restricts to admissible tangent directions.
This file does not construct admissible paths or assert transversality. The result is
pointwise on a fixed coordinate domain, not a weighted Sobolev or moving-domain assertion.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, second edition,
  Sections 3.1 and 8.1 (universal linearization and Hamiltonian perturbations).
-/

public noncomputable section

open Bundle CovariantDerivative
open TauCeti.Manifold
open scoped Manifold Topology

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  (ω : SmoothTwoForm I M)
  (J Y : ℝ × ℝ → ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
  (Ks Kt δKs δKt : ℝ × ℝ → M → ℝ)

/-- Exact simultaneous coefficient variation of the Floer operator, including the mixed
quadratic term. No equation or almost complex condition is required. -/
theorem floerOperator_add_smul_coefficients (u : ℝ × ℝ → M) (z : ℝ × ℝ)
    (hKs : MDifferentiableAt I 𝓘(ℝ) (Ks z) (u z))
    (hKt : MDifferentiableAt I 𝓘(ℝ) (Kt z) (u z))
    (hδKs : MDifferentiableAt I 𝓘(ℝ) (δKs z) (u z))
    (hδKt : MDifferentiableAt I 𝓘(ℝ) (δKt z) (u z)) (r : ℝ) :
    ω.floerOperator (fun w x ↦ J w x + r • Y w x)
        (fun w ↦ Ks w + r • δKs w) (fun w ↦ Kt w + r • δKt w) u z =
      ω.floerOperator J Ks Kt u z + r •
        (Y z (u z) (curveVelocity I (fun t ↦ u (z.1, t)) z.2 -
            ω.hamiltonianVectorField (Kt z) (u z)) -
          ω.hamiltonianVectorField (δKs z) (u z) -
          J z (u z) (ω.hamiltonianVectorField (δKt z) (u z)) -
          r • Y z (u z) (ω.hamiltonianVectorField (δKt z) (u z))) := by
  rw [ω.floerOperator_add_smul (fun w x ↦ J w x + r • Y w x)
    Ks Kt u δKs δKt z hKs hKt hδKs hδKt]
  simp only [floerOperator_def, add_apply, smul_apply, map_sub, smul_sub, smul_add]
  abel

/-- The affine coefficient correction has a derivative at zero even when the perturbation
fields are only continuous. This difference isolates the part independent of the connection. -/
private theorem hasDerivAt_sectionCoord_floerOperator_coefficient_difference
    {u : ℝ → ℝ × ℝ → M} {z : ℝ × ℝ}
    (hu : ContMDiffAt 𝓘(ℝ, ℝ × (ℝ × ℝ)) I 2 (Function.uncurry u) (0, z))
    (hJ : MDiffAt (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x) x (J z x)) (u 0 z))
    (hY : ContinuousAt (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x) x (Y z x)) (u 0 z))
    (hXt : MDiffAt (T% (ω.hamiltonianVectorField (Kt z))) (u 0 z))
    (hδXs : ContinuousAt (T% (ω.hamiltonianVectorField (δKs z))) (u 0 z))
    (hδXt : ContinuousAt (T% (ω.hamiltonianVectorField (δKt z))) (u 0 z))
    (hK : ∀ᶠ r in 𝓝 (0 : ℝ),
      MDifferentiableAt I 𝓘(ℝ) (Ks z) (u r z) ∧
      MDifferentiableAt I 𝓘(ℝ) (Kt z) (u r z) ∧
      MDifferentiableAt I 𝓘(ℝ) (δKs z) (u r z) ∧
      MDifferentiableAt I 𝓘(ℝ) (δKt z) (u r z)) :
    HasDerivAt (sectionCoord (F := E) (fun r ↦ u r z) (fun r ↦
      ω.floerOperator (fun w x ↦ J w x + r • Y w x)
          (fun w ↦ Ks w + r • δKs w) (fun w ↦ Kt w + r • δKt w) (u r) z -
        ω.floerOperator J Ks Kt (u r) z) (u 0 z))
      (Y z (u 0 z) (curveVelocity I (fun t ↦ u 0 (z.1, t)) z.2 -
          ω.hamiltonianVectorField (Kt z) (u 0 z)) -
        ω.hamiltonianVectorField (δKs z) (u 0 z) -
        J z (u 0 z) (ω.hamiltonianVectorField (δKt z) (u 0 z))) 0 := by
  let γ := fun r ↦ u r z
  let Vt := fun r ↦ curveVelocity I (fun t ↦ u r (z.1, t)) z.2
  let W := fun r ↦
    Y z (γ r) (Vt r - ω.hamiltonianVectorField (Kt z) (γ r)) -
      ω.hamiltonianVectorField (δKs z) (γ r) -
      J z (γ r) (ω.hamiltonianVectorField (δKt z) (γ r)) -
      r • Y z (γ r) (ω.hamiltonianVectorField (δKt z) (γ r))
  -- Establish only continuity of the correction; none of its coefficient fields is differentiated.
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ 0 :=
    (hu.comp 0 (contMDiff_iff_contDiff.mpr (contDiff_prodMk_left z)).contMDiffAt).mdifferentiableAt
      (by norm_num)
  have ht : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2
      (fun p : ℝ × ℝ ↦ u p.1 (z.1, p.2)) (0, z.2) :=
    hu.comp (0, z.2) (contMDiff_iff_contDiff.mpr (by fun_prop :
      ContDiff ℝ 2 (fun p : ℝ × ℝ ↦ (p.1, (z.1, p.2))))).contMDiffAt
  have hVt := (ht.contMDiffAt_curveVelocity_snd_slice (f := fun r t ↦ u r (z.1, t))
    (m := 1) (by norm_num)).mdifferentiableAt one_ne_zero
  have hΔt := hVt.sub_sectionAlong (hXt.comp 0 hγ)
  have hYγ : ContinuousAt (fun r ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (γ r) (Y z (γ r))) 0 :=
    hY.comp (f := γ) hγ.continuousAt
  have hδXsγ : ContinuousAt
      (fun r ↦ TotalSpace.mk' E (γ r) (ω.hamiltonianVectorField (δKs z) (γ r))) 0 :=
    hδXs.comp (f := γ) hγ.continuousAt
  have hδXtγ : ContinuousAt
      (fun r ↦ TotalSpace.mk' E (γ r) (ω.hamiltonianVectorField (δKt z) (γ r))) 0 :=
    hδXt.comp (f := γ) hγ.continuousAt
  have hJγ := (hJ.comp 0 hγ).continuousAt
  have hbase := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ 0)
  have hcoord (V : ∀ r, TangentSpace I (γ r))
      (hV : ContinuousAt (fun r ↦ TotalSpace.mk' E (γ r) (V r)) 0) :=
    continuousAt_sectionCoord γ V hV hbase
  have hW : ContinuousAt (sectionCoord (F := E) γ W (γ 0)) 0 := by
    simpa only [W, sectionCoord_sub, sectionCoord_smul] using!
      (((hcoord _ (hYγ.clm_bundle_apply hΔt.continuousAt)).sub (hcoord _ hδXsγ)).sub
        (hcoord _ (hJγ.clm_bundle_apply hδXtγ))).sub
          (continuousAt_id.smul (hcoord _ (hYγ.clm_bundle_apply hδXtγ)))
  -- At zero, the derivative of r • W(r) is W(0), using continuity rather than a product rule.
  have hp : HasDerivAt (fun r ↦ r • sectionCoord (F := E) γ W (γ 0) r)
      (W 0) 0 := by
    have hd := (hasDerivAt_id (0 : ℝ)).smul_of_eq_zero hW rfl
    simp only [one_smul] at hd
    refine hd.congr_deriv ?_
    rw [sectionCoord_apply]
    exact continuousLinearMapAt_trivializationAt_self (γ 0) (W 0)
  -- Read the exact affine expansion in section coordinates, retaining the mixed term.
  simp only [W, γ, Vt, zero_smul, sub_zero] at hp
  refine hp.congr_of_eventuallyEq ?_
  filter_upwards [hK] with r hr
  simp only [sectionCoord_apply]
  rw [ω.floerOperator_add_smul_coefficients J Y Ks Kt δKs δKt
    (u r) z hr.1 hr.2.1 hr.2.2.1 hr.2.2.2 r]
  simp [γ]

/-- The simultaneous affine-coefficient Floer operator is differentiable as a tangent-bundle map
at zero. Only continuity of the perturbation directions is needed; no connection is required. -/
theorem mdifferentiableAt_floerOperator_add_smul_coefficients
    {u : ℝ → ℝ × ℝ → M} {z : ℝ × ℝ}
    (hu : ContMDiffAt 𝓘(ℝ, ℝ × (ℝ × ℝ)) I 2 (Function.uncurry u) (0, z))
    (hJ : MDiffAt (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x) x (J z x)) (u 0 z))
    (hY : ContinuousAt (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x) x (Y z x)) (u 0 z))
    (hXs : MDiffAt (T% (ω.hamiltonianVectorField (Ks z))) (u 0 z))
    (hXt : MDiffAt (T% (ω.hamiltonianVectorField (Kt z))) (u 0 z))
    (hδXs : ContinuousAt (T% (ω.hamiltonianVectorField (δKs z))) (u 0 z))
    (hδXt : ContinuousAt (T% (ω.hamiltonianVectorField (δKt z))) (u 0 z))
    (hK : ∀ᶠ r in 𝓝 (0 : ℝ),
      MDifferentiableAt I 𝓘(ℝ) (Ks z) (u r z) ∧
      MDifferentiableAt I 𝓘(ℝ) (Kt z) (u r z) ∧
      MDifferentiableAt I 𝓘(ℝ) (δKs z) (u r z) ∧
      MDifferentiableAt I 𝓘(ℝ) (δKt z) (u r z)) :
    MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent (fun r ↦ TotalSpace.mk' E (u r z)
      (ω.floerOperator (fun w x ↦ J w x + r • Y w x)
        (fun w ↦ Ks w + r • δKs w) (fun w ↦ Kt w + r • δKt w) (u r) z)) 0 := by
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun r ↦ u r z) 0 :=
    (hu.comp 0 (contMDiff_iff_contDiff.mpr (contDiff_prodMk_left z)).contMDiffAt).mdifferentiableAt
      (by norm_num)
  apply (differentiableAt_sectionCoord_iff _ _ hγ
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (u 0 z))).1
  have hF := differentiableAt_sectionCoord _ _
    (ω.mdifferentiableAt_floerOperator J Ks Kt hu hJ hXs hXt)
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (u 0 z))
  have hd := ω.hasDerivAt_sectionCoord_floerOperator_coefficient_difference
    J Y Ks Kt δKs δKt hu hJ hY hXt hδXs hδXt hK
  simpa only [sectionCoord_sub, add_sub_cancel] using! hF.add hd.differentiableAt

variable [FiniteDimensional ℝ E]

/-- **Joint intrinsic first variation.** For a jointly `C²` map family, a torsion-free
connection, and affine paths of the two Hamiltonian coefficients and the endomorphism field,
the covariant derivative at zero is the map linearization plus the three coefficient
terms. The fixed coefficient fields need only be differentiable at the base image point;
the perturbation directions need only be continuous there. The scalar Hamiltonians must be
differentiable along the map family near zero, so their Hamiltonian fields respect affine
combinations there. -/
theorem alongCurve_floerOperator_add_smul_coefficients
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (htor : cov.IsTorsionFree) {u : ℝ → ℝ × ℝ → M} {z : ℝ × ℝ}
    (hu : ContMDiffAt 𝓘(ℝ, ℝ × (ℝ × ℝ)) I 2 (Function.uncurry u) (0, z))
    (hJ : MDiffAt (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x) x (J z x)) (u 0 z))
    (hY : ContinuousAt (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x) x (Y z x)) (u 0 z))
    (hXs : MDiffAt (T% (ω.hamiltonianVectorField (Ks z))) (u 0 z))
    (hXt : MDiffAt (T% (ω.hamiltonianVectorField (Kt z))) (u 0 z))
    (hδXs : ContinuousAt (T% (ω.hamiltonianVectorField (δKs z))) (u 0 z))
    (hδXt : ContinuousAt (T% (ω.hamiltonianVectorField (δKt z))) (u 0 z))
    (hK : ∀ᶠ r in 𝓝 (0 : ℝ),
      MDifferentiableAt I 𝓘(ℝ) (Ks z) (u r z) ∧
      MDifferentiableAt I 𝓘(ℝ) (Kt z) (u r z) ∧
      MDifferentiableAt I 𝓘(ℝ) (δKs z) (u r z) ∧
      MDifferentiableAt I 𝓘(ℝ) (δKt z) (u r z)) :
    alongCurve cov (fun r ↦ u r z) (fun r ↦
      ω.floerOperator (fun w x ↦ J w x + r • Y w x)
        (fun w ↦ Ks w + r • δKs w) (fun w ↦ Kt w + r • δKt w) (u r) z) 0 =
      ω.floerLinearization cov J Ks Kt (u 0)
          (fun w ↦ curveVelocity I (fun r ↦ u r w) 0) z +
        Y z (u 0 z) (curveVelocity I (fun t ↦ u 0 (z.1, t)) z.2 -
          ω.hamiltonianVectorField (Kt z) (u 0 z)) -
        ω.hamiltonianVectorField (δKs z) (u 0 z) -
        J z (u 0 z) (ω.hamiltonianVectorField (δKt z) (u 0 z)) := by
  let γ := fun r ↦ u r z
  let F := fun r ↦ ω.floerOperator J Ks Kt (u r) z
  let G := fun r ↦ ω.floerOperator (fun w x ↦ J w x + r • Y w x)
    (fun w ↦ Ks w + r • δKs w) (fun w ↦ Kt w + r • δKt w) (u r) z
  -- Reuse the regularity API for the sum rule and the ordinary derivative of the correction.
  have hF := differentiableAt_sectionCoord γ F
    (ω.mdifferentiableAt_floerOperator J Ks Kt hu hJ hXs hXt)
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (u 0 z))
  have hd := ω.hasDerivAt_sectionCoord_floerOperator_coefficient_difference
    J Y Ks Kt δKs δKt hu hJ hY hXt hδXs hδXt hK
  have hsum : G = fun r ↦ F r + (G r - F r) := by funext r; abel
  have hzero : G 0 - F 0 = 0 := by simp [G, F]
  -- Name the curve and operators in the goal so the sum rule matches these local abbreviations.
  -- The difference vanishes at zero, so its Christoffel term vanishes as well.
  change alongCurve cov γ G 0 = _
  rw [hsum, alongCurve_add cov γ F (fun r ↦ G r - F r) hF hd.differentiableAt,
    ← alongCurveWithin_univ cov γ (fun r ↦ G r - F r) 0,
    alongCurveWithin_eq_derivWithin_sectionCoord_of_eq_zero cov γ _ hzero,
    derivWithin_univ, hd.deriv,
    ω.alongCurve_floerOperator cov htor J Ks Kt hu hJ hXs hXt]
  abel

end TauCeti.SmoothTwoForm
