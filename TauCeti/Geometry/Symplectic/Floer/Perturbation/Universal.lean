/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Perturbation.Manifold
import TauCeti.Geometry.Manifold.VectorBundle.Translate

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

variable [FiniteDimensional ℝ E]

/-- **Joint intrinsic first variation.** For a jointly `C²` map family, a torsion-free
connection, and affine paths of the two Hamiltonian coefficients and the endomorphism field,
the covariant derivative at zero is the map linearization plus the three coefficient
terms. The coefficient vector fields and endomorphism fields need only be differentiable
at the base image point. The scalar Hamiltonians must be differentiable along the map
family near zero, so their Hamiltonian fields respect affine combinations there. -/
theorem alongCurve_floerOperator_add_smul_coefficients
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (htor : cov.IsTorsionFree) {u : ℝ → ℝ × ℝ → M} {z : ℝ × ℝ}
    (hu : ContMDiffAt 𝓘(ℝ, ℝ × (ℝ × ℝ)) I 2 (Function.uncurry u) (0, z))
    (hJ : MDiffAt (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x) x (J z x)) (u 0 z))
    (hY : MDiffAt (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x) x (Y z x)) (u 0 z))
    (hXs : MDiffAt (T% (ω.hamiltonianVectorField (Ks z))) (u 0 z))
    (hXt : MDiffAt (T% (ω.hamiltonianVectorField (Kt z))) (u 0 z))
    (hδXs : MDiffAt (T% (ω.hamiltonianVectorField (δKs z))) (u 0 z))
    (hδXt : MDiffAt (T% (ω.hamiltonianVectorField (δKt z))) (u 0 z))
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
  let Vt := fun r ↦ curveVelocity I (fun t ↦ u r (z.1, t)) z.2
  let W := fun r ↦
    Y z (γ r) (Vt r - ω.hamiltonianVectorField (Kt z) (γ r)) -
      ω.hamiltonianVectorField (δKs z) (γ r) -
      J z (γ r) (ω.hamiltonianVectorField (δKt z) (γ r)) -
      r • Y z (γ r) (ω.hamiltonianVectorField (δKt z) (γ r))
  -- Establish regularity of the fixed operator and the coefficient correction separately.
  have hF := ω.differentiableAt_sectionCoord_floerOperator J Ks Kt hu hJ hXs hXt
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ 0 :=
    (hu.comp 0 (contMDiff_iff_contDiff.mpr (contDiff_prodMk_left z)).contMDiffAt).mdifferentiableAt
      (by norm_num)
  have hbase := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (u 0 z)
  -- Only the t-velocity is needed for the coefficient correction.
  have ht : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2
      (fun p : ℝ × ℝ ↦ u p.1 (z.1, p.2)) (0, z.2) :=
    hu.comp (0, z.2) (contMDiff_iff_contDiff.mpr (by fun_prop :
      ContDiff ℝ 2 (fun p : ℝ × ℝ ↦ (p.1, (z.1, p.2))))).contMDiffAt
  have hVt := ht.mdifferentiableAt_curveVelocity_snd (f := fun r t ↦ u r (z.1, t))
  have hJγ := hJ.comp 0 hγ
  have hYγ := hY.comp 0 hγ
  have hXtγ := hXt.comp 0 hγ
  have hδXsγ := hδXs.comp 0 hγ
  have hδXtγ := hδXt.comp 0 hγ
  have hΔt := hVt.sub_sectionAlong hXtγ
  -- The correction W is differentiable in bundle coordinates; only its value at zero
  -- survives the product rule for r • W(r).
  have hA := differentiableAt_sectionCoord γ _ (hYγ.clm_bundle_apply hΔt) hbase
  have hB := differentiableAt_sectionCoord γ _ hδXsγ hbase
  have hC := differentiableAt_sectionCoord γ _ (hJγ.clm_bundle_apply hδXtγ) hbase
  have hD := differentiableAt_sectionCoord γ _ (hYγ.clm_bundle_apply hδXtγ) hbase
  have hW : DifferentiableAt ℝ (sectionCoord (F := E) γ W (γ 0)) 0 := by
    simpa only [W, sectionCoord_sub, sectionCoord_smul] using!
      ((hA.sub hB).sub hC).sub (differentiableAt_id.smul hD)
  -- Use the exact affine expansion, retaining the mixed quadratic term.
  have heq : (fun r ↦ ω.floerOperator (fun w x ↦ J w x + r • Y w x)
      (fun w ↦ Ks w + r • δKs w) (fun w ↦ Kt w + r • δKt w) (u r) z) =ᶠ[𝓝 0]
      (fun r ↦ ω.floerOperator J Ks Kt (u r) z + r • W r) :=
    hK.mono fun r hr ↦ ω.floerOperator_add_smul_coefficients J Y Ks Kt δKs δKt
      (u r) z hr.1 hr.2.1 hr.2.2.1 hr.2.2.2 r
  -- Apply the sum and scalar product rules, then the fixed-coefficient map variation.
  rw [alongCurve_congr cov γ _ heq,
    alongCurve_add cov γ _ _ hF
      (by simpa only [sectionCoord_smul] using! differentiableAt_id.smul hW),
    alongCurve_smul cov γ W (fun r : ℝ ↦ r) differentiableAt_id hW,
    ω.alongCurve_floerOperator cov htor J Ks Kt hu hJ hXs hXt]
  simp only [W, γ, Vt, deriv_id'', one_smul, zero_smul, add_zero, sub_zero]
  abel

end TauCeti.SmoothTwoForm
