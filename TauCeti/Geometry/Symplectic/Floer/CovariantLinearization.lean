/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
public import TauCeti.Geometry.Symplectic.Floer.Linearization
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Surface
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# Intrinsic map variation of the Floer equation

For a torsion-free connection on the target, differentiate the inhomogeneous Floer operator
`F(u) = u_s - X_Ks + J(u)(u_t - X_Kt)` along a family of maps. Its covariant derivative is

`D_u ξ = ∇_s ξ - ∇_ξ X_Ks + (∇_ξ J)(u_t - X_Kt) + J(∇_t ξ - ∇_ξ X_Kt)`.

All vectors live in the actual tangent fibre of the target. The derivative of `J` is the
induced Hom connection, not the ordinary derivative of a matrix in a chosen chart. The
variation field is the actual parameter velocity of the family, and the interchange of
parameter and domain derivatives follows from torsion-freeness and joint `C²` regularity.
Domain-dependent coefficients are allowed; coefficients are held fixed during this map
variation. No Floer equation, compatibility of the connection with `J`, or metric is required.
This is a pointwise formula, not a Sobolev or Fredholm assertion.

The operator is written with partial curve velocities, so its definition does not depend on
any choice of connection. For a differentiable map, `floerOperator_eq` identifies it with the
coordinate expression of the intrinsic perturbed derivative `du - X_K`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Sections 3.1 and 8.1 (linearization and Hamiltonian perturbations).
-/

public noncomputable section

open Bundle CovariantDerivative
open TauCeti.Manifold
open scoped Manifold Topology

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The intrinsic Floer operator `u_s - X_Ks + J(u)(u_t - X_Kt)`, with partial derivatives
expressed as velocities of the two coordinate curves. -/
def floerOperator (ω : SmoothTwoForm I M)
    (J : ℝ × ℝ → ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (Ks Kt : ℝ × ℝ → M → ℝ) (u : ℝ × ℝ → M) (z : ℝ × ℝ) : TangentSpace I (u z) :=
  curveVelocity I (fun s ↦ u (s, z.2)) z.1 - ω.hamiltonianVectorField (Ks z) (u z) +
    J z (u z) (curveVelocity I (fun t ↦ u (z.1, t)) z.2 -
      ω.hamiltonianVectorField (Kt z) (u z))

/-- The partial-velocity expression for the intrinsic Floer operator. -/
theorem floerOperator_def (ω : SmoothTwoForm I M)
    (J : ℝ × ℝ → ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (Ks Kt : ℝ × ℝ → M → ℝ) (u : ℝ × ℝ → M) (z : ℝ × ℝ) :
    ω.floerOperator J Ks Kt u z =
      curveVelocity I (fun s ↦ u (s, z.2)) z.1 - ω.hamiltonianVectorField (Ks z) (u z) +
        J z (u z) (curveVelocity I (fun t ↦ u (z.1, t)) z.2 -
          ω.hamiltonianVectorField (Kt z) (u z)) := (rfl)

/-- For a differentiable map the Floer operator is `du - X_K` on the real coordinate
vector plus `J` applied to `du - X_K` on the imaginary coordinate vector. -/
theorem floerOperator_eq (ω : SmoothTwoForm I M)
    (J : ℝ × ℝ → ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (Ks Kt : ℝ × ℝ → M → ℝ) {u : ℝ × ℝ → M} {z : ℝ × ℝ}
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) :
    ω.floerOperator J Ks Kt u z =
      ω.perturbedMFDeriv Ks Kt u z stdComplexLineReal +
        J z (u z) (ω.perturbedMFDeriv Ks Kt u z stdComplexLineImag) := by
  have hu' : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I
      (fun p : ℝ × ℝ ↦ u (p.1, p.2)) (z.1, z.2) := by
    simpa only [Prod.mk.eta] using hu
  rw [floerOperator_def, perturbedMFDeriv_apply_stdComplexLineReal,
    perturbedMFDeriv_apply_stdComplexLineImag,
    curveVelocity_eq_mfderiv_fst (f := fun s t ↦ u (s, t)) hu',
    curveVelocity_eq_mfderiv_snd (f := fun s t ↦ u (s, t)) hu']
  simp only [stdComplexLineReal_eq, stdComplexLineImag_eq]

variable [FiniteDimensional ℝ E]

/-- For almost complex coefficients, the zero equation is complex linearity of `du - X_K`. -/
theorem floerOperator_eq_zero_iff (ω : SmoothTwoForm I M)
    (J : ℝ × ℝ → ∀ x : M, AlmostComplexStructure (TangentSpace I x))
    (Ks Kt : ℝ × ℝ → M → ℝ) {u : ℝ × ℝ → M} {z : ℝ × ℝ}
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) :
    ω.floerOperator (fun w x ↦ (J w x).toLinearMap.toContinuousLinearMap) Ks Kt u z = 0 ↔
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedMFDeriv Ks Kt u z).toLinearMap := by
  rw [floerOperator_eq ω _ Ks Kt hu, ω.isComplexLinearMap_perturbedMFDeriv_iff]
  simp only [perturbedMFDeriv_apply_stdComplexLineReal,
    perturbedMFDeriv_apply_stdComplexLineImag, LinearMap.coe_toContinuousLinearMap']

/-- The map-direction linearization formula for a torsion-free target connection and fixed
domain-dependent coefficients. The `∇J` term uses the induced endomorphism connection.
`alongCurve_floerOperator` gives its derivative interpretation under torsion-freeness. -/
def floerLinearization (ω : SmoothTwoForm I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (J : ℝ × ℝ → ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (Ks Kt : ℝ × ℝ → M → ℝ) (u : ℝ × ℝ → M)
    (ξ : ∀ z, TangentSpace I (u z)) (z : ℝ × ℝ) : TangentSpace I (u z) :=
  alongCurve cov (fun s ↦ u (s, z.2)) (fun s ↦ ξ (s, z.2)) z.1 -
      cov (ω.hamiltonianVectorField (Ks z)) (u z) (ξ z) +
    cov.hom cov (J z) (u z) (ξ z)
      (curveVelocity I (fun t ↦ u (z.1, t)) z.2 - ω.hamiltonianVectorField (Kt z) (u z)) +
    J z (u z) (alongCurve cov (fun t ↦ u (z.1, t)) (fun t ↦ ξ (z.1, t)) z.2 -
      cov (ω.hamiltonianVectorField (Kt z)) (u z) (ξ z))

/-- The full covariant formula for the map-direction linearization. -/
theorem floerLinearization_def (ω : SmoothTwoForm I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (J : ℝ × ℝ → ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (Ks Kt : ℝ × ℝ → M → ℝ) (u : ℝ × ℝ → M)
    (ξ : ∀ z, TangentSpace I (u z)) (z : ℝ × ℝ) :
    ω.floerLinearization cov J Ks Kt u ξ z =
      alongCurve cov (fun s ↦ u (s, z.2)) (fun s ↦ ξ (s, z.2)) z.1 -
          cov (ω.hamiltonianVectorField (Ks z)) (u z) (ξ z) +
        cov.hom cov (J z) (u z) (ξ z)
          (curveVelocity I (fun t ↦ u (z.1, t)) z.2 - ω.hamiltonianVectorField (Kt z) (u z)) +
        J z (u z) (alongCurve cov (fun t ↦ u (z.1, t)) (fun t ↦ ξ (z.1, t)) z.2 -
          cov (ω.hamiltonianVectorField (Kt z)) (u z) (ξ z)) := (rfl)

section Algebra

variable (ω : SmoothTwoForm I M)
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  (J : ℝ × ℝ → ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
  (Ks Kt : ℝ × ℝ → M → ℝ) (u : ℝ × ℝ → M)
  (ξ η : ∀ z, TangentSpace I (u z)) (z : ℝ × ℝ)

/-- The intrinsic linearization sends the zero direction to zero. -/
@[simp]
theorem floerLinearization_zero : ω.floerLinearization cov J Ks Kt u 0 z = 0 := by
  simp [floerLinearization_def]

/-- The intrinsic linearization commutes with constant real scaling. -/
@[simp]
theorem floerLinearization_smul (c : ℝ) :
    ω.floerLinearization cov J Ks Kt u (c • ξ) z =
      c • ω.floerLinearization cov J Ks Kt u ξ z := by
  simp only [floerLinearization_def, Pi.smul_apply, alongCurve_const_smul, map_smul,
    smul_apply, smul_sub, smul_add, map_sub]

/-- The intrinsic linearization is additive on directions differentiable along the two
coordinate curves. -/
theorem floerLinearization_add
    (hξs : DifferentiableAt ℝ
      (sectionCoord (F := E) (fun s ↦ u (s, z.2)) (fun s ↦ ξ (s, z.2)) (u z)) z.1)
    (hηs : DifferentiableAt ℝ
      (sectionCoord (F := E) (fun s ↦ u (s, z.2)) (fun s ↦ η (s, z.2)) (u z)) z.1)
    (hξt : DifferentiableAt ℝ
      (sectionCoord (F := E) (fun t ↦ u (z.1, t)) (fun t ↦ ξ (z.1, t)) (u z)) z.2)
    (hηt : DifferentiableAt ℝ
      (sectionCoord (F := E) (fun t ↦ u (z.1, t)) (fun t ↦ η (z.1, t)) (u z)) z.2) :
    ω.floerLinearization cov J Ks Kt u (ξ + η) z =
      ω.floerLinearization cov J Ks Kt u ξ z + ω.floerLinearization cov J Ks Kt u η z := by
  simp only [floerLinearization_def, Pi.add_apply,
    alongCurve_add cov _ _ _ hξs hηs, alongCurve_add cov _ _ _ hξt hηt,
    map_add, add_apply, map_sub]
  abel

end Algebra

/-- **Intrinsic first variation of the Floer operator.** For a jointly `C²` map family and a
torsion-free target connection, the covariant parameter derivative of the nonlinear operator
is its map-direction linearization on the actual parameter velocity. Only differentiability
of the coefficient fields at the image point is needed. -/
theorem alongCurve_floerOperator (ω : SmoothTwoForm I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (htor : cov.IsTorsionFree)
    (J : ℝ × ℝ → ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (Ks Kt : ℝ × ℝ → M → ℝ) {u : ℝ → ℝ × ℝ → M} {q : ℝ} {z : ℝ × ℝ}
    (hu : ContMDiffAt 𝓘(ℝ, ℝ × (ℝ × ℝ)) I 2 (Function.uncurry u) (q, z))
    (hJ : MDiffAt (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x) x (J z x)) (u q z))
    (hKs : MDiffAt (T% (ω.hamiltonianVectorField (Ks z))) (u q z))
    (hKt : MDiffAt (T% (ω.hamiltonianVectorField (Kt z))) (u q z)) :
    alongCurve cov (fun a ↦ u a z) (fun a ↦ ω.floerOperator J Ks Kt (u a) z) q =
      ω.floerLinearization cov J Ks Kt (u q)
        (fun w ↦ curveVelocity I (fun a ↦ u a w) q) z := by
  let γ := fun a ↦ u a z
  let Vs := fun a ↦ curveVelocity I (fun s ↦ u a (s, z.2)) z.1
  let Vt := fun a ↦ curveVelocity I (fun t ↦ u a (z.1, t)) z.2
  have hs : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2
      (fun p : ℝ × ℝ ↦ u p.1 (p.2, z.2)) (q, z.1) :=
    hu.comp (q, z.1) (contMDiff_iff_contDiff.mpr (by fun_prop :
      ContDiff ℝ 2 (fun p : ℝ × ℝ ↦ (p.1, (p.2, z.2))))).contMDiffAt
  have ht : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2
      (fun p : ℝ × ℝ ↦ u p.1 (z.1, p.2)) (q, z.2) :=
    hu.comp (q, z.2) (contMDiff_iff_contDiff.mpr (by fun_prop :
      ContDiff ℝ 2 (fun p : ℝ × ℝ ↦ (p.1, (z.1, p.2))))).contMDiffAt
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ q :=
    (hu.comp q (contMDiff_iff_contDiff.mpr (contDiff_prodMk_left z)).contMDiffAt).mdifferentiableAt
      (by norm_num)
  have hbase := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (u q z)
  have hVs := hs.differentiableAt_sectionCoord_curveVelocity_snd
    (f := fun a s ↦ u a (s, z.2)) hbase
  have hVt := ht.differentiableAt_sectionCoord_curveVelocity_snd
    (f := fun a t ↦ u a (z.1, t)) hbase
  have hVs' := (differentiableAt_sectionCoord_iff γ Vs hγ hbase).1 hVs
  have hVt' := (differentiableAt_sectionCoord_iff γ Vt hγ hbase).1 hVt
  have hXs := hKs.comp q hγ
  have hXt := hKt.comp q hγ
  have hΔs := hVs'.sub_sectionAlong hXs
  have hΔt := hVt'.sub_sectionAlong hXt
  have hJΔt := (hJ.comp q hγ).clm_bundle_apply hΔt
  simp_rw [floerOperator_def]
  rw [alongCurve_add cov γ _ _
    (differentiableAt_sectionCoord _ _ hΔs hbase)
    (differentiableAt_sectionCoord _ _ hJΔt hbase),
    alongCurve_clm_apply cov γ _ (J z) hγ hJ hΔt,
    alongCurve_sub cov γ Vs _ hVs (differentiableAt_sectionCoord _ _ hXs hbase),
    alongCurve_sub cov γ Vt _ hVt (differentiableAt_sectionCoord _ _ hXt hbase),
    alongCurve_pullback cov γ _ (hasMFDerivAt_curveVelocity hγ) hKs,
    alongCurve_pullback cov γ _ (hasMFDerivAt_curveVelocity hγ) hKt]
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hscomm := alongCurve_curveVelocity_comm cov htor (f := fun a s ↦ u a (s, z.2))
    (by simpa only [minSmoothness_of_isRCLikeNormedField] using hs)
  have htcomm := alongCurve_curveVelocity_comm cov htor (f := fun a t ↦ u a (z.1, t))
    (by simpa only [minSmoothness_of_isRCLikeNormedField] using ht)
  rw [← hscomm, ← htcomm, floerLinearization_def]
  abel

end TauCeti.SmoothTwoForm

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Under the canonical target tangent identification, the intrinsic Floer operator for a
constant form agrees with the vector-space operator at differentiable maps. -/
theorem floerOperator_constSmooth (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    {u : ℝ × ℝ → V} {z : ℝ × ℝ} (hu : DifferentiableAt ℝ u z) :
    NormedSpace.fromTangentSpace (u z)
        (ω.constSmooth.floerOperator (fun w x ↦
          (NormedSpace.fromTangentSpace x).symm.toContinuousLinearMap ∘L
            J w x ∘L (NormedSpace.fromTangentSpace x).toContinuousLinearMap) Ks Kt u z) =
      ω.floerOperator J Ks Kt u z := by
  rw [SmoothTwoForm.floerOperator_eq ω.constSmooth _ Ks Kt hu.mdifferentiableAt, map_add]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply,
    fromTangentSpace_perturbedMFDeriv_constSmooth_apply, floerOperator_def,
    perturbedFDeriv_apply_stdComplexLineReal, perturbedFDeriv_apply_stdComplexLineImag]

end TauCeti.SymplecticForm
