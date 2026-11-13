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
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.TimeDependentFlow
public import TauCeti.Geometry.Manifold.Flow.Periodic
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

At the stationary cylinder `u(s, t) = φ_{s₀, t}(x)` over a trajectory of the time-dependent
Hamiltonian flow `φ` of `G`, with `Ks = 0` and `Kt = G_t`, the linearization is the operator
`ξ ↦ ∇_s ξ + J(∇_t ξ - ∇_ξ X_{G_t})` on fields along `u` over `ℝ²`: the `∇J` term multiplies
`u_t - X_{G_t}(u)`, which vanishes along a trajectory. This operator is invariant under
translation in `s` when `J` is independent of `s`, and descends to the cylinder `ℝ × S¹` when `J`
and `G` are `1`-periodic in `t`; neither is assumed here. The covariant variational equation
`∇_t (dφ_{s₀, t} v) = ∇_{dφ_{s₀, t} v} X_{G_t}` of the flow
(`CovariantDerivative.alongCurve_mfderiv_timeDependentFlowOf`) therefore says that the
`s`-independent field `ξ(s, t) = dφ_{s₀, t} v` lies in its kernel, for every `v ∈ T_x M`, every
family `J` and every torsion-free connection
(`floerLinearization_mfderiv_timeDependentFlowOf`). Over a `1`-periodic
orbit of a `1`-periodic Hamiltonian, `ξ` is `1`-periodic in `t` when `v` is fixed by the
derivative of the time-one map (`TauCeti.mfderiv_timeDependentFlowOf_add_period_apply_of_eq`), and
it vanishes nowhere when `v ≠ 0`. So a degenerate orbit gives a nowhere-vanishing `C¹` kernel
field on `ℝ²` which is independent of `s` and `1`-periodic in `t`
(`exists_ne_zero_floerLinearization_eq_zero_of_not_isNondegenerateFixedPt`), the same field for
every family `J` and every torsion-free connection. This is the manifold counterpart of one
direction of the vector-space criterion
`TauCeti.SymplecticForm.isNondegenerateFixedPt_iff_forall_eq_zero_of_asymptoticOperator_eq_zero`,
where `TauCeti.SymplecticForm.floerLinearization_eq_stationaryCylinderOperator` identifies the
linearization at a stationary cylinder with the asymptotic operator.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Sections 3.1 and 8.1 (linearization and Hamiltonian perturbations).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2 (the linearized operator at a stationary solution and
  nondegenerate periodic orbits).
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

/-- **The `J`-direction derivative of the Floer operator.** Along the line `J + q Y` of
domain-dependent endomorphism fields, the intrinsic Floer operator is affine in `q`, with
derivative `Y(u)(∂t u - X_Kt)` in the tangent fibre at `u z`. -/
theorem hasDerivAt_floerOperator_add_smul (ω : SmoothTwoForm I M)
    (J Y : ℝ × ℝ → ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (Ks Kt : ℝ × ℝ → M → ℝ) (u : ℝ × ℝ → M) (z : ℝ × ℝ) (q : ℝ) :
    HasDerivAt (fun q : ℝ ↦ (ω.floerOperator (fun w x ↦ J w x + q • Y w x) Ks Kt u z : E))
      (Y z (u z) (curveVelocity I (fun t ↦ u (z.1, t)) z.2 -
        ω.hamiltonianVectorField (Kt z) (u z)) : E) q := by
  set ξ := curveVelocity I (fun t ↦ u (z.1, t)) z.2 - ω.hamiltonianVectorField (Kt z) (u z)
  have h (q : ℝ) : ω.floerOperator (fun w x ↦ J w x + q • Y w x) Ks Kt u z =
      ω.floerOperator J Ks Kt u z + q • Y z (u z) ξ := by
    simp only [floerOperator_def, _root_.add_apply, _root_.smul_apply, ξ]
    abel
  have hd := ((hasDerivAt_id q).smul_const (F := E) (Y z (u z) ξ : E)).const_add (F := E)
    (ω.floerOperator J Ks Kt u z : E)
  exact (hd.congr_deriv (one_smul ℝ (Y z (u z) ξ : E))).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun q ↦ h q)

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
    alongCurve_clm_apply cov γ _ (J z) hJ hΔt,
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

section StationaryCylinder

variable [T2Space M] [BoundarylessManifold I M]

/-- **The linearized flow lies in the kernel of the linearization at a stationary cylinder.** Let
`G` be a time-dependent Hamiltonian whose vector field `X_{G_t}` is jointly `C²`, with
time-dependent flow `φ`, and let `u(s, t) = φ_{s₀, t}(x)` be the stationary cylinder over the
trajectory of `x` from time `s₀`. For the cylindrical perturbation `Ks = 0`, `Kt = G_t`, every
family `J` and every torsion-free connection, the `s`-independent field `ξ(s, t) = dφ_{s₀, t} v`
is annihilated by the linearized Floer operator, at every point where the trajectory is defined.
-/
theorem floerLinearization_mfderiv_timeDependentFlowOf (ω : SmoothTwoForm I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) (htor : cov.IsTorsionFree)
    (J : ℝ × ℝ → ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x) {G : ℝ → M → ℝ}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, ω.hamiltonianVectorField (G p.1) p.2⟩ : TangentBundle I M)))
    {s₀ : ℝ} {x : M} (v : TangentSpace I x) {z : ℝ × ℝ}
    (h : ((s₀, z.2), x) ∈ timeDependentFlowDomain fun t ↦ ω.hamiltonianVectorField (G t)) :
    ω.floerLinearization cov J (fun _ _ ↦ 0) (fun w ↦ G w.2)
        (fun w ↦ timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (G t)) s₀ w.2 x)
        (fun w ↦ mfderiv I I
          (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (G t)) s₀ w.2) x v) z = 0 := by
  -- The stationary cylinder solves the field equation in `t`, so the `∇J` term drops out.
  rw [floerLinearization_def]
  dsimp only
  rw [curveVelocity_timeDependentFlowOf (hX.of_le (by norm_num)) h,
    alongCurve_mfderiv_timeDependentFlowOf (X := fun t ↦ ω.hamiltonianVectorField (G t)) cov
      htor hX h v, hamiltonianVectorField_const]
  simp only [CovariantDerivative.zero, sub_self, map_zero, zero_apply, sub_zero, add_zero,
    Pi.zero_apply]
  -- Along the constant curve in `s`, the field is constant, so its covariant derivative vanishes.
  exact alongCurve_const_const cov
    (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (G t)) s₀ z.2 x)
    (mfderiv I I (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (G t)) s₀ z.2) x v) z.1

/-- **A degenerate `1`-periodic orbit gives a periodic kernel element of the linearization.** Let
`G` be a `1`-periodic time-dependent Hamiltonian whose vector field is jointly `C²`, and let `x` be
a fixed point of the time-one map `φ_{s₀, s₀ + 1}`, with the flow from `(s₀, x)` defined at time
`s₀ + 1`, which is not nondegenerate. Along the stationary cylinder over the orbit of `x` there is
a nowhere-vanishing `C¹` field `ξ`, independent of `s` and `1`-periodic in `t`, which the
linearized Floer operator annihilates for every family `J` and every torsion-free connection.
`floerLinearization_mfderiv_timeDependentFlowOf` gives such a field explicitly, as the linearized
flow of a nonzero vector fixed by the derivative of the time-one map. -/
theorem exists_ne_zero_floerLinearization_eq_zero_of_not_isNondegenerateFixedPt
    (ω : SmoothTwoForm I M) {G : ℝ → M → ℝ} (hG : Function.Periodic G 1)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, ω.hamiltonianVectorField (G p.1) p.2⟩ : TangentBundle I M)))
    {s₀ : ℝ} {x : M}
    (h : ((s₀, s₀ + 1), x) ∈ timeDependentFlowDomain fun t ↦ ω.hamiltonianVectorField (G t))
    (hfix : Function.IsFixedPt
      (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (G t)) s₀ (s₀ + 1)) x)
    (hdeg : ¬IsNondegenerateFixedPt I
      (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (G t)) s₀ (s₀ + 1)) x) :
    ∃ ξ : ∀ z : ℝ × ℝ, TangentSpace I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (G t)) s₀ z.2 x),
      ContMDiff 𝓘(ℝ, ℝ × ℝ) I.tangent 1 (fun z ↦ TotalSpace.mk' E
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (G t)) s₀ z.2 x) (ξ z)) ∧
      (∀ z, ξ z ≠ 0) ∧ (∀ z a, ξ (a, z.2) = ξ z) ∧ (∀ z, ξ (z.1, z.2 + 1) = ξ z) ∧
      ∀ cov : CovariantDerivative I E (TangentSpace I : M → Type _), cov.IsTorsionFree →
        ∀ (J : ℝ × ℝ → ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x) z,
          ω.floerLinearization cov J (fun _ _ ↦ 0) (fun w ↦ G w.2)
            (fun w ↦ timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (G t)) s₀ w.2 x)
            ξ z = 0 := by
  have hX₁ := hX.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hper : Function.Periodic (fun t ↦ ω.hamiltonianVectorField (G t)) 1 := fun t ↦ by
    simp only [hG t]
  have hall (t : ℝ) := mem_timeDependentFlowDomain_of_isFixedPt hX₁ hper one_ne_zero h hfix t
  have hdiff : MDifferentiableAt I I
      (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (G t)) s₀ (s₀ + 1)) x :=
    (contMDiffAt_timeDependentFlowOf (n := 2) (by norm_num) hX
      h).mdifferentiableAt two_ne_zero
  -- Degeneracy provides a nonzero vector fixed by the derivative of the time-one map.
  obtain ⟨v, hv, hv0⟩ : ∃ v : TangentSpace I x, mfderiv I I
      (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (G t)) s₀ (s₀ + 1)) x v = v ∧
        v ≠ 0 := by
    simpa only [isNondegenerateFixedPt_iff, hfix, hdiff, true_and, not_forall,
      exists_prop] using hdeg
  refine ⟨fun w ↦ mfderiv I I
      (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (G t)) s₀ w.2) x v,
    fun z ↦ (contMDiffAt_totalSpaceMk_mfderiv_timeDependentFlowOf (m := 1) (n := 2)
      (by norm_num) (by norm_num) hX v (hall z.2)).comp z
        (contMDiff_iff_contDiff.mpr contDiff_snd).contMDiffAt,
    fun z hz ↦ hv0 (injective_mfderiv_timeDependentFlowOf hX₁ (hall z.2)
      (hz.trans (map_zero _).symm)), fun _ _ ↦ rfl,
    fun z ↦ mfderiv_timeDependentFlowOf_add_period_apply_of_eq hX₁ hper one_ne_zero h hfix hv z.2,
    fun cov htor J z ↦ floerLinearization_mfderiv_timeDependentFlowOf ω cov htor J hX v (hall z.2)⟩

end StationaryCylinder

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
