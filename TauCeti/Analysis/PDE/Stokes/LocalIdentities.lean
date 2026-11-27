/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.PDE.Stokes.Stress
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.FDeriv.Matrix

/-!
# Local work and reciprocity identities of Stokes flow

For a velocity field `u : (ι → ℝ) → ι → ℝ`, a pressure `p : (ι → ℝ) → ℝ` and a constant real
viscosity `μ` on the coordinate space `ι → ℝ`, this file defines

* the velocity gradient `(Du)ᵢⱼ = ∂ⱼ uᵢ` (`TauCeti.Stokes.velocityGradient`), the matrix of
  `fderiv ℝ u x` in the standard basis, whose trace is the divergence `div u`;
* the stress field `σ(u,p)(x) = -p(x) I + μ (Du(x) + Du(x)ᵀ)` (`TauCeti.Stokes.stress`);
* the row divergence `(Div σ)ᵢ = ∑ⱼ ∂ⱼ σᵢⱼ` of a matrix field (`TauCeti.Stokes.stressDivergence`),
  so that the momentum equation of steady Stokes flow with body force `f` reads
  `stressDivergence (stress μ u p) x + f x = 0`;
* the predicate `TauCeti.Stokes.IsStokesSolutionAt`, consisting of exactly the momentum equation
  and the incompressibility condition `div u = 0` at a point.

The velocity gradient, the stress and the row divergence are linear at points of
differentiability (`TauCeti.Stokes.velocityGradient_add`, `TauCeti.Stokes.stress_add`,
`TauCeti.Stokes.stressDivergence_add` and their `_sub` and `_const_smul` forms).

The main results are the pointwise identities behind the work–dissipation identity and the
Lorentz reciprocal theorem (Kim–Karrila, *Microhydrodynamics*, §2.2–2.3). For the work flux
`σ(u,p) v` of a stress against a comparison velocity `v`,

* `TauCeti.Stokes.trace_velocityGradient_stress_mulVec`:
  `div (σ(u,p) v) = v · Div σ(u,p) + 2μ e(u) : e(v) - p div v`;
* `TauCeti.Stokes.trace_velocityGradient_stress_mulVec_of_stressDivergence_add_eq_zero`: for a
  solution of the momentum equation with force `f`, `div (σ(u,p) v) = 2μ e(u) : e(v) - p div v -
  v · f`. The comparison field `v` only needs to be differentiable at the point and need not solve
  any equation.

For the reciprocal flux `J = σ(u,p) v - σ(v,q) u`,

* `TauCeti.Stokes.trace_velocityGradient_reciprocalFlux`:
  `div J = v · Div σ(u,p) - u · Div σ(v,q) - p div v + q div u`;
* `TauCeti.Stokes.trace_velocityGradient_reciprocalFlux_of_isStokesSolutionAt`: for two
  incompressible solutions with forces `f` and `g`, `div J = u · g - v · f`.

Here `e(A) = (A + Aᵀ)/2` is `TauCeti.PDE.coefficientSymmetricPart` and `A : B = tr (Aᵀ B)` is the
trace pairing. The single-flow identity and the zero-force specializations are recorded as
corollaries. All identities hold for every real `μ` and every finite index type. Only
pointwise differentiability is assumed: the velocities whose stress is differentiated are twice
differentiable at the point (`DifferentiableAt ℝ (fderiv ℝ u) x`), and the pressures are
differentiable there. Since the stress is symmetric, `σ v = σᵀ v`, so the work flux is the
flux `σᵀ v` whose normal component `v · σ n` is the work of the traction.

Finally, `TauCeti.Stokes.contDiffAt_stress_apply`, `TauCeti.Stokes.contDiffAt_stress_mulVec` and
`TauCeti.Stokes.contDiffAt_reciprocalFlux` give the regularity of the stress, the work flux and the
reciprocal flux from `C^{k+1}` velocities and `C^k` pressures, as needed to integrate these
identities; `TauCeti.Stokes.differentiableAt_stress_mulVec` and
`TauCeti.Stokes.differentiableAt_reciprocalFlux` are their pointwise differentiable counterparts.

## References

* Sangtae Kim and Seppo J. Karrila, *Microhydrodynamics: Principles and Selected Applications*,
  Butterworth–Heinemann, 1991, §1.2 and §2.2–2.3.
-/

public section

open Matrix TauCeti.PDE
open scoped Topology

namespace TauCeti.Stokes

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Velocity gradient, stress field and row divergence -/

/-- The velocity gradient `(Du)ᵢⱼ = ∂ⱼ uᵢ` of a vector field `u` at `x`: the matrix of the Fréchet
derivative `fderiv ℝ u x` in the standard basis. Its trace is the divergence `div u`. -/
noncomputable def velocityGradient (u : (ι → ℝ) → ι → ℝ) (x : ι → ℝ) : Matrix ι ι ℝ :=
  LinearMap.toMatrix' (fderiv ℝ u x : (ι → ℝ) →ₗ[ℝ] ι → ℝ)

@[simp]
theorem velocityGradient_apply (u : (ι → ℝ) → ι → ℝ) (x : ι → ℝ) (i j : ι) :
    velocityGradient u x i j = fderiv ℝ u x (Pi.single j 1) i := by
  simp [velocityGradient, LinearMap.toMatrix'_apply]

/-- At a point of differentiability, the entries of the velocity gradient are the partial
derivatives `∂ⱼ uᵢ` of the components of `u`. -/
theorem velocityGradient_apply_of_differentiableAt {u : (ι → ℝ) → ι → ℝ} {x : ι → ℝ}
    (hu : DifferentiableAt ℝ u x) (i j : ι) :
    velocityGradient u x i j = fderiv ℝ (fun y => u y i) x (Pi.single j 1) := by
  rw [velocityGradient_apply, fderiv_apply hu, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]

/-- The trace of the velocity gradient is the divergence `∑ᵢ ∂ᵢ uᵢ`, in the form used by
Mathlib's divergence theorem on a box. -/
theorem trace_velocityGradient_eq_sum (u : (ι → ℝ) → ι → ℝ) (x : ι → ℝ) :
    (velocityGradient u x).trace = ∑ i, fderiv ℝ u x (Pi.single i 1) i := by
  simp [Matrix.trace]

/-- The trace of the velocity gradient is the coordinate-free divergence, the trace of the
Fréchet derivative. -/
theorem trace_velocityGradient (u : (ι → ℝ) → ι → ℝ) (x : ι → ℝ) :
    (velocityGradient u x).trace = LinearMap.trace ℝ (ι → ℝ) (fderiv ℝ u x) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ ι), LinearMap.toMatrix_eq_toMatrix',
    velocityGradient]

/-- The velocity gradient at `x` only depends on the field near `x`. -/
theorem _root_.Filter.EventuallyEq.velocityGradient_eq {u v : (ι → ℝ) → ι → ℝ} {x : ι → ℝ}
    (h : u =ᶠ[𝓝 x] v) : velocityGradient u x = velocityGradient v x := by
  rw [velocityGradient, velocityGradient, h.fderiv_eq]

/-- Velocity fields that agree near `x` have velocity gradients that agree near `x`. -/
theorem _root_.Filter.EventuallyEq.velocityGradient {u v : (ι → ℝ) → ι → ℝ} {x : ι → ℝ}
    (h : u =ᶠ[𝓝 x] v) : velocityGradient u =ᶠ[𝓝 x] velocityGradient v :=
  h.eventuallyEq_nhds.mono fun _ hy => hy.velocityGradient_eq

/-- The velocity gradient is additive on fields differentiable at the point. -/
theorem velocityGradient_add {u v : (ι → ℝ) → ι → ℝ} {x : ι → ℝ} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) :
    velocityGradient (u + v) x = velocityGradient u x + velocityGradient v x := by
  rw [velocityGradient, velocityGradient, velocityGradient, fderiv_add hu hv,
    ContinuousLinearMap.toLinearMap_add, map_add]

/-- The velocity gradient commutes with subtraction of fields differentiable at the point. -/
theorem velocityGradient_sub {u v : (ι → ℝ) → ι → ℝ} {x : ι → ℝ} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) :
    velocityGradient (u - v) x = velocityGradient u x - velocityGradient v x := by
  rw [velocityGradient, velocityGradient, velocityGradient, fderiv_sub hu hv,
    ContinuousLinearMap.toLinearMap_sub, map_sub]

/-- The velocity gradient commutes with scaling a field differentiable at the point. -/
theorem velocityGradient_const_smul {u : (ι → ℝ) → ι → ℝ} {x : ι → ℝ}
    (hu : DifferentiableAt ℝ u x) (c : ℝ) :
    velocityGradient (c • u) x = c • velocityGradient u x := by
  rw [velocityGradient, velocityGradient, fderiv_const_smul hu c,
    ContinuousLinearMap.toLinearMap_smul, map_smul]

/-- The Newtonian stress field `σ(u,p)(x) = -p(x) I + μ (Du(x) + Du(x)ᵀ)` of a velocity `u` and a
pressure `p` with constant viscosity `μ`. -/
noncomputable def stress (μ : ℝ) (u : (ι → ℝ) → ι → ℝ) (p : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    Matrix ι ι ℝ :=
  newtonianStress μ (p x) (velocityGradient u x)

theorem stress_def (μ : ℝ) (u : (ι → ℝ) → ι → ℝ) (p : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    stress μ u p x = newtonianStress μ (p x) (velocityGradient u x) := (rfl)

@[simp]
theorem transpose_stress (μ : ℝ) (u : (ι → ℝ) → ι → ℝ) (p : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    (stress μ u p x)ᵀ = stress μ u p x :=
  transpose_newtonianStress μ (p x) _

/-- Velocities and pressures that agree near `x` have stress fields that agree near `x`. -/
theorem _root_.Filter.EventuallyEq.stress {u v : (ι → ℝ) → ι → ℝ} {p q : (ι → ℝ) → ℝ}
    {x : ι → ℝ} (hu : u =ᶠ[𝓝 x] v) (hp : p =ᶠ[𝓝 x] q) (μ : ℝ) :
    stress μ u p =ᶠ[𝓝 x] stress μ v q := by
  filter_upwards [hu.velocityGradient, hp] with y hy hpy
  rw [stress_def, stress_def, hy, hpy]

/-- The stress is additive in the pair `(u, p)` at a point where both velocities are
differentiable. -/
theorem stress_add (μ : ℝ) {u v : (ι → ℝ) → ι → ℝ} (p q : (ι → ℝ) → ℝ) {x : ι → ℝ}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    stress μ (u + v) (p + q) x = stress μ u p x + stress μ v q x := by
  rw [stress_def, stress_def, stress_def, velocityGradient_add hu hv, Pi.add_apply,
    newtonianStress_add]

/-- The stress commutes with subtraction in the pair `(u, p)` at a point where both velocities
are differentiable. -/
theorem stress_sub (μ : ℝ) {u v : (ι → ℝ) → ι → ℝ} (p q : (ι → ℝ) → ℝ) {x : ι → ℝ}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    stress μ (u - v) (p - q) x = stress μ u p x - stress μ v q x := by
  rw [stress_def, stress_def, stress_def, velocityGradient_sub hu hv, Pi.sub_apply]
  simp only [newtonianStress_def, transpose_sub]
  module

/-- The stress commutes with scaling the pair `(u, p)` at a point where the velocity is
differentiable. -/
theorem stress_const_smul (μ : ℝ) {u : (ι → ℝ) → ι → ℝ} (p : (ι → ℝ) → ℝ) {x : ι → ℝ}
    (hu : DifferentiableAt ℝ u x) (c : ℝ) :
    stress μ (c • u) (c • p) x = c • stress μ u p x := by
  rw [stress_def, stress_def, velocityGradient_const_smul hu c, Pi.smul_apply, smul_eq_mul,
    newtonianStress_smul]

/-- The row divergence `(Div σ)ᵢ = ∑ⱼ ∂ⱼ σᵢⱼ` of a matrix field `σ` at `x`. For the stress field
`σ(u,p)`, the momentum equation of steady Stokes flow with body force `f` is
`stressDivergence (stress μ u p) x + f x = 0`. -/
noncomputable def stressDivergence (σ : (ι → ℝ) → Matrix ι ι ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun i => ∑ j, fderiv ℝ (fun y => σ y i j) x (Pi.single j 1)

@[simp]
theorem stressDivergence_apply (σ : (ι → ℝ) → Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) :
    stressDivergence σ x i = ∑ j, fderiv ℝ (fun y => σ y i j) x (Pi.single j 1) := (rfl)

/-- The row divergence is additive on matrix fields whose entries are differentiable at `x`. -/
theorem stressDivergence_add {σ τ : (ι → ℝ) → Matrix ι ι ℝ} {x : ι → ℝ}
    (hσ : ∀ i j, DifferentiableAt ℝ (fun y => σ y i j) x)
    (hτ : ∀ i j, DifferentiableAt ℝ (fun y => τ y i j) x) :
    stressDivergence (σ + τ) x = stressDivergence σ x + stressDivergence τ x := by
  funext i
  simp only [stressDivergence_apply, Pi.add_apply, Matrix.add_apply, ← Finset.sum_add_distrib,
    fderiv_fun_add (hσ i _) (hτ i _), add_apply]

/-- The row divergence commutes with subtraction of matrix fields whose entries are
differentiable at `x`. -/
theorem stressDivergence_sub {σ τ : (ι → ℝ) → Matrix ι ι ℝ} {x : ι → ℝ}
    (hσ : ∀ i j, DifferentiableAt ℝ (fun y => σ y i j) x)
    (hτ : ∀ i j, DifferentiableAt ℝ (fun y => τ y i j) x) :
    stressDivergence (σ - τ) x = stressDivergence σ x - stressDivergence τ x := by
  funext i
  simp only [stressDivergence_apply, Pi.sub_apply, Matrix.sub_apply, ← Finset.sum_sub_distrib,
    fderiv_fun_sub (hσ i _) (hτ i _), sub_apply]

/-- The row divergence commutes with scaling a matrix field whose entries are differentiable at
`x`. -/
theorem stressDivergence_const_smul {σ : (ι → ℝ) → Matrix ι ι ℝ} {x : ι → ℝ}
    (hσ : ∀ i j, DifferentiableAt ℝ (fun y => σ y i j) x) (c : ℝ) :
    stressDivergence (c • σ) x = c • stressDivergence σ x := by
  funext i
  simp only [stressDivergence_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
    fderiv_const_mul (hσ i _) c, smul_apply, Finset.mul_sum]

/-- The row divergence at `x` only depends on the matrix field near `x`. -/
theorem _root_.Filter.EventuallyEq.stressDivergence_eq {σ τ : (ι → ℝ) → Matrix ι ι ℝ}
    {x : ι → ℝ} (h : σ =ᶠ[𝓝 x] τ) : stressDivergence σ x = stressDivergence τ x := by
  funext i
  refine Finset.sum_congr rfl fun j _ => ?_
  have hij : (fun y => σ y i j) =ᶠ[𝓝 x] fun y => τ y i j :=
    h.mono fun y hy => congrArg (fun M : Matrix ι ι ℝ => M i j) hy
  rw [hij.fderiv_eq]

/-- The incompressible steady Stokes equations at a point `x`, with viscosity `μ`, velocity `u`,
pressure `p` and body-force density `f`: the momentum equation `Div σ(u,p) + f = 0` and the
incompressibility condition `div u = 0`. -/
structure IsStokesSolutionAt (μ : ℝ) (u : (ι → ℝ) → ι → ℝ) (p : (ι → ℝ) → ℝ)
    (f : (ι → ℝ) → ι → ℝ) (x : ι → ℝ) : Prop where
  /-- The momentum equation `Div σ(u,p) + f = 0` at `x`. -/
  stressDivergence_add_eq_zero : stressDivergence (stress μ u p) x + f x = 0
  /-- The incompressibility condition `div u = 0` at `x`. -/
  trace_velocityGradient_eq_zero : (velocityGradient u x).trace = 0

/-! ### Regularity of the stress and the work flux -/

/-- The entries of the velocity gradient of a velocity that is twice differentiable at `x` are
differentiable at `x`. -/
theorem differentiableAt_velocityGradient_apply {u : (ι → ℝ) → ι → ℝ} {x : ι → ℝ}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) (i j : ι) :
    DifferentiableAt ℝ (fun y => velocityGradient u y i j) x := by
  simp only [velocityGradient_apply]
  exact differentiableAt_pi.1 (hu.clm_apply (differentiableAt_const _)) i

/-- The entries of the stress are differentiable at `x` when the velocity is twice differentiable
and the pressure is differentiable at `x`. -/
theorem differentiableAt_stress_apply (μ : ℝ) {u : (ι → ℝ) → ι → ℝ} {p : (ι → ℝ) → ℝ}
    {x : ι → ℝ} (hu : DifferentiableAt ℝ (fderiv ℝ u) x) (hp : DifferentiableAt ℝ p x)
    (i j : ι) : DifferentiableAt ℝ (fun y => stress μ u p y i j) x := by
  simp only [stress_def, newtonianStress_apply]
  refine ((differentiableAt_velocityGradient_apply hu i j).add
    (differentiableAt_velocityGradient_apply hu j i)).const_mul μ |>.sub ?_
  split_ifs
  · exact hp
  · exact differentiableAt_const _

/-- The entries of the velocity gradient of a `C^{k+1}` velocity are `C^k`. -/
theorem contDiffAt_velocityGradient_apply {k : WithTop ℕ∞} {u : (ι → ℝ) → ι → ℝ} {x : ι → ℝ}
    (hu : ContDiffAt ℝ (k + 1) u x) (i j : ι) :
    ContDiffAt ℝ k (fun y => velocityGradient u y i j) x := by
  simp only [velocityGradient_apply]
  exact contDiffAt_pi.1 ((hu.fderiv_right le_rfl).clm_apply contDiffAt_const) i

/-- The entries of the stress of a `C^{k+1}` velocity and a `C^k` pressure are `C^k`. -/
theorem contDiffAt_stress_apply (μ : ℝ) {k : WithTop ℕ∞} {u : (ι → ℝ) → ι → ℝ}
    {p : (ι → ℝ) → ℝ} {x : ι → ℝ} (hu : ContDiffAt ℝ (k + 1) u x) (hp : ContDiffAt ℝ k p x)
    (i j : ι) : ContDiffAt ℝ k (fun y => stress μ u p y i j) x := by
  simp only [stress_def, newtonianStress_apply]
  refine (contDiffAt_const.mul ((contDiffAt_velocityGradient_apply hu i j).add
    (contDiffAt_velocityGradient_apply hu j i))).sub ?_
  split_ifs
  · exact hp
  · exact contDiffAt_const

/-- The work flux `σ(u,p) v` of a `C^{k+1}` velocity `u` and a `C^k` pressure `p` against a `C^k`
velocity `v` is `C^k`. -/
theorem contDiffAt_stress_mulVec (μ : ℝ) {k : WithTop ℕ∞} {u v : (ι → ℝ) → ι → ℝ}
    {p : (ι → ℝ) → ℝ} {x : ι → ℝ} (hu : ContDiffAt ℝ (k + 1) u x) (hp : ContDiffAt ℝ k p x)
    (hv : ContDiffAt ℝ k v x) : ContDiffAt ℝ k (fun y => stress μ u p y *ᵥ v y) x := by
  refine contDiffAt_pi.2 fun i => ?_
  simp only [mulVec, dotProduct]
  exact ContDiffAt.sum fun j _ =>
    (contDiffAt_stress_apply μ hu hp i j).mul (contDiffAt_pi.1 hv j)

/-- The work flux `σ(u,p) v` is differentiable at `x` when the velocity `u` is twice
differentiable and the pressure `p` and the velocity `v` are differentiable at `x`. -/
theorem differentiableAt_stress_mulVec (μ : ℝ) {u v : (ι → ℝ) → ι → ℝ} {p : (ι → ℝ) → ℝ}
    {x : ι → ℝ} (hu : DifferentiableAt ℝ (fderiv ℝ u) x) (hp : DifferentiableAt ℝ p x)
    (hv : DifferentiableAt ℝ v x) : DifferentiableAt ℝ (fun y => stress μ u p y *ᵥ v y) x := by
  simpa only [mulVecCLM_apply] using
    (differentiableAt_mulVecCLM (differentiableAt_stress_apply μ hu hp)).clm_apply hv

/-! ### The product rule for the divergence of a matrix times a vector -/

/-- The divergence of `A v`, for a differentiable matrix field `A` and vector field `v`, is
`tr (A Dv) + v · Div Aᵀ`. -/
theorem trace_velocityGradient_mulVec {A : (ι → ℝ) → Matrix ι ι ℝ} {v : (ι → ℝ) → ι → ℝ}
    {x : ι → ℝ} (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (hv : DifferentiableAt ℝ v x) :
    (velocityGradient (fun y => A y *ᵥ v y) x).trace =
      (A x * velocityGradient v x).trace + v x ⬝ᵥ stressDivergence (fun y => (A y)ᵀ) x := by
  have hv' : ∀ j, DifferentiableAt ℝ (fun y => v y j) x := differentiableAt_pi.1 hv
  have hAv : DifferentiableAt ℝ (fun y => A y *ᵥ v y) x := by
    simpa only [mulVecCLM_apply] using (differentiableAt_mulVecCLM hA).clm_apply hv
  have hDv : Matrix.of (fun j i => fderiv ℝ (fun y => v y j) x (Pi.single i 1)) =
      velocityGradient v x := by
    ext j i
    rw [velocityGradient_apply_of_differentiableAt hv, Matrix.of_apply]
  have h := Matrix.sum_fderiv_mulVec_eq_trace_add A v (fun i => Pi.single i 1) x hA hv'
  rw [hDv] at h
  rw [Matrix.trace]
  simp only [diag_apply, velocityGradient_apply_of_differentiableAt hAv]
  rw [h]
  simp only [dotProduct, stressDivergence_apply, transpose_apply]

/-! ### The pairing identity for the work flux -/

/-- **Pairing identity.** The divergence of the work flux `σ(u,p) v` of the stress of `(u,p)`
against a velocity `v` is `v · Div σ(u,p) + 2μ e(u) : e(v) - p div v`. The velocity `u` is twice
differentiable at `x`, the pressure `p` and the comparison velocity `v` are differentiable at `x`,
and no equation is assumed. -/
theorem trace_velocityGradient_stress_mulVec (μ : ℝ) {u v : (ι → ℝ) → ι → ℝ}
    {p : (ι → ℝ) → ℝ} {x : ι → ℝ} (hu : DifferentiableAt ℝ (fderiv ℝ u) x)
    (hp : DifferentiableAt ℝ p x) (hv : DifferentiableAt ℝ v x) :
    (velocityGradient (fun y => stress μ u p y *ᵥ v y) x).trace =
      v x ⬝ᵥ stressDivergence (stress μ u p) x +
        2 * μ * ((coefficientSymmetricPart (velocityGradient u x))ᵀ *
          coefficientSymmetricPart (velocityGradient v x)).trace -
        p x * (velocityGradient v x).trace := by
  rw [trace_velocityGradient_mulVec (differentiableAt_stress_apply μ hu hp) hv]
  simp only [transpose_stress]
  rw [← transpose_stress μ u p x, stress_def, trace_transpose_newtonianStress_mul]
  ring

/-- The pairing identity for a solution of the momentum equation `Div σ(u,p) + f = 0` at `x`:
`div (σ(u,p) v) = 2μ e(u) : e(v) - p div v - v · f`, for any comparison velocity `v` that is
differentiable at `x`. Neither field is assumed incompressible. -/
theorem trace_velocityGradient_stress_mulVec_of_stressDivergence_add_eq_zero (μ : ℝ)
    {u v f : (ι → ℝ) → ι → ℝ} {p : (ι → ℝ) → ℝ} {x : ι → ℝ}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) (hp : DifferentiableAt ℝ p x)
    (hv : DifferentiableAt ℝ v x) (huf : stressDivergence (stress μ u p) x + f x = 0) :
    (velocityGradient (fun y => stress μ u p y *ᵥ v y) x).trace =
      2 * μ * ((coefficientSymmetricPart (velocityGradient u x))ᵀ *
          coefficientSymmetricPart (velocityGradient v x)).trace -
        p x * (velocityGradient v x).trace - v x ⬝ᵥ f x := by
  rw [trace_velocityGradient_stress_mulVec μ hu hp hv, eq_neg_of_add_eq_zero_left huf,
    dotProduct_neg]
  ring

/-- **Single-flow identity.** For a solution of the momentum equation `Div σ(u,p) + f = 0` at `x`,
`div (σ(u,p) u) = 2μ e(u) : e(u) - p div u - u · f`. -/
theorem trace_velocityGradient_stress_mulVec_self (μ : ℝ) {u f : (ι → ℝ) → ι → ℝ}
    {p : (ι → ℝ) → ℝ} {x : ι → ℝ} (hu₁ : DifferentiableAt ℝ u x)
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) (hp : DifferentiableAt ℝ p x)
    (huf : stressDivergence (stress μ u p) x + f x = 0) :
    (velocityGradient (fun y => stress μ u p y *ᵥ u y) x).trace =
      2 * μ * ((coefficientSymmetricPart (velocityGradient u x))ᵀ *
          coefficientSymmetricPart (velocityGradient u x)).trace -
        p x * (velocityGradient u x).trace - u x ⬝ᵥ f x :=
  trace_velocityGradient_stress_mulVec_of_stressDivergence_add_eq_zero μ hu hp hu₁ huf

/-- **Single-flow identity, incompressible case.** For an incompressible solution with force `f`
at `x`, `div (σ(u,p) u) = 2μ e(u) : e(u) - u · f`. -/
theorem IsStokesSolutionAt.trace_velocityGradient_stress_mulVec_self {μ : ℝ}
    {u f : (ι → ℝ) → ι → ℝ} {p : (ι → ℝ) → ℝ} {x : ι → ℝ} (h : IsStokesSolutionAt μ u p f x)
    (hu₁ : DifferentiableAt ℝ u x) (hu : DifferentiableAt ℝ (fderiv ℝ u) x)
    (hp : DifferentiableAt ℝ p x) :
    (velocityGradient (fun y => stress μ u p y *ᵥ u y) x).trace =
      2 * μ * ((coefficientSymmetricPart (velocityGradient u x))ᵀ *
          coefficientSymmetricPart (velocityGradient u x)).trace - u x ⬝ᵥ f x := by
  rw [_root_.TauCeti.Stokes.trace_velocityGradient_stress_mulVec_self μ hu₁ hu hp
      h.stressDivergence_add_eq_zero,
    h.trace_velocityGradient_eq_zero, mul_zero, sub_zero]

/-- **Local dissipation.** For an incompressible solution with zero body force at `x`,
`div (σ(u,p) u) = 2μ e(u) : e(u)`. -/
theorem IsStokesSolutionAt.trace_velocityGradient_stress_mulVec_self_of_force_eq_zero {μ : ℝ}
    {u : (ι → ℝ) → ι → ℝ} {p : (ι → ℝ) → ℝ} {x : ι → ℝ} (h : IsStokesSolutionAt μ u p 0 x)
    (hu₁ : DifferentiableAt ℝ u x) (hu : DifferentiableAt ℝ (fderiv ℝ u) x)
    (hp : DifferentiableAt ℝ p x) :
    (velocityGradient (fun y => stress μ u p y *ᵥ u y) x).trace =
      2 * μ * ((coefficientSymmetricPart (velocityGradient u x))ᵀ *
          coefficientSymmetricPart (velocityGradient u x)).trace := by
  rw [h.trace_velocityGradient_stress_mulVec_self hu₁ hu hp, Pi.zero_apply, dotProduct_zero,
    sub_zero]

/-! ### The reciprocal flux -/

/-- The reciprocal flux `J = σ(u,p) v - σ(v,q) u` of two flows `(u,p)` and `(v,q)` with the same
viscosity `μ`. Since the stress is symmetric, this is `σ(u,p)ᵀ v - σ(v,q)ᵀ u`, and its normal
component `J · n = v · σ(u,p) n - u · σ(v,q) n` is the difference of the reciprocal tractions'
works (`TauCeti.Stokes.reciprocalFlux_dotProduct`). -/
noncomputable def reciprocalFlux (μ : ℝ) (u : (ι → ℝ) → ι → ℝ) (p : (ι → ℝ) → ℝ)
    (v : (ι → ℝ) → ι → ℝ) (q : (ι → ℝ) → ℝ) (x : ι → ℝ) : ι → ℝ :=
  stress μ u p x *ᵥ v x - stress μ v q x *ᵥ u x

theorem reciprocalFlux_def (μ : ℝ) (u : (ι → ℝ) → ι → ℝ) (p : (ι → ℝ) → ℝ)
    (v : (ι → ℝ) → ι → ℝ) (q : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    reciprocalFlux μ u p v q x = stress μ u p x *ᵥ v x - stress μ v q x *ᵥ u x := (rfl)

/-- The reciprocal flux is the difference of the work fluxes `σ(u,p) v` and `σ(v,q) u`, as
functions. -/
theorem reciprocalFlux_eq_sub (μ : ℝ) (u : (ι → ℝ) → ι → ℝ) (p : (ι → ℝ) → ℝ)
    (v : (ι → ℝ) → ι → ℝ) (q : (ι → ℝ) → ℝ) :
    reciprocalFlux μ u p v q =
      (fun y => stress μ u p y *ᵥ v y) - fun y => stress μ v q y *ᵥ u y :=
  funext fun y => by rw [reciprocalFlux_def, Pi.sub_apply]

/-- The reciprocal flux is differentiable at `x` when the velocities are twice differentiable and
the pressures are differentiable at `x`. -/
theorem differentiableAt_reciprocalFlux (μ : ℝ) {u v : (ι → ℝ) → ι → ℝ} {p q : (ι → ℝ) → ℝ}
    {x : ι → ℝ} (hu₁ : DifferentiableAt ℝ u x) (hv₁ : DifferentiableAt ℝ v x)
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) (hv : DifferentiableAt ℝ (fderiv ℝ v) x)
    (hp : DifferentiableAt ℝ p x) (hq : DifferentiableAt ℝ q x) :
    DifferentiableAt ℝ (reciprocalFlux μ u p v q) x := by
  rw [reciprocalFlux_eq_sub]
  exact (differentiableAt_stress_mulVec μ hu hp hv₁).sub
    (differentiableAt_stress_mulVec μ hv hq hu₁)

/-- The reciprocal flux of `C^{k+1}` velocities and `C^k` pressures is `C^k`. -/
theorem contDiffAt_reciprocalFlux (μ : ℝ) {k : WithTop ℕ∞} {u v : (ι → ℝ) → ι → ℝ}
    {p q : (ι → ℝ) → ℝ} {x : ι → ℝ} (hu : ContDiffAt ℝ (k + 1) u x)
    (hv : ContDiffAt ℝ (k + 1) v x) (hp : ContDiffAt ℝ k p x) (hq : ContDiffAt ℝ k q x) :
    ContDiffAt ℝ k (reciprocalFlux μ u p v q) x := by
  rw [reciprocalFlux_eq_sub]
  exact (contDiffAt_stress_mulVec μ hu hp (hv.of_le le_self_add)).sub
    (contDiffAt_stress_mulVec μ hv hq (hu.of_le le_self_add))

/-- The normal component of the reciprocal flux is the difference of the works
`v · σ(u,p) n - u · σ(v,q) n` of the two tractions on a surface with normal `n`. -/
theorem reciprocalFlux_dotProduct (μ : ℝ) (u : (ι → ℝ) → ι → ℝ) (p : (ι → ℝ) → ℝ)
    (v : (ι → ℝ) → ι → ℝ) (q : (ι → ℝ) → ℝ) (x ν : ι → ℝ) :
    reciprocalFlux μ u p v q x ⬝ᵥ ν =
      v x ⬝ᵥ (stress μ u p x *ᵥ ν) - u x ⬝ᵥ (stress μ v q x *ᵥ ν) := by
  simp only [reciprocalFlux_def, sub_dotProduct, dotProduct_mulVec, ← mulVec_transpose,
    transpose_stress]

/-- **Reciprocal flux identity.** For velocities `u`, `v` twice differentiable at `x` and
pressures `p`, `q` differentiable at `x`,
`div J = v · Div σ(u,p) - u · Div σ(v,q) - p div v + q div u`. No equation is assumed. -/
theorem trace_velocityGradient_reciprocalFlux (μ : ℝ) {u v : (ι → ℝ) → ι → ℝ}
    {p q : (ι → ℝ) → ℝ} {x : ι → ℝ} (hu₁ : DifferentiableAt ℝ u x)
    (hv₁ : DifferentiableAt ℝ v x) (hu : DifferentiableAt ℝ (fderiv ℝ u) x)
    (hv : DifferentiableAt ℝ (fderiv ℝ v) x) (hp : DifferentiableAt ℝ p x)
    (hq : DifferentiableAt ℝ q x) :
    (velocityGradient (reciprocalFlux μ u p v q) x).trace =
      v x ⬝ᵥ stressDivergence (stress μ u p) x - u x ⬝ᵥ stressDivergence (stress μ v q) x -
        p x * (velocityGradient v x).trace + q x * (velocityGradient u x).trace := by
  rw [reciprocalFlux_eq_sub, velocityGradient_sub (differentiableAt_stress_mulVec μ hu hp hv₁)
      (differentiableAt_stress_mulVec μ hv hq hu₁), trace_sub,
    trace_velocityGradient_mulVec (differentiableAt_stress_apply μ hu hp) hv₁,
    trace_velocityGradient_mulVec (differentiableAt_stress_apply μ hv hq) hu₁]
  simp only [transpose_stress]
  rw [← transpose_stress μ u p x, ← transpose_stress μ v q x, stress_def, stress_def]
  have h := trace_transpose_newtonianStress_mul_sub μ (p x) (q x) (velocityGradient u x)
    (velocityGradient v x)
  linear_combination h

/-- **Local reciprocity.** For incompressible solutions `(u,p)` with force `f` and `(v,q)` with
force `g` at `x`, of the Stokes equations with the same viscosity `μ`, the reciprocal flux
satisfies `div J = u · g - v · f`. -/
theorem trace_velocityGradient_reciprocalFlux_of_isStokesSolutionAt {μ : ℝ}
    {u v f g : (ι → ℝ) → ι → ℝ} {p q : (ι → ℝ) → ℝ} {x : ι → ℝ}
    (huf : IsStokesSolutionAt μ u p f x) (hvg : IsStokesSolutionAt μ v q g x)
    (hu₁ : DifferentiableAt ℝ u x) (hv₁ : DifferentiableAt ℝ v x)
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) (hv : DifferentiableAt ℝ (fderiv ℝ v) x)
    (hp : DifferentiableAt ℝ p x) (hq : DifferentiableAt ℝ q x) :
    (velocityGradient (reciprocalFlux μ u p v q) x).trace = u x ⬝ᵥ g x - v x ⬝ᵥ f x := by
  rw [trace_velocityGradient_reciprocalFlux μ hu₁ hv₁ hu hv hp hq,
    eq_neg_of_add_eq_zero_left huf.stressDivergence_add_eq_zero,
    eq_neg_of_add_eq_zero_left hvg.stressDivergence_add_eq_zero,
    huf.trace_velocityGradient_eq_zero, hvg.trace_velocityGradient_eq_zero,
    dotProduct_neg, dotProduct_neg]
  ring

/-- **Local reciprocity, zero-force case.** The reciprocal flux of two incompressible solutions
with zero body force at `x` is divergence free there. -/
theorem trace_velocityGradient_reciprocalFlux_eq_zero {μ : ℝ} {u v : (ι → ℝ) → ι → ℝ}
    {p q : (ι → ℝ) → ℝ} {x : ι → ℝ} (hu₀ : IsStokesSolutionAt μ u p 0 x)
    (hv₀ : IsStokesSolutionAt μ v q 0 x) (hu₁ : DifferentiableAt ℝ u x)
    (hv₁ : DifferentiableAt ℝ v x) (hu : DifferentiableAt ℝ (fderiv ℝ u) x)
    (hv : DifferentiableAt ℝ (fderiv ℝ v) x) (hp : DifferentiableAt ℝ p x)
    (hq : DifferentiableAt ℝ q x) :
    (velocityGradient (reciprocalFlux μ u p v q) x).trace = 0 := by
  rw [trace_velocityGradient_reciprocalFlux_of_isStokesSolutionAt hu₀ hv₀ hu₁ hv₁ hu hv hp hq]
  simp

end TauCeti.Stokes
