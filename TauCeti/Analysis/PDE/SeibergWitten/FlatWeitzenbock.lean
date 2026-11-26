/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
public import TauCeti.Analysis.PDE.SeibergWitten.SelfDualSplitting
public import TauCeti.LinearAlgebra.CliffordAlgebra.Module.Pairing
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.InnerProductSpace.HodgeStar.Isometry
import TauCeti.Analysis.InnerProductSpace.Laplacian.LocalExtr
import TauCeti.Analysis.InnerProductSpace.SquaredDistance
import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.OrthonormalBasis
import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Basic

/-!
# The flat Weitzenböck formula for the Seiberg–Witten Dirac operator

Let `V` be a finite-dimensional real inner product space and `W` a Hermitian Clifford module,
`c(v) = ρ (ι Q v)` with `Q v = -‖v‖²`. A spinor field `ψ : V → W` and a real one-form `b` on `V`,
the imaginary connection form `a = i b` of a line, give the covariant derivative and the Dirac
operator

`∇_v ψ = dψ(v) + i b(v) ψ`  (`TauCeti.SeibergWitten.covariantDeriv`),
`D ψ = ∑ₖ c(eₖ) ∇_{eₖ} ψ`  (`flatDirac`),

for any orthonormal basis `(eₖ)` (`flatDirac_eq_sum`). Without a basis, `D ψ` is the metric
trace of the Clifford pairing `(v, w) ↦ c(v) ∇_w ψ` (`AlgHom.cliffordPairing`, `flatDirac_def`).
This is the Dirac operator of the twisted spinors on a flat chart in which the background
connection is trivial. For `ψ = α u₀` with `u₀` constant it is the operator of the flat limiting
equations of `TauCeti.Analysis.PDE.SeibergWitten.FlatLimit` (`flatDirac_smul_const`). The operator
is additive in fields differentiable at the point (`flatDirac_add`) and affine in the connection,
`D_{b + b'} ψ = D_b ψ + i c(b') ψ` (`flatDirac_add_connection`), where the Clifford multiplication
`i c(b') φ` is the flat Dirac operator of the constant field `φ` for the connection `b'`
(`flatDirac_const_eq_smul_ι`); it has norm `‖b'‖ ‖φ‖` (`norm_flatDirac_const`) and is
locally Lipschitz in `(b', φ)` (`norm_flatDirac_const_sub_flatDirac_const_le`). Since the `c(eₖ)`
satisfy the Clifford relations and the commutator of covariant derivatives is the
curvature, `∇_v ∇_w ψ - ∇_w ∇_v ψ = i db(v, w) ψ` (`covariantDeriv_sub_swap`), the square of `D` is

`D (D ψ) = -∑ₖ ∇_{eₖ} ∇_{eₖ} ψ + i c₂(db) ψ`

(`flatDirac_flatDirac`, the **Weitzenböck formula**), where `c₂` is the Clifford action
`CliffordAlgebra.bivectorExterior` of two-vectors and `db` is read as a two-vector through the
inner product. Pairing with `ψ` turns the rough Laplacian into the Laplacian of `|ψ|²`,

`Δ |ψ|² / 2 = Re ⟪ψ, ∑ₖ ∇_{eₖ} ∇_{eₖ} ψ⟫ + ∑ₖ |∇_{eₖ} ψ|²`

(`laplacian_norm_sq_eq`), with `Δ = div ∘ grad`. On the positive half-spinors of an oriented
four-space the Clifford action of `db` pairs with `ψ` through the quadratic two-form `q`,
`Re ⟪ψ, i c₂(db) ψ⟫ = 4 ⟪q(ψ), db⟫` (`TauCeti.SeibergWitten.inner_quadraticTwoForm_eq_re_inner`),
so a solution of the Dirac equation `D ψ = 0` taking a value in `W⁺` at `x` satisfies, at `x`,

`Δ |ψ|² / 2 = ∑ₖ |∇_{eₖ} ψ|² + 4 ⟪q(ψ), db⟫`

(`laplacian_norm_sq_eq_of_flatDirac_eq_zero`).

For Taubes's large-parameter equations, with real curvature `F = i F_a = -db` as in
`TauCeti.Analysis.PDE.SeibergWitten.LargeParameterCurvature`, the curvature equation for the
normalized spinor `χ = Ψ / √r` reads `F + ⋆F = (r / 4) ω - r q(χ) - η`, where `ω` is the
symplectic form, self-dual of norm `√2`, and `η` is a perturbation. Since
`C(i ω) = 2 (P_α - P_β)` and `C(i q(χ)) χ = |χ|² χ / 2`, the Weitzenböck formula becomes the
forced equation

`∇*∇ χ + (r / 4) (|χ|² - 1) χ + (r / 2) P_β χ + C(i η) χ / 2 = 0`

(`sum_covariantDeriv_eq_of_add_hodgeStar_eq`), the flat form of the equation assumed in
`CovariantDerivative.IsMetricCompatible.norm_sq_le_max_of_roughLaplacian_add_eq_zero`. Pairing
with `χ`, `⟪q(χ), ω⟫ = (|P_α χ|² - |P_β χ|²) / 2` and `|q(χ)|² = |χ|⁴ / 8` give **Taubes's
identity**

`Δ |χ|² / 2 = ∑ₖ |∇_{eₖ} χ|² + (r / 4) (|χ|⁴ - |P_α χ|² + |P_β χ|²) + 2 ⟪q(χ), η⟫`

(`laplacian_norm_sq_eq_of_add_hodgeStar_eq`). Writing `χ = α u₀ + β`, the potential is
`(r / 4) (|χ|² - 1) |χ|² + (r / 2) |β|²`. At a local maximum of `|χ|²` the left side is
nonpositive, which gives the pointwise inequality

`|χ|² ≤ 1 + 2 √2 |η| / r`

at that point (`norm_sq_le_one_add_of_isLocalMax`), the key step of Taubes's coarse bound
`|α|² + |β|² ≤ 1 + C / r`. The coarse bound itself follows by the maximum principle on a
compact manifold, which this file does not provide. For the flat limiting equations,
`r = 1 / 2` and `η = 0`, so `|χ| ≤ 1` at every local maximum of `|χ|`. On a manifold the same
computation acquires the scalar curvature, the curvature of the canonical connection `A₀` and
the derivatives of `u₀`; here the chart is flat and these terms are absent.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Chapter II, §8 (the Bochner–Weitzenböck formula for Dirac operators).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, Chapter 5.
* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 2.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open CliffordAlgebra Module Complex
open InnerProductSpace Laplacian Filter
open scoped RealInnerProductSpace InnerProductSpace Topology

section CovariantDeriv

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {b : V → V [⋀^Fin 1]→L[ℝ] ℝ} {ψ : V → W} {x : V}

/-! ### The covariant derivative -/

/-- The covariant derivative of `α u₀` for a constant spinor `u₀` is `(∇_a α) u₀`. -/
theorem covariantDeriv_smul_const {α : V → ℂ} (hα : DifferentiableAt ℝ α x) (u₀ : W)
    (v : V) :
    covariantDeriv b (fun y ↦ α y • u₀) x v = covariantDeriv b α x v • u₀ := by
  rw [covariantDeriv_apply, fderiv_smul_const hα, covariantDeriv_apply]
  simp only [ContinuousLinearMap.smulRight_apply, add_smul, smul_assoc]

/-! ### Second covariant derivatives and the curvature -/

/-- The second covariant derivative `∇_v ∇_w ψ` of a spinor field, expanded: the second derivative
of `ψ`, the derivative of `b`, the mixed terms and the quadratic term in `b`. -/
theorem covariantDeriv_covariantDeriv_apply (hψ : DifferentiableAt ℝ ψ x)
    (hψ' : DifferentiableAt ℝ (fderiv ℝ ψ) x) (hb : DifferentiableAt ℝ b x) (v w : V) :
    covariantDeriv b (fun y ↦ covariantDeriv b ψ y w) x v =
      fderiv ℝ (fderiv ℝ ψ) x v w + fderiv ℝ (fun y ↦ b y fun _ ↦ w) x v • I • ψ x +
        b x (fun _ ↦ w) • I • fderiv ℝ ψ x v + b x (fun _ ↦ v) • I • fderiv ℝ ψ x w -
        (b x (fun _ ↦ v) * b x (fun _ ↦ w)) • ψ x := by
  have hbw : HasFDerivAt (fun y ↦ b y fun _ ↦ w) (fderiv ℝ (fun y ↦ b y fun _ ↦ w) x) x :=
    (hb.hasFDerivAt.continuousAlternatingMap_apply_const _).differentiableAt.hasFDerivAt
  have H : HasFDerivAt (fun y ↦ fderiv ℝ ψ y w + b y (fun _ ↦ w) • I • ψ y) _ x :=
    (hψ'.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).add
      (hbw.smul (hψ.hasFDerivAt.const_smul I))
  simp only [covariantDeriv_apply]
  rw [H.fderiv]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply, _root_.zero_apply,
    ContinuousLinearMap.flip_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
    _root_.map_zero, zero_add, smul_add, I_smul_smul_I_smul]
  module

/-- **The curvature of the covariant derivative**: for a `C²` spinor field and a differentiable
connection form, `∇_v ∇_w ψ - ∇_w ∇_v ψ = db(v, w) i ψ`. -/
theorem covariantDeriv_sub_swap (hψ : ContDiffAt ℝ 2 ψ x) (hb : DifferentiableAt ℝ b x)
    (v w : V) :
    covariantDeriv b (fun y ↦ covariantDeriv b ψ y w) x v -
        covariantDeriv b (fun y ↦ covariantDeriv b ψ y v) x w =
      extDeriv b x ![v, w] • I • ψ x := by
  have hψ₁ : DifferentiableAt ℝ ψ x := hψ.differentiableAt (by norm_num)
  have hψ₂ : DifferentiableAt ℝ (fderiv ℝ ψ) x :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [covariantDeriv_covariantDeriv_apply hψ₁ hψ₂ hb,
    covariantDeriv_covariantDeriv_apply hψ₁ hψ₂ hb,
    extDeriv_apply_pair_of_differentiableAt hb, hψ.isSymmSndFDerivAt (by simp) v w]
  module

/-- The covariant derivative of a field whose derivative is differentiable at `x` is
differentiable at `x`, for a connection form differentiable at `x`. -/
theorem differentiableAt_covariantDeriv_apply (hψ : DifferentiableAt ℝ ψ x)
    (hψ' : DifferentiableAt ℝ (fderiv ℝ ψ) x) (hb : DifferentiableAt ℝ b x) (w : V) :
    DifferentiableAt ℝ (fun y ↦ covariantDeriv b ψ y w) x := by
  simp only [covariantDeriv_apply]
  exact (hψ'.clm_apply (differentiableAt_const w)).add
    ((hb.hasFDerivAt.continuousAlternatingMap_apply_const _).differentiableAt.smul
      (hψ.const_smul I))

/-- The covariant derivative commutes with constant complex-linear maps and with finite sums:
`∇_v (∑ₖ fₖ gₖ) = ∑ₖ fₖ (∇_v gₖ)`. -/
theorem covariantDeriv_sum_apply [FiniteDimensional ℂ W] {κ : Type*} [Fintype κ]
    (f : κ → Module.End ℂ W)
    {g : κ → V → W} (hg : ∀ k, DifferentiableAt ℝ (g k) x) (v : V) :
    covariantDeriv b (fun y ↦ ∑ k, f k (g k y)) x v =
      ∑ k, f k (covariantDeriv b (g k) x v) := by
  have H : HasFDerivAt (fun y ↦ ∑ k, f k (g k y))
      (∑ k, ((f k).restrictScalars ℝ).toContinuousLinearMap.comp (fderiv ℝ (g k) x)) x :=
    HasFDerivAt.fun_sum fun k _ ↦
      ((f k).restrictScalars ℝ).toContinuousLinearMap.hasFDerivAt.comp x (hg k).hasFDerivAt
  rw [covariantDeriv_apply, H.fderiv]
  simp [Finset.smul_sum, ← Finset.sum_add_distrib, map_smul, LinearMap.map_smul_of_tower]

/-- The covariant derivative of a field vanishing near `x` vanishes at `x`. -/
theorem covariantDeriv_eq_zero_of_eventuallyEq {φ : V → W} (h : φ =ᶠ[𝓝 x] 0) :
    covariantDeriv b φ x = 0 := by
  ext v
  simp [covariantDeriv_apply, h.fderiv_eq, h.eq_of_nhds]

end CovariantDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Q : QuadraticForm ℝ V}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
  {b : V → V [⋀^Fin 1]→L[ℝ] ℝ} {ψ : V → W} {x : V}

/-! ### The Laplacian of `|ψ|²` -/

/-- The connection terms cancel from `Re ⟪ψ, ∇_v ∇_v ψ⟫ + |∇_v ψ|²`, which is half the second
derivative of `|ψ|²` along `v`. -/
private theorem re_inner_add_norm_sq_covariantDeriv (hψ : DifferentiableAt ℝ ψ x)
    (hψ' : DifferentiableAt ℝ (fderiv ℝ ψ) x) (hb : DifferentiableAt ℝ b x) (v : V) :
    (⟪ψ x, covariantDeriv b (fun y ↦ covariantDeriv b ψ y v) x v⟫_ℂ).re +
        ‖covariantDeriv b ψ x v‖ ^ 2 =
      (⟪ψ x, fderiv ℝ (fderiv ℝ ψ) x v v⟫_ℂ).re + ‖fderiv ℝ ψ x v‖ ^ 2 := by
  let := InnerProductSpace.complexToReal (G := W)
  have hre (u w : W) : (⟪u, w⟫_ℂ).re = ⟪u, w⟫_ℝ := by
    rw [real_inner_eq_re_inner ℂ, RCLike.re_to_complex]
  have h₁ (z : W) : ⟪z, I • z⟫_ℝ = 0 := real_inner_I_smul_self ℂ z
  have h₂ (u w : W) : ⟪u, I • w⟫_ℝ + ⟪w, I • u⟫_ℝ = 0 := by
    rw [← hre, ← hre, inner_smul_right, inner_smul_right, ← inner_conj_symm u w]
    simp only [Complex.mul_re, I_re, I_im, Complex.conj_re, Complex.conj_im]
    ring
  have h₃ (z : W) : ⟪I • z, I • z⟫_ℝ = ⟪z, z⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_smul, norm_I, one_mul]
  rw [covariantDeriv_covariantDeriv_apply hψ hψ' hb, covariantDeriv_apply,
    hre, hre, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, h₁, h₃]
  linear_combination (2 * b x fun _ ↦ v) * h₂ (ψ x) (fderiv ℝ ψ x v) +
    (b x fun _ ↦ v) * real_inner_comm (fderiv ℝ ψ x v) (I • ψ x)

/-- **The Laplacian of `|ψ|²` through the covariant derivative**: for a `C²` spinor field and a
differentiable connection form, in any orthonormal basis `(eₖ)`,

`Δ |ψ|² = 2 ∑ₖ (Re ⟪ψ, ∇_{eₖ} ∇_{eₖ} ψ⟫ + |∇_{eₖ} ψ|²)`.

The connection terms cancel because `|ψ|²` is gauge invariant. -/
theorem laplacian_norm_sq_eq [FiniteDimensional ℝ V] (hψ : ContDiffAt ℝ 2 ψ x)
    (hb : DifferentiableAt ℝ b x) {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ V) :
    Δ (fun y ↦ ‖ψ y‖ ^ 2) x =
      2 * ∑ k, ((⟪ψ x, covariantDeriv b (fun y ↦ covariantDeriv b ψ y (e k)) x
        (e k)⟫_ℂ).re + ‖covariantDeriv b ψ x (e k)‖ ^ 2) := by
  have hψ₁ : DifferentiableAt ℝ ψ x := hψ.differentiableAt (by norm_num)
  have hψ₂ : DifferentiableAt ℝ (fderiv ℝ ψ) x :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [re_inner_add_norm_sq_covariantDeriv hψ₁ hψ₂ hb, iteratedFDeriv_two_apply]
  let := InnerProductSpace.complexToReal (G := W)
  simpa [real_inner_eq_re_inner ℂ, real_inner_self_eq_norm_sq, add_comm] using
    fderiv_fderiv_norm_sq_sub_comp_apply (a := (0 : W)) hψ (e k) (e k)

/-! ### The Dirac operator and the Weitzenböck formula -/

section Dirac

variable [FiniteDimensional ℝ V]

/-- The **flat Dirac operator** `D ψ = ∑ₖ c(eₖ) ∇_{eₖ} ψ` of the connection `d + i b`, defined
without a basis as the metric contraction of `(v, w) ↦ c(v) ∇_w ψ`. -/
def flatDirac (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ψ : V → W) (x : V) : W :=
  LinearMap.BilinMap.metricTrace (ρ.cliffordPairing (covariantDeriv b ψ x).toLinearMap)

/-- The flat Dirac operator is the metric trace of the Clifford pairing `(v, w) ↦ c(v) ∇_w ψ`. -/
theorem flatDirac_def (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ψ : V → W) (x : V) :
    flatDirac ρ b ψ x =
      LinearMap.BilinMap.metricTrace (ρ.cliffordPairing (covariantDeriv b ψ x).toLinearMap) := by
  rw [flatDirac]

/-- The flat Dirac operator in an orthonormal basis: `D ψ = ∑ₖ c(eₖ) ∇_{eₖ} ψ`. -/
theorem flatDirac_eq_sum {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ V)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ψ : V → W) (x : V) :
    flatDirac ρ b ψ x = ∑ k, ρ (ι Q (e k)) (covariantDeriv b ψ x (e k)) := by
  rw [flatDirac_def, LinearMap.BilinMap.metricTrace_eq_sum _ e]
  simp only [AlgHom.cliffordPairing_apply, ContinuousLinearMap.coe_coe]

/-- The flat Dirac operator of `α u₀` for a constant spinor `u₀`:
`D (α u₀) = ∑ₖ (∇_a α)(eₖ) c(eₖ) u₀`. On the canonical line this is the flat limiting Dirac
operator of `TauCeti.SeibergWitten.sum_covariantDeriv_smul_ι_apply_eq_zero_iff`. -/
theorem flatDirac_smul_const {α : V → ℂ} (hα : DifferentiableAt ℝ α x) (u₀ : W) {κ : Type*}
    [Fintype κ] (e : OrthonormalBasis κ ℝ V) :
    flatDirac ρ b (fun y ↦ α y • u₀) x = ∑ k, covariantDeriv b α x (e k) • ρ (ι Q (e k)) u₀ := by
  simp [flatDirac_eq_sum ρ e, covariantDeriv_smul_const hα]

/-- **The flat Dirac operator is affine in the connection**: changing `b` by `b'` adds the
Clifford multiplication `i c(b') ψ`, which is the flat Dirac operator of the constant field with
value `ψ x` for the connection `b'`. -/
theorem flatDirac_add_connection (b b' : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ψ : V → W) (x : V) :
    flatDirac ρ (b + b') ψ x = flatDirac ρ b ψ x + flatDirac ρ b' (fun _ ↦ ψ x) x := by
  simp only [flatDirac_eq_sum ρ (stdOrthonormalBasis ℝ V), covariantDeriv_apply, fderiv_fun_const,
    Pi.zero_apply, zero_apply, zero_add, Pi.add_apply,
    ContinuousAlternatingMap.add_apply, add_smul, map_add, Finset.sum_add_distrib, add_assoc]

/-- The flat Dirac operator is additive in fields differentiable at the point. -/
theorem flatDirac_add {ζ : V → W} (hψ : DifferentiableAt ℝ ψ x) (hζ : DifferentiableAt ℝ ζ x) :
    flatDirac ρ b (ψ + ζ) x = flatDirac ρ b ψ x + flatDirac ρ b ζ x := by
  simp only [flatDirac_eq_sum ρ (stdOrthonormalBasis ℝ V), covariantDeriv_apply,
    fderiv_add hψ hζ, add_apply, Pi.add_apply, smul_add, map_add,
    Finset.sum_add_distrib]
  abel

/-- The flat Dirac operator is complex-linear in the field: it commutes with complex scalars. -/
theorem flatDirac_smul (c : ℂ) :
    flatDirac ρ b (c • ψ) x = c • flatDirac ρ b ψ x := by
  simp only [flatDirac_eq_sum ρ (stdOrthonormalBasis ℝ V), covariantDeriv_apply,
    fderiv_const_smul_field, smul_apply, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← LinearMap.map_smul, smul_add, smul_comm c (b x _), smul_comm c I]

/-- The Clifford multiplication `i c(b) φ`, the flat Dirac operator of a constant field, is
linear in the connection form. -/
theorem flatDirac_smul_connection_const (c : ℝ) (φ : W) :
    flatDirac ρ (c • b) (fun _ ↦ φ) x = c • flatDirac ρ b (fun _ ↦ φ) x := by
  simp only [flatDirac_eq_sum ρ (stdOrthonormalBasis ℝ V), covariantDeriv_apply, fderiv_fun_const,
    Pi.zero_apply, zero_apply, zero_add, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
    LinearMap.map_smul_of_tower]

/-- **The Clifford multiplication by a connection form**: the flat Dirac operator of a constant
field `φ` for the connection `b` is `i c(v) φ`, where `v` is the vector dual to the covector
`b x` through the inner product. -/
theorem flatDirac_const_eq_smul_ι (φ : W) :
    flatDirac ρ b (fun _ ↦ φ) x = I • ρ (ι Q ((InnerProductSpace.toDual ℝ V).symm
      ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ)
        (0 : Fin 1)).symm (b x)))) φ := by
  set v := (InnerProductSpace.toDual ℝ V).symm
    ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ) (0 : Fin 1)).symm
      (b x))
  have hv (w : V) : b x (fun _ ↦ w) = ⟪v, w⟫ := by
    simp [v, InnerProductSpace.toDual_symm_apply]
  let e := stdOrthonormalBasis ℝ V
  rw [flatDirac_eq_sum ρ e]
  conv_rhs => rw [← e.sum_repr' v]
  simp [covariantDeriv_apply, hv, map_sum, Finset.smul_sum, real_inner_comm,
    LinearMap.map_smul_of_tower, smul_comm I]

variable [FiniteDimensional ℂ W]

/-- **The norm of the Clifford multiplication by a connection form**: for the negative-definite
form `Q v = -‖v‖²` and skew-adjoint generators, the flat Dirac operator of a constant field `φ`,
which is `i c(b) φ` with `b` read as a vector through the inner product, has norm
`‖b x‖ ‖φ‖`. -/
theorem norm_flatDirac_const (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (φ : W) :
    ‖flatDirac ρ b (fun _ ↦ φ) x‖ = ‖b x‖ * ‖φ‖ := by
  rw [flatDirac_const_eq_smul_ι, norm_smul, norm_I, one_mul, CliffordAlgebra.norm_map_ι_apply hQ hρ,
    LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]

/-- **The Clifford multiplication by a connection form is locally Lipschitz**: the bilinear map
`(b, φ) ↦ i c(b) φ`, the flat Dirac operator of a constant field, satisfies
`‖i c(b₁) φ₁ - i c(b₂) φ₂‖ ≤ ‖b₁ - b₂‖ ‖φ₁‖ + ‖b₂‖ ‖φ₁ - φ₂‖` at every point. -/
theorem norm_flatDirac_const_sub_flatDirac_const_le (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (b₁ b₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (φ₁ φ₂ : W) :
    ‖flatDirac ρ b₁ (fun _ ↦ φ₁) x - flatDirac ρ b₂ (fun _ ↦ φ₂) x‖ ≤
      ‖b₁ x - b₂ x‖ * ‖φ₁‖ + ‖b₂ x‖ * ‖φ₁ - φ₂‖ := by
  have hb : flatDirac ρ b₁ (fun _ ↦ φ₁) x =
      flatDirac ρ b₂ (fun _ ↦ φ₁) x + flatDirac ρ (b₁ - b₂) (fun _ ↦ φ₁) x := by
    rw [← flatDirac_add_connection, add_sub_cancel]
  have hφ : flatDirac ρ b₂ (fun _ ↦ φ₁) x =
      flatDirac ρ b₂ (fun _ ↦ φ₂) x + flatDirac ρ b₂ (fun _ ↦ φ₁ - φ₂) x := by
    rw [← flatDirac_add ρ (differentiableAt_const _) (differentiableAt_const _)]
    congr 1
    ext
    simp
  rw [hb, hφ, add_sub_right_comm, add_sub_cancel_left]
  refine (norm_add_le _ _).trans ?_
  rw [norm_flatDirac_const ρ hQ hρ, norm_flatDirac_const ρ hQ hρ, Pi.sub_apply]
  linarith

/-- **The Weitzenböck formula for the flat Dirac operator**: for a `C²` spinor field and a
differentiable connection form `b`, in any orthonormal basis `(eₖ)`,

`D (D ψ) = -∑ₖ ∇_{eₖ} ∇_{eₖ} ψ + i c₂(db) ψ`,

where the curvature `db` is read as a two-vector through the inner product. -/
theorem flatDirac_flatDirac (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hψ : ContDiffAt ℝ 2 ψ x)
    (hb : DifferentiableAt ℝ b x) {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ V) :
    flatDirac ρ b (flatDirac ρ b ψ) x =
      -∑ k, covariantDeriv b (fun y ↦ covariantDeriv b ψ y (e k)) x (e k) +
        I • ρ (bivectorExterior Q ((alternatingFormEquiv V 2).symm (extDeriv b x))) (ψ x) := by
  have hψ₁ : DifferentiableAt ℝ ψ x := hψ.differentiableAt (by norm_num)
  have hψ₂ : DifferentiableAt ℝ (fderiv ℝ ψ) x :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hD : flatDirac ρ b ψ = fun y ↦ ∑ k, ρ (ι Q (e k)) (covariantDeriv b ψ y (e k)) :=
    funext (flatDirac_eq_sum ρ e b ψ)
  -- `∇_{eⱼ} (D ψ) = ∑ₖ c(eₖ) ∇_{eⱼ} ∇_{eₖ} ψ`, since the `c(eₖ)` are constant.
  have hDD (j : κ) : covariantDeriv b (flatDirac ρ b ψ) x (e j) =
      ∑ k, ρ (ι Q (e k)) (covariantDeriv b (fun y ↦ covariantDeriv b ψ y (e k)) x
        (e j)) := by
    rw [hD]
    exact covariantDeriv_sum_apply (fun k ↦ ρ (ι Q (e k)))
      (g := fun k y ↦ covariantDeriv b ψ y (e k))
      (fun k ↦ differentiableAt_covariantDeriv_apply hψ₁ hψ₂ hb (e k)) (e j)
  rw [flatDirac_eq_sum ρ e, Finset.sum_congr rfl fun j _ ↦ congrArg (ρ (ι Q (e j))) (hDD j),
    sum_ι_sum_ι_apply ρ hQ e _ (I • ψ x), map_smul]
  intro j k
  rw [covariantDeriv_sub_swap hψ hb, inner_alternatingFormEquiv_symm_ιMulti]

end Dirac

/-! ### Solutions of the Dirac equation in dimension four -/

section SeibergWitten

variable [Fact (finrank ℝ V = 4)] [FiniteDimensional ℂ W] (o : Orientation ℝ V (Fin 4)) {ρ}
  (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)

-- The dimension `Fact` makes the oriented four-space finite-dimensional.
attribute [local instance] finiteDimensional_of_finrank_four

include hQ in
/-- At a solution of the Dirac equation the rough Laplacian is the Clifford action of the
curvature: `∑ₖ ∇_{eₖ} ∇_{eₖ} ψ = i c₂(db) ψ`. -/
private theorem sum_covariantDeriv_eq_of_flatDirac_eq_zero (hψ : ContDiffAt ℝ 2 ψ x)
    (hb : DifferentiableAt ℝ b x) (hD : flatDirac ρ b ψ =ᶠ[𝓝 x] 0) {κ : Type*} [Fintype κ]
    (e : OrthonormalBasis κ ℝ V) :
    ∑ k, covariantDeriv b (fun y ↦ covariantDeriv b ψ y (e k)) x (e k) =
      I • ρ (bivectorExterior Q ((alternatingFormEquiv V 2).symm (extDeriv b x))) (ψ x) := by
  have h := flatDirac_flatDirac ρ hQ hψ hb e
  rw [flatDirac_eq_sum ρ e, covariantDeriv_eq_zero_of_eventuallyEq hD] at h
  simp only [_root_.zero_apply, _root_.map_zero, Finset.sum_const_zero] at h
  exact neg_add_eq_zero.1 h.symm

include hQ in
/-- **The Weitzenböck identity for `|ψ|²` at a solution of the Dirac equation.** If `ψ` is `C²`,
solves `D ψ = 0` near `x` and takes a value `φ ∈ W⁺` at `x`, then, in any orthonormal basis,

`Δ |ψ|² = 2 (∑ₖ |∇_{eₖ} ψ|² + 4 ⟪q(φ), db⟫)`

at `x`, where `q` is the quadratic two-form and the curvature `db` is read as a two-vector. -/
theorem laplacian_norm_sq_eq_of_flatDirac_eq_zero (hψ : ContDiffAt ℝ 2 ψ x)
    (hb : DifferentiableAt ℝ b x) (hD : flatDirac ρ b ψ =ᶠ[𝓝 x] 0)
    {φ : positiveHalfSpinors o ρ} (hφ : ψ x = φ) {κ : Type*} [Fintype κ]
    (e : OrthonormalBasis κ ℝ V) :
    Δ (fun y ↦ ‖ψ y‖ ^ 2) x =
      2 * (∑ k, ‖covariantDeriv b ψ x (e k)‖ ^ 2 +
        4 * ⟪(quadraticTwoForm o ρ hkl φ : ⋀[ℝ]^2 V),
          (alternatingFormEquiv V 2).symm (extDeriv b x)⟫) := by
  rw [laplacian_norm_sq_eq hψ hb e, Finset.sum_add_distrib, ← Complex.re_sum, ← inner_sum,
    sum_covariantDeriv_eq_of_flatDirac_eq_zero hQ hψ hb hD e,
    inner_quadraticTwoForm_eq_re_inner o ρ hQ hkl, hφ, ← coe_cliffordRestriction_apply,
    Submodule.coe_inner]
  ring

/-- The curvature `db`, read as a two-vector, is minus the real curvature `F = -db`. -/
private theorem alternatingFormEquiv_symm_extDeriv :
    (alternatingFormEquiv V 2).symm (extDeriv b x) =
      -(alternatingFormEquiv V 2).symm (-extDeriv b x) := by
  rw [map_neg, neg_neg]

/-- The pairing of `q(φ)` with the curvature under the large-parameter curvature equation
`F + ⋆F = (r / 4) ω - r q(φ) - η`:
`4 ⟪q(φ), -F⟫ = 2 r |q(φ)|² - (r / 2) ⟪q(φ), ω⟫ + 2 ⟪q(φ), η⟫`. -/
private theorem four_mul_inner_quadraticTwoForm_neg {r : ℝ} {ω η F : ⋀[ℝ]^2 V}
    (φ : positiveHalfSpinors o ρ)
    (hF : F + o.hodgeStar hkl F =
      (r / 4) • ω - r • (quadraticTwoForm o ρ hkl φ : ⋀[ℝ]^2 V) - η) :
    4 * ⟪(quadraticTwoForm o ρ hkl φ : ⋀[ℝ]^2 V), -F⟫ =
      2 * r * ‖(quadraticTwoForm o ρ hkl φ : ⋀[ℝ]^2 V)‖ ^ 2 -
        r / 2 * ⟪(quadraticTwoForm o ρ hkl φ : ⋀[ℝ]^2 V), ω⟫ +
        2 * ⟪(quadraticTwoForm o ρ hkl φ : ⋀[ℝ]^2 V), η⟫ := by
  set q := (quadraticTwoForm o ρ hkl φ : ⋀[ℝ]^2 V)
  -- `q` is self-dual, so it pairs with `F + ⋆F` as with `2 F`.
  have hstar : ⟪q, o.hodgeStar hkl F⟫ = ⟪q, F⟫ :=
    Orientation.inner_hodgeStar_right_of_hodgeStar_eq_self o even_two hkl
      (Orientation.hodgeStar_coe_of_mem_eigenspace_one o hkl (quadraticTwoForm o ρ hkl φ)) F
  have h := congrArg (⟪q, ·⟫) hF
  simp only [inner_add_right, inner_sub_right, real_inner_smul_right, hstar,
    real_inner_self_eq_norm_sq] at h
  rw [inner_neg_right]
  linarith

variable (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
  (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)

include hQ hρ h₂ in
/-- **The forced Weitzenböck equation of the large-parameter equations.** Let `ψ` be a `C²`
normalized spinor field solving the Dirac equation `D ψ = 0` near `x`, with value `χ ∈ W⁺` at `x`,
and suppose the real curvature `F = -db` satisfies `F + ⋆F = (r / 4) ω - r q(χ) - η` at `x`. Then
at `x`, in any orthonormal basis,

`∑ₖ ∇_{eₖ} ∇_{eₖ} ψ = (r / 4) (|χ|² - 1) χ + (r / 2) P_β χ + C(i η) χ / 2`,

that is, `∇*∇ψ + (r / 4) (|ψ|² - 1) ψ + (r / 2) β + C(i η) ψ / 2 = 0` with `β = P_β ψ`. -/
theorem sum_covariantDeriv_eq_of_add_hodgeStar_eq (hψ : ContDiffAt ℝ 2 ψ x)
    (hb : DifferentiableAt ℝ b x) (hD : flatDirac ρ b ψ =ᶠ[𝓝 x] 0)
    {χ : positiveHalfSpinors o ρ} (hχ : ψ x = χ) {r : ℝ} {ω η : ⋀[ℝ]^2 V}
    (hF : (alternatingFormEquiv V 2).symm (-extDeriv b x) +
        o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b x)) =
      (r / 4) • ω - r • (quadraticTwoForm o ρ hkl χ : ⋀[ℝ]^2 V) - η)
    {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ V) :
    ∑ k, covariantDeriv b (fun y ↦ covariantDeriv b ψ y (e k)) x (e k) =
      (((r / 4 * (‖χ‖ ^ 2 - 1)) • χ + (r / 2) • cliffordProjection o ρ (-ω) χ +
        (2⁻¹ : ℝ) • cliffordRestriction o ρ η χ : positiveHalfSpinors o ρ) : W) := by
  rw [sum_covariantDeriv_eq_of_flatDirac_eq_zero hQ hψ hb hD e,
    alternatingFormEquiv_symm_extDeriv]
  set F := (alternatingFormEquiv V 2).symm (-extDeriv b x)
  -- `C` kills the anti-self-dual part `F - ⋆F`, so `C(F + ⋆F) = 2 C(F)`.
  have hCχ : (2 : ℝ) • cliffordRestriction o ρ F χ = cliffordRestriction o ρ
      ((r / 4) • ω - r • (quadraticTwoForm o ρ hkl χ : ⋀[ℝ]^2 V) - η) χ := by
    rw [← hF, map_add, _root_.add_apply, cliffordRestriction_hodgeStar o ρ hQ hkl, two_smul]
  simp only [map_sub, map_smul, _root_.sub_apply, _root_.smul_apply,
    cliffordRestriction_quadraticTwoForm_apply_self o hQ hkl hρ h₂,
    cliffordRestriction_eq_cliffordProjection o ρ ω] at hCχ
  have hP : cliffordProjection o ρ ω χ = χ - cliffordProjection o ρ (-ω) χ := by
    rw [cliffordProjection_neg_apply]
    abel
  rw [hχ, ← coe_cliffordRestriction_apply, map_neg, _root_.neg_apply]
  congr 1
  refine smul_right_injective _ (two_ne_zero (α := ℝ)) ?_
  simp only [smul_neg, hCχ, hP, one_apply_eq_self, ← Complex.coe_smul]
  push_cast
  module

include hQ hρ h₂ in
/-- **Taubes's Weitzenböck identity for the large-parameter equations.** Let `ψ` be a `C²`
normalized spinor field solving the Dirac equation `D ψ = 0` near `x`, with value `χ ∈ W⁺` at `x`,
and suppose the real curvature `F = -db` satisfies the large-parameter curvature equation

`F + ⋆F = (r / 4) ω - r q(χ) - η`

at `x`. Then at `x`, in any orthonormal basis,

`Δ |ψ|² / 2 = ∑ₖ |∇_{eₖ} ψ|² + (r / 4) (|χ|⁴ - |P_α χ|² + |P_β χ|²) + 2 ⟪q(χ), η⟫`,

where `P_α = cliffordProjection o ρ ω` and `P_β = cliffordProjection o ρ (-ω)`. -/
theorem laplacian_norm_sq_eq_of_add_hodgeStar_eq (hψ : ContDiffAt ℝ 2 ψ x)
    (hb : DifferentiableAt ℝ b x) (hD : flatDirac ρ b ψ =ᶠ[𝓝 x] 0)
    {χ : positiveHalfSpinors o ρ} (hχ : ψ x = χ) {r : ℝ} {ω η : ⋀[ℝ]^2 V}
    (hF : (alternatingFormEquiv V 2).symm (-extDeriv b x) +
        o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b x)) =
      (r / 4) • ω - r • (quadraticTwoForm o ρ hkl χ : ⋀[ℝ]^2 V) - η)
    {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ V) :
    Δ (fun y ↦ ‖ψ y‖ ^ 2) x / 2 =
      ∑ k, ‖covariantDeriv b ψ x (e k)‖ ^ 2 +
        r / 4 * (‖χ‖ ^ 4 - ‖cliffordProjection o ρ ω χ‖ ^ 2 +
          ‖cliffordProjection o ρ (-ω) χ‖ ^ 2) +
        2 * ⟪(quadraticTwoForm o ρ hkl χ : ⋀[ℝ]^2 V), η⟫ := by
  rw [laplacian_norm_sq_eq_of_flatDirac_eq_zero o hQ hkl hψ hb hD hχ e,
    alternatingFormEquiv_symm_extDeriv,
    four_mul_inner_quadraticTwoForm_neg o hkl χ hF, Submodule.norm_coe,
    norm_quadraticTwoForm_sq o hQ hkl hρ h₂,
    inner_quadraticTwoForm o hQ hkl]
  ring

include hQ hρ h₂ in
/-- **Taubes's pointwise bound at a local maximum of `|ψ|²`.** Under the hypotheses of
`laplacian_norm_sq_eq_of_add_hodgeStar_eq`, with `r > 0` and `‖ω‖ ≤ √2`, if `|ψ|²` has a local
maximum at `x`, then

`|χ|² ≤ 1 + 2 √2 |η| / r`.

This pointwise inequality at a local maximum is the key step of Taubes's coarse bound
`|α|² + |β|² ≤ 1 + C / r`; for the flat limiting equations (`r = 1 / 2`, `η = 0`) it gives
`|χ| ≤ 1`. -/
theorem norm_sq_le_one_add_of_isLocalMax (hψ : ContDiffAt ℝ 2 ψ x)
    (hb : DifferentiableAt ℝ b x) (hD : flatDirac ρ b ψ =ᶠ[𝓝 x] 0)
    {χ : positiveHalfSpinors o ρ} (hχ : ψ x = χ) {r : ℝ} (hr : 0 < r) {ω η : ⋀[ℝ]^2 V}
    (hω : ‖ω‖ ≤ √2)
    (hF : (alternatingFormEquiv V 2).symm (-extDeriv b x) +
        o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b x)) =
      (r / 4) • ω - r • (quadraticTwoForm o ρ hkl χ : ⋀[ℝ]^2 V) - η)
    (hmax : IsLocalMax (fun y ↦ ‖ψ y‖ ^ 2) x) :
    ‖χ‖ ^ 2 ≤ 1 + 2 * √2 * ‖η‖ / r := by
  set q := (quadraticTwoForm o ρ hkl χ : ⋀[ℝ]^2 V)
  have hΔ := laplacian_nonpos_of_isLocalMax (ContDiffAt.norm_sq ℂ hψ) hmax
  have hid := laplacian_norm_sq_eq_of_add_hodgeStar_eq o hQ hkl hρ h₂ hψ hb hD hχ hF
    (stdOrthonormalBasis ℝ V)
  have hP := inner_quadraticTwoForm o hQ hkl (ω := ω) χ
  have hsum : 0 ≤ ∑ k, ‖covariantDeriv b ψ x (stdOrthonormalBasis ℝ V k)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ by positivity
  -- `|q(χ)| = |χ|² / (2 √2)` and `|ω| ≤ √2` bound the two pairings of `q(χ)`.
  have hq : ‖q‖ = ‖χ‖ ^ 2 / (2 * √2) :=
    (Submodule.norm_coe _).trans (norm_quadraticTwoForm o hQ hkl hρ h₂ χ)
  have hs : √2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
  have h₁ : ⟪q, ω⟫ ≤ ‖χ‖ ^ 2 / 2 := by
    refine ((real_inner_le_norm q ω).trans
      (mul_le_mul_of_nonneg_left hω (norm_nonneg q))).trans_eq ?_
    rw [hq]
    field_simp
  have hη : -⟪q, η⟫ ≤ ‖χ‖ ^ 2 / (2 * √2) * ‖η‖ := by
    have h := abs_le.1 (abs_real_inner_le_norm q η)
    rw [← hq]
    linarith
  -- Hence `|χ|² (r (|χ|² - 1) - 2 √2 |η|) ≤ 0`.
  set t := ‖χ‖ ^ 2 with ht
  have ht₀ : 0 ≤ t := by positivity
  have hkey : t * (r * (t - 1) - 2 * √2 * ‖η‖) ≤ 0 := by
    have h4 : ‖χ‖ ^ 4 = t ^ 2 := by rw [ht]; ring
    have hη' : -⟪q, η⟫ ≤ t * ‖η‖ * √2 / 4 := by
      refine hη.trans_eq ?_
      field_simp
      rw [hs]
      ring
    rw [h4] at hid
    nlinarith [mul_le_mul_of_nonneg_left h₁ hr.le, congrArg (r * ·) hP]
  rcases ht₀.eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · have : r * (t - 1) ≤ 2 * √2 * ‖η‖ := by
      by_contra hc
      nlinarith [not_le.1 hc]
    rw [← sub_le_iff_le_add', le_div_iff₀ hr]
    linarith

end SeibergWitten

end TauCeti.SeibergWitten
