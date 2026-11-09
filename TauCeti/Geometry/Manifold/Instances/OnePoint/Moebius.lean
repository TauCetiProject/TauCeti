/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
public import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars

/-!
# Möbius transformations of the projective line are analytic

Mathlib identifies the projective line `OnePoint 𝕜` with the projectivization `ℙ 𝕜 (Fin 2 → 𝕜)`
(`OnePoint.equivProjectivization`) and lets `GL (Fin 2) 𝕜` act on it through this identification
(`OnePoint.instGLAction`), by the Möbius transformations
`z ↦ (a * z + b) / (c * z + d)`. This file relates that description to the two charts of the
analytic manifold `OnePoint 𝕜`, and shows that every Möbius transformation is analytic.

In homogeneous coordinates, the affine chart reads the point `[v₀ : v₁]` as `v₀ / v₁` where
`v₁ ≠ 0`, and the inverted chart reads it as `v₁ / v₀` where `v₀ ≠ 0`. The inverse of the inverted
chart is itself the Möbius transformation of the matrix `!![0, 1; 1, 0]`, restricted to `𝕜`.

Analyticity is checked on `𝕜` first: near a point `z₀` where `c * z₀ + d ≠ 0` the transformation
is the analytic function `(a * z + b) / (c * z + d)` followed by the inclusion `𝕜 → OnePoint 𝕜`,
and near a pole it is `(c * z + d) / (a * z + b)` followed by the inverse of the inverted chart,
the numerator `a * z₀ + b` being nonzero there because the matrix is invertible. Near `∞`, a
Möbius transformation precomposed with the inverse of the inverted chart is again a Möbius
transformation restricted to `𝕜`.

Hence `GL (Fin 2) 𝕜` acts on `OnePoint 𝕜` by analytic maps (`OnePoint.instContMDiffConstSMul`),
and so does `PSL(2, 𝕜)`, which acts through representatives (`OnePoint.instContMDiffConstSMulPSL`).
For `𝕜 = ℂ`, each Möbius transformation is therefore a biholomorphism of the Riemann sphere, with
inverse the transformation of the inverse matrix: this is `Diffeomorph.constSmul 𝓘(ℂ) ω g`.
Restricting scalars, the Möbius transformations are also smooth maps of the underlying real
surface, and in the affine coordinate the transformation of `!![a, b; c, d]` has derivative
`det / (c * z + d) ^ 2`.

## Main results

* `OnePoint.affineChart_equivProjectivization_symm_mk` and
  `OnePoint.invChart_equivProjectivization_symm_mk`: the two charts in homogeneous coordinates.
* `OnePoint.invChart_symm_eq_smul`: the inverse of the inverted chart is a Möbius transformation.
* `Matrix.GeneralLinearGroup.contMDiff_smul_coe`: a Möbius transformation restricted to `𝕜` is
  analytic.
* `OnePoint.instContMDiffConstSMul`: `GL (Fin 2) 𝕜` acts on `OnePoint 𝕜` by analytic maps.
* `OnePoint.instContMDiffConstSMulPGL`: so does `PGL(2, 𝕜)`.
* `OnePoint.instContinuousConstSMul`: in particular it acts by homeomorphisms.
* `OnePoint.instContMDiffConstSMulPSL`: `PSL(2, 𝕜)` acts on `OnePoint 𝕜` by analytic maps.
* `OnePoint.instContMDiffConstSMulGLReal`, `OnePoint.instContMDiffConstSMulPSLReal`: `GL(2, ℂ)`
  and `PSL(2, ℂ)` act on the Riemann sphere by smooth maps of the underlying real surface.
* `Matrix.GeneralLinearGroup.mfderiv_smul_coe_apply`: the derivative of a Möbius transformation
  at a finite point with finite image, read in the affine charts.
* `OnePoint.mfderiv_smul_coe_apply`: the same derivative on the Riemann sphere regarded as a real
  surface.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §§1–2.
-/

public noncomputable section

open Filter Matrix Set Topology

open scoped ContDiff Manifold MatrixGroups

namespace OnePoint

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [DecidableEq 𝕜]

/-! ### The charts in homogeneous coordinates

These lemmas are `simp↓` (pre-simp) lemmas: as ordinary simp lemmas they would never fire, since
`simp` first rewrites the inner point with Mathlib's `equivProjectivization_symm_apply_mk`. -/

/-- The point `[v₀ : v₁]` of the projective line lies in the source of the affine chart exactly
when `v₁ ≠ 0`. -/
@[simp↓]
theorem equivProjectivization_symm_mk_mem_affineChart_source_iff {v : Fin 2 → 𝕜} (hv : v ≠ 0) :
    (equivProjectivization 𝕜).symm (.mk 𝕜 v hv) ∈ affineChart.source ↔ v 1 ≠ 0 := by
  by_cases h : v 1 = 0 <;> simp [h]

/-- The affine chart reads the point `[v₀ : v₁]` of the projective line as `v₀ / v₁`. Off its
source, where `v₁ = 0`, both sides are `0`. -/
@[simp↓]
theorem affineChart_equivProjectivization_symm_mk {v : Fin 2 → 𝕜} (hv : v ≠ 0) :
    affineChart ((equivProjectivization 𝕜).symm (.mk 𝕜 v hv)) = v 0 / v 1 := by
  by_cases h : v 1 = 0 <;> simp [h, div_eq_inv_mul]

section Proper

variable [ProperSpace 𝕜]

/-- The point `[v₀ : v₁]` of the projective line lies in the source of the inverted chart exactly
when `v₀ ≠ 0`. -/
@[simp↓]
theorem equivProjectivization_symm_mk_mem_invChart_source_iff {v : Fin 2 → 𝕜} (hv : v ≠ 0) :
    (equivProjectivization 𝕜).symm (.mk 𝕜 v hv) ∈ invChart.source ↔ v 0 ≠ 0 := by
  by_cases h : v 1 = 0
  · have h0 : v 0 ≠ 0 := fun h0 ↦ hv (funext fun i ↦ by fin_cases i <;> assumption)
    simp [h, h0]
  · simp [h]

/-- The inverted chart reads the point `[v₀ : v₁]` of the projective line as `v₁ / v₀`. Off its
source, where `v₀ = 0`, both sides are `0`. -/
@[simp↓]
theorem invChart_equivProjectivization_symm_mk {v : Fin 2 → 𝕜} (hv : v ≠ 0) :
    invChart ((equivProjectivization 𝕜).symm (.mk 𝕜 v hv)) = v 1 / v 0 := by
  by_cases h1 : v 1 = 0 <;> simp [h1, div_eq_inv_mul]

/-! ### Möbius transformations -/

/-- The inverse of the inverted chart, `0 ↦ ∞` and `w ↦ w⁻¹` for `w ≠ 0`, is the Möbius
transformation `z ↦ 1 / z` of the matrix `!![0, 1; 1, 0]`, restricted to `𝕜`. -/
theorem invChart_symm_eq_smul (w : 𝕜) :
    invChart.symm w = GeneralLinearGroup.mkOfDetNeZero (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) 𝕜)
      (by simp) • (w : OnePoint 𝕜) := by
  rw [smul_some_eq_ite]
  by_cases hw : w = 0 <;> simp [GeneralLinearGroup.mkOfDetNeZero, hw]

end Proper

end OnePoint

namespace Matrix.GeneralLinearGroup

open OnePoint

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [DecidableEq 𝕜] [ProperSpace 𝕜]

/-- **A Möbius transformation restricted to `𝕜` is analytic.** For `g = !![a, b; c, d]`, it is
`z ↦ (a * z + b) / (c * z + d)` away from the pole and sends the pole to `∞`. -/
theorem contMDiff_smul_coe (g : GL (Fin 2) 𝕜) :
    ContMDiff 𝓘(𝕜) 𝓘(𝕜) ω fun z : 𝕜 ↦ g • (z : OnePoint 𝕜) := by
  intro z₀
  -- The transformation is the quotient of the affine forms `a * z + b` and `c * z + d`.
  have hpc : ContDiff 𝕜 ω fun z : 𝕜 ↦ g 0 0 * z + g 0 1 := by fun_prop
  have hqc : ContDiff 𝕜 ω fun z : 𝕜 ↦ g 1 0 * z + g 1 1 := by fun_prop
  by_cases hq₀ : g 1 0 * z₀ + g 1 1 = 0
  · -- At the pole, the transformation is the reciprocal quotient read in the inverted chart.
    have hp₀ : g 0 0 * z₀ + g 0 1 ≠ 0 := by
      intro hp₀
      apply g.det_ne_zero
      rw [det_fin_two]
      linear_combination g 0 0 * hq₀ - g 1 0 * hp₀
    have hev : (fun z : 𝕜 ↦ g • (z : OnePoint 𝕜)) =ᶠ[𝓝 z₀]
        fun z ↦ invChart.symm ((g 1 0 * z + g 1 1) / (g 0 0 * z + g 0 1)) := by
      filter_upwards [hpc.continuous.continuousAt.eventually_ne hp₀] with z hz
      rw [smul_some_eq_ite]
      split_ifs with h
      · rw [h, zero_div, invChart_symm_zero]
      · rw [invChart_symm_of_ne_zero (div_ne_zero h hz), inv_div]
    exact ((contMDiff_invChart_symm _).comp z₀
      ((hqc.contDiffAt.div hpc.contDiffAt hp₀).contMDiffAt)).congr_of_eventuallyEq hev
  · -- Away from the pole, the transformation is the quotient followed by the inclusion.
    have hev : (fun z : 𝕜 ↦ g • (z : OnePoint 𝕜)) =ᶠ[𝓝 z₀]
        fun z ↦ (((g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1) : 𝕜) : OnePoint 𝕜) := by
      filter_upwards [hqc.continuous.continuousAt.eventually_ne hq₀] with z hz
      rw [smul_some_eq_ite]
      split_ifs with h
      exacts [absurd h hz, rfl]
    exact ((contMDiff_coe _).comp z₀
      ((hpc.contDiffAt.div hqc.contDiffAt hq₀).contMDiffAt)).congr_of_eventuallyEq hev

end Matrix.GeneralLinearGroup

namespace OnePoint

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [DecidableEq 𝕜] [ProperSpace 𝕜]

/-- **Möbius transformations of the projective line are analytic.** For `𝕜 = ℂ`, every
transformation `z ↦ (a * z + b) / (c * z + d)` of the Riemann sphere is holomorphic, and hence a
biholomorphism `Diffeomorph.constSmul 𝓘(ℂ) ω g` with inverse the transformation of `g⁻¹`. -/
instance instContMDiffConstSMul : ContMDiffConstSMul 𝓘(𝕜) ω (GL (Fin 2) 𝕜) (OnePoint 𝕜) where
  contMDiff_const_smul g x := by
    induction x using OnePoint.rec with
    | infty =>
      -- Near `∞`, read the transformation through the inverted chart, whose inverse is itself a
      -- Möbius transformation `σ`.
      obtain ⟨σ, hσ⟩ : ∃ σ : GL (Fin 2) 𝕜, ∀ w : 𝕜, invChart.symm w = σ • (w : OnePoint 𝕜) :=
        ⟨_, invChart_symm_eq_smul⟩
      have hev : (fun x : OnePoint 𝕜 ↦ g • x) =ᶠ[𝓝 (∞ : OnePoint 𝕜)]
          (fun w : 𝕜 ↦ (g * σ) • (w : OnePoint 𝕜)) ∘ invChart := by
        filter_upwards [invChart.open_source.mem_nhds (by simp)] with x hx
        rw [Function.comp_apply, mul_smul, ← hσ, invChart.left_inv hx]
      exact (((g * σ).contMDiff_smul_coe _).comp _
        (contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (Or.inr rfl))
          (by simp))).congr_of_eventuallyEq hev
    | coe z =>
      -- Near a finite point, read the transformation through the affine chart.
      have hev : (fun x : OnePoint 𝕜 ↦ g • x) =ᶠ[𝓝 (z : OnePoint 𝕜)]
          (fun w : 𝕜 ↦ g • (w : OnePoint 𝕜)) ∘ affineChart := by
        filter_upwards [affineChart.open_source.mem_nhds (by simp)] with x hx
        rw [Function.comp_apply, ← affineChart_symm_apply, affineChart.left_inv hx]
      exact ((g.contMDiff_smul_coe _).comp _
        (contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (Or.inl rfl))
          (by simp))).congr_of_eventuallyEq hev

/-- **The Möbius transformations of `PGL(2, 𝕜)` are analytic**, since the class of a matrix acts
as the matrix does. -/
instance instContMDiffConstSMulPGL : ContMDiffConstSMul 𝓘(𝕜) ω PGL(2, 𝕜) (OnePoint 𝕜) where
  contMDiff_const_smul g := by
    induction g using ProjGenLinGroup.induction_on with
    | mk g => simpa only [pglMk_smul] using contMDiff_const_smul (I := 𝓘(𝕜)) (n := ω) g

/-- Möbius transformations are homeomorphisms of the projective line. -/
instance instContinuousConstSMul : ContinuousConstSMul (GL (Fin 2) 𝕜) (OnePoint 𝕜) :=
  ContMDiffConstSMul.continuousConstSMul (I := 𝓘(𝕜)) ω

/-- `PSL(2, 𝕜)` acts on the projective line by analytic maps, through representatives. -/
instance instContMDiffConstSMulPSL : ContMDiffConstSMul 𝓘(𝕜) ω PSL(2, 𝕜) (OnePoint 𝕜) where
  contMDiff_const_smul g := by
    induction g using QuotientGroup.induction_on with
    | H A =>
      simpa only [pslMk_smul] using contMDiff_const_smul (I := 𝓘(𝕜)) (n := ω) (A : GL (Fin 2) 𝕜)

/-! ### Möbius transformations as smooth maps of the real surface -/

/-- `GL(2, ℂ)` acts on the Riemann sphere, regarded as a real surface, by smooth (indeed
real-analytic) maps: each Möbius transformation is holomorphic. -/
instance instContMDiffConstSMulGLReal {n : WithTop ℕ∞} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n (GL (Fin 2) ℂ) (OnePoint ℂ) where
  contMDiff_const_smul g := by
    simpa only [modelWithCornersSelf_restrictScalars] using
      ((contMDiff_const_smul (I := 𝓘(ℂ)) (n := ω) g).restrictScalars ℝ).of_le le_top

/-- `PSL(2, ℂ)` acts on the Riemann sphere, regarded as a real surface, by smooth (indeed
real-analytic) maps. -/
instance instContMDiffConstSMulPSLReal {n : WithTop ℕ∞} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n PSL(2, ℂ) (OnePoint ℂ) where
  contMDiff_const_smul g := by
    simpa only [modelWithCornersSelf_restrictScalars] using
      ((contMDiff_const_smul (I := 𝓘(ℂ)) (n := ω) g).restrictScalars ℝ).of_le le_top

end OnePoint

namespace Matrix.GeneralLinearGroup

open OnePoint

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [DecidableEq 𝕜] [ProperSpace 𝕜]

/-- **The derivative of a Möbius transformation.** At a finite point `z` that is not a pole,
`z ↦ (a z + b) / (c z + d)` has derivative `(a d - b c) / (c z + d) ^ 2`, read in the affine
charts at `z` and at its image. -/
theorem mfderiv_smul_coe_apply (g : GL (Fin 2) 𝕜) {z : 𝕜} (hz : g 1 0 * z + g 1 1 ≠ 0) (v : 𝕜) :
    mfderiv 𝓘(𝕜) 𝓘(𝕜) (fun x : OnePoint 𝕜 ↦ g • x) z v =
      ((g : Matrix (Fin 2) (Fin 2) 𝕜).det / (g 1 0 * z + g 1 1) ^ 2 * v : 𝕜) := by
  have hq : Continuous fun w : 𝕜 ↦ g 1 0 * w + g 1 1 := by fun_prop
  have hgz : g • (z : OnePoint 𝕜) = (((g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1) : 𝕜) :
      OnePoint 𝕜) := by
    rw [smul_some_eq_ite, ite_eq_right_iff.2 fun h ↦ absurd h hz]
  refine mfderiv_apply_eq_of_hasDerivAt
    ((contMDiff_const_smul (I := 𝓘(𝕜)) (n := ⊤) g).mdifferentiable (by simp) _) ?_ ?_ v
    (φ := fun w ↦ (g 0 0 * w + g 0 1) / (g 1 0 * w + g 1 1))
  · rw [hgz, chartAt_coe, chartAt_coe, affineChart_coe]
    filter_upwards [hq.continuousAt.eventually_ne hz] with w hw
    simp [smul_some_eq_ite, hw]
  · rw [chartAt_coe, affineChart_coe, det_fin_two]
    have hp : HasDerivAt (fun w : 𝕜 ↦ g 0 0 * w + g 0 1) (g 0 0) z := by
      simpa using ((hasDerivAt_id z).const_mul (g 0 0)).add_const (c := g 0 1)
    have hq' : HasDerivAt (fun w : 𝕜 ↦ g 1 0 * w + g 1 1) (g 1 0) z := by
      simpa using ((hasDerivAt_id z).const_mul (g 1 0)).add_const (c := g 1 1)
    convert HasDerivAt.div hp hq' hz using 1
    ring


end Matrix.GeneralLinearGroup

namespace OnePoint

/-- **The derivative of a Möbius transformation in the affine coordinate.** At a finite point `z`
which `g = !![a, b; c, d]` does not send to `∞`, the derivative of `g` on the Riemann sphere,
read in the affine charts, is multiplication by `det g / (c * z + d) ^ 2`. -/
theorem mfderiv_smul_coe_apply (g : GL (Fin 2) ℂ) {z : ℂ} (hz : g 1 0 * z + g 1 1 ≠ 0)
    (v : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • · : OnePoint ℂ → OnePoint ℂ) z v =
      (g : Matrix (Fin 2) (Fin 2) ℂ).det / (g 1 0 * z + g 1 1) ^ 2 * v := by
  have hmd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (g • · : OnePoint ℂ → OnePoint ℂ) z :=
    (contMDiff_const_smul (I := 𝓘(ℂ)) (n := ω) g).mdifferentiableAt (by simp)
  -- The real derivative is the complex one, computed by
  -- `Matrix.GeneralLinearGroup.mfderiv_smul_coe_apply`; the casts `tangentSpaceCastModel` between
  -- the tangent spaces and `ℂ` are identities.
  exact (DFunLike.congr_fun (hmd.mfderiv_restrictScalars ℝ) v).trans
    (g.mfderiv_smul_coe_apply hz v)

end OnePoint
