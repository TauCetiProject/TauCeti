/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Moebius
public import TauCeti.Topology.Compactification.OnePoint.Stabilizer
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# First jets of Möbius transformations

Let `𝕜` be a proper nontrivially normed field, such as `ℂ`. The projective line `OnePoint 𝕜` is a
one-dimensional manifold over `𝕜`, with the affine chart at finite points and the inverted chart
`w = 1 / z` at `∞`, so each tangent space is `𝕜` read in the preferred chart at that point.

This file computes the derivatives of Möbius transformations in these charts and shows that a
Möbius transformation is determined by its first jet at `0` together with its value at `∞`.

* At a finite point `z` with finite image, the derivative of `z ↦ (a z + b) / (c z + d)` is
  multiplication by `(a d - b c) / (c z + d) ^ 2`
  (`Matrix.GeneralLinearGroup.mfderiv_smul_coe`).
* The subgroup of `PGL(2, 𝕜)` fixing `0` and `∞` is the group `𝕜ˣ` of dilations
  (`OnePoint.pglFixingZeroInftyEquiv`), and this coordinate is the first jet at `0`: an element
  fixing `0` and `∞` has derivative `a` at `0`, where `a` is its coordinate
  (`OnePoint.mfderiv_smul_zero_eq_pglFixingZeroInftyEquiv`). Read in the inverted chart at the
  other fixed point `∞`, its derivative is `a⁻¹`
  (`OnePoint.mfderiv_smul_infty_eq_pglFixingZeroInftyEquiv`).
* **First-jet coordinates.** For distinct points `p` and `q` and a nonzero tangent vector `v` at
  `p`, exactly one element of `PGL(2, 𝕜)` sends `0` to `p` and `∞` to `q` and has derivative `v`
  at `0` on the unit tangent vector `1` (`OnePoint.existsUnique_pgl_smul_zero_infty_mfderiv_eq`).
  So `g ↦ (g • 0, dg₀ 1, g • ∞)` identifies `PGL(2, 𝕜)` with the triples of a point, a nonzero
  tangent vector at it and a second point. This is the analogue, with one point replaced by a
  tangent direction, of the parametrization of `PGL(2, 𝕜)` by ordered triples of distinct points
  (`OnePoint.existsUnique_pgl_smul_zero_one_infty_eq`). The derivative is taken in the preferred
  chart at `g • 0`, the affine chart when `p` is finite and the inverted chart when `p = ∞`.

For the Riemann sphere, where `PGL(2, ℂ)` is the group of automorphisms, these coordinates
normalize the reparametrizations of a genus-zero domain carrying two marked points and a tangent
direction at one of them, in the way that ordered triples normalize three marked points.

## Main results

* `Matrix.GeneralLinearGroup.mfderiv_smul_coe`: the derivative of a Möbius transformation at a
  finite point with finite image.
* `OnePoint.mfderiv_pglFixingZeroInftyEquiv_symm_zero` and
  `OnePoint.mfderiv_pglFixingZeroInftyEquiv_symm_infty`: the dilation `z ↦ a z` has derivative `a`
  at `0` and `a⁻¹` at `∞`.
* `OnePoint.mfderiv_pgl_smul_ne_zero`: the derivative of a Möbius transformation is nonzero on
  nonzero tangent vectors.
* `OnePoint.mfderiv_smul_zero_eq_pglFixingZeroInftyEquiv`: the coordinate of an element fixing `0`
  and `∞` is its derivative at `0`.
* `OnePoint.mfderiv_mul_pglFixingZeroInftyEquiv_symm_zero`: precomposing with the dilation
  `z ↦ a z` multiplies the derivative at `0` by `a`.
* `OnePoint.existsUnique_pgl_smul_zero_infty_mfderiv_eq`: the first-jet coordinates of
  `PGL(2, 𝕜)`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §§1–2.
* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §§3.2 and 4.3.
-/

public section

open Filter Matrix MulAction Set Topology

open scoped Manifold MatrixGroups

namespace OnePoint

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [DecidableEq 𝕜] [ProperSpace 𝕜]

/-- A Möbius transformation of `PGL(2, 𝕜)` is differentiable. -/
private theorem mdifferentiableAt_pgl_smul (g : PGL(2, 𝕜)) (x : OnePoint 𝕜) :
    MDifferentiableAt 𝓘(𝕜) 𝓘(𝕜) (fun y : OnePoint 𝕜 ↦ g • y) x :=
  (contMDiff_const_smul (I := 𝓘(𝕜)) (n := ⊤) g).mdifferentiable (by simp) x

/-- The derivative of a Möbius transformation of `PGL(2, 𝕜)` vanishes on no nonzero tangent
vector, since the transformation is a diffeomorphism. -/
theorem mfderiv_pgl_smul_ne_zero (g : PGL(2, 𝕜)) (x : OnePoint 𝕜) {v : 𝕜} (hv : v ≠ 0) :
    (mfderiv 𝓘(𝕜) 𝓘(𝕜) (fun y : OnePoint 𝕜 ↦ g • y) x v : 𝕜) ≠ 0 := by
  intro h
  obtain ⟨e, he⟩ := (Diffeomorph.constSmul 𝓘(𝕜) ⊤ g).isInvertible_mfderiv (x := x) (by simp)
  rw [Diffeomorph.coe_constSmul] at he
  rw [← he] at h
  exact hv (e.map_eq_zero_iff.1 h)

end OnePoint

namespace Matrix.GeneralLinearGroup

open OnePoint

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [DecidableEq 𝕜] [ProperSpace 𝕜]

/-- **The derivative of a Möbius transformation.** At a finite point `z` that is not a pole,
`z ↦ (a z + b) / (c z + d)` has derivative `(a d - b c) / (c z + d) ^ 2`, read in the affine
charts at `z` and at its image. -/
theorem mfderiv_smul_coe (g : GL (Fin 2) 𝕜) {z : 𝕜} (hz : g 1 0 * z + g 1 1 ≠ 0) (v : 𝕜) :
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

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [DecidableEq 𝕜] [ProperSpace 𝕜]

/-- **The dilation `z ↦ a z` has derivative `a` at `0`.** -/
theorem mfderiv_pglFixingZeroInftyEquiv_symm_zero (a : 𝕜ˣ) (v : 𝕜) :
    mfderiv 𝓘(𝕜) 𝓘(𝕜) (fun x : OnePoint 𝕜 ↦ (pglFixingZeroInftyEquiv.symm a : PGL(2, 𝕜)) • x)
      ((0 : 𝕜) : OnePoint 𝕜) v = (a * v : 𝕜) := by
  refine mfderiv_apply_eq_of_hasDerivAt (mdifferentiableAt_pgl_smul _ _) ?_
    (((hasDerivAt_id _).const_mul (a : 𝕜)).congr_deriv (mul_one _)) v
    (φ := fun w : 𝕜 ↦ (a : 𝕜) * w)
  · refine Eventually.of_forall fun w ↦ ?_
    simp

/-- **The dilation `z ↦ a z` has derivative `a⁻¹` at `∞`**, read in the inverted chart, in which
it is `w ↦ a⁻¹ w`. -/
theorem mfderiv_pglFixingZeroInftyEquiv_symm_infty (a : 𝕜ˣ) (v : 𝕜) :
    mfderiv 𝓘(𝕜) 𝓘(𝕜) (fun x : OnePoint 𝕜 ↦ (pglFixingZeroInftyEquiv.symm a : PGL(2, 𝕜)) • x)
      (∞ : OnePoint 𝕜) v = (((a⁻¹ : 𝕜ˣ) : 𝕜) * v : 𝕜) := by
  refine mfderiv_apply_eq_of_hasDerivAt (mdifferentiableAt_pgl_smul _ _) ?_
    (((hasDerivAt_id _).const_mul ((a⁻¹ : 𝕜ˣ) : 𝕜)).congr_deriv (mul_one _)) v
    (φ := fun w : 𝕜 ↦ ((a⁻¹ : 𝕜ˣ) : 𝕜) * w)
  · refine Eventually.of_forall fun w ↦ ?_
    rw [pglFixingZeroInftyEquiv_symm_smul_infty, chartAt_infty]
    by_cases hw : w = 0
    · simp [hw]
    · simp [hw, mul_comm]

/-- **The coordinate of an element fixing `0` and `∞` is its first jet at `0`**: the unit `a`
attached to it by `OnePoint.pglFixingZeroInftyEquiv` is its derivative at `0`. -/
@[simp]
theorem mfderiv_smul_zero_eq_pglFixingZeroInftyEquiv
    (g : fixingSubgroup PGL(2, 𝕜) {((0 : 𝕜) : OnePoint 𝕜), (∞ : OnePoint 𝕜)}) (v : 𝕜) :
    mfderiv 𝓘(𝕜) 𝓘(𝕜) (fun x : OnePoint 𝕜 ↦ (g : PGL(2, 𝕜)) • x) ((0 : 𝕜) : OnePoint 𝕜) v =
      ((pglFixingZeroInftyEquiv g : 𝕜) * v : 𝕜) := by
  conv_lhs => rw [← pglFixingZeroInftyEquiv.symm_apply_apply g]
  exact mfderiv_pglFixingZeroInftyEquiv_symm_zero _ v

/-- The derivative at `∞` of an element fixing `0` and `∞`, read in the inverted chart, is the
inverse of its derivative at `0`. -/
@[simp]
theorem mfderiv_smul_infty_eq_pglFixingZeroInftyEquiv
    (g : fixingSubgroup PGL(2, 𝕜) {((0 : 𝕜) : OnePoint 𝕜), (∞ : OnePoint 𝕜)}) (v : 𝕜) :
    mfderiv 𝓘(𝕜) 𝓘(𝕜) (fun x : OnePoint 𝕜 ↦ (g : PGL(2, 𝕜)) • x) (∞ : OnePoint 𝕜) v =
      ((((pglFixingZeroInftyEquiv g)⁻¹ : 𝕜ˣ) : 𝕜) * v : 𝕜) := by
  conv_lhs => rw [← pglFixingZeroInftyEquiv.symm_apply_apply g]
  exact mfderiv_pglFixingZeroInftyEquiv_symm_infty _ v

/-- Precomposing a Möbius transformation with the dilation `z ↦ a z` multiplies its derivative at
`0` by `a`. -/
theorem mfderiv_mul_pglFixingZeroInftyEquiv_symm_zero (g : PGL(2, 𝕜)) (a : 𝕜ˣ) (v : 𝕜) :
    mfderiv 𝓘(𝕜) 𝓘(𝕜)
      (fun x : OnePoint 𝕜 ↦ (g * (pglFixingZeroInftyEquiv.symm a : PGL(2, 𝕜))) • x)
      ((0 : 𝕜) : OnePoint 𝕜) v =
      (a : 𝕜) • mfderiv 𝓘(𝕜) 𝓘(𝕜) (fun x : OnePoint 𝕜 ↦ g • x) ((0 : 𝕜) : OnePoint 𝕜) v := by
  have hcomp : (fun x : OnePoint 𝕜 ↦ (g * (pglFixingZeroInftyEquiv.symm a : PGL(2, 𝕜))) • x) =
      (fun x ↦ g • x) ∘ fun x ↦ (pglFixingZeroInftyEquiv.symm a : PGL(2, 𝕜)) • x :=
    funext fun x ↦ mul_smul _ _ x
  rw [mfderiv_congr hcomp]
  -- The dilation fixes `0`, so the chain rule evaluates the derivative of `g` at `0` itself.
  refine (mfderiv_comp_apply_of_eq ((0 : 𝕜) : OnePoint 𝕜) (y := ((0 : 𝕜) : OnePoint 𝕜))
    (mdifferentiableAt_pgl_smul _ _) (mdifferentiableAt_pgl_smul _ _) (by simp) v).trans ?_
  rw [mfderiv_pglFixingZeroInftyEquiv_symm_zero]
  exact (mfderiv 𝓘(𝕜) 𝓘(𝕜) (fun x : OnePoint 𝕜 ↦ g • x) _).map_smul (a : 𝕜) v

/-- **First-jet coordinates of `PGL(2, 𝕜)`.** For distinct points `p` and `q` of the projective
line and a nonzero tangent vector `v` at `p`, read in the preferred chart at `p`, exactly one
Möbius transformation sends `0` to `p` and `∞` to `q` and has derivative `v` at `0` on the
tangent vector `1`. -/
theorem existsUnique_pgl_smul_zero_infty_mfderiv_eq {p q : OnePoint 𝕜} (hpq : p ≠ q) {v : 𝕜}
    (hv : v ≠ 0) :
    ∃! g : PGL(2, 𝕜), g • ((0 : 𝕜) : OnePoint 𝕜) = p ∧ g • (∞ : OnePoint 𝕜) = q ∧
      mfderiv 𝓘(𝕜) 𝓘(𝕜) (fun x : OnePoint 𝕜 ↦ g • x) ((0 : 𝕜) : OnePoint 𝕜) (1 : 𝕜) = v := by
  classical
  -- Some transformation sends `0` to `p` and `∞` to `q`; correct its derivative by a dilation.
  obtain ⟨r, hr⟩ := Infinite.exists_notMem_finset ({p, q} : Finset (OnePoint 𝕜))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
  obtain ⟨h, h0, -, hinf⟩ :=
    (existsUnique_pgl_smul_zero_one_infty_eq (Ne.symm hr.1) hpq hr.2).exists
  set u : 𝕜 := mfderiv 𝓘(𝕜) 𝓘(𝕜) (fun x : OnePoint 𝕜 ↦ h • x) ((0 : 𝕜) : OnePoint 𝕜) (1 : 𝕜)
  have hu : u ≠ 0 := mfderiv_pgl_smul_ne_zero h _ one_ne_zero
  -- Two transformations agreeing at `0` and `∞` differ by a dilation.
  have hfix (g : PGL(2, 𝕜)) (hg0 : g • ((0 : 𝕜) : OnePoint 𝕜) = p)
      (hginf : g • (∞ : OnePoint 𝕜) = q) :
      ∃ a : 𝕜ˣ, g = h * (pglFixingZeroInftyEquiv.symm a : PGL(2, 𝕜)) := by
    have hmem : h⁻¹ * g ∈
        fixingSubgroup PGL(2, 𝕜) {((0 : 𝕜) : OnePoint 𝕜), (∞ : OnePoint 𝕜)} := by
      simp [mem_fixingSubgroup_iff, mul_smul, hg0, hginf, ← h0, ← hinf]
    refine ⟨pglFixingZeroInftyEquiv ⟨_, hmem⟩, ?_⟩
    rw [pglFixingZeroInftyEquiv.symm_apply_apply, mul_inv_cancel_left]
  refine ⟨h * (pglFixingZeroInftyEquiv.symm (Units.mk0 (v / u) (div_ne_zero hv hu)) :
    PGL(2, 𝕜)), ⟨?_, ?_, ?_⟩, ?_⟩
  · simp [mul_smul, h0]
  · rw [mul_smul, pglFixingZeroInftyEquiv_symm_smul_infty, hinf]
  · rw [mfderiv_mul_pglFixingZeroInftyEquiv_symm_zero]
    exact div_mul_cancel₀ v hu
  · rintro g ⟨hg0, hginf, hgv⟩
    obtain ⟨a, rfl⟩ := hfix g hg0 hginf
    rw [mfderiv_mul_pglFixingZeroInftyEquiv_symm_zero] at hgv
    have ha : a = Units.mk0 (v / u) (div_ne_zero hv hu) := Units.ext (eq_div_of_mul_eq hu hgv)
    rw [ha]

end OnePoint
