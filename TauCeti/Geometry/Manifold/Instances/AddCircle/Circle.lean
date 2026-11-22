/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import TauCeti.Geometry.Diffeomorphism.Sphere
import TauCeti.Geometry.Manifold.Instances.Sphere
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# The circle `AddCircle p` as the unit circle of `ℂ`

For a positive real `p`, Mathlib's map `AddCircle.toCircle : AddCircle p → Circle` sends the class
of `t` to `exp (2π i t / p)` on the unit circle `S¹ ⊆ ℂ`, and is a homeomorphism
(`AddCircle.homeomorphCircle`). Here `AddCircle p` carries the smooth structure whose charts
are local real lifts (`AddCircle.instIsManifold`), and `Circle` carries Mathlib's smooth
structure as the unit sphere of `ℂ`, modelled on `EuclideanSpace ℝ (Fin 1)`. This file shows that
the two smooth structures agree: `toCircle` is an analytic diffeomorphism
(`AddCircle.diffeomorphCircle p n : AddCircle p ≃ₘ^n⟮𝓘(ℝ), 𝓡 1⟯ Circle`, for every smoothness
exponent `n`). Followed by the standard coordinates `ℂ ≅ ℝ²`, it identifies `AddCircle p` with
the unit circle of the Euclidean plane (`AddCircle.diffeomorphSphere`), the case `n = 1` of the
spheres `Sⁿ = sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1`.

Composed with the quotient map `ℝ → AddCircle p`, the map `toCircle` is the rescaled standard
parametrization `t ↦ exp (2π i t / p)` of the circle (`AddCircle.toCircle_apply_mk`). This
parametrization is analytic and its differential never vanishes, because its velocity
`(2π / p) i exp (2π i t / p)` in `ℂ` is nonzero. By the inverse function theorem it is therefore a
local diffeomorphism, and since the quotient map is a local diffeomorphism, so is `toCircle`.
Being bijective, it is a diffeomorphism.

This identification lets the time form `dt_p` of `AddCircle p` and the angular form `dθ` of the unit
circle be compared, which is done in `TauCeti.Geometry.Manifold.DeRham.Circle`.

## Main declarations

* `AddCircle.contMDiff_toCircle`: `toCircle` is `C^n` for every `n`.
* `AddCircle.diffeomorphCircle p n`: `toCircle` as a `C^n` diffeomorphism
  `AddCircle p ≃ₘ^n⟮𝓘(ℝ), 𝓡 1⟯ Circle`.
* `AddCircle.diffeomorphSphere p n`: the `C^n` diffeomorphism from `AddCircle p` to the unit circle
  of `ℝ²` sending the class of `t` to `(cos (2π t / p), sin (2π t / p))`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 4 (the inverse function theorem for manifolds and
  local diffeomorphisms) and Chapter 21 (smooth covering maps).
-/

public section

noncomputable section

open Set Function TauCeti
open scoped Manifold ContDiff Real

namespace AddCircle

attribute [local instance] finrank_real_complex_fact'

variable (p : ℝ) [Fact (0 < p)]

omit [Fact (0 < p)] in
/-- The rescaled standard parametrization `t ↦ exp (2π i t / p)` of the unit circle is
analytic. -/
private theorem contMDiff_circleExp_const_mul (n : ℕ∞ω) :
    ContMDiff 𝓘(ℝ) (𝓡 1) n fun t : ℝ ↦ Circle.exp (2 * π / p * t) :=
  contMDiff_circleExp.comp (contDiff_const.mul contDiff_id).contMDiff

/-- The rescaled standard parametrization `t ↦ exp (2π i t / p)` of the unit circle has injective
differential at every point: it is `Circle.exp`, whose differential is injective, after
multiplication by `2π / p ≠ 0`. -/
private theorem injective_mfderiv_circleExp_const_mul (t : ℝ) :
    Injective (mfderiv 𝓘(ℝ) (𝓡 1) (fun s : ℝ ↦ Circle.exp (2 * π / p * s)) t) := by
  set c : ℝ := 2 * π / p
  have hc : c ≠ 0 := div_ne_zero (by positivity) (Fact.out : 0 < p).ne'
  have hd : mfderiv 𝓘(ℝ) (𝓡 1) (fun s : ℝ ↦ Circle.exp (c * s)) t =
      (mfderiv 𝓘(ℝ) (𝓡 1) Circle.exp (c * t)).comp (c • ContinuousLinearMap.id ℝ ℝ) :=
    ((contMDiff_circleExp.mdifferentiableAt (n := 1) one_ne_zero).hasMFDerivAt.comp t
      ((hasFDerivAt_id t).const_mul c).hasMFDerivAt).mfderiv
  rw [hd]
  -- The composite acts as `Circle.exp`'s differential after multiplication by `c`.
  exact (injective_mfderiv_circleExp (c * t)).comp (smul_right_injective ℝ hc)

/-- The map `toCircle : AddCircle p → Circle` is `C^n` for every `n`. -/
theorem contMDiff_toCircle (n : ℕ∞ω) :
    ContMDiff 𝓘(ℝ) (𝓡 1) n (toCircle : AddCircle p → Circle) := by
  rw [← (isLocalDiffeomorph_coe p n).contMDiff_comp_iff QuotientAddGroup.mk_surjective le_rfl]
  -- Read on `ℝ`, `toCircle` is the rescaled parametrization `t ↦ exp (2π i t / p)`.
  exact (contMDiff_circleExp_const_mul p n).congr toCircle_apply_mk

/-- The map `toCircle : AddCircle p → Circle` is a `C^n` local diffeomorphism for every `n ≥ 1`:
its lift `t ↦ exp (2π i t / p)` has nowhere vanishing differential. -/
private theorem isLocalDiffeomorph_toCircle {n : ℕ∞ω} (hn : 1 ≤ n) :
    IsLocalDiffeomorph 𝓘(ℝ) (𝓡 1) n (toCircle : AddCircle p → Circle) := by
  intro x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact isLocalDiffeomorphAt_of_eqOn_comp (s := univ) isOpen_univ (mem_univ t)
    (ModelWithCorners.isInteriorPoint_iff.mpr (by simp)) hn
    (fun s _ ↦ toCircle_apply_mk s) (contMDiff_circleExp_const_mul p n).contMDiffOn
    (injective_mfderiv_circleExp_const_mul p t) (by simp) (isLocalDiffeomorph_coe p n t)

/-- The inverse of the homeomorphism `toCircle : AddCircle p ≃ₜ Circle` is `C^n` for every `n`: it
is the inverse of the analytic diffeomorphism built from the bijective local diffeomorphism
`toCircle`. -/
private theorem contMDiff_homeomorphCircle_symm (n : ℕ∞ω) :
    ContMDiff (𝓡 1) 𝓘(ℝ) n (homeomorphCircle (Fact.out : 0 < p).ne').symm := by
  have hbij : Bijective (toCircle : AddCircle p → Circle) :=
    funext (homeomorphCircle_apply (Fact.out : 0 < p).ne') ▸ (homeomorphCircle _).bijective
  have hf := isLocalDiffeomorph_toCircle p (n := ω) le_top
  have hD : ⇑(homeomorphCircle (Fact.out : 0 < p).ne').symm =
      (hf.diffeomorphOfBijective hbij).symm := by
    funext y
    refine hbij.injective ?_
    rw [← homeomorphCircle_apply (Fact.out : 0 < p).ne', Homeomorph.apply_symm_apply]
    exact ((congrFun (hf.coe_diffeomorphOfBijective hbij) _).symm.trans
      ((hf.diffeomorphOfBijective hbij).apply_symm_apply y)).symm
  rw [hD]
  exact (hf.diffeomorphOfBijective hbij).symm.contMDiff.of_le le_top

/-- The **identification of `AddCircle p` with the unit circle** `S¹ ⊆ ℂ`, as a `C^n`
diffeomorphism: the map `toCircle`, sending the class of `t` to `exp (2π i t / p)`. Its underlying
homeomorphism is Mathlib's `AddCircle.homeomorphCircle`. -/
def diffeomorphCircle (n : ℕ∞ω) : AddCircle p ≃ₘ^n⟮𝓘(ℝ), 𝓡 1⟯ Circle where
  toEquiv := (homeomorphCircle (Fact.out : 0 < p).ne').toEquiv
  contMDiff_toFun := by
    rw [Homeomorph.coe_toEquiv, funext (homeomorphCircle_apply _)]
    exact contMDiff_toCircle p n
  contMDiff_invFun := contMDiff_homeomorphCircle_symm p n

/-- The underlying map of `diffeomorphCircle p n` is `AddCircle.toCircle`. -/
@[simp]
theorem coe_diffeomorphCircle (n : ℕ∞ω) : ⇑(diffeomorphCircle p n) = toCircle :=
  funext (homeomorphCircle_apply _)

/-- The inverse of `diffeomorphCircle p n` is the inverse of the homeomorphism
`AddCircle.homeomorphCircle`. In particular it does not depend on `n`. -/
@[simp]
theorem coe_diffeomorphCircle_symm (n : ℕ∞ω) :
    ⇑(diffeomorphCircle p n).symm = (homeomorphCircle (Fact.out : 0 < p).ne').symm := (rfl)

/-- The diffeomorphism `diffeomorphCircle p n` sends the class of `t` to `exp (2π i t / p)`. -/
theorem diffeomorphCircle_apply_mk (n : ℕ∞ω) (t : ℝ) :
    diffeomorphCircle p n t = Circle.exp (2 * π / p * t) := by
  rw [coe_diffeomorphCircle, toCircle_apply_mk]

/-- The underlying homeomorphism of `diffeomorphCircle p n` is `AddCircle.homeomorphCircle`. -/
@[simp]
theorem toHomeomorph_diffeomorphCircle (n : ℕ∞ω) :
    (diffeomorphCircle p n).toHomeomorph = homeomorphCircle (Fact.out : 0 < p).ne' := (rfl)

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

/-- The **identification of `AddCircle p` with the unit circle of `ℝ²`**, as a `C^n`
diffeomorphism: `AddCircle.diffeomorphCircle` followed by the standard coordinates
`z ↦ (re z, im z)` of `ℂ`, so the class of `t` goes to `(cos (2π t / p), sin (2π t / p))`
(`AddCircle.coe_diffeomorphSphere_mk`). -/
def diffeomorphSphere (n : ℕ∞ω) :
    AddCircle p ≃ₘ^n⟮𝓘(ℝ), 𝓡 1⟯ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  -- `Circle` is by definition the unit sphere of `ℂ`, with the same smooth structure, as in
  -- `TauCeti.EuclideanSpace.sphereIsometryEquivCircle`.
  (diffeomorphCircle p n).trans (Complex.orthonormalBasisOneI.repr.unitSphereDiffeomorph n)

/-- The diffeomorphism `diffeomorphSphere p n` sends `θ` to the coordinates of `toCircle θ ∈ ℂ`. -/
@[simp]
theorem coe_diffeomorphSphere_apply (n : ℕ∞ω) (θ : AddCircle p) :
    (diffeomorphSphere p n θ : EuclideanSpace ℝ (Fin 2)) =
      Complex.orthonormalBasisOneI.repr (toCircle θ : ℂ) := by
  rw [← coe_diffeomorphCircle p n]
  -- The value of the composite is that of the linear isometry at `diffeomorphCircle p n θ`, read
  -- in `ℂ` through the identification of `Circle` with the unit sphere of `ℂ`.
  exact LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply (n := 1) (k := 1) (m := n) _ _

/-- The diffeomorphism `diffeomorphSphere p n` sends the class of `t` to
`(cos (2π t / p), sin (2π t / p))`. -/
theorem coe_diffeomorphSphere_mk (n : ℕ∞ω) (t : ℝ) :
    (diffeomorphSphere p n t : EuclideanSpace ℝ (Fin 2)) =
      !₂[Real.cos (2 * π / p * t), Real.sin (2 * π / p * t)] := by
  rw [coe_diffeomorphSphere_apply, toCircle_apply_mk, Circle.coe_exp]
  ext i
  fin_cases i
  · simpa only [Complex.orthonormalBasisOneI_repr_apply, Fin.zero_eta, Matrix.cons_val_zero]
      using Complex.exp_ofReal_mul_I_re _
  · simpa only [Complex.orthonormalBasisOneI_repr_apply, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
      using Complex.exp_ofReal_mul_I_im _

end AddCircle
