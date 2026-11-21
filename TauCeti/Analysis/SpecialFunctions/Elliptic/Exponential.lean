/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Quotient
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.LieGroup
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.LocalParameter
public import TauCeti.Analysis.SpecialFunctions.Elliptic.Period.Lattice
public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Basic
public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Holomorphic
public import TauCeti.Geometry.Manifold.Algebra.TypeTags
public import TauCeti.Topology.Separation.TypeTags
import TauCeti.Analysis.SpecialFunctions.Elliptic.Topology
import TauCeti.Geometry.Lie.Exponential.Classification
import TauCeti.Topology.Algebra.ContinuousMonoidHom.QuotientKerEquiv

/-!
# The exponential map of a complex elliptic curve

The points `E(ℂ)` of an elliptic curve over `ℂ` form a compact connected commutative complex Lie
group (`WeierstrassCurve.Projective.Point.instLieAddGroup`), built from the projective Weierstrass
equation. This file constructs its **exponential map** `exp_E : ℂ →+ E(ℂ)` from the flows of
invariant vector fields, normalized by the local parameter `-X / Y` at the origin, and identifies it
with the Weierstrass uniformization: its kernel is the period lattice of `E`.

Regard `E(ℂ)` as a real Lie group by restricting scalars. A tangent vector `v` at the origin
generates a translation-invariant vector field; its flow for time one carries the origin to a point
`exp v`, and `v ↦ exp v` is a holomorphic group homomorphism
(`TauCeti.contMDiff_mulInvariantExp_complex`). The tangent space at the origin is identified with
`ℂ` through the chart of `E(ℂ)` at the origin, which is not canonical, so this map is only defined
up to a rescaling `v ↦ c v`. The local parameter `t = -X / Y` at the origin
(`WeierstrassCurve.Projective.Point.localParameter`) removes this ambiguity: `exp_E` is the
rescaling along which `t` has derivative `1` at `0`
(`WeierstrassCurve.Projective.hasDerivAt_localParameter_exp`). As the invariant differential is
`(1 + O(t)) dt`, this is the classical normalization under which `exp_E` pulls the invariant
differential back to `dz`; differential forms themselves are not used here.

A continuous homomorphism `g : ℂ → E(ℂ)` is determined by `t ∘ g` to first order at `0`
(`WeierstrassCurve.Projective.eq_exp_of_hasDerivAt`): its restrictions to the real lines through `0`
are continuous one-parameter subgroups, hence exponentials of tangent vectors
(`exists_eq_mulInvariantOneParameterSubgroup`), and the derivative of `t ∘ g` at `0` recovers those
vectors. The Weierstrass point map `z ↦ (℘(z), ℘'(z) / 2)` of a period pair `L` is such a
homomorphism, and in the chart at infinity `t = -2 ℘ / ℘'` has derivative `1` at `0`. So the
exponential map of the curve `E_Λ` of `Λ` is the Weierstrass point map
(`WeierstrassCurve.Projective.exp_weierstrassCurve`); more generally, after any change of variables
`C` with scaling factor `u`, `exp_{C • E_Λ}(z)` is the image of the point of `u⁻¹ z`
(`WeierstrassCurve.Projective.exp_variableChange_weierstrassCurve`). Since every complex elliptic
curve `E` is the image of `E_Λ` for `Λ = E.periodLattice` under a change of variables with `u = 1`,
the kernel of `exp_E` is `E.periodLattice` (`WeierstrassCurve.Projective.ker_exp`).

The general theory of the exponential map of a commutative real Lie group gives the global structure
of `exp_E`: it is an open map, onto since `E(ℂ)` is connected, and with discrete kernel a covering
map, inducing an isomorphism of topological groups `ℂ / ker exp_E ≃ E(ℂ)`.

## Main definitions

* `WeierstrassCurve.Projective.exp`: the exponential map `exp_E : ℂ →+ E(ℂ)`.
* `WeierstrassCurve.Projective.expQuotientKerContinuousAddEquiv`: the induced isomorphism of
  topological groups `ℂ / ker exp_E ≃ₜ+ E(ℂ)`.

## Main results

* `WeierstrassCurve.Projective.exists_exp_eq_mulInvariantExp`: `exp_E` is a rescaling of the
  tangent-space exponential of the underlying real Lie group.
* `WeierstrassCurve.Projective.hasDerivAt_localParameter_exp`: along `exp_E`, the local parameter
  `-X / Y` has derivative `1` at `0`.
* `WeierstrassCurve.Projective.eq_exp_of_hasDerivAt`: `exp_E` is the only continuous homomorphism
  with this normalization.
* `WeierstrassCurve.Projective.contMDiff_exp`: `exp_E` is holomorphic.
* `WeierstrassCurve.Projective.exp_weierstrassCurve` and
  `WeierstrassCurve.Projective.exp_variableChange_weierstrassCurve`: the comparison with the
  Weierstrass point map `z ↦ (℘(z), ℘'(z) / 2)`.
* `WeierstrassCurve.Projective.ker_exp`: the kernel of `exp_E` is the period lattice of `E`.
* `WeierstrassCurve.Projective.exp_surjective`, `WeierstrassCurve.Projective.isOpenMap_exp` and
  `WeierstrassCurve.Projective.isCoveringMap_exp`: `exp_E` is an open covering map onto `E(ℂ)`.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, §IV.1 and §VI.5.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 20.
-/

public section

open Filter Topology
open scoped ContDiff Manifold

namespace WeierstrassCurve.Projective

/-! ### The exponential map -/

variable (W : Projective ℂ) [W.IsElliptic]

/-- **The points of a complex elliptic curve form a real Lie group**: the complex Lie group
`W.Point`, written multiplicatively, with scalars restricted to `ℝ`. -/
instance (n : ℕ∞ω) : LieGroup 𝓘(ℝ, ℂ) n (Multiplicative W.Point) :=
  LieGroup.restrictScalars_self (𝕜 := ℂ) ℝ

/-- The tangent-space exponential of `E(ℂ)`, for the identification of the tangent space at the
origin with `ℂ` given by the chart at the origin: the time-one value of the flow of the invariant
vector field generated by `v`. -/
private noncomputable def tangentExp (v : ℂ) : W.Point :=
  (mulInvariantExp (I := 𝓘(ℝ, ℂ)) (G := Multiplicative W.Point)
    (v : GroupLieAlgebra 𝓘(ℝ, ℂ) (Multiplicative W.Point))).toAdd

private theorem tangentExp_add (v w : ℂ) : W.tangentExp (v + w) = W.tangentExp v + W.tangentExp w :=
  congrArg Multiplicative.toAdd (GroupLieAlgebra.mulInvariantExp_add (I := 𝓘(ℝ, ℂ))
    (G := Multiplicative W.Point) v w)

private theorem tangentExp_zero : W.tangentExp 0 = 0 :=
  congrArg Multiplicative.toAdd (mulInvariantExp_zero (I := 𝓘(ℝ, ℂ))
    (G := Multiplicative W.Point))

private theorem contMDiff_tangentExp (n : ℕ∞ω) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) n W.tangentExp :=
  -- The type tag `Multiplicative W.Point` carries the charts of `W.Point`
  -- (`Multiplicative.chartedSpace`), and `Multiplicative.toAdd` is the identity on points.
  TauCeti.contMDiff_mulInvariantExp_complex (E := ℂ) (G := Multiplicative W.Point) n

/-- The derivative at `0` of the local parameter along `tangentExp`. -/
private noncomputable def tangentScale : ℂ :=
  deriv (fun v ↦ (W.tangentExp v).localParameter) 0

private theorem hasDerivAt_localParameter_tangentExp :
    HasDerivAt (fun v ↦ (W.tangentExp v).localParameter) W.tangentScale 0 := by
  refine DifferentiableAt.hasDerivAt ?_
  have h := (Point.contMDiffAt_localParameter_zero (W := W) 1).comp_of_eq
    ((W.contMDiff_tangentExp 1).contMDiffAt (x := 0)) W.tangentExp_zero
  exact mdifferentiableAt_iff_differentiableAt.mp (h.mdifferentiableAt one_ne_zero)

/-- A continuous homomorphism `g : ℂ → E(ℂ)` along which the local parameter has derivative `1`
at `0` is `z ↦ tangentExp (z / c)`, where `c ≠ 0` is the derivative of the local parameter along
`tangentExp`. -/
private theorem tangentScale_ne_zero_and_eq_tangentExp {g : ℂ →+ W.Point} (hg : Continuous g)
    (h : HasDerivAt (fun z ↦ (g z).localParameter) 1 0) :
    W.tangentScale ≠ 0 ∧ ∀ w, g w = W.tangentExp (W.tangentScale⁻¹ * w) := by
  -- Along the real line through `w`, `g` is a one-parameter subgroup `t ↦ tangentExp (t v)`.
  have key : ∀ w, ∃ v : ℂ, (∀ t : ℝ, g (t * w) = W.tangentExp (t * v)) ∧
      W.tangentScale * v = w := by
    intro w
    let φ : ContinuousMonoidHom (Multiplicative ℝ) (Multiplicative W.Point) :=
      { toFun t := Multiplicative.ofAdd (g (t.toAdd * w))
        map_one' := by simp
        map_mul' s t := by simp [add_mul]
        continuous_toFun := continuous_ofAdd.comp (hg.comp
          ((Complex.continuous_ofReal.comp continuous_toAdd).mul continuous_const)) }
    obtain ⟨v, hv⟩ := exists_eq_mulInvariantOneParameterSubgroup (I := 𝓘(ℝ, ℂ)) φ
    -- The Lie algebra is the tangent space `ℂ` at the origin, with its real scalar action.
    let e := groupLieAlgebraEquivModelVectorSpace (I := 𝓘(ℝ, ℂ)) (G := Multiplicative W.Point)
    have hline : ∀ t : ℝ, g (t * w) = W.tangentExp (t * e v) := fun t ↦ by
      have := DFunLike.congr_fun hv (Multiplicative.ofAdd t)
      rw [mulInvariantOneParameterSubgroup_eq_mulInvariantExp_smul, ← e.symm_apply_apply v,
        ← e.symm.map_smul, Complex.real_smul] at this
      exact congrArg Multiplicative.toAdd this
    refine ⟨e v, hline, ?_⟩
    -- Compare the derivatives at `0` of the local parameter along this line.
    have h₁ : HasDerivAt (fun t : ℝ ↦ (g (t * w)).localParameter) w 0 := by
      have := (h.comp_of_eq (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).mul_const w) (by simp)).comp_ofReal
      simpa using this
    have h₂ : HasDerivAt (fun t : ℝ ↦ (W.tangentExp (t * e v)).localParameter)
        (W.tangentScale * e v) 0 := by
      have := (W.hasDerivAt_localParameter_tangentExp.comp_of_eq (0 : ℂ)
        ((hasDerivAt_id (0 : ℂ)).mul_const (e v)) (by simp)).comp_ofReal
      simpa using this
    simp_rw [hline] at h₁
    exact h₂.unique h₁
  obtain ⟨v₁, -, hv₁⟩ := key 1
  have hc : W.tangentScale ≠ 0 := left_ne_zero_of_mul_eq_one hv₁
  refine ⟨hc, fun w ↦ ?_⟩
  obtain ⟨v, hline, hv⟩ := key w
  simpa [← hv, inv_mul_cancel_left₀ hc] using hline 1

/-- **The exponential map `exp_E : ℂ → E(ℂ)` of a complex elliptic curve.** It is the time-one
flow from the origin of the invariant vector fields of `E(ℂ)`
(`WeierstrassCurve.Projective.exists_exp_eq_mulInvariantExp`), with tangent vectors at the origin
measured by the local parameter `-X / Y`
(`WeierstrassCurve.Projective.hasDerivAt_localParameter_exp`). -/
noncomputable def exp : ℂ →+ W.Point where
  toFun z := W.tangentExp (W.tangentScale⁻¹ * z)
  map_zero' := by rw [mul_zero, tangentExp_zero]
  map_add' z w := by rw [mul_add, tangentExp_add]

/-- **`exp_E` is the only normalized continuous homomorphism**: a continuous homomorphism
`g : ℂ → E(ℂ)` along which the local parameter `-X / Y` has derivative `1` at `0` is `exp_E`. -/
theorem eq_exp_of_hasDerivAt {g : ℂ →+ W.Point} (hg : Continuous g)
    (h : HasDerivAt (fun z ↦ (g z).localParameter) 1 0) : g = W.exp :=
  AddMonoidHom.ext fun w ↦ (W.tangentScale_ne_zero_and_eq_tangentExp hg h).2 w

/-- **`exp_E` is holomorphic**: it is `C^n` over `ℂ` for every `n`, including `n = ω`. -/
theorem contMDiff_exp (n : ℕ∞ω) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) n W.exp :=
  (W.contMDiff_tangentExp n).comp (contDiff_const.mul contDiff_id).contMDiff

/-- `exp_E` is holomorphic. -/
theorem mdifferentiable_exp : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) W.exp :=
  (W.contMDiff_exp 1).mdifferentiable one_ne_zero

/-- `exp_E` is continuous. -/
@[fun_prop]
theorem continuous_exp : Continuous W.exp :=
  (W.contMDiff_exp 0).continuous

/-! ### Comparison with the Weierstrass point map -/

section Comparison

variable (L : PeriodPair) (C : VariableChange ℂ)

/-- The Weierstrass point map of `L`, carried to the curve `C • E_Λ` and precomposed with the
rescaling by `C.u⁻¹`. -/
private noncomputable def weierstrassPointVariableChange :
    ℂ →+ (C • L.weierstrassCurve).toProjective.Point :=
  ((Point.addEquivVariableChange L.weierstrassCurve C).symm.toAddMonoidHom.comp
    ((Point.toAffineAddEquiv L.weierstrassCurve.toProjective).symm.toAddMonoidHom.comp
      L.weierstrassPointHom)).comp (AddMonoidHom.mulLeft ((C.u : ℂ)⁻¹))

private theorem weierstrassPointVariableChange_apply (z : ℂ) :
    weierstrassPointVariableChange L C z = (Point.addEquivVariableChange L.weierstrassCurve C).symm
      (L.weierstrassPoint ((C.u : ℂ)⁻¹ * z)).toProjective := by
  simp [weierstrassPointVariableChange, PeriodPair.weierstrassPointHom_apply]

private theorem continuous_weierstrassPointVariableChange :
    Continuous (weierstrassPointVariableChange L C) := by
  simp_rw [funext (weierstrassPointVariableChange_apply L C),
    ← Point.coe_continuousAddEquivVariableChange_symm]
  exact (map_continuous _).comp
    (L.continuous_weierstrassPoint_toProjective.comp (continuous_const.mul continuous_id))

/-- In the chart at infinity, the local parameter of `C • E_Λ` at the point with homogeneous
coordinates `[a : 1 : b]` is `-(u'²a + r'b) / (u'²s'a + u'³ + t'b)`, for `C⁻¹ = (u', r', s', t')`.
Along a curve through the origin with `a' = -1` and `b' = 0` it has derivative `1 / u' = C.u`. -/
private theorem hasDerivAt_localParameter_chartAtInfinity {a b : ℂ → ℂ}
    (ha : HasDerivAt a (-1) 0) (hb : HasDerivAt b 0 0) (ha0 : a 0 = 0) (hb0 : b 0 = 0) :
    HasDerivAt (fun y ↦ -(((C⁻¹.u : ℂ) ^ 2 * a y + C⁻¹.r * b y) /
      ((C⁻¹.u : ℂ) ^ 2 * C⁻¹.s * a y + (C⁻¹.u : ℂ) ^ 3 + C⁻¹.t * b y))) (C.u : ℂ) 0 := by
  have hU : (C⁻¹.u : ℂ) ≠ 0 := (C⁻¹.u).ne_zero
  have hCU : (C.u : ℂ) = (C⁻¹.u : ℂ)⁻¹ := by simp [VariableChange.inv_def]
  have hN := (ha.const_mul ((C⁻¹.u : ℂ) ^ 2)).add (hb.const_mul C⁻¹.r)
  have hD := (((ha.const_mul ((C⁻¹.u : ℂ) ^ 2 * C⁻¹.s)).add_const ((C⁻¹.u : ℂ) ^ 3)).add
    (hb.const_mul C⁻¹.t))
  convert (hN.div hD (by simp [ha0, hb0, hU])).neg using 1
  simp only [Pi.add_apply, ha0, hb0]
  rw [hCU]
  field_simp
  ring

/-- Along the Weierstrass point map carried to `C • E_Λ`, the local parameter has derivative
`C.u` at `0`, so after the rescaling by `C.u⁻¹` it has derivative `1`. -/
private theorem hasDerivAt_localParameter_weierstrassPointVariableChange :
    HasDerivAt (fun z ↦ (weierstrassPointVariableChange L C z).localParameter) 1 0 := by
  have ha : HasDerivAt (fun z ↦ 2 * (L.weierstrassP z / L.derivWeierstrassP z)) (-1) 0 := by
    convert (L.hasDerivAt_weierstrassP_div_derivWeierstrassP (zero_mem _)).const_mul 2 using 1
    norm_num
  have hf := hasDerivAt_localParameter_chartAtInfinity C ha
    (by simpa using (L.hasDerivAt_inv_derivWeierstrassP (zero_mem _)).const_mul 2)
    (by simp) (by simp)
  have hcomp := hf.comp_of_eq (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).const_mul ((C.u : ℂ)⁻¹))
    (by simp)
  rw [mul_one, mul_inv_cancel₀ C.u.ne_zero] at hcomp
  refine hcomp.congr_of_eventuallyEq ?_
  have ht : Tendsto (fun z : ℂ ↦ (C.u : ℂ)⁻¹ * z) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 (0 : ℂ))).const_mul ((C.u : ℂ)⁻¹)
  filter_upwards [ht.eventually (L.eventually_mk_eq_weierstrassPoint_toProjective (zero_mem _))]
    with z ⟨_, hz⟩
  rw [weierstrassPointVariableChange_apply, ← hz,
    Point.localParameter_addEquivVariableChange_symm_mk]
  simp

/-- Along the Weierstrass point map, the local parameter `-2 ℘ / ℘'` has derivative `1` at
`0`. -/
private theorem hasDerivAt_localParameter_weierstrassPoint :
    HasDerivAt (fun z ↦ (L.weierstrassPoint z).toProjective.localParameter) 1 0 := by
  have h : HasDerivAt (fun z ↦ -2 * (L.weierstrassP z / L.derivWeierstrassP z)) 1 0 := by
    convert (L.hasDerivAt_weierstrassP_div_derivWeierstrassP (zero_mem _)).const_mul (-2) using 1
    norm_num
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [L.eventually_mk_eq_weierstrassPoint_toProjective (zero_mem _)] with z ⟨_, hz⟩
  rw [← hz, Point.localParameter_mk]
  simp

end Comparison

variable {W} in
/-- The derivative of the local parameter along `tangentExp` does not vanish, as some normalized
continuous homomorphism exists: the Weierstrass point map, carried to `W`. -/
private theorem tangentScale_ne_zero : W.tangentScale ≠ 0 := by
  obtain ⟨L, C, -, rfl⟩ := WeierstrassCurve.exists_periodPair_variableChange_smul_eq W
  exact (tangentScale_ne_zero_and_eq_tangentExp _
    (continuous_weierstrassPointVariableChange L C)
    (hasDerivAt_localParameter_weierstrassPointVariableChange L C)).1

/-- **`exp_E` is a time-one flow of invariant vector fields**: for some `c ∈ ℂˣ` it is
`z ↦ exp (c z)`, where `exp` is the tangent-space exponential of `E(ℂ)` regarded as a real Lie
group, with tangent space at the origin identified with `ℂ` by the chart there. -/
theorem exists_exp_eq_mulInvariantExp :
    ∃ c : ℂˣ, ∀ z, W.exp z = (mulInvariantExp (I := 𝓘(ℝ, ℂ)) (G := Multiplicative W.Point)
      ((c * z : ℂ) : GroupLieAlgebra 𝓘(ℝ, ℂ) (Multiplicative W.Point))).toAdd :=
  ⟨Units.mk0 _ (inv_ne_zero W.tangentScale_ne_zero), fun _ ↦ (rfl)⟩

/-- **The normalization of `exp_E`**: along `exp_E`, the local parameter `-X / Y` at the origin
has derivative `1` at `0`. -/
theorem hasDerivAt_localParameter_exp :
    HasDerivAt (fun z ↦ (W.exp z).localParameter) 1 0 := by
  have h := W.hasDerivAt_localParameter_tangentExp.comp_of_eq (0 : ℂ)
    ((hasDerivAt_id (0 : ℂ)).const_mul W.tangentScale⁻¹) (by simp)
  rwa [mul_one, mul_inv_cancel₀ W.tangentScale_ne_zero] at h

/-- **The exponential map of a lattice curve is the Weierstrass point map**:
`exp_{E_Λ}(z) = (℘(z), ℘'(z) / 2)`, the point at infinity for `z ∈ Λ`. -/
theorem exp_weierstrassCurve (L : PeriodPair) (z : ℂ) :
    L.weierstrassCurve.toProjective.exp z = (L.weierstrassPoint z).toProjective := by
  let g : ℂ →+ L.weierstrassCurve.toProjective.Point :=
    (Point.toAffineAddEquiv L.weierstrassCurve.toProjective).symm.toAddMonoidHom.comp
      L.weierstrassPointHom
  have hg : ⇑g = fun z ↦ (L.weierstrassPoint z).toProjective :=
    funext fun z ↦ by simp [g, PeriodPair.weierstrassPointHom_apply]
  have h := eq_exp_of_hasDerivAt _ (g := g)
    (by rw [hg]; exact L.continuous_weierstrassPoint_toProjective)
    (by rw [hg]; exact hasDerivAt_localParameter_weierstrassPoint L)
  rw [← h, hg]

/-- **Rescaling naturality of the exponential map**: after a change of variables `C` with scaling
factor `u`, the exponential map of `C • E_Λ` sends `z` to the image under `C` of the point
`(℘(u⁻¹ z), ℘'(u⁻¹ z) / 2)` of `E_Λ`. -/
theorem exp_variableChange_weierstrassCurve (L : PeriodPair) (C : VariableChange ℂ) (z : ℂ) :
    (C • L.weierstrassCurve).toProjective.exp z =
      (Point.addEquivVariableChange L.weierstrassCurve C).symm
        (L.weierstrassPoint ((C.u : ℂ)⁻¹ * z)).toProjective := by
  rw [← weierstrassPointVariableChange_apply, eq_exp_of_hasDerivAt _
    (continuous_weierstrassPointVariableChange L C)
    (hasDerivAt_localParameter_weierstrassPointVariableChange L C)]

/-- **The kernel of `exp_E` is the period lattice of `E`.** -/
theorem ker_exp : W.exp.ker = W.periodLattice.toAddSubgroup := by
  obtain ⟨L, C, hu, rfl⟩ := WeierstrassCurve.exists_periodPair_variableChange_smul_eq W
  rw [periodLattice_eq_iff.mpr ⟨C, hu, rfl⟩]
  classical
  ext z
  have h := (Point.toAffineAddEquiv L.weierstrassCurve.toProjective).symm.map_eq_zero_iff
    (x := L.weierstrassPoint z)
  rw [Point.toAffineAddEquiv_symm_apply] at h
  rw [AddMonoidHom.mem_ker, exp_variableChange_weierstrassCurve, hu, Units.val_one, inv_one,
    one_mul, AddEquivClass.map_eq_zero_iff, h, PeriodPair.weierstrassPoint_eq_zero_iff,
    Submodule.mem_toAddSubgroup]

/-- `exp_E` vanishes exactly on the period lattice of `E`. -/
@[simp]
theorem exp_eq_zero_iff {z : ℂ} : W.exp z = 0 ↔ z ∈ W.periodLattice := by
  rw [← AddMonoidHom.mem_ker, ker_exp, Submodule.mem_toAddSubgroup]

/-! ### Global structure of the exponential map -/

section Global

local instance : ConnectedSpace (Multiplicative W.Point) :=
  Homeomorph.ofAdd.connectedSpace_iff.mp inferInstance

/-- The real left-invariant derivations of `E(ℂ)` are identified with its tangent space `ℂ` at the
origin. -/
private noncomputable def derivationEquiv :
    ℂ ≃L[ℝ] LeftInvariantDerivation 𝓘(ℝ, ℂ) (Multiplicative W.Point) :=
  (leftInvariantDerivationEquivGroupLieAlgebra (I := 𝓘(ℝ, ℂ)) (G := Multiplicative W.Point)
    BoundarylessManifold.isInteriorPoint).symm.toContinuousLinearEquiv

private theorem coe_tangentExp : W.tangentExp =
    Multiplicative.toAdd ∘ lieExp (I := 𝓘(ℝ, ℂ)) (G := Multiplicative W.Point) ∘
      W.derivationEquiv := by
  funext v
  rw [Function.comp_apply, Function.comp_apply, lieExp_eq_mulInvariantExp, tangentExp]
  exact congrArg (fun v ↦ Multiplicative.toAdd
    (mulInvariantExp (I := 𝓘(ℝ, ℂ)) (G := Multiplicative W.Point) v))
    ((leftInvariantDerivationEquivGroupLieAlgebra (I := 𝓘(ℝ, ℂ)) (G := Multiplicative W.Point)
      BoundarylessManifold.isInteriorPoint).apply_symm_apply v).symm

/-- `exp_E` is `tangentExp` after the rescaling `z ↦ c⁻¹ z` by the nonzero `tangentScale`. -/
private theorem coe_exp : ⇑W.exp = W.tangentExp ∘ Homeomorph.mulLeft₀ W.tangentScale⁻¹
    (inv_ne_zero W.tangentScale_ne_zero) :=
  (rfl)

/-- **`exp_E` is surjective**, as `E(ℂ)` is connected. -/
theorem exp_surjective : Function.Surjective W.exp := by
  rw [coe_exp, coe_tangentExp]
  exact Multiplicative.toAdd.surjective.comp
    (((TauCeti.lieExp_surjective_of_preconnectedSpace (I := 𝓘(ℝ, ℂ))
      (G := Multiplicative W.Point)).comp (derivationEquiv W).surjective).comp
      (Homeomorph.surjective _))

/-- `exp_E` is an open map. -/
theorem isOpenMap_exp : IsOpenMap W.exp := by
  rw [coe_exp, coe_tangentExp]
  exact (isOpenMap_toAdd.comp ((TauCeti.isOpenMap_lieExp (I := 𝓘(ℝ, ℂ))
    (G := Multiplicative W.Point)).comp (derivationEquiv W).toHomeomorph.isOpenMap)).comp
    (Homeomorph.isOpenMap _)

/-- **`exp_E` is a covering map.** It is an open continuous surjective homomorphism with discrete
kernel. -/
theorem isCoveringMap_exp : IsCoveringMap W.exp := by
  have hd : IsDiscrete (W.exp.ker : Set ℂ) := by
    rw [ker_exp, Submodule.coe_toAddSubgroup]
    exact SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
  exact ((W.isOpenMap_exp.isQuotientMap W.continuous_exp
    W.exp_surjective).isAddQuotientCoveringMap_of_isDiscrete_ker_addMonoidHom hd).isCoveringMap

end Global

/-- **`E(ℂ)` is the quotient of `ℂ` by the kernel of `exp_E`**, as topological groups; that kernel
is the period lattice (`WeierstrassCurve.Projective.ker_exp`). -/
noncomputable def expQuotientKerContinuousAddEquiv : ℂ ⧸ W.exp.ker ≃ₜ+ W.Point :=
  ContinuousAddEquiv.quotientKerEquivOfSurjective W.exp
    (W.isOpenMap_exp.isStrictMap W.continuous_exp) W.exp_surjective

/-- The isomorphism `ℂ / ker exp_E ≃ₜ+ E(ℂ)` sends the class of `z` to `exp_E z`. -/
@[simp]
theorem expQuotientKerContinuousAddEquiv_mk (z : ℂ) :
    W.expQuotientKerContinuousAddEquiv (QuotientAddGroup.mk z) = W.exp z := by
  rw [expQuotientKerContinuousAddEquiv, ContinuousAddEquiv.quotientKerEquivOfSurjective_apply_mk]

/-- The inverse of `ℂ / ker exp_E ≃ₜ+ E(ℂ)` sends `exp_E z` to the class of `z`. -/
@[simp]
theorem expQuotientKerContinuousAddEquiv_symm_exp (z : ℂ) :
    W.expQuotientKerContinuousAddEquiv.symm (W.exp z) = QuotientAddGroup.mk z := by
  rw [ContinuousAddEquiv.symm_apply_eq, expQuotientKerContinuousAddEquiv_mk]

end WeierstrassCurve.Projective
