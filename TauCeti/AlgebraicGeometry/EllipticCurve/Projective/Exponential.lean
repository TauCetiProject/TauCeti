/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.InvariantDifferential
public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Holomorphic
public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.TangentLattice
public import TauCeti.Topology.Separation.TypeTags
import TauCeti.Geometry.Lie.Exponential.Classification
import TauCeti.Geometry.Lie.Exponential.Derivative.Basic
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible

/-!
# The exponential map of a complex elliptic curve

The points `E(ℂ)` of an elliptic curve over `ℂ` form a compact commutative complex Lie group
(`WeierstrassCurve.Projective.Point.instLieAddGroup`), built from the projective Weierstrass
equation. This file constructs its **exponential map** `exp_E : ℂ →+ E(ℂ)` from the flows of
invariant vector fields, normalized by the local parameter `-X / Y` at the origin, and develops its
local theory intrinsically, without the Weierstrass uniformization.

Regard `E(ℂ)` as a real Lie group by restricting scalars
(`WeierstrassCurve.Projective.Point.instLieGroupMultiplicativeReal`). A tangent vector `v` at the
origin generates a translation-invariant vector field; its flow for time one carries the origin to
a point `exp v`. This tangent-space exponential is canonical, and holomorphic
(`TauCeti.contMDiff_mulInvariantExp_complex`), but expressing its domain as `ℂ` requires a
coordinate on the tangent space at the origin. The differential of the local parameter
`t = -X / Y` at the origin (`WeierstrassCurve.Projective.Point.localParameter`) supplies one,
intrinsic to the Weierstrass equation: the tangent-space exponential has derivative the identity at
`0` (`TauCeti.hasFDerivAt_extChartAt_mulInvariantExp_zero_complex`) and `t` is a local coordinate
at the origin (`WeierstrassCurve.Projective.isLocalDiffeomorphAt_localParameter_zero`), so `exp_E`
is the tangent-space exponential in the coordinate along which `t` has derivative `1` at `0`
(`WeierstrassCurve.Projective.hasDerivAt_localParameter_exp`). As the invariant differential is
`(1 + O(t)) dt`, this is the classical normalization under which `exp_E` pulls the invariant
differential back to `dz` (`WeierstrassCurve.Projective.pullback_invariantDifferential_exp`).

An additive homomorphism `g : ℂ → E(ℂ)` with `(t ∘ g)'(0) = 1` is automatically continuous:
the normalization confines the cluster points of `g` at `0` to a finite set (the finite affine
fibre `x = 0` together with the origin), and compactness and divisibility then show that the
origin is the only one.
It is then determined by this normalization
(`WeierstrassCurve.Projective.eq_exp_of_hasDerivAt`): its restrictions to the real lines through `0`
are continuous one-parameter subgroups, hence exponentials of tangent vectors
(`exists_eq_mulInvariantOneParameterSubgroup`), and the derivative of `t ∘ g` at `0` recovers those
vectors. A change of variables `C` with scaling factor `u` multiplies the local parameter by `u` to
first order at the origin, as the coordinate `Z / Y` of the chart at infinity vanishes to second
order there (`WeierstrassCurve.Projective.Point.hasMFDerivAt_affineChart_apply_one_zero`). So the
inverse point map `(Point.addEquivVariableChange E C).symm` from `E(ℂ)` to `(C • E)(ℂ)` sends
`exp_E (u⁻¹ z)` to `exp_{C • E} z` (`WeierstrassCurve.Projective.exp_variableChange`).

The comparison with the Weierstrass uniformization, the period lattice as kernel and the global
structure of `exp_E` are in `TauCeti.Analysis.SpecialFunctions.Elliptic.Exponential`.

## Main definitions

* `WeierstrassCurve.Projective.exp`: the exponential map `exp_E : ℂ →+ E(ℂ)`.

## Main results

* `WeierstrassCurve.Projective.exists_exp_eq_mulInvariantExp_rescale`: `exp_E` is a rescaling of
  the tangent-space exponential of the underlying real Lie group.
* `WeierstrassCurve.Projective.hasDerivAt_localParameter_exp`: along `exp_E`, the local parameter
  `-X / Y` has derivative `1` at `0`.
* `WeierstrassCurve.Projective.eq_exp_of_hasDerivAt`: `exp_E` is the only additive homomorphism
  with this normalization; continuity follows from it.
* `WeierstrassCurve.Projective.contMDiff_exp`: `exp_E` is holomorphic.
* `WeierstrassCurve.Projective.isInvertible_mfderiv_exp` and
  `WeierstrassCurve.Projective.isLocalDiffeomorphAt_exp`: the derivative of `exp_E` is invertible at
  every point, so `exp_E` is a local biholomorphism.
* `WeierstrassCurve.Projective.isOpenMap_exp` and `WeierstrassCurve.Projective.exp_surjective`:
  `exp_E` is an open map, onto `E(ℂ)` once `E(ℂ)` is known to be connected.
* `WeierstrassCurve.Projective.pullback_invariantDifferential_exp`: the global holomorphic,
  nowhere-zero invariant differential pulls back to `dz`.
* `WeierstrassCurve.Projective.mvfderiv_eq_invariantDifferential_of_exp_comp_eventuallyEq_id`:
  a continuous local inverse of `exp_E` integrates the invariant differential.
* `WeierstrassCurve.Projective.exp_variableChange`: the rescaling of `exp_E` under a change of
  variables.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, §IV.1 and §VI.5.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 20.
-/

public section

open Filter Topology Matrix Projectivization
open scoped ContDiff Manifold

namespace WeierstrassCurve.Projective

/-! ### The exponential map -/

variable (W : Projective ℂ) [W.IsElliptic]

/-- The tangent-space exponential of `E(ℂ)`, for the identification of the tangent space at the
origin with `ℂ` given by the chart at the origin: the exponential homomorphism of the real Lie
group `E(ℂ)` on its tangent space (`TauCeti.mulInvariantExpAddMonoidHom`). -/
private noncomputable def tangentExp : ℂ →+ W.Point :=
  (AddEquiv.additiveMultiplicative W.Point).toAddMonoidHom.comp
    (TauCeti.mulInvariantExpAddMonoidHom 𝓘(ℝ, ℂ) (Multiplicative W.Point))

private theorem coe_tangentExp : ⇑W.tangentExp =
    Multiplicative.toAdd ∘ Additive.toMul ∘
      TauCeti.mulInvariantExpAddMonoidHom 𝓘(ℝ, ℂ) (Multiplicative W.Point) := by
  funext v
  simp [tangentExp]

/-- The value of `tangentExp` at `v` is the time-one value of the flow of the invariant vector
field generated by `v`. -/
private theorem tangentExp_apply (v : ℂ) : W.tangentExp v =
    (mulInvariantExp (I := 𝓘(ℝ, ℂ)) (G := Multiplicative W.Point)
      (v : GroupLieAlgebra 𝓘(ℝ, ℂ) (Multiplicative W.Point))).toAdd := by
  rw [coe_tangentExp, Function.comp_apply, Function.comp_apply,
    TauCeti.mulInvariantExpAddMonoidHom_apply, toMul_ofMul]

private theorem contMDiff_tangentExp (n : ℕ∞ω) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) n W.tangentExp := by
  have h : ⇑W.tangentExp = fun v : ℂ ↦
      (mulInvariantExp (I := 𝓘(ℝ, ℂ)) (G := Multiplicative W.Point)
        (v : GroupLieAlgebra 𝓘(ℝ, ℂ) (Multiplicative W.Point))).toAdd :=
    funext W.tangentExp_apply
  rw [h]
  exact Multiplicative.contMDiff_toAdd.comp
    (TauCeti.contMDiff_mulInvariantExp_complex (E := ℂ) (G := Multiplicative W.Point) n)

/-- The derivative at `0` of the local parameter along `tangentExp`. -/
private noncomputable def tangentScale : ℂ :=
  deriv (fun v ↦ (W.tangentExp v).localParameter) 0

private theorem hasDerivAt_localParameter_tangentExp :
    HasDerivAt (fun v ↦ (W.tangentExp v).localParameter) W.tangentScale 0 := by
  refine DifferentiableAt.hasDerivAt ?_
  have h := (Point.contMDiffAt_localParameter_zero (W := W) 1).comp_of_eq
    ((W.contMDiff_tangentExp 1).contMDiffAt (x := 0)) (map_zero _)
  exact mdifferentiableAt_iff_differentiableAt.mp (h.mdifferentiableAt one_ne_zero)

/-- In the chart at the origin, `tangentExp` has derivative the identity at `0`. -/
private theorem hasMFDerivAt_tangentExp_zero :
    HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) W.tangentExp 0 (ContinuousLinearMap.id ℂ ℂ) := by
  refine ⟨(W.contMDiff_tangentExp 0).continuous.continuousAt, ?_⟩
  have h := TauCeti.hasFDerivAt_extChartAt_mulInvariantExp_zero_complex (E := ℂ)
    (G := Multiplicative W.Point)
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, map_zero, modelWithCornersSelf_coe,
    Set.range_id, hasFDerivWithinAt_univ, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
    Function.comp_id, id_eq]
  -- The type tag `Multiplicative` keeps the charts of `W.Point`, and the tangent spaces of the
  -- model space `ℂ` are `ℂ` itself.
  convert h using 1
  · funext v
    rw [Function.comp_apply, tangentExp_apply]
    rfl
  · rfl

variable {W} in
/-- The derivative of the local parameter along `tangentExp` does not vanish: `tangentExp` has
derivative the identity at `0`, and the local parameter is a local coordinate at the origin. -/
private theorem tangentScale_ne_zero : W.tangentScale ≠ 0 := by
  have hd := W.hasMFDerivAt_tangentExp_zero
  have ht : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) Point.localParameter (W.tangentExp 0) := by
    rw [map_zero]
    exact (Point.contMDiffAt_localParameter_zero (W := W) 1).mdifferentiableAt one_ne_zero
  have hinj : Function.Injective (mfderiv 𝓘(ℂ) 𝓘(ℂ) Point.localParameter (W.tangentExp 0)) := by
    rw [map_zero]
    exact ((W.isLocalDiffeomorphAt_localParameter_zero (n := 1)).isInvertible_mfderiv
      one_ne_zero).injective
  -- The tangent vector `1` at `0 : ℂ`.
  let v : TangentSpace 𝓘(ℂ) (0 : ℂ) := (1 : ℂ)
  have hκ : mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun v ↦ (W.tangentExp v).localParameter) 0 v =
      W.tangentScale := by
    rw [← mvfderiv_apply_eq_mfderiv_apply, TauCeti.mvfderiv_eq_fderiv_apply,
      W.hasDerivAt_localParameter_tangentExp.hasFDerivAt.fderiv,
      ContinuousLinearMap.toSpanSingleton_apply (R₁ := ℂ) (r := v), smul_eq_mul (α := ℂ) v,
      one_mul]
  have h1 := TauCeti.mfderiv_apply_mfderiv_of_eventuallyEq_comp
    (κ := fun v ↦ (W.tangentExp v).localParameter) (.of_forall fun _ ↦ rfl) ht
    hd.mdifferentiableAt v
  rw [hκ, hd.mfderiv] at h1
  intro h0
  -- `v` is the complex number `1`, sent to `0` by the injective derivative.
  exact one_ne_zero (α := ℂ) (hinj (h1.trans (h0.trans
    (map_zero (mfderiv 𝓘(ℂ) 𝓘(ℂ) Point.localParameter (W.tangentExp 0))).symm)))

/-- A continuous homomorphism `g : ℂ → E(ℂ)` along which the local parameter has derivative `1`
at `0` is `z ↦ tangentExp (z / c)`, where `c ≠ 0` is the derivative of the local parameter along
`tangentExp`. -/
private theorem eq_tangentExp_rescale {g : ℂ →+ W.Point} (hg : Continuous g)
    (h : HasDerivAt (fun z ↦ (g z).localParameter) 1 0) (w : ℂ) :
    g w = W.tangentExp (W.tangentScale⁻¹ * w) := by
  -- Along the real line through `w`, `g` is a one-parameter subgroup `t ↦ tangentExp (t v)`.
  have key : ∀ w : ℂ, ∃ v : ℂ, (∀ t : ℝ, g (t * w) = W.tangentExp (t * v)) ∧
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
      rw [tangentExp_apply]
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
  obtain ⟨v, hline, hv⟩ := key w
  simpa [← hv, inv_mul_cancel_left₀ W.tangentScale_ne_zero] using hline 1

/-- **The exponential map `exp_E : ℂ → E(ℂ)` of a complex elliptic curve.** It is the time-one
flow from the origin of the invariant vector fields of `E(ℂ)`
(`WeierstrassCurve.Projective.exists_exp_eq_mulInvariantExp_rescale`), with tangent vectors at the
origin measured by the local parameter `-X / Y`
(`WeierstrassCurve.Projective.hasDerivAt_localParameter_exp`). -/
noncomputable def exp : ℂ →+ W.Point :=
  W.tangentExp.comp (AddMonoidHom.mulLeft W.tangentScale⁻¹)

/-- The nonzero derivative rules out the junk values of the local parameter near zero.
Every cluster point therefore lies over the finite affine fibre `x = 0`, or is the origin. -/
private theorem mem_finite_fiber_of_mapClusterPt {g : ℂ →+ W.Point}
    (h : HasDerivAt (fun z ↦ (g z).localParameter) 1 0) {P : W.Point}
    (hP : MapClusterPt P (𝓝[≠] 0) g) :
    P ∈ {Q | (Point.toAffineAddEquiv W Q).xRep 0 = 0} ∪ {0} := by
  obtain ⟨F, hF, hg⟩ := mapClusterPt_iff_ultrafilter.1 hP
  obtain ⟨s, hs, he⟩ := Point.exists_contMDiffAt_mk_eq P
  have hcoord : Tendsto (fun z ↦ s (g z)) F (𝓝 (s P)) := hs.continuousAt.tendsto.comp hg
  have ht : Tendsto (fun z ↦ (g z).localParameter) F (𝓝 0) := by
    simpa using h.continuousAt.tendsto.mono_left (hF.trans nhdsWithin_le_nhds)
  have heq : (fun z ↦ s (g z) 0) =ᶠ[F]
      fun z ↦ -(g z).localParameter * s (g z) 1 := by
    filter_upwards [hg.eventually he, (h.eventually_ne one_ne_zero (c := 0)).filter_mono hF]
      with z ⟨hz, hez⟩ hne
    have htval : (g z).localParameter = -(s (g z) 0 / s (g z) 1) := by
      simpa only [Point.localParameter_mk] using congrArg Point.localParameter hez.symm
    rw [htval] at hne ⊢
    have hY : s (g z) 1 ≠ 0 := by
      intro hzero
      exact hne (by simp [hzero])
    simp [hY]
  have hX : s P 0 = 0 := by
    have h0 := ht.neg.mul (hcoord.apply_nhds 1)
    simpa using tendsto_nhds_unique_of_eventuallyEq (hcoord.apply_nhds 0) h0 heq
  obtain ⟨hns, hrep⟩ := he.self_of_nhds
  rw [← hrep]
  by_cases hZ : s P 2 = 0
  · right
    apply (Point.toAffineAddEquiv W).injective
    simp [Point.toAffineAddEquiv_apply, Point.toAffineLift_eq,
      Point.toAffine_of_Z_eq_zero hZ, Point.toAffineLift_zero]
  · left
    simp [Point.toAffineAddEquiv_apply, Point.toAffineLift_eq,
      Point.toAffine_of_Z_ne_zero hns hZ, Affine.Point.xRep_some, hX]

/-- The finite fibre gives a uniform integer annihilating every cluster point: the multiples of a
cluster point at `0` are again cluster points there, so they lie in the finite fibre, and the
factorial of its size annihilates every cluster point whose multiples remain in that fibre. -/
private theorem exists_nsmul_mapClusterPt_eq_zero {g : ℂ →+ W.Point}
    (h : HasDerivAt (fun z ↦ (g z).localParameter) 1 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ P, MapClusterPt P (𝓝[≠] 0) g → N • P = 0 := by
  let S : Set W.Point := {Q | (Point.toAffineAddEquiv W Q).xRep 0 = 0} ∪ {0}
  have hS : S.Finite := ((W.toAffine.finite_preimage_xRep0 0).preimage
    (Point.toAffineAddEquiv W).injective.injOn).union (Set.finite_singleton 0)
  refine ⟨S.ncard.factorial, Nat.factorial_pos _, fun P hP ↦ ?_⟩
  have hmul : ∀ n : ℕ, n • P ∈ S := by
    intro n
    by_cases hn : n = 0
    · simp [hn, S]
    have hc := hP.continuousAt_comp (continuous_nsmul n).continuousAt
    have hscale : Tendsto (fun z : ℂ ↦ n • z) (𝓝[≠] 0) (𝓝[≠] 0) := by
      simpa [nsmul_eq_mul] using ((hasDerivAt_id (0 : ℂ)).const_mul (n : ℂ)).tendsto_nhdsNE
        (by simpa using hn)
    apply W.mem_finite_fiber_of_mapClusterPt h
    exact (hc.congrFun (Eventually.of_forall fun z ↦ (g.map_nsmul (n := n) z).symm)).of_comp hscale
  have hsub : (AddSubmonoid.multiples P : Set W.Point) ⊆ S := by
    rintro Q ⟨n, rfl⟩
    exact hmul n
  have hfin := hS.subset hsub
  have hord := finite_multiples.1 hfin
  apply addOrderOf_dvd_iff_nsmul_eq_zero.1
  apply Nat.dvd_factorial hord.addOrderOf_pos
  rw [← Nat.card_addSubmonoidMultiples]
  exact Set.ncard_le_ncard hsub hS

/-- Normalization of an additive homomorphism already forces continuity. Compactness produces
cluster points of `g(z/N)`; the uniform annihilator forces their `N`-fold multiples to be zero. -/
private theorem continuous_of_hasDerivAt_localParameter {g : ℂ →+ W.Point}
    (h : HasDerivAt (fun z ↦ (g z).localParameter) 1 0) : Continuous g := by
  obtain ⟨N, hN, hkill⟩ := W.exists_nsmul_mapClusterPt_eq_zero h
  have hlim : Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (0 : W.Point)) := by
    apply tendsto_nhds_of_unique_mapClusterPt
    intro P hP
    obtain ⟨F, hF, hg⟩ := mapClusterPt_iff_ultrafilter.1 hP
    obtain ⟨Q, hQ⟩ := exists_clusterPt_of_compactSpace
      (Filter.map (fun z : ℂ ↦ g (z / N)) F)
    have hscale : Tendsto (fun z : ℂ ↦ z / N) F (𝓝[≠] 0) := by
      simpa using (((hasDerivAt_id (0 : ℂ)).div_const (N : ℂ)).tendsto_nhdsNE
        (by simpa using hN.ne')).mono_left hF
    have hQc : MapClusterPt Q F (fun z : ℂ ↦ g (z / N)) := hQ
    have hQ0 := hkill Q (hQc.of_comp hscale)
    have hQP := hQc.continuousAt_comp (continuous_nsmul N).continuousAt
    have heq : (fun P : W.Point ↦ N • P) ∘ (fun z : ℂ ↦ g (z / N)) = g := by
      funext z
      rw [Function.comp_apply, ← map_nsmul, nsmul_eq_mul,
        mul_div_cancel₀ _ (by exact_mod_cast hN.ne')]
    rw [heq] at hQP
    have hEq : N • Q = P := eq_of_nhds_neBot
      (hQP.clusterPt.neBot.mono (inf_le_inf_left _ hg))
    exact hEq.symm.trans hQ0
  apply continuous_of_continuousAt_zero g
  apply continuousAt_iff_punctured_nhds.2
  simpa only [map_zero] using hlim

/-- **`exp_E` is the only normalized additive homomorphism**: a homomorphism
`g : ℂ → E(ℂ)` along which the local parameter `-X / Y` has derivative `1` at `0` is `exp_E`.
Continuity follows from the derivative hypothesis and compactness of `E(ℂ)`. -/
theorem eq_exp_of_hasDerivAt {g : ℂ →+ W.Point}
    (h : HasDerivAt (fun z ↦ (g z).localParameter) 1 0) : g = W.exp :=
  AddMonoidHom.ext (W.eq_tangentExp_rescale (W.continuous_of_hasDerivAt_localParameter h) h)

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

/-- **`exp_E` is a time-one flow of invariant vector fields**: for some `c ∈ ℂˣ` it is
`z ↦ exp (c z)`, where `exp` is the tangent-space exponential of `E(ℂ)` regarded as a real Lie
group, with tangent space at the origin identified with `ℂ` by the chart there. -/
theorem exists_exp_eq_mulInvariantExp_rescale :
    ∃ c : ℂˣ, ∀ z, W.exp z = (mulInvariantExp (I := 𝓘(ℝ, ℂ)) (G := Multiplicative W.Point)
      ((c * z : ℂ) : GroupLieAlgebra 𝓘(ℝ, ℂ) (Multiplicative W.Point))).toAdd :=
  ⟨Units.mk0 _ (inv_ne_zero W.tangentScale_ne_zero), fun _ ↦ W.tangentExp_apply _⟩

/-- **The normalization of `exp_E`**: along `exp_E`, the local parameter `-X / Y` at the origin
has derivative `1` at `0`. -/
theorem hasDerivAt_localParameter_exp :
    HasDerivAt (fun z ↦ (W.exp z).localParameter) 1 0 := by
  have h := W.hasDerivAt_localParameter_tangentExp.comp_of_eq (0 : ℂ)
    ((hasDerivAt_id (0 : ℂ)).const_mul W.tangentScale⁻¹) (by simp)
  rwa [mul_one, mul_inv_cancel₀ W.tangentScale_ne_zero] at h

/-- The invariant differential inverts the derivative of `exp_E` at every point. -/
@[simp]
theorem invariantDifferential_apply_mfderiv_exp (z : ℂ) (v : TangentSpace 𝓘(ℂ) z) :
    W.invariantDifferential (W.exp z) (mfderiv 𝓘(ℂ) 𝓘(ℂ) W.exp z v) =
      NormedSpace.fromTangentSpace z v := by
  have hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun P : W.Point ↦ P - W.exp z) :=
    (contMDiff_id.sub contMDiff_const).mdifferentiable (n := 1) one_ne_zero
  have ht := (Point.contMDiffAt_localParameter_zero (W := W) 1).mdifferentiableAt one_ne_zero
  have hs : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun P : W.Point ↦ (P - W.exp z).localParameter) (W.exp z) :=
    ht.comp_of_eq (W.exp z) (hτ _) (sub_self _)
  have hc : HasDerivAt
      ((fun P : W.Point ↦ (P - W.exp z).localParameter) ∘ W.exp) 1 z := by
    simpa only [Function.comp_def, ← map_sub, id_eq, mul_one] using
      W.hasDerivAt_localParameter_exp.comp_of_eq z ((hasDerivAt_id z).sub_const z) (by simp)
  -- The tangent vector `v` is a complex number; the explicit `ℂ` arguments let the rewrites
  -- treat it as one.
  rw [invariantDifferential_apply, ← mvfderiv_comp_apply z hs (W.mdifferentiable_exp z),
    TauCeti.mvfderiv_eq_fderiv_apply, hc.hasFDerivAt.fderiv,
    ContinuousLinearMap.toSpanSingleton_apply (R₁ := ℂ) (r := v),
    smul_eq_mul (α := ℂ) v, mul_one (M := ℂ) v,
    NormedSpace.fromTangentSpace_apply]

/-- **The derivative of `exp_E` is invertible** at every point: the invariant differential
inverts it, so it is injective. -/
theorem isInvertible_mfderiv_exp (z : ℂ) :
    (mfderiv 𝓘(ℂ) 𝓘(ℂ) W.exp z).IsInvertible :=
  (TauCeti.isInvertible_mfderiv_iff_injective rfl).2 fun v w h ↦
    (NormedSpace.fromTangentSpace z).injective <| by
      rw [← W.invariantDifferential_apply_mfderiv_exp, ← W.invariantDifferential_apply_mfderiv_exp,
        h]

/-- The exponential is locally biholomorphic, by its invertible derivative: it is a local
diffeomorphism of class `C^n` for every `n`, including `n = ω`. -/
theorem isLocalDiffeomorphAt_exp {n : ℕ∞ω} (z : ℂ) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) n W.exp z := by
  obtain ⟨e, he⟩ := W.isInvertible_mfderiv_exp z
  exact (TauCeti.isLocalDiffeomorphAt_of_mfderiv_eq (n := ω) (W.contMDiff_exp ω).contMDiffOn
    isOpen_univ (Set.mem_univ z) (by exact BoundarylessManifold.isInteriorPoint)
    (by exact le_top) he).of_le le_top

/-- **Local logarithms integrate the invariant differential**: if `g` is continuous at `Q` and
inverts `exp_E` near `Q`, its differential at `Q` is the invariant differential at `Q`. No
differentiability of `g` is assumed: it follows from the local invertibility of `exp_E`. -/
theorem mvfderiv_eq_invariantDifferential_of_exp_comp_eventuallyEq_id {g : W.Point → ℂ}
    {Q : W.Point} (hg : ContinuousAt g Q) (hid : W.exp ∘ g =ᶠ[𝓝 Q] id) :
    mvfderiv 𝓘(ℂ) g Q = W.invariantDifferential Q := by
  have hmd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g Q := by
    have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 (W.exp ∘ g) Q :=
      contMDiffAt_id.congr_of_eventuallyEq hid
    have hi : ContMDiffWithinAt 𝓘(ℂ) 𝓘(ℂ) 1 g Set.univ Q :=
      hcomp.contMDiffWithinAt.of_comp_isLocalDiffeomorph
        (W.isLocalDiffeomorphAt_exp (n := 1) (g Q)) hg.continuousWithinAt
    exact hi.contMDiffAt (by simp) |>.mdifferentiableAt one_ne_zero
  apply ContinuousLinearMap.ext
  intro v
  have hv := TauCeti.mfderiv_apply_mfderiv_of_eventuallyEq_comp hid
    (W.mdifferentiable_exp (g Q)) hmd v
  rw [mfderiv_id, ContinuousLinearMap.id_apply] at hv
  have hω := W.invariantDifferential_apply_mfderiv_exp (g Q) (mfderiv 𝓘(ℂ) 𝓘(ℂ) g Q v)
  have hQ : W.exp (g Q) = Q := hid.self_of_nhds
  rw [hQ] at hω
  rw [mvfderiv_apply_eq_mfderiv_apply]
  exact hω.symm.trans (congrArg (W.invariantDifferential Q) hv)

/-- `exp_E` is `tangentExp` after the rescaling `z ↦ c⁻¹ z` by the nonzero `tangentScale`. -/
private theorem coe_exp : ⇑W.exp = W.tangentExp ∘ Homeomorph.mulLeft₀ W.tangentScale⁻¹
    (inv_ne_zero W.tangentScale_ne_zero) := by
  rw [Homeomorph.coe_mulLeft₀, exp, AddMonoidHom.coe_comp, AddMonoidHom.coe_mulLeft]

/-- `exp_E` is an open map. -/
theorem isOpenMap_exp : IsOpenMap W.exp := by
  rw [coe_exp, coe_tangentExp]
  exact (isOpenMap_toAdd.comp (isOpenMap_toMul.comp
    (TauCeti.isOpenMap_mulInvariantExpAddMonoidHom (I := 𝓘(ℝ, ℂ))
      (G := Multiplicative W.Point)))).comp (Homeomorph.isOpenMap _)

/-- **`exp_E` is surjective** when `E(ℂ)` is preconnected (as it always is, by
`WeierstrassCurve.Projective.Point.instConnectedSpace`): the exponential of a preconnected
commutative Lie group is surjective (`TauCeti.lieExp_surjective_of_preconnectedSpace`). -/
theorem exp_surjective [PreconnectedSpace W.Point] : Function.Surjective W.exp := by
  have : PreconnectedSpace (Multiplicative W.Point) := inferInstanceAs (PreconnectedSpace W.Point)
  rw [coe_exp, coe_tangentExp]
  exact (Multiplicative.toAdd.surjective.comp (Additive.toMul.surjective.comp
    (TauCeti.mulInvariantExpAddMonoidHom_surjective (I := 𝓘(ℝ, ℂ))
      (G := Multiplicative W.Point)))).comp (Homeomorph.surjective _)

/-- **The global pullback identity `exp_E*ω = dz`.** -/
@[simp]
theorem pullback_invariantDifferential_exp :
    W.invariantDifferential.pullback W.exp = mvfderiv 𝓘(ℂ) id := by
  funext z
  apply ContinuousLinearMap.ext
  intro v
  -- As a complex number, `v` is fixed by the identity of `ℂ`.
  rw [TauCeti.RiemannSurface.OneForm.pullback_apply, TauCeti.mvfderiv_eq_fderiv_apply, fderiv_id,
    ContinuousLinearMap.id_apply (R₁ := ℂ) (M₁ := ℂ) v, W.invariantDifferential_apply_mfderiv_exp,
    NormedSpace.fromTangentSpace_apply]

/-! ### Rescaling under a change of variables -/

section VariableChange

/-- In the chart at infinity, for `C⁻¹ = (u', r', s', t')`, the function
`-(u'²a + r'b) / (u'²s'a + u'³ + t'b)` has derivative `1 / u' = C.u` at `0` along a curve through
the origin with `a' = -1` and `b' = 0`. -/
private theorem hasDerivAt_localParameter_chartAtInfinity (C : VariableChange ℂ) {a b : ℂ → ℂ}
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

/-- On the affine chart `Y = 1`, with coordinates `a = X / Y` and `b = Z / Y`, the inverse change
of variables `C` gives a point the local parameter `-(u'²a + r'b) / (u'²s'a + u'³ + t'b)`, for
`C⁻¹ = (u', r', s', t')`: this is
`WeierstrassCurve.Projective.Point.localParameter_addEquivVariableChange_symm_mk` at the
coordinates `[a : 1 : b]`. -/
private theorem localParameter_addEquivVariableChange_symm_of_mem_affineOpen
    {E : WeierstrassCurve ℂ} (C : VariableChange ℂ) {P : E.toProjective.Point}
    (hP : P.toProjectivization ∈ affineOpen 1) :
    ((Point.addEquivVariableChange E C).symm P).localParameter =
      -(((C⁻¹.u : ℂ) ^ 2 * affineChart 1 P.toProjectivization 0 +
          C⁻¹.r * affineChart 1 P.toProjectivization 1) /
        ((C⁻¹.u : ℂ) ^ 2 * C⁻¹.s * affineChart 1 P.toProjectivization 0 + (C⁻¹.u : ℂ) ^ 3 +
          C⁻¹.t * affineChart 1 P.toProjectivization 1)) := by
  obtain ⟨v, hv⟩ := Quotient.exists_rep P.point
  have hns : E.toProjective.NonsingularLift ⟦v⟧ := hv.symm ▸ P.nonsingular
  obtain rfl : Point.mk hns = P := Point.ext hv
  rw [Point.toProjectivization_mk, mk_mem_affineOpen_iff] at hP
  rw [Point.localParameter_addEquivVariableChange_symm_mk, Point.toProjectivization_mk,
    affineChart_mk, ← mul_div_mul_left _ _ (inv_ne_zero hP)]
  congr 2 <;> simp [Fin.succAbove_ne_zero_zero, div_eq_inv_mul] <;> field_simp

/-- **Rescaling naturality of the exponential map**: after a change of variables `C` with
scaling factor `u`, the exponential map of `C • E` sends `z` to the image of `exp_E (u⁻¹ z)`
under the inverse point map `(Point.addEquivVariableChange E C).symm` from `E(ℂ)` to `(C • E)(ℂ)`.
-/
theorem exp_variableChange (E : WeierstrassCurve ℂ) [E.IsElliptic] (C : VariableChange ℂ)
    (z : ℂ) :
    (C • E).toProjective.exp z =
      (Point.addEquivVariableChange E C).symm (E.toProjective.exp ((C.u : ℂ)⁻¹ * z)) := by
  let W := E.toProjective
  -- The coordinates `X / Y` and `Z / Y` of `exp_E` in the affine chart `Y = 1`.
  let a : ℂ → ℂ := fun z ↦ affineChart 1 (W.exp z).toProjectivization 0
  let b : ℂ → ℂ := fun z ↦ affineChart 1 (W.exp z).toProjectivization 1
  have hmem : ∀ᶠ z in 𝓝 (0 : ℂ), (W.exp z).toProjectivization ∈ affineOpen 1 :=
    (Point.continuous_toProjectivization.comp W.continuous_exp).continuousAt.preimage_mem_nhds
      (by
        simpa using (isOpen_affineOpen 1).mem_nhds
          (Point.toProjectivization_zero_mem_affineOpen (W := W)))
  have ha : HasDerivAt a (-1) 0 := by
    have h := W.hasDerivAt_localParameter_exp.neg
    rw [Point.localParameter_eq_neg_affineChart] at h
    simpa only [Pi.neg_def, neg_neg] using h
  have hb : HasDerivAt b 0 0 := by
    have hm : HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (fun P : W.Point ↦ affineChart 1 P.toProjectivization 1)
        (W.exp 0) 0 := by
      rw [map_zero]
      exact Point.hasMFDerivAt_affineChart_apply_one_zero
    have hc := hasMFDerivAt_iff_hasFDerivAt.mp (hm.comp 0 (W.mdifferentiable_exp 0).hasMFDerivAt)
    rw [ContinuousLinearMap.zero_comp] at hc
    exact hasDerivAt_iff_hasFDerivAt.mpr (by rwa [ContinuousLinearMap.toSpanSingleton_zero])
  have hab0 : a 0 = 0 ∧ b 0 = 0 := by
    simp [a, b, Point.toProjectivization_zero, affineChart_mk]
  -- Along `exp_E`, the local parameter of `C • E` has derivative `C.u` at `0`.
  have hf : HasDerivAt (fun z ↦ ((Point.addEquivVariableChange E C).symm
      (W.exp z)).localParameter) (C.u : ℂ) 0 :=
    (hasDerivAt_localParameter_chartAtInfinity C ha hb hab0.1 hab0.2).congr_of_eventuallyEq
      (hmem.mono fun _ hz ↦ localParameter_addEquivVariableChange_symm_of_mem_affineOpen C hz)
  let g : ℂ →+ (C • E).toProjective.Point :=
    ((Point.addEquivVariableChange E C).symm.toAddMonoidHom.comp W.exp).comp
      (AddMonoidHom.mulLeft ((C.u : ℂ)⁻¹))
  have hcomp := hf.comp_of_eq (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).const_mul ((C.u : ℂ)⁻¹))
    (by simp)
  rw [mul_one, mul_inv_cancel₀ C.u.ne_zero] at hcomp
  exact (DFunLike.congr_fun (eq_exp_of_hasDerivAt _ (g := g) hcomp) z).symm

/-- After a change of variables `C` with scaling factor `u`, the point map
`Point.addEquivVariableChange E C` from `(C • E)(ℂ)` to `E(ℂ)` sends `exp_{C • E} z` to
`exp_E (u⁻¹ z)`. -/
theorem addEquivVariableChange_exp (E : WeierstrassCurve ℂ) [E.IsElliptic]
    (C : VariableChange ℂ) (z : ℂ) :
    Point.addEquivVariableChange E C ((C • E).toProjective.exp z) =
      E.toProjective.exp ((C.u : ℂ)⁻¹ * z) := by
  rw [exp_variableChange, AddEquiv.apply_symm_apply]

end VariableChange

end WeierstrassCurve.Projective
