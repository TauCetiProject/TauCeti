/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.InvariantDifferential
public import TauCeti.Analysis.SpecialFunctions.Elliptic.Period.Lattice
public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Holomorphic
public import TauCeti.Geometry.Manifold.Algebra.Quotient
public import TauCeti.Topology.Separation.TypeTags
import TauCeti.Analysis.SpecialFunctions.Elliptic.AdditionTheorem
import TauCeti.Geometry.Lie.Exponential.Classification
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible
import TauCeti.Topology.Algebra.ContinuousMonoidHom.QuotientKerEquiv

/-!
# The exponential map of a complex elliptic curve

The points `E(ℂ)` of an elliptic curve over `ℂ` form a compact connected commutative complex Lie
group (`WeierstrassCurve.Projective.Point.instLieAddGroup`), built from the projective Weierstrass
equation. This file constructs its **exponential map** `exp_E : ℂ →+ E(ℂ)` from the flows of
invariant vector fields, normalized by the local parameter `-X / Y` at the origin, and identifies it
with the Weierstrass uniformization: its kernel is the period lattice of `E`.

Regard `E(ℂ)` as a real Lie group by restricting scalars
(`WeierstrassCurve.Projective.Point.instLieGroupMultiplicativeReal`). A tangent vector `v` at the
origin generates a translation-invariant vector field; its flow for time one carries the origin to
a point `exp v`. This tangent-space exponential is canonical, and holomorphic
(`TauCeti.contMDiff_mulInvariantExp_complex`), but expressing its domain as `ℂ` requires a
coordinate on the tangent space at the origin. The differential of the local parameter
`t = -X / Y` at the origin (`WeierstrassCurve.Projective.Point.localParameter`) supplies one,
intrinsic to the Weierstrass equation: `exp_E` is the tangent-space exponential in the coordinate
along which `t` has derivative `1` at `0`
(`WeierstrassCurve.Projective.hasDerivAt_localParameter_exp`). As the invariant differential is
`(1 + O(t)) dt`, this is the classical normalization under which `exp_E` pulls the invariant
differential back to `dz`. The global form
`WeierstrassCurve.Projective.invariantDifferential` is holomorphic and nowhere zero, and its
pullback is `dz` everywhere (`WeierstrassCurve.Projective.pullback_invariantDifferential_exp`).
On affine coordinate neighbourhoods with `2y + a₁x + a₃ ≠ 0` it agrees with
`dx / (2y + a₁x + a₃)`
(`WeierstrassCurve.Projective.invariantDifferential_eq_inv_smul_mvfderiv`).

An additive homomorphism `g : ℂ → E(ℂ)` with `(t ∘ g)'(0) = 1` is automatically continuous:
the normalization confines the cluster points of `g` at `0` to a finite set (the finite affine
fibre `x = 0` together with the origin), and compactness and divisibility then show that the
origin is the only one.
It is then determined by this normalization
(`WeierstrassCurve.Projective.eq_exp_of_hasDerivAt`): its restrictions to the real lines through `0`
are continuous one-parameter subgroups, hence exponentials of tangent vectors
(`exists_eq_mulInvariantOneParameterSubgroup`), and the derivative of `t ∘ g` at `0` recovers those
vectors. The Weierstrass point map of a period pair `L`, the affine point `(℘(z), ℘'(z) / 2)` off
the lattice and the point at infinity on it, is such a homomorphism, and in the chart at infinity
`t = -2 ℘ / ℘'` has derivative `1` at `0`. So the exponential map of the curve `E_Λ` of `Λ` is the
Weierstrass point map (`PeriodPair.exp_weierstrassCurve`). A change of variables `C` with scaling
factor `u` rescales the exponential map: the inverse point map
`(Point.addEquivVariableChange E C).symm` from `E(ℂ)` to `(C • E)(ℂ)` sends `exp_E (u⁻¹ z)` to
`exp_{C • E} z` (`WeierstrassCurve.Projective.exp_variableChange`). Since every complex elliptic
curve `E` is the image of `E_Λ` for `Λ = E.periodLattice` under a change of variables with `u = 1`,
the kernel of `exp_E` is `E.periodLattice` (`WeierstrassCurve.Projective.ker_exp`).

The general theory of the exponential map of a commutative real Lie group gives the global structure
of `exp_E`: it is an open map, onto since `E(ℂ)` is connected, and with discrete kernel a covering
map, inducing an isomorphism of topological groups `ℂ / ker exp_E ≃ E(ℂ)`, which is biholomorphic.

## Main definitions

* `WeierstrassCurve.Projective.exp`: the exponential map `exp_E : ℂ →+ E(ℂ)`.
* `WeierstrassCurve.Projective.expQuotientKerContinuousAddEquiv`: the induced isomorphism of
  topological groups `ℂ / ker exp_E ≃ₜ+ E(ℂ)`.

## Main results

* `WeierstrassCurve.Projective.exists_exp_eq_mulInvariantExp_rescale`: `exp_E` is a rescaling of
  the tangent-space exponential of the underlying real Lie group.
* `WeierstrassCurve.Projective.hasDerivAt_localParameter_exp`: along `exp_E`, the local parameter
  `-X / Y` has derivative `1` at `0`.
* `WeierstrassCurve.Projective.eq_exp_of_hasDerivAt`: `exp_E` is the only additive homomorphism
  with this normalization; continuity follows from it.
* `WeierstrassCurve.Projective.contMDiff_exp`: `exp_E` is holomorphic.
* `WeierstrassCurve.Projective.isInvertible_mfderiv_exp`: the derivative of `exp_E` is invertible
  at every point.
* `WeierstrassCurve.Projective.isLocalDiffeomorphAt_localParameter_zero`: the local parameter is a
  local coordinate at the origin.
* `PeriodPair.exp_weierstrassCurve` and `PeriodPair.exp_variableChange_weierstrassCurve`: the
  comparison with the Weierstrass point map.
* `WeierstrassCurve.Projective.exp_variableChange`: the rescaling of `exp_E` under a change of
  variables.
* `WeierstrassCurve.Projective.pullback_invariantDifferential_exp`: the global holomorphic,
  nowhere-zero invariant differential pulls back to `dz`; it is the only form doing so
  (`WeierstrassCurve.Projective.pullback_exp_eq_mvfderiv_id_iff`).
* `WeierstrassCurve.Projective.invariantDifferential_eq_inv_smul_mvfderiv`: its agreement with
  the algebraic differential `dx / (2y + a₁x + a₃)` on the affine locus where
  `2y + a₁x + a₃ ≠ 0`.
* `WeierstrassCurve.Projective.mvfderiv_localInverse_exp`: local inverses of `exp_E` integrate
  the invariant differential.
* `WeierstrassCurve.Projective.ker_exp` and `WeierstrassCurve.Projective.exp_eq_exp_iff`: the
  kernel of `exp_E` is the period lattice of `E`, so two points have the same image exactly when
  they differ by a period.
* `WeierstrassCurve.Projective.exp_surjective`, `WeierstrassCurve.Projective.isOpenMap_exp` and
  `WeierstrassCurve.Projective.isCoveringMap_exp`: `exp_E` is an open covering map onto `E(ℂ)`.
* `WeierstrassCurve.Projective.contMDiff_expQuotientKerContinuousAddEquiv` and
  `WeierstrassCurve.Projective.contMDiff_expQuotientKerContinuousAddEquiv_symm`: the isomorphism
  `ℂ / ker exp_E ≃ E(ℂ)` is biholomorphic.

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

/-- The real left-invariant derivations of `E(ℂ)` are identified with its tangent space `ℂ` at the
origin. -/
private noncomputable def derivationEquiv :
    ℂ ≃L[ℝ] LeftInvariantDerivation 𝓘(ℝ, ℂ) (Multiplicative W.Point) :=
  (leftInvariantDerivationEquivGroupLieAlgebra (I := 𝓘(ℝ, ℂ)) (G := Multiplicative W.Point)
    BoundarylessManifold.isInteriorPoint).symm.toContinuousLinearEquiv

/-- The tangent-space exponential of `E(ℂ)`, for the identification of the tangent space at the
origin with `ℂ` given by the chart at the origin: the exponential homomorphism of the real Lie
group `E(ℂ)` (`TauCeti.lieExpAddMonoidHom`), transported to the tangent space `ℂ`. -/
private noncomputable def tangentExp : ℂ →+ W.Point :=
  (AddEquiv.additiveMultiplicative W.Point).toAddMonoidHom.comp
    ((TauCeti.lieExpAddMonoidHom (I := 𝓘(ℝ, ℂ)) (G := Multiplicative W.Point)).comp
      (W.derivationEquiv : ℂ →+ LeftInvariantDerivation 𝓘(ℝ, ℂ) (Multiplicative W.Point)))

private theorem coe_tangentExp : ⇑W.tangentExp =
    Multiplicative.toAdd ∘ lieExp (I := 𝓘(ℝ, ℂ)) (G := Multiplicative W.Point) ∘
      W.derivationEquiv := by
  funext v
  simp only [tangentExp, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp,
    AddMonoidHom.coe_ofClass, Function.comp_apply, TauCeti.lieExpAddMonoidHom_apply,
    AddEquiv.additiveMultiplicative_apply, toMul_ofMul]

/-- The value of `tangentExp` at `v` is the time-one value of the flow of the invariant vector
field generated by `v`. -/
private theorem tangentExp_apply (v : ℂ) : W.tangentExp v =
    (mulInvariantExp (I := 𝓘(ℝ, ℂ)) (G := Multiplicative W.Point)
      (v : GroupLieAlgebra 𝓘(ℝ, ℂ) (Multiplicative W.Point))).toAdd := by
  rw [coe_tangentExp, Function.comp_apply, Function.comp_apply, lieExp_eq_mulInvariantExp]
  exact congrArg (fun v ↦ Multiplicative.toAdd
    (mulInvariantExp (I := 𝓘(ℝ, ℂ)) (G := Multiplicative W.Point) v))
    ((leftInvariantDerivationEquivGroupLieAlgebra (I := 𝓘(ℝ, ℂ)) (G := Multiplicative W.Point)
      BoundarylessManifold.isInteriorPoint).apply_symm_apply v)

private theorem contMDiff_tangentExp (n : ℕ∞ω) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) n W.tangentExp := by
  rw [show ⇑W.tangentExp = _ from funext W.tangentExp_apply]
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

/-- A continuous homomorphism `g : ℂ → E(ℂ)` along which the local parameter has derivative `1`
at `0` is `z ↦ tangentExp (z / c)`, where `c ≠ 0` is the derivative of the local parameter along
`tangentExp`. -/
private theorem tangentScale_ne_zero_and_eq_tangentExp_rescale {g : ℂ →+ W.Point}
    (hg : Continuous g) (h : HasDerivAt (fun z ↦ (g z).localParameter) 1 0) :
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
  obtain ⟨v₁, -, hv₁⟩ := key 1
  have hc : W.tangentScale ≠ 0 := left_ne_zero_of_mul_eq_one hv₁
  refine ⟨hc, fun w ↦ ?_⟩
  obtain ⟨v, hline, hv⟩ := key w
  simpa [← hv, inv_mul_cancel_left₀ hc] using hline 1

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
  let F := 𝓝[≠] (0 : ℂ) ⊓ comap g (𝓝 P)
  have : F.NeBot := neBot_inf_comap_iff_map.2 (by simpa [inf_comm] using hP.clusterPt.neBot)
  have hg : Tendsto g F (𝓝 P) := tendsto_comap.mono_left inf_le_right
  obtain ⟨s, hs, he⟩ := Point.exists_contMDiffAt_mk_eq P
  have hcoord : Tendsto (fun z ↦ s (g z)) F (𝓝 (s P)) := hs.continuousAt.tendsto.comp hg
  have ht : Tendsto (fun z ↦ (g z).localParameter) F (𝓝 0) := by
    simpa using h.continuousAt.tendsto.mono_left (inf_le_left.trans nhdsWithin_le_nhds)
  have heq : (fun z ↦ s (g z) 0) =ᶠ[F]
      fun z ↦ -(g z).localParameter * s (g z) 1 := by
    filter_upwards [hg.eventually he, (h.eventually_ne one_ne_zero (c := 0)).filter_mono
      inf_le_left] with z ⟨hz, hez⟩ hne
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
factorial of its size annihilates each of its points of finite order. -/
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
    let F := 𝓝[≠] (0 : ℂ) ⊓ comap g (𝓝 P)
    have : F.NeBot := neBot_inf_comap_iff_map.2 (by simpa [inf_comm] using hP.clusterPt.neBot)
    have hg : Tendsto g F (𝓝 P) := tendsto_comap.mono_left inf_le_right
    obtain ⟨Q, hQ⟩ := exists_clusterPt_of_compactSpace
      (Filter.map (fun z : ℂ ↦ g (z / N)) F)
    have hscale : Tendsto (fun z : ℂ ↦ z / N) F (𝓝[≠] 0) := by
      simpa using (((hasDerivAt_id (0 : ℂ)).div_const (N : ℂ)).tendsto_nhdsNE
        (by simpa using hN.ne')).mono_left inf_le_left
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
  AddMonoidHom.ext fun w ↦ (W.tangentScale_ne_zero_and_eq_tangentExp_rescale
    (W.continuous_of_hasDerivAt_localParameter h) h).2 w

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

open Matrix
open scoped PeriodPair

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

/-- In the chart at infinity, the local parameter of the point with homogeneous coordinates
`C⁻¹.toMatrix *ᵥ [a : 1 : b]` is `-(u'²a + r'b) / (u'²s'a + u'³ + t'b)`, for
`C⁻¹ = (u', r', s', t')`. Along a curve through the origin with `a' = -1` and `b' = 0` it has
derivative `1 / u' = C.u`. -/
private theorem hasDerivAt_localParameter_chartAtInfinity {a b : ℂ → ℂ}
    (ha : HasDerivAt a (-1) 0) (hb : HasDerivAt b 0 0) (ha0 : a 0 = 0) (hb0 : b 0 = 0) :
    HasDerivAt (fun y ↦ -((C⁻¹.toMatrix *ᵥ ![a y, 1, b y]) 0 /
      (C⁻¹.toMatrix *ᵥ ![a y, 1, b y]) 1)) (C.u : ℂ) 0 := by
  have hU : (C⁻¹.u : ℂ) ≠ 0 := (C⁻¹.u).ne_zero
  have hCU : (C.u : ℂ) = (C⁻¹.u : ℂ)⁻¹ := by simp [VariableChange.inv_def]
  have hN := (ha.const_mul ((C⁻¹.u : ℂ) ^ 2)).add (hb.const_mul C⁻¹.r)
  have hD := (((ha.const_mul ((C⁻¹.u : ℂ) ^ 2 * C⁻¹.s)).add_const ((C⁻¹.u : ℂ) ^ 3)).add
    (hb.const_mul C⁻¹.t))
  convert (hN.div hD (by simp [ha0, hb0, hU])).neg using 1
  · funext y
    simp [VariableChange.toMatrix_def, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · simp only [Pi.add_apply, ha0, hb0]
    rw [hCU]
    field_simp
    ring

/-- The Weierstrass point map in the chart at infinity: near `0`, the point
`(℘(z), ℘'(z) / 2)` has homogeneous coordinates `[a z : 1 : b z]` with `a = 2 ℘ / ℘'` and
`b = 2 / ℘'`, where `a(0) = b(0) = 0`, `a'(0) = -1` and `b'(0) = 0`. Carried to `C • E_Λ`, it has
local parameter `-(C⁻¹.toMatrix *ᵥ [a : 1 : b]) 0 / (C⁻¹.toMatrix *ᵥ [a : 1 : b]) 1`, so its
derivative at `0` is `C.u`. -/
private theorem hasDerivAt_localParameter_symm_weierstrassPoint {f : ℂ → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, f z = -((C⁻¹.toMatrix *ᵥ ![2 * (℘[L] z / ℘'[L] z), 1, 2 * (℘'[L] z)⁻¹]) 0 /
        (C⁻¹.toMatrix *ᵥ ![2 * (℘[L] z / ℘'[L] z), 1, 2 * (℘'[L] z)⁻¹]) 1)) :
    HasDerivAt f (C.u : ℂ) 0 := by
  have ha : HasDerivAt (fun z ↦ 2 * (L.weierstrassP z / L.derivWeierstrassP z)) (-1) 0 := by
    convert (L.hasDerivAt_weierstrassP_div_derivWeierstrassP (zero_mem _)).const_mul 2 using 1
    norm_num
  refine (hasDerivAt_localParameter_chartAtInfinity C ha
    (by simpa using (L.hasDerivAt_inv_derivWeierstrassP (zero_mem _)).const_mul 2)
    (by simp) (by simp)).congr_of_eventuallyEq hf

/-- Along the Weierstrass point map carried to `C • E_Λ`, the local parameter has derivative
`C.u` at `0`, so after the rescaling by `C.u⁻¹` it has derivative `1`. -/
private theorem hasDerivAt_localParameter_weierstrassPointVariableChange :
    HasDerivAt (fun z ↦ (weierstrassPointVariableChange L C z).localParameter) 1 0 := by
  have hf : HasDerivAt (fun z ↦ ((Point.addEquivVariableChange L.weierstrassCurve C).symm
      (L.weierstrassPoint z).toProjective).localParameter) (C.u : ℂ) 0 := by
    refine hasDerivAt_localParameter_symm_weierstrassPoint L C ?_
    filter_upwards [L.eventually_mk_eq_weierstrassPoint_toProjective (zero_mem _)]
      with z ⟨_, hz⟩
    rw [← hz, Point.addEquivVariableChange_symm_mk, Point.localParameter_mk]
  have hcomp := hf.comp_of_eq (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).const_mul ((C.u : ℂ)⁻¹))
    (by simp)
  rw [mul_one, mul_inv_cancel₀ C.u.ne_zero] at hcomp
  exact hcomp.congr_of_eventuallyEq
    (.of_forall fun z ↦ by
      simp only [weierstrassPointVariableChange_apply, Function.comp_apply, id_eq])

/-- Along the Weierstrass point map, the local parameter `-2 ℘ / ℘'` has derivative `1` at
`0`: this is the case `C = 1` of the chart-at-infinity computation. -/
private theorem hasDerivAt_localParameter_weierstrassPoint :
    HasDerivAt (fun z ↦ (L.weierstrassPoint z).toProjective.localParameter) 1 0 := by
  refine (hasDerivAt_localParameter_symm_weierstrassPoint L 1 ?_).congr_deriv
    (by rw [VariableChange.one_def, Units.val_one])
  filter_upwards [L.eventually_mk_eq_weierstrassPoint_toProjective (zero_mem _)] with z ⟨_, hz⟩
  rw [← hz, Point.localParameter_mk, inv_one, VariableChange.toMatrix_one, one_mulVec]

end Comparison

variable {W} in
/-- The derivative of the local parameter along `tangentExp` does not vanish, as some normalized
continuous homomorphism exists: the Weierstrass point map, carried to `W`. -/
private theorem tangentScale_ne_zero : W.tangentScale ≠ 0 := by
  obtain ⟨L, C, -, rfl⟩ := WeierstrassCurve.exists_periodPair_variableChange_smul_eq W
  exact (tangentScale_ne_zero_and_eq_tangentExp_rescale _
    (continuous_weierstrassPointVariableChange L C)
    (hasDerivAt_localParameter_weierstrassPointVariableChange L C)).1

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

end WeierstrassCurve.Projective

namespace PeriodPair

open WeierstrassCurve

/-- **The exponential map of a lattice curve is the Weierstrass point map**:
`exp_{E_Λ}(z)` is the affine point `(℘(z), ℘'(z) / 2)` for `z ∉ Λ`, and the point at infinity for
`z ∈ Λ`. -/
theorem exp_weierstrassCurve (L : PeriodPair) (z : ℂ) :
    L.weierstrassCurve.toProjective.exp z = (L.weierstrassPoint z).toProjective := by
  let g : ℂ →+ L.weierstrassCurve.toProjective.Point :=
    (Projective.Point.toAffineAddEquiv L.weierstrassCurve.toProjective).symm.toAddMonoidHom.comp
      L.weierstrassPointHom
  have hg : ⇑g = fun z ↦ (L.weierstrassPoint z).toProjective :=
    funext fun z ↦ by simp [g, PeriodPair.weierstrassPointHom_apply]
  have h := Projective.eq_exp_of_hasDerivAt _ (g := g)
    (by rw [hg]; exact Projective.hasDerivAt_localParameter_weierstrassPoint L)
  rw [← h, hg]

/-- **Rescaling naturality of the exponential map of a lattice curve**: after a change of
variables `C` with scaling factor `u`, the exponential map of `C • E_Λ` sends `z` to the image of
the Weierstrass point of `u⁻¹ z` under the inverse point map
`(Point.addEquivVariableChange E_Λ C).symm` from `E_Λ(ℂ)` to `(C • E_Λ)(ℂ)`. -/
theorem exp_variableChange_weierstrassCurve (L : PeriodPair) (C : VariableChange ℂ) (z : ℂ) :
    (C • L.weierstrassCurve).toProjective.exp z =
      (Projective.Point.addEquivVariableChange L.weierstrassCurve C).symm
        (L.weierstrassPoint ((C.u : ℂ)⁻¹ * z)).toProjective := by
  rw [← Projective.weierstrassPointVariableChange_apply, Projective.eq_exp_of_hasDerivAt _
    (Projective.hasDerivAt_localParameter_weierstrassPointVariableChange L C)]

end PeriodPair

namespace WeierstrassCurve.Projective

/-- **Rescaling naturality of the exponential map**: after a change of variables `C` with
scaling factor `u`, the exponential map of `C • E` sends `z` to the image of `exp_E (u⁻¹ z)`
under the inverse point map `(Point.addEquivVariableChange E C).symm` from `E(ℂ)` to `(C • E)(ℂ)`.
-/
theorem exp_variableChange (E : WeierstrassCurve ℂ) [E.IsElliptic] (C : VariableChange ℂ)
    (z : ℂ) :
    (C • E).toProjective.exp z =
      (Point.addEquivVariableChange E C).symm (E.toProjective.exp ((C.u : ℂ)⁻¹ * z)) := by
  obtain ⟨L, C', hu, rfl⟩ := WeierstrassCurve.exists_periodPair_variableChange_smul_eq E
  let g : ℂ →+ (C • C' • L.weierstrassCurve).toProjective.Point :=
    ((Point.addEquivVariableChange _ C).symm.toAddMonoidHom.comp
      (C' • L.weierstrassCurve).toProjective.exp).comp (AddMonoidHom.mulLeft ((C.u : ℂ)⁻¹))
  -- `exp_E` is the Weierstrass point map carried to `E = C' • E_Λ`, as `C'.u = 1`. Carried
  -- further to `C • E`, the local parameter has derivative `(C * C').u = C.u` at `0`.
  have hf : HasDerivAt (fun z ↦ ((Point.addEquivVariableChange _ C).symm
      ((C' • L.weierstrassCurve).toProjective.exp z)).localParameter) ((C * C').u : ℂ) 0 := by
    refine hasDerivAt_localParameter_symm_weierstrassPoint L (C * C') ?_
    filter_upwards [L.eventually_mk_eq_weierstrassPoint_toProjective (zero_mem _)]
      with z ⟨_, hz⟩
    rw [PeriodPair.exp_variableChange_weierstrassCurve, hu, Units.val_one, inv_one, one_mul, ← hz,
      Point.addEquivVariableChange_symm_mk, Point.addEquivVariableChange_symm_mk,
      Point.localParameter_mk]
    simp only [Matrix.mulVec_mulVec, ← VariableChange.toMatrix_mul, ← mul_inv_rev]
  have hcomp := hf.comp_of_eq (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).const_mul ((C.u : ℂ)⁻¹))
    (by simp)
  rw [mul_one, VariableChange.mul_def, Units.val_mul, hu, Units.val_one, mul_one,
    mul_inv_cancel₀ C.u.ne_zero] at hcomp
  exact (DFunLike.congr_fun (eq_exp_of_hasDerivAt _ (g := g) hcomp) z).symm

/-- After a change of variables `C` with scaling factor `u`, the point map
`Point.addEquivVariableChange E C` from `(C • E)(ℂ)` to `E(ℂ)` sends `exp_{C • E} z` to
`exp_E (u⁻¹ z)`. -/
theorem addEquivVariableChange_exp (E : WeierstrassCurve ℂ) [E.IsElliptic]
    (C : VariableChange ℂ) (z : ℂ) :
    Point.addEquivVariableChange E C ((C • E).toProjective.exp z) =
      E.toProjective.exp ((C.u : ℂ)⁻¹ * z) := by
  rw [exp_variableChange, AddEquiv.apply_symm_apply]

variable (W : Projective ℂ) [W.IsElliptic]

/-- **`exp_E` satisfies the affine invariant-differential equation.** Where `exp_E z` is
eventually the affine point `(x z, y z)` near `z₀`, the coordinate `x` has derivative
`2 y + a₁ x + a₃` at `z₀`. Writing `E` as the image of `E_Λ` under a change of variables
`(1, r, s, t)`, this is `℘' = 2 (℘' / 2)` for the coordinates `x = ℘ - r` and
`y = ℘' / 2 - s x - t`. Where `2y + a₁x + a₃ ≠ 0` this compares `exp_E` with the form
`dx / (2y + a₁x + a₃)` (`WeierstrassCurve.Projective.invariantDifferential_eq_inv_smul_mvfderiv`);
the global pullback is `WeierstrassCurve.Projective.pullback_invariantDifferential_exp`. -/
theorem hasDerivAt_of_eventually_toAffineAddEquiv_exp_eq_some {x y : ℂ → ℂ} {z₀ : ℂ}
    (h : ∀ᶠ z in 𝓝 z₀, ∃ hz : W.toAffine.Nonsingular (x z) (y z),
      Point.toAffineAddEquiv W (W.exp z) = .some (x z) (y z) hz) :
    HasDerivAt x (2 * y z₀ + W.a₁ * x z₀ + W.a₃) z₀ := by
  obtain ⟨L, C, hu, rfl⟩ := WeierstrassCurve.exists_periodPair_variableChange_smul_eq W
  -- The change of variables `C = (1, r, s, t)` carries the affine point `(x z, y z)` of `exp_E z`
  -- to the point `(℘ z, ℘' z / 2)` of `E_Λ`.
  have key : ∀ z, (∃ hz : (C • L.weierstrassCurve).toProjective.toAffine.Nonsingular (x z) (y z),
      Point.toAffineAddEquiv _ ((C • L.weierstrassCurve).toProjective.exp z) =
        .some (x z) (y z) hz) →
      z ∉ L.lattice ∧ L.weierstrassP z = x z + C.r ∧
        L.derivWeierstrassP z / 2 = y z + C.s * x z + C.t := by
    rintro z ⟨hz, hxy⟩
    have h₁ := congrArg (Affine.Point.addEquivVariableChange L.weierstrassCurve C) hxy
    rw [← Point.toAffineAddEquiv_addEquivVariableChange, addEquivVariableChange_exp, hu,
      Units.val_one, inv_one, one_mul, PeriodPair.exp_weierstrassCurve,
      Point.toAffineAddEquiv_toProjective] at h₁
    by_cases hzL : z ∈ L.lattice
    · simp [L.weierstrassPoint_of_mem hzL] at h₁
    · simp only [L.weierstrassPoint_of_notMem hzL, Affine.Point.coe_addEquivVariableChange,
        Affine.Point.equivVariableChange_some, Affine.Point.some.injEq, hu, Units.val_one,
        one_pow, one_mul] at h₁
      exact ⟨hzL, h₁.1, h₁.2⟩
  obtain ⟨hz₀, -, hy₀⟩ := key z₀ h.self_of_nhds
  have hx : x =ᶠ[𝓝 z₀] fun z ↦ L.weierstrassP z - C.r :=
    h.mono fun z hz ↦ eq_sub_of_add_eq (key z hz).2.1.symm
  refine (((L.hasDerivAt_weierstrassP hz₀).sub_const C.r).congr_of_eventuallyEq hx).congr_deriv ?_
  simp only [variableChange_a₁, variableChange_a₃, PeriodPair.weierstrassCurve_a₁,
    PeriodPair.weierstrassCurve_a₃, hu, Units.val_one, inv_one, one_pow, one_mul]
  linear_combination 2 * hy₀

/-- **The kernel of `exp_E` is the period lattice of `E`.** -/
theorem ker_exp : W.exp.ker = W.periodLattice.toAddSubgroup := by
  obtain ⟨L, C, hu, rfl⟩ := WeierstrassCurve.exists_periodPair_variableChange_smul_eq W
  rw [periodLattice_eq_iff.mpr ⟨C, hu, rfl⟩]
  classical
  ext z
  rw [AddMonoidHom.mem_ker, PeriodPair.exp_variableChange_weierstrassCurve, hu, Units.val_one,
    inv_one, one_mul, AddEquivClass.map_eq_zero_iff,
    ← (Point.toAffineAddEquiv L.weierstrassCurve.toProjective).map_eq_zero_iff,
    Point.toAffineAddEquiv_toProjective, PeriodPair.weierstrassPoint_eq_zero_iff,
    Submodule.mem_toAddSubgroup]

/-- `exp_E` vanishes exactly on the period lattice of `E`. -/
@[simp]
theorem exp_eq_zero_iff {z : ℂ} : W.exp z = 0 ↔ z ∈ W.periodLattice := by
  rw [← AddMonoidHom.mem_ker, ker_exp, Submodule.mem_toAddSubgroup]

/-- Two points of `ℂ` have the same image under `exp_E` exactly when they differ by a period. -/
theorem exp_eq_exp_iff {z w : ℂ} : W.exp z = W.exp w ↔ z - w ∈ W.periodLattice := by
  rw [← exp_eq_zero_iff, map_sub, sub_eq_zero]

variable {W} in
/-- The kernel of `exp_E`, the period lattice, is discrete. -/
instance instDiscreteTopologyKerExp : DiscreteTopology W.exp.ker := by
  rw [← SetLike.isDiscrete_iff_discreteTopology, ker_exp, Submodule.coe_toAddSubgroup]
  exact SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance

/-! ### Global structure of the exponential map -/

section Global

local instance : ConnectedSpace (Multiplicative W.Point) :=
  Homeomorph.ofAdd.connectedSpace_iff.mp inferInstance

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
  have hd : IsDiscrete (W.exp.ker : Set ℂ) :=
    SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
  exact ((W.isOpenMap_exp.isQuotientMap W.continuous_exp
    W.exp_surjective).isAddQuotientCoveringMap_of_isDiscrete_ker_addMonoidHom hd).isCoveringMap

end Global

/-! ### The invariant holomorphic differential -/

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

/-- **The invariant differential is the only form pulling back to `dz`** along `exp_E`. -/
theorem pullback_exp_eq_mvfderiv_id_iff {α : TauCeti.RiemannSurface.OneForm W.Point} :
    α.pullback W.exp = mvfderiv 𝓘(ℂ) id ↔ α = W.invariantDifferential := by
  rw [← W.pullback_invariantDifferential_exp]
  exact (TauCeti.RiemannSurface.OneForm.pullback_injective W.exp_surjective
    fun z ↦ (W.isInvertible_mfderiv_exp z).surjective).eq_iff

/-- The invariant differential vanishes nowhere. -/
theorem invariantDifferential_ne_zero (P : W.Point) : W.invariantDifferential P ≠ 0 := by
  obtain ⟨z, rfl⟩ := W.exp_surjective P
  intro h
  have hv := W.invariantDifferential_apply_mfderiv_exp z
    ((NormedSpace.fromTangentSpace z).symm 1)
  rw [h] at hv
  have h01 : (0 : ℂ) = 1 := by simpa only [zero_apply,
    ContinuousLinearEquiv.apply_symm_apply] using hv
  exact zero_ne_one h01

/-- The exponential is locally biholomorphic, by its invertible derivative: it is a local
diffeomorphism of class `C^n` for every `n`, including `n = ω`. -/
theorem isLocalDiffeomorphAt_exp {n : ℕ∞ω} (z : ℂ) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) n W.exp z := by
  obtain ⟨e, he⟩ := W.isInvertible_mfderiv_exp z
  exact (TauCeti.isLocalDiffeomorphAt_of_mfderiv_eq (n := ω) (W.contMDiff_exp ω).contMDiffOn
    isOpen_univ (Set.mem_univ z) (by exact BoundarylessManifold.isInteriorPoint)
    (by exact le_top) he).of_le le_top

/-- **The local parameter is a local coordinate at the origin**: it is a local diffeomorphism of
class `C^n` there for every `n`, including `n = ω`, as it has derivative `1` along `exp_E`. -/
theorem isLocalDiffeomorphAt_localParameter_zero {n : ℕ∞ω} :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) n (Point.localParameter : W.Point → ℂ) 0 := by
  have ht := (Point.contMDiffAt_localParameter_zero (W := W) 1).mdifferentiableAt one_ne_zero
  have hm : mfderiv 𝓘(ℂ) 𝓘(ℂ) (Point.localParameter ∘ W.exp) 0 = _ :=
    W.hasDerivAt_localParameter_exp.hasFDerivAt.hasMFDerivAt.mfderiv
  have hcomp : (mfderiv 𝓘(ℂ) 𝓘(ℂ) (Point.localParameter ∘ W.exp) 0).IsInvertible :=
    ⟨ContinuousLinearEquiv.refl ℂ ℂ, by
      rw [hm]
      ext
      -- Both sides are `1`, as elements of the tangent spaces `ℂ`.
      exact (one_smul ℂ (1 : ℂ)).symm⟩
  have hd := (TauCeti.isInvertible_mfderiv_of_isInvertible_mfderiv_comp rfl
    (by rwa [map_zero]) (W.mdifferentiable_exp 0) hcomp).2
  rw [map_zero] at hd
  obtain ⟨e, he⟩ := hd
  -- The local parameter is holomorphic on the open set of points near which it is holomorphic.
  exact (TauCeti.isLocalDiffeomorphAt_of_mfderiv_eq (n := ω) (s := {P | ∀ᶠ Q in 𝓝 P,
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (Point.localParameter : W.Point → ℂ) Q})
    (fun _ hP ↦ hP.self_of_nhds.contMDiffWithinAt) isOpen_setOfPred_eventually_nhds
    (Point.eventually_contMDiffAt_localParameter ω)
    (by exact BoundarylessManifold.isInteriorPoint) (by exact le_top) he).of_le le_top

/-- **Local logarithms integrate the invariant differential**: on its source, the differential of
a local inverse of `exp_E` of class `C^n`, `n ≠ 0`, is the invariant differential. -/
theorem mvfderiv_localInverse_exp {n : ℕ∞ω} {z : ℂ}
    (hf : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) n W.exp z) (hn : n ≠ 0) {Q : W.Point}
    (hQ : Q ∈ hf.localInverse.source) :
    mvfderiv 𝓘(ℂ) hf.localInverse Q = W.invariantDifferential Q := by
  have hmd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) hf.localInverse Q :=
    (hf.contMDiffOn_localInverse.contMDiffAt
      (hf.localInverse.open_source.mem_nhds hQ)).mdifferentiableAt hn
  have hid : W.exp ∘ hf.localInverse =ᶠ[𝓝 Q] id :=
    eventuallyEq_of_mem (hf.localInverse.open_source.mem_nhds hQ) hf.localInverse_eqOn_right
  apply ContinuousLinearMap.ext
  intro v
  have hv : mfderiv 𝓘(ℂ) 𝓘(ℂ) W.exp (hf.localInverse Q)
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) hf.localInverse Q v) = v := by
    rw [TauCeti.mfderiv_apply_mfderiv_of_eventuallyEq_comp hid (W.mdifferentiable_exp _)
      hmd v, mfderiv_id, ContinuousLinearMap.id_apply]
  have hω := W.invariantDifferential_apply_mfderiv_exp (hf.localInverse Q)
    (mfderiv 𝓘(ℂ) 𝓘(ℂ) hf.localInverse Q v)
  rw [hf.localInverse_right_inv hQ] at hv hω
  rw [mvfderiv_apply_eq_mfderiv_apply]
  exact hω.symm.trans (congrArg (W.invariantDifferential Q) hv)

/-- The invariant differential is holomorphic everywhere, including at infinity and two-torsion:
near every point it is the differential of a holomorphic local logarithm. -/
theorem holomorphicAt_invariantDifferential (P : W.Point) :
    W.invariantDifferential.HolomorphicAt P := by
  obtain ⟨z, rfl⟩ := W.exp_surjective P
  let hf := W.isLocalDiffeomorphAt_exp (n := 1) z
  have hU : ∀ᶠ Q in 𝓝 (W.exp z), Q ∈ hf.localInverse.source :=
    hf.localInverse.open_source.mem_nhds hf.localInverse_mem_source
  refine (TauCeti.RiemannSurface.OneForm.holomorphicAt_mvfderiv (hU.mono fun Q hQ ↦ ?_)).congr
    (hU.mono fun Q hQ ↦ W.mvfderiv_localInverse_exp hf one_ne_zero hQ)
  exact (hf.contMDiffOn_localInverse.contMDiffAt
    (hf.localInverse.open_source.mem_nhds hQ)).mdifferentiableAt one_ne_zero

/-- On any affine coordinate neighbourhood `(x, y)` of `P` where `2y + a₁x + a₃ ≠ 0` at `P`, the
global invariant form at `P` is the algebraic differential `dx / (2y + a₁x + a₃)`. Where the
denominator vanishes (at two-torsion) and at infinity, the global form is the holomorphic,
nowhere-zero extension (`WeierstrassCurve.Projective.holomorphicAt_invariantDifferential` and
`WeierstrassCurve.Projective.invariantDifferential_ne_zero`). -/
theorem invariantDifferential_eq_inv_smul_mvfderiv {x y : W.Point → ℂ} {P : W.Point}
    (h : ∀ᶠ Q in 𝓝 P, ∃ hQ : W.toAffine.Nonsingular (x Q) (y Q),
      Point.toAffineAddEquiv W Q = .some (x Q) (y Q) hQ)
    (hne : 2 * y P + W.a₁ * x P + W.a₃ ≠ 0) :
    W.invariantDifferential P =
      (2 * y P + W.a₁ * x P + W.a₃)⁻¹ • mvfderiv 𝓘(ℂ) x P := by
  obtain ⟨z, rfl⟩ := W.exp_surjective P
  have hd : HasDerivAt (x ∘ W.exp) (2 * y (W.exp z) + W.a₁ * x (W.exp z) + W.a₃) z :=
    W.hasDerivAt_of_eventually_toAffineAddEquiv_exp_eq_some
      (W.continuous_exp.continuousAt.eventually h)
  let hf := W.isLocalDiffeomorphAt_exp (n := 1) z
  have hx : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) x (W.exp z) := by
    have hi := hf.mdifferentiableAt_localInverse one_ne_zero
    have hc := hd.differentiableAt.mdifferentiableAt.comp_of_eq (W.exp z) hi
      (hf.localInverse_left_inv hf.localInverse_mem_target)
    apply hc.congr_of_eventuallyEq
    filter_upwards [hf.localInverse_eventuallyEq_right] with Q hQ
    exact congrArg x hQ.symm
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := (W.isInvertible_mfderiv_exp z).surjective v
  rw [W.invariantDifferential_apply_mfderiv_exp, smul_apply,
    ← mvfderiv_comp_apply z hx (W.mdifferentiable_exp z), TauCeti.mvfderiv_eq_fderiv_apply,
    hd.hasFDerivAt.fderiv, ContinuousLinearMap.toSpanSingleton_apply (R₁ := ℂ) (r := w),
    smul_eq_mul, smul_eq_mul (α := ℂ) w]
  -- The tangent vector `w` is the complex number `c⁻¹ * (w * c)`.
  exact (inv_mul_cancel_left₀ hne w).symm.trans (congrArg _ (mul_comm (_ : ℂ) w))

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

/-- **`ℂ / ker exp_E ≃ E(ℂ)` is holomorphic**, for the complex structure of the quotient by the
discrete subgroup `ker exp_E`: its composite with the projection is `exp_E`. -/
theorem contMDiff_expQuotientKerContinuousAddEquiv (n : ℕ∞ω) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) n W.expQuotientKerContinuousAddEquiv := by
  rw [W.exp.ker.contMDiff_quotient_iff (n := ω) le_top]
  simpa only [Function.comp_def, expQuotientKerContinuousAddEquiv_mk] using W.contMDiff_exp n

/-- **The inverse of `ℂ / ker exp_E ≃ E(ℂ)` is holomorphic**: it is the inverse of a holomorphic
homeomorphism of Riemann surfaces. -/
theorem contMDiff_expQuotientKerContinuousAddEquiv_symm (n : ℕ∞ω) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) n W.expQuotientKerContinuousAddEquiv.symm := by
  let e := W.expQuotientKerContinuousAddEquiv.toHomeomorph
  have he : e.isHomeomorph.homeomorph e = e := Homeomorph.ext fun _ ↦ rfl
  have h := e.isHomeomorph.mdifferentiable_symm
    ((W.contMDiff_expQuotientKerContinuousAddEquiv 1).mdifferentiable one_ne_zero)
  rw [he] at h
  exact h.contMDiff

end WeierstrassCurve.Projective
