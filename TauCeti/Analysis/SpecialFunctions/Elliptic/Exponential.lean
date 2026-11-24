/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Exponential
public import TauCeti.Analysis.SpecialFunctions.Elliptic.Period.Lattice
public import TauCeti.Geometry.Manifold.Algebra.Quotient
import TauCeti.Analysis.SpecialFunctions.Elliptic.AdditionTheorem
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.Complex.Chart
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Topology.Algebra.ContinuousMonoidHom.QuotientKerEquiv

/-!
# The exponential map of a complex elliptic curve and the Weierstrass uniformization

The exponential map `exp_E : ℂ →+ E(ℂ)` of a complex elliptic curve
(`WeierstrassCurve.Projective.exp`, constructed intrinsically in
`TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Exponential`) is identified here with the
Weierstrass uniformization: its kernel is the period lattice of `E`.

The Weierstrass point map of a period pair `L`, the affine point `(℘(z), ℘'(z) / 2)` off the
lattice and the point at infinity on it, is an additive homomorphism, and in the chart at infinity
the local parameter `t = -2 ℘ / ℘'` has derivative `1` at `0`. By the uniqueness of the normalized
homomorphism (`WeierstrassCurve.Projective.eq_exp_of_hasDerivAt`), the exponential map of the
curve `E_Λ` of `Λ` is the Weierstrass point map (`PeriodPair.exp_weierstrassCurve`). Since every
complex elliptic curve `E` is the image of `E_Λ` for `Λ = E.periodLattice` under a change of
variables with `u = 1`, the rescaling naturality `WeierstrassCurve.Projective.exp_variableChange`
shows that the kernel of `exp_E` is `E.periodLattice` (`WeierstrassCurve.Projective.ker_exp`).

The general theory of the exponential map of a commutative real Lie group gives the global structure
of `exp_E`: it is an open map, onto since `E(ℂ)` is connected
(`WeierstrassCurve.Projective.exp_surjective`); with discrete kernel it is a covering map,
inducing an isomorphism of topological groups `ℂ / ker exp_E ≃ E(ℂ)`, which is biholomorphic.

## Main definitions

* `WeierstrassCurve.Projective.expQuotientKerContinuousAddEquiv`: the induced isomorphism of
  topological groups `ℂ / ker exp_E ≃ₜ+ E(ℂ)`.
* `WeierstrassCurve.Projective.expQuotientKerDiffeomorph`: the same isomorphism, as a
  biholomorphism.

## Main results

* `PeriodPair.exp_weierstrassCurve` and `PeriodPair.exp_variableChange_weierstrassCurve`: the
  comparison with the Weierstrass point map.
* `WeierstrassCurve.Projective.ker_exp` and `WeierstrassCurve.Projective.exp_eq_exp_iff`: the
  kernel of `exp_E` is the period lattice of `E`, so two points have the same image exactly when
  they differ by a period.
* `WeierstrassCurve.Projective.isCoveringMap_exp`: `exp_E` is a covering map onto `E(ℂ)`.
* `WeierstrassCurve.Projective.pullback_exp_eq_mvfderiv_id_iff`: the invariant differential is the
  only form pulling back to `dz`.
* `WeierstrassCurve.Projective.invariantDifferential_eq_inv_smul_mvfderiv`: its agreement with
  the algebraic differential `dx / (2y + a₁x + a₃)` on the affine locus where
  `2y + a₁x + a₃ ≠ 0`.
* `WeierstrassCurve.Projective.contMDiff_expQuotientKerContinuousAddEquiv` and
  `WeierstrassCurve.Projective.contMDiff_expQuotientKerContinuousAddEquiv_symm`: the isomorphism
  `ℂ / ker exp_E ≃ E(ℂ)` is biholomorphic.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, §IV.1 and §VI.5.
-/

public section

open Filter Topology
open scoped ContDiff Manifold

namespace WeierstrassCurve.Projective

open scoped PeriodPair

/-- Along the Weierstrass point map, the local parameter `-2 ℘ / ℘'` of the chart at infinity has
derivative `1` at `0`. -/
private theorem hasDerivAt_localParameter_weierstrassPoint (L : PeriodPair) :
    HasDerivAt (fun z ↦ (L.weierstrassPoint z).toProjective.localParameter) 1 0 := by
  have h : HasDerivAt (fun z ↦ -(2 * (℘[L] z / ℘'[L] z))) 1 0 := by
    convert ((L.hasDerivAt_weierstrassP_div_derivWeierstrassP (zero_mem _)).const_mul 2).neg
      using 1
    norm_num
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [L.eventually_mk_eq_weierstrassPoint_toProjective (zero_mem _)] with z ⟨_, hz⟩
  rw [← hz, Point.localParameter_mk]
  simp

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
  rw [Projective.exp_variableChange, exp_weierstrassCurve]

end PeriodPair

namespace WeierstrassCurve.Projective

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
  let e := Point.toAffineAddEquiv L.weierstrassCurve.toProjective
  let c := (Point.addEquivVariableChange L.weierstrassCurve C).symm
  have h : (C • L.weierstrassCurve).toProjective.exp =
      c.toAddMonoidHom.comp (e.symm.toAddMonoidHom.comp L.weierstrassPointHom) := by
    apply AddMonoidHom.ext
    intro z
    simp only [PeriodPair.exp_variableChange_weierstrassCurve, hu, Units.val_one,
      inv_one, one_mul, AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_ofClass, PeriodPair.weierstrassPointHom_apply, e, c,
      Point.toAffineAddEquiv_symm_apply]
  rw [h, AddMonoidHom.ker_comp_of_injective _ _ c.injective,
    AddMonoidHom.ker_comp_of_injective _ _ e.symm.injective, L.ker_weierstrassPointHom]

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

/-- **`exp_E` is a covering map.** It is an open continuous surjective homomorphism with discrete
kernel. -/
theorem isCoveringMap_exp : IsCoveringMap W.exp := by
  have hd : IsDiscrete (W.exp.ker : Set ℂ) :=
    SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
  exact ((W.isOpenMap_exp.isQuotientMap W.continuous_exp
    W.exp_surjective).isAddQuotientCoveringMap_of_isDiscrete_ker_addMonoidHom hd).isCoveringMap

/-! ### The invariant holomorphic differential -/

/-- **The invariant differential is the only form pulling back to `dz`** along `exp_E`. -/
theorem pullback_exp_eq_mvfderiv_id_iff {α : TauCeti.RiemannSurface.OneForm W.Point} :
    α.pullback W.exp = mvfderiv 𝓘(ℂ) id ↔ α = W.invariantDifferential := by
  rw [← W.pullback_invariantDifferential_exp]
  exact (TauCeti.RiemannSurface.OneForm.pullback_injective (fun P ↦ by
    obtain ⟨z, rfl⟩ := W.exp_surjective P
    exact ⟨z, rfl, (W.isInvertible_mfderiv_exp z).surjective⟩)).eq_iff

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
  have hx : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) x (W.exp z) :=
    (hf.mdifferentiableAt_comp_iff one_ne_zero).mp hd.differentiableAt.mdifferentiableAt
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := (W.isInvertible_mfderiv_exp z).surjective v
  rw [W.invariantDifferential_apply_mfderiv_exp, smul_apply,
    ← mvfderiv_comp_apply z hx (W.mdifferentiable_exp z), TauCeti.mvfderiv_eq_fderiv_apply,
    hd.hasFDerivAt.fderiv, ContinuousLinearMap.toSpanSingleton_apply (R₁ := ℂ) (r := w),
    smul_eq_mul, smul_eq_mul (α := ℂ) w]
  -- The tangent vector `w` is the complex number `c⁻¹ * (w * c)`.
  exact (inv_mul_cancel_left₀ hne w).symm.trans (congrArg _ (mul_comm (_ : ℂ) w))


/-! ### The quotient by the kernel -/

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
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) n W.expQuotientKerContinuousAddEquiv.symm :=
  (W.expQuotientKerContinuousAddEquiv.toHomeomorph.mdifferentiable_symm
    ((W.contMDiff_expQuotientKerContinuousAddEquiv 1).mdifferentiable one_ne_zero)).contMDiff

/-- **The biholomorphism `ℂ / ker exp_E ≃ E(ℂ)`**: the isomorphism
`WeierstrassCurve.Projective.expQuotientKerContinuousAddEquiv` as a `C^n` diffeomorphism for every
`n`; for `n = ω` it is a biholomorphism. -/
noncomputable def expQuotientKerDiffeomorph (n : ℕ∞ω) :
    (ℂ ⧸ W.exp.ker) ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ W.Point where
  toEquiv := W.expQuotientKerContinuousAddEquiv.toEquiv
  contMDiff_toFun := W.contMDiff_expQuotientKerContinuousAddEquiv n
  contMDiff_invFun := W.contMDiff_expQuotientKerContinuousAddEquiv_symm n

/-- The biholomorphism `ℂ / ker exp_E ≃ E(ℂ)` is the group isomorphism
`WeierstrassCurve.Projective.expQuotientKerContinuousAddEquiv`. -/
@[simp]
theorem coe_expQuotientKerDiffeomorph (n : ℕ∞ω) :
    ⇑(W.expQuotientKerDiffeomorph n) = W.expQuotientKerContinuousAddEquiv :=
  (rfl)

/-- The inverse of the biholomorphism `ℂ / ker exp_E ≃ E(ℂ)` is the inverse of the group
isomorphism `WeierstrassCurve.Projective.expQuotientKerContinuousAddEquiv`. -/
@[simp]
theorem coe_expQuotientKerDiffeomorph_symm (n : ℕ∞ω) :
    ⇑(W.expQuotientKerDiffeomorph n).symm = W.expQuotientKerContinuousAddEquiv.symm :=
  (rfl)

end WeierstrassCurve.Projective
