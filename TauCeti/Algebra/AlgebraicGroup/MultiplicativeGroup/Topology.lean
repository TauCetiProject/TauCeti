/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.Algebra.Polynomial.Laurent.Polynomial
public import TauCeti.Topology.Algebra.PointTopology.Localization
import TauCeti.Analysis.Normed.Field.ZPowers
import TauCeti.Topology.Algebra.Group.Subgroup
import TauCeti.Topology.Algebra.PointTopology.Separation

/-!
# The point topology on the multiplicative group

For a commutative topological `R`-algebra `A`, the points of the multiplicative group
`𝔾ₘ = Spec R[T;T⁻¹]` with values in `A` are the units of `A`
(`TauCeti.MultiplicativeGroup.pointsMulEquiv`). A point is determined by its values on `T` and on
`T⁻¹`, so the point topology is the topology of `Aˣ` as the hyperbola `xy = 1` in `A × A`, that is,
Mathlib's topology on `Aˣ` induced by `Units.embedProduct`. This file bundles the identification as
an isomorphism of topological groups. Since `R[T;T⁻¹]` is the localization of `R[X]` away from `X`,
the homeomorphism is `TauCeti.PointTopology.localizationAwayXHomeomorph`.

Over a proper normed field, such as `ℚ_[p]`, a point of `𝔾ₘ` generates a relatively compact
subgroup exactly when the corresponding unit has norm one
(`TauCeti.MultiplicativeGroup.isCompact_closure_zpowers_iff_norm_eq_one`).

As an application, the points of an affine group over a totally disconnected ring are totally
disconnected (`TauCeti.PointTopology.instTotallyDisconnectedSpaceWithConv`), but the hypothesis on
the coefficient ring cannot be dropped: the real points of `𝔾ₘ` form `ℝˣ`, which contains the
connected half-line of positive reals.

## Main declarations

* `TauCeti.MultiplicativeGroup.pointsContinuousMulEquiv`: the points of `𝔾ₘ` with the point
  topology are isomorphic, as topological groups, to `Aˣ` with the units topology.
* `TauCeti.MultiplicativeGroup.isCompact_closure_zpowers_iff_norm_eq_one`: over a proper normed
  field, the powers of a point of `𝔾ₘ` are relatively compact exactly when its unit has norm one.
* `TauCeti.MultiplicativeGroup.not_totallyDisconnectedSpace_real`: the real points of `𝔾ₘ` are not
  totally disconnected.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  §3, pp. 3–4.
-/

public section

open WithConv TauCeti.PointTopology
open scoped LaurentPolynomial

namespace TauCeti.MultiplicativeGroup

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [TopologicalSpace A]
  [IsTopologicalSemiring A]

variable (R A) in
/-- The points of the multiplicative group with values in `A`, with the point topology, are
isomorphic as topological groups to the units of `A` with the topology induced by
`Units.embedProduct`. The underlying group isomorphism is `pointsMulEquiv`. -/
noncomputable def pointsContinuousMulEquiv : WithConv (R[T;T⁻¹] →ₐ[R] A) ≃ₜ* Aˣ where
  toMulEquiv := pointsMulEquiv
  -- `R[T;T⁻¹]` is the localization of `R[X]` away from `X`, and on the underlying points
  -- `pointsMulEquiv` is `localizationAwayXHomeomorph`, which is a homeomorphism.
  continuous_toFun :=
    ((localizationAwayXHomeomorph R R[T;T⁻¹] A).continuous.comp
      isHomeomorph_ofConv.continuous).congr fun f ↦ Units.ext <| by simp
  continuous_invFun := by
    have hc : Continuous fun u : Aˣ ↦ toConv ((localizationAwayXHomeomorph R R[T;T⁻¹] A).symm u) :=
      isHomeomorph_ofConv.isEmbedding.isInducing.continuous_iff.2
        (localizationAwayXHomeomorph R R[T;T⁻¹] A).symm.continuous
    refine hc.congr fun u ↦ ?_
    rw [MulEquiv.invFun_eq_symm, MulEquiv.eq_symm_apply, Units.ext_iff]
    simpa only [pointsMulEquiv_apply, ofConv_toConv, laurentEvalEquiv_symm_apply,
      val_localizationAwayXHomeomorph_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
      Polynomial.toLaurent_X] using
        congrArg Units.val ((localizationAwayXHomeomorph R R[T;T⁻¹] A).apply_symm_apply u)

/-- The underlying group isomorphism of `pointsContinuousMulEquiv` is `pointsMulEquiv`. -/
@[simp]
theorem coe_pointsContinuousMulEquiv :
    (pointsContinuousMulEquiv R A : WithConv (R[T;T⁻¹] →ₐ[R] A) ≃* Aˣ) = pointsMulEquiv :=
  (rfl)

/-- The forward map of `pointsContinuousMulEquiv` is `pointsMulEquiv`. -/
@[simp]
theorem pointsContinuousMulEquiv_apply (f : WithConv (R[T;T⁻¹] →ₐ[R] A)) :
    pointsContinuousMulEquiv R A f = pointsMulEquiv f :=
  (rfl)

/-- The inverse map of `pointsContinuousMulEquiv` is the inverse of `pointsMulEquiv`. -/
@[simp]
theorem pointsContinuousMulEquiv_symm_apply (u : Aˣ) :
    (pointsContinuousMulEquiv R A).symm u = (pointsMulEquiv (R := R)).symm u :=
  (rfl)

/-- Over a proper normed field `K`, the powers of a `K`-point `x` of the multiplicative group form a
relatively compact subgroup exactly when the unit `pointsMulEquiv x` has norm one. -/
theorem isCompact_closure_zpowers_iff_norm_eq_one {K : Type*} [NormedField K] [ProperSpace K]
    [Algebra R K] (x : WithConv (R[T;T⁻¹] →ₐ[R] K)) :
    IsCompact (closure (Subgroup.zpowers x : Set (WithConv (R[T;T⁻¹] →ₐ[R] K)))) ↔
      ‖(pointsMulEquiv x : K)‖ = 1 := by
  let e := pointsContinuousMulEquiv R K
  rw [← TauCeti.isCompact_closure_zpowers_iff_norm_eq_one, ← pointsContinuousMulEquiv_apply]
  -- The topological group isomorphism `e` and its inverse carry cyclic subgroups with compact
  -- closure to cyclic subgroups with compact closure.
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := Subgroup.isCompact_closure_map h e.toMulEquiv.toMonoidHom e.continuous
    rwa [MonoidHom.map_zpowers] at this
  · have := Subgroup.isCompact_closure_map h e.symm.toMulEquiv.toMonoidHom e.symm.continuous
    rw [MonoidHom.map_zpowers] at this
    change IsCompact (closure (SetLike.coe (Subgroup.zpowers (e.symm (e x))))) at this
    rwa [e.symm_apply_apply] at this

/-- The real points of the multiplicative group, with the point topology, are not totally
disconnected: they contain the connected image of the path `r ↦ exp r`. -/
theorem not_totallyDisconnectedSpace_real :
    ¬TotallyDisconnectedSpace (WithConv (ℝ[T;T⁻¹] →ₐ[ℝ] ℝ)) := by
  intro h
  let u : ℝ → ℝˣ := fun r ↦ Units.mk0 (Real.exp r) (Real.exp_ne_zero r)
  have hu : Continuous u := Units.isEmbedding_val₀.continuous_iff.mpr Real.continuous_exp
  have hsub :=
    (isPreconnected_range ((pointsContinuousMulEquiv ℝ ℝ).symm.continuous.comp hu)).subsingleton
  have h01 : u 0 = u 1 := (pointsContinuousMulEquiv ℝ ℝ).symm.injective (hsub ⟨0, rfl⟩ ⟨1, rfl⟩)
  have h1 : Real.exp 1 = 1 := by simpa [u] using (congrArg Units.val h01).symm
  exact one_ne_zero (Real.exp_eq_one_iff 1 |>.mp h1)

end TauCeti.MultiplicativeGroup
