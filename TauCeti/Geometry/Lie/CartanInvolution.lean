/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Geometry.Lie.Adjoint.Derivation
public import TauCeti.Geometry.Lie.Exponential.Basic
import TauCeti.Algebra.Lie.CartanInvolution.Conjugacy
import TauCeti.Geometry.Lie.Adjoint.Exponential.Formula

/-!
# Conjugacy of Cartan involutions on a real Lie group's Lie algebra

On the Lie algebra `LeftInvariantDerivation I G` of a finite-dimensional smooth real Lie group `G`,
the operator exponential `exp (ad Z)` coincides with the group adjoint action `Ad (lieExp Z)`
(`LeftInvariantDerivation.Ad_lieExp_apply`). Combining this with the algebraic conjugacy theorem
`LieEquiv.IsCartanInvolution.exists_conj_exp_ad` shows that any two Cartan involutions `θ`, `θ'`
of `LeftInvariantDerivation I G` are conjugate by `Ad (lieExp Z)` for some `Z ∈ θ.cartanP`.

## Main results

* `TauCeti.Lie.exists_conj_cartanInvolution`: any two Cartan involutions `θ` and `θ'` of the Lie
  algebra of a finite-dimensional smooth real Lie group are conjugate by `Ad (lieExp Z)` for some
  `Z ∈ θ.cartanP`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser (2002), Chapter VI, §2,
  Corollary 6.19.
-/

public section

namespace TauCeti.Lie

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- **Conjugacy of Cartan involutions on a Lie group's Lie algebra** (Knapp, Ch. VI, Cor. 6.19):
any two Cartan involutions `θ` and `θ'` of `LeftInvariantDerivation I G` are conjugate by
`Ad (lieExp Z)` for some `Z ∈ θ.cartanP`. -/
theorem exists_conj_cartanInvolution
    {θ θ' : LeftInvariantDerivation I G ≃ₗ⁅ℝ⁆ LeftInvariantDerivation I G}
    (hθ : θ.IsCartanInvolution) (hθ' : θ'.IsCartanInvolution) :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    ∃ Z ∈ θ.cartanP, ∀ Y,
      θ' (Ad (I := I) (lieExp Z) Y) = Ad (I := I) (lieExp Z) (θ Y) := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  obtain ⟨Z, hZ, hconj⟩ := hθ.exists_conj_exp_ad hθ'
  refine ⟨Z, hZ, fun Y ↦ ?_⟩
  rw [Z.Ad_lieExp_apply Y, Z.Ad_lieExp_apply (θ Y)]
  exact hconj Y

end TauCeti.Lie
