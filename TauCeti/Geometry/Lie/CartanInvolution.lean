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
# Conjugacy of Cartan involutions on the Lie algebra of a real Lie group

On `LeftInvariantDerivation I G` of a finite-dimensional real Lie group `G`, any two Cartan
involutions `θ` and `θ'` are conjugate by `Ad (lieExp Z)` for some `Z ∈ θ.cartanP`
(`TauCeti.Lie.exists_conj_cartanInvolution`).

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §2, Theorem 6.16.
-/

public section

open LieAlgebra
open scoped ContDiff Manifold

namespace TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **Conjugacy of Cartan involutions on a real Lie group**: any two Cartan involutions `θ` and
`θ'` of `LeftInvariantDerivation I G` satisfy `θ' (Ad (lieExp Z) Y) = Ad (lieExp Z) (θ Y)` for
some `Z ∈ θ.cartanP`. -/
theorem exists_conj_cartanInvolution
    {θ θ' : LeftInvariantDerivation I G ≃ₗ⁅ℝ⁆ LeftInvariantDerivation I G}
    (hθ : θ.IsCartanInvolution) (hθ' : θ'.IsCartanInvolution) :
    ∃ Z ∈ θ.cartanP, ∀ Y,
      θ' (Ad (I := I) (lieExp Z) Y) = Ad (I := I) (lieExp Z) (θ Y) := by
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  obtain ⟨Z, hZP, hconj⟩ := hθ.exists_mem_cartanP_conj_exp (LinearEquiv.refl ℝ _) hθ'
  exact ⟨Z, hZP, fun Y ↦ by
    simpa only [LinearEquiv.refl_apply, LinearEquiv.refl_symm, LinearEquiv.conj_refl,
      LeftInvariantDerivation.Ad_lieExp_apply] using hconj Y⟩

end TauCeti.Lie
