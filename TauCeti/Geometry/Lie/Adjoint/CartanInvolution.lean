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
# Conjugacy of Cartan involutions on the Lie algebra of a Lie group

For a finite-dimensional real Lie group `G` with Lie algebra `LeftInvariantDerivation I G`,
any two Cartan involutions `θ` and `θ'` are conjugate by `Ad (lieExp Z)` for some
`Z ∈ cartanP θ`.

This specializes the inner operator-exponential conjugacy theorem
`TauCeti.IsCartanInvolution.exists_exp_ad_conj_of_linearEquiv` to `LeftInvariantDerivation I G`
and identifies `exp (ad Z)` with `Ad (lieExp Z)` via `LeftInvariantDerivation.Ad_lieExp_apply`.

## Main results

* `TauCeti.exists_conj_cartanInvolution`: any two Cartan involutions `θ` and `θ'` of
  `LeftInvariantDerivation I G` satisfy `θ' (Ad (lieExp Z) Y) = Ad (lieExp Z) (θ Y)` for some
  `Z ∈ cartanP θ`.
* `TauCeti.exists_conj_cartanInvolution_equiv`: the equivalent bundled conjugation identity
  `((Ad (lieExp Z)).symm.trans θ).trans (Ad (lieExp Z)) = θ'`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §2, Theorem 6.16 and Corollary 6.19.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- **Conjugacy of Cartan involutions**: any two Cartan involutions `θ` and `θ'` of the Lie
algebra `LeftInvariantDerivation I G` of a finite-dimensional real Lie group `G` satisfy
`θ' (Ad (lieExp Z) Y) = Ad (lieExp Z) (θ Y)` for some `Z ∈ cartanP θ`. -/
theorem exists_conj_cartanInvolution
    {θ θ' : LeftInvariantDerivation I G ≃ₗ⁅ℝ⁆ LeftInvariantDerivation I G}
    (hθ : IsCartanInvolution θ) (hθ' : IsCartanInvolution θ') :
    ∃ Z ∈ cartanP θ, ∀ Y,
      θ' (TauCeti.Lie.Ad (I := I) (lieExp Z) Y) =
        TauCeti.Lie.Ad (I := I) (lieExp Z) (θ Y) := by
  have _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  obtain ⟨Z, hZ, hconj⟩ :=
    hθ.exists_exp_ad_conj_of_linearEquiv hθ' (LinearEquiv.refl ℝ (LeftInvariantDerivation I G))
  refine ⟨Z, hZ, fun Y ↦ ?_⟩
  have hY := LeftInvariantDerivation.Ad_lieExp_apply (I := I) (G := G) Z Y
  have hθY := LeftInvariantDerivation.Ad_lieExp_apply (I := I) (G := G) Z (θ Y)
  have hY' := hconj Y
  simp only [LinearEquiv.refl_symm, LinearEquiv.refl_apply, LinearEquiv.conj_refl] at hY'
  simpa only [← hY, ← hθY] using hY'

/-- Bundled equivalence form of `TauCeti.exists_conj_cartanInvolution`: any two Cartan involutions
`θ` and `θ'` of `LeftInvariantDerivation I G` are conjugate by `Ad (lieExp Z)` for some
`Z ∈ cartanP θ`. -/
theorem exists_conj_cartanInvolution_equiv
    {θ θ' : LeftInvariantDerivation I G ≃ₗ⁅ℝ⁆ LeftInvariantDerivation I G}
    (hθ : IsCartanInvolution θ) (hθ' : IsCartanInvolution θ') :
    ∃ Z ∈ cartanP θ,
      ((TauCeti.Lie.Ad (I := I) (lieExp Z)).symm.trans θ).trans
        (TauCeti.Lie.Ad (I := I) (lieExp Z)) = θ' := by
  obtain ⟨Z, hZ, hconj⟩ := exists_conj_cartanInvolution hθ hθ'
  refine ⟨Z, hZ, LieEquiv.ext fun Y ↦ ?_⟩
  simp only [LieEquiv.trans_apply]
  rw [← hconj ((TauCeti.Lie.Ad (I := I) (lieExp Z)).symm Y), LieEquiv.apply_symm_apply]

end TauCeti
