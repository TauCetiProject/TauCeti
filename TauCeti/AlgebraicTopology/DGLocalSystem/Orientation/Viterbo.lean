/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.FreeLoopTwist
public import TauCeti.AlgebraicTopology.DGLocalSystem.Orientation.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.FreeLoop

/-!
# The orientation part of the Viterbo twist

Let `M` be a topological manifold of dimension `d` and `R` a commutative ring. The Viterbo
isomorphism for the cotangent bundle of `M` identifies symplectic homology with the homology of
the free loop space `𝓛M` twisted by a degree-zero rank-one local system `η₀` (Barraud–Damian–
Humilière–Oancea, §§1.5 and 4.1). It is the product `σ ⊗ ev₀^*(o_M^{-1}) ⊗ ev₀^*(o_M^{-w})` of a
sign system `σ` built from the second Stiefel–Whitney class of `M` with an orientation part, where
`o_M` is the orientation local system of `M` (`TauCeti.RankOneLocalSystem.orientation`),
`ev₀ : 𝓛M → M` is evaluation at the base point, and `w(γ)` is `0` on the loops along which `M` is
orientable and `-1` on the others: the sign exponent
`TauCeti.MooreFreeLoopSpace.signExponent` of the orientation characters of `M`, constant on the
path components of `𝓛M`. This file constructs the orientation part

`ev₀^*(o_M^{-1}) ⊗ ev₀^*(o_M^{-w(γ)})`

as a rank-one local system on the free loop space based at a free loop `γ`
(`TauCeti.RankOneLocalSystem.viterboOrientationTwist`,
`TauCeti.RankOneLocalSystem.viterboOrientationTwist_def`). It is the twist
`TauCeti.RankOneLocalSystem.freeLoopTwist` of the family of orientation characters of `M`
(`TauCeti.RankOneLocalSystem.viterboOrientationTwist_eq_freeLoopTwist`), so the general laws of
that twist apply: since `o_M` is its own inverse, it is `ev₀^* o_M` on the component of a loop
preserving the local orientations and trivial on the component of a loop reversing them, a loop
of free loops acts accordingly by the orientation character of the loop traced by the base points
or trivially, it is its own inverse, and it is trivial over a ring in which `2 = 0`. It is trivial
on an orientable manifold.

The factor `ev₀^*(o_M^{-w})` is needed. Rotating a free loop `γ` once around itself is a loop of
free loops based at `γ` whose base points trace `γ`
(`TauCeti.MooreFreeLoopSpace.rotationLoop`). Along it `ev₀^* o_M` alone acts by the orientation
sign of `γ` (`TauCeti.RankOneLocalSystem.pullback_basepointMap_orientation_ρ_rotationLoop`), which
is `-1` on a loop reversing the orientation, so this factor is a nontrivial local system there as
soon as `2 ≠ 0`. The orientation part acts trivially along the rotation of every loop
(`TauCeti.RankOneLocalSystem.viterboOrientationTwist_ρ_rotationLoop`). Along the constant loops the
orientation part restricts to the orientation local system of `M`
(`TauCeti.RankOneLocalSystem.pullback_constMap_viterboOrientationTwist`), its contribution to the
identification `i_M^* η₀ ≃ o_M` of the twist along the constant loops.

## Main definitions

* `TauCeti.RankOneLocalSystem.viterboOrientationTwist`: the orientation part
  `ev₀^*(o_M^{-1}) ⊗ ev₀^*(o_M^{-w})` of the Viterbo twist.

## Main results

* `TauCeti.RankOneLocalSystem.viterboOrientationTwist_ρ_rotationLoop`: it is trivial along the
  rotation of every loop, while `ev₀^* o_M` is not trivial along the rotation of an
  orientation-reversing loop when `2 ≠ 0`
  (`TauCeti.RankOneLocalSystem.pullback_basepointMap_orientation_ρ_rotationLoop_ne_one`).
* `TauCeti.RankOneLocalSystem.pullback_constMap_viterboOrientationTwist`: along the constant loops
  it is the orientation local system.
* `TauCeti.HomologicalOrientation.viterboOrientationTwist_eq_one`: it is trivial on an orientable
  manifold.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §§1.5 and 4.1.
-/

public section

noncomputable section

open Module

universe w

namespace TauCeti

open MooreFreeLoopSpace

variable {M E : Type w} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {d : ℕ}
  (R : Type*) [CommRing R] (hd : finrank ℝ E = d)

namespace RankOneLocalSystem

/-- The **orientation part of the Viterbo twist**, `ev₀^*(o_M^{-1}) ⊗ ev₀^*(o_M^{-w})`, as a
rank-one local system on the free loop space of a manifold `M` based at a free loop `γ`: `o_M` is
the orientation local system of `M`, pulled back along evaluation at the base point, and `w` is the
sign exponent of the orientation characters, `0` when `γ` preserves the local orientations and
`-1` when it reverses them. It is the twist `TauCeti.RankOneLocalSystem.freeLoopTwist` of the
family of orientation characters. -/
def viterboOrientationTwist (γ : MooreFreeLoopSpace M) :
    RankOneLocalSystem (MooreFreeLoopSpace M) γ R :=
  freeLoopTwist R (orientationCharacter hd) γ

variable {R}

theorem viterboOrientationTwist_eq_freeLoopTwist (γ : MooreFreeLoopSpace M) :
    viterboOrientationTwist R hd γ = freeLoopTwist R (orientationCharacter hd) γ :=
  (rfl)

/-- The orientation part of the Viterbo twist is the tensor product
`ev₀^*(o_M^{-1}) ⊗ ev₀^*(o_M^{-w(γ)})` of two pullbacks of the orientation local system along the
evaluation at the base point. -/
theorem viterboOrientationTwist_def (γ : MooreFreeLoopSpace M) :
    viterboOrientationTwist R hd γ =
      pullback (basepointMap M) (basepointMap_apply γ) (orientation R hd γ.basepoint)⁻¹ *
        pullback (basepointMap M) (basepointMap_apply γ)
          (orientation R hd γ.basepoint ^ (-signExponent (orientationCharacter hd) γ)) := by
  rw [viterboOrientationTwist_eq_freeLoopTwist, freeLoopTwist_def, orientation_def]

/-! ### The rotation of a loop -/

/-- **Along the rotation of a loop `γ`, the pullback `ev₀^* o_M` of the orientation local system
acts by the orientation sign of `γ`**, since the base points of the rotation loop trace `γ`. -/
theorem pullback_basepointMap_orientation_ρ_rotationLoop (γ : MooreFreeLoopSpace M) :
    (pullback (basepointMap M) (basepointMap_apply γ) (orientation R hd γ.basepoint)).ρ
        γ.rotationLoop =
      Units.map (Int.castRingHom R).toMonoidHom (orientationSign hd γ) := by
  rw [orientation_def, pullback_basepointMap_ofMonodromy_ρ_rotationLoop, orientationSign_def]

/-- **The pullback `ev₀^* o_M` alone is nontrivial along the rotation of a loop reversing the
orientation**, over a ring in which `2 ≠ 0`. So the factor `ev₀^*(o_M^{-w})` of the Viterbo twist
is needed to make it trivial along rotations
(`TauCeti.RankOneLocalSystem.viterboOrientationTwist_ρ_rotationLoop`). -/
theorem pullback_basepointMap_orientation_ρ_rotationLoop_ne_one (h2 : (2 : R) ≠ 0)
    {γ : MooreFreeLoopSpace M} (h : orientationSign hd γ ≠ 1) :
    (pullback (basepointMap M) (basepointMap_apply γ) (orientation R hd γ.basepoint)).ρ
      γ.rotationLoop ≠ 1 := by
  rw [orientationSign_def] at h
  rw [orientation_def]
  exact pullback_basepointMap_ofMonodromy_ρ_rotationLoop_ne_one h2 h

/-- **The orientation part of the Viterbo twist is trivial along the rotation of every loop.** -/
@[simp]
theorem viterboOrientationTwist_ρ_rotationLoop (γ : MooreFreeLoopSpace M) :
    (viterboOrientationTwist R hd γ).ρ γ.rotationLoop = 1 :=
  freeLoopTwist_ρ_rotationLoop γ

/-! ### Constant loops -/

/-- **Along the constant loops, the orientation part of the Viterbo twist is the orientation local
system**: its pullback along the inclusion `M → 𝓛M` of the constant loops is `o_M`. -/
theorem pullback_constMap_viterboOrientationTwist (x : M) :
    pullback (constMap M) (constMap_apply x) (viterboOrientationTwist R hd (const x)) =
      orientation R hd x := by
  rw [viterboOrientationTwist_eq_freeLoopTwist, pullback_constMap_freeLoopTwist, orientation_def]

end RankOneLocalSystem

/-- **On an orientable manifold the orientation part of the Viterbo twist is trivial.** -/
theorem HomologicalOrientation.viterboOrientationTwist_eq_one (o : HomologicalOrientation M E d)
    (γ : MooreFreeLoopSpace M) : RankOneLocalSystem.viterboOrientationTwist R hd γ = 1 :=
  RankOneLocalSystem.freeLoopTwist_eq_one (o.orientationCharacter_eq_one hd γ.basepoint)

end TauCeti
