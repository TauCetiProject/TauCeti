/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Orientation
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.FreeLoop
public import TauCeti.Topology.PathSpace.Moore.Rotation

/-!
# The orientation part of the Viterbo twist

Let `M` be a topological manifold of dimension `d` and `R` a commutative ring. The Viterbo
isomorphism for the cotangent bundle of `M` identifies symplectic homology with the homology of
the free loop space `𝓛M` twisted by a degree-zero rank-one local system `η₀` (Barraud–Damian–
Humilière–Oancea, §§1.5 and 4.1). It is the product `σ ⊗ ev₀^*(o_M^{-1}) ⊗ ev₀^*(o_M^{-w})` of a
sign system `σ` built from the second Stiefel–Whitney class of `M` with an orientation part, where
`o_M` is the orientation local system of `M` (`TauCeti.RankOneLocalSystem.orientation`),
`ev₀ : 𝓛M → M` is evaluation at the base point, and `w(γ)` is `0` on the loops along which `M` is
orientable and `-1` on the others (`TauCeti.MooreFreeLoopSpace.orientationExponent`). This file
constructs the orientation part

`ev₀^*(o_M^{-1}) ⊗ ev₀^*(o_M^{-w(γ)})`

as a rank-one local system on the free loop space based at a free loop `γ`
(`TauCeti.RankOneLocalSystem.viterboOrientationTwist`). The exponent `w` is constant on the path
components of `𝓛M` (`TauCeti.MooreFreeLoopSpace.orientationExponent_eq_of_joined`), so the formula
defines one local system on each component, read at any base point there.

Since `o_M` is its own inverse, the orientation part is `ev₀^* o_M` on the component of a loop
preserving the local orientations
(`TauCeti.RankOneLocalSystem.viterboOrientationTwist_of_orientationSign_eq_one`), and trivial on
the component of a loop reversing them
(`TauCeti.RankOneLocalSystem.viterboOrientationTwist_of_orientationSign_ne_one`). A loop of free
loops acts accordingly by the orientation character of the loop traced by the base points, or
trivially (`TauCeti.RankOneLocalSystem.viterboOrientationTwist_ρ_apply`). It is trivial on an
orientable manifold and over a ring in which `2 = 0`, and it is its own inverse.

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

* `TauCeti.RankOneLocalSystem.viterboOrientationTwist_of_orientationSign_eq_one`,
  `TauCeti.RankOneLocalSystem.viterboOrientationTwist_of_orientationSign_ne_one`: it is `ev₀^* o_M`
  on the orientable components and trivial on the others.
* `TauCeti.RankOneLocalSystem.viterboOrientationTwist_ρ_apply`,
  `TauCeti.RankOneLocalSystem.monodromy_viterboOrientationTwist`: its action and its monodromy.
* `TauCeti.RankOneLocalSystem.viterboOrientationTwist_ρ_rotationLoop`: it is trivial along the
  rotation of every loop, while `ev₀^* o_M` is not
  (`TauCeti.RankOneLocalSystem.pullback_basepointMap_orientation_ρ_rotationLoop_ne_one`).
* `TauCeti.RankOneLocalSystem.pullback_constMap_viterboOrientationTwist`: along the constant loops
  it is the orientation local system.

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
exponent `TauCeti.MooreFreeLoopSpace.orientationExponent`, `0` when `γ` preserves the local
orientations and `-1` when it reverses them. -/
def viterboOrientationTwist (γ : MooreFreeLoopSpace M) :
    RankOneLocalSystem (MooreFreeLoopSpace M) γ R :=
  pullback (basepointMap M) (basepointMap_apply γ) (orientation R hd γ.basepoint)⁻¹ *
    pullback (basepointMap M) (basepointMap_apply γ)
      (orientation R hd γ.basepoint ^ (-orientationExponent hd γ))

variable {R}

theorem viterboOrientationTwist_def (γ : MooreFreeLoopSpace M) :
    viterboOrientationTwist R hd γ =
      pullback (basepointMap M) (basepointMap_apply γ) (orientation R hd γ.basepoint)⁻¹ *
        pullback (basepointMap M) (basepointMap_apply γ)
          (orientation R hd γ.basepoint ^ (-orientationExponent hd γ)) :=
  (rfl)

/-- **On the component of a loop preserving the orientation, the orientation part of the Viterbo
twist is `ev₀^* o_M`.** -/
theorem viterboOrientationTwist_of_orientationSign_eq_one {γ : MooreFreeLoopSpace M}
    (h : orientationSign hd γ = 1) :
    viterboOrientationTwist R hd γ =
      pullback (basepointMap M) (basepointMap_apply γ) (orientation R hd γ.basepoint) := by
  rw [viterboOrientationTwist_def, orientationExponent_of_orientationSign_eq_one hd h, neg_zero,
    zpow_zero, map_one, mul_one, inv_orientation]

/-- **On the component of a loop reversing the orientation, the orientation part of the Viterbo
twist is trivial.** -/
theorem viterboOrientationTwist_of_orientationSign_ne_one {γ : MooreFreeLoopSpace M}
    (h : orientationSign hd γ ≠ 1) : viterboOrientationTwist R hd γ = 1 := by
  rw [viterboOrientationTwist_def, orientationExponent_of_orientationSign_ne_one hd h, neg_neg,
    zpow_one, ← map_mul, inv_mul_cancel, map_one]

/-- A loop `Γ` of free loops based at `γ` acts on the orientation part of the Viterbo twist by the
orientation character of the loop traced by the base points when `γ` preserves the orientation,
and trivially when `γ` reverses it. -/
theorem viterboOrientationTwist_ρ_apply (γ : MooreFreeLoopSpace M)
    (Γ : MooreLoopSpace (MooreFreeLoopSpace M) γ) :
    (viterboOrientationTwist R hd γ).ρ Γ =
      if orientationSign hd γ = 1 then
        Units.map (Int.castRingHom R).toMonoidHom
          (orientationCharacter hd γ.basepoint (MooreLoopSpace.fundamentalGroupHom γ.basepoint
            (MooreLoopSpace.map (basepointMap M) (basepointMap_apply γ) Γ)))
      else 1 := by
  split_ifs with h
  · rw [viterboOrientationTwist_of_orientationSign_eq_one hd h, pullback_ρ_apply,
      orientation_ρ_apply]
  · rw [viterboOrientationTwist_of_orientationSign_ne_one hd h, one_ρ, MonoidHom.one_apply]

/-- The monodromy of the orientation part of the Viterbo twist: the orientation character of `M`
composed with the map of fundamental groups induced by evaluation at the base point, when `γ`
preserves the orientation, and trivial when it reverses it. -/
theorem monodromy_viterboOrientationTwist (γ : MooreFreeLoopSpace M) :
    (viterboOrientationTwist R hd γ).monodromy =
      if orientationSign hd γ = 1 then
        ((Units.map (Int.castRingHom R).toMonoidHom).comp
          (orientationCharacter hd γ.basepoint)).comp
            (FundamentalGroup.mapOfEq (basepointMap M) (basepointMap_apply γ))
      else 1 := by
  split_ifs with h
  · rw [viterboOrientationTwist_of_orientationSign_eq_one hd h, monodromy_pullback,
      monodromy_orientation]
  · rw [viterboOrientationTwist_of_orientationSign_ne_one hd h, monodromy_one]

/-- **The orientation part of the Viterbo twist is its own inverse.** -/
@[simp]
theorem inv_viterboOrientationTwist (γ : MooreFreeLoopSpace M) :
    (viterboOrientationTwist R hd γ)⁻¹ = viterboOrientationTwist R hd γ := by
  by_cases h : orientationSign hd γ = 1
  · rw [viterboOrientationTwist_of_orientationSign_eq_one hd h, ← map_inv, inv_orientation]
  · rw [viterboOrientationTwist_of_orientationSign_ne_one hd h, inv_one]

/-- **Over a ring of characteristic two the orientation part of the Viterbo twist is trivial.** -/
theorem viterboOrientationTwist_eq_one_of_two_eq_zero (h2 : (2 : R) = 0)
    (γ : MooreFreeLoopSpace M) : viterboOrientationTwist R hd γ = 1 := by
  rw [viterboOrientationTwist_def, orientation_eq_one_of_two_eq_zero h2, inv_one, one_zpow,
    map_one, one_mul]

/-! ### The rotation of a loop -/

/-- **Along the rotation of a loop `γ`, the pullback `ev₀^* o_M` of the orientation local system
acts by the orientation sign of `γ`**, since the base points of the rotation loop trace `γ`. -/
theorem pullback_basepointMap_orientation_ρ_rotationLoop (γ : MooreFreeLoopSpace M) :
    (pullback (basepointMap M) (basepointMap_apply γ) (orientation R hd γ.basepoint)).ρ
        γ.rotationLoop =
      Units.map (Int.castRingHom R).toMonoidHom (orientationSign hd γ) := by
  rw [pullback_ρ_apply, map_basepointMap_rotationLoop, orientation_ρ_apply, orientationSign_def]

/-- **The pullback `ev₀^* o_M` alone is nontrivial along the rotation of a loop reversing the
orientation**, over a ring in which `2 ≠ 0`. So the factor `ev₀^*(o_M^{-w})` of the Viterbo twist
is needed to make it trivial along rotations
(`TauCeti.RankOneLocalSystem.viterboOrientationTwist_ρ_rotationLoop`). -/
theorem pullback_basepointMap_orientation_ρ_rotationLoop_ne_one (h2 : (2 : R) ≠ 0)
    {γ : MooreFreeLoopSpace M} (h : orientationSign hd γ ≠ 1) :
    (pullback (basepointMap M) (basepointMap_apply γ) (orientation R hd γ.basepoint)).ρ
      γ.rotationLoop ≠ 1 := by
  rw [pullback_basepointMap_orientation_ρ_rotationLoop, Ne, Int.unitsMap_castRingHom_eq_one_iff]
  exact not_or_intro h h2

/-- **The orientation part of the Viterbo twist is trivial along the rotation of every loop.** -/
@[simp]
theorem viterboOrientationTwist_ρ_rotationLoop (γ : MooreFreeLoopSpace M) :
    (viterboOrientationTwist R hd γ).ρ γ.rotationLoop = 1 := by
  by_cases h : orientationSign hd γ = 1
  · rw [viterboOrientationTwist_of_orientationSign_eq_one hd h,
      pullback_basepointMap_orientation_ρ_rotationLoop, h, map_one]
  · rw [viterboOrientationTwist_of_orientationSign_ne_one hd h, one_ρ, MonoidHom.one_apply]

/-! ### Constant loops -/

/-- Moore loops in `M` with the same underlying Moore path have the same orientation character,
even when their base points are only propositionally equal. -/
private theorem orientationCharacter_fundamentalGroupHom_congr {x y : M}
    {α : MooreLoopSpace M y} {β : MooreLoopSpace M x} (h : α.toMoorePath = β.toMoorePath) :
    orientationCharacter hd y (MooreLoopSpace.fundamentalGroupHom y α) =
      orientationCharacter hd x (MooreLoopSpace.fundamentalGroupHom x β) := by
  obtain rfl : y = x := by rw [← α.source_eq, h, β.source_eq]
  rw [MooreLoopSpace.ext h]

/-- **Along the constant loops, the orientation part of the Viterbo twist is the orientation local
system**: its pullback along the inclusion `M → 𝓛M` of the constant loops is `o_M`. -/
theorem pullback_constMap_viterboOrientationTwist (x : M) :
    pullback (constMap M) (constMap_apply x) (viterboOrientationTwist R hd (const x)) =
      orientation R hd x :=
  RankOneLocalSystem.ext <| MonoidHom.ext fun δ ↦ by
    rw [viterboOrientationTwist_of_orientationSign_eq_one hd (orientationSign_const hd x),
      pullback_ρ_apply, pullback_ρ_apply, orientation_ρ_apply, orientation_ρ_apply]
    congr 1
    exact orientationCharacter_fundamentalGroupHom_congr hd <| MoorePath.ext (by simp) fun t ↦ by
      simp [MoorePath.map_apply]

end RankOneLocalSystem

/-- **On an orientable manifold the orientation part of the Viterbo twist is trivial.** -/
theorem HomologicalOrientation.viterboOrientationTwist_eq_one (o : HomologicalOrientation M E d)
    (γ : MooreFreeLoopSpace M) : RankOneLocalSystem.viterboOrientationTwist R hd γ = 1 := by
  rw [RankOneLocalSystem.viterboOrientationTwist_of_orientationSign_eq_one hd
      (o.orientationSign_eq_one hd γ), o.rankOneLocalSystem_orientation_eq_one R hd, map_one]

end TauCeti
