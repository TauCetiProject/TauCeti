/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.FreeLoop
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Character
public import TauCeti.Topology.PathSpace.Moore.Comparison.FundamentalGroup

/-!
# The orientation sign of a free loop

Let `M` be a topological manifold of dimension `d`. A free Moore loop `γ` in `M` is a loop at its
own base point, so the orientation character at that point assigns it a sign
`w₁(γ) ∈ {±1}` (`TauCeti.MooreFreeLoopSpace.orientationSign`): `1` when transport of local
orientations around `γ` preserves them, and `-1` when it reverses them. For a smooth manifold this
records whether the pullback of the tangent bundle along `γ` is orientable.

The sign is constant on the path components of the free loop space
(`TauCeti.MooreFreeLoopSpace.orientationSign_eq_of_joined`): freely homotopic loops have conjugate
classes after a change of base point along the track of the base point, and the orientation
character is invariant under both, being a character with values in an abelian group and
independent of the base point (`TauCeti.orientationCharacter_fundamentalGroupMulEquivOfPath`,
`TauCeti.apply_fromPath_eq_of_joined_toCircle`). The
statement for loops parametrized by the unit interval is
`TauCeti.orientationCharacter_eq_of_joined_toCircle`.

The sign is recorded as the exponent `w(γ)` of the source (§4.1): `0` when `γ` preserves the local
orientations and `-1` when it reverses them (`TauCeti.MooreFreeLoopSpace.orientationExponent`).
This exponent enters the degree-zero twist of the Viterbo isomorphism for cotangent bundles, whose
orientation part is the local system `ev₀^*(o_M^{-1}) ⊗ ev₀^*(o_M^{-w})` on the free loop space.

## Main definitions

* `TauCeti.MooreFreeLoopSpace.orientationSign`: the orientation character of a free loop.
* `TauCeti.MooreFreeLoopSpace.orientationExponent`: the exponent `w(γ) ∈ {0, -1}`.

## Main results

* `TauCeti.orientationCharacter_eq_of_joined_toCircle`: freely homotopic loops have the same
  orientation character.
* `TauCeti.MooreFreeLoopSpace.orientationSign_eq_of_joined`: the orientation sign is constant on
  the path components of the free loop space.
* `TauCeti.MooreFreeLoopSpace.orientationSign_const`: constant loops preserve the orientation.
* `TauCeti.HomologicalOrientation.orientationSign_eq_one`: on an orientable manifold every loop
  preserves the orientation.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.1.
-/

public section

noncomputable section

open Module

universe w

namespace TauCeti

variable {M E : Type w} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {d : ℕ}
  (hd : finrank ℝ E = d)

/-- **Freely homotopic loops have the same orientation character.** If two loops `ℓ₀` at `x` and
`ℓ₁` at `y` are joined in the free loop space `C(S¹, M)`, then the orientation character at `x`
of `ℓ₀` is the orientation character at `y` of `ℓ₁`. -/
theorem orientationCharacter_eq_of_joined_toCircle {x y : M} {ℓ₀ : Path x x} {ℓ₁ : Path y y}
    (h : Joined ℓ₀.toCircle ℓ₁.toCircle) :
    orientationCharacter hd x (.fromPath (Path.Homotopic.Quotient.mk ℓ₀)) =
      orientationCharacter hd y (.fromPath (Path.Homotopic.Quotient.mk ℓ₁)) :=
  apply_fromPath_eq_of_joined_toCircle (orientationCharacter hd)
    (orientationCharacter_fundamentalGroupMulEquivOfPath hd) h

namespace MooreFreeLoopSpace

/-- The **orientation sign** `w₁(γ) ∈ {±1}` of a free Moore loop `γ` in a manifold: the orientation
character at its base point of the class of `γ`, read as a loop there. It is `1` when transport of
local orientations around `γ` preserves them and `-1` when it reverses them. -/
def orientationSign (γ : MooreFreeLoopSpace M) : ℤˣ :=
  orientationCharacter hd γ.basepoint
    (MooreLoopSpace.fundamentalGroupHom γ.basepoint γ.toMooreLoop)

theorem orientationSign_def (γ : MooreFreeLoopSpace M) :
    orientationSign hd γ =
      orientationCharacter hd γ.basepoint
        (MooreLoopSpace.fundamentalGroupHom γ.basepoint γ.toMooreLoop) :=
  (rfl)

/-- The orientation sign of a free loop is the orientation character of the loop parametrized by
the unit interval. -/
theorem orientationSign_eq_orientationCharacter_toPath (γ : MooreFreeLoopSpace M) :
    orientationSign hd γ =
      orientationCharacter hd γ.basepoint
        (.fromPath (Path.Homotopic.Quotient.mk γ.toMooreLoop.toPath)) := by
  rw [orientationSign_def, MooreLoopSpace.fundamentalGroupHom_apply, map_inv,
    Int.units_inv_eq_self]

/-- **The orientation sign is constant on the path components of the free loop space**: freely
homotopic free loops preserve or reverse the local orientations together. -/
theorem orientationSign_eq_of_joined {γ γ' : MooreFreeLoopSpace M} (h : Joined γ γ') :
    orientationSign hd γ = orientationSign hd γ' := by
  have hcircle (δ : MooreFreeLoopSpace M) : toCircleMap δ = δ.toMooreLoop.toPath.toCircle := by
    simpa only [toFreeLoop_toMooreLoop] using toCircleMap_toFreeLoop_eq_toCircle _ δ.toMooreLoop
  have h' := h.map (toCircleMap (X := M)).continuous
  rw [hcircle, hcircle] at h'
  simp only [orientationSign_eq_orientationCharacter_toPath]
  exact orientationCharacter_eq_of_joined_toCircle hd h'

/-- **Constant loops preserve the orientation.** -/
@[simp]
theorem orientationSign_const (x : M) : orientationSign hd (const x) = 1 := by
  have h : (const x).toMooreLoop = 1 :=
    MooreLoopSpace.eq_one_of_length_eq_zero (by rw [length_toMooreLoop, length_const])
  rw [orientationSign_def, h, map_one, map_one]

/-- The exponent `w(γ)` of a free loop `γ` in the degree-zero twist of the Viterbo isomorphism:
`0` when `γ` preserves the local orientations and `-1` when it reverses them. -/
def orientationExponent (γ : MooreFreeLoopSpace M) : ℤ :=
  if orientationSign hd γ = 1 then 0 else -1

/-- A loop preserving the orientation has exponent `0`. -/
theorem orientationExponent_of_orientationSign_eq_one {γ : MooreFreeLoopSpace M}
    (h : orientationSign hd γ = 1) : orientationExponent hd γ = 0 := by
  simp [orientationExponent, h]

/-- A loop reversing the orientation has exponent `-1`. -/
theorem orientationExponent_of_orientationSign_ne_one {γ : MooreFreeLoopSpace M}
    (h : orientationSign hd γ ≠ 1) : orientationExponent hd γ = -1 := by
  simp [orientationExponent, h]

/-- The exponent is constant on the path components of the free loop space. -/
theorem orientationExponent_eq_of_joined {γ γ' : MooreFreeLoopSpace M} (h : Joined γ γ') :
    orientationExponent hd γ = orientationExponent hd γ' := by
  rw [orientationExponent, orientationExponent, orientationSign_eq_of_joined hd h]

/-- Constant loops have exponent `0`. -/
@[simp]
theorem orientationExponent_const (x : M) : orientationExponent hd (const x) = 0 :=
  orientationExponent_of_orientationSign_eq_one hd (orientationSign_const hd x)

end MooreFreeLoopSpace

/-- **On an orientable manifold every free loop preserves the orientation.** -/
theorem HomologicalOrientation.orientationSign_eq_one (o : HomologicalOrientation M E d)
    (γ : MooreFreeLoopSpace M) : MooreFreeLoopSpace.orientationSign hd γ = 1 := by
  rw [MooreFreeLoopSpace.orientationSign_def, o.orientationCharacter_eq_one hd,
    MonoidHom.one_apply]

end TauCeti
