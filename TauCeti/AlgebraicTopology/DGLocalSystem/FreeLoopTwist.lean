/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.RankOne
public import TauCeti.AlgebraicTopology.FundamentalGroup.FreeLoop
public import TauCeti.Topology.PathSpace.Moore.Rotation

/-!
# The twist of a sign character family on the free loop space

Let `χ` be a family of characters `π₁(X, x) →* ℤˣ` of the fundamental groups of a space `X`, and
`R` a commutative ring. At each point `x` let `o_x` be the rank-one DG local system whose monodromy
is `χ x` read in `Rˣ`; it is its own inverse. Let `w(γ)` be the sign exponent of a free Moore loop
`γ`, `0` when `χ` takes the value `1` on `γ` and `-1` otherwise
(`TauCeti.MooreFreeLoopSpace.signExponent`). The **twist** of `χ` at a free loop `γ` is the
rank-one local system

`ev₀^*(o⁻¹) ⊗ ev₀^*(o^{-w(γ)})`

on `(𝓛X, γ)`, pulled back along the evaluation `ev₀ : 𝓛X → X` at the base point
(`TauCeti.RankOneLocalSystem.freeLoopTwist`). This is the shape of the orientation factors of the
degree-zero twist `η₀` of Barraud–Damian–Humilière–Oancea (§4.1): the sign characters of the
orientation double cover of a vector bundle give `IsCoveringMap.freeLoopSignTwist`, and the
orientation characters of a manifold give `TauCeti.RankOneLocalSystem.viterboOrientationTwist`.

When `χ` takes the value `1` on `γ` the twist is `ev₀^* o`, and otherwise it is trivial, because
`o⁻¹ ⊗ o` is (`TauCeti.RankOneLocalSystem.freeLoopTwist_eq_pullback_of_apply_eq_one`,
`TauCeti.RankOneLocalSystem.freeLoopTwist_eq_one_of_apply_ne_one`). A loop of free loops acts
accordingly by `χ` of the loop traced by the base points, or trivially
(`TauCeti.RankOneLocalSystem.freeLoopTwist_ρ_apply`). The twist is its own inverse, and it is
trivial when `χ` is trivial at the base point or `2 = 0` in `R`. Along the constant loops it is `o`
(`TauCeti.RankOneLocalSystem.pullback_constMap_freeLoopTwist`).

The factor `ev₀^*(o^{-w})` is needed to make the twist trivial along rotations. Rotating a free
loop `γ` once around itself is a loop of free loops based at `γ` whose base points trace `γ`
(`TauCeti.MooreFreeLoopSpace.rotationLoop`). Along it `ev₀^* o` alone acts by `χ` of `γ`
(`TauCeti.RankOneLocalSystem.pullback_basepointMap_ofMonodromy_ρ_rotationLoop`), which is not
trivial when `χ` takes the value `-1` on `γ` and `2 ≠ 0`, while the twist acts trivially along the
rotation of every loop (`TauCeti.RankOneLocalSystem.freeLoopTwist_ρ_rotationLoop`).

## Main definitions

* `TauCeti.RankOneLocalSystem.freeLoopTwist`: the rank-one local system
  `ev₀^*(o⁻¹) ⊗ ev₀^*(o^{-w})` on the free loop space.

## Main results

* `TauCeti.RankOneLocalSystem.freeLoopTwist_eq_pullback_of_apply_eq_one`,
  `TauCeti.RankOneLocalSystem.freeLoopTwist_eq_one_of_apply_ne_one`: its value on each kind of
  component.
* `TauCeti.RankOneLocalSystem.freeLoopTwist_ρ_apply`,
  `TauCeti.RankOneLocalSystem.monodromy_freeLoopTwist`: its action and its monodromy.
* `TauCeti.RankOneLocalSystem.pullback_constMap_freeLoopTwist`: along the constant loops it is `o`.
* `TauCeti.RankOneLocalSystem.freeLoopTwist_ρ_rotationLoop`: it is trivial along the rotation of
  every loop.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §§1.5 and 4.1.
-/

public section

noncomputable section

namespace TauCeti

open MooreFreeLoopSpace

namespace RankOneLocalSystem

variable {X : Type*} [TopologicalSpace X] (R : Type*) [CommRing R]
  (χ : ∀ x : X, FundamentalGroup X x →* ℤˣ)

/-- **The twist of a family of sign characters** `χ` at a free loop `γ`: the rank-one local system
`ev₀^*(o⁻¹) ⊗ ev₀^*(o^{-w(γ)})` on `(𝓛X, γ)`, where `o` is the rank-one local system with monodromy
`χ` read in `Rˣ`, `w` the sign exponent of `χ` and `ev₀ : 𝓛X → X` the evaluation at the base
point. -/
def freeLoopTwist (γ : MooreFreeLoopSpace X) : RankOneLocalSystem (MooreFreeLoopSpace X) γ R :=
  pullback (basepointMap X) (basepointMap_apply γ)
      (ofMonodromy ((Units.map (Int.castRingHom R).toMonoidHom).comp (χ γ.basepoint)))⁻¹ *
    pullback (basepointMap X) (basepointMap_apply γ)
      (ofMonodromy ((Units.map (Int.castRingHom R).toMonoidHom).comp (χ γ.basepoint)) ^
        (-signExponent χ γ))

variable {R χ}

theorem freeLoopTwist_def (γ : MooreFreeLoopSpace X) :
    freeLoopTwist R χ γ =
      pullback (basepointMap X) (basepointMap_apply γ)
          (ofMonodromy ((Units.map (Int.castRingHom R).toMonoidHom).comp (χ γ.basepoint)))⁻¹ *
        pullback (basepointMap X) (basepointMap_apply γ)
          (ofMonodromy ((Units.map (Int.castRingHom R).toMonoidHom).comp (χ γ.basepoint)) ^
            (-signExponent χ γ)) :=
  (rfl)

/-- **Where `χ` takes the value `1` on `γ`, the twist is `ev₀^* o`.** -/
theorem freeLoopTwist_eq_pullback_of_apply_eq_one {γ : MooreFreeLoopSpace X}
    (h : χ γ.basepoint (MooreLoopSpace.fundamentalGroupHom γ.basepoint γ.toMooreLoop) = 1) :
    freeLoopTwist R χ γ =
      pullback (basepointMap X) (basepointMap_apply γ)
        (ofMonodromy ((Units.map (Int.castRingHom R).toMonoidHom).comp (χ γ.basepoint))) := by
  rw [freeLoopTwist_def, (signExponent_eq_zero_iff χ γ).2 h, neg_zero, zpow_zero, map_one, mul_one,
    inv_ofMonodromy_unitsMap_comp]

/-- **Where `χ` takes the value `-1` on `γ`, the twist is trivial**: there it is
`ev₀^*(o⁻¹ ⊗ o)`. -/
theorem freeLoopTwist_eq_one_of_apply_ne_one {γ : MooreFreeLoopSpace X}
    (h : χ γ.basepoint (MooreLoopSpace.fundamentalGroupHom γ.basepoint γ.toMooreLoop) ≠ 1) :
    freeLoopTwist R χ γ = 1 := by
  rw [freeLoopTwist_def,
    (signExponent_eq_neg_one_iff χ γ).2 ((Int.units_eq_one_or _).resolve_left h), neg_neg,
    zpow_one, ← map_mul, inv_mul_cancel, map_one]

/-- **The action on the twist**: a loop `Γ` of free loops based at `γ` acts by `χ` of the loop
`ev₀ ∘ Γ` traced by the base points when `χ` takes the value `1` on `γ`, and trivially
otherwise. -/
theorem freeLoopTwist_ρ_apply (γ : MooreFreeLoopSpace X)
    (Γ : MooreLoopSpace (MooreFreeLoopSpace X) γ) :
    (freeLoopTwist R χ γ).ρ Γ =
      if χ γ.basepoint (MooreLoopSpace.fundamentalGroupHom γ.basepoint γ.toMooreLoop) = 1 then
        Units.map (Int.castRingHom R).toMonoidHom
          (χ γ.basepoint (MooreLoopSpace.fundamentalGroupHom γ.basepoint
            (MooreLoopSpace.map (basepointMap X) (basepointMap_apply γ) Γ)))
      else 1 := by
  split_ifs with h
  · rw [freeLoopTwist_eq_pullback_of_apply_eq_one h, pullback_ρ_apply,
      ofMonodromy_unitsMap_comp_ρ_apply]
  · rw [freeLoopTwist_eq_one_of_apply_ne_one h, one_ρ, MonoidHom.one_apply]

/-- The monodromy of the twist: `χ` composed with the map of fundamental groups induced by
evaluation at the base point, read in `Rˣ`, when `χ` takes the value `1` on `γ`, and trivial
otherwise. -/
theorem monodromy_freeLoopTwist (γ : MooreFreeLoopSpace X) :
    (freeLoopTwist R χ γ).monodromy =
      if χ γ.basepoint (MooreLoopSpace.fundamentalGroupHom γ.basepoint γ.toMooreLoop) = 1 then
        ((Units.map (Int.castRingHom R).toMonoidHom).comp (χ γ.basepoint)).comp
          (FundamentalGroup.mapOfEq (basepointMap X) (basepointMap_apply γ))
      else 1 := by
  split_ifs with h
  · rw [freeLoopTwist_eq_pullback_of_apply_eq_one h, monodromy_pullback, monodromy_ofMonodromy]
  · rw [freeLoopTwist_eq_one_of_apply_ne_one h, monodromy_one]

/-- **The twist is its own inverse.** -/
@[simp]
theorem inv_freeLoopTwist (γ : MooreFreeLoopSpace X) :
    (freeLoopTwist R χ γ)⁻¹ = freeLoopTwist R χ γ := by
  by_cases h : χ γ.basepoint (MooreLoopSpace.fundamentalGroupHom γ.basepoint γ.toMooreLoop) = 1
  · rw [freeLoopTwist_eq_pullback_of_apply_eq_one h, ← map_inv, inv_ofMonodromy_unitsMap_comp]
  · rw [freeLoopTwist_eq_one_of_apply_ne_one h, inv_one]

/-- **The twist is defined over `ℤ`**: extending its coefficients along a ring homomorphism
`φ : R →+* R'` gives the twist of the same family of sign characters with coefficients in `R'`. -/
@[simp]
theorem mapRingHom_freeLoopTwist {R' : Type*} [CommRing R'] (φ : R →+* R')
    (γ : MooreFreeLoopSpace X) : mapRingHom φ (freeLoopTwist R χ γ) = freeLoopTwist R' χ γ := by
  simp only [freeLoopTwist_def, RingHom.toMonoidHom_eq_coe, map_mul, mapRingHom_pullback, map_inv,
    map_zpow, mapRingHom_ofMonodromy_unitsMap_comp]

/-- A character trivial at the base point gives a trivial twist. -/
theorem freeLoopTwist_eq_one {γ : MooreFreeLoopSpace X} (h : χ γ.basepoint = 1) :
    freeLoopTwist R χ γ = 1 := by
  rw [freeLoopTwist_def, (ofMonodromy_unitsMap_comp_eq_one_iff _).2 (.inl h), inv_one, one_zpow,
    map_one, one_mul]

/-- **Over a ring of characteristic two the twist is trivial.** -/
theorem freeLoopTwist_eq_one_of_two_eq_zero (h2 : (2 : R) = 0) (γ : MooreFreeLoopSpace X) :
    freeLoopTwist R χ γ = 1 := by
  rw [freeLoopTwist_def, (ofMonodromy_unitsMap_comp_eq_one_iff _).2 (.inr h2), inv_one, one_zpow,
    map_one, one_mul]

/-! ### Constant loops -/

/-- **Along the constant loops the twist is `o`**: its pullback along the inclusion `X → 𝓛X` of the
constant loops is the rank-one local system with monodromy `χ` read in `Rˣ`. -/
theorem pullback_constMap_freeLoopTwist (x : X) :
    pullback (constMap X) (constMap_apply x) (freeLoopTwist R χ (const x)) =
      ofMonodromy ((Units.map (Int.castRingHom R).toMonoidHom).comp (χ x)) := by
  refine RankOneLocalSystem.ext <| MonoidHom.ext fun δ ↦ ?_
  rw [freeLoopTwist_eq_pullback_of_apply_eq_one (by rw [toMooreLoop_const, map_one, map_one]),
    pullback_ρ_apply, pullback_ρ_apply, ofMonodromy_unitsMap_comp_ρ_apply,
    ofMonodromy_unitsMap_comp_ρ_apply]
  congr 1
  exact MooreLoopSpace.apply_fundamentalGroupHom_congr χ <| MoorePath.ext (by simp) fun t ↦ by
    simp [MoorePath.map_apply]

/-! ### The rotation of a loop -/

/-- **Along the rotation of a loop `γ`, the pullback `ev₀^* o` acts by `χ` of `γ`**, since the
base points of the rotation loop trace `γ`. -/
theorem pullback_basepointMap_ofMonodromy_ρ_rotationLoop (γ : MooreFreeLoopSpace X) :
    (pullback (basepointMap X) (basepointMap_apply γ)
        (ofMonodromy ((Units.map (Int.castRingHom R).toMonoidHom).comp (χ γ.basepoint)))).ρ
        γ.rotationLoop =
      Units.map (Int.castRingHom R).toMonoidHom
        (χ γ.basepoint (MooreLoopSpace.fundamentalGroupHom γ.basepoint γ.toMooreLoop)) := by
  rw [pullback_ρ_apply, map_basepointMap_rotationLoop, ofMonodromy_unitsMap_comp_ρ_apply]

/-- **The pullback `ev₀^* o` alone is nontrivial along the rotation of a loop on which `χ` is not
`1`**, over a ring in which `2 ≠ 0`. So the factor `ev₀^*(o^{-w})` of the twist is needed to make
it trivial along rotations (`TauCeti.RankOneLocalSystem.freeLoopTwist_ρ_rotationLoop`). -/
theorem pullback_basepointMap_ofMonodromy_ρ_rotationLoop_ne_one (h2 : (2 : R) ≠ 0)
    {γ : MooreFreeLoopSpace X}
    (h : χ γ.basepoint (MooreLoopSpace.fundamentalGroupHom γ.basepoint γ.toMooreLoop) ≠ 1) :
    (pullback (basepointMap X) (basepointMap_apply γ)
        (ofMonodromy ((Units.map (Int.castRingHom R).toMonoidHom).comp (χ γ.basepoint)))).ρ
      γ.rotationLoop ≠ 1 := by
  rw [pullback_basepointMap_ofMonodromy_ρ_rotationLoop, Ne, Int.unitsMap_castRingHom_eq_one_iff]
  exact not_or_intro h h2

/-- **The twist is trivial along the rotation of every loop.** -/
@[simp]
theorem freeLoopTwist_ρ_rotationLoop (γ : MooreFreeLoopSpace X) :
    (freeLoopTwist R χ γ).ρ γ.rotationLoop = 1 := by
  by_cases h : χ γ.basepoint (MooreLoopSpace.fundamentalGroupHom γ.basepoint γ.toMooreLoop) = 1
  · rw [freeLoopTwist_eq_pullback_of_apply_eq_one h,
      pullback_basepointMap_ofMonodromy_ρ_rotationLoop, h, map_one]
  · rw [freeLoopTwist_eq_one_of_apply_ne_one h, one_ρ, MonoidHom.one_apply]

end RankOneLocalSystem

end TauCeti
