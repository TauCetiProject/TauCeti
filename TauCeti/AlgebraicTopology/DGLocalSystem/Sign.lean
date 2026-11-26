/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.FreeLoopTwist
public import TauCeti.Topology.Homotopy.Monodromy.SignCharacter

/-!
# The sign local system of a covering as a rank-one DG local system

Let `p : E → X` be a covering map whose fibre over `x` is finite, for instance the orientation
double cover of a real vector bundle `V → X`. Its **sign local system** `o` at `x` is the rank-one
DG local system whose monodromy is the sign character `π₁(X, x) →* ℤˣ` of the cover, read in the
coefficient ring (`IsCoveringMap.signRankOneLocalSystem`): a Moore loop acts by the sign of the
permutation of the fibre given by path lifting along it
(`IsCoveringMap.signRankOneLocalSystem_ρ_apply`). It is its own inverse
(`IsCoveringMap.inv_signRankOneLocalSystem`), and it is trivial when the sign character is
(`IsCoveringMap.signRankOneLocalSystem_eq_one`).

When every fibre is finite, let `w(γ)` be the sign exponent of a free loop `γ` on the Moore free
loop space `𝓛X`: `0` when `γ` has sign `1` and `-1` otherwise
(`IsCoveringMap.freeLoopSignExponent`). The **sign twist** at a free loop `γ₀` is the rank-one
local system

`ev₀^*(o⁻¹) ⊗ ev₀^*(o^{-w(γ₀)})`

on `(𝓛X, γ₀)`, pulled back along the evaluation `ev₀ : 𝓛X → X` at the base point
(`IsCoveringMap.freeLoopSignTwist`, `IsCoveringMap.freeLoopSignTwist_def`), the twist
`TauCeti.RankOneLocalSystem.freeLoopTwist` of the family of sign characters. On the components where
`w = 0` it is `ev₀^*(o⁻¹)`, and on the components where `w = -1` it is trivial, because `o⁻¹ ⊗ o`
is (`IsCoveringMap.freeLoopSignTwist_eq_pullback_of_freeLoopSignCharacter_eq_one`,
`IsCoveringMap.freeLoopSignTwist_eq_one_of_freeLoopSignCharacter_eq_neg_one`). A loop of free
loops `Γ` acts by the sign of the loop `ev₀ ∘ Γ` traced by the base points on the first kind of
component, and trivially on the second (`IsCoveringMap.freeLoopSignTwist_ρ_apply`). If the sign
character is trivial, the twist is trivial (`IsCoveringMap.freeLoopSignTwist_eq_one`). For the
orientation double cover of a real vector bundle this is the orientation twist of
`TauCeti.AlgebraicTopology.DGLocalSystem.Orientation.Twist`.

## Main definitions

* `IsCoveringMap.signRankOneLocalSystem`: the sign local system of a covering with finite fibres,
  as a rank-one DG local system.
* `IsCoveringMap.freeLoopSignTwist`: the rank-one local system `ev₀^*(o⁻¹) ⊗ ev₀^*(o^{-w})` on the
  free loop space.

## Main results

* `IsCoveringMap.monodromy_signRankOneLocalSystem`: the monodromy of the sign local system is the
  sign character.
* `IsCoveringMap.inv_signRankOneLocalSystem`: `o⁻¹ = o`.
* `IsCoveringMap.signRankOneLocalSystem_mul_self`: `o ⊗ o = 1`.
* `IsCoveringMap.freeLoopSignTwist_ρ_apply`: the action of a loop of free loops on the sign
  twist.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §§1.5 and 4.1.
* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry and
  topology*, IRMA Lect. Math. Theor. Phys. 24, EMS (2015), §§5–6 (the local system on the free
  loop space in the Viterbo isomorphism).
-/

public section

noncomputable section

open TauCeti

namespace IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
  (hp : IsCoveringMap p) (R : Type*) [CommRing R]

/-- **The sign local system of a covering, as a rank-one DG local system** at `x`, for a finite
fibre over `x`: its monodromy is the sign character of the covering, read in `R`. -/
def signRankOneLocalSystem {x : X} (hx : (p ⁻¹' {x}).Finite) : RankOneLocalSystem X x R :=
  RankOneLocalSystem.ofMonodromy
    ((Units.map (Int.castRingHom R).toMonoidHom).comp (hp.signCharacter hx))

theorem signRankOneLocalSystem_def {x : X} (hx : (p ⁻¹' {x}).Finite) :
    hp.signRankOneLocalSystem R hx =
      RankOneLocalSystem.ofMonodromy
        ((Units.map (Int.castRingHom R).toMonoidHom).comp (hp.signCharacter hx)) :=
  (rfl)

variable {R} {x : X}

/-- The monodromy of the sign local system is the sign character of the covering. -/
@[simp]
theorem monodromy_signRankOneLocalSystem (hx : (p ⁻¹' {x}).Finite) :
    (hp.signRankOneLocalSystem R hx).monodromy =
      (Units.map (Int.castRingHom R).toMonoidHom).comp (hp.signCharacter hx) :=
  RankOneLocalSystem.monodromy_ofMonodromy _

/-- A Moore loop acts on the sign local system by the sign character of its class. -/
@[simp]
theorem signRankOneLocalSystem_ρ_apply (hx : (p ⁻¹' {x}).Finite) (γ : MooreLoopSpace X x) :
    (hp.signRankOneLocalSystem R hx).ρ γ =
      Units.map (Int.castRingHom R).toMonoidHom
        (hp.signCharacter hx (MooreLoopSpace.fundamentalGroupHom x γ)) :=
  RankOneLocalSystem.ofMonodromy_unitsMap_comp_ρ_apply _ γ

/-- The sign local system is its own inverse: loops act by `±1`. -/
@[simp]
theorem inv_signRankOneLocalSystem (hx : (p ⁻¹' {x}).Finite) :
    (hp.signRankOneLocalSystem R hx)⁻¹ = hp.signRankOneLocalSystem R hx :=
  RankOneLocalSystem.inv_ofMonodromy_unitsMap_comp _

/-- The square of the sign local system is trivial. -/
@[simp]
theorem signRankOneLocalSystem_mul_self (hx : (p ⁻¹' {x}).Finite) :
    hp.signRankOneLocalSystem R hx * hp.signRankOneLocalSystem R hx = 1 := by
  nth_rw 1 [← hp.inv_signRankOneLocalSystem hx]
  exact inv_mul_cancel _

/-- A trivial sign character gives a trivial sign local system. -/
theorem signRankOneLocalSystem_eq_one (hx : (p ⁻¹' {x}).Finite) (h : hp.signCharacter hx = 1) :
    hp.signRankOneLocalSystem R hx = 1 :=
  (RankOneLocalSystem.ofMonodromy_unitsMap_comp_eq_one_iff _).2 (.inl h)

/-! ### The sign twist on the free loop space -/

section FreeLoop

variable (R) (hfin : ∀ x, (p ⁻¹' {x}).Finite)

/-- **The sign twist** at a free loop `γ₀`: the rank-one local system
`ev₀^*(o⁻¹) ⊗ ev₀^*(o^{-w(γ₀)})` on `(𝓛X, γ₀)`, where `o` is the sign local system of the cover,
`w` the sign exponent and `ev₀ : 𝓛X → X` the evaluation at the base point. It is the twist
`TauCeti.RankOneLocalSystem.freeLoopTwist` of the family of sign characters of the cover. For the
orientation cover of the tangent bundle of a manifold this is the orientation factor of the
degree-zero twist `η₀` of Barraud–Damian–Humilière–Oancea. -/
def freeLoopSignTwist (γ₀ : MooreFreeLoopSpace X) :
    RankOneLocalSystem (MooreFreeLoopSpace X) γ₀ R :=
  RankOneLocalSystem.freeLoopTwist R (fun x ↦ hp.signCharacter (hfin x)) γ₀

variable {R}

/-- The sign twist is the tensor product `ev₀^*(o⁻¹) ⊗ ev₀^*(o^{-w(γ₀)})` of the two
pullbacks along the evaluation at the base point. -/
theorem freeLoopSignTwist_def (γ₀ : MooreFreeLoopSpace X) :
    hp.freeLoopSignTwist R hfin γ₀ =
      RankOneLocalSystem.pullback (MooreFreeLoopSpace.basepointMap X)
          (MooreFreeLoopSpace.basepointMap_apply γ₀)
          (hp.signRankOneLocalSystem R (hfin γ₀.basepoint))⁻¹ *
        RankOneLocalSystem.pullback (MooreFreeLoopSpace.basepointMap X)
          (MooreFreeLoopSpace.basepointMap_apply γ₀)
          (hp.signRankOneLocalSystem R (hfin γ₀.basepoint) ^
            (-hp.freeLoopSignExponent hfin γ₀)) := by
  rw [freeLoopSignTwist, RankOneLocalSystem.freeLoopTwist_def, freeLoopSignExponent_def,
    signRankOneLocalSystem_def]

/-- On a component of free loops of sign `1`, the sign twist is `ev₀^*(o⁻¹)`. -/
theorem freeLoopSignTwist_eq_pullback_of_freeLoopSignCharacter_eq_one {γ₀ : MooreFreeLoopSpace X}
    (h : hp.freeLoopSignCharacter hfin (MooreFreeLoopSpace.toCircleMap γ₀) = 1) :
    hp.freeLoopSignTwist R hfin γ₀ =
      RankOneLocalSystem.pullback (MooreFreeLoopSpace.basepointMap X)
        (MooreFreeLoopSpace.basepointMap_apply γ₀)
        (hp.signRankOneLocalSystem R (hfin γ₀.basepoint))⁻¹ := by
  rw [freeLoopSignTwist, inv_signRankOneLocalSystem, signRankOneLocalSystem_def]
  exact RankOneLocalSystem.freeLoopTwist_eq_pullback_of_apply_eq_one
    ((hp.freeLoopSignCharacter_toCircleMap hfin γ₀).symm.trans h)

/-- On a component of free loops of sign `-1`, the sign twist is trivial: there it is
`ev₀^*(o⁻¹ ⊗ o)`. -/
theorem freeLoopSignTwist_eq_one_of_freeLoopSignCharacter_eq_neg_one {γ₀ : MooreFreeLoopSpace X}
    (h : hp.freeLoopSignCharacter hfin (MooreFreeLoopSpace.toCircleMap γ₀) = -1) :
    hp.freeLoopSignTwist R hfin γ₀ = 1 :=
  RankOneLocalSystem.freeLoopTwist_eq_one_of_apply_ne_one <| by
    rw [← freeLoopSignCharacter_toCircleMap, h]
    decide

/-- **The action on the sign twist**: a loop `Γ` of free loops at `γ₀` acts by the sign of
the loop `ev₀ ∘ Γ` of base points when `γ₀` has sign `1`, and trivially otherwise. -/
@[simp]
theorem freeLoopSignTwist_ρ_apply (γ₀ : MooreFreeLoopSpace X)
    (Γ : MooreLoopSpace (MooreFreeLoopSpace X) γ₀) :
    (hp.freeLoopSignTwist R hfin γ₀).ρ Γ =
      if hp.freeLoopSignCharacter hfin (MooreFreeLoopSpace.toCircleMap γ₀) = 1 then
        Units.map (Int.castRingHom R).toMonoidHom
          (hp.signCharacter (hfin γ₀.basepoint) (MooreLoopSpace.fundamentalGroupHom _
            (MooreLoopSpace.map (MooreFreeLoopSpace.basepointMap X)
              (MooreFreeLoopSpace.basepointMap_apply γ₀) Γ)))
      else 1 := by
  rw [freeLoopSignTwist, RankOneLocalSystem.freeLoopTwist_ρ_apply,
    freeLoopSignCharacter_toCircleMap]

/-- A trivial sign character at the base point trivializes the sign twist. -/
theorem freeLoopSignTwist_eq_one {γ₀ : MooreFreeLoopSpace X}
    (h : hp.signCharacter (hfin γ₀.basepoint) = 1) :
    hp.freeLoopSignTwist R hfin γ₀ = 1 :=
  RankOneLocalSystem.freeLoopTwist_eq_one h

end FreeLoop

end IsCoveringMap
