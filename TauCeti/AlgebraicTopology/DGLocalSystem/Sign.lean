/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.RankOne
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

## Main definitions

* `IsCoveringMap.signRankOneLocalSystem`: the sign local system of a covering with finite fibres,
  as a rank-one DG local system.

## Main results

* `IsCoveringMap.monodromy_signRankOneLocalSystem`: the monodromy of the sign local system is the
  sign character.
* `IsCoveringMap.inv_signRankOneLocalSystem`: `o⁻¹ = o`.
* `IsCoveringMap.signRankOneLocalSystem_mul_self`: `o ⊗ o = 1`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.1.
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

end IsCoveringMap
