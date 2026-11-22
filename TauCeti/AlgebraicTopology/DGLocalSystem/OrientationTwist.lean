/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.RankOne
public import TauCeti.Topology.Homotopy.Monodromy.SignCharacter
public import TauCeti.Topology.PathSpace.Moore.Comparison.FreeLoop
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Character

/-!
# The orientation twist on the free loop space

Let `p : E → X` be a covering map with finite fibres, for instance the orientation double cover of
a real vector bundle `V → X`. Its **sign local system** `o` at `x` is the rank-one DG local system
whose monodromy is the sign character `π₁(X, x) →* ℤˣ` of the cover, read in the coefficient ring
(`IsCoveringMap.signRankOneLocalSystem`): a Moore loop acts by the sign of the permutation of the
fibre given by path lifting along it. It is its own inverse
(`IsCoveringMap.inv_signRankOneLocalSystem`).

On the free loop space `𝓛X`, put `w(γ) = 0` when the free loop `γ` has sign `1`, and `w(γ) = -1`
otherwise (`IsCoveringMap.orientationExponent`), where the sign of a free loop is the sign
character of the circle map it traces (`IsCoveringMap.freeLoopSignCharacter`). For the
orientation cover of `V`, `w(γ) = 0` exactly when `V` pulled back to the circle along `γ` is
orientable. The exponent is constant on the path components of `𝓛X`
(`IsCoveringMap.orientationExponent_eq_of_joined`). The **orientation twist** at a free loop `γ₀`
is the rank-one local system

`ev₀^*(o⁻¹) ⊗ ev₀^*(o^{-w(γ₀)})`

on `(𝓛X, γ₀)`, pulled back along the evaluation `ev₀ : 𝓛X → X` at the base point
(`IsCoveringMap.orientationTwist`). On the components where `w = 0` it is `ev₀^*(o⁻¹)`, and on the
components where `w = -1` it is trivial, because `o⁻¹ ⊗ o` is
(`IsCoveringMap.orientationTwist_of_freeLoopSignCharacter_eq_one`,
`IsCoveringMap.orientationTwist_of_freeLoopSignCharacter_eq_neg_one`). A loop of free loops `Γ`
acts by the sign of the loop `ev₀ ∘ Γ` traced by the base points on the first kind of component,
and trivially on the second (`IsCoveringMap.orientationTwist_ρ_apply`). If the sign character is
trivial, in particular for an orientable bundle, the twist is trivial.

For the tangent bundle `V = TQ` of a manifold `Q`
(`TauCeti.VectorBundleOrientationCover.freeLoopOrientationTwist`) this is the factor
`ev₀^*(o_Q^{-1}) ⊗ ev₀^*(o_Q^{-w})` of the degree-zero twist `η₀` of
Barraud–Damian–Humilière–Oancea on the free loop space of `Q`, which enters their Viterbo
isomorphism with DG coefficients for the cotangent bundle `T^*Q`; `η₀` is its tensor product with
the rank-one local system on `𝓛Q` transgressing the second Stiefel–Whitney class of `TQ`.

## Main definitions

* `IsCoveringMap.signRankOneLocalSystem`: the sign local system of a covering with finite fibres,
  as a rank-one DG local system.
* `IsCoveringMap.orientationExponent`: the exponent `w`, `0` or `-1`, of a free loop.
* `IsCoveringMap.orientationTwist`: the rank-one local system `ev₀^*(o⁻¹) ⊗ ev₀^*(o^{-w})` on the
  free loop space.
* `TauCeti.VectorBundleOrientationCover.freeLoopOrientationTwist`: the orientation twist of a real
  vector bundle.

## Main results

* `IsCoveringMap.monodromy_signRankOneLocalSystem`: the monodromy of the sign local system is the
  sign character.
* `IsCoveringMap.orientationExponent_eq_of_joined`: `w` is constant on path components.
* `IsCoveringMap.orientationTwist_ρ_apply`: the action of a loop of free loops on the twist.
* `TauCeti.VectorBundleOrientation.freeLoopOrientationTwist_eq_one`: an oriented bundle has
  trivial orientation twist.

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

/-! ### The sign local system -/

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
        (hp.signCharacter hx (MooreLoopSpace.fundamentalGroupHom x γ)) := by
  rw [signRankOneLocalSystem, RankOneLocalSystem.ofMonodromy_ρ_apply, MonoidHom.comp_apply,
    ← map_inv, Int.units_inv_eq_self]

/-- The sign local system is its own inverse: loops act by `±1`. -/
@[simp]
theorem inv_signRankOneLocalSystem (hx : (p ⁻¹' {x}).Finite) :
    (hp.signRankOneLocalSystem R hx)⁻¹ = hp.signRankOneLocalSystem R hx :=
  RankOneLocalSystem.inv_ofMonodromy_unitsMap_comp _

/-- A trivial sign character gives a trivial sign local system. -/
theorem signRankOneLocalSystem_eq_one (hx : (p ⁻¹' {x}).Finite) (h : hp.signCharacter hx = 1) :
    hp.signRankOneLocalSystem R hx = 1 :=
  (RankOneLocalSystem.ofMonodromy_unitsMap_comp_eq_one_iff _).2 (.inl h)

/-! ### The free loop space -/

variable (hfin : ∀ x, (p ⁻¹' {x}).Finite)

/-- **The orientation exponent** `w` of a free loop: `0` when the loop has sign `1`, so that for
the orientation cover of a vector bundle the bundle pulled back along the loop is orientable, and
`-1` otherwise. -/
def orientationExponent (γ : MooreFreeLoopSpace X) : ℤ :=
  if hp.freeLoopSignCharacter hfin (MooreFreeLoopSpace.toCircleMap γ) = 1 then 0 else -1

theorem orientationExponent_eq_zero_iff (γ : MooreFreeLoopSpace X) :
    hp.orientationExponent hfin γ = 0 ↔
      hp.freeLoopSignCharacter hfin (MooreFreeLoopSpace.toCircleMap γ) = 1 := by
  rw [orientationExponent]
  split_ifs with h <;> simp [h]

theorem orientationExponent_eq_neg_one_iff (γ : MooreFreeLoopSpace X) :
    hp.orientationExponent hfin γ = -1 ↔
      hp.freeLoopSignCharacter hfin (MooreFreeLoopSpace.toCircleMap γ) = -1 := by
  rw [orientationExponent]
  rcases Int.units_eq_one_or (hp.freeLoopSignCharacter hfin (MooreFreeLoopSpace.toCircleMap γ))
    with h | h <;> simp [h]

/-- The orientation exponent is constant on the path components of the free loop space. -/
theorem orientationExponent_eq_of_joined {γ δ : MooreFreeLoopSpace X} (h : Joined γ δ) :
    hp.orientationExponent hfin γ = hp.orientationExponent hfin δ := by
  rw [orientationExponent, orientationExponent, hp.freeLoopSignCharacter_eq_of_joined hfin
    (h.map MooreFreeLoopSpace.toCircleMap.continuous)]

variable (R) in
/-- **The orientation twist** at a free loop `γ₀`: the rank-one local system
`ev₀^*(o⁻¹) ⊗ ev₀^*(o^{-w(γ₀)})` on `(𝓛X, γ₀)`, where `o` is the sign local system of the cover,
`w` the orientation exponent and `ev₀ : 𝓛X → X` the evaluation at the base point. For the
orientation cover of the tangent bundle of a manifold this is the orientation factor of the
degree-zero twist `η₀` of Barraud–Damian–Humilière–Oancea. -/
def orientationTwist (γ₀ : MooreFreeLoopSpace X) :
    RankOneLocalSystem (MooreFreeLoopSpace X) γ₀ R :=
  RankOneLocalSystem.pullback (MooreFreeLoopSpace.basepointMap X)
    (MooreFreeLoopSpace.basepointMap_apply γ₀)
    ((hp.signRankOneLocalSystem R (hfin γ₀.basepoint))⁻¹ *
      hp.signRankOneLocalSystem R (hfin γ₀.basepoint) ^ (-hp.orientationExponent hfin γ₀))

/-- On a component of free loops of sign `1`, the orientation twist is `ev₀^*(o⁻¹)`. -/
theorem orientationTwist_of_freeLoopSignCharacter_eq_one {γ₀ : MooreFreeLoopSpace X}
    (h : hp.freeLoopSignCharacter hfin (MooreFreeLoopSpace.toCircleMap γ₀) = 1) :
    hp.orientationTwist R hfin γ₀ =
      RankOneLocalSystem.pullback (MooreFreeLoopSpace.basepointMap X)
        (MooreFreeLoopSpace.basepointMap_apply γ₀)
        (hp.signRankOneLocalSystem R (hfin γ₀.basepoint))⁻¹ := by
  rw [orientationTwist, (hp.orientationExponent_eq_zero_iff hfin γ₀).2 h, neg_zero, zpow_zero,
    mul_one]

/-- On a component of free loops of sign `-1`, the orientation twist is trivial: there it is
`ev₀^*(o⁻¹ ⊗ o)`. -/
theorem orientationTwist_of_freeLoopSignCharacter_eq_neg_one {γ₀ : MooreFreeLoopSpace X}
    (h : hp.freeLoopSignCharacter hfin (MooreFreeLoopSpace.toCircleMap γ₀) = -1) :
    hp.orientationTwist R hfin γ₀ = 1 := by
  rw [orientationTwist, (hp.orientationExponent_eq_neg_one_iff hfin γ₀).2 h, neg_neg, zpow_one,
    inv_mul_cancel, map_one]

/-- **The action on the orientation twist**: a loop `Γ` of free loops at `γ₀` acts by the sign of
the loop `ev₀ ∘ Γ` of base points when `γ₀` has sign `1`, and trivially otherwise. -/
theorem orientationTwist_ρ_apply (γ₀ : MooreFreeLoopSpace X)
    (Γ : MooreLoopSpace (MooreFreeLoopSpace X) γ₀) :
    (hp.orientationTwist R hfin γ₀).ρ Γ =
      if hp.freeLoopSignCharacter hfin (MooreFreeLoopSpace.toCircleMap γ₀) = 1 then
        Units.map (Int.castRingHom R).toMonoidHom
          (hp.signCharacter (hfin γ₀.basepoint) (MooreLoopSpace.fundamentalGroupHom _
            (MooreLoopSpace.map (MooreFreeLoopSpace.basepointMap X)
              (MooreFreeLoopSpace.basepointMap_apply γ₀) Γ)))
      else 1 := by
  split_ifs with h
  · rw [hp.orientationTwist_of_freeLoopSignCharacter_eq_one hfin h, inv_signRankOneLocalSystem,
      RankOneLocalSystem.pullback_ρ_apply, signRankOneLocalSystem_ρ_apply]
  · rw [hp.orientationTwist_of_freeLoopSignCharacter_eq_neg_one hfin
      ((Int.units_eq_one_or _).resolve_left h), RankOneLocalSystem.one_ρ, MonoidHom.one_apply]

/-- A trivial sign character at the base point trivializes the orientation twist. -/
theorem orientationTwist_eq_one {γ₀ : MooreFreeLoopSpace X}
    (h : hp.signCharacter (hfin γ₀.basepoint) = 1) :
    hp.orientationTwist R hfin γ₀ = 1 := by
  rw [orientationTwist, hp.signRankOneLocalSystem_eq_one _ h, inv_one, one_zpow, mul_one, map_one]

end IsCoveringMap

/-! ### Real vector bundles -/

namespace TauCeti.VectorBundleOrientationCover

open Module

variable {B : Type*} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type*) [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  [FiniteDimensional ℝ F] {ι : Type*} [Fintype ι] (R : Type*) [CommRing R]

/-- **The orientation twist of a real vector bundle** `E → B` of rank `card ι` on the free loop
space of `B`, at the free loop `γ₀`: the orientation twist of its orientation double cover. A free
loop has exponent `0` when `E` pulled back along it is orientable, that is, when transport along
it preserves the orientations of the fibre, and `-1` otherwise. For the tangent bundle of a
manifold `Q` this is the factor `ev₀^*(o_Q^{-1}) ⊗ ev₀^*(o_Q^{-w})` of the degree-zero twist `η₀`
of Barraud–Damian–Humilière–Oancea. -/
def freeLoopOrientationTwist (hι : Fintype.card ι = finrank ℝ F) (γ₀ : MooreFreeLoopSpace B) :
    RankOneLocalSystem (MooreFreeLoopSpace B) γ₀ R :=
  (isCoveringMap_proj (F := F) (E := E) hι).orientationTwist R (finite_fiber hι) γ₀

end TauCeti.VectorBundleOrientationCover

namespace TauCeti.VectorBundleOrientation

open Module VectorBundleOrientationCover

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  [FiniteDimensional ℝ F] {ι : Type*} [Fintype ι] {R : Type*} [CommRing R]

/-- **An oriented bundle has trivial orientation twist.** -/
theorem freeLoopOrientationTwist_eq_one (hι : Fintype.card ι = finrank ℝ F)
    (o : VectorBundleOrientation F E ι) (γ₀ : MooreFreeLoopSpace B) :
    freeLoopOrientationTwist F E R hι γ₀ = 1 :=
  (isCoveringMap_proj hι).orientationTwist_eq_one (finite_fiber hι) <| by
    rw [← orientationCharacter_eq_signCharacter hι]
    exact MonoidHom.ext (o.orientationCharacter_eq_one hι)

end TauCeti.VectorBundleOrientation
