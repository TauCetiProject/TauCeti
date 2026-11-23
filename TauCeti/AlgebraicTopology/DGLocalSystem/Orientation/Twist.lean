/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Sign
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Character

/-!
# The orientation twist on the free loop space

Let `p : E → X` be a covering map with finite fibres, for instance the orientation double cover of
a real vector bundle `V → X`, and let `o` be its sign local system
(`IsCoveringMap.signRankOneLocalSystem`), the rank-one DG local system on which a Moore loop acts by
the sign of the permutation of the fibre given by path lifting along it.

On the free loop space `𝓛X`, put `w(γ) = 0` when the free loop `γ` has sign `1`, and `w(γ) = -1`
otherwise (`IsCoveringMap.orientationExponent`), where the sign of a free loop is the sign
character of the circle map it traces (`IsCoveringMap.freeLoopSignCharacter`). For the
orientation cover of `V`, `w(γ) = 0` exactly when `V` pulled back to the circle along `γ` is
orientable
(`TauCeti.VectorBundleOrientationCover.orientationExponent_eq_zero_iff_exists_section`,
`TauCeti.VectorBundleOrientationCover.orientationExponent_eq_neg_one_iff_not_exists_section`).
The exponent is constant on the path components of `𝓛X`
(`IsCoveringMap.orientationExponent_eq_of_joined`). The **orientation twist** at a free loop `γ₀`
is the rank-one local system

`ev₀^*(o⁻¹) ⊗ ev₀^*(o^{-w(γ₀)})`

on `(𝓛X, γ₀)`, pulled back along the evaluation `ev₀ : 𝓛X → X` at the base point
(`IsCoveringMap.orientationTwist`, `IsCoveringMap.orientationTwist_def`). On the components where
`w = 0` it is `ev₀^*(o⁻¹)`, and on the components where `w = -1` it is trivial, because `o⁻¹ ⊗ o`
is (`IsCoveringMap.orientationTwist_eq_pullback_of_freeLoopSignCharacter_eq_one`,
`IsCoveringMap.orientationTwist_eq_one_of_freeLoopSignCharacter_eq_neg_one`). A loop of free
loops `Γ` acts by the sign of the loop `ev₀ ∘ Γ` traced by the base points on the first kind of
component, and trivially on the second (`IsCoveringMap.orientationTwist_ρ_apply`). If the sign
character is trivial, in particular for an orientable bundle, the twist is trivial.

For the tangent bundle `V = TQ` of a manifold `Q`
(`TauCeti.VectorBundleOrientationCover.freeLoopOrientationTwist`) this is the factor
`ev₀^*(o_Q^{-1}) ⊗ ev₀^*(o_Q^{-w})` of the degree-zero twist `η₀` of
Barraud–Damian–Humilière–Oancea on the free loop space of `Q`, which enters their Viterbo
isomorphism with DG coefficients for the cotangent bundle `T^*Q`; `η₀` is its tensor product with
the rank-one local system on `𝓛Q` transgressing the second Stiefel–Whitney class of `TQ`.

## Main definitions

* `IsCoveringMap.orientationTwist`: the rank-one local system `ev₀^*(o⁻¹) ⊗ ev₀^*(o^{-w})` on the
  free loop space.
* `TauCeti.VectorBundleOrientationCover.freeLoopOrientationTwist`: the orientation twist of a real
  vector bundle.

## Main results

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
  (hp : IsCoveringMap p) (R : Type*) [CommRing R] (hfin : ∀ x, (p ⁻¹' {x}).Finite)

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

variable {R}

/-- The orientation twist is the tensor product `ev₀^*(o⁻¹) ⊗ ev₀^*(o^{-w(γ₀)})` of the two
pullbacks along the evaluation at the base point. -/
theorem orientationTwist_def (γ₀ : MooreFreeLoopSpace X) :
    hp.orientationTwist R hfin γ₀ =
      RankOneLocalSystem.pullback (MooreFreeLoopSpace.basepointMap X)
          (MooreFreeLoopSpace.basepointMap_apply γ₀)
          (hp.signRankOneLocalSystem R (hfin γ₀.basepoint))⁻¹ *
        RankOneLocalSystem.pullback (MooreFreeLoopSpace.basepointMap X)
          (MooreFreeLoopSpace.basepointMap_apply γ₀)
          (hp.signRankOneLocalSystem R (hfin γ₀.basepoint) ^ (-hp.orientationExponent hfin γ₀)) :=
  map_mul _ _ _

/-- On a component of free loops of sign `1`, the orientation twist is `ev₀^*(o⁻¹)`. -/
theorem orientationTwist_eq_pullback_of_freeLoopSignCharacter_eq_one {γ₀ : MooreFreeLoopSpace X}
    (h : hp.freeLoopSignCharacter hfin (MooreFreeLoopSpace.toCircleMap γ₀) = 1) :
    hp.orientationTwist R hfin γ₀ =
      RankOneLocalSystem.pullback (MooreFreeLoopSpace.basepointMap X)
        (MooreFreeLoopSpace.basepointMap_apply γ₀)
        (hp.signRankOneLocalSystem R (hfin γ₀.basepoint))⁻¹ := by
  simp [orientationTwist, (hp.orientationExponent_eq_zero_iff hfin γ₀).2 h]

/-- On a component of free loops of sign `-1`, the orientation twist is trivial: there it is
`ev₀^*(o⁻¹ ⊗ o)`. -/
theorem orientationTwist_eq_one_of_freeLoopSignCharacter_eq_neg_one {γ₀ : MooreFreeLoopSpace X}
    (h : hp.freeLoopSignCharacter hfin (MooreFreeLoopSpace.toCircleMap γ₀) = -1) :
    hp.orientationTwist R hfin γ₀ = 1 := by
  simp [orientationTwist, (hp.orientationExponent_eq_neg_one_iff hfin γ₀).2 h,
    -inv_signRankOneLocalSystem]

/-- **The action on the orientation twist**: a loop `Γ` of free loops at `γ₀` acts by the sign of
the loop `ev₀ ∘ Γ` of base points when `γ₀` has sign `1`, and trivially otherwise. -/
@[simp]
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
  · simp [hp.orientationTwist_eq_pullback_of_freeLoopSignCharacter_eq_one hfin h]
  · simp [hp.orientationTwist_eq_one_of_freeLoopSignCharacter_eq_neg_one hfin
      ((Int.units_eq_one_or _).resolve_left h)]

/-- A trivial sign character at the base point trivializes the orientation twist. -/
theorem orientationTwist_eq_one {γ₀ : MooreFreeLoopSpace X}
    (h : hp.signCharacter (hfin γ₀.basepoint) = 1) :
    hp.orientationTwist R hfin γ₀ = 1 := by
  simp [orientationTwist, hp.signRankOneLocalSystem_eq_one _ h]

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

variable {F E R}

/-- The orientation twist of a real vector bundle is the orientation twist of its orientation
double cover. -/
theorem freeLoopOrientationTwist_def (hι : Fintype.card ι = finrank ℝ F)
    (γ₀ : MooreFreeLoopSpace B) :
    freeLoopOrientationTwist F E R hι γ₀ =
      (isCoveringMap_proj (F := F) (E := E) hι).orientationTwist R (finite_fiber hι) γ₀ :=
  (rfl)

/-- **Orientability along a free loop.** In the orientation double cover, a free loop `γ` has
exponent `0` exactly when the orientations of the fibres along the circle traced by `γ` can be
chosen continuously, that is when `E` pulled back along it is orientable. -/
theorem orientationExponent_eq_zero_iff_exists_section (hι : Fintype.card ι = finrank ℝ F)
    (γ : MooreFreeLoopSpace B) :
    (isCoveringMap_proj (F := F) (E := E) hι).orientationExponent (finite_fiber hι) γ = 0 ↔
      ∃ s : C(Circle, VectorBundleOrientationCover F E ι),
        ∀ z, (s z).proj = MooreFreeLoopSpace.toCircleMap γ z :=
  (IsCoveringMap.orientationExponent_eq_zero_iff _ _ γ).trans <|
    IsCoveringMap.freeLoopSignCharacter_eq_one_iff _ _ (fun _ _ h ↦ eq_or_eq_deck hι h) _
      (surjective_proj hι _)

/-- **Non-orientability along a free loop.** In the orientation double cover, a free loop `γ` has
exponent `-1` exactly when the orientations of the fibres along the circle traced by `γ` cannot be
chosen continuously, that is when `E` pulled back along it is not orientable. -/
theorem orientationExponent_eq_neg_one_iff_not_exists_section
    (hι : Fintype.card ι = finrank ℝ F) (γ : MooreFreeLoopSpace B) :
    (isCoveringMap_proj (F := F) (E := E) hι).orientationExponent (finite_fiber hι) γ = -1 ↔
      ¬∃ s : C(Circle, VectorBundleOrientationCover F E ι),
        ∀ z, (s z).proj = MooreFreeLoopSpace.toCircleMap γ z :=
  (IsCoveringMap.orientationExponent_eq_neg_one_iff _ _ γ).trans <|
    Int.units_ne_iff_eq_neg.symm.trans <| not_congr <|
      IsCoveringMap.freeLoopSignCharacter_eq_one_iff _ _ (fun _ _ h ↦ eq_or_eq_deck hι h) _
        (surjective_proj hι _)

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
