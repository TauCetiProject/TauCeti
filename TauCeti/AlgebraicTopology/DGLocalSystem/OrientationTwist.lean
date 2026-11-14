/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.RankOne
public import TauCeti.AlgebraicTopology.LocalCoefficient.Sign.Character
public import TauCeti.Topology.VectorBundle.Orientation.Cover

/-!
# The orientation twist on the free loop space

Let `p : E → X` be a double cover whose fibres are the pairs `{e, σ e}`, for instance the
orientation double cover of a real vector bundle `V → X`, and let `o` be its sign local system:
the rank-one local system on which a loop acts by its sign
(`IsCoveringMap.signRankOneLocalSystem`, a rank-one DG local system in the sense of
`TauCeti.RankOneLocalSystem`). Its monodromy is the sign character of the cover
(`IsCoveringMap.monodromy_signRankOneLocalSystem`), which is also the monodromy of the classical
sign local system (`IsCoveringMap.signLocalSystem_map_toArrow`).

On the free loop space `𝓛X`, put `w(γ) = 0` when the free loop `γ` has sign `1`, and `w(γ) = -1`
otherwise (`IsCoveringMap.orientationExponent`). For the orientation cover of `V`, `w(γ) = 0`
exactly when `V` pulled back to the circle along `γ` is orientable. The exponent is constant on
the path components of `𝓛X` (`IsCoveringMap.orientationExponent_eq_of_joined`). The
**orientation twist** at a free loop `γ₀` is the rank-one local system

`ev₀^*(o⁻¹) ⊗ ev₀^*(o^{-w(γ₀)})`

on `(𝓛X, γ₀)`, pulled back along the evaluation `ev₀ : 𝓛X → X` at the base point
(`IsCoveringMap.orientationTwist`). On the components where `w = 0` it is `ev₀^*(o⁻¹)`, and on the
components where `w = -1` it is trivial, because `o⁻¹ ⊗ o` is
(`IsCoveringMap.orientationTwist_of_freeLoopSign_eq_one`,
`IsCoveringMap.orientationTwist_of_freeLoopSign_eq_neg_one`). A loop of free loops `Γ` acts by the
sign of the loop `ev₀ ∘ Γ` traced by the base points on the first kind of component, and trivially
on the second (`IsCoveringMap.orientationTwist_ρ_apply`). If the cover has a continuous section,
in particular for an orientable bundle, the twist is trivial.

For the tangent bundle `V = TQ` of a manifold `Q`
(`TauCeti.VectorBundleOrientationCover.freeLoopOrientationTwist`) this is the factor
`ev₀^*(o_Q^{-1}) ⊗ ev₀^*(o_Q^{-w})` of the degree-zero twist `η₀` of
Barraud–Damian–Humilière–Oancea on the free loop space of `Q`, which enters their Viterbo
isomorphism with DG coefficients for the cotangent bundle `T^*Q`; `η₀` is its tensor product with
the rank-one local system on `𝓛Q` transgressing the second Stiefel–Whitney class of `TQ`.

## Main definitions

* `IsCoveringMap.signRankOneLocalSystem`: the sign local system of a double cover, as a rank-one
  DG local system.
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
* `IsCoveringMap.orientationTwist_eq_one_of_section`: a section of the cover trivializes the
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

section Twist

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
  (hp : IsCoveringMap p) {σ : C(E, E)} (hσ : p ∘ σ = p) (hfix : ∀ e, σ e ≠ e)
  (hfib : ∀ e e', p e' = p e → e' = e ∨ e' = σ e) (R : Type*) [CommRing R]

/-- **The sign local system of a double cover, as a rank-one DG local system** at `x`: a Moore
loop acts by its sign, read in the coefficient ring `R`. -/
def signRankOneLocalSystem {x : X} (e : p ⁻¹' {x}) : RankOneLocalSystem X x R where
  ρ := (Units.map (Int.castRingHom R : ℤ →* R)).comp (hp.loopSign hσ hfix hfib e)
  eq_of_joined _ _ h := by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hp.loopSign_eq_of_joined hσ hfix hfib e h]

variable {R} {x : X}

theorem signRankOneLocalSystem_ρ (e : p ⁻¹' {x}) :
    (hp.signRankOneLocalSystem hσ hfix hfib R e).ρ =
      (Units.map (Int.castRingHom R : ℤ →* R)).comp (hp.loopSign hσ hfix hfib e) :=
  (rfl)

@[simp]
theorem signRankOneLocalSystem_ρ_apply (e : p ⁻¹' {x}) (γ : MooreLoopSpace X x) :
    ((hp.signRankOneLocalSystem hσ hfix hfib R e).ρ γ : R) =
      ((hp.loopSign hσ hfix hfib e γ : ℤ) : R) := by
  simp [signRankOneLocalSystem_ρ]

/-- The sign local system does not depend on the point of the fibre. -/
theorem signRankOneLocalSystem_eq (e e' : p ⁻¹' {x}) :
    hp.signRankOneLocalSystem hσ hfix hfib R e = hp.signRankOneLocalSystem hσ hfix hfib R e' :=
  RankOneLocalSystem.ext <| by
    rw [signRankOneLocalSystem_ρ, signRankOneLocalSystem_ρ, hp.loopSign_eq hσ hfix hfib e e']

/-- The sign local system is its own inverse: loops act by `±1`. -/
@[simp]
theorem inv_signRankOneLocalSystem (e : p ⁻¹' {x}) :
    (hp.signRankOneLocalSystem hσ hfix hfib R e)⁻¹ = hp.signRankOneLocalSystem hσ hfix hfib R e :=
  RankOneLocalSystem.ext <| MonoidHom.ext fun γ ↦ by
    rw [RankOneLocalSystem.inv_ρ, MonoidHom.inv_apply, signRankOneLocalSystem_ρ,
      MonoidHom.comp_apply, ← map_inv, Int.units_inv_eq_self]

/-- **The monodromy of the sign local system** is the sign character of the cover: it agrees with
the transport of the classical sign local system (`IsCoveringMap.signLocalSystem_map_toArrow`). -/
theorem monodromy_signRankOneLocalSystem (e : p ⁻¹' {x}) (g : FundamentalGroup X x) :
    (hp.signRankOneLocalSystem hσ hfix hfib R e).monodromy g =
      Units.map (Int.castRingHom R : ℤ →* R) (hp.signCharacter hσ hfix hfib e g) := by
  obtain ⟨γ, hγ⟩ := MooreLoopSpace.fundamentalGroupHom_surjective x g⁻¹
  rw [← inv_inv g, ← hγ, RankOneLocalSystem.monodromy_fundamentalGroupHom_inv, map_inv,
    Int.units_inv_eq_self, signRankOneLocalSystem_ρ, MonoidHom.comp_apply, loopSign_apply]

/-- A continuous section of the cover trivializes its sign local system. -/
theorem signRankOneLocalSystem_eq_one_of_section {s : X → E} (hs : Continuous s)
    (hps : ∀ x, s x ∈ p ⁻¹' {x}) (e : p ⁻¹' {x}) :
    hp.signRankOneLocalSystem hσ hfix hfib R e = 1 :=
  RankOneLocalSystem.ext <| MonoidHom.ext fun γ ↦ Units.ext <| by
    rw [signRankOneLocalSystem_ρ_apply, loopSign_apply,
      hp.signCharacter_eq_one_of_section hσ hfix hfib hs hps e]
    simp

/-! ### The free loop space -/

variable (hsurj : Function.Surjective p)

/-- **The orientation exponent** `w` of a free loop: `0` when the loop has sign `1`, so that for
the orientation cover of a vector bundle the bundle pulled back along the loop is orientable, and
`-1` otherwise. -/
def orientationExponent (γ : MooreFreeLoopSpace X) : ℤ :=
  if hp.freeLoopSign hσ hfix hfib hsurj γ = 1 then 0 else -1

theorem orientationExponent_eq_zero_iff (γ : MooreFreeLoopSpace X) :
    hp.orientationExponent hσ hfix hfib hsurj γ = 0 ↔
      hp.freeLoopSign hσ hfix hfib hsurj γ = 1 := by
  rw [orientationExponent]
  split_ifs with h <;> simp [h]

theorem orientationExponent_eq_neg_one_iff (γ : MooreFreeLoopSpace X) :
    hp.orientationExponent hσ hfix hfib hsurj γ = -1 ↔
      hp.freeLoopSign hσ hfix hfib hsurj γ = -1 := by
  rw [orientationExponent]
  rcases Int.units_eq_one_or (hp.freeLoopSign hσ hfix hfib hsurj γ) with h | h <;> simp [h]

/-- The orientation exponent is constant on the path components of the free loop space. -/
theorem orientationExponent_eq_of_joined {γ δ : MooreFreeLoopSpace X} (h : Joined γ δ) :
    hp.orientationExponent hσ hfix hfib hsurj γ = hp.orientationExponent hσ hfix hfib hsurj δ := by
  rw [orientationExponent, orientationExponent, hp.freeLoopSign_eq_of_joined hσ hfix hfib hsurj h]

variable (R) in
/-- **The orientation twist** at a free loop `γ₀`: the rank-one local system
`ev₀^*(o⁻¹) ⊗ ev₀^*(o^{-w(γ₀)})` on `(𝓛X, γ₀)`, where `o` is the sign local system of the cover,
`w` the orientation exponent and `ev₀ : 𝓛X → X` the evaluation at the base point. For the
orientation cover of the tangent bundle of a manifold this is the orientation factor of the
degree-zero twist `η₀` of Barraud–Damian–Humilière–Oancea. -/
def orientationTwist (γ₀ : MooreFreeLoopSpace X) :
    RankOneLocalSystem (MooreFreeLoopSpace X) γ₀ R :=
  let o := hp.signRankOneLocalSystem hσ hfix hfib R
    ⟨Function.surjInv hsurj γ₀.basepoint, Function.surjInv_eq hsurj _⟩
  RankOneLocalSystem.comap (MooreFreeLoopSpace.basepointMap X)
    (MooreFreeLoopSpace.basepointMap_apply γ₀)
    (o⁻¹ * o ^ (-hp.orientationExponent hσ hfix hfib hsurj γ₀))

/-- The orientation twist, computed from any point `e` of the fibre over the base point. -/
theorem orientationTwist_eq (γ₀ : MooreFreeLoopSpace X) (e : p ⁻¹' {γ₀.basepoint}) :
    hp.orientationTwist hσ hfix hfib R hsurj γ₀ =
      RankOneLocalSystem.comap (MooreFreeLoopSpace.basepointMap X)
        (MooreFreeLoopSpace.basepointMap_apply γ₀)
        ((hp.signRankOneLocalSystem hσ hfix hfib R e)⁻¹ *
          hp.signRankOneLocalSystem hσ hfix hfib R e ^
            (-hp.orientationExponent hσ hfix hfib hsurj γ₀)) := by
  rw [orientationTwist, hp.signRankOneLocalSystem_eq hσ hfix hfib _ e]

/-- On a component of free loops of sign `1`, the orientation twist is `ev₀^*(o⁻¹)`. -/
theorem orientationTwist_of_freeLoopSign_eq_one {γ₀ : MooreFreeLoopSpace X}
    (h : hp.freeLoopSign hσ hfix hfib hsurj γ₀ = 1) (e : p ⁻¹' {γ₀.basepoint}) :
    hp.orientationTwist hσ hfix hfib R hsurj γ₀ =
      RankOneLocalSystem.comap (MooreFreeLoopSpace.basepointMap X)
        (MooreFreeLoopSpace.basepointMap_apply γ₀)
        (hp.signRankOneLocalSystem hσ hfix hfib R e)⁻¹ := by
  rw [orientationTwist_eq hp hσ hfix hfib hsurj γ₀ e,
    (hp.orientationExponent_eq_zero_iff hσ hfix hfib hsurj γ₀).2 h, neg_zero, zpow_zero, mul_one]

/-- On a component of free loops of sign `-1`, the orientation twist is trivial: there it is
`ev₀^*(o⁻¹ ⊗ o)`. -/
theorem orientationTwist_of_freeLoopSign_eq_neg_one {γ₀ : MooreFreeLoopSpace X}
    (h : hp.freeLoopSign hσ hfix hfib hsurj γ₀ = -1) :
    hp.orientationTwist hσ hfix hfib R hsurj γ₀ = 1 := by
  rw [orientationTwist, (hp.orientationExponent_eq_neg_one_iff hσ hfix hfib hsurj γ₀).2 h,
    neg_neg, zpow_one, inv_mul_cancel, map_one]

/-- **The action on the orientation twist**: a loop `Γ` of free loops at `γ₀` acts by the sign of
the loop `ev₀ ∘ Γ` of base points when `γ₀` has sign `1`, and trivially otherwise. -/
theorem orientationTwist_ρ_apply (γ₀ : MooreFreeLoopSpace X) (e : p ⁻¹' {γ₀.basepoint})
    (Γ : MooreLoopSpace (MooreFreeLoopSpace X) γ₀) :
    ((hp.orientationTwist hσ hfix hfib R hsurj γ₀).ρ Γ : R) =
      if hp.freeLoopSign hσ hfix hfib hsurj γ₀ = 1 then
        ((hp.loopSign hσ hfix hfib e (MooreLoopSpace.map (MooreFreeLoopSpace.basepointMap X)
          (MooreFreeLoopSpace.basepointMap_apply γ₀) Γ) : ℤ) : R)
      else 1 := by
  split_ifs with h
  · rw [hp.orientationTwist_of_freeLoopSign_eq_one hσ hfix hfib hsurj h e,
      inv_signRankOneLocalSystem, RankOneLocalSystem.comap_ρ_apply, signRankOneLocalSystem_ρ_apply]
  · rw [hp.orientationTwist_of_freeLoopSign_eq_neg_one hσ hfix hfib hsurj
      ((Int.units_eq_one_or _).resolve_left h)]
    simp

/-- A continuous section of the cover trivializes the orientation twist: for the orientation cover,
an oriented bundle has trivial orientation twist. -/
theorem orientationTwist_eq_one_of_section {s : X → E} (hs : Continuous s)
    (hps : ∀ x, s x ∈ p ⁻¹' {x}) (γ₀ : MooreFreeLoopSpace X) :
    hp.orientationTwist hσ hfix hfib R hsurj γ₀ = 1 := by
  rw [orientationTwist, hp.signRankOneLocalSystem_eq_one_of_section hσ hfix hfib hs hps, inv_one,
    one_zpow, mul_one, map_one]

end Twist

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
  (isCoveringMap_proj (F := F) (E := E) hι).orientationTwist proj_comp_deck deck_ne_self
    (fun _ _ h ↦ eq_or_eq_deck hι h) R (surjective_proj hι) γ₀

variable {F E R}

/-- An oriented bundle has trivial orientation twist. -/
theorem freeLoopOrientationTwist_eq_one (hι : Fintype.card ι = finrank ℝ F)
    (o : VectorBundleOrientation F E ι) (γ₀ : MooreFreeLoopSpace B) :
    freeLoopOrientationTwist F E R hι γ₀ = 1 :=
  (isCoveringMap_proj hι).orientationTwist_eq_one_of_section proj_comp_deck deck_ne_self
    (fun _ _ h ↦ eq_or_eq_deck hι h) (surjective_proj hι) (o.continuous_mk_cover hι)
    (fun b ↦ (rfl : (⟨b, o b⟩ : VectorBundleOrientationCover F E ι).proj = b)) γ₀

end TauCeti.VectorBundleOrientationCover
