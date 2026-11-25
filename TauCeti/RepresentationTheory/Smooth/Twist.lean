/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Category
public import TauCeti.RepresentationTheory.Smooth.Character

/-!
# Twisting smooth representations by a smooth character

Let `G` be a topological group, `A` a commutative ring and `χ : G →* Aˣ` a smooth character. The
twist `V ↦ V ⊗ χ`, the same module with `g` acting by `χ(g) ρ(g)` (`Representation.charTwist`),
preserves smoothness and keeps every intertwining map intertwining. So it is a functor
`SmoothRep.twist χ : SmoothRep A G ⥤ SmoothRep A G`, acting as the identity on underlying modules
and linear maps. Twisting by the trivial character is the identity, twisting by `ψ` and then by
`χ` is twisting by `χψ`, and twisting by `χ⁻¹` undoes twisting by `χ`. Hence the twist is an
autoequivalence of `SmoothRep A G` (`SmoothRep.twistEquiv`).

## Main definitions

* `TauCeti.SmoothRep.twist χ hχ`: the twist functor `V ↦ V ⊗ χ`.
* `TauCeti.SmoothRep.twistOneIso`: `twist 1 ≅ 𝟭`.
* `TauCeti.SmoothRep.twistCompTwistIso`: `twist ψ ⋙ twist χ ≅ twist (χψ)`.
* `TauCeti.SmoothRep.twistCompTwistInvIso`, `TauCeti.SmoothRep.twistInvCompTwistIso`:
  `twist χ ⋙ twist χ⁻¹ ≅ 𝟭` and `twist χ⁻¹ ⋙ twist χ ≅ 𝟭`.
* `TauCeti.SmoothRep.twistEquiv χ hχ`: the twist as an autoequivalence of `SmoothRep A G`.

## References

* I. Bernstein and A. Zelevinsky, *Representations of the group GL(n, F)*, Russian Math. Surveys
  31:3 (1976), 1–68, Ch. I §2, 2.25(c), p. 23.
-/

public section

noncomputable section

open CategoryTheory Representation

universe w u v

namespace TauCeti.SmoothRep

variable {A : Type u} {G : Type v} [CommRing A] [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G]

/-- **The twist by a smooth character** `χ`, as an endofunctor of `SmoothRep A G`: it sends `V`
to the same module with `g` acting by `χ(g) ρ(g)`, and an intertwining map to the same linear map
(`Representation.IntertwiningMap.charTwistLinearEquiv`). -/
-- An abbreviation, so that the twisted objects are seen to have the same underlying modules.
abbrev twist (χ : G →* Aˣ) (hχ : IsSmoothCharacter χ) : SmoothRep.{w} A G ⥤ SmoothRep.{w} A G where
  obj V := ⟨Rep.of (charTwist χ V.obj.ρ), hχ.isSmooth_charTwist _⟩
  map f := ObjectProperty.homMk <| Rep.ofHom <| IntertwiningMap.charTwistLinearEquiv χ f.hom.hom
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

/-- **Twisting by the trivial character is the identity**: `twist 1 ≅ 𝟭`. -/
def twistOneIso : twist.{w} (1 : G →* Aˣ) isSmoothCharacter_one ≅ 𝟭 (SmoothRep.{w} A G) :=
  NatIso.ofComponents (fun V ↦ ObjectProperty.isoMk _ <| Rep.mkIso <|
      .mk (LinearEquiv.refl A V.obj) fun g ↦ by
        ext v
        simp)
    fun _ ↦ by ext; simp

/-- **Successive twists multiply the characters**: `twist ψ ⋙ twist χ ≅ twist (χψ)`. -/
def twistCompTwistIso {χ ψ : G →* Aˣ} (hχ : IsSmoothCharacter χ) (hψ : IsSmoothCharacter ψ) :
    twist.{w} ψ hψ ⋙ twist χ hχ ≅ twist (χ * ψ) (hχ.mul hψ) :=
  NatIso.ofComponents (fun V ↦ ObjectProperty.isoMk _ <| Rep.mkIso <|
      .mk (LinearEquiv.refl A V.obj) fun g ↦ by
        ext v
        simp [mul_smul])
    fun _ ↦ by ext; simp

/-- **Twisting by `χ⁻¹` undoes twisting by `χ`**: `twist χ ⋙ twist χ⁻¹ ≅ 𝟭`. -/
def twistCompTwistInvIso {χ : G →* Aˣ} (hχ : IsSmoothCharacter χ) :
    twist.{w} χ hχ ⋙ twist χ⁻¹ hχ.inv ≅ 𝟭 (SmoothRep.{w} A G) :=
  NatIso.ofComponents (fun V ↦ ObjectProperty.isoMk _ <| Rep.mkIso <|
      .mk (LinearEquiv.refl A V.obj) fun g ↦ by
        ext v
        simp [smul_smul])
    fun _ ↦ by ext; simp

/-- **Twisting by `χ` undoes twisting by `χ⁻¹`**: `twist χ⁻¹ ⋙ twist χ ≅ 𝟭`. -/
def twistInvCompTwistIso {χ : G →* Aˣ} (hχ : IsSmoothCharacter χ) :
    twist.{w} χ⁻¹ hχ.inv ⋙ twist χ hχ ≅ 𝟭 (SmoothRep.{w} A G) :=
  NatIso.ofComponents (fun V ↦ ObjectProperty.isoMk _ <| Rep.mkIso <|
      .mk (LinearEquiv.refl A V.obj) fun g ↦ by
        ext v
        simp [smul_smul])
    fun _ ↦ by ext; simp

/-- **The twist by a smooth character is an autoequivalence** of `SmoothRep A G`, with inverse the
twist by `χ⁻¹`. -/
def twistEquiv (χ : G →* Aˣ) (hχ : IsSmoothCharacter χ) :
    SmoothRep.{w} A G ≌ SmoothRep.{w} A G :=
  .mk (twist χ hχ) (twist χ⁻¹ hχ.inv) (twistCompTwistInvIso hχ).symm (twistInvCompTwistIso hχ)

@[simp]
theorem twistEquiv_functor (χ : G →* Aˣ) (hχ : IsSmoothCharacter χ) :
    (twistEquiv.{w} χ hχ).functor = twist χ hχ :=
  (rfl)

instance isEquivalence_twist (χ : G →* Aˣ) (hχ : IsSmoothCharacter χ) :
    (twist.{w} χ hχ).IsEquivalence :=
  (twistEquiv χ hχ).isEquivalence_functor

end TauCeti.SmoothRep
