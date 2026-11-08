/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AffineScheme
public import TauCeti.AlgebraicGeometry.Restrict

/-!
# Invariant opens of a scheme with a group action and the action on their sections

Let a group `G` act on a scheme `X` by automorphisms, `σ : G →* Aut X`. An open `U` of `X` is
invariant when `(σ g)⁻¹ U = U` for every `g`. Then `G` acts on the sections `Γ(X, U)` by ring
automorphisms through pullback along inverses, `g • a = (σ g⁻¹)^* a`, extending
`AlgebraicGeometry.Scheme.globalSectionsMulSemiringAction` from `U = ⊤` to every invariant open
(`AlgebraicGeometry.Scheme.sectionsMulSemiringAction_top`). Restriction between invariant
opens is equivariant, and the basic open of an invariant section is invariant.

For an invariant affine open `U`, the action on `Γ(X, U)` is the one whose affine invariant quotient
`Spec Γ(X, U)ᴳ` is a chart of the quotient of `X` by `G`, constructed in
`TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.Glued.Basic`.

## Main definitions

* `AlgebraicGeometry.Scheme.Opens.IsInvariant`: an open is invariant under `σ`.
* `AlgebraicGeometry.Scheme.sectionsMulSemiringAction`: the action of `G` on the sections over an
  invariant open, not an instance since it depends on `σ`.

## Main results

* `AlgebraicGeometry.Scheme.presheaf_map_smul`: restriction between invariant opens is equivariant.
* `AlgebraicGeometry.Scheme.Opens.IsInvariant.basicOpen`: basic opens of invariant sections are
  invariant.
-/

public section

open CategoryTheory Opposite

namespace AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {G : Type v} [Group G] {σ : G →* Aut X}

variable (σ) in
/-- An open subset `U` of `X` is invariant under `σ` when it is its own preimage under every
automorphism `σ g`. -/
def Scheme.Opens.IsInvariant (U : X.Opens) : Prop :=
  ∀ g, (σ g).asIso.hom ⁻¹ᵁ U = U

/-- An open is invariant exactly when it is its own preimage under every `σ g`. -/
lemma Scheme.Opens.isInvariant_iff {U : X.Opens} :
    U.IsInvariant σ ↔ ∀ g, (σ g).asIso.hom ⁻¹ᵁ U = U :=
  Iff.rfl

namespace Scheme.Opens.IsInvariant

/-- An invariant open is its own preimage under every `σ g`. -/
lemma preimage_eq {U : X.Opens} (hU : U.IsInvariant σ) (g : G) : (σ g).asIso.hom ⁻¹ᵁ U = U :=
  hU g

variable (σ) in
/-- The whole scheme is invariant. -/
lemma top : (⊤ : X.Opens).IsInvariant σ :=
  fun _ ↦ rfl

/-- The intersection of two invariant opens is invariant. -/
lemma inf {U V : X.Opens} (hU : U.IsInvariant σ) (hV : V.IsInvariant σ) :
    (U ⊓ V).IsInvariant σ := fun g ↦ by
  rw [Scheme.Hom.preimage_inf, hU.preimage_eq g, hV.preimage_eq g]

/-- A point lies in an invariant open exactly when its image under `σ g` does. -/
lemma apply_mem_iff {U : X.Opens} (hU : U.IsInvariant σ) (g : G) {x : X} :
    (σ g).asIso.hom x ∈ U ↔ x ∈ U := by
  conv_rhs => rw [← hU.preimage_eq g]
  rfl

end Scheme.Opens.IsInvariant

variable (σ) in
/-- **A group acting on a scheme acts on the sections over an invariant open**, by pullback along
inverses: `g • a = (σ g⁻¹)^* a`. For `U = ⊤` this is `Scheme.globalSectionsMulSemiringAction`
(`Scheme.sectionsMulSemiringAction_top`). It is not an instance, since `σ` and the invariance
proof do not occur in the type `Γ(X, U)`. -/
@[instance_reducible]
noncomputable def Scheme.sectionsMulSemiringAction {U : X.Opens} (hU : U.IsInvariant σ) :
    MulSemiringAction G Γ(X, U) where
  smul g a := ((σ g⁻¹).asIso.hom.appLE U U (hU.preimage_eq g⁻¹).ge).hom a
  -- In the two proofs below, `g • a` is `(σ g⁻¹)^*(a)` by the `smul` field above, and `change`
  -- states the goal in that form.
  one_smul a := by
    change ((σ 1⁻¹).asIso.hom.appLE U U (hU.preimage_eq 1⁻¹).ge).hom a = a
    rw [Scheme.Hom.congr_appLE _ (g := 𝟙 X) (by simp) _ _ _ (by simp)]
    -- The preimage of `U` under the identity is `U` itself, by definition.
    exact congr(($(Scheme.Hom.appLE_eq_app (f := 𝟙 X) (U := U))).hom a)
  mul_smul g h a := by
    change ((σ (g * h)⁻¹).asIso.hom.appLE U U (hU.preimage_eq _).ge).hom a =
      ((σ g⁻¹).asIso.hom.appLE U U (hU.preimage_eq _).ge).hom
        (((σ h⁻¹).asIso.hom.appLE U U (hU.preimage_eq _).ge).hom a)
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    congr 2
    exact Scheme.Hom.congr_appLE _ (by simp [Aut.mul_asIso]) _ _ _ _
  smul_zero g := map_zero _
  smul_add g := map_add _
  smul_one g := map_one _
  smul_mul g := map_mul _

/-- Under `Scheme.sectionsMulSemiringAction σ hU`, `g` acts on a section by pullback along
`σ g⁻¹`. -/
lemma Scheme.sectionsMulSemiringAction_smul_def {U : X.Opens} (hU : U.IsInvariant σ) (g : G)
    (a : Γ(X, U)) :
    letI := Scheme.sectionsMulSemiringAction σ hU
    g • a = ((σ g⁻¹).asIso.hom.appLE U U (hU.preimage_eq g⁻¹).ge).hom a :=
  (rfl)

/-- On global sections, the action on the sections over the invariant open `⊤` is the action
`Scheme.globalSectionsMulSemiringAction` on global functions. -/
lemma Scheme.sectionsMulSemiringAction_top :
    Scheme.sectionsMulSemiringAction σ (Scheme.Opens.IsInvariant.top σ) =
      Scheme.globalSectionsMulSemiringAction σ := by
  have h (g : G) (a : Γ(X, ⊤)) :
      (letI := Scheme.sectionsMulSemiringAction σ (Scheme.Opens.IsInvariant.top σ); g • a) =
        (letI := Scheme.globalSectionsMulSemiringAction σ; g • a) := by
    rw [Scheme.sectionsMulSemiringAction_smul_def,
      Scheme.globalSectionsMulSemiringAction_smul_def]
    -- The preimage of `⊤` under any morphism is `⊤` itself, by definition.
    exact congr(($(Scheme.Hom.appLE_eq_app (f := (σ g⁻¹).asIso.hom) (U := ⊤))).hom a)
  -- A `MulSemiringAction` is determined by its scalar multiplication; its other fields are proofs.
  generalize Scheme.sectionsMulSemiringAction σ _ = A at h
  generalize Scheme.globalSectionsMulSemiringAction σ = B at h
  obtain ⟨A⟩ := A
  obtain ⟨B⟩ := B
  congr
  exact DistribMulAction.ext (funext₂ h)

/-- The automorphism `σ g` acts on the sections over an invariant open as `g⁻¹`. -/
lemma Scheme.appLE_apply_eq_inv_smul {U : X.Opens} (hU : U.IsInvariant σ) (g : G)
    (a : Γ(X, U)) :
    letI := Scheme.sectionsMulSemiringAction σ hU
    ((σ g).asIso.hom.appLE U U (hU.preimage_eq g).ge).hom a = g⁻¹ • a := by
  rw [Scheme.sectionsMulSemiringAction_smul_def]
  congr 2
  exact Scheme.Hom.congr_appLE _ (by rw [inv_inv]) _ _ _ _

/-- Restriction of sections between invariant opens is equivariant. -/
lemma Scheme.presheaf_map_smul {U V : X.Opens} (hU : U.IsInvariant σ) (hV : V.IsInvariant σ)
    (h : V ≤ U) (g : G) (a : Γ(X, U)) :
    letI := Scheme.sectionsMulSemiringAction σ hU
    letI := Scheme.sectionsMulSemiringAction σ hV
    (X.presheaf.map (homOfLE h).op).hom (g • a) = g • (X.presheaf.map (homOfLE h).op).hom a := by
  simp only [Scheme.sectionsMulSemiringAction_smul_def, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

/-- The basic open of a section over an invariant open is invariant when the section is. -/
lemma Scheme.Opens.IsInvariant.basicOpen {U : X.Opens} (hU : U.IsInvariant σ) (r : Γ(X, U))
    (hr : letI := Scheme.sectionsMulSemiringAction σ hU; ∀ g : G, g • r = r) :
    (X.basicOpen r).IsInvariant σ := fun g ↦ by
  have h := Scheme.basicOpen_appLE (σ g).asIso.hom U U (hU.preimage_eq g).ge r
  rw [Scheme.appLE_apply_eq_inv_smul hU, hr] at h
  refine (h.trans (inf_eq_right.mpr ?_)).symm
  conv_rhs => rw [← hU.preimage_eq g]
  exact Scheme.Hom.preimage_mono _ (X.basicOpen_le r)

end AlgebraicGeometry
