/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Open subsets of schemes

This file records general-purpose facts about open subsets of schemes.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.instNonemptyTop` states that the whole space is a nonempty open
  subset of any nonempty scheme.
* `AlgebraicGeometry.IsAffineOpen.presheaf_map_fromSpec_appIso_hom` identifies restriction of
  structure-sheaf sections along the affine chart `Spec Γ(X, U)`.
* `AlgebraicGeometry.Scheme.Hom.appLE_eq_id_of_eq_id` identifies the restriction maps of a scheme
  endomorphism equal to the identity.
* `AlgebraicGeometry.Scheme.forall_affineOpens_map_of_le`: a condition on the restrictions of a
  section over `V` to all affine opens inside `V` is inherited by its restriction to any smaller
  open.
* `AlgebraicGeometry.Scheme.existsUnique_gluing_affineOpens`: sections over the affine opens,
  compatible with restriction, glue to a unique global section.
* `AlgebraicGeometry.IsAffineOpen.fromSpec_appLE_self` and
  `AlgebraicGeometry.Scheme.Hom.appLE_ΓSpecIso_hom_naturality` compute the global sections of
  affine charts `Spec R ⟶ X` and their precomposites with `Spec.map φ`.
-/

open TopologicalSpace AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

public section

open CategoryTheory Opposite

noncomputable section

variable {X : Scheme.{u}} {U : X.Opens}

/-- The preimages of two opens covering the target cover the source. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.preimage_sup_eq_top {Y : Scheme.{u}}
    (f : X ⟶ Y) {U V : Y.Opens} (hUV : U ⊔ V = ⊤) :
    f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V = ⊤ := by
  rw [← f.preimage_sup, hUV, f.preimage_top]

/-- If an endomorphism `f` of `X` equals the identity, then so does each of its restriction maps
`Γ(X, U) ⟶ Γ(X, U)`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.appLE_eq_id_of_eq_id {f : X ⟶ X}
    (hf : f = 𝟙 X) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ U) : f.appLE U U e = 𝟙 _ := by
  subst hf
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
  exact (Category.id_comp _).trans (X.presheaf.map_id _)

/-- A condition imposed on the restrictions of a section `b` over `V` to all affine opens inside `V`
is inherited by the restriction of `b` to any smaller open `V'`. -/
theorem _root_.AlgebraicGeometry.Scheme.forall_affineOpens_map_of_le {V V' : X.Opens}
    (hV'V : V' ≤ V) {b : Γ(X, V)} {P : ∀ W : X.affineOpens, Γ(X, W) → Prop}
    (h : ∀ (W : X.affineOpens) (hWV : W.1 ≤ V), P W (X.presheaf.map (homOfLE hWV).op b))
    (W : X.affineOpens) (hWV' : W.1 ≤ V') :
    P W (X.presheaf.map (homOfLE hWV').op (X.presheaf.map (homOfLE hV'V).op b)) := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
  exact h W (hWV'.trans hV'V)

/-- **Sections glue along the affine opens.** A family of sections `s U ∈ Γ(X, U)`, one over each
affine open `U` of `X`, compatible with restriction from an affine open to a smaller one, consists
of the restrictions of a unique global section. -/
theorem _root_.AlgebraicGeometry.Scheme.existsUnique_gluing_affineOpens (X : Scheme.{u})
    (s : ∀ U : X.affineOpens, Γ(X, U.1))
    (hs : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1), X.presheaf.map (homOfLE h).op (s U) = s V) :
    ∃! t : Γ(X, ⊤), ∀ U : X.affineOpens, X.presheaf.map (homOfLE le_top).op t = s U := by
  -- every open `V` is covered by the affine opens it contains
  have hcov (V : X.Opens) : V ≤ ⨆ W : {W : X.affineOpens // W.1 ≤ V}, W.1.1 := fun x hx ↦ by
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
    exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWV⟩, hxW⟩
  refine X.sheaf.existsUnique_gluing' (fun U : X.affineOpens ↦ U.1) ⊤ (fun _ ↦ homOfLE le_top)
    (iSup_affineOpens_eq_top X).ge s fun U U' ↦ ?_
  -- on `U ⊓ U'`, the two restrictions agree on every affine open `W ⊆ U ⊓ U'`
  refine X.sheaf.eq_of_locally_eq' (fun W : {W : X.affineOpens // W.1 ≤ U.1 ⊓ U'.1} ↦ W.1.1) _
    (fun W ↦ homOfLE W.2) (hcov _) _ _ fun W ↦ ?_
  -- stated through `X.presheaf`, the underlying presheaf of `X.sheaf`
  have h₁ : X.presheaf.map (homOfLE W.2).op (X.presheaf.map (Opens.infLELeft U.1 U'.1).op (s U)) =
      s W.1 := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact hs U W.1 (W.2.trans inf_le_left)
  have h₂ :
      X.presheaf.map (homOfLE W.2).op (X.presheaf.map (Opens.infLERight U.1 U'.1).op (s U')) =
        s W.1 := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact hs U' W.1 (W.2.trans inf_le_right)
  exact h₁.trans h₂.symm

/-- Along the open immersion `hU.fromSpec : Spec Γ(X, U) ⟶ X` onto an affine open `U`,
restricting a section of `𝒪_X` from `U` to the image of an open `V` and transporting it to `V`
gives the restriction to `V` of the corresponding global section of `Spec Γ(X, U)`. -/
@[reassoc]
theorem _root_.AlgebraicGeometry.IsAffineOpen.presheaf_map_fromSpec_appIso_hom
    (hU : IsAffineOpen U) (V : (Spec Γ(X, U)).Opens) :
    X.presheaf.map (homOfLE (by
        simpa [hU.opensRange_fromSpec] using hU.fromSpec.image_le_opensRange V)).op ≫
      (hU.fromSpec.appIso V).hom =
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map V.leTop.op := by
  rw [← hU.fromSpec.appLE_appIso_inv (by simp [hU.fromSpec_preimage_self]), Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc,
    ← Functor.map_comp]
  rfl

/-- Pulling a section over an affine open `U` back to all of `Spec Γ(X, U)` along `hU.fromSpec`
is the inverse of the global-sections isomorphism of `Spec`. -/
theorem _root_.AlgebraicGeometry.IsAffineOpen.fromSpec_appLE_self (hU : IsAffineOpen U)
    (e : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  exact (congrArg _ ((congrArg _ (Subsingleton.elim _ _)).trans
    ((Spec Γ(X, U)).presheaf.map_id _))).trans (Category.comp_id _)

/-- Global sections of an affine chart `f : Spec R ⟶ Y` are natural in `R`: precomposing `f` with
`Spec.map φ` turns the induced map `Γ(Y, V) ⟶ R` into its composite with `φ`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.appLE_ΓSpecIso_hom_naturality {R S : CommRingCat.{u}}
    {Y : Scheme.{u}} (f : Spec R ⟶ Y) {q : Spec S ⟶ Y} (φ : R ⟶ S) (h : q = Spec.map φ ≫ f)
    {V : Y.Opens} (e : ⊤ ≤ f ⁻¹ᵁ V) (e' : ⊤ ≤ q ⁻¹ᵁ V) :
    q.appLE V ⊤ e' ≫ (Scheme.ΓSpecIso S).hom =
      (f.appLE V ⊤ e ≫ (Scheme.ΓSpecIso R).hom) ≫ φ := by
  subst h
  -- `Scheme.Hom.appLE_eq_app` at `⊤` applies because `Spec.map φ ⁻¹ᵁ ⊤` is `⊤` by definition.
  have h : (Spec.map φ ≫ f).appLE V ⊤ e' = f.appLE V ⊤ e ≫ (Spec.map φ).appTop :=
    (Scheme.Hom.appLE_comp_appLE (Spec.map φ) f V ⊤ ⊤ e le_top).symm.trans
      (congrArg (f.appLE V ⊤ e ≫ ·) (Scheme.Hom.appLE_eq_app (Spec.map φ) (U := ⊤)))
  rw [h, Category.assoc, Category.assoc, Scheme.ΓSpecIso_naturality]

end

end

namespace Scheme

/-- The whole space is a nonempty open subset of a nonempty scheme. -/
public instance instNonemptyTop {X : Scheme.{u}} [Nonempty X] :
    Nonempty ((⊤ : X.Opens) : Type u) :=
  let ⟨x⟩ := ‹Nonempty X›
  ⟨⟨x, trivial⟩⟩

end Scheme

end AlgebraicGeometry

end TauCeti
