/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.AlgebraicGeometry.Limits
public import TauCeti.CategoryTheory.Comma.Over

/-!
# Base change of a section of a scheme morphism

A `T`-point `x : T ⟶ X` of `X` over `S` has a graph `T ⟶ T ×_S X`, a section of the
projection `T ×_S X ⟶ T` (`graphSection`). Graphs commute with base change along morphisms
`T' ⟶ T` over `S`, and form pullback squares with the induced morphisms
`T' ×_S X ⟶ T ×_S X` (`isPullback_graphSection`). A section `x₀` of `f` induces a section
`baseChangeSection` on each base change `T ×_S X`: the graph of the `T`-point `T ⟶ S ⟶ X`
(`basePoint`), so its projection formulas and naturality in `T` follow from those of graphs.
For a base change `X' = S' ×_S X` along `g : S' ⟶ S`, the base-changed sections of `x₀` and of
its base change `x₀'` agree under `T ×_S X ≅ T ×_{S'} X'`
(`baseChangeSection_comp_pullbackRightPullbackFstIso_inv`).

Over an open `U` of `S`, a section `σ` of `g : Z ⟶ S` restricts functions on `g⁻¹ U` to `U`,
giving a `Γ(S, U)`-algebra map `σ^* : Γ(Z, g⁻¹ U) → Γ(S, U)` (`sectionAlgHom`).
-/

public section

open CategoryTheory Limits

namespace TauCeti
namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} {f : X ⟶ S} {x₀ : S ⟶ X} (hx₀ : x₀ ≫ f = 𝟙 S)

/-- The **graph** `T ⟶ T ×_S X` of a `T`-point `x : T ⟶ X` of `X` over `S`: the section of the
projection `T ×_S X ⟶ T` whose second component is `x`. -/
def graphSection {T : Over S} (x : T ⟶ Over.mk f) : T.left ⟶ pullback T.hom f :=
  pullback.lift (𝟙 T.left) x.left (by simpa using (Over.w x).symm)

/-- The graph of a `T`-point is a section of the projection `T ×_S X ⟶ T`. -/
@[reassoc (attr := simp)]
lemma graphSection_fst {T : Over S} (x : T ⟶ Over.mk f) :
    graphSection x ≫ pullback.fst T.hom f = 𝟙 T.left :=
  pullback.lift_fst _ _ _

/-- The second component of the graph of a `T`-point `x` is `x` itself. -/
@[reassoc (attr := simp)]
lemma graphSection_snd {T : Over S} (x : T ⟶ Over.mk f) :
    graphSection x ≫ pullback.snd T.hom f = x.left :=
  pullback.lift_snd _ _ _

/-- Graphs commute with base change: the graph of `φ ≫ x` followed by the induced morphism
`T' ×_S X ⟶ T ×_S X` is `φ` followed by the graph of `x`. -/
@[reassoc]
lemma graphSection_comp_pullback_map {T' T : Over S} (φ : T' ⟶ T) (x : T ⟶ Over.mk f) :
    graphSection (φ ≫ x) ≫ ((Over.pullback f).map φ).left = φ.left ≫ graphSection x := by
  apply pullback.hom_ext <;> simp

/-- The graph of a `T`-point `x` and the graph of its base change `φ ≫ x` along `φ : T' ⟶ T` form
a pullback square with the induced morphism `T' ×_S X ⟶ T ×_S X`. -/
lemma isPullback_graphSection {T' T : Over S} (φ : T' ⟶ T) (x : T ⟶ Over.mk f) :
    IsPullback (graphSection (φ ≫ x)) φ.left ((Over.pullback f).map φ).left
      (graphSection x) := by
  -- The square formed by `T' ×_S X ⟶ T ×_S X` and the two projections is a pullback square;
  -- pasting with it gives a square whose horizontal composites are identities.
  refine IsPullback.of_right ?_ (graphSection_comp_pullback_map φ x)
    (Over.isPullback_pullback_map_left f φ).flip
  rw [graphSection_fst, graphSection_fst]
  exact IsPullback.id_horiz φ.left

/-- The `T`-point `T ⟶ S ⟶ X` of `X` over `S` given by a section `x₀` of `f`. -/
def basePoint (T : Over S) : T ⟶ Over.mk f :=
  Over.homMk (T.hom ≫ x₀) (by simp [hx₀])

/-- The underlying morphism of the base point is `T ⟶ S ⟶ X`. -/
@[simp]
lemma basePoint_left (T : Over S) : (basePoint hx₀ T).left = T.hom ≫ x₀ :=
  (rfl)

/-- The base points are compatible with morphisms over `S`. -/
@[reassoc (attr := simp)]
lemma comp_basePoint {T' T : Over S} (φ : T' ⟶ T) : φ ≫ basePoint hx₀ T = basePoint hx₀ T' := by
  ext
  simp [Over.w_assoc φ]

variable (f x₀)

/-- The base change `x₀_T : T ⟶ T ×_S X` of a section `x₀` of `f : X ⟶ S` to a scheme `T` over
`S`: the graph of the `T`-point `T ⟶ S ⟶ X`. -/
def baseChangeSection (T : Over S) : T.left ⟶ pullback T.hom f :=
  graphSection (basePoint hx₀ T)

/-- The graph of the base point `T ⟶ S ⟶ X` is the base-changed section. -/
lemma graphSection_basePoint (T : Over S) :
    graphSection (basePoint hx₀ T) = baseChangeSection f x₀ hx₀ T :=
  (rfl)

/-- The base-changed section is a section of the projection `T ×_S X ⟶ T`. -/
@[reassoc (attr := simp)]
lemma baseChangeSection_fst (T : Over S) :
    baseChangeSection f x₀ hx₀ T ≫ pullback.fst T.hom f = 𝟙 T.left :=
  graphSection_fst _

/-- The base-changed section followed by the projection to `X` is `T ⟶ S ⟶ X`. -/
@[reassoc (attr := simp)]
lemma baseChangeSection_snd (T : Over S) :
    baseChangeSection f x₀ hx₀ T ≫ pullback.snd T.hom f = T.hom ≫ x₀ :=
  graphSection_snd _

/-- The base-changed sections are compatible with the morphisms `T' ×_S X ⟶ T ×_S X` induced by
morphisms `T' ⟶ T` over `S`. -/
@[reassoc]
lemma baseChangeSection_comp_pullback_map {T' T : Over S} (φ : T' ⟶ T) :
    baseChangeSection f x₀ hx₀ T' ≫
        ((Over.pullback f).map φ).left =
      φ.left ≫ baseChangeSection f x₀ hx₀ T := by
  rw [baseChangeSection, baseChangeSection, ← comp_basePoint hx₀ φ]
  exact graphSection_comp_pullback_map φ (basePoint hx₀ T)

/-- The base-changed section over `T'` is the pullback of the base-changed section over `T`
along a morphism `T' ⟶ T` of schemes over `S`. -/
lemma isPullback_baseChangeSection {T' T : Over S} (φ : T' ⟶ T) :
    IsPullback (baseChangeSection f x₀ hx₀ T') φ.left
      ((Over.pullback f).map φ).left (baseChangeSection f x₀ hx₀ T) :=
  IsPullback.of_right
    (by simpa only [baseChangeSection_fst] using IsPullback.id_horiz φ.left)
    (baseChangeSection_comp_pullback_map f x₀ hx₀ φ) (Over.isPullback_pullback_map_left f φ).flip

variable {S' : Scheme.{u}} (g : S' ⟶ S)

/-- The base-changed sections are compatible with `T ×_S X ≅ T ×_{S'} (S' ×_S X)`. -/
@[reassoc]
lemma baseChangeSection_comp_pullbackRightPullbackFstIso_inv (T : Over S') :
    baseChangeSection f x₀ hx₀ ((Over.map g).obj T) ≫ (pullbackRightPullbackFstIso g f T.hom).inv =
      𝟙 T.left ≫ baseChangeSection (pullback.fst g f) (baseChangeSection f x₀ hx₀ (Over.mk g))
        (baseChangeSection_fst f x₀ hx₀ (Over.mk g)) T := by
  -- The lemmas for the base-changed sections are stated for `T.hom`, which `simp` does not match
  -- against `((Over.map g).obj T).hom = T.hom ≫ g` and `(Over.mk g).hom = g`.
  have h₁ := baseChangeSection_fst f x₀ hx₀ ((Over.map g).obj T)
  have h₂ := baseChangeSection_snd f x₀ hx₀ ((Over.map g).obj T)
  have h₃ := baseChangeSection_fst f x₀ hx₀ (Over.mk g)
  have h₄ := baseChangeSection_snd f x₀ hx₀ (Over.mk g)
  simp only [Over.map_obj_hom, Over.mk_hom] at h₁ h₂ h₃ h₄
  apply pullback.hom_ext
  · simpa using h₁
  · apply pullback.hom_ext
    · simp [reassoc_of% h₁, h₃]
    · simp [h₂, h₄]

end

section SectionAlgHom

variable {Z S : Scheme.{u}} (g : Z ⟶ S) {σ : S ⟶ Z} (hσ : σ ≫ g = 𝟙 S)

include hσ in
/-- A section `σ` of `g` pulls `g⁻¹ U` back to `U`. -/
theorem preimage_preimage_of_comp_eq_id (U : S.Opens) : σ ⁻¹ᵁ g ⁻¹ᵁ U = U := by
  rw [← Scheme.Hom.comp_preimage, hσ, Scheme.Hom.id_preimage]

/-- The ring map `Γ(S, U) → Γ(Z, g⁻¹ U) → Γ(S, U)` of a section is the identity. -/
theorem app_comp_appLE_of_comp_eq_id (U : S.Opens) :
    g.app U ≫ σ.appLE (g ⁻¹ᵁ U) U (preimage_preimage_of_comp_eq_id g hσ U).ge = 𝟙 _ := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (f : S ⟶ S) (_ : f = 𝟙 S) (e : U ≤ f ⁻¹ᵁ U), f.appLE U U e = 𝟙 _ := by
    rintro _ rfl e
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact S.presheaf.map_id _
  exact key _ hσ _

/-- The `Γ(S, U)`-algebra map `σ^* : Γ(Z, g⁻¹ U) → Γ(S, U)` of a section `σ` of `g`, over an open
`U` of `S`. -/
noncomputable def sectionAlgHom (U : S.Opens) :
    letI := (g.app U).hom.toAlgebra
    Γ(Z, g ⁻¹ᵁ U) →ₐ[Γ(S, U)] Γ(S, U) :=
  letI := (g.app U).hom.toAlgebra
  { (σ.appLE (g ⁻¹ᵁ U) U (preimage_preimage_of_comp_eq_id g hσ U).ge).hom with
    commutes' a := congr($(app_comp_appLE_of_comp_eq_id g hσ U).hom a) }

/-- The algebra map `σ^*` of a section evaluates the restriction along `σ`. -/
@[simp]
theorem sectionAlgHom_apply (U : S.Opens) (b : Γ(Z, g ⁻¹ᵁ U)) :
    sectionAlgHom g hσ U b = σ.appLE (g ⁻¹ᵁ U) U (preimage_preimage_of_comp_eq_id g hσ U).ge b :=
  (rfl)

/-- On global sections, `sectionAlgHom g hσ ⊤` transports `b : Γ(Z, g ⁻¹ᵁ ⊤)` along
`g.preimage_top` and applies `σ.appTop`. -/
theorem sectionAlgHom_top_apply (b : Γ(Z, g ⁻¹ᵁ ⊤)) :
    sectionAlgHom g hσ ⊤ b =
      σ.appTop (Z.presheaf.map (eqToHom g.preimage_top.symm).op b) := by
  have happ : σ.appLE ⊤ ⊤ σ.preimage_top.ge = σ.appTop := σ.appLE_eq_app
  rw [sectionAlgHom_apply, ← CommRingCat.comp_apply, ← happ, Scheme.Hom.map_appLE]

/-- Evaluating `sectionAlgHom g hσ ⊤` on a global section `u : Γ(Z, ⊤)` transported to
`Γ(Z, g ⁻¹ᵁ ⊤)` gives `σ.appTop u`. -/
theorem sectionAlgHom_top_map_apply (u : Γ(Z, ⊤)) :
    sectionAlgHom g hσ ⊤ (Z.presheaf.map (eqToHom g.preimage_top).op u) = σ.appTop u := by
  rw [sectionAlgHom_top_apply,
    ← CommRingCat.comp_apply (Z.presheaf.map _) (Z.presheaf.map _), ← Functor.map_comp,
    eqToHom_op, eqToHom_op, eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id,
    CommRingCat.id_apply]

/-- The kernel of `sectionAlgHom g hσ ⊤` is the image of `RingHom.ker σ.appTop.hom` under
`Z.presheaf.map (eqToHom g.preimage_top).op`. -/
theorem ker_sectionAlgHom_top :
    letI := (g.app ⊤).hom.toAlgebra
    RingHom.ker (sectionAlgHom g hσ ⊤) =
      (RingHom.ker σ.appTop.hom).map (Z.presheaf.map (eqToHom g.preimage_top).op).hom := by
  let _ := (g.app ⊤).hom.toAlgebra
  let e : Γ(Z, ⊤) ≃+* Γ(Z, g ⁻¹ᵁ ⊤) :=
    (Z.presheaf.mapIso (eqToIso g.preimage_top).op).commRingCatIsoToRingEquiv
  have he : (RingHom.ker σ.appTop.hom).map (Z.presheaf.map (eqToHom g.preimage_top).op).hom =
      (RingHom.ker σ.appTop.hom).map e := rfl
  have he_symm (b : Γ(Z, g ⁻¹ᵁ ⊤)) :
      e.symm b = Z.presheaf.map (eqToHom g.preimage_top.symm).op b := rfl
  rw [he]
  ext b
  rw [RingHom.mem_ker, sectionAlgHom_top_apply, ← Ideal.symm_apply_mem_of_equiv_iff,
    RingHom.mem_ker, he_symm]

/-- Composing `g.app ⊤` with transport along `g.preimage_top.symm` gives `g.appTop`. -/
@[reassoc]
theorem app_top_comp_map_preimage_top :
    g.app ⊤ ≫ Z.presheaf.map (eqToHom g.preimage_top.symm).op = g.appTop := by
  have htop : g.appLE ⊤ ⊤ g.preimage_top.ge = g.appTop := g.appLE_eq_app
  rw [g.app_eq_appLE, Scheme.Hom.appLE_map, htop]

/-- Composing `g.appTop` with transport along `g.preimage_top` gives `g.app ⊤`. -/
@[reassoc]
theorem appTop_comp_map_preimage_top :
    g.appTop ≫ Z.presheaf.map (eqToHom g.preimage_top).op = g.app ⊤ := by
  have htop : g.appLE ⊤ ⊤ g.preimage_top.ge = g.appTop := g.appLE_eq_app
  rw [← htop, Scheme.Hom.appLE_map]
  exact g.appLE_eq_app

end SectionAlgHom

end AlgebraicGeometry
end TauCeti
