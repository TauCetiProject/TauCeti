/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.AlgebraicGeometry.Limits
public import TauCeti.CategoryTheory.Comma.Over
import Mathlib.AlgebraicGeometry.PullbackCarrier

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
giving a `Γ(S, U)`-algebra map `σ^* : Γ(Z, g⁻¹ U) → Γ(S, U)` (`sectionAlgHom`). More generally, a
morphism `f : X ⟶ Y` over `S` induces a `Γ(S, ⊤)`-algebra homomorphism
`Γ(Y, ⊤) →ₐ[Γ(S, ⊤)] Γ(X, ⊤)` (`Scheme.Hom.appTopAlgHom`).

In any pullback square `gY : Y' ⟶ Y` over `b : S' ⟶ S`, the preimage `gY ⁻¹' Set.range s` of a
section `s` is the range of a compatible lifted section `s'`
(`preimage_range_section_of_isPullback`, specialized to `baseChangeSection` and to closed rational
points over field extensions in `preimage_range_section_eq_range_baseChangeSection` and
`preimage_singleton_section_closedPoint_of_isPullback`).
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

/-- Over a scheme with at most one point, a point of a base change that projects into the image
of a section is the value of the base-changed section. -/
lemma baseChangeSection_eq_of_snd_eq {T : Scheme.{u}} [Subsingleton T] (g : T ⟶ S)
    (t : T) {y : (pullback g f : Scheme.{u})} {s : S}
    (hy : (pullback.snd g f : _ ⟶ X) y = x₀ s) :
    baseChangeSection f x₀ hx₀ (Over.mk g) t = y := by
  have : IsIso (x₀ ≫ f) := by rw [hx₀]; infer_instance
  have : Subsingleton (pullback (pullback.snd g f) x₀ : Scheme.{u}) :=
    ((pullbackLeftPullbackSndIso g f x₀).hom ≫ pullback.fst _ _).homeomorph.subsingleton
  have image_mem (z : (pullback g f : Scheme.{u}))
      (hz : (pullback.snd g f : _ ⟶ X) z ∈ Set.range x₀) :
      z ∈ Set.range (pullback.fst (pullback.snd g f) x₀ : _ ⟶ _) := by
    rw [Scheme.Pullback.range_fst]
    exact hz
  obtain ⟨y', hy'⟩ := image_mem y ⟨s, hy.symm⟩
  obtain ⟨z', hz'⟩ := image_mem (baseChangeSection f x₀ hx₀ (Over.mk g) t) ⟨g t, by
    simpa only [Over.mk_hom, Scheme.Hom.comp_apply] using
      congrArg (fun m : T ⟶ X ↦ m t) (baseChangeSection_snd f x₀ hx₀ (Over.mk g)).symm⟩
  rw [← hy', ← hz', Subsingleton.elim y' z']

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

/-- On global sections, `sectionAlgHom g hσ ⊤` applies `σ.appTop`. -/
theorem sectionAlgHom_top_apply (b : Γ(Z, ⊤)) :
    sectionAlgHom g hσ ⊤ b = σ.appTop b :=
  (sectionAlgHom_apply g hσ ⊤ b).trans congr($(σ.appLE_eq_app).hom b)

/-- A morphism `f : X ⟶ Y` over `S` (`f ≫ g = h`) induces `Γ(Y, ⊤) →ₐ[Γ(S, ⊤)] Γ(X, ⊤)`. -/
noncomputable def _root_.AlgebraicGeometry.Scheme.Hom.appTopAlgHom {X Y S : Scheme.{u}}
    (f : X ⟶ Y) {g : Y ⟶ S} {h : X ⟶ S} (hfg : f ≫ g = h) :
    letI := g.appTop.hom.toAlgebra; letI := h.appTop.hom.toAlgebra
    Γ(Y, ⊤) →ₐ[Γ(S, ⊤)] Γ(X, ⊤) :=
  letI := g.appTop.hom.toAlgebra; letI := h.appTop.hom.toAlgebra
  { f.appTop.hom with
    commutes' r := congr($((Scheme.Hom.comp_appTop f g).symm.trans
      (congrArg Scheme.Hom.appTop hfg)).hom r) }

/-- Evaluating `f.appTopAlgHom hfg` applies `f.appTop`. -/
@[simp] theorem _root_.AlgebraicGeometry.Scheme.Hom.appTopAlgHom_apply {X Y S : Scheme.{u}}
    (f : X ⟶ Y) {g : Y ⟶ S} {h : X ⟶ S} (hfg : f ≫ g = h) (u : Γ(Y, ⊤)) :
    f.appTopAlgHom hfg u = f.appTop u := (rfl)

/-- The underlying function of `f.appTopAlgHom hfg` is `f.appTop`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.coe_appTopAlgHom {X Y S : Scheme.{u}}
    (f : X ⟶ Y) {g : Y ⟶ S} {h : X ⟶ S} (hfg : f ≫ g = h) : ⇑(f.appTopAlgHom hfg) = f.appTop :=
  (rfl)

/-- Coercing `f.appTopAlgHom hfg` to a ring homomorphism recovers `f.appTop.hom`. -/
@[simp, norm_cast] theorem _root_.AlgebraicGeometry.Scheme.Hom.toRingHom_appTopAlgHom
    {X Y S : Scheme.{u}} (f : X ⟶ Y) {g : Y ⟶ S} {h : X ⟶ S} (hfg : f ≫ g = h) :
    (f.appTopAlgHom hfg : Γ(Y, ⊤) →+* Γ(X, ⊤)) = f.appTop.hom := (rfl)

end SectionAlgHom

section SectionPullback

variable {S S' Y Y' : Scheme.{u}} {gY : Y' ⟶ Y} {p' : Y' ⟶ S'} {p : Y ⟶ S} {b : S' ⟶ S}

/-- **The preimage of a section in a pullback square is the lifted section.** Let `Y'` be the
pullback of `p : Y ⟶ S` along `b : S' ⟶ S`, let `s : S ⟶ Y` be a section of `p`, and let
`s' : S' ⟶ Y'` be a section of `p'` satisfying `s' ≫ gY = b ≫ s`. Then
`gY ⁻¹' Set.range s = Set.range s'`, with no assumption on `b`. -/
theorem preimage_range_section_of_isPullback (H : IsPullback gY p' p b)
    {s : S ⟶ Y} (hs : s ≫ p = 𝟙 S) {s' : S' ⟶ Y'} (hs'p : s' ≫ p' = 𝟙 S')
    (hs'g : s' ≫ gY = b ≫ s) :
    gY ⁻¹' Set.range s = Set.range s' := by
  have htop : IsPullback b (s' ≫ p') (s ≫ p) b := by
    rw [hs'p, hs]
    exact IsPullback.id_vert b
  have hsec : IsPullback b s' s gY := IsPullback.of_bot htop hs'g.symm H
  simpa only [Set.preimage_univ, Set.image_univ] using
    (Scheme.image_preimage_eq_of_isPullback hsec Set.univ).symm

/-- Specialization of `preimage_range_section_of_isPullback` to `baseChangeSection`. -/
@[simp]
theorem preimage_range_section_eq_range_baseChangeSection {s : S ⟶ Y} (hs : s ≫ p = 𝟙 S)
    (b : S' ⟶ S) :
    pullback.snd b p ⁻¹' Set.range s = Set.range (baseChangeSection p s hs (Over.mk b)) :=
  preimage_range_section_of_isPullback (IsPullback.of_hasPullback b p).flip hs
    (baseChangeSection_fst p s hs (Over.mk b)) (baseChangeSection_snd p s hs (Over.mk b))

/-- Over a field extension `L / k`, the preimage of a `k`-rational point `s (closedPoint k)` under
the base-change projection `Y' ⟶ Y` is the single `L`-rational point `s' (closedPoint L)`. -/
theorem preimage_singleton_section_closedPoint_of_isPullback {k L : Type u} [Field k] [Field L]
    [Algebra k L] {gY : Y' ⟶ Y} {p' : Y' ⟶ Spec (.of L)} {p : Y ⟶ Spec (.of k)}
    (H : IsPullback gY p' p (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    {s : Spec (.of k) ⟶ Y} (hs : s ≫ p = 𝟙 _) {s' : Spec (.of L) ⟶ Y'} (hs'p : s' ≫ p' = 𝟙 _)
    (hs'g : s' ≫ gY = Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ s) :
    gY ⁻¹' {s (IsLocalRing.closedPoint k)} = {s' (IsLocalRing.closedPoint L)} := by
  have hrk : Set.range s = {s (IsLocalRing.closedPoint k)} :=
    Set.range_eq_singleton fun z ↦ congrArg s (Subsingleton.elim z _)
  have hrL : Set.range s' = {s' (IsLocalRing.closedPoint L)} :=
    Set.range_eq_singleton fun z ↦ congrArg s' (Subsingleton.elim z _)
  rw [← hrk, ← hrL]
  exact preimage_range_section_of_isPullback H hs hs'p hs'g

end SectionPullback

end AlgebraicGeometry
end TauCeti
