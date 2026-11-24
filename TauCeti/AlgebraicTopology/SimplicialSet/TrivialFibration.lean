/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Cylinder
public import TauCeti.AlgebraicTopology.SimplicialSet.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialSet.PiZero

/-!
# Trivial fibrations of simplicial sets are shrinkable

A morphism `p : X ⟶ Y` of simplicial sets is *shrinkable* (in the sense of Dold) when it has a
section `s` such that `p ≫ s` is homotopic to `𝟙 X` through a homotopy over `Y`, that is, a
homotopy `h : X ⊗ Δ[1] ⟶ X` with `h ≫ p = fst ≫ p`. This is the simplicial analogue of a
fibrewise deformation of `X` onto the image of a section.

We prove that a morphism has the right lifting property with respect to all monomorphisms (a
trivial fibration for the Kan–Quillen model structure, see `SSet.rlp_monomorphisms`) exactly when
it is a Kan fibration which is shrinkable:

* a trivial fibration is a split epimorphism, any two maps into its source which agree after
  composing with it are homotopic over its target, and hence every section of it extends to a
  shrinking;
* conversely, a shrinkable left fibration is a trivial fibration;
* for a Kan fibration, a section `s` such that `p ≫ s` is homotopic to `𝟙 X`, by a homotopy which
  need not lie over `Y`, already extends to a shrinking: correcting the homotopy is a lifting
  problem against the anodyne inclusion `X ⊗ Λ[2, 0] ⟶ X ⊗ Δ[2]`.

In particular a trivial fibration is a simplicial homotopy equivalence, compatibly with the
projection to `Y`, and so induces a bijection on connected components. This is the combinatorial
input for the comparison of trivial fibrations with weak equivalences in the Kan–Quillen model
structure.

## Main declarations

* `SSet.Shrinking p`: a section of `p` together with a homotopy over `Y` from `p ≫ s` to `𝟙 X`.
* `SSet.isSplitEpi_of_rlp_monomorphisms`: a trivial fibration is a split epimorphism.
* `SSet.exists_homotopy_of_rlp_monomorphisms`: maps into the source of a trivial fibration which
  agree after composing with it are homotopic over its target.
* `SSet.Shrinking.ofRLP`: every section of a trivial fibration extends to a shrinking.
* `SSet.Shrinking.rlp_monomorphisms`: a shrinkable left fibration is a trivial fibration.
* `SSet.Homotopy.exists_lift_horn₂₀`: filling a horn `Λ[2, 0]` of homotopies relative to a Kan
  fibration.
* `SSet.Shrinking.ofHomotopy`: a section of a Kan fibration which is a homotopy inverse extends to
  a shrinking.
* `SSet.rlp_monomorphisms_iff`: the resulting characterization of trivial fibrations.
* `SSet.bijective_mapπ₀_of_rlp_monomorphisms`: a trivial fibration induces a bijection on
  connected components.

## References

* A. Dold, *Partitions of unity in the theory of fibrations*, Ann. of Math. 78 (1963).
* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Chapter I.
-/

public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits MorphismProperty
  HomotopicalAlgebra

open scoped Simplicial

namespace SSet

open modelCategoryQuillen

variable {X Y : SSet.{u}}

/-- A morphism with the right lifting property with respect to all monomorphisms is a split
epimorphism. -/
lemma isSplitEpi_of_rlp_monomorphisms {p : X ⟶ Y} (hp : (monomorphisms SSet.{u}).rlp p) :
    IsSplitEpi p := by
  have := hp _ (monomorphisms.infer_property (⊥ : Y.Subcomplex).ι)
  have sq : CommSq (Subcomplex.isInitialBot.to X) (⊥ : Y.Subcomplex).ι p (𝟙 Y) :=
    ⟨Subcomplex.isInitialBot.hom_ext _ _⟩
  exact ⟨⟨sq.lift, sq.fac_right⟩⟩

/-- Two morphisms `f g : Z ⟶ X` which agree after composing with a morphism `p : X ⟶ Y` having
the right lifting property with respect to all monomorphisms are homotopic over `Y`. -/
lemma exists_homotopy_of_rlp_monomorphisms {p : X ⟶ Y} (hp : (monomorphisms SSet.{u}).rlp p)
    {Z : SSet.{u}} (f g : Z ⟶ X) (w : f ≫ p = g ≫ p) :
    ∃ H : Homotopy f g, H.h ≫ p = fst Z Δ[1] ≫ f ≫ p := by
  -- Lift against the inclusion of the two ends of the cylinder the map which is `f` on
  -- `Z ⊗ {0}` and `g` on `Z ⊗ {1}`.
  let A₀ := Subcomplex.range (ι₀ : Z ⟶ Z ⊗ Δ[1])
  let A₁ := Subcomplex.range (ι₁ : Z ⟶ Z ⊗ Δ[1])
  have hsq := (show Subcomplex.BicartSq ⊥ A₀ A₁ (A₀ ⊔ A₁) from
    ⟨rfl, range_ι₀_inf_range_ι₁⟩).isPushout
  let φ : ((A₀ ⊔ A₁ : (Z ⊗ Δ[1]).Subcomplex) : SSet.{u}) ⟶ X :=
    hsq.desc (A₀.ι ≫ fst _ _ ≫ f) (A₁.ι ≫ fst _ _ ≫ g) (Subcomplex.isInitialBot.hom_ext _ _)
  have sq : CommSq φ (A₀ ⊔ A₁).ι p (fst _ _ ≫ f ≫ p) :=
    ⟨hsq.hom_ext (by simp [φ]) (by simp [φ, w])⟩
  have := hp _ (monomorphisms.infer_property (A₀ ⊔ A₁).ι)
  have h₀ : ι₀ = Subcomplex.toRange ι₀ ≫ Subcomplex.homOfLE le_sup_left ≫ (A₀ ⊔ A₁).ι := by
    simp [A₀]
  have h₁ : ι₁ = Subcomplex.toRange ι₁ ≫ Subcomplex.homOfLE le_sup_right ≫ (A₀ ⊔ A₁).ι := by
    simp [A₁]
  refine ⟨.mk' sq.lift ?_ ?_, sq.fac_right⟩
  · rw [h₀, Category.assoc, Category.assoc, sq.fac_left]
    simp [φ, A₀, hsq.inl_desc]
  · rw [h₁, Category.assoc, Category.assoc, sq.fac_left]
    simp [φ, A₁, hsq.inr_desc]

/-- A *shrinking* of a morphism `p : X ⟶ Y` of simplicial sets: a section `s` of `p` together
with a homotopy from `p ≫ s` to `𝟙 X` over `Y`. A morphism admitting a shrinking is shrinkable
in the sense of Dold. -/
structure Shrinking (p : X ⟶ Y) where
  /-- The section of `p`. -/
  section_ : Y ⟶ X
  /-- The section is a right inverse of `p`. -/
  section_comp : section_ ≫ p = 𝟙 Y := by cat_disch
  /-- The homotopy from `p ≫ section_` to the identity. -/
  homotopy : Homotopy (p ≫ section_) (𝟙 X)
  /-- The homotopy lies over `Y`. -/
  homotopy_h_comp : homotopy.h ≫ p = fst X Δ[1] ≫ p := by cat_disch

namespace Shrinking

attribute [reassoc (attr := simp)] section_comp homotopy_h_comp

variable {p : X ⟶ Y}

/-- Given a morphism `p` with the right lifting property with respect to all monomorphisms (a
trivial fibration), every section `s` of `p` extends to a shrinking of `p`. -/
noncomputable def ofRLP (hp : (monomorphisms SSet.{u}).rlp p) (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y) :
    Shrinking p where
  section_ := s
  section_comp := hs
  homotopy := (exists_homotopy_of_rlp_monomorphisms hp (p ≫ s) (𝟙 X) (by simp [hs])).choose
  homotopy_h_comp := by
    simpa [hs] using
      (exists_homotopy_of_rlp_monomorphisms hp (p ≫ s) (𝟙 X) (by simp [hs])).choose_spec

/-- The section of `ofRLP hp s hs` is `s`. -/
@[simp]
theorem ofRLP_section_ (hp : (monomorphisms SSet.{u}).rlp p) (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y) :
    (ofRLP hp s hs).section_ = s := by
  -- A tactic proof keeps the body of `ofRLP` private: an exported `dsimp` lemma would need it.
  rfl

/-- Filling the horn `Λ[2, 0]` of homotopies relative to a Kan fibration `p`: given homotopies
`H₀₁` from `f₀` to `f₁` and `H₀₂` from `f₀` to `f₂`, and a map `ω : Z ⊗ Δ[2] ⟶ Y` whose faces
`0 → 1` and `0 → 2` are the composites of `H₀₁` and `H₀₂` with `p`, there is a homotopy from `f₁`
to `f₂` whose composite with `p` is the face `1 → 2` of `ω`. -/
lemma Homotopy.exists_lift_horn₂₀ [Fibration p] {Z : SSet.{u}} {f₀ f₁ f₂ : Z ⟶ X}
    (H₀₁ : Homotopy f₀ f₁) (H₀₂ : Homotopy f₀ f₂) (ω : Z ⊗ Δ[2] ⟶ Y)
    (h₀₁ : Z ◁ stdSimplex.δ 2 ≫ ω = H₀₁.h ≫ p) (h₀₂ : Z ◁ stdSimplex.δ 1 ≫ ω = H₀₂.h ≫ p) :
    ∃ K : Homotopy f₁ f₂, K.h ≫ p = Z ◁ stdSimplex.δ 0 ≫ ω := by
  -- The two cylinders glue to a map on `Z ⊗ Λ[2, 0]`, along their common end `f₀`, which extends
  -- to `Z ⊗ Δ[2]` over `ω` since `Z ⊗ Λ[2, 0] ⟶ Z ⊗ Δ[2]` is anodyne. The face `1 → 2` of the
  -- extension is the required homotopy.
  have hpo : IsPushout (Z ◁ stdSimplex.δ 1) (Z ◁ stdSimplex.δ 1) (Z ◁ horn₂₀.ι₀₁)
      (Z ◁ horn₂₀.ι₀₂) :=
    horn₂₀.isPushout.{u}.map (tensorLeft Z)
  have e₁ : horn₂₀.ι₀₁ ≫ Λ[2, 0].ι = stdSimplex.{u}.δ 2 := horn.ι_ι _ _ _
  have e₂ : horn₂₀.ι₀₂ ≫ Λ[2, 0].ι = stdSimplex.{u}.δ 1 := horn.ι_ι _ _ _
  have d₁ : Z ◁ stdSimplex.{u}.δ (1 : Fin 2) ≫ Z ◁ stdSimplex.δ (0 : Fin 3) =
      Z ◁ stdSimplex.δ 0 ≫ Z ◁ stdSimplex.δ 2 := by
    simp only [← MonoidalCategory.whiskerLeft_comp]
    exact congrArg _ (CosimplicialObject.δ_comp_δ stdSimplex (i := 0) (j := 1) (by decide)).symm
  have d₂ : Z ◁ stdSimplex.{u}.δ (0 : Fin 2) ≫ Z ◁ stdSimplex.δ (0 : Fin 3) =
      Z ◁ stdSimplex.δ 0 ≫ Z ◁ stdSimplex.δ 1 := by
    simp only [← MonoidalCategory.whiskerLeft_comp]
    exact congrArg _ (CosimplicialObject.δ_comp_δ stdSimplex (i := 0) (j := 0) (by decide)).symm
  have h₀ : ι₀ ≫ H₀₁.h = ι₀ ≫ H₀₂.h := by rw [H₀₁.h₀, H₀₂.h₀]
  let φ : Z ⊗ (Λ[2, 0] : SSet.{u}) ⟶ X := hpo.desc H₀₁.h H₀₂.h (by
    rw [whiskerLeft_stdSimplex_δ_one, Category.assoc, Category.assoc, h₀])
  have sq : CommSq φ (Z ◁ Λ[2, 0].ι) p ω := ⟨hpo.hom_ext
    (by rw [hpo.inl_desc_assoc, ← whiskerLeft_comp_assoc, e₁, h₀₁])
    (by rw [hpo.inr_desc_assoc, ← whiskerLeft_comp_assoc, e₂, h₀₂])⟩
  have := (anodyneExtensions.horn_ι (n := 2) 0).whiskerLeft Z p (mem_fibrations p)
  -- The faces `0 → 1` and `0 → 2` of the extension are `H₀₁` and `H₀₂`.
  have l₀₁ : Z ◁ stdSimplex.δ 2 ≫ sq.lift = H₀₁.h := by
    rw [← e₁, MonoidalCategory.whiskerLeft_comp_assoc, sq.fac_left, hpo.inl_desc]
  have l₀₂ : Z ◁ stdSimplex.δ 1 ≫ sq.lift = H₀₂.h := by
    rw [← e₂, MonoidalCategory.whiskerLeft_comp_assoc, sq.fac_left, hpo.inr_desc]
  -- The ends of the face `1 → 2` are the ends `1` and `2` of these faces.
  refine ⟨.mk' (Z ◁ stdSimplex.δ 0 ≫ sq.lift) ?_ ?_, ?_⟩
  · rw [← fstStdSimplexZeroIso_inv_whiskerLeft_stdSimplex_δ_one_assoc, reassoc_of% d₁, l₀₁,
      fstStdSimplexZeroIso_inv_whiskerLeft_stdSimplex_δ_zero_assoc, H₀₁.h₁]
  · rw [← fstStdSimplexZeroIso_inv_whiskerLeft_stdSimplex_δ_zero_assoc, reassoc_of% d₂, l₀₂,
      fstStdSimplexZeroIso_inv_whiskerLeft_stdSimplex_δ_zero_assoc, H₀₂.h₁]
  · rw [Homotopy.mk'_h, Category.assoc, sq.fac_right]

/-- Let `p` be a Kan fibration with a section `s` such that `p ≫ s` is homotopic to `𝟙 X`. Then
there is also such a homotopy over `Y`. -/
private lemma exists_homotopy_over_of_homotopy [Fibration p] (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y)
    (H : Homotopy (p ≫ s) (𝟙 X)) :
    ∃ K : Homotopy (p ≫ s) (𝟙 X), K.h ≫ p = fst X Δ[1] ≫ p := by
  -- `σ = H ≫ p ≫ s` is a homotopy from `p ≫ s` to itself with the same image `H ≫ p` in `Y` as
  -- `H`. Fill the horn `Λ[2, 0]` formed by `σ` and `H` over the degenerate triangle of `H ≫ p`
  -- collapsing the edge `1 → 2`: its face `1 → 2` lies over the constant edge.
  let σ : Homotopy (p ≫ s) (p ≫ s) := .mk' (H.h ≫ p ≫ s) (by simp [reassoc_of% hs])
    (by simp)
  have d₁ : stdSimplex.{u}.δ (2 : Fin 3) ≫ stdSimplex.σ 1 = 𝟙 _ :=
    CosimplicialObject.δ_comp_σ_succ _ (i := 1)
  have d₂ : stdSimplex.{u}.δ (1 : Fin 3) ≫ stdSimplex.σ 1 = 𝟙 _ :=
    CosimplicialObject.δ_comp_σ_self _ (i := 1)
  have d₀ : (stdSimplex.{u}.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫ stdSimplex.σ 1 =
      stdSimplex.σ 0 ≫ stdSimplex.δ 0 :=
    CosimplicialObject.δ_comp_σ_of_le _ (i := 0) (j := 0) (by decide)
  obtain ⟨K, hK⟩ := Homotopy.exists_lift_horn₂₀ (p := p) σ H (X ◁ stdSimplex.σ 1 ≫ H.h ≫ p)
    (by rw [← whiskerLeft_comp_assoc, d₁]; simp [σ, hs])
    (by rw [← whiskerLeft_comp_assoc, d₂]; simp)
  refine ⟨K, ?_⟩
  rw [hK, ← whiskerLeft_comp_assoc, d₀]
  simp [whiskerLeft_stdSimplex_δ_zero]

/-- A section `s` of a Kan fibration `p` such that `p ≫ s` is homotopic to `𝟙 X`, through a
homotopy which need not lie over `Y`, extends to a shrinking of `p`. -/
noncomputable def ofHomotopy [Fibration p] (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y)
    (H : Homotopy (p ≫ s) (𝟙 X)) : Shrinking p where
  section_ := s
  section_comp := hs
  homotopy := (exists_homotopy_over_of_homotopy s hs H).choose
  homotopy_h_comp := (exists_homotopy_over_of_homotopy s hs H).choose_spec

/-- The section of `ofHomotopy s hs H` is `s`. -/
@[simp]
theorem ofHomotopy_section_ [Fibration p] (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y)
    (H : Homotopy (p ≫ s) (𝟙 X)) : (ofHomotopy s hs H).section_ = s := by
  -- A tactic proof keeps the body of `ofHomotopy` private: an exported `dsimp` lemma would need
  -- it.
  rfl

/-- A left fibration admitting a shrinking has the right lifting property with respect to all
monomorphisms. -/
theorem rlp_monomorphisms [LeftFibration p] (h : Shrinking p) : (monomorphisms SSet.{u}).rlp p := by
  intro A B i (hi : Mono i)
  refine ⟨fun {a b} sq ↦ ?_⟩
  -- Deform `b ≫ h.section_` along the shrinking, extending the shrinking homotopy on `A`, by the
  -- covering homotopy extension property of `p`; the other end of the deformation is a lift.
  obtain ⟨L, -, hL, hLp⟩ := exists_lift_cylinder_ι₀_of_mono i p (fst _ _ ≫ b) (b ≫ h.section_)
    (a ▷ Δ[1] ≫ h.homotopy.h) (by simp) (by simp [sq.w]) (by simp [sq.w_assoc])
  exact ⟨⟨{ l := ι₁ ≫ L
            fac_left := by rw [← ι₁_comp_assoc, hL]; simp
            fac_right := by simp [hLp] }⟩⟩

end Shrinking

/-- A morphism of simplicial sets has the right lifting property with respect to all monomorphisms
(it is a trivial fibration for the Kan–Quillen model structure) if and only if it is a Kan
fibration admitting a shrinking. -/
theorem rlp_monomorphisms_iff {p : X ⟶ Y} :
    (monomorphisms SSet.{u}).rlp p ↔ Fibration p ∧ Nonempty (Shrinking p) :=
  ⟨fun hp ↦ ⟨(modelCategoryQuillen.fibration_iff p).2 (antitone_rlp J_le_monomorphisms _ hp),
    have := isSplitEpi_of_rlp_monomorphisms hp
    ⟨.ofRLP hp (section_ p) (IsSplitEpi.id p)⟩⟩, fun ⟨_, ⟨h⟩⟩ ↦ h.rlp_monomorphisms⟩

/-- A morphism with the right lifting property with respect to all monomorphisms (a trivial
fibration) induces a bijection on connected components. -/
lemma bijective_mapπ₀_of_rlp_monomorphisms {p : X ⟶ Y} (hp : (monomorphisms SSet.{u}).rlp p) :
    Function.Bijective (mapπ₀ p) := by
  have := isSplitEpi_of_rlp_monomorphisms hp
  let h := Shrinking.ofRLP hp (section_ p) (IsSplitEpi.id p)
  refine Function.bijective_iff_has_inverse.2 ⟨mapπ₀ h.section_, fun c ↦ ?_, fun c ↦ ?_⟩
  · rw [← mapπ₀_comp_apply, h.homotopy.mapπ₀_eq, mapπ₀_id_apply]
  · rw [← mapπ₀_comp_apply, h.section_comp, mapπ₀_id_apply]

end SSet
