/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import TauCeti.AlgebraicTopology.SimplicialSet.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialSet.PiZero
public import TauCeti.AlgebraicTopology.SimplicialSet.StdSimplex

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
* conversely, a shrinkable Kan fibration is a trivial fibration.

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
* `SSet.Shrinking.rlp_monomorphisms`: a shrinkable Kan fibration is a trivial fibration.
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

/-- A Kan fibration admitting a shrinking has the right lifting property with respect to all
monomorphisms. -/
theorem rlp_monomorphisms [Fibration p] (h : Shrinking p) : (monomorphisms SSet.{u}).rlp p := by
  intro A B i (hi : Mono i)
  refine ⟨fun {a b} sq ↦ ?_⟩
  -- Deform `b ≫ h.section_` along the shrinking, extending the shrinking homotopy on `A`, by
  -- lifting against the anodyne pushout-product of `i` with the vertex `0` of `Δ[1]`; the other
  -- end of the deformation is a lift.
  let P := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i Λ[1, 0].ι
  have hP : anodyneExtensions P.ι := anodyneExtensions_pushoutObjObjι P (.horn_ι 0)
  have := hP p (mem_fibrations p)
  let φ : P.pt ⟶ X := P.isPushout.desc (fst _ _ ≫ b ≫ h.section_) (a ▷ _ ≫ h.homotopy.h) (by
    have e : X ◁ Λ[1, 0].ι ≫ h.homotopy.h = fst _ _ ≫ p ≫ h.section_ := by
      have hι : X ◁ Λ[1, 0].ι = fst _ _ ≫ ι₀ := CartesianMonoidalCategory.hom_ext _ _
        (by simp) (by simp [horn_one_ι_eq_const, comp_const])
      rw [hι, Category.assoc, Homotopy.h₀]
    dsimp
    rw [whisker_exchange_assoc, e]
    simp [sq.w_assoc])
  have sq' : CommSq φ P.ι p (fst _ _ ≫ b) := ⟨P.hom_ext (by simp [φ]) (by
    simp [φ, sq.w])⟩
  exact ⟨⟨{ l := ι₁ ≫ sq'.lift
            fac_left := by
              have e : i ▷ Δ[1] = P.inr ≫ P.ι := P.inr_ι.symm
              rw [← ι₁_comp_assoc, e, Category.assoc, sq'.fac_left]
              simp [φ]
            fac_right := by simp }⟩⟩

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
