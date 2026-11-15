/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import TauCeti.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Lifting homotopies along Kan fibrations

The ends `Z ⊗ {0}` and `Z ⊗ {1}` of the cylinder `Z ⊗ Δ[1]` are anodyne extensions
(`SSet.anodyneExtensions_ι₀`, `SSet.anodyneExtensions_ι₁`): they are the images of
`Z ⊗ Λ[1, 0]` and `Z ⊗ Λ[1, 1]`, and the product of `Z` with a horn inclusion is anodyne. So a
homotopy into the base of a Kan fibration lifts, starting from a lift of either of its ends.

More generally, a Kan fibration has the covering homotopy extension property with respect to every
monomorphism `i : A ⟶ B` (`SSet.exists_lift_cylinder_of_mono`): a homotopy `B ⊗ Δ[1] ⟶ Y` lifts,
extending a lift of its start `B ⊗ {0}` and a compatible lift of its restriction to
`A ⊗ Δ[1]`. This is lifting against the pushout-product of `i` with `Λ[1, 0] ⟶ Δ[1]`, the
inclusion of `B ⊗ {0} ∪ A ⊗ Δ[1]` into `B ⊗ Δ[1]`, which is anodyne by the theorem of Joël Riou
and Jack McKoen in Mathlib (`SSet.anodyneExtensions_pushoutObjObjι`).

## References

* P. Gabriel and M. Zisman, *Calculus of fractions and homotopy theory*, Ergebnisse der
  Mathematik 35, Springer, 1967, Chapter IV, Section 2.
* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Chapter I, Section 4.
-/

public section

universe u

open CategoryTheory Limits MorphismProperty MonoidalCategory CartesianMonoidalCategory
  HomotopicalAlgebra Simplicial

namespace SSet

open modelCategoryQuillen

/-- The end `Z ⊗ {k}` of the cylinder `Z ⊗ Δ[1]`; it is `ι₀` for `k = 0` and `ι₁` for `k = 1`. -/
private noncomputable abbrev cylinderEnd (Z : SSet.{u}) (k : Fin 2) : Z ⟶ Z ⊗ Δ[1] :=
  lift (𝟙 Z) (const (stdSimplex.obj₀Equiv.symm k))

private lemma cylinderEnd_zero (Z : SSet.{u}) : cylinderEnd Z 0 = ι₀ := rfl

private lemma cylinderEnd_one (Z : SSet.{u}) : cylinderEnd Z 1 = ι₁ := rfl

/-- The product of `Z` with the inclusion of the horn `Λ[1, k]`, which is the vertex `k`, factors
through the end `Z ⊗ {k}` of the cylinder. -/
private lemma whiskerLeft_horn_one_ι (Z : SSet.{u}) (k : Fin 2) :
    Z ◁ Λ[1, k].ι = fst _ _ ≫ cylinderEnd Z k :=
  CartesianMonoidalCategory.hom_ext _ _ (by simp) (by simp [horn_one_ι_eq_const, comp_const])

/-- The end `Z ⊗ {k}` of the cylinder factors through `Z ⊗ Λ[1, k]` by a section of the
projection to `Z`. -/
private lemma exists_section_whiskerLeft_horn_one_ι (Z : SSet.{u}) (k : Fin 2) :
    ∃ s : Z ⟶ Z ⊗ (Λ[1, k] : SSet.{u}), s ≫ fst _ _ = 𝟙 Z ∧
      s ≫ Z ◁ Λ[1, k].ι = cylinderEnd Z k :=
  -- Any map to the horn `Λ[1, k]` composes with its inclusion to the constant map at `k`.
  ⟨lift (𝟙 Z) (stdSimplex.isTerminalObj₀.from Z ≫ horn.ι k (k + 1) (by fin_cases k <;> decide)),
    by simp, by simp only [lift_whiskerLeft, Category.assoc, horn_one_ι_eq_const, comp_const]⟩

/-- The end `Z ⊗ {k}` of the cylinder `Z ⊗ Δ[1]` is an anodyne extension. -/
private lemma anodyneExtensions_cylinderEnd (Z : SSet.{u}) (k : Fin 2) :
    anodyneExtensions (cylinderEnd Z k) := by
  intro E B p hp
  have := anodyneExtensions.whiskerLeft (anodyneExtensions.horn_ι.{u} (n := 1) k) Z p hp
  obtain ⟨s, hs₁, hs₂⟩ := exists_section_whiskerLeft_horn_one_ι Z k
  refine ⟨fun {f g} sq ↦ ?_⟩
  -- Lift against `Z ⊗ Λ[1, k] ⟶ Z ⊗ Δ[1]` and restrict along the section `s`.
  have sq' : CommSq (fst _ _ ≫ f) (Z ◁ Λ[1, k].ι) p g :=
    ⟨by rw [whiskerLeft_horn_one_ι, Category.assoc, sq.w, Category.assoc]⟩
  exact ⟨⟨{ l := sq'.lift
            fac_left := by rw [← hs₂, Category.assoc, sq'.fac_left, reassoc_of% hs₁] }⟩⟩

/-- The end `Z ⊗ {0}` of the cylinder `Z ⊗ Δ[1]` is an anodyne extension. -/
lemma anodyneExtensions_ι₀ (Z : SSet.{u}) : anodyneExtensions (ι₀ : Z ⟶ Z ⊗ Δ[1]) :=
  cylinderEnd_zero Z ▸ anodyneExtensions_cylinderEnd Z 0

/-- The end `Z ⊗ {1}` of the cylinder `Z ⊗ Δ[1]` is an anodyne extension. -/
lemma anodyneExtensions_ι₁ (Z : SSet.{u}) : anodyneExtensions (ι₁ : Z ⟶ Z ⊗ Δ[1]) :=
  cylinderEnd_one Z ▸ anodyneExtensions_cylinderEnd Z 1

/-- The covering homotopy extension property of a Kan fibration `p : X ⟶ Y` with respect to a
monomorphism `i : A ⟶ B`: a homotopy `H : B ⊗ Δ[1] ⟶ Y` lifts along `p`, extending a lift `g` of
its start and a lift `L` of its restriction to `A ⊗ Δ[1]` which agree on `A ⊗ {0}`. -/
theorem exists_lift_cylinder_of_mono {A B X Y : SSet.{u}} (i : A ⟶ B) [Mono i] (p : X ⟶ Y)
    [Fibration p] (H : B ⊗ Δ[1] ⟶ Y) (g : B ⟶ X) (L : A ⊗ Δ[1] ⟶ X) (hg : g ≫ p = ι₀ ≫ H)
    (hL : L ≫ p = i ▷ Δ[1] ≫ H) (hgL : i ≫ g = ι₀ ≫ L) :
    ∃ L' : B ⊗ Δ[1] ⟶ X, ι₀ ≫ L' = g ∧ i ▷ Δ[1] ≫ L' = L ∧ L' ≫ p = H := by
  -- Lift against the anodyne pushout-product of `i` with the vertex `0` of `Δ[1]`, the
  -- inclusion of `B ⊗ {0} ∪ A ⊗ Δ[1]`, on which `g` and `L` define a map.
  let P := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i Λ[1, 0].ι
  have := anodyneExtensions_pushoutObjObjι P (.horn_ι 0) p (mem_fibrations p)
  let φ : P.pt ⟶ X := P.isPushout.desc (fst _ _ ≫ g) L (by
    dsimp
    rw [whiskerLeft_horn_one_ι, cylinderEnd_zero, Category.assoc, ← hgL, whiskerRight_fst_assoc])
  have sq : CommSq φ P.ι p H := ⟨P.hom_ext
    (by simp only [φ, IsPushout.inl_desc_assoc, P.inl_ι_assoc, curriedTensor_obj_map,
      whiskerLeft_horn_one_ι, cylinderEnd_zero, Category.assoc, hg])
    (by simp [φ, hL])⟩
  obtain ⟨s, hs₁, hs₂⟩ := exists_section_whiskerLeft_horn_one_ι B 0
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · have e : B ◁ Λ[1, 0].ι = P.inl ≫ P.ι := P.inl_ι.symm
    -- `ι₀` is the composite of the section `s` with `B ⊗ Λ[1, 0] ⟶ B ⊗ Δ[1]`.
    rw [← cylinderEnd_zero, ← hs₂, e, Category.assoc, Category.assoc, sq.fac_left]
    simp [φ, reassoc_of% hs₁]
  · have e : i ▷ Δ[1] = P.inr ≫ P.ι := P.inr_ι.symm
    rw [e, Category.assoc, sq.fac_left]
    simp [φ]

end SSet
