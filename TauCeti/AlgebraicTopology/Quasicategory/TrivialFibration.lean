/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.CategoricalEquivalence
public import TauCeti.AlgebraicTopology.Quasicategory.CategoricalFibration
public import TauCeti.AlgebraicTopology.Quasicategory.PointwiseEquivalence
public import TauCeti.AlgebraicTopology.Quasicategory.RightFibration.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.TrivialFibration

/-!
# Trivial fibrations of quasicategories

A trivial fibration of simplicial sets is a map `p : X ⟶ Y` with the right lifting property with
respect to every monomorphism, `(monomorphisms SSet).rlp p`. This file compares trivial
fibrations with the categorical notions of maps of quasicategories: categorical fibrations,
essential surjectivity and categorical equivalences.

A trivial fibration is a categorical fibration (`SSet.CategoricalFibration.of_rlp_monomorphisms`):
it is a Kan fibration, hence an inner fibration, and through every vertex `x₀` of `X` it has a
section `s`, obtained by lifting the identity of `Y` against the inclusion of the vertex `p x₀`.
The section carries the equivalences out of `p x₀` to equivalences out of `x₀` lifting them.

**A trivial fibration between quasicategories is a categorical equivalence**
(`SSet.QCat.IsCategoricalEquivalence.of_rlp_monomorphisms`). A section `s` of `p` is a
quasi-inverse: `s ≫ p` is the identity of `Y`, and the identity of `X` and `p ≫ s` agree after
composing with `p`, so they are joined by a homotopy `X ⊗ Δ[1] ⟶ X` over `Y`. This homotopy is an
edge of the functor quasicategory `Fun(X, X)`. Its component at a vertex `x` lies over the
degenerate edge at `p x`, and a trivial fibration is a right fibration, which reflects
equivalences, so every component is an equivalence. Since equivalences of functors are detected
pointwise (`SSet.Edge.isEquivalence_iff_forall_isEquivalence_map_evalAt`), the homotopy is an
equivalence of `Fun(X, X)`, which gives the invertible `2`-morphism from `𝟙 X` to `p ≫ s` in the
bicategory of quasicategories.

Conversely, the characterization of categorical equivalences as the fully faithful and
essentially surjective maps rests on the fact that a categorical fibration between quasicategories
that is fully faithful and essentially surjective is a trivial fibration. Its first step, lifting
vertices, holds for every essentially surjective categorical fibration to a quasicategory: the
equivalence joining a vertex `y` to a vertex `p x` of the image lifts to an edge out of `x` ending
over `y` (`SSet.CategoricalFibration.surjective_app_zero_of_essSurj`). Lifting the boundaries of
the higher simplices uses that the maps of right mapping spaces are weak equivalences, and is not
proved here.

## Main results

* `SSet.CategoricalFibration.of_rlp_monomorphisms`: a trivial fibration is a categorical fibration.
* `SSet.QCat.IsCategoricalEquivalence.of_rlp_monomorphisms`: a trivial fibration between
  quasicategories is a categorical equivalence.
* `SSet.CategoricalFibration.surjective_app_zero_of_essSurj`: an essentially surjective categorical
  fibration to a quasicategory is surjective on vertices.

## References

* J. Lurie, *Kerodon*, §4.5 (equivalences of ∞-categories) and §4.6.2 (fully faithful and
  essentially surjective functors).
* J. Lurie, *Higher Topos Theory*, §1.2.10 and §2.4.6.
-/

public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed Limits
  MorphismProperty Opposite Simplicial

namespace SSet

variable {X Y : SSet.{u}}

namespace CategoricalFibration

/-- **A trivial fibration is a categorical fibration.** It is an inner fibration, and through each
vertex `x₀` of its source it has a section, which lifts the equivalences out of `p x₀`. -/
theorem of_rlp_monomorphisms {p : X ⟶ Y} (hp : (monomorphisms SSet.{u}).rlp p) :
    CategoricalFibration p := by
  have := (rlp_monomorphisms_iff.1 hp).1
  refine { mem := mem_innerFibrations p, exists_isEquivalence_lift := fun x₀ _ e he ↦ ?_ }
  -- Lift the identity of `Y` against the inclusion of the vertex `p x₀`, sending it to `x₀`.
  let y : Δ[0] ⟶ Y := yonedaEquiv.symm (p.app _ x₀)
  have := stdSimplex.isTerminalObj₀.mono_from y
  have := hp y (monomorphisms.infer_property y)
  have sq : CommSq (yonedaEquiv.symm x₀) y p (𝟙 Y) :=
    ⟨by rw [yonedaEquiv_symm_comp, Category.comp_id]⟩
  refine exists_isEquivalence_lift_of_section sq.lift sq.fac_right ?_ e he
  have h := congrArg yonedaEquiv sq.fac_left
  rwa [yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h

/-- **An essentially surjective categorical fibration to a quasicategory is surjective on
vertices**: the equivalence joining a vertex `y` to a vertex `p x` of the image lifts to an edge
out of `x`, whose target lies over `y`. -/
theorem surjective_app_zero_of_essSurj [Quasicategory Y] (p : X ⟶ Y) [CategoricalFibration p]
    [(mapHomotopyCategory p).EssSurj] : Function.Surjective (p.app (op ⦋0⦌)) := by
  intro y
  obtain ⟨x, e, he⟩ := (essSurj_mapHomotopyCategory_iff p).1 inferInstance y
  obtain ⟨x₁, e', -, h⟩ := exists_isEquivalence_lift x e he
  refine ⟨x₁, ?_⟩
  rw [← e'.tgt_eq, ← e.tgt_eq, ← h, δ_naturality_apply]

end CategoricalFibration

namespace QCat

variable {X Y : QCat.{u}}

/-- The vertex of `Fun(X, Z)` corresponding to `φ : 𝟙_ SSet ⟶ Fun(X, Z)` is the map uncurried
from `φ`. -/
private lemma ihomObj₀Equiv_unitHomEquiv {X Z : SSet.{u}} (φ : 𝟙_ SSet ⟶ (ihom X).obj Z) :
    ihomObj₀Equiv X Z (unitHomEquiv _ φ) = MonoidalClosed.uncurry' φ := by
  have h : toUnit X ≫ φ = const (unitHomEquiv _ φ) := by
    rw [← comp_const (toUnit X)]
    exact congrArg _ ((unitHomEquiv _).symm_apply_apply φ).symm
  have hρ : lift (𝟙 X) (toUnit X) = (ρ_ X).inv := by ext <;> simp
  rw [ihomObj₀Equiv_apply, ← h, MonoidalClosed.uncurry', uncurry_eq, ← lift_whiskerLeft, hρ,
    Category.assoc]

/-- The object of the hom-category `X ⟶ Y` of the bicategory of quasicategories underlying a
`1`-morphism `f` is the class of the vertex of `Fun(X, Y)` corresponding to `f`. -/
private lemma homEquiv_eq_mk (f : X ⟶ Y) :
    CatEnrichedOrdinary.homEquiv f =
      HomotopyCategory.mk ((ihomObj₀Equiv X.obj Y.obj).symm f.hom) :=
  -- By definition, `homEquiv f` is the class of the vertex `unitHomEquiv _ (eHomEquiv SSet f)`,
  -- and `eHomEquiv SSet f` uncurries to `f.hom`.
  congrArg HomotopyCategory.mk
    ((Equiv.eq_symm_apply _).2 (ihomObj₀Equiv_unitHomEquiv (eHomEquiv SSet f)))

/-- An equivalence of `Fun(X, Y)` between the vertices corresponding to `f` and `g` gives an
invertible `2`-morphism `f ≅ g` of the bicategory of quasicategories. -/
private lemma nonempty_iso_of_isEquivalence {f g : X ⟶ Y}
    {α : Edge ((ihomObj₀Equiv X.obj Y.obj).symm f.hom) ((ihomObj₀Equiv X.obj Y.obj).symm g.hom)}
    (hα : α.IsEquivalence) : Nonempty (f ≅ g) := by
  have := Y.property
  obtain ⟨φ⟩ := HomotopyCategory.nonempty_iso_mk_iff.2 ⟨α, hα⟩
  let ψ : CatEnrichedOrdinary.homEquiv f ≅ CatEnrichedOrdinary.homEquiv g :=
    eqToIso (homEquiv_eq_mk f) ≪≫ φ ≪≫ eqToIso (homEquiv_eq_mk g).symm
  exact ⟨{ hom := .mk ψ.hom
           inv := .mk ψ.inv
           hom_inv_id := CatEnrichedOrdinary.Hom.ext _ _ ψ.hom_inv_id
           inv_hom_id := CatEnrichedOrdinary.Hom.ext _ _ ψ.inv_hom_id }⟩

/-- **A trivial fibration between quasicategories is a categorical equivalence.** A section `s` of
`p` is a quasi-inverse: `s ≫ p` is the identity, and a homotopy over `Y` from the identity of `X`
to `p ≫ s` is an equivalence of `Fun(X, X)`, since its components lie over identities. -/
theorem IsCategoricalEquivalence.of_rlp_monomorphisms {p : X ⟶ Y}
    (hp : (monomorphisms SSet.{u}).rlp p.hom) : IsCategoricalEquivalence p := by
  have := X.property
  have := (rlp_monomorphisms_iff.1 hp).1
  have := isSplitEpi_of_rlp_monomorphisms hp
  have hs : section_ p.hom ≫ p.hom = 𝟙 _ := IsSplitEpi.id p.hom
  let s : Y ⟶ X := ObjectProperty.homMk (section_ p.hom)
  obtain ⟨H, hH⟩ := exists_homotopy_of_rlp_monomorphisms hp (𝟙 X.obj) (p.hom ≫ section_ p.hom)
    (by simp [hs])
  -- The component of `H` at `x` lies over the degenerate edge at `p x`, so it is an equivalence.
  have hα : ((ihomEdgeEquiv _ _).symm H).IsEquivalence := by
    refine (Edge.isEquivalence_iff_forall_isEquivalence_map_evalAt _).2 fun x ↦ ?_
    rw [← Edge.isEquivalence_map_iff_of_rightFibration p.hom]
    refine (Edge.isEquivalence_iff_of_edge_eq ?_).1 (Edge.isEquivalence_id (p.hom.app _ x))
    rw [Edge.id_edge, σ_zero_eq_yonedaEquiv_const]
    simp [← yonedaEquiv_comp, hH]
  -- The identities and composites of `1`-morphisms in the bicategory of quasicategories are those
  -- of the full subcategory `QCat` of `SSet` only up to unfolding, so `simp` does not see them:
  -- the maps underlying `𝟙 X` and `p ≫ s` are `𝟙 X.obj` and `p.hom ≫ section_ p.hom` by `rfl`.
  obtain ⟨η⟩ := nonempty_iso_of_isEquivalence (f := 𝟙 X) (g := p ≫ s)
    ((Edge.isEquivalence_ofEq_iff (e := (ihomEdgeEquiv _ _).symm H) rfl rfl).2 hα)
  have hε : s ≫ p = 𝟙 Y := by
    -- As above, the map underlying `s ≫ p` is `section_ p.hom ≫ p.hom` by definition.
    ext : 1
    exact hs
  exact (isCategoricalEquivalence_iff_exists_equivalence p).2
    ⟨.mkOfAdjointifyCounit η (eqToIso hε), rfl⟩

end QCat

end SSet
