/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.BaseChangeSection
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Functor
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Section
public import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
public import TauCeti.AlgebraicGeometry.IdealSheaf.Section

/-!
# Graphs of points as relative effective Cartier divisors

Let `f : X ⟶ S` be a separated morphism of schemes. A `T`-point `x : T ⟶ X` of `X` over `S` has a
graph `Γₓ : T ⟶ X_T = T ×_S X` (`TauCeti.AlgebraicGeometry.graphSection`), a section of the
projection `X_T ⟶ T` and hence a closed immersion. Its ideal sheaf commutes with base change along
morphisms `T' ⟶ T` over `S`. When `f` is moreover smooth of relative dimension one, the graph is a
relative effective Cartier divisor on `X_T` over `T`
(`Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension`).

Together these make the graph a natural transformation `graphDivisor` from the functor of points
`T ↦ Hom_S(T, X)` of `X` to the functor `Div_{X/S}` of relative effective Cartier divisors. It is
injective at every `T`, since a point is determined by its graph, and a section of a separated
morphism by its ideal sheaf.
Composed with the Abel map `D ↦ 𝒪(D)` it gives the degree-one Abel map `x ↦ 𝒪(Γₓ)` into the
relative Picard presheaf, from which `TauCeti.AlgebraicGeometry.abelJacobiMap` is built.

## Main declarations

* `TauCeti.AlgebraicGeometry.ker_graphSection_comp`: the ideal sheaf of the graph commutes with
  base change;
* `TauCeti.AlgebraicGeometry.ker_graphSection_inj`: a point is determined by the ideal sheaf of
  its graph;
* `TauCeti.AlgebraicGeometry.graphDivisor`: the natural transformation `Hom_S(-, X) ⟶ Div_{X/S}`
  sending a point to its graph;
* `TauCeti.AlgebraicGeometry.graphDivisor_app_injective`: distinct points have distinct graph
  divisors.

## References

* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.3.
* The Stacks Project, *Picard Schemes of Curves*, section *Moduli of divisors on smooth curves*.
-/

public section

open CategoryTheory Limits

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} {f : X ⟶ S}

/-- The graph of a `T`-point of a separated morphism is a closed immersion. -/
instance [IsSeparated f] {T : Over S} (x : T ⟶ Over.mk f) :
    IsClosedImmersion (graphSection x) :=
  (graphSection x).isClosedImmersion_of_comp_eq_id (graphSection_fst x)

/-- **The ideal sheaf of a graph commutes with base change.** For a separated morphism `f`, the
ideal sheaf of the graph of the base change `φ ≫ x` of a `T`-point `x` along `φ : T' ⟶ T` is the
inverse image of the ideal sheaf of the graph of `x` along `T' ×_S X ⟶ T ×_S X`. -/
lemma ker_graphSection_comp [IsSeparated f] {T' T : Over S} (φ : T' ⟶ T) (x : T ⟶ Over.mk f) :
    (graphSection (φ ≫ x)).ker = (graphSection x).ker.comap ((Over.pullback f).map φ).left :=
  Scheme.IdealSheafData.ker_eq_comap_of_isPullback _ (isPullback_graphSection φ x)

/-- **A point is determined by the ideal sheaf of its graph**: for a separated `f`, two
`T`-points of `X` over `S` are equal exactly when their graphs have the same ideal sheaf. -/
@[simp]
lemma ker_graphSection_inj [IsSeparated f] {T : Over S} {x y : T ⟶ Over.mk f} :
    (graphSection x).ker = (graphSection y).ker ↔ x = y := by
  rw [Scheme.Hom.ker_eq_ker_iff_of_comp_eq_id _ _ (graphSection_fst x) (graphSection_fst y)]
  refine ⟨fun h ↦ Over.OverMorphism.ext ?_, fun h ↦ h ▸ rfl⟩
  rw [← graphSection_snd x, ← graphSection_snd y, h]

variable [IsSeparated f] [SmoothOfRelativeDimension 1 f]

/-- The graph of a `T`-point of a separated morphism which is smooth of relative dimension one is
a relative effective Cartier divisor on `X_T` over `T`. -/
lemma ker_graphSection_mem_relativeEffectiveCartierSubfunctor_obj {T : Over S}
    (x : T ⟶ Over.mk f) :
    (graphSection x).ker ∈ (relativeEffectiveCartierSubfunctor f).obj (Opposite.op T) :=
  (mem_relativeEffectiveCartierSubfunctor_obj_iff f).mpr
    (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension _ (graphSection_fst x))

variable (f) in
/-- The **graph divisor**: for a separated morphism `f : X ⟶ S` which is smooth of relative
dimension one, the natural transformation from the functor of points `T ↦ Hom_S(T, X)` of `X` to
the functor `Div_{X/S}` of relative effective Cartier divisors, sending a `T`-point `x` to its
graph `Γₓ ⊆ X_T`. -/
def graphDivisor : yoneda.obj (Over.mk f) ⟶ (relativeEffectiveCartierSubfunctor f).toFunctor where
  app T := TypeCat.ofHom fun x ↦
    ⟨(graphSection x).ker, ker_graphSection_mem_relativeEffectiveCartierSubfunctor_obj x⟩
  naturality T T' φ := by
    ext x
    exact Subtype.ext (ker_graphSection_comp φ.unop x)

-- The source and target of `(graphDivisor f).app T` are spelled out in their simp-normal form
-- (without `yoneda_obj_obj` and `Subfunctor.toFunctor_obj`), so that the left-hand side passes
-- the `simpNF` linter.
/-- The ideal sheaf of the graph divisor of `x` is the ideal sheaf of the graph of `x`. -/
@[simp]
lemma graphDivisor_app_apply_val {T : (Over S)ᵒᵖ} (x : T.unop ⟶ Over.mk f) :
    (ConcreteCategory.hom (C := Type u) (X := T.unop ⟶ Over.mk f)
      (Y := (relativeEffectiveCartierSubfunctor f).obj T) ((graphDivisor f).app T) x).1 =
      (graphSection x).ker :=
  (rfl)

/-- The graph divisor of the base change `φ ≫ x` of a `T`-point `x` along `φ : T' ⟶ T` is the
pullback of the graph divisor of `x`. -/
lemma graphDivisor_app_comp {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T') (x : T.unop ⟶ Over.mk f) :
    (graphDivisor f).app T' (φ.unop ≫ x) =
      (relativeEffectiveCartierSubfunctor f).toFunctor.map φ ((graphDivisor f).app T x) :=
  Subtype.ext (ker_graphSection_comp φ.unop x)

/-- **Distinct points have distinct graph divisors**: for every scheme `T` over `S`, the graph
divisor is injective on `T`-points. -/
lemma graphDivisor_app_injective (T : (Over S)ᵒᵖ) :
    Function.Injective ((graphDivisor f).app T) :=
  fun _ _ h ↦ ker_graphSection_inj.mp (congrArg Subtype.val h)

end

end AlgebraicGeometry

end TauCeti
