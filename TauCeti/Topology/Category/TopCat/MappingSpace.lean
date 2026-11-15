/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.Topology.CompactOpen

/-!
# Locally compact spaces are exponentiable in `TopCat`

For a locally compact space `Y`, currying identifies continuous maps `Y × X → Z` with continuous
maps `X → C(Y, Z)`, where `C(Y, Z)` carries the compact-open topology. In categorical terms, the
functor `Y ⊗ -` on `TopCat` is left adjoint to the mapping space functor `C(Y, -)`, so `Y` is a
closed object of the cartesian monoidal category `TopCat`.

Since left adjoints preserve colimits, both `Y ⊗ -` and `- ⊗ Y` preserve all colimits in
`TopCat`. Concretely, if `c` is a colimit cocone over a diagram `F`, then `c.pt × Y` carries the
final topology for the maps `F.obj j × Y → c.pt × Y`, and a map out of `c.pt × Y` is continuous
as soon as all of its restrictions to the stages `F.obj j × Y` are. Taking `Y` to be the unit
interval, a homotopy on a colimit, for instance on the skeletal colimit realizing a simplicial
space, is continuous exactly when its restriction to each stage is. This is the comparison
`(colim X_n) × [0, 1] ≅ colim (X_n × [0, 1])` used to glue stagewise homotopies on such colimits.

Local compactness is used and not merely convenient: if `p : ℝ → X` collapses the positive
integers to a single point, then `p × id : ℝ × ℚ → X × ℚ` is not a quotient map, so `- × ℚ` does
not preserve the pushout defining `X`.

## Main declarations

* `TopCat.mappingSpace Y`: the functor `X ↦ C(Y, X)` on `TopCat`.
* `TopCat.curryEquiv`: for locally compact `Y`, the bijection between maps `Y ⊗ X ⟶ Z`
  and maps `X ⟶ C(Y, Z)`.
* `TopCat.closed`: a locally compact space is a closed object of `TopCat`, with internal
  hom `TopCat.mappingSpace Y`. Mathlib's adjunction and braided closed API then show that
  `tensorLeft Y` and `tensorRight Y` preserve colimits.
* `TopCat.continuous_iff_of_isColimit_prod`: a map out of `c.pt × Y` is continuous if and
  only if its restrictions to all `F.obj j × Y` are.

## References

* R. H. Fox, *On topologies for function spaces*, Bull. Amer. Math. Soc. 51 (1945), 429–432, for
  the exponential law for locally compact spaces.
* J. H. C. Whitehead, *Note on a theorem due to Borsuk*, Bull. Amer. Math. Soc. 54 (1948),
  1125–1132, for the lemma that the product of a quotient map with a locally compact space is a
  quotient map.
* J. R. Munkres, *Topology*, second edition, Prentice Hall, 2000, Section 22, Example 7, for the
  failure of this lemma without local compactness.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe w w' u v

namespace TopCat

/-- The mapping space functor `X ↦ C(Y, X)` on `TopCat`, where `C(Y, X)` carries the
compact-open topology and a map acts by postcomposition. -/
@[expose, simps! obj map_hom_apply]
def mappingSpace (Y : TopCat.{u}) : TopCat.{u} ⥤ TopCat.{u} where
  obj X := TopCat.of C(Y, X)
  map f := TopCat.ofHom ⟨f.hom.comp, ContinuousMap.continuous_postcomp f.hom⟩

variable (Y : TopCat.{u}) [LocallyCompactSpace Y]

/-- Currying: for a locally compact space `Y`, continuous maps `Y × X → Z` correspond to
continuous maps from `X` to the mapping space `C(Y, Z)`. -/
def curryEquiv (X Z : TopCat.{u}) : (Y ⊗ X ⟶ Z) ≃ (X ⟶ TopCat.of C(Y, Z)) where
  toFun f := TopCat.ofHom (ContinuousMap.curry ((β_ X Y).hom ≫ f).hom)
  invFun g := (β_ Y X).hom ≫ TopCat.ofHom (ContinuousMap.uncurry g.hom)
  left_inv _ := rfl
  right_inv _ := rfl

/- The two evaluation lemmas below are not `simp` lemmas: their left-hand sides apply a morphism
into `TopCat.of C(Y, Z)` and a morphism out of `Y ⊗ X`, whose carriers agree with `C(Y, Z)` and
`Y × X` only up to unfolding, so `simp` cannot match them against the terms it produces. -/

/-- The curried form of `f : Y ⊗ X ⟶ Z` sends `x` to `y ↦ f (y, x)`. -/
theorem curryEquiv_apply_hom_apply_apply {X Z : TopCat.{u}} (f : Y ⊗ X ⟶ Z) (x : X) (y : Y) :
    (curryEquiv Y X Z f).hom x y = f.hom (y, x) :=
  (rfl)

/-- The uncurried form of `g : X ⟶ C(Y, Z)` sends `(y, x)` to `g x y`. -/
theorem curryEquiv_symm_apply_hom_apply {X Z : TopCat.{u}} (g : X ⟶ TopCat.of C(Y, Z))
    (p : ↑(Y ⊗ X)) : ((curryEquiv Y X Z).symm g).hom p = g.hom p.2 p.1 :=
  (rfl)

/-- For a locally compact space `Y`, the functor `Y ⊗ -` on `TopCat` is left adjoint to the
mapping space functor `C(Y, -)`. -/
def tensorLeftAdjunction : tensorLeft Y ⊣ mappingSpace Y :=
  Adjunction.mkOfHomEquiv
    { homEquiv := curryEquiv Y
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }

/-- The hom-set bijection of `TopCat.tensorLeftAdjunction` is currying. -/
theorem tensorLeftAdjunction_homEquiv_apply {X Z : TopCat.{u}} (f : Y ⊗ X ⟶ Z) :
    (tensorLeftAdjunction Y).homEquiv X Z f = curryEquiv Y X Z f :=
  (rfl)

/-- The inverse hom-set bijection of `TopCat.tensorLeftAdjunction` is uncurrying. -/
theorem tensorLeftAdjunction_homEquiv_symm_apply {X Z : TopCat.{u}}
    (g : X ⟶ (mappingSpace Y).obj Z) :
    ((tensorLeftAdjunction Y).homEquiv X Z).symm g = (curryEquiv Y X Z).symm g :=
  (rfl)

/-- A locally compact space is a closed object of the cartesian monoidal category `TopCat`: its
internal hom is the mapping space with the compact-open topology. -/
instance closed : Closed Y :=
  ⟨mappingSpace Y, tensorLeftAdjunction Y⟩

variable {J : Type w} [Category.{w'} J] {F : J ⥤ TopCat.{u}} {c : Cocone F}

/-- For a colimit cocone `c` in `TopCat` and a locally compact space `Y`, a map out of
`c.pt × Y` is continuous if and only if its restriction to every stage `F.obj j × Y` is. -/
theorem continuous_iff_of_isColimit_prod (hc : IsColimit c) {Z : Type v} [TopologicalSpace Z]
    (f : c.pt × Y → Z) :
    Continuous f ↔ ∀ j, Continuous fun p : F.obj j × Y ↦ f (c.ι.app j p.1, p.2) :=
  TopCat.continuous_iff_of_isColimit _ (isColimitOfPreserves (tensorRight Y) hc) f

end TopCat
