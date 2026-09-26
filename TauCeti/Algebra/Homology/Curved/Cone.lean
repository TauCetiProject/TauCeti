/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.Algebra.Homology.Curved.Duplex

/-!
# The mapping cone of a morphism of curved duplexes

Let `C` be an `R`-linear category with binary biproducts and let `f : X ⟶ Y` be a morphism of
curved duplexes of curvature `w`. The **mapping cone** of `f` adds the components of the parity
shift of `X` to those of `Y`,
```
cone(f)₀ = X₁ ⊞ Y₀,    cone(f)₁ = X₀ ⊞ Y₁,
```
with the differential `[[-d_X, 0], [f, d_Y]]`. Both of its composites are again multiplication by
`w`: the diagonal entries contribute the curvature of `X` and of `Y`, and the off-diagonal entry
cancels because `f` commutes with the differentials. The cone therefore stays inside the curved
duplexes of the *same* curvature, which is what makes it available as the cofibre operation of
their homotopy category. A curved duplex is a two-periodic complex only when `w = 0`, so for
nonzero curvature the cone is not an instance of Mathlib's
`HomologicalComplex.homotopyCofiber`; and since a curved duplex has no homology when `w ≠ 0`, it
is cones and homotopies rather than quasi-isomorphisms that carry the weak-equivalence theory.

The cone comes with the closed morphisms `Y ⟶ cone f` and `cone f ⟶ X[1]` given by the biproduct
inclusion and projection, so that on components `cone f` is a split extension of the parity shift
of `X` by `Y`. Two homotopy-theoretic facts make it a cofibre: the composite `X ⟶ Y ⟶ cone f` is
null-homotopic, and the cone of an isomorphism is contractible.

Since the parity shift is the only shift available on curved duplexes, the compatibility of the
cone with it is recorded here: the two constructions agree up to the sign on the summand coming
from the target of `f`.

## Main definitions

* `TauCeti.CurvedDuplex.mappingCone`: the mapping cone of a morphism of curved duplexes.
* `TauCeti.CurvedDuplex.mappingCone.inr`: the inclusion `Y ⟶ cone f`.
* `TauCeti.CurvedDuplex.mappingCone.fst`: the projection `cone f ⟶ X[1]`.
* `TauCeti.CurvedDuplex.mappingCone.map`: the morphism of cones induced by a commutative square.
* `TauCeti.CurvedDuplex.mappingCone.parityShiftIso`: the parity shift of `cone f` is the cone of
  the parity shift of `f`.

## Main results

* `TauCeti.CurvedDuplex.mappingCone.comp_inr`: the composite `X ⟶ Y ⟶ cone f` is the
  null-homotopic morphism of the odd map given by the two biproduct inclusions, hence vanishes in
  the homotopy category.
* `TauCeti.CurvedDuplex.isZero_quotientFunctor_obj_mappingCone_of_isIso`: the cone of an
  isomorphism is contractible.

## References

* I. Frenkel, M. Khovanov, O. Schiffmann, *Homological realization of Nakajima varieties and Weyl
  group actions*, Compos. Math. **141** (2005), 1479–1503, Sections 2–3 (curved complexes,
  duplexes, and their homotopy categories).
* The sign conventions and the names `inr` and `fst` follow Joël Riou's mapping cone of cochain
  complexes in `Mathlib.Algebra.Homology.HomotopyCategory.MappingCone`.
-/

public section

universe w' v u

namespace TauCeti

open CategoryTheory Category Limits Preadditive

namespace CurvedDuplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {R : Type w'} [Semiring R] [Linear R C] {w : R} {X Y : CurvedDuplex C w}

attribute [local simp] Hom.comm₀ Hom.comm₁ Hom.comm₀_assoc Hom.comm₁_assoc

-- The cone is exposed, unlike the morphisms and the isomorphism below: its components must unfold
-- to biproducts for a consumer to define a morphism into or out of it by giving biproduct data.
/-- The **mapping cone** of a morphism `f : X ⟶ Y` of curved duplexes: its components are
`X₁ ⊞ Y₀` and `X₀ ⊞ Y₁`, and its differential is `[[-d_X, 0], [f, d_Y]]`. -/
@[expose, implicit_reducible, simps]
noncomputable def mappingCone (f : X ⟶ Y) : CurvedDuplex C w where
  X₀ := X.X₁ ⊞ Y.X₀
  X₁ := X.X₀ ⊞ Y.X₁
  d₀ := biprod.lift (-(biprod.fst ≫ X.d₁)) (biprod.fst ≫ f.f₁ + biprod.snd ≫ Y.d₀)
  d₁ := biprod.lift (-(biprod.fst ≫ X.d₀)) (biprod.fst ≫ f.f₀ + biprod.snd ≫ Y.d₁)
  d₀_comp_d₁ := by refine biprod.hom_ext _ _ ?_ ?_ <;> simp
  d₁_comp_d₀ := by refine biprod.hom_ext _ _ ?_ ?_ <;> simp

namespace mappingCone

/-- The inclusion `Y ⟶ cone f` of the target of `f` into its mapping cone, given on components by
the biproduct inclusion. -/
noncomputable def inr (f : X ⟶ Y) : Y ⟶ mappingCone f where
  f₀ := biprod.inr
  f₁ := biprod.inr
  comm₀ := by refine biprod.hom_ext _ _ ?_ ?_ <;> simp
  comm₁ := by refine biprod.hom_ext _ _ ?_ ?_ <;> simp

@[simp]
theorem inr_f₀ (f : X ⟶ Y) : (inr f).f₀ = biprod.inr := by unfold inr; rfl

@[simp]
theorem inr_f₁ (f : X ⟶ Y) : (inr f).f₁ = biprod.inr := by unfold inr; rfl

/-- The projection `cone f ⟶ X[1]` of the mapping cone onto the parity shift of the source of
`f`, given on components by the biproduct projection. -/
noncomputable def fst (f : X ⟶ Y) : mappingCone f ⟶ (parityShift C w).obj X where
  f₀ := biprod.fst
  f₁ := biprod.fst
  comm₀ := by simp
  comm₁ := by simp

@[simp]
theorem fst_f₀ (f : X ⟶ Y) : (fst f).f₀ = biprod.fst := by unfold fst; rfl

@[simp]
theorem fst_f₁ (f : X ⟶ Y) : (fst f).f₁ = biprod.fst := by unfold fst; rfl

/-- The two closed morphisms of the mapping cone compose to zero: on components they are the
inclusion and the projection of a biproduct. -/
@[reassoc (attr := simp), simp]
theorem inr_fst (f : X ⟶ Y) : inr f ≫ fst f = 0 := by
  ext <;> simp

section Functoriality

variable {X' Y' : CurvedDuplex C w} {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- The morphism of mapping cones induced by a commutative square `f ≫ b = a ≫ f'`: on components
it is the biproduct of the parity shift of `a` with `b`. -/
noncomputable def map (a : X ⟶ X') (b : Y ⟶ Y') (comm : f ≫ b = a ≫ f') :
    mappingCone f ⟶ mappingCone f' where
  f₀ := biprod.map a.f₁ b.f₀
  f₁ := biprod.map a.f₀ b.f₁
  comm₀ := by
    have h₁ : f.f₁ ≫ b.f₁ = a.f₁ ≫ f'.f₁ := by simpa using congrArg Hom.f₁ comm
    refine biprod.hom_ext _ _ ?_ ?_ <;> simp [h₁]
  comm₁ := by
    have h₀ : f.f₀ ≫ b.f₀ = a.f₀ ≫ f'.f₀ := by simpa using congrArg Hom.f₀ comm
    refine biprod.hom_ext _ _ ?_ ?_ <;> simp [h₀]

@[simp]
theorem map_f₀ (a : X ⟶ X') (b : Y ⟶ Y') (comm : f ≫ b = a ≫ f') :
    (map a b comm).f₀ = biprod.map a.f₁ b.f₀ := by unfold map; rfl

@[simp]
theorem map_f₁ (a : X ⟶ X') (b : Y ⟶ Y') (comm : f ≫ b = a ≫ f') :
    (map a b comm).f₁ = biprod.map a.f₀ b.f₁ := by unfold map; rfl

/-- The morphism of cones restricts to `b` on the inclusions of the targets. -/
@[reassoc (attr := simp), simp]
theorem inr_map (a : X ⟶ X') (b : Y ⟶ Y') (comm : f ≫ b = a ≫ f') :
    inr f ≫ map a b comm = b ≫ inr f' := by
  ext <;> simp

/-- The morphism of cones covers the parity shift of `a` on the projections to the shifted
sources. -/
@[reassoc (attr := simp), simp]
theorem map_fst (a : X ⟶ X') (b : Y ⟶ Y') (comm : f ≫ b = a ≫ f') :
    map a b comm ≫ fst f' = fst f ≫ (parityShift C w).map a := by
  ext <;> simp

/-- The morphism of cones induced by the identity square is the identity. -/
@[simp]
theorem map_id : map (f := f) (f' := f) (𝟙 X) (𝟙 Y) (by simp) = 𝟙 (mappingCone f) := by
  ext <;> refine biprod.hom_ext _ _ ?_ ?_ <;> simp

/-- The morphism of cones induced by a horizontal composite of squares is the composite of the
morphisms of cones. -/
theorem map_comp {X'' Y'' : CurvedDuplex C w} {f'' : X'' ⟶ Y''} (a : X ⟶ X') (b : Y ⟶ Y')
    (comm : f ≫ b = a ≫ f') (a' : X' ⟶ X'') (b' : Y' ⟶ Y'') (comm' : f' ≫ b' = a' ≫ f'') :
    map a b comm ≫ map a' b' comm' =
      map (a ≫ a') (b ≫ b') (by rw [← assoc, comm, assoc, comm', assoc]) := by
  ext <;> refine biprod.hom_ext _ _ ?_ ?_ <;> simp

/-- A square whose two vertical maps are isomorphisms induces an isomorphism of mapping cones. -/
instance isIso_map (a : X ⟶ X') (b : Y ⟶ Y') (comm : f ≫ b = a ≫ f') [IsIso a] [IsIso b] :
    IsIso (map a b comm) := by
  refine (isIso_iff _).2 ⟨?_, ?_⟩
  · rw [map_f₀]
    exact (biprod.mapIso (asIso a.f₁) (asIso b.f₀)).isIso_hom
  · rw [map_f₁]
    exact (biprod.mapIso (asIso a.f₀) (asIso b.f₁)).isIso_hom

end Functoriality

/-- The composite `X ⟶ Y ⟶ cone f` is the null-homotopic morphism of the odd map given by the two
biproduct inclusions. -/
theorem comp_inr (f : X ⟶ Y) : f ≫ inr f = nullHomotopicMap biprod.inl biprod.inl := by
  ext <;> refine biprod.hom_ext _ _ ?_ ?_ <;> simp

/-- The composite `X ⟶ Y ⟶ cone f` vanishes in the homotopy category. -/
@[simp]
theorem quotientFunctor_map_comp_inr (f : X ⟶ Y) :
    (nullHomotopic C w).quotientFunctor.map f ≫
      (nullHomotopic C w).quotientFunctor.map (inr f) = 0 := by
  rw [← Functor.map_comp, MorphismIdeal.quotientFunctor_map_eq_zero_iff, mem_nullHomotopic_iff]
  exact ⟨_, _, (comp_inr f).symm⟩

/-- The parity shift of the mapping cone of `f` is the mapping cone of the parity shift of `f`.
Both curved duplexes have the same components; the isomorphism negates the summand coming from
the target of `f`, where the sign of the parity shift and the sign of the cone differ. -/
noncomputable def parityShiftIso (f : X ⟶ Y) :
    (parityShift C w).obj (mappingCone f) ≅ mappingCone ((parityShift C w).map f) where
  hom := homMk (biprod.map (𝟙 _) (-𝟙 _)) (biprod.map (𝟙 _) (-𝟙 _))
    (by refine biprod.hom_ext _ _ ?_ ?_ <;> simp)
    (by refine biprod.hom_ext _ _ ?_ ?_ <;> simp)
  inv := homMk (biprod.map (𝟙 _) (-𝟙 _)) (biprod.map (𝟙 _) (-𝟙 _))
    (by refine biprod.hom_ext _ _ ?_ ?_ <;> simp)
    (by refine biprod.hom_ext _ _ ?_ ?_ <;> simp)
  hom_inv_id := by ext <;> refine biprod.hom_ext _ _ ?_ ?_ <;> simp
  inv_hom_id := by ext <;> refine biprod.hom_ext _ _ ?_ ?_ <;> simp

@[simp]
theorem parityShiftIso_hom_f₀ (f : X ⟶ Y) :
    (parityShiftIso f).hom.f₀ = biprod.map (𝟙 X.X₀) (-𝟙 Y.X₁) := by
  unfold parityShiftIso; rfl

@[simp]
theorem parityShiftIso_hom_f₁ (f : X ⟶ Y) :
    (parityShiftIso f).hom.f₁ = biprod.map (𝟙 X.X₁) (-𝟙 Y.X₀) := by
  unfold parityShiftIso; rfl

@[simp]
theorem parityShiftIso_inv_f₀ (f : X ⟶ Y) :
    (parityShiftIso f).inv.f₀ = biprod.map (𝟙 X.X₀) (-𝟙 Y.X₁) := by
  unfold parityShiftIso; rfl

@[simp]
theorem parityShiftIso_inv_f₁ (f : X ⟶ Y) :
    (parityShiftIso f).inv.f₁ = biprod.map (𝟙 X.X₁) (-𝟙 Y.X₀) := by
  unfold parityShiftIso; rfl

end mappingCone

/-- The identity of the mapping cone of an identity morphism is null-homotopic: it is `d h + h d`
for the odd map which includes the summand coming from the target into the one coming from the
source. -/
theorem nullHomotopicMap_mappingCone_id (X : CurvedDuplex C w) :
    nullHomotopicMap (X := mappingCone (𝟙 X)) (Y := mappingCone (𝟙 X))
        (biprod.snd ≫ biprod.inl) (biprod.snd ≫ biprod.inl) =
      𝟙 (mappingCone (𝟙 X)) := by
  ext <;> refine biprod.hom_ext _ _ ?_ ?_ <;> simp

/-- The mapping cone of an identity morphism is contractible, hence a zero object of the homotopy
category. -/
theorem isZero_quotientFunctor_obj_mappingCone_id (X : CurvedDuplex C w) :
    IsZero ((nullHomotopic C w).quotientFunctor.obj (mappingCone (𝟙 X))) := by
  rw [MorphismIdeal.isZero_quotientFunctor_obj_iff, mem_nullHomotopic_iff]
  exact ⟨_, _, nullHomotopicMap_mappingCone_id X⟩

/-- The mapping cone of an isomorphism is contractible, hence a zero object of the homotopy
category. -/
theorem isZero_quotientFunctor_obj_mappingCone_of_isIso (f : X ⟶ Y) [IsIso f] :
    IsZero ((nullHomotopic C w).quotientFunctor.obj (mappingCone f)) :=
  (isZero_quotientFunctor_obj_mappingCone_id Y).of_iso
    ((nullHomotopic C w).quotientFunctor.mapIso (asIso (mappingCone.map f (𝟙 Y) (by simp))))

end CurvedDuplex

end TauCeti
