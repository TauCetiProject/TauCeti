/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import TauCeti.Algebra.Category.ModuleCat.Tower.Exact

/-!
# Derived limits of towers of complexes of modules

Let `K` be a cochain complex of towers of `R`-modules, an object of
`CochainComplex (ℕᵒᵖ ⥤ ModuleCat R) ℤ`. Its product complex `∏ₙ Kₙ` carries the shift chain
map `δ(x)ₙ = xₙ - φₙ(xₙ₊₁)`, and the *homotopy limit* `holim K` is the mapping cocone
`Cone(δ)[-1]` of `δ`. This file shows that `holim` is a functor sending quasi-isomorphisms of
complexes of towers to quasi-isomorphisms, so that it descends to the **derived limit functor**
`Rlim : D(ℕᵒᵖ ⥤ ModuleCat R) ⥤ D(R)` between derived categories, computed on every complex of
towers by its homotopy limit. By construction `holim K` sits in the fibre triangle
`holim K → ∏ₙ Kₙ → ∏ₙ Kₙ → (holim K)[1]` of `δ`, which is distinguished in `D(R)`; consequently
the projections `Rlim K → Kₙ` are compatible with the transition maps `Kₙ₊₁ → Kₙ` in `D(R)`,
although the corresponding maps of complexes are only compatible up to homotopy.

The key input is that products of modules are exact: the product functor `A ↦ ∏ₙ Aₙ` on towers
preserves homology, hence quasi-isomorphisms of complexes, and a commutative square of
quasi-isomorphisms induces a quasi-isomorphism of mapping cones.

Here a complex of towers is a cochain complex in the functor category `ℕᵒᵖ ⥤ ModuleCat R`, the
setting of the derived category of towers. The product complex of `TauCeti.ComplexTower`, for
towers of complexes `ℕᵒᵖ ⥤ CochainComplex (ModuleCat R) ℤ`, has the same terms and
differentials; the functorial form `ModuleTower.productComplexFunctor` is the one compatible
with localization.

## Main declarations

* `TauCeti.ModuleTower.productFunctor`: the product functor `A ↦ ∏ₙ Aₙ` on towers, which
  preserves homology (`TauCeti.ModuleTower.exact_map_productFunctor`).
* `TauCeti.ModuleTower.shiftNatTrans`, `TauCeti.ModuleTower.complexShift`: the shift maps `δ`, as
  natural endomorphisms of the product functor and of the product complex functor.
* `TauCeti.ModuleTower.homotopyLimitFunctor`: the homotopy limit `Cone(δ)[-1]`, which preserves
  quasi-isomorphisms (`TauCeti.ModuleTower.quasiIso_homotopyLimitFunctor_map`).
* `TauCeti.ModuleTower.homotopyLimitTriangle`: the fibre triangle of `δ`, distinguished in the
  derived category (`TauCeti.ModuleTower.homotopyLimitTriangle_distinguished`).
* `TauCeti.ModuleTower.derivedLimit`: the derived limit functor `Rlim`, with
  `TauCeti.ModuleTower.derivedLimitFactors : Q ⋙ Rlim ≅ holim ⋙ Q`.
* `TauCeti.ModuleTower.derivedLimitπ`: the projections `Rlim K → Kₙ`, compatible with the
  transitions (`TauCeti.ModuleTower.derivedLimitπ_comp_transition`).

## References

* [Stacks: More on Algebra, Lemma 15.87.1, Tag 0919](https://stacks.math.columbia.edu/tag/0919)
* [Stacks, Tag 091D](https://stacks.math.columbia.edu/tag/091D) (derived limits of inverse
  systems as fibres of `1 - shift` on products)
* M. Bökstedt and A. Neeman, *Homotopy limits in triangulated categories*, Compositio Math. 86
  (1993), 209–234.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory Opposite CochainComplex

universe w w' v u

namespace ModuleTower

variable (R : Type u) [Ring R]

section Product

/-- The product functor `A ↦ ∏ₙ Aₙ` on towers of `R`-modules. -/
@[expose, simps]
def productFunctor : ModuleTower.{v} R ⥤ ModuleCat.{v} R where
  obj F := ModuleCat.of R F.Product
  map f := ModuleCat.ofHom (productMap f)
  map_id F := by
    ext1
    exact productMap_id
  map_comp f g := by
    ext1
    exact productMap_comp f g

instance : (productFunctor.{v} R).Additive where
  map_add {_ _ f g} := by
    ext1
    exact productMap_add f g

variable {R} in
/-- The product functor is exact: it sends exact short complexes of towers to exact short
complexes of modules. -/
theorem exact_map_productFunctor {S : ShortComplex (ModuleTower.{v} R)} (hS : S.Exact) :
    (S.map (productFunctor R)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact exact_productMap fun n ↦
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.map ((evaluation ℕᵒᵖ (ModuleCat.{v} R)).obj (op n)))

instance : (productFunctor.{v} R).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ fun _ hS ↦ exact_map_productFunctor hS

/-- The shift maps `δ(x)ₙ = xₙ - φₙ(xₙ₊₁)`, as a natural endomorphism of the product functor. -/
@[expose, simps]
def shiftNatTrans : productFunctor.{v} R ⟶ productFunctor.{v} R where
  app F := ModuleCat.ofHom F.shift
  naturality _ _ f := by
    ext1
    exact shift_natural f

/-- The projection `∏ₖ Aₖ → Aₙ`, as a natural transformation from the product functor to the
evaluation at `n`. -/
@[expose, simps]
def productπ (n : ℕ) :
    productFunctor.{v} R ⟶ (evaluation ℕᵒᵖ (ModuleCat.{v} R)).obj (op n) where
  app F := ModuleCat.ofHom (LinearMap.proj n)
  naturality _ _ f := by
    ext x : 2
    exact productMap_apply f x n

/-- The shift followed by the projection onto `Aₙ` is the projection onto `Aₙ` minus the
projection onto `Aₙ₊₁` followed by the transition `Aₙ₊₁ → Aₙ`. -/
theorem shiftNatTrans_comp_productπ (n : ℕ) :
    shiftNatTrans.{v} R ≫ productπ R n =
      productπ R n - productπ R (n + 1) ≫
        (evaluation ℕᵒᵖ (ModuleCat.{v} R)).map (homOfLE (Nat.le_succ n)).op := by
  ext F : 2
  ext x
  -- Both sides are `xₙ - φₙ(xₙ₊₁)`, by `shift_apply` and `transition_def`.
  exact (F.shift_apply x n).trans (by rw [transition_def]; rfl)

end Product

section Complexes

/-- The product complex `∏ₙ Kₙ` of a cochain complex of towers. -/
abbrev productComplexFunctor :
    CochainComplex (ModuleTower.{v} R) ℤ ⥤ CochainComplex (ModuleCat.{v} R) ℤ :=
  (productFunctor R).mapHomologicalComplex _

/-- The shift chain maps `δ : ∏ₙ Kₙ → ∏ₙ Kₙ`, natural in the complex of towers `K`. -/
def complexShift : productComplexFunctor.{v} R ⟶ productComplexFunctor.{v} R :=
  NatTrans.mapHomologicalComplex (shiftNatTrans R) _

@[simp]
theorem complexShift_app_f (K : CochainComplex (ModuleTower.{v} R) ℤ) (i : ℤ) :
    ((complexShift R).app K).f i = ModuleCat.ofHom (K.X i).shift :=
  (rfl)

variable {R}

/-- The product complex functor preserves quasi-isomorphisms, since products of modules are
exact. -/
instance quasiIso_productComplexFunctor_map {K L : CochainComplex (ModuleTower.{v} R) ℤ}
    (f : K ⟶ L) [QuasiIso f] : QuasiIso ((productComplexFunctor R).map f) :=
  HomologicalComplex.quasiIso_map_of_preservesHomology f _

variable (R)

/-- The homotopy limit `Cone(δ)[-1]` of a cochain complex of towers `K`: the mapping cocone of
the shift chain map `δ : ∏ₙ Kₙ → ∏ₙ Kₙ`. It computes the derived limit `Rlim K`. -/
@[expose]
def homotopyLimitFunctor :
    CochainComplex (ModuleTower.{v} R) ℤ ⥤ CochainComplex (ModuleCat.{v} R) ℤ where
  obj K := mappingCocone ((complexShift R).app K)
  map f := (mappingCone.map _ _ ((productComplexFunctor R).map f)
    ((productComplexFunctor R).map f) ((complexShift R).naturality f).symm)⟦(-1 : ℤ)⟧'
  map_id K := by
    have h : mappingCone.map _ _ ((productComplexFunctor R).map (𝟙 K))
        ((productComplexFunctor R).map (𝟙 K)) ((complexShift R).naturality (𝟙 K)).symm =
          𝟙 _ := by
      simp only [CategoryTheory.Functor.map_id]
      exact mappingCone.map_id _
    rw [h]
    exact CategoryTheory.Functor.map_id _ _
  map_comp f g := by
    have h : mappingCone.map _ _ ((productComplexFunctor R).map (f ≫ g))
        ((productComplexFunctor R).map (f ≫ g)) ((complexShift R).naturality (f ≫ g)).symm =
          mappingCone.map _ _ ((productComplexFunctor R).map f)
            ((productComplexFunctor R).map f) ((complexShift R).naturality f).symm ≫
          mappingCone.map _ _ ((productComplexFunctor R).map g)
            ((productComplexFunctor R).map g) ((complexShift R).naturality g).symm := by
      simp only [CategoryTheory.Functor.map_comp]
      exact mappingCone.map_comp _ _ _ _ _ _ _ _ _
    rw [h]
    exact CategoryTheory.Functor.map_comp _ _ _

theorem homotopyLimitFunctor_obj (K : CochainComplex (ModuleTower.{v} R) ℤ) :
    (homotopyLimitFunctor R).obj K = mappingCocone ((complexShift R).app K) :=
  (rfl)

theorem homotopyLimitFunctor_map {K L : CochainComplex (ModuleTower.{v} R) ℤ} (f : K ⟶ L) :
    (homotopyLimitFunctor R).map f = (mappingCone.map _ _ ((productComplexFunctor R).map f)
      ((productComplexFunctor R).map f) ((complexShift R).naturality f).symm)⟦(-1 : ℤ)⟧' :=
  (rfl)

variable {R}

/-- The map `holim K → ∏ₙ Kₙ` from the homotopy limit of a complex of towers to its product
complex. -/
def homotopyLimitFst (K : CochainComplex (ModuleTower.{v} R) ℤ) :
    (homotopyLimitFunctor R).obj K ⟶ (productComplexFunctor R).obj K :=
  mappingCocone.fst _

theorem homotopyLimitFst_def (K : CochainComplex (ModuleTower.{v} R) ℤ) :
    homotopyLimitFst K = mappingCocone.fst ((complexShift R).app K) :=
  (rfl)

/-- The fibre triangle `holim K → ∏ₙ Kₙ → ∏ₙ Kₙ → (holim K)[1]` of the shift chain map, the
mapping cocone triangle of `δ`. -/
@[expose, simps! obj₁ obj₂ obj₃ mor₁ mor₂ mor₃]
def homotopyLimitTriangle (K : CochainComplex (ModuleTower.{v} R) ℤ) :
    Pretriangulated.Triangle (CochainComplex (ModuleCat.{v} R) ℤ) :=
  Pretriangulated.Triangle.mk (homotopyLimitFst K) ((complexShift R).app K)
    (mappingCocone.triangle ((complexShift R).app K)).mor₃

/-- The fibre triangle of the shift becomes distinguished in the derived category. -/
theorem homotopyLimitTriangle_distinguished [HasDerivedCategory.{w'} (ModuleCat.{v} R)]
    (K : CochainComplex (ModuleTower.{v} R) ℤ) :
    DerivedCategory.Q.mapTriangle.obj (homotopyLimitTriangle K) ∈
      distTriang (DerivedCategory (ModuleCat.{v} R)) :=
  DerivedCategory.mappingCocone_triangle_distinguished _

/-- In the derived category, the map `holim K → ∏ₙ Kₙ` composes to zero with the shift. -/
@[reassoc (attr := simp)]
theorem Q_map_homotopyLimitFst_comp_Q_map_complexShift
    [HasDerivedCategory.{w'} (ModuleCat.{v} R)] (K : CochainComplex (ModuleTower.{v} R) ℤ) :
    DerivedCategory.Q.map (homotopyLimitFst K) ≫ DerivedCategory.Q.map ((complexShift R).app K) =
      0 :=
  Pretriangulated.comp_distTriang_mor_zero₁₂ _ (homotopyLimitTriangle_distinguished K)

/-- The homotopy limit sends quasi-isomorphisms of complexes of towers to quasi-isomorphisms. -/
instance quasiIso_homotopyLimitFunctor_map {K L : CochainComplex (ModuleTower.{v} R) ℤ}
    (f : K ⟶ L) [QuasiIso f] : QuasiIso ((homotopyLimitFunctor R).map f) := by
  let _ := HasDerivedCategory.standard (ModuleCat.{v} R)
  have comm := ((complexShift R).naturality f).symm
  -- The cone map is the third component of a morphism of distinguished mapping cone triangles
  -- whose first two components are quasi-isomorphisms.
  have : QuasiIso (mappingCone.map _ _ _ _ comm) := by
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact Pretriangulated.isIso₃_of_isIso₁₂
      (DerivedCategory.Q.mapTriangle.map (mappingCone.triangleMap _ _ _ _ comm))
      (DerivedCategory.mappingCone_triangle_distinguished _)
      (DerivedCategory.mappingCone_triangle_distinguished _)
      (inferInstanceAs (IsIso (DerivedCategory.Q.map ((productComplexFunctor R).map f))))
      (inferInstanceAs (IsIso (DerivedCategory.Q.map ((productComplexFunctor R).map f))))
  exact (quasiIso_shift_iff _ (-1)).2 this

variable (R)

/-- The homotopy limit inverts quasi-isomorphisms after localization. -/
theorem quasiIso_isInvertedBy_homotopyLimitFunctor_comp_Q
    [HasDerivedCategory.{w'} (ModuleCat.{v} R)] :
    (HomologicalComplex.quasiIso (ModuleTower.{v} R) (ComplexShape.up ℤ)).IsInvertedBy
      (homotopyLimitFunctor R ⋙ DerivedCategory.Q) := fun _ _ f hf ↦ by
  have : QuasiIso f := hf
  dsimp only [Functor.comp_map]
  infer_instance

end Complexes

section Derived

variable [HasDerivedCategory.{w} (ModuleTower.{v} R)] [HasDerivedCategory.{w'} (ModuleCat.{v} R)]

/-- The **derived limit** functor `Rlim : D(ℕᵒᵖ ⥤ ModuleCat R) ⥤ D(R)` on the derived category of
towers of `R`-modules, induced by the homotopy limit `Cone(δ)[-1]`
(`ModuleTower.derivedLimitFactors`). -/
def derivedLimit :
    DerivedCategory (ModuleTower.{v} R) ⥤ DerivedCategory (ModuleCat.{v} R) :=
  Localization.lift _ (quasiIso_isInvertedBy_homotopyLimitFunctor_comp_Q R)
    (DerivedCategory.Q (C := ModuleTower.{v} R))

@[no_expose]
instance : Localization.Lifting (DerivedCategory.Q (C := ModuleTower.{v} R))
    (HomologicalComplex.quasiIso (ModuleTower.{v} R) (ComplexShape.up ℤ))
    (homotopyLimitFunctor R ⋙ DerivedCategory.Q) (derivedLimit R) :=
  Localization.liftingLift _ (quasiIso_isInvertedBy_homotopyLimitFunctor_comp_Q R) _

/-- On a complex of towers, the derived limit is computed by the homotopy limit. -/
def derivedLimitFactors :
    DerivedCategory.Q ⋙ derivedLimit R ≅ homotopyLimitFunctor R ⋙ DerivedCategory.Q :=
  Localization.Lifting.iso (DerivedCategory.Q (C := ModuleTower.{v} R))
    (HomologicalComplex.quasiIso (ModuleTower.{v} R) (ComplexShape.up ℤ)) _ _

end Derived

section Projections

variable [HasDerivedCategory.{w} (ModuleTower.{v} R)] [HasDerivedCategory.{w'} (ModuleCat.{v} R)]
  {R}

/-- The projection `Rlim K → Kₙ` of the derived limit of a complex of towers onto its `n`-th
complex, induced by the projection `∏ₖ Kₖ → Kₙ`. -/
def derivedLimitπ (K : CochainComplex (ModuleTower.{v} R) ℤ) (n : ℕ) :
    (derivedLimit R).obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj
        ((((evaluation ℕᵒᵖ (ModuleCat.{v} R)).obj (op n)).mapHomologicalComplex _).obj K) :=
  (derivedLimitFactors R).hom.app K ≫ DerivedCategory.Q.map
    (homotopyLimitFst K ≫ (NatTrans.mapHomologicalComplex (productπ R n) _).app K)

/-- The projections of the derived limit are compatible with the transition maps
`Kₙ₊₁ → Kₙ` of the tower. -/
theorem derivedLimitπ_comp_transition (K : CochainComplex (ModuleTower.{v} R) ℤ) (n : ℕ) :
    derivedLimitπ K (n + 1) ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          ((evaluation ℕᵒᵖ (ModuleCat.{v} R)).map (homOfLE (Nat.le_succ n)).op) _).app K) =
      derivedLimitπ K n := by
  -- At the level of complexes, `πₙ₊₁ ≫ φₙ = πₙ - δ ≫ πₙ`.
  have h : (NatTrans.mapHomologicalComplex (productπ R (n + 1)) _).app K ≫
      (NatTrans.mapHomologicalComplex
        ((evaluation ℕᵒᵖ (ModuleCat.{v} R)).map (homOfLE (Nat.le_succ n)).op) _).app K =
        (NatTrans.mapHomologicalComplex (productπ R n) _).app K -
          (complexShift R).app K ≫ (NatTrans.mapHomologicalComplex (productπ R n) _).app K := by
    have h₀ := shiftNatTrans_comp_productπ R n
    rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq'] at h₀
    ext i : 1
    exact congr_app h₀ (K.X i)
  -- The correction term factors through `holim K → ∏ₙ Kₙ → ∏ₙ Kₙ`, which vanishes in `D(R)`.
  rw [derivedLimitπ, derivedLimitπ, Category.assoc, ← CategoryTheory.Functor.map_comp,
    Category.assoc, h]
  simp [Preadditive.comp_sub]

end Projections

end ModuleTower

end TauCeti
