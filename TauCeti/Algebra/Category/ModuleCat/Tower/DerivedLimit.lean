/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import TauCeti.Algebra.Category.ModuleCat.Tower.Product
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCocone

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

When every term of `K` is a tower with vanishing `lim¹`, for instance when all transitions are
surjective, the derived limit is the termwise limit complex `lim K`: the inclusion
`lim K → ∏ₙ Kₙ` lifts to a quasi-isomorphism `lim K → holim K`, because
`0 → lim K → ∏ₙ Kₙ → ∏ₙ Kₙ → 0` is then a short exact sequence of complexes. Under the resulting
isomorphism `Rlim K ≅ lim K` the projections of `Rlim K` are the projections of the limit.

The key input is that products of modules are exact: the product functor `A ↦ ∏ₙ Aₙ` on towers
(`TauCeti.ModuleTower.productFunctor`) preserves homology, hence quasi-isomorphisms of complexes,
and a commutative square of quasi-isomorphisms induces a quasi-isomorphism of mapping cones.

Here a complex of towers is a cochain complex in the functor category `ℕᵒᵖ ⥤ ModuleCat R`, the
setting of the derived category of towers. The product complex of `TauCeti.ComplexTower`, for
towers of complexes `ℕᵒᵖ ⥤ CochainComplex (ModuleCat R) ℤ`, has the same terms and
differentials; the functorial form `ModuleTower.productComplexFunctor` is the one compatible
with localization.

## Main declarations

* `TauCeti.ModuleTower.productComplexFunctor`: the product complex `∏ₙ Kₙ`, which preserves
  quasi-isomorphisms.
* `TauCeti.ModuleTower.complexShift`: the shift chain maps `δ`, as a natural endomorphism of the
  product complex functor.
* `TauCeti.ModuleTower.homotopyLimitFunctor`: the homotopy limit `Cone(δ)[-1]`, which preserves
  quasi-isomorphisms (`TauCeti.ModuleTower.quasiIso_homotopyLimitFunctor_map`).
* `TauCeti.ModuleTower.homotopyLimitTriangle`: the fibre triangle of `δ`, distinguished in the
  derived category (`TauCeti.ModuleTower.homotopyLimitTriangle_distinguished`).
* `TauCeti.ModuleTower.derivedLimit`: the derived limit functor `Rlim`, with
  `TauCeti.ModuleTower.derivedLimitFactors : Q ⋙ Rlim ≅ holim ⋙ Q`.
* `TauCeti.ModuleTower.derivedLimitπ`: the projections `Rlim K → Kₙ`, compatible with the
  transitions (`TauCeti.ModuleTower.derivedLimitπ_comp_transition`).
* `TauCeti.ModuleTower.homotopyLimitLift`: the natural comparison map `lim K → holim K`, whose
  projections are the inclusion of `lim K` and zero, a quasi-isomorphism when every term has
  vanishing `lim¹` (`TauCeti.ModuleTower.quasiIso_homotopyLimitLift`).
* `TauCeti.ModuleTower.derivedLimitIsoLimComplex`: the isomorphism `Rlim K ≅ lim K` in that case,
  compatible with the projections
  (`TauCeti.ModuleTower.derivedLimitIsoLimComplex_inv_comp_derivedLimitπ`).

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

/-- The map `holim K → ∏ₙ Kₙ` is natural in the complex of towers `K`. -/
@[reassoc]
theorem homotopyLimitFunctor_map_comp_homotopyLimitFst
    {K L : CochainComplex (ModuleTower.{v} R) ℤ} (f : K ⟶ L) :
    (homotopyLimitFunctor R).map f ≫ homotopyLimitFst L =
      homotopyLimitFst K ≫ (productComplexFunctor R).map f :=
  mappingCocone.shiftFunctor_map_mappingCone_map_comp_fst _ _ _ _ _

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

/-- The termwise limit `lim K` of a cochain complex of towers `K`. -/
abbrev limComplexFunctor :
    CochainComplex (ModuleTower.{v} R) ℤ ⥤ CochainComplex (ModuleCat.{v} R) ℤ :=
  (limFunctor R).mapHomologicalComplex _

/-- The inclusion `lim K → ∏ₙ Kₙ` of the termwise limit into the product complex. -/
def limComplexι : limComplexFunctor.{v} R ⟶ productComplexFunctor.{v} R :=
  NatTrans.mapHomologicalComplex (limι R) _

variable {R}

@[simp]
theorem limComplexι_app_f (K : CochainComplex (ModuleTower.{v} R) ℤ) (i : ℤ) :
    ((limComplexι R).app K).f i = (limι R).app (K.X i) :=
  (rfl)

/-- The termwise limit is killed by the shift: `lim K → ∏ₙ Kₙ → ∏ₙ Kₙ` vanishes. -/
@[reassoc (attr := simp)]
theorem limComplexι_app_comp_complexShift_app (K : CochainComplex (ModuleTower.{v} R) ℤ) :
    (limComplexι R).app K ≫ (complexShift R).app K = 0 := by
  ext i : 1
  exact limι_app_comp_shiftNatTrans_app R (K.X i)

/-- The comparison map `lim K → holim K` from the termwise limit of a complex of towers to its
homotopy limit, lifting the inclusion `lim K → ∏ₙ Kₙ` through the mapping cocone of `δ`. -/
def homotopyLimitLift (K : CochainComplex (ModuleTower.{v} R) ℤ) :
    (limComplexFunctor R).obj K ⟶ (homotopyLimitFunctor R).obj K :=
  mappingCocone.lift _ ((limComplexι R).app K) 0 (by simp)

/-- The comparison map `lim K → holim K` followed by `holim K → ∏ₙ Kₙ` is the inclusion of the
termwise limit. -/
@[reassoc (attr := simp)]
theorem homotopyLimitLift_comp_homotopyLimitFst (K : CochainComplex (ModuleTower.{v} R) ℤ) :
    homotopyLimitLift K ≫ homotopyLimitFst K = (limComplexι R).app K :=
  mappingCocone.lift_fst _ _ _ _

/-- The comparison map `lim K → holim K` has vanishing second component in the mapping cocone
of `δ`. -/
@[simp, reassoc]
theorem homotopyLimitLift_f_snd_v (K : CochainComplex (ModuleTower.{v} R) ℤ) (p q : ℤ)
    (hpq : p + -1 = q) :
    (homotopyLimitLift K).f p ≫ (mappingCocone.snd ((complexShift R).app K)).v p q hpq = 0 :=
  (mappingCocone.lift_f_snd_v _ _ _ _ p q hpq).trans (HomComplex.Cochain.zero_v ..)

/-- The comparison map `lim K → holim K` is natural in the complex of towers `K`. -/
@[reassoc]
theorem homotopyLimitLift_naturality {K L : CochainComplex (ModuleTower.{v} R) ℤ} (f : K ⟶ L) :
    (limComplexFunctor R).map f ≫ homotopyLimitLift L =
      homotopyLimitLift K ≫ (homotopyLimitFunctor R).map f := by
  -- Both sides are compared through the two projections of the mapping cocone.
  have hfst : (limComplexFunctor R).map f ≫ homotopyLimitLift L ≫ homotopyLimitFst L =
      homotopyLimitLift K ≫ (homotopyLimitFunctor R).map f ≫ homotopyLimitFst L := by
    rw [homotopyLimitLift_comp_homotopyLimitFst, homotopyLimitFunctor_map_comp_homotopyLimitFst,
      homotopyLimitLift_comp_homotopyLimitFst_assoc]
    exact (limComplexι R).naturality f
  have hsnd := mappingCocone.shiftFunctor_map_mappingCone_map_f_snd_v _ _
    ((productComplexFunctor R).map f) ((productComplexFunctor R).map f)
    ((complexShift R).naturality f).symm
  ext p : 1
  apply mappingCocone.ext_to _ p (p + -1) rfl
  · have h := HomologicalComplex.congr_hom hfst p
    simp only [HomologicalComplex.comp_f] at h
    exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)
  · have h₁ : ((limComplexFunctor R).map f).f p ≫ (homotopyLimitLift L).f p ≫
        (mappingCocone.snd _).v p (p + -1) rfl = 0 := by
      rw [homotopyLimitLift_f_snd_v, Limits.comp_zero]
    have h₂ : (homotopyLimitLift K).f p ≫ ((homotopyLimitFunctor R).map f).f p ≫
        (mappingCocone.snd _).v p (p + -1) rfl = 0 := by
      -- `(homotopyLimitFunctor R).map f` is the shifted mapping cone map only up to unfolding.
      erw [hsnd p, homotopyLimitLift_f_snd_v_assoc K p (p + -1) rfl, Limits.zero_comp]
    exact (Category.assoc _ _ _).trans (h₁.trans (h₂.symm.trans (Category.assoc _ _ _).symm))

/-- For a complex of towers whose terms have vanishing `lim¹`, for instance towers with surjective
transitions, the comparison map `lim K → holim K` is a quasi-isomorphism. -/
theorem quasiIso_homotopyLimitLift {K : CochainComplex (ModuleTower.{v} R) ℤ}
    (hK : ∀ i, Subsingleton (K.X i).limOne) :
    QuasiIso (homotopyLimitLift K) :=
  mappingCocone.quasiIso_lift_of_shortExact (S := ShortComplex.mk _ _
    (limComplexι_app_comp_complexShift_app K))
    (HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i ↦
      shortExact_limι_shiftNatTrans (hK i))

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

theorem derivedLimitπ_def (K : CochainComplex (ModuleTower.{v} R) ℤ) (n : ℕ) :
    derivedLimitπ K n = (derivedLimitFactors R).hom.app K ≫ DerivedCategory.Q.map
      (homotopyLimitFst K ≫ (NatTrans.mapHomologicalComplex (productπ R n) _).app K) :=
  (rfl)

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
  rw [derivedLimitπ_def, derivedLimitπ_def, Category.assoc, ← CategoryTheory.Functor.map_comp,
    Category.assoc, h]
  simp [Preadditive.comp_sub]

end Projections

section LimComplex

variable [HasDerivedCategory.{w} (ModuleTower.{v} R)] [HasDerivedCategory.{w'} (ModuleCat.{v} R)]
  {R}

/-- For a complex of towers whose terms have vanishing `lim¹`, for instance towers with surjective
transitions, the derived limit is the termwise limit: `Rlim K ≅ lim K` in `D(R)`, through the
comparison map `lim K → holim K`. -/
def derivedLimitIsoLimComplex (K : CochainComplex (ModuleTower.{v} R) ℤ)
    (hK : ∀ i, Subsingleton (K.X i).limOne) :
    (derivedLimit R).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((limComplexFunctor R).obj K) :=
  have := quasiIso_homotopyLimitLift hK
  (derivedLimitFactors R).app K ≪≫ (asIso (DerivedCategory.Q.map (homotopyLimitLift K))).symm

theorem derivedLimitIsoLimComplex_inv (K : CochainComplex (ModuleTower.{v} R) ℤ)
    (hK : ∀ i, Subsingleton (K.X i).limOne) :
    (derivedLimitIsoLimComplex K hK).inv =
      DerivedCategory.Q.map (homotopyLimitLift K) ≫ (derivedLimitFactors R).inv.app K :=
  (rfl)

/-- Under the identification of the derived limit with the termwise limit, the projections
`Rlim K → Kₙ` become the projections `lim K → Kₙ`. -/
@[reassoc (attr := simp)]
theorem derivedLimitIsoLimComplex_inv_comp_derivedLimitπ
    (K : CochainComplex (ModuleTower.{v} R) ℤ)
    (hK : ∀ i, Subsingleton (K.X i).limOne) (n : ℕ) :
    (derivedLimitIsoLimComplex K hK).inv ≫ derivedLimitπ K n =
      DerivedCategory.Q.map
        ((limComplexι R).app K ≫ (NatTrans.mapHomologicalComplex (productπ R n) _).app K) := by
  rw [derivedLimitIsoLimComplex_inv, derivedLimitπ_def, Category.assoc,
    Iso.inv_hom_id_app_assoc, ← CategoryTheory.Functor.map_comp,
    homotopyLimitLift_comp_homotopyLimitFst_assoc]

end LimComplex

end ModuleTower

end TauCeti
