/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import TauCeti.Algebra.Category.Grp.FilteredColimits

/-!
# Filtered colimits of modules with independent universe levels

The forgetful functor from `ModuleCat.{u} R` to `Type u` preserves filtered colimits with no
constraint between the ring universe `v` and the module universe `u`
(`ModuleCat.forget_preservesFilteredColimits`), factoring through `AddCommGrpCat.{u}`.

It also records a recognition criterion with no universe constraints at all: a cocone of modules
is colimiting as soon as its legs are jointly surjective and any two elements with the same image
in the apex already have a common image somewhere deeper in the diagram
(`TauCeti.ModuleCat.isColimitOfJointlySurjective`). It is the criterion for abelian groups,
`TauCeti.AddCommGrpCat.isColimitOfJointlySurjective`, reflected along the forgetful functor to
`AddCommGrpCat`, which reflects colimits whatever the universes of the ring and the modules. This
covers modules of chains with local coefficients, whose universe is that of the space rather than
that of the ring. Over a directed order, injectivity only needs checking on elements mapped to zero
in the apex (`TauCeti.ModuleCat.isColimitOfJointlySurjectiveOfMapEqZero`).

Finally, for a commutative ring `R` and a filtered (or empty) index category `J`, a compatible
family of `R`-bilinear pairings `F(j) × G(j) → H(j)` induces a canonical `R`-bilinear pairing
`colimit F × colimit G → colimit H` (`TauCeti.ModuleCat.colimitBilinear`), uniquely determined by
its values on the colimit insertions (`TauCeti.ModuleCat.colimit_bilinear_ext`).
-/

public noncomputable section

open CategoryTheory Limits

namespace ModuleCat

universe u v

/-- Forgetting modules preserves filtered colimits with no constraint between the ring universe
and the module universe. -/
instance forget_preservesFilteredColimits (R : Type v) [Ring R] :
    PreservesFilteredColimits (CategoryTheory.forget (ModuleCat.{u} R)) where
  preserves_filtered_colimits _ _ _ :=
    Limits.comp_preservesColimitsOfShape
      (CategoryTheory.forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
      (CategoryTheory.forget AddCommGrpCat.{u})

end ModuleCat

namespace TauCeti.ModuleCat

universe u v w

section ColimitExt

variable {R : Type*} [Ring R] {J : Type u} [Category.{w} J] {F : J ⥤ _root_.ModuleCat.{v} R}

/-- A cocone on a diagram of modules is colimiting as soon as its legs are jointly surjective and
any two elements with the same image in the apex have a common image somewhere deeper in the
diagram. There are no universe bounds on the index category, the ring or the modules. -/
def isColimitOfJointlySurjective (t : Cocone F)
    (hsurj : ∀ x : t.pt, ∃ (j : J) (y : F.obj j), (t.ι.app j).hom y = x)
    (hinj : ∀ (i j : J) (xi : F.obj i) (xj : F.obj j),
      (t.ι.app i).hom xi = (t.ι.app j).hom xj →
        ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), (F.map f).hom xi = (F.map g).hom xj) :
    IsColimit t := by
  let Φ := forget₂ (_root_.ModuleCat.{v} R) _root_.AddCommGrpCat.{v}
  let hc : IsColimit (Φ.mapCocone t) :=
    AddCommGrpCat.isColimitOfJointlySurjective (Φ.mapCocone t) hsurj hinj
  have : HasColimit (F ⋙ Φ) := ⟨⟨_, hc⟩⟩
  exact isColimitOfReflects Φ hc

/-- A cocone on a diagram of modules indexed by a directed order is colimiting as soon as its legs
are jointly surjective and every element mapped to zero in the apex is already mapped to zero
somewhere further along the diagram. -/
def isColimitOfJointlySurjectiveOfMapEqZero {ι : Type u} [Preorder ι] [IsDirectedOrder ι]
    {F : ι ⥤ _root_.ModuleCat.{v} R} (t : Cocone F)
    (hsurj : ∀ x : t.pt, ∃ (j : ι) (y : F.obj j), (t.ι.app j).hom y = x)
    (hzero : ∀ (i : ι) (x : F.obj i), (t.ι.app i).hom x = 0 →
      ∃ (j : ι) (hij : i ≤ j), (F.map (homOfLE hij)).hom x = 0) :
    IsColimit t :=
  isColimitOfJointlySurjective t hsurj fun i j xi xj hij ↦ by
    obtain ⟨l, hil, hjl⟩ := exists_ge_ge i j
    -- the difference of the two images at a common upper bound vanishes in the apex
    obtain ⟨m, hlm, hm⟩ := hzero l ((F.map (homOfLE hil)).hom xi - (F.map (homOfLE hjl)).hom xj)
      (by rwa [map_sub, sub_eq_zero, ← ConcreteCategory.comp_apply, Cocone.w,
        ← ConcreteCategory.comp_apply, Cocone.w])
    refine ⟨m, homOfLE (hil.trans hlm), homOfLE (hjl.trans hlm), ?_⟩
    rwa [map_sub, sub_eq_zero, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← F.map_comp, ← F.map_comp] at hm

/-- Two `R`-linear maps out of a colimit of `R`-modules agree if they agree on all colimit
insertions `colimit.ι F j`. -/
theorem linearMap_colimit_ext [HasColimit F] {M : _root_.ModuleCat.{v} R}
    {f g : (colimit F : _root_.ModuleCat.{v} R) →ₗ[R] M}
    (h : ∀ j (x : F.obj j), f (colimit.ι F j x) = g (colimit.ι F j x)) : f = g := by
  have h' : (_root_.ModuleCat.ofHom f : colimit F ⟶ M) = _root_.ModuleCat.ofHom g :=
    colimit.hom_ext fun j ↦ by
      ext x
      exact h j x
  exact congrArg _root_.ModuleCat.Hom.hom h'

end ColimitExt

section FilteredBilinear

variable {R : Type*} [CommRing R] {J : Type u} [Category.{w} J] [IsFilteredOrEmpty J]

/-- Two `R`-bilinear maps out of filtered colimits of `R`-modules agree if they agree on pairs
coming from the same index `j : J`. -/
theorem colimit_bilinear_ext {F G : J ⥤ _root_.ModuleCat.{v} R} [HasColimit F] [HasColimit G]
    {M : _root_.ModuleCat.{v} R}
    {Φ Ψ : (colimit F : _root_.ModuleCat.{v} R) →ₗ[R] (colimit G : _root_.ModuleCat.{v} R) →ₗ[R] M}
    (h : ∀ j (x : F.obj j) (y : G.obj j),
      Φ (colimit.ι F j x) (colimit.ι G j y) = Ψ (colimit.ι F j x) (colimit.ι G j y)) :
    Φ = Ψ :=
  linearMap_colimit_ext
    (M := _root_.ModuleCat.of R ((colimit G : _root_.ModuleCat.{v} R) →ₗ[R] M)) fun i x ↦
    linearMap_colimit_ext fun j y ↦ by
      rw [← colimit.w F (IsFiltered.leftToMax i j), ← colimit.w G (IsFiltered.rightToMax i j),
        _root_.ModuleCat.comp_apply, _root_.ModuleCat.comp_apply]
      exact h (IsFiltered.max i j) _ _

/-- Two `R`-trilinear maps out of filtered colimits of `R`-modules agree if they agree on triples
coming from the same index `j : J`. -/
theorem colimit_trilinear_ext {F₁ F₂ F₃ : J ⥤ _root_.ModuleCat.{v} R}
    [HasColimit F₁] [HasColimit F₂] [HasColimit F₃] {M : _root_.ModuleCat.{v} R}
    {Φ Ψ : (colimit F₁ : _root_.ModuleCat.{v} R) →ₗ[R] (colimit F₂ : _root_.ModuleCat.{v} R) →ₗ[R]
      (colimit F₃ : _root_.ModuleCat.{v} R) →ₗ[R] M}
    (h : ∀ j (x : F₁.obj j) (y : F₂.obj j) (z : F₃.obj j),
      Φ (colimit.ι F₁ j x) (colimit.ι F₂ j y) (colimit.ι F₃ j z) =
        Ψ (colimit.ι F₁ j x) (colimit.ι F₂ j y) (colimit.ι F₃ j z)) :
    Φ = Ψ :=
  colimit_bilinear_ext
    (M := _root_.ModuleCat.of R ((colimit F₃ : _root_.ModuleCat.{v} R) →ₗ[R] M)) fun m x y ↦
    linearMap_colimit_ext fun i₃ z ↦ by
      rw [← colimit.w F₁ (IsFiltered.leftToMax m i₃), ← colimit.w F₂ (IsFiltered.leftToMax m i₃),
        ← colimit.w F₃ (IsFiltered.rightToMax m i₃), _root_.ModuleCat.comp_apply,
        _root_.ModuleCat.comp_apply, _root_.ModuleCat.comp_apply]
      exact h (IsFiltered.max m i₃) _ _ _

variable {F G H : J ⥤ _root_.ModuleCat.{v} R} [HasColimit F] [HasColimit G] [HasColimit H]
  (B : ∀ j, F.obj j →ₗ[R] G.obj j →ₗ[R] H.obj j)
  (hB : ∀ ⦃i j : J⦄ (f : i ⟶ j) x y, B j (F.map f x) (G.map f y) = H.map f (B i x y))

private def colimitBilinearLeg (i : J) (x : F.obj i) (j : J) : G.obj j ⟶ colimit H :=
  _root_.ModuleCat.ofHom <|
    (colimit.ι H (IsFiltered.max i j)).hom.comp <|
      (B (IsFiltered.max i j) (F.map (IsFiltered.leftToMax i j) x)).comp
        (G.map (IsFiltered.rightToMax i j)).hom

section WithCompat
include hB

omit [HasColimit F] [HasColimit G] in
private lemma colimitBilinearLeg_eq (i : J) (x : F.obj i) (j k : J)
    (fi : i ⟶ k) (fj : j ⟶ k) (y : G.obj j) :
    colimitBilinearLeg B i x j y = colimit.ι H k (B k (F.map fi x) (G.map fj y)) := by
  let k₀ := IsFiltered.max i j
  let fi₀ := IsFiltered.leftToMax i j
  let fj₀ := IsFiltered.rightToMax i j
  let a₁ := IsFiltered.leftToMax k₀ k
  let b₁ := IsFiltered.rightToMax k₀ k
  let c := IsFiltered.coeqHom (fi₀ ≫ a₁) (fi ≫ b₁)
  let d := IsFiltered.coeqHom (fj₀ ≫ a₁ ≫ c) (fj ≫ b₁ ≫ c)
  have hi : fi₀ ≫ (a₁ ≫ c ≫ d) = fi ≫ (b₁ ≫ c ≫ d) := by
    simp only [← Category.assoc]
    exact IsFiltered.coeq_condition (fi₀ ≫ a₁) (fi ≫ b₁) =≫ d
  have hj : fj₀ ≫ (a₁ ≫ c ≫ d) = fj ≫ (b₁ ≫ c ≫ d) := by
    simpa only [Category.assoc] using IsFiltered.coeq_condition (fj₀ ≫ a₁ ≫ c) (fj ≫ b₁ ≫ c)
  have step (k' m : J) (fi' : i ⟶ k') (fj' : j ⟶ k') (u' : k' ⟶ m) :
      colimit.ι H k' (B k' (F.map fi' x) (G.map fj' y)) =
        colimit.ι H m (B m (F.map (fi' ≫ u') x) (G.map (fj' ≫ u') y)) := by
    rw [← colimit.w H u', _root_.ModuleCat.comp_apply, ← hB, ← _root_.ModuleCat.comp_apply,
      ← F.map_comp, ← _root_.ModuleCat.comp_apply, ← G.map_comp]
  exact (step k₀ _ fi₀ fj₀ (a₁ ≫ c ≫ d)).trans <| by
    rw [hi, hj]
    exact (step k _ fi fj (b₁ ≫ c ≫ d)).symm

private def colimitBilinearRight (i : J) (x : F.obj i) : colimit G ⟶ colimit H :=
  colimit.desc G
    { pt := colimit H
      ι :=
        { app := colimitBilinearLeg B i x
          naturality j₁ j₂ f := by
            ext y
            simp only [Functor.const_obj_map, _root_.ModuleCat.hom_comp, LinearMap.comp_apply]
            change colimitBilinearLeg B i x j₂ (G.map f y) = colimitBilinearLeg B i x j₁ y
            rw [colimitBilinearLeg_eq B hB i x j₂ _ (IsFiltered.leftToMax i j₂)
                (IsFiltered.rightToMax i j₂),
              colimitBilinearLeg_eq B hB i x j₁ _ (IsFiltered.leftToMax i j₂)
                (f ≫ IsFiltered.rightToMax i j₂),
              ← _root_.ModuleCat.comp_apply, ← G.map_comp] } }

omit [HasColimit F] in
private lemma colimitBilinearRight_ι (i : J) (x : F.obj i) (j : J) (y : G.obj j) :
    colimitBilinearRight B hB i x (colimit.ι G j y) = colimitBilinearLeg B i x j y := by
  rw [← _root_.ModuleCat.comp_apply, colimitBilinearRight, colimit.ι_desc]

private def colimitBilinearCocone : Cocone F where
  pt := _root_.ModuleCat.of R ((colimit G : _root_.ModuleCat.{v} R) →ₗ[R]
    (colimit H : _root_.ModuleCat.{v} R))
  ι :=
    { app i := _root_.ModuleCat.ofHom
        { toFun x := (colimitBilinearRight B hB i x).hom
          map_add' x₁ x₂ := linearMap_colimit_ext fun j y ↦ by
            simp [colimitBilinearRight_ι, colimitBilinearLeg]
          map_smul' r x := linearMap_colimit_ext fun j y ↦ by
            simp [colimitBilinearRight_ι, colimitBilinearLeg] }
      naturality i₁ i₂ f := by
        ext x
        refine linearMap_colimit_ext fun j y ↦ ?_
        change colimitBilinearRight B hB i₂ (F.map f x) (colimit.ι G j y) =
          colimitBilinearRight B hB i₁ x (colimit.ι G j y)
        rw [colimitBilinearRight_ι, colimitBilinearRight_ι,
          colimitBilinearLeg_eq B hB i₂ _ j _ (IsFiltered.leftToMax i₂ j)
            (IsFiltered.rightToMax i₂ j),
          colimitBilinearLeg_eq B hB i₁ _ j _ (f ≫ IsFiltered.leftToMax i₂ j)
            (IsFiltered.rightToMax i₂ j),
          ← _root_.ModuleCat.comp_apply, ← F.map_comp] }

/-- The `R`-bilinear pairing on filtered colimits of `R`-modules induced by a compatible family of
`R`-bilinear pairings `B j : F(j) →ₗ[R] G(j) →ₗ[R] H(j)`. -/
def colimitBilinear :
    (colimit F : _root_.ModuleCat.{v} R) →ₗ[R] (colimit G : _root_.ModuleCat.{v} R) →ₗ[R]
      (colimit H : _root_.ModuleCat.{v} R) :=
  (colimit.desc F (colimitBilinearCocone B hB)).hom

/-- On elements inserted from the same index `j : J`, `colimitBilinear` applies `B j` followed by
the colimit insertion `colimit.ι H j`. -/
@[simp]
theorem colimitBilinear_ι (j : J) (x : F.obj j) (y : G.obj j) :
    colimitBilinear B hB (colimit.ι F j x) (colimit.ι G j y) = colimit.ι H j (B j x y) := by
  have hfac : colimitBilinear B hB (colimit.ι F j x) = (colimitBilinearRight B hB j x).hom :=
    (_root_.ModuleCat.comp_apply _ _ x).symm.trans <|
      ConcreteCategory.congr_hom (colimit.ι_desc (colimitBilinearCocone B hB) j) x
  rw [hfac]
  change colimitBilinearRight B hB j x (colimit.ι G j y) = _
  rw [colimitBilinearRight_ι, colimitBilinearLeg_eq B hB j x j j (𝟙 j) (𝟙 j) y, F.map_id, G.map_id]
  rfl

end WithCompat

end FilteredBilinear

end TauCeti.ModuleCat
