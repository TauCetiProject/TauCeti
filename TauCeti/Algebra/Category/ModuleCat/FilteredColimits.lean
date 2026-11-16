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

The native filtered-colimit cocone allows the module universe to be larger than the ring
universe. This file exports preservation by the forgetful functor for that universe combination.

It also records a recognition criterion with no universe constraints at all: a cocone of modules
is colimiting as soon as its legs are jointly surjective and any two elements with the same image
in the apex already have a common image somewhere deeper in the diagram
(`TauCeti.ModuleCat.isColimitOfJointlySurjective`). It is the criterion for abelian groups,
`TauCeti.AddCommGrpCat.isColimitOfJointlySurjective`, reflected along the forgetful functor to
`AddCommGrpCat`, which reflects colimits whatever the universes of the ring and the modules. This
covers modules of chains with local coefficients, whose universe is that of the space rather than
that of the ring.

Finally, for a commutative ring `R` and a filtered (or empty) index category `J`, a compatible
family of `R`-bilinear pairings `F(j) × G(j) → H(j)` induces a canonical `R`-bilinear pairing
`colimit F × colimit G → colimit H` (`TauCeti.ModuleCat.colimitBilinear`), uniquely determined by
its values on the colimit insertions (`TauCeti.ModuleCat.colimit_bilinear_ext`).
-/

public noncomputable section

open CategoryTheory Limits

namespace ModuleCat

universe u v

/-- Forgetting modules preserves filtered colimits also when the module universe is larger
than the ring universe. -/
instance forget_preservesFilteredColimits_max (R : Type v) [Ring R] :
    PreservesFilteredColimits (CategoryTheory.forget (ModuleCat.{max u v} R)) where
  preserves_filtered_colimits J _ _ := by
    let : PreservesColimitsOfShape J
        (CategoryTheory.forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}) :=
      { preservesColimit := fun {F} ↦
          preservesColimit_of_preserves_colimit_cocone
            (ModuleCat.FilteredColimits.colimitCoconeIsColimit F)
            (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
              (F ⋙ CategoryTheory.forget₂ (ModuleCat.{max u v} R)
                AddCommGrpCat.{max u v})) }
    exact Limits.comp_preservesColimitsOfShape
      (CategoryTheory.forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
      (CategoryTheory.forget AddCommGrpCat.{max u v})

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
    Φ = Ψ := by
  refine linearMap_colimit_ext
    (M := _root_.ModuleCat.of R ((colimit G : _root_.ModuleCat.{v} R) →ₗ[R] M)) fun i x ↦ ?_
  refine linearMap_colimit_ext fun j y ↦ ?_
  let k := IsFiltered.max i j
  rw [← colimit.w F (IsFiltered.leftToMax i j), ← colimit.w G (IsFiltered.rightToMax i j),
    _root_.ModuleCat.comp_apply, _root_.ModuleCat.comp_apply]
  exact h k _ _

/-- Two `R`-trilinear maps out of filtered colimits of `R`-modules agree if they agree on triples
coming from the same index `j : J`. -/
theorem colimit_trilinear_ext {F₁ F₂ F₃ : J ⥤ _root_.ModuleCat.{v} R}
    [HasColimit F₁] [HasColimit F₂] [HasColimit F₃] {M : _root_.ModuleCat.{v} R}
    {Φ Ψ : (colimit F₁ : _root_.ModuleCat.{v} R) →ₗ[R] (colimit F₂ : _root_.ModuleCat.{v} R) →ₗ[R]
      (colimit F₃ : _root_.ModuleCat.{v} R) →ₗ[R] M}
    (h : ∀ j (x : F₁.obj j) (y : F₂.obj j) (z : F₃.obj j),
      Φ (colimit.ι F₁ j x) (colimit.ι F₂ j y) (colimit.ι F₃ j z) =
        Ψ (colimit.ι F₁ j x) (colimit.ι F₂ j y) (colimit.ι F₃ j z)) :
    Φ = Ψ := by
  refine linearMap_colimit_ext
    (M := _root_.ModuleCat.of R ((colimit F₂ : _root_.ModuleCat.{v} R) →ₗ[R]
      (colimit F₃ : _root_.ModuleCat.{v} R) →ₗ[R] M)) fun i₁ x₁ ↦ ?_
  refine linearMap_colimit_ext
    (M := _root_.ModuleCat.of R ((colimit F₃ : _root_.ModuleCat.{v} R) →ₗ[R] M)) fun i₂ x₂ ↦ ?_
  refine linearMap_colimit_ext fun i₃ x₃ ↦ ?_
  let m := IsFiltered.max i₁ i₂
  let k := IsFiltered.max m i₃
  rw [← colimit.w F₁ (IsFiltered.leftToMax i₁ i₂ ≫ IsFiltered.leftToMax m i₃),
    ← colimit.w F₂ (IsFiltered.rightToMax i₁ i₂ ≫ IsFiltered.leftToMax m i₃),
    ← colimit.w F₃ (IsFiltered.rightToMax m i₃),
    _root_.ModuleCat.comp_apply, _root_.ModuleCat.comp_apply, _root_.ModuleCat.comp_apply]
  exact h k _ _ _

variable {F G H : J ⥤ _root_.ModuleCat.{v} R} [HasColimit F] [HasColimit G] [HasColimit H]

private def colimitBilinearLeg (B : ∀ j, F.obj j →ₗ[R] G.obj j →ₗ[R] H.obj j)
    (i : J) (x : F.obj i) (j : J) : G.obj j ⟶ colimit H :=
  _root_.ModuleCat.ofHom <|
    (colimit.ι H (IsFiltered.max i j)).hom.comp <|
      (B (IsFiltered.max i j) (F.map (IsFiltered.leftToMax i j) x)).comp
        (G.map (IsFiltered.rightToMax i j)).hom

omit [HasColimit F] [HasColimit G] in
private lemma colimitBilinearLeg_eq (B : ∀ j, F.obj j →ₗ[R] G.obj j →ₗ[R] H.obj j)
    (hB : ∀ ⦃i j : J⦄ (f : i ⟶ j) x y, B j (F.map f x) (G.map f y) = H.map f (B i x y))
    (i : J) (x : F.obj i) (j k : J) (fi : i ⟶ k) (fj : j ⟶ k) (y : G.obj j) :
    colimitBilinearLeg B i x j y = colimit.ι H k (B k (F.map fi x) (G.map fj y)) := by
  let k₀ := IsFiltered.max i j
  let fi₀ : i ⟶ k₀ := IsFiltered.leftToMax i j
  let fj₀ : j ⟶ k₀ := IsFiltered.rightToMax i j
  let m₁ := IsFiltered.max k₀ k
  let a₁ : k₀ ⟶ m₁ := IsFiltered.leftToMax k₀ k
  let b₁ : k ⟶ m₁ := IsFiltered.rightToMax k₀ k
  let c : m₁ ⟶ IsFiltered.coeq (fi₀ ≫ a₁) (fi ≫ b₁) := IsFiltered.coeqHom (fi₀ ≫ a₁) (fi ≫ b₁)
  let d := IsFiltered.coeqHom (fj₀ ≫ a₁ ≫ c) (fj ≫ b₁ ≫ c)
  let m := IsFiltered.coeq (fj₀ ≫ a₁ ≫ c) (fj ≫ b₁ ≫ c)
  let u₀ : k₀ ⟶ m := a₁ ≫ c ≫ d
  let u : k ⟶ m := b₁ ≫ c ≫ d
  have hi : fi₀ ≫ u₀ = fi ≫ u := by
    simp only [u₀, u, ← Category.assoc]
    exact IsFiltered.coeq_condition (fi₀ ≫ a₁) (fi ≫ b₁) =≫ d
  have hj : fj₀ ≫ u₀ = fj ≫ u := by
    simp only [u₀, u, ← Category.assoc]
    have h := IsFiltered.coeq_condition (fj₀ ≫ a₁ ≫ c) (fj ≫ b₁ ≫ c)
    simpa only [Category.assoc] using h
  have step (k' : J) (fi' : i ⟶ k') (fj' : j ⟶ k') (u' : k' ⟶ m) :
      colimit.ι H k' (B k' (F.map fi' x) (G.map fj' y)) =
        colimit.ι H m (B m (F.map (fi' ≫ u') x) (G.map (fj' ≫ u') y)) := by
    rw [← colimit.w H u', _root_.ModuleCat.comp_apply, ← hB, ← _root_.ModuleCat.comp_apply,
      ← F.map_comp, ← _root_.ModuleCat.comp_apply, ← G.map_comp]
  exact (step k₀ fi₀ fj₀ u₀).trans <| by
    rw [hi, hj]
    exact (step k fi fj u).symm

private def colimitBilinearRight (B : ∀ j, F.obj j →ₗ[R] G.obj j →ₗ[R] H.obj j)
    (hB : ∀ ⦃i j : J⦄ (f : i ⟶ j) x y, B j (F.map f x) (G.map f y) = H.map f (B i x y))
    (i : J) (x : F.obj i) : colimit G ⟶ colimit H :=
  colimit.desc G
    { pt := colimit H
      ι :=
        { app := colimitBilinearLeg B i x
          naturality j₁ j₂ f := by
            ext y
            let k := IsFiltered.max i j₂
            let fi : i ⟶ k := IsFiltered.leftToMax i j₂
            let fj₂ : j₂ ⟶ k := IsFiltered.rightToMax i j₂
            simp only [Functor.const_obj_map, _root_.ModuleCat.hom_comp, LinearMap.comp_apply]
            -- Unfold the cocone naturality equation to an equality of `colimitBilinearLeg` values.
            change colimitBilinearLeg B i x j₂ (G.map f y) = colimitBilinearLeg B i x j₁ y
            rw [colimitBilinearLeg_eq B hB i x j₂ k fi fj₂,
              colimitBilinearLeg_eq B hB i x j₁ k fi (f ≫ fj₂),
              ← _root_.ModuleCat.comp_apply, ← G.map_comp] } }

omit [HasColimit F] in
private lemma colimitBilinearRight_ι (B : ∀ j, F.obj j →ₗ[R] G.obj j →ₗ[R] H.obj j)
    (hB : ∀ ⦃i j : J⦄ (f : i ⟶ j) x y, B j (F.map f x) (G.map f y) = H.map f (B i x y))
    (i : J) (x : F.obj i) (j : J) (y : G.obj j) :
    colimitBilinearRight B hB i x (colimit.ι G j y) = colimitBilinearLeg B i x j y := by
  rw [← _root_.ModuleCat.comp_apply, colimitBilinearRight, colimit.ι_desc]

private def colimitBilinearLeftLeg (B : ∀ j, F.obj j →ₗ[R] G.obj j →ₗ[R] H.obj j)
    (hB : ∀ ⦃i j : J⦄ (f : i ⟶ j) x y, B j (F.map f x) (G.map f y) = H.map f (B i x y))
    (i : J) :
    F.obj i ⟶
      _root_.ModuleCat.of R ((colimit G : _root_.ModuleCat.{v} R) →ₗ[R]
        (colimit H : _root_.ModuleCat.{v} R)) :=
  _root_.ModuleCat.ofHom
    { toFun := fun x ↦ (colimitBilinearRight B hB i x).hom
      map_add' := fun x₁ x₂ ↦ linearMap_colimit_ext fun j y ↦ by
        simp [colimitBilinearRight_ι, colimitBilinearLeg]
      map_smul' := fun r x ↦ linearMap_colimit_ext fun j y ↦ by
        simp [colimitBilinearRight_ι, colimitBilinearLeg] }

private def colimitBilinearCocone (B : ∀ j, F.obj j →ₗ[R] G.obj j →ₗ[R] H.obj j)
    (hB : ∀ ⦃i j : J⦄ (f : i ⟶ j) x y, B j (F.map f x) (G.map f y) = H.map f (B i x y)) :
    Cocone F where
  pt := _root_.ModuleCat.of R ((colimit G : _root_.ModuleCat.{v} R) →ₗ[R]
    (colimit H : _root_.ModuleCat.{v} R))
  ι :=
    { app := colimitBilinearLeftLeg B hB
      naturality i₁ i₂ f := by
        ext x
        refine linearMap_colimit_ext fun j y ↦ ?_
        let k := IsFiltered.max i₂ j
        let fi₂ : i₂ ⟶ k := IsFiltered.leftToMax i₂ j
        let fj : j ⟶ k := IsFiltered.rightToMax i₂ j
        -- Unfold the cocone naturality equation to values of `colimitBilinearRight`.
        change colimitBilinearRight B hB i₂ (F.map f x) (colimit.ι G j y) =
          colimitBilinearRight B hB i₁ x (colimit.ι G j y)
        rw [colimitBilinearRight_ι, colimitBilinearRight_ι,
          colimitBilinearLeg_eq B hB i₂ _ j k fi₂ fj,
          colimitBilinearLeg_eq B hB i₁ _ j k (f ≫ fi₂) fj,
          ← _root_.ModuleCat.comp_apply, ← F.map_comp] }

/-- The `R`-bilinear pairing on filtered colimits of `R`-modules induced by a compatible family of
`R`-bilinear pairings `B j : F(j) →ₗ[R] G(j) →ₗ[R] H(j)`. -/
def colimitBilinear (B : ∀ j, F.obj j →ₗ[R] G.obj j →ₗ[R] H.obj j)
    (hB : ∀ ⦃i j : J⦄ (f : i ⟶ j) x y, B j (F.map f x) (G.map f y) = H.map f (B i x y)) :
    (colimit F : _root_.ModuleCat.{v} R) →ₗ[R] (colimit G : _root_.ModuleCat.{v} R) →ₗ[R]
      (colimit H : _root_.ModuleCat.{v} R) :=
  (colimit.desc F (colimitBilinearCocone B hB)).hom

/-- On elements inserted from the same index `j : J`, `colimitBilinear` applies `B j` followed by
the colimit insertion `colimit.ι H j`. -/
@[simp]
theorem colimitBilinear_ι (B : ∀ j, F.obj j →ₗ[R] G.obj j →ₗ[R] H.obj j)
    (hB : ∀ ⦃i j : J⦄ (f : i ⟶ j) x y, B j (F.map f x) (G.map f y) = H.map f (B i x y))
    (j : J) (x : F.obj j) (y : G.obj j) :
    colimitBilinear B hB (colimit.ι F j x) (colimit.ι G j y) = colimit.ι H j (B j x y) := by
  have hfac : colimitBilinear B hB (colimit.ι F j x) = (colimitBilinearRight B hB j x).hom := by
    have h := ConcreteCategory.congr_hom (colimit.ι_desc (colimitBilinearCocone B hB) j) x
    exact (_root_.ModuleCat.comp_apply _ _ x).symm.trans h
  rw [hfac]
  -- Evaluate the bundled linear map `(colimitBilinearRight ...).hom` as a morphism application.
  change colimitBilinearRight B hB j x (colimit.ι G j y) = _
  rw [colimitBilinearRight_ι, colimitBilinearLeg_eq B hB j x j j (𝟙 j) (𝟙 j) y, F.map_id, G.map_id]
  rfl

end FilteredBilinear

end TauCeti.ModuleCat
