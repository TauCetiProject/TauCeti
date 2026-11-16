/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.CompactlyGenerated.Coreflection
public import TauCeti.Topology.Convenient.MonoidalClosed

/-!
# Cartesian monoidal closed structure and compact-open comparisons for `CompactlyGenerated`

`TopCat` is not cartesian closed because `C(X, Y)` admits a continuous evaluation map in general
only when `X` is locally compact. Refining products and mapping spaces by
`TopCat.toCompactlyGenerated` resolves this while preserving locally compact products and
compact-open mapping spaces up to canonical isomorphism.

We equip `CompactlyGenerated.{u, w}` with chosen finite products and `MonoidalClosed` by
transporting `GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)`
(`TauCeti.Topology.Convenient.MonoidalClosed`) along `CompactlyGenerated.equivGeneratedByTopCat`,
unwrapping points via `CompactlyGenerated.tensorEquiv` and `CompactlyGenerated.ihomEquiv`:

* **Cartesian monoidal closedness**: `CartesianMonoidalCategory`, `BraidedCategory`, and
  `MonoidalClosed` on `CompactlyGenerated.{u, w}`, with `ihomTensorIso` evaluation lemmas.
* **Convenient vs. ordinary products (Fox–Whitehead, Hatcher Proposition A.15)**:
  `PreservesLimit (pair X Y) compactlyGeneratedToTop.{u, w}` and
  `prodComparisonIsoOfLocallyCompactLeft` / `Right` (see
  `TauCeti.Topology.Convenient.CompactlyGenerated` for the point-set theorems).
* **Compact-open comparisons (Vogt Proposition 3.2, Hatcher Proposition A.16)**: unconditional
  `ihomIsoCompactOpen` and `compactOpenCurryIso` (see
  `Topology.ContinuousMapGeneratedBy.homeomorphContinuousMapOfT2` for Hausdorff sources), plus
  `T2Space`/`Nontrivial` preservation, `unitSquareHomeomorph`, and `boolIhomIso` at `{u, w}`.

## References

* R. H. Fox, *On topologies for function spaces*, Bull. Amer. Math. Soc. 51 (1945), 429–432.
* J. H. C. Whitehead, *Note on a theorem due to Borsuk*, Bull. Amer. Math. Soc. 54 (1948).
* N. E. Steenrod, *A convenient category of topological spaces*, Michigan Math. J. 14 (1967).
* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory* (1971).
* M. Escardó, J. Lawson, and A. Simpson, *Comparing Cartesian closed categories of (core) compactly
  generated spaces*, Topology Appl. 143 (2004), 105–145.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), A.14–A.16.
-/

public section
noncomputable section

universe u w

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open Topology TopologicalSpace

/-! ### Chosen finite products and cartesian monoidal closed structure on `CompactlyGenerated` -/

namespace CompactlyGenerated

instance instLocallyCompactSpaceToGeneratedByTopCat (X : CompactlyGenerated.{u, w})
    [LocallyCompactSpace X] : LocallyCompactSpace (toGeneratedByTopCat.{u, w}.obj X) := ‹_›
instance instT2SpaceToGeneratedByTopCat (X : CompactlyGenerated.{u, w}) [T2Space X] :
    T2Space (toGeneratedByTopCat.{u, w}.obj X) := ‹_›

/-- The one-point space `PUnit` is terminal in `CompactlyGenerated.{u, w}`. -/
def isTerminalPUnit : IsTerminal (of.{u, w} PUnit.{w + 1}) :=
  IsTerminal.ofUniqueHom (fun _ ↦ ConcreteCategory.ofHom ⟨fun _ ↦ PUnit.unit, continuous_const⟩)
    (fun _ _ ↦ by ext x)

/-- The chosen binary product cone in `CompactlyGenerated.{u, w}`, with point
`TopCat.toCompactlyGenerated.obj (TopCat.of (X × Y))`. -/
@[expose] def prodBinaryFan (X Y : CompactlyGenerated.{u, w}) : BinaryFan X Y :=
  let fan := GeneratedByTopCat.prodBinaryFan
    (toGeneratedByTopCat.{u, w}.obj X) (toGeneratedByTopCat.{u, w}.obj Y)
  BinaryFan.mk (fromGeneratedByTopCat.{u, w}.map fan.fst) (fromGeneratedByTopCat.{u, w}.map fan.snd)

/-- `prodBinaryFan X Y` is a limit cone in `CompactlyGenerated.{u, w}`. -/
def prodBinaryFanIsLimit (X Y : CompactlyGenerated.{u, w}) : IsLimit (prodBinaryFan X Y) :=
  mapIsLimitOfPreservesOfIsLimit fromGeneratedByTopCat.{u, w} _ _
    (GeneratedByTopCat.prodBinaryFanIsLimit (toGeneratedByTopCat.{u, w}.obj X)
      (toGeneratedByTopCat.{u, w}.obj Y))

/-- Chosen finite products on `CompactlyGenerated.{u, w}`, with unit `of PUnit` and binary product
`TopCat.toCompactlyGenerated.obj (TopCat.of (X × Y))`. -/
instance instCartesianMonoidalCategory : CartesianMonoidalCategory CompactlyGenerated.{u, w} :=
  .ofChosenFiniteProducts ⟨_, isTerminalPUnit⟩
    fun X Y ↦ ⟨prodBinaryFan X Y, prodBinaryFanIsLimit X Y⟩

instance instBraidedCategory : BraidedCategory CompactlyGenerated.{u, w} :=
  .ofCartesianMonoidalCategory

theorem tensorObj_def (X Y : CompactlyGenerated.{u, w}) :
    X ⊗ Y = TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of (X × Y)) := (rfl)
theorem tensorUnit_def : 𝟙_ CompactlyGenerated.{u, w} = of.{u, w} PUnit.{w + 1} := (rfl)
@[simp] theorem toGeneratedByTopCat_obj_tensor (X Y : CompactlyGenerated.{u, w}) :
    toGeneratedByTopCat.{u, w}.obj (X ⊗ Y) =
      toGeneratedByTopCat.{u, w}.obj X ⊗ toGeneratedByTopCat.{u, w}.obj Y := (rfl)
@[simp] theorem toGeneratedByTopCat_obj_unit :
    toGeneratedByTopCat.{u, w}.obj (𝟙_ CompactlyGenerated.{u, w}) =
      𝟙_ (GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)) := (rfl)

/-- The canonical bijection identifying points of `X ⊗ Y` in `CompactlyGenerated.{u, w}` with
`X × Y`. -/
@[expose] def tensorEquiv (X Y : CompactlyGenerated.{u, w}) : ↑(X ⊗ Y) ≃ X × Y :=
  TopCat.toCompactlyGeneratedEquiv.{u, w} (TopCat.of (X × Y))

/-- `X ⊗ Y` of two Hausdorff spaces in `CompactlyGenerated.{u, w}` is Hausdorff. -/
instance instT2SpaceTensor (X Y : CompactlyGenerated.{u, w}) [T2Space X] [T2Space Y] :
    T2Space ↑(X ⊗ Y) :=
  inferInstanceAs (T2Space ↑(toGeneratedByTopCat.{u, w}.obj X ⊗ toGeneratedByTopCat.{u, w}.obj Y))
instance instNontrivialTensorLeft (X Y : CompactlyGenerated.{u, w}) [Nontrivial X] [Nonempty Y] :
    Nontrivial ↑(X ⊗ Y) := (tensorEquiv X Y).nontrivial
instance instNontrivialTensorRight (X Y : CompactlyGenerated.{u, w}) [Nonempty X] [Nontrivial Y] :
    Nontrivial ↑(X ⊗ Y) := (tensorEquiv X Y).nontrivial

variable {W W₁ W₂ X X₁ X₂ Y Y' Y₁ Y₂ Z Z' : CompactlyGenerated.{u, w}}

@[ext] theorem tensor_ext {p q : ↑(X ⊗ Y)} (h : tensorEquiv X Y p = tensorEquiv X Y q) : p = q :=
  (tensorEquiv X Y).injective h
@[simp] theorem fst_apply (p : ↑(X ⊗ Y)) : fst X Y p = (tensorEquiv X Y p).1 := (rfl)
@[simp] theorem snd_apply (p : ↑(X ⊗ Y)) : snd X Y p = (tensorEquiv X Y p).2 := (rfl)

private theorem eq_tensorEquiv_symm {p : ↑(X ⊗ Y)} {x : X} {y : Y}
    (h₁ : fst X Y p = x) (h₂ : snd X Y p = y) : p = (tensorEquiv X Y).symm (x, y) :=
  (tensorEquiv X Y).injective <| (Prod.ext h₁ h₂).trans ((tensorEquiv X Y).apply_symm_apply _).symm

@[simp] theorem lift_apply (f : W ⟶ X) (g : W ⟶ Y) (w : W) :
    CartesianMonoidalCategory.lift f g w = (tensorEquiv X Y).symm (f w, g w) :=
  eq_tensorEquiv_symm congr($(lift_fst f g) w) congr($(lift_snd f g) w)
@[simp] theorem tensor_apply (f : W₁ ⟶ X) (g : W₂ ⟶ Y) (p : ↑(W₁ ⊗ W₂)) :
    (f ⊗ₘ g) p = (tensorEquiv X Y).symm (f (tensorEquiv W₁ W₂ p).1, g (tensorEquiv W₁ W₂ p).2) :=
  eq_tensorEquiv_symm congr($(tensorHom_fst f g) p) congr($(tensorHom_snd f g) p)
@[simp] theorem whiskerLeft_apply (X : CompactlyGenerated.{u, w}) (g : Y₁ ⟶ Y₂) (p : ↑(X ⊗ Y₁)) :
    (X ◁ g) p = (tensorEquiv X Y₂).symm ((tensorEquiv X Y₁ p).1, g (tensorEquiv X Y₁ p).2) :=
  eq_tensorEquiv_symm congr($(whiskerLeft_fst X g) p) congr($(whiskerLeft_snd X g) p)
@[simp] theorem whiskerRight_apply (f : X₁ ⟶ X₂) (Y : CompactlyGenerated.{u, w}) (p : ↑(X₁ ⊗ Y)) :
    (f ▷ Y) p = (tensorEquiv X₂ Y).symm (f (tensorEquiv X₁ Y p).1, (tensorEquiv X₁ Y p).2) :=
  eq_tensorEquiv_symm congr($(whiskerRight_fst f Y) p) congr($(whiskerRight_snd f Y) p)
@[simp] theorem braiding_hom_apply (p : ↑(X ⊗ Y)) :
    (β_ X Y).hom p = (tensorEquiv Y X).symm (tensorEquiv X Y p).swap :=
  eq_tensorEquiv_symm congr($(braiding_hom_fst X Y) p) congr($(braiding_hom_snd X Y) p)
@[simp] theorem braiding_inv_apply (p : ↑(Y ⊗ X)) :
    (β_ X Y).inv p = (tensorEquiv X Y).symm (tensorEquiv Y X p).swap :=
  eq_tensorEquiv_symm congr($(braiding_inv_fst X Y) p) congr($(braiding_inv_snd X Y) p)
@[simp] theorem associator_hom_apply (p : ↑((X ⊗ Y) ⊗ Z)) :
    (α_ X Y Z).hom p = (tensorEquiv X (Y ⊗ Z)).symm ((tensorEquiv X Y (tensorEquiv _ Z p).1).1,
      (tensorEquiv Y Z).symm ((tensorEquiv X Y (tensorEquiv _ Z p).1).2, (tensorEquiv _ Z p).2)) :=
  eq_tensorEquiv_symm congr($(associator_hom_fst X Y Z) p)
    (eq_tensorEquiv_symm congr($(associator_hom_snd_fst X Y Z) p)
      congr($(associator_hom_snd_snd X Y Z) p))
@[simp] theorem associator_inv_apply (p : ↑(X ⊗ (Y ⊗ Z))) :
    (α_ X Y Z).inv p = (tensorEquiv (X ⊗ Y) Z).symm ((tensorEquiv X Y).symm
      ((tensorEquiv X _ p).1, (tensorEquiv Y Z (tensorEquiv X _ p).2).1),
      (tensorEquiv Y Z (tensorEquiv X _ p).2).2) :=
  eq_tensorEquiv_symm (eq_tensorEquiv_symm congr($(associator_inv_fst_fst X Y Z) p)
    congr($(associator_inv_fst_snd X Y Z) p)) congr($(associator_inv_snd X Y Z) p)
@[simp] theorem leftUnitor_hom_apply (p : ↑(𝟙_ CompactlyGenerated.{u, w} ⊗ X)) :
    (λ_ X).hom p = (tensorEquiv _ X p).2 := by rw [leftUnitor_hom, snd_apply]
@[simp] theorem leftUnitor_inv_apply (x : X) :
    (λ_ X).inv x = (tensorEquiv _ X).symm (PUnit.unit, x) :=
  eq_tensorEquiv_symm (PUnit.ext _ _) congr($(Iso.inv_hom_id (λ_ X)) x)
@[simp] theorem rightUnitor_hom_apply (p : ↑(X ⊗ 𝟙_ CompactlyGenerated.{u, w})) :
    (ρ_ X).hom p = (tensorEquiv X _ p).1 := by rw [rightUnitor_hom, fst_apply]
@[simp] theorem rightUnitor_inv_apply (x : X) :
    (ρ_ X).inv x = (tensorEquiv X _).symm (x, PUnit.unit) :=
  eq_tensorEquiv_symm congr($(Iso.inv_hom_id (ρ_ X)) x) (PUnit.ext _ _)

/-- Constant morphism `X ⟶ Y` with value `y : Y` in `CompactlyGenerated.{u, w}`. -/
def const (y : Y) : X ⟶ Y := InducedCategory.homMk (TopCat.const y)

@[simp] theorem const_apply (y : Y) (x : X) : const y x = y := (rfl)

/-- The internal hom functor on `CompactlyGenerated.{u, w}`, sending `Y` to the `u`-compactly
generated refinement of `ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) X Y`. -/
@[expose] protected def ihom (X : CompactlyGenerated.{u, w}) :
    CompactlyGenerated.{u, w} ⥤ CompactlyGenerated.{u, w} :=
  toGeneratedByTopCat.{u, w} ⋙
    GeneratedByTopCat.ihom (toGeneratedByTopCat.{u, w}.obj X) ⋙ fromGeneratedByTopCat.{u, w}

/-- Currying in `CompactlyGenerated.{u, w}`: morphisms `X ⊗ Y ⟶ Z` correspond naturally to
morphisms `Y ⟶ (CompactlyGenerated.ihom X).obj Z`, transported from
`GeneratedByTopCat.tensorHomEquiv` along `CompactlyGenerated.equivGeneratedByTopCat`. -/
def tensorHomEquiv (X Y Z : CompactlyGenerated.{u, w}) :
    (X ⊗ Y ⟶ Z) ≃ (Y ⟶ (CompactlyGenerated.ihom X).obj Z) :=
  let T := toGeneratedByTopCat.{u, w}; let F := fromGeneratedByTopCat.{u, w}
  { toFun f := F.map (GeneratedByTopCat.tensorHomEquiv (T.obj X) (T.obj Y) (T.obj Z) (T.map f))
    invFun g := F.map
      ((GeneratedByTopCat.tensorHomEquiv (T.obj X) (T.obj Y) (T.obj Z)).symm (T.map g))
    left_inv f := congrArg F.map ((GeneratedByTopCat.tensorHomEquiv _ _ _).left_inv (T.map f))
    right_inv g := congrArg F.map ((GeneratedByTopCat.tensorHomEquiv _ _ _).right_inv (T.map g)) }

theorem tensorHomEquiv_symm_comp (f : Y' ⟶ Y) (g : Y ⟶ (CompactlyGenerated.ihom X).obj Z) :
    (tensorHomEquiv X Y' Z).symm (f ≫ g) = X ◁ f ≫ (tensorHomEquiv X Y Z).symm g := by
  have hw : fromGeneratedByTopCat.{u, w}.map
      (toGeneratedByTopCat.{u, w}.obj X ◁ toGeneratedByTopCat.{u, w}.map f) = X ◁ f :=
    ConcreteCategory.hom_ext _ _ fun p : ↑(X ⊗ Y') ↦ (GeneratedByTopCat.whiskerLeft_apply
      (toGeneratedByTopCat.{u, w}.obj X) (toGeneratedByTopCat.{u, w}.map f) p).trans
        (whiskerLeft_apply X f p).symm
  exact (congrArg fromGeneratedByTopCat.{u, w}.map (GeneratedByTopCat.tensorHomEquiv_symm_comp
    (toGeneratedByTopCat.{u, w}.map f) (toGeneratedByTopCat.{u, w}.map g))).trans
      (congrArg (· ≫ (tensorHomEquiv X Y Z).symm g) hw)

theorem tensorHomEquiv_comp (f : X ⊗ Y ⟶ Z) (g : Z ⟶ Z') :
    tensorHomEquiv X Y Z' (f ≫ g) = tensorHomEquiv X Y Z f ≫ (CompactlyGenerated.ihom X).map g :=
  congrArg fromGeneratedByTopCat.{u, w}.map <| GeneratedByTopCat.tensorHomEquiv_comp
    (toGeneratedByTopCat.{u, w}.map f) (toGeneratedByTopCat.{u, w}.map g)

/-- **Cartesian closedness of `CompactlyGenerated.{u, w}`**: for every test universe `u` and carrier
universe `w`, `CompactlyGenerated.{u, w}` is a cartesian monoidal closed category. -/
instance instMonoidalClosed : MonoidalClosed CompactlyGenerated.{u, w} where
  closed X :=
    { rightAdj := CompactlyGenerated.ihom X
      adj := Adjunction.mkOfHomEquiv
        { homEquiv := tensorHomEquiv X
          homEquiv_naturality_left_symm := tensorHomEquiv_symm_comp
          homEquiv_naturality_right := tensorHomEquiv_comp } }

theorem homEquiv_def (X Y Z : CompactlyGenerated.{u, w}) :
    (ihom.adjunction X).homEquiv Y Z = tensorHomEquiv X Y Z :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _
theorem ihom_obj_def (X Y : CompactlyGenerated.{u, w}) : (ihom X).obj Y =
    TopCat.toCompactlyGenerated.{u, w}.obj
      (TopCat.of (ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) X Y)) := (rfl)
theorem ihom_map_def (p : Y ⟶ Y') : (ihom X).map p = (CompactlyGenerated.ihom X).map p := (rfl)

/-- The canonical bijection identifying points of `(ihom X).obj Y` in `CompactlyGenerated.{u, w}`
with `(fun K : CompHaus.{u} ↦ K)`-continuous maps `X → Y`. -/
@[expose] def ihomEquiv (X Y : CompactlyGenerated.{u, w}) :
    ↑((ihom X).obj Y) ≃ ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) X Y :=
  TopCat.toCompactlyGeneratedEquiv.{u, w}
    (TopCat.of (ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) X Y))

/-- If `X` is nonempty and `Y` is nontrivial, `(ihom X).obj Y` is nontrivial. -/
instance instNontrivialIhom (X Y : CompactlyGenerated.{u, w}) [Nonempty X] [Nontrivial Y] :
    Nontrivial ↑((ihom X).obj Y) := (ihomEquiv X Y).nontrivial

@[ext] theorem ihom_obj_ext {f g : ↑((ihom X).obj Y)}
    (h : ∀ x, ihomEquiv X Y f x = ihomEquiv X Y g x) : f = g :=
  (ihomEquiv X Y).injective (DFunLike.ext _ _ h)
@[simp] theorem ihom_map_apply (p : Y ⟶ Y') (g : ↑((ihom X).obj Y)) (x : X) :
    ihomEquiv X Y' ((ihom X).map p g) x = p (ihomEquiv X Y g x) := (rfl)
@[simp] theorem tensorHomEquiv_apply_apply (f : X ⊗ Y ⟶ Z) (y : Y) (x : X) :
    ihomEquiv X Z (tensorHomEquiv X Y Z f y) x = f ((tensorEquiv X Y).symm (x, y)) :=
  GeneratedByTopCat.tensorHomEquiv_apply_apply (toGeneratedByTopCat.{u, w}.map f) y x
@[simp] theorem tensorHomEquiv_symm_apply (g : Y ⟶ (CompactlyGenerated.ihom X).obj Z)
    (p : ↑(X ⊗ Y)) : (tensorHomEquiv X Y Z).symm g p =
      ihomEquiv X Z (g (tensorEquiv X Y p).2) (tensorEquiv X Y p).1 :=
  GeneratedByTopCat.tensorHomEquiv_symm_apply (toGeneratedByTopCat.{u, w}.map g) p
@[simp] theorem curry_apply (f : X ⊗ Y ⟶ Z) (y : Y) (x : X) :
    ihomEquiv X Z (MonoidalClosed.curry f y) x = f ((tensorEquiv X Y).symm (x, y)) := by
  rw [← MonoidalClosed.homEquiv_apply_eq, homEquiv_def]; exact tensorHomEquiv_apply_apply f y x
@[simp] theorem uncurry_apply (g : Y ⟶ (ihom X).obj Z) (p : ↑(X ⊗ Y)) :
    MonoidalClosed.uncurry g p = ihomEquiv X Z (g (tensorEquiv X Y p).2) (tensorEquiv X Y p).1 := by
  rw [← MonoidalClosed.homEquiv_symm_apply_eq, homEquiv_def]; exact tensorHomEquiv_symm_apply g p
@[simp] theorem ihom_ev_app_apply (p : ↑(X ⊗ (ihom X).obj Y)) :
    dsimp% (ihom.ev X).app Y p = ihomEquiv X Y (tensorEquiv X _ p).2 (tensorEquiv X _ p).1 := by
  simp [← MonoidalClosed.uncurry_id_eq_ev]
@[simp] theorem ihom_coev_app_apply (y : Y) (x : X) :
    ihomEquiv X (X ⊗ Y) (dsimp% (ihom.coev X).app Y y) x = (tensorEquiv X Y).symm (x, y) := by
  simp [← MonoidalClosed.curry_id_eq_coev]
@[simp] theorem pre_app_apply (f : X₂ ⟶ X₁) (g : ↑((ihom X₁).obj Y)) (x₂ : X₂) :
    ihomEquiv X₂ Y ((MonoidalClosed.pre f).app Y g) x₂ = ihomEquiv X₁ Y g (f x₂) := by
  simpa using (uncurry_apply ((MonoidalClosed.pre f).app Y) ((tensorEquiv X₂ _).symm (x₂, g))).symm

/-- Evaluation of the internal hom `(ihom X).obj Y` at a point `x : X`. -/
def evalHom (Y : CompactlyGenerated.{u, w}) (x : X) : (ihom X).obj Y ⟶ Y :=
  (λ_ _).inv ≫ (const x ▷ _) ≫ (ihom.ev X).app Y

@[simp] theorem evalHom_apply (Y : CompactlyGenerated.{u, w}) (x : X) (g : ↑((ihom X).obj Y)) :
    evalHom Y x g = ihomEquiv X Y g x := by simp [evalHom]

@[simp] theorem ihomTensorIso_hom_apply (X Y Z : CompactlyGenerated.{u, w})
    (g : ↑((ihom (X ⊗ Y)).obj Z)) (x : X) (y : Y) :
    ihomEquiv Y Z (ihomEquiv X ((ihom Y).obj Z) ((ihomTensorIso X Y Z).hom g) x) y =
      ihomEquiv (X ⊗ Y) Z g ((tensorEquiv X Y).symm (x, y)) := by
  simpa [MonoidalClosed.ihomTensorIso_hom] using congr($(MonoidalClosed.uncurry_uncurry_ihomCurry
    Y X Z) ((tensorEquiv Y (X ⊗ (ihom (Y ⊗ X)).obj Z)).symm
      (y, (tensorEquiv X ((ihom (Y ⊗ X)).obj Z)).symm
        (x, (MonoidalClosed.pre (β_ Y X).hom).app Z g))))
@[simp] theorem ihomTensorIso_inv_apply (X Y Z : CompactlyGenerated.{u, w})
    (h : ↑((ihom X).obj ((ihom Y).obj Z))) (p : ↑(X ⊗ Y)) :
    ihomEquiv (X ⊗ Y) Z ((ihomTensorIso X Y Z).inv h) p =
      ihomEquiv Y Z (ihomEquiv X ((ihom Y).obj Z) h (tensorEquiv X Y p).1)
        (tensorEquiv X Y p).2 := by
  simpa [show (ihomTensorIso X Y Z).hom ((ihomTensorIso X Y Z).inv h) = h from
    congr($((ihomTensorIso X Y Z).inv_hom_id) h)] using (ihomTensorIso_hom_apply X Y Z
      ((ihomTensorIso X Y Z).inv h) (tensorEquiv X Y p).1 (tensorEquiv X Y p).2).symm

/-! ### Product and compact-open mapping space comparisons -/

section Comparison

variable (X Y Z : CompactlyGenerated.{u, w})

@[simp] theorem prodComparison_compactlyGeneratedToTop_apply (p : ↑(X ⊗ Y)) :
    dsimp% CartesianMonoidalCategory.prodComparison compactlyGeneratedToTop.{u, w} X Y p =
      tensorEquiv X Y p :=
  Prod.ext
    congr($(CartesianMonoidalCategory.prodComparison_fst compactlyGeneratedToTop.{u, w} X Y) p)
    congr($(CartesianMonoidalCategory.prodComparison_snd compactlyGeneratedToTop.{u, w} X Y) p)

instance preservesLimit_pair_compactlyGeneratedToTop [UCompactlyGeneratedSpace.{u} (X × Y)] :
    PreservesLimit (pair X Y) compactlyGeneratedToTop.{u, w} := by
  have h : CartesianMonoidalCategory.prodComparison compactlyGeneratedToTop.{u, w} X Y =
      (TopCat.isoOfHomeo (counitHomeomorph.{u, w} (X × Y))).hom :=
    TopCat.ext fun p ↦ (prodComparison_compactlyGeneratedToTop_apply X Y p).trans
      (@counitHomeomorph_apply.{u, w} (X × Y) _ ‹_› p).symm
  have : IsIso (CartesianMonoidalCategory.prodComparison compactlyGeneratedToTop.{u, w} X Y) :=
    h ▸ inferInstance
  exact preservesLimit_pair_of_isIso_prodComparison compactlyGeneratedToTop.{u, w} X Y

@[simp] theorem prodComparisonIso_compactlyGeneratedToTop_inv_apply
    [PreservesLimit (pair X Y) compactlyGeneratedToTop.{u, w}] (p : X × Y) :
    dsimp% (CartesianMonoidalCategory.prodComparisonIso compactlyGeneratedToTop.{u, w} X Y).inv p =
      (tensorEquiv X Y).symm p :=
  (tensorEquiv X Y).injective <| (prodComparison_compactlyGeneratedToTop_apply X Y _).symm.trans <|
    congr($((CartesianMonoidalCategory.prodComparisonIso
      compactlyGeneratedToTop.{u, w} X Y).inv_hom_id)
      (p : ↑(compactlyGeneratedToTop.{u, w}.obj X ⊗
        compactlyGeneratedToTop.{u, w}.obj Y))).trans ((tensorEquiv X Y).apply_symm_apply p).symm

instance preservesLimit_pair_compactlyGeneratedToTop_of_locallyCompactSpace_left
    [LocallyCompactSpace X] : PreservesLimit (pair X Y) compactlyGeneratedToTop.{u, w} :=
  have := UCompactlyGeneratedSpace.prod_of_locallyCompactSpace_left (Y := X) (Z := Y); inferInstance
instance preservesLimit_pair_compactlyGeneratedToTop_of_locallyCompactSpace_right
    [LocallyCompactSpace Y] : PreservesLimit (pair X Y) compactlyGeneratedToTop.{u, w} :=
  have := UCompactlyGeneratedSpace.prod_of_locallyCompactSpace_right (Y := X) (Z := Y)
  inferInstance

/-- When `X` is locally compact, `X ⊗ Y` in `CompactlyGenerated.{u, w}` has the ordinary product
topology in `TopCat.{w}`. -/
def prodComparisonIsoOfLocallyCompactLeft [LocallyCompactSpace X] :
    (X ⊗ Y).toTop ≅ X.toTop ⊗ Y.toTop :=
  CartesianMonoidalCategory.prodComparisonIso compactlyGeneratedToTop.{u, w} X Y

@[simp] theorem prodComparisonIsoOfLocallyCompactLeft_hom [LocallyCompactSpace X] :
    (prodComparisonIsoOfLocallyCompactLeft X Y).hom =
      CartesianMonoidalCategory.prodComparison compactlyGeneratedToTop.{u, w} X Y := (rfl)
@[simp] theorem prodComparisonIsoOfLocallyCompactLeft_inv_apply [LocallyCompactSpace X]
    (p : X × Y) : dsimp% (prodComparisonIsoOfLocallyCompactLeft X Y).inv p =
      (tensorEquiv X Y).symm p := prodComparisonIso_compactlyGeneratedToTop_inv_apply X Y p

/-- When `Y` is locally compact, `X ⊗ Y` in `CompactlyGenerated.{u, w}` has the ordinary product
topology in `TopCat.{w}`. -/
def prodComparisonIsoOfLocallyCompactRight [LocallyCompactSpace Y] :
    (X ⊗ Y).toTop ≅ X.toTop ⊗ Y.toTop :=
  CartesianMonoidalCategory.prodComparisonIso compactlyGeneratedToTop.{u, w} X Y

@[simp] theorem prodComparisonIsoOfLocallyCompactRight_hom [LocallyCompactSpace Y] :
    (prodComparisonIsoOfLocallyCompactRight X Y).hom =
      CartesianMonoidalCategory.prodComparison compactlyGeneratedToTop.{u, w} X Y := (rfl)
@[simp] theorem prodComparisonIsoOfLocallyCompactRight_inv_apply [LocallyCompactSpace Y]
    (p : X × Y) : dsimp% (prodComparisonIsoOfLocallyCompactRight X Y).inv p =
      (tensorEquiv X Y).symm p := prodComparisonIso_compactlyGeneratedToTop_inv_apply X Y p

/-- **Compact-open internal hom comparison**: for arbitrary universes `u, w` and arbitrary
`X, Y : CompactlyGenerated.{u, w}` (with no local compactness or Hausdorffness assumption),
`(ihom X).obj Y` is canonically isomorphic to `TopCat.toCompactlyGenerated.obj (TopCat.of C(X, Y))`
where `C(X, Y)` carries the compact-open topology. -/
def ihomIsoCompactOpen :
    (ihom X).obj Y ≅ TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(X, Y)) :=
  fromGeneratedByTopCat.{u, w}.mapIso <| GeneratedByTopCat.ihomIsoCompactOpen
    (toGeneratedByTopCat.{u, w}.obj X) (toGeneratedByTopCat.{u, w}.obj Y)

@[simp] theorem ihomIsoCompactOpen_hom_apply (g : ↑((ihom X).obj Y)) (x : X) :
    (TopCat.toCompactlyGeneratedEquiv.{u, w} (TopCat.of C(X, Y))
      ((ihomIsoCompactOpen X Y).hom g)) x = ihomEquiv X Y g x :=
  GeneratedByTopCat.ihomIsoCompactOpen_hom_apply
    (toGeneratedByTopCat.{u, w}.obj X) (toGeneratedByTopCat.{u, w}.obj Y) g x
@[simp] theorem ihomIsoCompactOpen_inv_apply
    (f : ↑(TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(X, Y)))) (x : X) :
    ihomEquiv X Y ((ihomIsoCompactOpen X Y).inv f) x =
      (TopCat.toCompactlyGeneratedEquiv.{u, w} (TopCat.of C(X, Y)) f) x :=
  GeneratedByTopCat.ihomIsoCompactOpen_inv_apply
    (toGeneratedByTopCat.{u, w}.obj X) (toGeneratedByTopCat.{u, w}.obj Y) f x

/-- **Exponential law for compact-open mapping spaces in `CompactlyGenerated`**: for arbitrary
`X, Y, Z : CompactlyGenerated.{u, w}`, the compactly generated refinement of `C(↑(X ⊗ Y), Z)` is
canonically isomorphic to the compactly generated refinement of
`C(X, ↑(TopCat.toCompactlyGenerated.obj (TopCat.of C(Y, Z))))`. -/
def compactOpenCurryIso :
    TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(↑(X ⊗ Y), Z)) ≅
      TopCat.toCompactlyGenerated.{u, w}.obj
        (TopCat.of C(X, ↑(TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(Y, Z))))) :=
  fromGeneratedByTopCat.{u, w}.mapIso <| GeneratedByTopCat.compactOpenCurryIso
    (toGeneratedByTopCat.{u, w}.obj X) (toGeneratedByTopCat.{u, w}.obj Y)
    (toGeneratedByTopCat.{u, w}.obj Z)

@[simp] theorem compactOpenCurryIso_hom_apply
    (f : ↑(TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(↑(X ⊗ Y), Z)))) (x : X) (y : Y) :
    TopCat.toCompactlyGeneratedEquiv.{u, w} (TopCat.of C(Y, Z))
      (TopCat.toCompactlyGeneratedEquiv.{u, w}
        (TopCat.of C(X, ↑(TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(Y, Z)))))
        ((compactOpenCurryIso X Y Z).hom f) x) y =
      TopCat.toCompactlyGeneratedEquiv.{u, w} (TopCat.of C(↑(X ⊗ Y), Z)) f
        ((tensorEquiv X Y).symm (x, y)) :=
  GeneratedByTopCat.compactOpenCurryIso_hom_apply (toGeneratedByTopCat.{u, w}.obj X)
    (toGeneratedByTopCat.{u, w}.obj Y) (toGeneratedByTopCat.{u, w}.obj Z) f x y
@[simp] theorem compactOpenCurryIso_inv_apply
    (g : ↑(TopCat.toCompactlyGenerated.{u, w}.obj
      (TopCat.of C(X, ↑(TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(Y, Z)))))))
    (p : ↑(X ⊗ Y)) :
    TopCat.toCompactlyGeneratedEquiv.{u, w} (TopCat.of C(↑(X ⊗ Y), Z))
      ((compactOpenCurryIso X Y Z).inv g) p =
      TopCat.toCompactlyGeneratedEquiv.{u, w} (TopCat.of C(Y, Z))
        (TopCat.toCompactlyGeneratedEquiv.{u, w}
          (TopCat.of C(X, ↑(TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(Y, Z)))))
          g (tensorEquiv X Y p).1) (tensorEquiv X Y p).2 :=
  GeneratedByTopCat.compactOpenCurryIso_inv_apply (toGeneratedByTopCat.{u, w}.obj X)
    (toGeneratedByTopCat.{u, w}.obj Y) (toGeneratedByTopCat.{u, w}.obj Z) g p

end Comparison

/-! ### Specializations: unit square and Boolean internal hom -/

/-- `of TopCat.I ⊗ of TopCat.I` in `CompactlyGenerated.{u, w}` is homeomorphic to
`TopCat.I × TopCat.I`. -/
def unitSquareHomeomorph :
    ↑(of.{u, w} TopCat.I.{w} ⊗ of.{u, w} TopCat.I.{w}) ≃ₜ TopCat.I.{w} × TopCat.I.{w} :=
  TopCat.homeoOfIso
    (prodComparisonIsoOfLocallyCompactLeft (of.{u, w} TopCat.I.{w}) (of.{u, w} TopCat.I.{w}))

@[simp] theorem unitSquareHomeomorph_apply
    (p : ↑(of.{u, w} TopCat.I.{w} ⊗ of.{u, w} TopCat.I.{w})) : unitSquareHomeomorph.{u, w} p =
      tensorEquiv (of.{u, w} TopCat.I.{w}) (of.{u, w} TopCat.I.{w}) p :=
  (TopCat.homeoOfIso_apply _ p).trans <| congr($(prodComparisonIsoOfLocallyCompactLeft_hom
    (of.{u, w} TopCat.I.{w}) (of.{u, w} TopCat.I.{w})) p).trans
    (prodComparison_compactlyGeneratedToTop_apply (of.{u, w} TopCat.I.{w})
      (of.{u, w} TopCat.I.{w}) p)
@[simp] theorem unitSquareHomeomorph_symm_apply (q : TopCat.I.{w} × TopCat.I.{w}) :
    unitSquareHomeomorph.{u, w}.symm q =
      (tensorEquiv (of.{u, w} TopCat.I.{w}) (of.{u, w} TopCat.I.{w})).symm q :=
  unitSquareHomeomorph.{u, w}.injective <| (unitSquareHomeomorph.{u, w}.apply_symm_apply q).trans <|
    ((tensorEquiv (of.{u, w} TopCat.I.{w})
      (of.{u, w} TopCat.I.{w})).apply_symm_apply q).symm.trans (unitSquareHomeomorph_apply _).symm

private def boolCasesHom (Y : CompactlyGenerated.{u, w}) :
    of.{u, w} (ULift.{w} Bool) ⊗ (Y ⊗ Y) ⟶ Y :=
  have : DiscreteTopology (ULift.{w} Bool) := Topology.IsEmbedding.uliftDown.discreteTopology
  let f : ULift.{w} Bool × ↑(Y ⊗ Y) → Y := fun q ↦
    Bool.rec (motive := fun _ ↦ Y) (fst Y Y q.2) (snd Y Y q.2) q.1.down
  have hf : Continuous f := continuous_prod_of_discrete_left.2 <| by
    rintro ⟨false | true⟩; exacts [(fst Y Y).hom.hom.continuous, (snd Y Y).hom.hom.continuous]
  ConcreteCategory.ofHom ⟨fun p ↦ f (tensorEquiv (of.{u, w} (ULift.{w} Bool)) (Y ⊗ Y) p),
    hf.comp (TopCat.continuous_toCompactlyGeneratedEquiv (TopCat.of (ULift.{w} Bool × ↑(Y ⊗ Y))))⟩
@[simp] private theorem boolCasesHom_apply (Y : CompactlyGenerated.{u, w})
    (p : ↑(of.{u, w} (ULift.{w} Bool) ⊗ (Y ⊗ Y))) :
    boolCasesHom Y p = Bool.rec (fst Y Y (tensorEquiv _ _ p).2) (snd Y Y (tensorEquiv _ _ p).2)
      (tensorEquiv _ _ p).1.down := rfl

/-- For every `Y : CompactlyGenerated.{u, w}`, `(ihom (of (ULift Bool))).obj Y ≅ Y ⊗ Y`. -/
def boolIhomIso (Y : CompactlyGenerated.{u, w}) :
    (ihom (of.{u, w} (ULift.{w} Bool))).obj Y ≅ Y ⊗ Y where
  hom := CartesianMonoidalCategory.lift (evalHom Y (ULift.up false)) (evalHom Y (ULift.up true))
  inv := MonoidalClosed.curry (boolCasesHom Y)
  hom_inv_id := by
    ext g b
    simpa using (curry_apply (boolCasesHom Y) _ b).trans (by rcases b with ⟨false | true⟩ <;> simp)
  inv_hom_id := CartesianMonoidalCategory.hom_ext _ _
    (by ext p; simpa using curry_apply (boolCasesHom Y) p (ULift.up false))
    (by ext p; simpa using curry_apply (boolCasesHom Y) p (ULift.up true))

@[simp] theorem boolIhomIso_hom_apply (Y : CompactlyGenerated.{u, w})
    (g : ↑((ihom (of.{u, w} (ULift.{w} Bool))).obj Y)) :
    tensorEquiv Y Y ((boolIhomIso Y).hom g) =
      (ihomEquiv (of.{u, w} (ULift.{w} Bool)) Y g (ULift.up false),
        ihomEquiv (of.{u, w} (ULift.{w} Bool)) Y g (ULift.up true)) := by simp [boolIhomIso]
@[simp] theorem boolIhomIso_inv_apply (Y : CompactlyGenerated.{u, w})
    (p : ↑(Y ⊗ Y)) (b : ULift.{w} Bool) :
    ihomEquiv (of.{u, w} (ULift.{w} Bool)) Y ((boolIhomIso Y).inv p) b =
      Bool.rec (fst Y Y p) (snd Y Y p) b.down := by
  simpa [boolIhomIso] using curry_apply (boolCasesHom Y) p b

end CompactlyGenerated

end
