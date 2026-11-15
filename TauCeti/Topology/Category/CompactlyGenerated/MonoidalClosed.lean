/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
public import TauCeti.Topology.Category.CompactlyGenerated.Coreflection
public import TauCeti.Topology.Convenient.MonoidalClosed

/-!
# Cartesian monoidal closed structure and compact-open comparisons for `CompactlyGenerated`

We equip `CompactlyGenerated.{u, w}` with chosen finite products and its cartesian monoidal closed
structure by transporting those of `GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)` along the
strict isomorphism `CompactlyGenerated.equivGeneratedByTopCat`, and prove the classical product and
mapping-space comparison theorems:

* **Convenient products and ordinary products (Fox–Whitehead, Hatcher Proposition A.15)**:
  `UCompactlyGeneratedSpace.prod_of_locallyCompactSpace_left` and `right` (together with their
  `CompactlyGeneratedSpace` specializations across independent universes) show that if `Y` and `Z`
  are compactly generated and at least one factor is locally compact, then the ordinary product
  `Y × Z` is already compactly generated. Categorically, `(X ⊗ Y).toTop` is canonically isomorphic
  to `X.toTop ⊗ Y.toTop` via `CompactlyGenerated.prodComparisonIsoOfLocallyCompactLeft` and
  `CompactlyGenerated.prodComparisonIsoOfLocallyCompactRight`.
* **Cartesian monoidal closedness**: `CompactlyGenerated.{u, w}` carries
  `CartesianMonoidalCategory`, `BraidedCategory`, and `MonoidalClosed` instances with unit
  `of PUnit`, convenient product `X ⊗ Y = k (X × Y)`, internal hom
  `(ihom X).obj Y = k (ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) X Y)`, and braided
  currying isomorphism `CompactlyGenerated.ihomTensorIso : (ihom (X ⊗ Y)).obj Z ≅
  (ihom X).obj ((ihom Y).obj Z)`.
* **Compact-open comparisons (Vogt Proposition 3.2, Hatcher Proposition A.16)**:
  * Unconditionally for arbitrary universes `u, w` and arbitrary
    `X, Y, Z : CompactlyGenerated.{u, w}` (with *no* local compactness or Hausdorffness hypothesis),
    `CompactlyGenerated.ihomIsoCompactOpen` identifies `(ihom X).obj Y` with `k C(X, Y)` where
    `C(X, Y)` carries the compact-open topology, yielding the exponential isomorphism
    `CompactlyGenerated.compactOpenCurryIso : k C(↑(X ⊗ Y), Z) ≅ k C(X, ↑(k C(Y, Z)))`.
  * When `Y` is Hausdorff and `(max v u)`-compactly generated,
    `Topology.ContinuousMapGeneratedBy.homeomorphContinuousMapOfT2` shows that even before applying
    `k`, `ContinuousMapGeneratedBy (fun S : CompHaus.{max v u} ↦ S) Y T` is already homeomorphic to
    `C(Y, T)`.
* **Concrete checks**: preservation of `T2Space` and `Nontrivial` under
  `TopCat.toCompactlyGenerated`, `⊗`, and `ihom`, identification of the unit square
  `of unitInterval ⊗ of unitInterval` with `unitInterval × unitInterval`
  (`CompactlyGenerated.unitSquareHomeomorph`), and the isomorphism
  `CompactlyGenerated.boolIhomIso : (ihom (of Bool)).obj Y ≅ Y ⊗ Y` for arbitrary
  `Y : CompactlyGenerated.{u, 0}`.

## References

* R. H. Fox, *On topologies for function spaces*, Bull. Amer. Math. Soc. 51 (1945), 429–432.
* J. H. C. Whitehead, *Note on a theorem due to Borsuk*, Bull. Amer. Math. Soc. 54 (1948),
  1125–1132.
* N. E. Steenrod, *A convenient category of topological spaces*, Michigan Math. J. 14 (1967),
  133–152.
* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Arch. Math.
  (Basel) 22 (1971), 545–555.
* M. Escardó, J. Lawson and A. Simpson, *Comparing Cartesian closed categories of (core) compactly
  generated spaces*, Topology Appl. 143 (2004), 105–145.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Appendix,
  Propositions A.14–A.16.
-/

public section

noncomputable section

universe u v v' w

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open Topology TopologicalSpace

/-! ### Ordinary products of compactly generated spaces and Hausdorff hom-spaces -/

/-- **Whitehead's product theorem (left factor locally compact)**: if `Y` and `Z` are
`u`-compactly generated and `Y` is locally compact, then the ordinary product `Y × Z` is
`u`-compactly generated. -/
theorem UCompactlyGeneratedSpace.prod_of_locallyCompactSpace_left
    {Y : Type v} {Z : Type v'} [TopologicalSpace Y] [TopologicalSpace Z]
    [UCompactlyGeneratedSpace.{u} Y] [UCompactlyGeneratedSpace.{u} Z] [LocallyCompactSpace Y] :
    UCompactlyGeneratedSpace.{u} (Y × Z) :=
  (isGeneratedBy_compHaus_iff (Y × Z)).1
    (IsGeneratedBy.prod_of_locallyCompactSpace_left (X := fun K : CompHaus.{u} ↦ K))

/-- **Whitehead's product theorem (right factor locally compact)**: if `Y` and `Z` are
`u`-compactly generated and `Z` is locally compact, then the ordinary product `Y × Z` is
`u`-compactly generated. -/
theorem UCompactlyGeneratedSpace.prod_of_locallyCompactSpace_right
    {Y : Type v} {Z : Type v'} [TopologicalSpace Y] [TopologicalSpace Z]
    [UCompactlyGeneratedSpace.{u} Y] [UCompactlyGeneratedSpace.{u} Z] [LocallyCompactSpace Z] :
    UCompactlyGeneratedSpace.{u} (Y × Z) :=
  (isGeneratedBy_compHaus_iff (Y × Z)).1
    (IsGeneratedBy.prod_of_locallyCompactSpace_right (X := fun K : CompHaus.{u} ↦ K))

/-- If `Y : Type u` and `Z : Type v` are compactly generated and `Y` is locally compact, then their
ordinary product `Y × Z` is compactly generated. -/
theorem CompactlyGeneratedSpace.prod_of_locallyCompactSpace_left
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    [CompactlyGeneratedSpace Y] [CompactlyGeneratedSpace Z] [LocallyCompactSpace Y] :
    CompactlyGeneratedSpace (Y × Z) := by
  have : UCompactlyGeneratedSpace.{max u v} Y := UCompactlyGeneratedSpace.ulift.{v, u} (X := Y)
  have : UCompactlyGeneratedSpace.{max u v} Z := UCompactlyGeneratedSpace.ulift.{u, v} (X := Z)
  exact UCompactlyGeneratedSpace.prod_of_locallyCompactSpace_left

/-- If `Y : Type u` and `Z : Type v` are compactly generated and `Z` is locally compact, then their
ordinary product `Y × Z` is compactly generated. -/
theorem CompactlyGeneratedSpace.prod_of_locallyCompactSpace_right
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    [CompactlyGeneratedSpace Y] [CompactlyGeneratedSpace Z] [LocallyCompactSpace Z] :
    CompactlyGeneratedSpace (Y × Z) := by
  have : UCompactlyGeneratedSpace.{max u v} Y := UCompactlyGeneratedSpace.ulift.{v, u} (X := Y)
  have : UCompactlyGeneratedSpace.{max u v} Z := UCompactlyGeneratedSpace.ulift.{u, v} (X := Z)
  exact UCompactlyGeneratedSpace.prod_of_locallyCompactSpace_right

namespace Topology.ContinuousMapGeneratedBy

/-- When `Y` is Hausdorff and `(max v u)`-compactly generated, the canonical map from
`ContinuousMapGeneratedBy (fun S : CompHaus.{max v u} ↦ S) Y T` into `C(Y, T)` (with the
compact-open topology) is continuous, with no local compactness assumption on `Y`. -/
@[continuity, fun_prop]
theorem continuous_toContinuousMap_of_t2Space {Y : Type v} {T : Type w}
    [TopologicalSpace Y] [TopologicalSpace T]
    [UCompactlyGeneratedSpace.{max v u} Y] [T2Space Y] :
    Continuous (toContinuousMap (X := fun S : CompHaus.{max v u} ↦ S) (Y := Y) (T := T)) := by
  refine ContinuousMap.continuous_compactOpen.2 fun K hK U hU ↦ ?_
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let S : CompHaus.{max v u} := CompHaus.of (ULift.{u} K)
  let ιK : C(S, Y) := ⟨fun s ↦ s.down.1, continuous_subtype_val.comp continuous_uliftDown⟩
  have hopen : IsOpen ((precomp (X := fun R : CompHaus.{max v u} ↦ R) (T := T) ιK) ⁻¹'
      {f : C(S, T) | Set.range f ⊆ U}) :=
    (ContinuousMap.isOpen_setOfPred_range_subset hU).preimage
      (continuous_precomp (X := fun R : CompHaus.{max v u} ↦ R) ιK)
  convert hopen using 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.MapsTo, Set.mem_preimage, Set.range_subset_iff,
    precomp_apply, Function.comp_apply, toContinuousMap_apply]
  exact ⟨fun hg s ↦ hg s.down.2, fun hg x hx ↦ hg (ULift.up ⟨x, hx⟩)⟩

/-- **Exact compact-open comparison for Hausdorff sources**: when `Y : Type v` is Hausdorff and
`(max v u)`-compactly generated, `ContinuousMapGeneratedBy (fun S : CompHaus.{max v u} ↦ S) Y T` is
homeomorphic to `C(Y, T)` with the compact-open topology, for any target space `T : Type w`. -/
def homeomorphContinuousMapOfT2 {Y : Type v} {T : Type w}
    [TopologicalSpace Y] [TopologicalSpace T]
    [UCompactlyGeneratedSpace.{max v u} Y] [T2Space Y] :
    ContinuousMapGeneratedBy (fun S : CompHaus.{max v u} ↦ S) Y T ≃ₜ C(Y, T) where
  toEquiv := equivContinuousMap
  continuous_toFun := by
    rw [Equiv.toFun_as_coe]
    exact (funext (equivContinuousMap_apply
      (X := fun S : CompHaus.{max v u} ↦ S) (Y := Y) (T := T))) ▸
      continuous_toContinuousMap_of_t2Space
  continuous_invFun := by
    rw [Equiv.invFun_as_coe]
    exact (funext (equivContinuousMap_symm_apply
      (X := fun S : CompHaus.{max v u} ↦ S) (Y := Y) (T := T))) ▸
      ContinuousMap.continuous_toContinuousMapGeneratedBy

@[simp]
theorem homeomorphContinuousMapOfT2_apply {Y : Type v} {T : Type w}
    [TopologicalSpace Y] [TopologicalSpace T]
    [UCompactlyGeneratedSpace.{max v u} Y] [T2Space Y]
    (g : ContinuousMapGeneratedBy (fun S : CompHaus.{max v u} ↦ S) Y T) :
    homeomorphContinuousMapOfT2 g = g.toContinuousMap :=
  equivContinuousMap_apply g

@[simp]
theorem homeomorphContinuousMapOfT2_symm_apply {Y : Type v} {T : Type w}
    [TopologicalSpace Y] [TopologicalSpace T]
    [UCompactlyGeneratedSpace.{max v u} Y] [T2Space Y] (f : C(Y, T)) :
    (homeomorphContinuousMapOfT2.{u, v, w} (Y := Y) (T := T)).symm f =
      f.toContinuousMapGeneratedBy (fun S : CompHaus.{max v u} ↦ S) :=
  equivContinuousMap_symm_apply f

end Topology.ContinuousMapGeneratedBy

namespace TopCat

instance instT2SpaceToCompactlyGenerated (X : TopCat.{w}) [T2Space X] :
    T2Space ↑(TopCat.toCompactlyGenerated.{u, w}.obj X) :=
  inferInstanceAs (T2Space (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) X))

end TopCat

/-! ### Chosen finite products and cartesian monoidal closed structure on `CompactlyGenerated` -/

namespace CompactlyGenerated

instance instLocallyCompactSpaceToGeneratedByTopCat (X : CompactlyGenerated.{u, w})
    [LocallyCompactSpace X] : LocallyCompactSpace (toGeneratedByTopCat.{u, w}.obj X) :=
  ‹LocallyCompactSpace X›

/-- The one-point space `PUnit` is terminal in `CompactlyGenerated.{u, w}`. -/
@[expose]
def isTerminalPUnit : IsTerminal (of.{u, w} PUnit.{w + 1}) :=
  IsTerminal.ofUniqueHom
    (fun _ ↦ InducedCategory.homMk (TopCat.ofHom ⟨fun _ ↦ PUnit.unit, continuous_const⟩))
    (fun _ _ ↦ by ext x)

/-- First projection from `TopCat.toCompactlyGenerated.obj (TopCat.of (X × Y))` onto `X`. -/
@[expose]
def prodFst (X Y : CompactlyGenerated.{u, w}) :
    TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of (X × Y)) ⟶ X :=
  InducedCategory.homMk <| TopCat.ofHom
    ⟨Prod.fst ∘ WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := X × Y),
      continuous_fst.comp WithGeneratedByTopology.continuous_equiv⟩

/-- Second projection from `TopCat.toCompactlyGenerated.obj (TopCat.of (X × Y))` onto `Y`. -/
@[expose]
def prodSnd (X Y : CompactlyGenerated.{u, w}) :
    TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of (X × Y)) ⟶ Y :=
  InducedCategory.homMk <| TopCat.ofHom
    ⟨Prod.snd ∘ WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := X × Y),
      continuous_snd.comp WithGeneratedByTopology.continuous_equiv⟩

/-- The chosen binary product cone in `CompactlyGenerated.{u, w}`, with point
`TopCat.toCompactlyGenerated.obj (TopCat.of (X × Y))`. -/
@[expose]
def prodBinaryFan (X Y : CompactlyGenerated.{u, w}) : BinaryFan X Y :=
  BinaryFan.mk (prodFst X Y) (prodSnd X Y)

/-- `prodBinaryFan X Y` is a limit cone in `CompactlyGenerated.{u, w}`. -/
@[expose]
def prodBinaryFanIsLimit (X Y : CompactlyGenerated.{u, w}) :
    IsLimit (prodBinaryFan X Y) :=
  BinaryFan.IsLimit.mk (prodBinaryFan X Y)
    (fun {W} f g ↦ InducedCategory.homMk
      (Y := TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of (X × Y))) <| TopCat.ofHom
      ⟨fun w ↦ (WithGeneratedByTopology.equiv
          (X := fun K : CompHaus.{u} ↦ K) (Y := X × Y)).symm (f w, g w),
        (IsGeneratedBy.equiv_symm_comp_continuous_iff
          (X := fun K : CompHaus.{u} ↦ K) _).2
          (f.hom.hom.continuous.prodMk g.hom.hom.continuous)⟩)
    (fun _ _ ↦ by ext; rfl)
    (fun _ _ ↦ by ext; rfl)
    (fun {W} f g m h₁ h₂ ↦ by
      ext w
      apply (TopCat.toCompactlyGeneratedEquiv.{u, w} (TopCat.of (X × Y))).injective
      exact Prod.ext (congr($h₁ w)) (congr($h₂ w)))

/-- Chosen finite products on `CompactlyGenerated.{u, w}`, with unit `of PUnit` and binary product
`TopCat.toCompactlyGenerated.obj (TopCat.of (X × Y))`. -/
instance instCartesianMonoidalCategory :
    CartesianMonoidalCategory CompactlyGenerated.{u, w} :=
  .ofChosenFiniteProducts ⟨_, isTerminalPUnit⟩
    (fun X Y ↦ ⟨prodBinaryFan X Y, prodBinaryFanIsLimit X Y⟩)

instance instBraidedCategory : BraidedCategory CompactlyGenerated.{u, w} :=
  .ofCartesianMonoidalCategory

theorem tensorObj_def (X Y : CompactlyGenerated.{u, w}) :
    X ⊗ Y = TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of (X × Y)) :=
  (rfl)

theorem tensorUnit_def :
    𝟙_ CompactlyGenerated.{u, w} = of.{u, w} PUnit.{w + 1} :=
  (rfl)

@[simp]
theorem toGeneratedByTopCat_obj_tensor (X Y : CompactlyGenerated.{u, w}) :
    toGeneratedByTopCat.{u, w}.obj (X ⊗ Y) =
      toGeneratedByTopCat.{u, w}.obj X ⊗ toGeneratedByTopCat.{u, w}.obj Y :=
  (rfl)

@[simp]
theorem toGeneratedByTopCat_obj_unit :
    toGeneratedByTopCat.{u, w}.obj (𝟙_ CompactlyGenerated.{u, w}) =
      𝟙_ (GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)) :=
  (rfl)

/-- The canonical bijection identifying points of the convenient product `X ⊗ Y` in
`CompactlyGenerated.{u, w}` with pairs in `X × Y`. -/
@[expose]
def tensorEquiv (X Y : CompactlyGenerated.{u, w}) : ↑(X ⊗ Y) ≃ X × Y :=
  TopCat.toCompactlyGeneratedEquiv.{u, w} (TopCat.of (X × Y))

/-- The convenient product `X ⊗ Y` of two Hausdorff spaces in `CompactlyGenerated.{u, w}` is
Hausdorff, with no Hausdorffification step needed. -/
instance instT2SpaceTensor (X Y : CompactlyGenerated.{u, w}) [T2Space X] [T2Space Y] :
    T2Space ↑(X ⊗ Y) :=
  inferInstanceAs (T2Space ↑(TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of (X × Y))))

instance instNontrivialTensorLeft (X Y : CompactlyGenerated.{u, w}) [Nontrivial X] [Nonempty Y] :
    Nontrivial ↑(X ⊗ Y) :=
  (tensorEquiv X Y).nontrivial

instance instNontrivialTensorRight (X Y : CompactlyGenerated.{u, w}) [Nonempty X] [Nontrivial Y] :
    Nontrivial ↑(X ⊗ Y) :=
  (tensorEquiv X Y).nontrivial

@[ext]
theorem tensor_ext {X Y : CompactlyGenerated.{u, w}} {p q : ↑(X ⊗ Y)}
    (h : tensorEquiv X Y p = tensorEquiv X Y q) : p = q :=
  (tensorEquiv X Y).injective h

@[simp]
theorem fst_apply {X Y : CompactlyGenerated.{u, w}} (p : ↑(X ⊗ Y)) :
    fst X Y p = (tensorEquiv X Y p).1 :=
  (rfl)

@[simp]
theorem snd_apply {X Y : CompactlyGenerated.{u, w}} (p : ↑(X ⊗ Y)) :
    snd X Y p = (tensorEquiv X Y p).2 :=
  (rfl)

private theorem eq_tensorEquiv_symm {X Y : CompactlyGenerated.{u, w}} {p : ↑(X ⊗ Y)}
    {x : X} {y : Y} (h₁ : fst X Y p = x) (h₂ : snd X Y p = y) :
    p = (tensorEquiv X Y).symm (x, y) :=
  (tensorEquiv X Y).injective <|
    (Prod.ext h₁ h₂).trans ((tensorEquiv X Y).apply_symm_apply _).symm

@[simp]
theorem lift_apply {W X Y : CompactlyGenerated.{u, w}} (f : W ⟶ X) (g : W ⟶ Y) (w : W) :
    CartesianMonoidalCategory.lift f g w = (tensorEquiv X Y).symm (f w, g w) :=
  eq_tensorEquiv_symm congr($(lift_fst f g) w) congr($(lift_snd f g) w)

@[simp]
theorem tensor_apply {W₁ W₂ X Y : CompactlyGenerated.{u, w}}
    (f : W₁ ⟶ X) (g : W₂ ⟶ Y) (p : ↑(W₁ ⊗ W₂)) :
    (f ⊗ₘ g) p =
      (tensorEquiv X Y).symm (f (tensorEquiv W₁ W₂ p).1, g (tensorEquiv W₁ W₂ p).2) :=
  eq_tensorEquiv_symm congr($(tensorHom_fst f g) p) congr($(tensorHom_snd f g) p)

@[simp]
theorem whiskerLeft_apply (X : CompactlyGenerated.{u, w}) {Y₁ Y₂ : CompactlyGenerated.{u, w}}
    (g : Y₁ ⟶ Y₂) (p : ↑(X ⊗ Y₁)) :
    (X ◁ g) p =
      (tensorEquiv X Y₂).symm ((tensorEquiv X Y₁ p).1, g (tensorEquiv X Y₁ p).2) :=
  eq_tensorEquiv_symm congr($(whiskerLeft_fst X g) p) congr($(whiskerLeft_snd X g) p)

@[simp]
theorem whiskerRight_apply {X₁ X₂ : CompactlyGenerated.{u, w}} (f : X₁ ⟶ X₂)
    (Y : CompactlyGenerated.{u, w}) (p : ↑(X₁ ⊗ Y)) :
    (f ▷ Y) p =
      (tensorEquiv X₂ Y).symm (f (tensorEquiv X₁ Y p).1, (tensorEquiv X₁ Y p).2) :=
  eq_tensorEquiv_symm congr($(whiskerRight_fst f Y) p) congr($(whiskerRight_snd f Y) p)

@[simp]
theorem braiding_hom_apply {X Y : CompactlyGenerated.{u, w}} (p : ↑(X ⊗ Y)) :
    (β_ X Y).hom p = (tensorEquiv Y X).symm (tensorEquiv X Y p).swap :=
  eq_tensorEquiv_symm congr($(braiding_hom_fst X Y) p) congr($(braiding_hom_snd X Y) p)

@[simp]
theorem braiding_inv_apply {X Y : CompactlyGenerated.{u, w}} (p : ↑(Y ⊗ X)) :
    (β_ X Y).inv p = (tensorEquiv X Y).symm (tensorEquiv Y X p).swap :=
  eq_tensorEquiv_symm congr($(braiding_inv_fst X Y) p) congr($(braiding_inv_snd X Y) p)

@[simp]
theorem associator_inv_apply {X Y Z : CompactlyGenerated.{u, w}} (p : ↑(X ⊗ (Y ⊗ Z))) :
    (α_ X Y Z).inv p =
      (tensorEquiv (X ⊗ Y) Z).symm
        ((tensorEquiv X Y).symm
          ((tensorEquiv X _ p).1, (tensorEquiv Y Z (tensorEquiv X _ p).2).1),
          (tensorEquiv Y Z (tensorEquiv X _ p).2).2) := by
  refine eq_tensorEquiv_symm ?_ congr($(associator_inv_snd X Y Z) p)
  exact eq_tensorEquiv_symm
    congr($(associator_inv_fst_fst X Y Z) p)
    congr($(associator_inv_fst_snd X Y Z) p)

@[simp]
theorem leftUnitor_hom_apply {X : CompactlyGenerated.{u, w}}
    (p : ↑(𝟙_ CompactlyGenerated.{u, w} ⊗ X)) :
    (λ_ X).hom p = (tensorEquiv _ X p).2 :=
  (rfl)

@[simp]
theorem leftUnitor_inv_apply {X : CompactlyGenerated.{u, w}} (x : X) :
    (λ_ X).inv x = (tensorEquiv _ X).symm (PUnit.unit, x) :=
  eq_tensorEquiv_symm (PUnit.ext _ _) congr($(Iso.inv_hom_id (λ_ X)) x)

@[simp]
theorem rightUnitor_hom_apply {X : CompactlyGenerated.{u, w}}
    (p : ↑(X ⊗ 𝟙_ CompactlyGenerated.{u, w})) :
    (ρ_ X).hom p = (tensorEquiv X _ p).1 :=
  (rfl)

@[simp]
theorem rightUnitor_inv_apply {X : CompactlyGenerated.{u, w}} (x : X) :
    (ρ_ X).inv x = (tensorEquiv X _).symm (x, PUnit.unit) :=
  eq_tensorEquiv_symm congr($(Iso.inv_hom_id (ρ_ X)) x) (PUnit.ext _ _)

/-- Turn a morphism `X ⊗ Y ⟶ Z` in `CompactlyGenerated.{u, w}` into a
`(fun K : CompHaus.{u} ↦ K)`-continuous map `X × Y → Z`. -/
def homToContinuousMapGeneratedBy {X Y Z : CompactlyGenerated.{u, w}} (f : X ⊗ Y ⟶ Z) :
    ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) (X × Y) Z where
  toFun p := f ((tensorEquiv X Y).symm p)
  prop := by
    rw [continuousGeneratedBy_def]
    intro K r
    exact f.hom.hom.continuous.comp
      ((IsGeneratedBy.equiv_symm_comp_continuous_iff (X := fun S : CompHaus.{u} ↦ S) r).2
        r.continuous)

/-- Turn a `(fun K : CompHaus.{u} ↦ K)`-continuous map `X × Y → Z` into a morphism `X ⊗ Y ⟶ Z` in
`CompactlyGenerated.{u, w}`. -/
def continuousMapGeneratedByToHom {X Y Z : CompactlyGenerated.{u, w}}
    (g : ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) (X × Y) Z) : X ⊗ Y ⟶ Z :=
  InducedCategory.homMk <| TopCat.ofHom
    (X := WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (X × Y))
    ⟨g ∘ tensorEquiv X Y,
      (WithGeneratedByTopology.continuous_from_iff
        (X := fun K : CompHaus.{u} ↦ K) (Y := X × Y) _).2 fun _ r ↦ g.prop r⟩

/-- The internal hom functor on `CompactlyGenerated.{u, w}`, sending `Y` to the `u`-compactly
generated refinement of `ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) X Y`. -/
@[expose]
protected def ihom (X : CompactlyGenerated.{u, w}) :
    CompactlyGenerated.{u, w} ⥤ CompactlyGenerated.{u, w} where
  obj Y := TopCat.toCompactlyGenerated.{u, w}.obj
    (TopCat.of (ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) X Y))
  map {Y Y'} p := InducedCategory.homMk
    (X := TopCat.toCompactlyGenerated.{u, w}.obj
      (TopCat.of (ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) X Y)))
    (Y := TopCat.toCompactlyGenerated.{u, w}.obj
      (TopCat.of (ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) X Y'))) <|
    TopCat.ofHom ((ContinuousMapGeneratedBy.mk p.hom.hom
      p.hom.hom.continuous.continuousGeneratedBy).postcomp.prop.continuousMap)
  map_id Y := by
    ext g
    apply (TopCat.toCompactlyGeneratedEquiv.{u, w}
      (TopCat.of (ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) X Y))).injective
    exact ContinuousMapGeneratedBy.ext (funext fun _ ↦ rfl)
  map_comp {Y₁ Y₂ Y₃} _ _ := by
    ext g
    apply (TopCat.toCompactlyGeneratedEquiv.{u, w}
      (TopCat.of (ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) X Y₃))).injective
    exact ContinuousMapGeneratedBy.ext (funext fun _ ↦ rfl)

/-- Currying in `CompactlyGenerated.{u, w}`: morphisms `X ⊗ Y ⟶ Z` correspond naturally to
morphisms `Y ⟶ (CompactlyGenerated.ihom X).obj Z`. -/
def tensorHomEquiv (X Y Z : CompactlyGenerated.{u, w}) :
    (X ⊗ Y ⟶ Z) ≃ (Y ⟶ (CompactlyGenerated.ihom X).obj Z) where
  toFun f := InducedCategory.homMk (Y := (CompactlyGenerated.ihom X).obj Z) <| TopCat.ofHom
    ⟨fun y ↦ (WithGeneratedByTopology.equiv
        (X := fun K : CompHaus.{u} ↦ K)
        (Y := ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) X Z)).symm
        (ContinuousMapGeneratedBy.curryEquiv (homToContinuousMapGeneratedBy f) y),
      (IsGeneratedBy.equiv_symm_comp_continuous_iff
        (X := fun K : CompHaus.{u} ↦ K) _).2 <|
        (IsGeneratedBy.continuous_iff (fun K : CompHaus.{u} ↦ K) _).2
          (ContinuousMapGeneratedBy.curryEquiv (homToContinuousMapGeneratedBy f)).prop⟩
  invFun g := continuousMapGeneratedByToHom <|
    ContinuousMapGeneratedBy.curryEquiv.symm
      ⟨fun y ↦ WithGeneratedByTopology.equiv
          (X := fun K : CompHaus.{u} ↦ K)
          (Y := ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) X Z) (g y),
        ((WithGeneratedByTopology.continuous_equiv
          (X := fun K : CompHaus.{u} ↦ K)
          (Y := ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) X Z)).comp
          g.hom.hom.continuous).continuousGeneratedBy⟩
  left_inv f := by
    ext p
    exact congrArg f ((tensorEquiv X Y).symm_apply_apply p)
  right_inv g := by
    ext y
    apply (TopCat.toCompactlyGeneratedEquiv.{u, w}
      (TopCat.of (ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) X Z))).injective
    exact ContinuousMapGeneratedBy.ext (funext fun _ ↦ rfl)

theorem tensorHomEquiv_symm_comp {X Y Y' Z : CompactlyGenerated.{u, w}}
    (f : Y' ⟶ Y) (g : Y ⟶ (CompactlyGenerated.ihom X).obj Z) :
    (tensorHomEquiv X Y' Z).symm (f ≫ g) = X ◁ f ≫ (tensorHomEquiv X Y Z).symm g := by
  ext p
  change WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K)
      (Y := ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) X Z)
      (g (f (tensorEquiv X Y' p).2)) (tensorEquiv X Y' p).1 =
    WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K)
      (Y := ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) X Z)
      (g (tensorEquiv X Y ((X ◁ f) p)).2) (tensorEquiv X Y ((X ◁ f) p)).1
  rw [whiskerLeft_apply, Equiv.apply_symm_apply]

theorem tensorHomEquiv_comp {X Y Z Z' : CompactlyGenerated.{u, w}}
    (f : X ⊗ Y ⟶ Z) (g : Z ⟶ Z') :
    tensorHomEquiv X Y Z' (f ≫ g) =
      tensorHomEquiv X Y Z f ≫ (CompactlyGenerated.ihom X).map g := by
  ext y
  apply (TopCat.toCompactlyGeneratedEquiv.{u, w}
    (TopCat.of (ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) X Z'))).injective
  exact ContinuousMapGeneratedBy.ext (funext fun _ ↦ rfl)

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

theorem ihom_obj_def (X Y : CompactlyGenerated.{u, w}) :
    (ihom X).obj Y = TopCat.toCompactlyGenerated.{u, w}.obj
      (TopCat.of (ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) X Y)) :=
  (rfl)

/-- The canonical bijection identifying points of the internal hom `(ihom X).obj Y` in
`CompactlyGenerated.{u, w}` with `(fun K : CompHaus.{u} ↦ K)`-continuous maps `X → Y`. -/
@[expose]
def ihomEquiv (X Y : CompactlyGenerated.{u, w}) :
    ↑((ihom X).obj Y) ≃ ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) X Y :=
  TopCat.toCompactlyGeneratedEquiv.{u, w}
    (TopCat.of (ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) X Y))

@[ext]
theorem ihom_obj_ext {X Y : CompactlyGenerated.{u, w}} {f g : ↑((ihom X).obj Y)}
    (h : ∀ x, ihomEquiv X Y f x = ihomEquiv X Y g x) : f = g :=
  (ihomEquiv X Y).injective (DFunLike.ext _ _ h)

@[simp]
theorem ihom_map_apply {X Y Y' : CompactlyGenerated.{u, w}} (p : Y ⟶ Y')
    (g : ↑((ihom X).obj Y)) (x : X) :
    ihomEquiv X Y' ((ihom X).map p g) x = p (ihomEquiv X Y g x) :=
  (rfl)

@[simp]
theorem tensorHomEquiv_apply_apply {X Y Z : CompactlyGenerated.{u, w}}
    (f : X ⊗ Y ⟶ Z) (y : Y) (x : X) :
    ihomEquiv X Z (tensorHomEquiv X Y Z f y) x = f ((tensorEquiv X Y).symm (x, y)) :=
  (rfl)

@[simp]
theorem tensorHomEquiv_symm_apply {X Y Z : CompactlyGenerated.{u, w}}
    (g : Y ⟶ (CompactlyGenerated.ihom X).obj Z) (p : ↑(X ⊗ Y)) :
    (tensorHomEquiv X Y Z).symm g p =
      ihomEquiv X Z (g (tensorEquiv X Y p).2) (tensorEquiv X Y p).1 :=
  (rfl)

@[simp]
theorem curry_apply {X Y Z : CompactlyGenerated.{u, w}} (f : X ⊗ Y ⟶ Z) (y : Y) (x : X) :
    ihomEquiv X Z (MonoidalClosed.curry f y) x = f ((tensorEquiv X Y).symm (x, y)) := by
  rw [← MonoidalClosed.homEquiv_apply_eq, homEquiv_def]
  exact tensorHomEquiv_apply_apply f y x

@[simp]
theorem uncurry_apply {X Y Z : CompactlyGenerated.{u, w}}
    (g : Y ⟶ (ihom X).obj Z) (p : ↑(X ⊗ Y)) :
    MonoidalClosed.uncurry g p =
      ihomEquiv X Z (g (tensorEquiv X Y p).2) (tensorEquiv X Y p).1 := by
  rw [← MonoidalClosed.homEquiv_symm_apply_eq, homEquiv_def]
  exact tensorHomEquiv_symm_apply g p

@[simp]
theorem ihom_ev_app_apply {X Y : CompactlyGenerated.{u, w}}
    (p : ↑(X ⊗ (ihom X).obj Y)) :
    dsimp% (ihom.ev X).app Y p =
      ihomEquiv X Y (tensorEquiv X _ p).2 (tensorEquiv X _ p).1 := by
  rw [← MonoidalClosed.uncurry_id_eq_ev, uncurry_apply]
  rfl

@[simp]
theorem ihom_coev_app_apply {X Y : CompactlyGenerated.{u, w}} (y : Y) (x : X) :
    dsimp% ihomEquiv X (X ⊗ Y) ((ihom.coev X).app Y y) x = (tensorEquiv X Y).symm (x, y) := by
  rw [ihom.coev, ← Adjunction.homEquiv_id, homEquiv_def]
  exact tensorHomEquiv_apply_apply (𝟙 _) y x

@[simp]
theorem pre_app_apply {X₁ X₂ Y : CompactlyGenerated.{u, w}} (f : X₂ ⟶ X₁)
    (g : ↑((ihom X₁).obj Y)) (x₂ : X₂) :
    ihomEquiv X₂ Y ((MonoidalClosed.pre f).app Y g) x₂ = ihomEquiv X₁ Y g (f x₂) := by
  have h := congr($(MonoidalClosed.uncurry_pre f Y) ((tensorEquiv X₂ _).symm (x₂, g)))
  rw [uncurry_apply, Equiv.apply_symm_apply, comp_apply, whiskerRight_apply,
    Equiv.apply_symm_apply] at h
  dsimp at h
  rw [ihom_ev_app_apply, Equiv.apply_symm_apply] at h
  exact h

/-- **Braided internal currying** in `CompactlyGenerated.{u, w}`:
`(ihom (X ⊗ Y)).obj Z ≅ (ihom X).obj ((ihom Y).obj Z)`, sending `f : X ⊗ Y ⟶ Z` to
`x ↦ (y ↦ f (x, y))`. -/
def ihomTensorIso (X Y Z : CompactlyGenerated.{u, w}) :
    (ihom (X ⊗ Y)).obj Z ≅ (ihom X).obj ((ihom Y).obj Z) :=
  (MonoidalClosed.internalHom.mapIso (β_ Y X).op).app Z ≪≫
    MonoidalClosed.ihomCurryIso Y X Z

@[simp]
theorem ihomTensorIso_hom_apply (X Y Z : CompactlyGenerated.{u, w})
    (g : ↑((ihom (X ⊗ Y)).obj Z)) (x : X) (y : Y) :
    ihomEquiv Y Z (ihomEquiv X ((ihom Y).obj Z) ((ihomTensorIso X Y Z).hom g) x) y =
      ihomEquiv (X ⊗ Y) Z g ((tensorEquiv X Y).symm (x, y)) := by
  have hhom : (ihomTensorIso X Y Z).hom =
      (MonoidalClosed.pre (β_ Y X).hom).app Z ≫ MonoidalClosed.ihomCurry Y X Z := rfl
  rw [hhom, comp_apply]
  have h := congr($(MonoidalClosed.uncurry_uncurry_ihomCurry Y X Z)
    ((tensorEquiv Y (X ⊗ (ihom (Y ⊗ X)).obj Z)).symm
      (y, (tensorEquiv X ((ihom (Y ⊗ X)).obj Z)).symm
        (x, (MonoidalClosed.pre (β_ Y X).hom).app Z g))))
  rw [uncurry_apply, Equiv.apply_symm_apply, uncurry_apply, Equiv.apply_symm_apply,
    comp_apply, associator_inv_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  dsimp at h
  rw [ihom_ev_app_apply, Equiv.apply_symm_apply, pre_app_apply, braiding_hom_apply,
    Equiv.apply_symm_apply] at h
  exact h

/-! ### Product and compact-open mapping space comparisons -/

/-- The canonical comparison morphism `(X ⊗ Y).toTop ⟶ X.toTop ⊗ Y.toTop` in `TopCat.{w}`, given
by the counit `adjCounit.app (X.toTop ⊗ Y.toTop)`. -/
@[expose]
def prodComparisonHom (X Y : CompactlyGenerated.{u, w}) :
    (X ⊗ Y).toTop ⟶ X.toTop ⊗ Y.toTop :=
  GeneratedByTopCat.prodComparisonHom
    (toGeneratedByTopCat.{u, w}.obj X) (toGeneratedByTopCat.{u, w}.obj Y)

@[simp]
theorem prodComparisonHom_apply (X Y : CompactlyGenerated.{u, w}) (p : ↑(X ⊗ Y)) :
    prodComparisonHom X Y p = tensorEquiv X Y p :=
  WithGeneratedByTopology.counit_apply (fun K : CompHaus.{u} ↦ K) (X := X × Y) p

/-- When `X` is locally compact, the convenient product `X ⊗ Y` in `CompactlyGenerated.{u, w}` has
the ordinary product topology in `TopCat.{w}`. -/
@[expose]
def prodComparisonIsoOfLocallyCompactLeft (X Y : CompactlyGenerated.{u, w})
    [LocallyCompactSpace X] :
    (X ⊗ Y).toTop ≅ X.toTop ⊗ Y.toTop :=
  GeneratedByTopCat.prodComparisonIsoOfLocallyCompactLeft
    (toGeneratedByTopCat.{u, w}.obj X) (toGeneratedByTopCat.{u, w}.obj Y)

@[simp]
theorem prodComparisonIsoOfLocallyCompactLeft_hom (X Y : CompactlyGenerated.{u, w})
    [LocallyCompactSpace X] :
    (prodComparisonIsoOfLocallyCompactLeft X Y).hom = prodComparisonHom X Y :=
  GeneratedByTopCat.prodComparisonIsoOfLocallyCompactLeft_hom
    (toGeneratedByTopCat.{u, w}.obj X) (toGeneratedByTopCat.{u, w}.obj Y)

/-- When `Y` is locally compact, the convenient product `X ⊗ Y` in `CompactlyGenerated.{u, w}` has
the ordinary product topology in `TopCat.{w}`. -/
@[expose]
def prodComparisonIsoOfLocallyCompactRight (X Y : CompactlyGenerated.{u, w})
    [LocallyCompactSpace Y] :
    (X ⊗ Y).toTop ≅ X.toTop ⊗ Y.toTop :=
  GeneratedByTopCat.prodComparisonIsoOfLocallyCompactRight
    (toGeneratedByTopCat.{u, w}.obj X) (toGeneratedByTopCat.{u, w}.obj Y)

@[simp]
theorem prodComparisonIsoOfLocallyCompactRight_hom (X Y : CompactlyGenerated.{u, w})
    [LocallyCompactSpace Y] :
    (prodComparisonIsoOfLocallyCompactRight X Y).hom = prodComparisonHom X Y :=
  GeneratedByTopCat.prodComparisonIsoOfLocallyCompactRight_hom
    (toGeneratedByTopCat.{u, w}.obj X) (toGeneratedByTopCat.{u, w}.obj Y)

/-- **Compact-open internal hom comparison**: for arbitrary universes `u, w` and arbitrary
`X, Y : CompactlyGenerated.{u, w}` (with no local compactness or Hausdorffness assumption),
`(ihom X).obj Y` is canonically isomorphic to `TopCat.toCompactlyGenerated.obj (TopCat.of C(X, Y))`
where `C(X, Y)` carries the compact-open topology. -/
def ihomIsoCompactOpen (X Y : CompactlyGenerated.{u, w}) :
    (ihom X).obj Y ≅ TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(X, Y)) :=
  fromGeneratedByTopCat.{u, w}.mapIso <|
    GeneratedByTopCat.ihomIsoCompactOpen
      (toGeneratedByTopCat.{u, w}.obj X) (toGeneratedByTopCat.{u, w}.obj Y)

@[simp]
theorem ihomIsoCompactOpen_hom_apply (X Y : CompactlyGenerated.{u, w})
    (g : ↑((ihom X).obj Y)) (x : X) :
    (TopCat.toCompactlyGeneratedEquiv.{u, w} (TopCat.of C(X, Y))
      ((ihomIsoCompactOpen X Y).hom g)) x = ihomEquiv X Y g x :=
  GeneratedByTopCat.ihomIsoCompactOpen_hom_apply
    (toGeneratedByTopCat.{u, w}.obj X) (toGeneratedByTopCat.{u, w}.obj Y) g x

@[simp]
theorem ihomIsoCompactOpen_inv_apply (X Y : CompactlyGenerated.{u, w})
    (f : ↑(TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(X, Y)))) (x : X) :
    ihomEquiv X Y ((ihomIsoCompactOpen X Y).inv f) x =
      (TopCat.toCompactlyGeneratedEquiv.{u, w} (TopCat.of C(X, Y)) f) x :=
  GeneratedByTopCat.ihomIsoCompactOpen_inv_apply
    (toGeneratedByTopCat.{u, w}.obj X) (toGeneratedByTopCat.{u, w}.obj Y) f x

/-- **Exponential law for compact-open mapping spaces in `CompactlyGenerated`**: for arbitrary
`X, Y, Z : CompactlyGenerated.{u, w}` (with no local compactness or Hausdorffness assumption), the
compactly generated refinements of the compact-open mapping spaces satisfy
`k C(↑(X ⊗ Y), Z) ≅ k C(X, ↑(k C(Y, Z)))`. -/
def compactOpenCurryIso (X Y Z : CompactlyGenerated.{u, w}) :
    TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(↑(X ⊗ Y), Z)) ≅
      TopCat.toCompactlyGenerated.{u, w}.obj
        (TopCat.of C(X, ↑(TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of C(Y, Z))))) :=
  (ihomIsoCompactOpen (X ⊗ Y) Z).symm ≪≫
    ihomTensorIso X Y Z ≪≫
    (ihom X).mapIso (ihomIsoCompactOpen Y Z) ≪≫
    ihomIsoCompactOpen X _

/-! ### Concrete checks on products and exponentials -/

/-- If `X` is nonempty and `Y` is nontrivial, the internal hom `(ihom X).obj Y` is nontrivial,
witnessed by two distinct constant maps. -/
instance instNontrivialIhom (X Y : CompactlyGenerated.{u, w}) [Nonempty X] [Nontrivial Y] :
    Nontrivial ↑((ihom X).obj Y) := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  obtain ⟨y₁, y₂, hy⟩ := exists_pair_ne Y
  refine ⟨(ihomEquiv X Y).symm ((ContinuousMap.const X y₁).toContinuousMapGeneratedBy _),
    (ihomEquiv X Y).symm ((ContinuousMap.const X y₂).toContinuousMapGeneratedBy _), fun h ↦ hy ?_⟩
  have hx := congrArg (fun g ↦ ihomEquiv X Y g x₀) h
  simpa only [Equiv.apply_symm_apply, ContinuousMap.toContinuousMapGeneratedBy_apply,
    ContinuousMap.const_apply] using hx

/-- The convenient product `of unitInterval ⊗ of unitInterval` in `CompactlyGenerated.{u, 0}` is
homeomorphic to the ordinary unit square `unitInterval × unitInterval`, since `unitInterval` is
compact and hence locally compact. -/
def unitSquareHomeomorph :
    ↑(of.{u, 0} unitInterval ⊗ of.{u, 0} unitInterval) ≃ₜ unitInterval × unitInterval :=
  TopCat.homeoOfIso
    (prodComparisonIsoOfLocallyCompactLeft (of.{u, 0} unitInterval) (of.{u, 0} unitInterval))

@[simp]
theorem unitSquareHomeomorph_apply
    (p : ↑(of.{u, 0} unitInterval ⊗ of.{u, 0} unitInterval)) :
    unitSquareHomeomorph.{u} p =
      tensorEquiv (of.{u, 0} unitInterval) (of.{u, 0} unitInterval) p :=
  (TopCat.homeoOfIso_apply _ p).trans <|
    congr($(prodComparisonIsoOfLocallyCompactLeft_hom
      (of.{u, 0} unitInterval) (of.{u, 0} unitInterval)) p).trans
      (prodComparisonHom_apply _ _ p)

@[simp]
theorem unitSquareHomeomorph_symm_apply (q : unitInterval × unitInterval) :
    unitSquareHomeomorph.{u}.symm q =
      (tensorEquiv (of.{u, 0} unitInterval) (of.{u, 0} unitInterval)).symm q := by
  apply unitSquareHomeomorph.{u}.injective
  rw [Homeomorph.apply_symm_apply, unitSquareHomeomorph_apply, Equiv.apply_symm_apply]

/-- Constant morphism `𝟙_ CompactlyGenerated.{u, 0} ⟶ of Bool` picking out `b : Bool`. -/
def boolConstHom (b : Bool) : 𝟙_ CompactlyGenerated.{u, 0} ⟶ of.{u, 0} Bool :=
  InducedCategory.homMk (TopCat.ofHom ⟨fun _ ↦ b, continuous_const⟩)

@[simp]
theorem boolConstHom_apply (b : Bool) (p : ↑(𝟙_ CompactlyGenerated.{u, 0})) :
    boolConstHom.{u} b p = b :=
  (rfl)

/-- Evaluation of `(ihom (of Bool)).obj Y` at a boolean `b : Bool`. -/
def boolEvalHom (Y : CompactlyGenerated.{u, 0}) (b : Bool) :
    (ihom (of.{u, 0} Bool)).obj Y ⟶ Y :=
  (λ_ _).inv ≫ (boolConstHom.{u} b ▷ _) ≫ (ihom.ev (of.{u, 0} Bool)).app Y

@[simp]
theorem boolEvalHom_apply (Y : CompactlyGenerated.{u, 0}) (b : Bool)
    (g : ↑((ihom (of.{u, 0} Bool)).obj Y)) :
    boolEvalHom Y b g = ihomEquiv (of.{u, 0} Bool) Y g b := by
  rw [boolEvalHom, comp_apply, comp_apply, leftUnitor_inv_apply, whiskerRight_apply,
    Equiv.apply_symm_apply, boolConstHom_apply]
  dsimp
  rw [ihom_ev_app_apply, Equiv.apply_symm_apply]

/-- Case-analysis morphism `of Bool ⊗ (Y ⊗ Y) ⟶ Y` selecting the first coordinate on `false` and
the second coordinate on `true`. -/
def boolCasesHom (Y : CompactlyGenerated.{u, 0}) :
    of.{u, 0} Bool ⊗ (Y ⊗ Y) ⟶ Y :=
  InducedCategory.homMk <|
    prodComparisonHom (of.{u, 0} Bool) (Y ⊗ Y) ≫
      TopCat.ofHom ⟨fun q : Bool × ↑(Y ⊗ Y) ↦ Bool.rec (fst Y Y q.2) (snd Y Y q.2) q.1,
        continuous_prod_of_discrete_left.2 <|
          Bool.rec (fst Y Y).hom.hom.continuous (snd Y Y).hom.hom.continuous⟩

@[simp]
theorem boolCasesHom_apply (Y : CompactlyGenerated.{u, 0}) (p : ↑(of.{u, 0} Bool ⊗ (Y ⊗ Y))) :
    boolCasesHom Y p =
      Bool.rec (fst Y Y (tensorEquiv (of.{u, 0} Bool) (Y ⊗ Y) p).2)
        (snd Y Y (tensorEquiv (of.{u, 0} Bool) (Y ⊗ Y) p).2)
        (tensorEquiv (of.{u, 0} Bool) (Y ⊗ Y) p).1 :=
  congrArg (fun q : Bool × ↑(Y ⊗ Y) ↦
      Bool.rec (motive := fun _ ↦ Y) (fst Y Y q.2) (snd Y Y q.2) q.1)
    (prodComparisonHom_apply (of.{u, 0} Bool) (Y ⊗ Y) p)

/-- For every `Y : CompactlyGenerated.{u, 0}`, the internal hom `(ihom (of Bool)).obj Y` out of the
discrete two-point space `Bool` is isomorphic to the convenient square `Y ⊗ Y`. -/
def boolIhomIso (Y : CompactlyGenerated.{u, 0}) :
    (ihom (of.{u, 0} Bool)).obj Y ≅ Y ⊗ Y where
  hom := CartesianMonoidalCategory.lift (boolEvalHom Y false) (boolEvalHom Y true)
  inv := MonoidalClosed.curry (boolCasesHom Y)
  hom_inv_id := by
    ext g b
    rw [comp_apply, id_apply, lift_apply, curry_apply, boolCasesHom_apply, Equiv.apply_symm_apply]
    cases b <;> simp only [fst_apply, snd_apply, Equiv.apply_symm_apply, boolEvalHom_apply]
  inv_hom_id := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · ext p
      rw [Category.assoc, lift_fst, Category.id_comp, comp_apply, boolEvalHom_apply,
        curry_apply, boolCasesHom_apply, Equiv.apply_symm_apply]
    · ext p
      rw [Category.assoc, lift_snd, Category.id_comp, comp_apply, boolEvalHom_apply,
        curry_apply, boolCasesHom_apply, Equiv.apply_symm_apply]

@[simp]
theorem boolIhomIso_hom_apply (Y : CompactlyGenerated.{u, 0})
    (g : ↑((ihom (of.{u, 0} Bool)).obj Y)) :
    tensorEquiv Y Y ((boolIhomIso Y).hom g) =
      (ihomEquiv (of.{u, 0} Bool) Y g false, ihomEquiv (of.{u, 0} Bool) Y g true) := by
  rw [boolIhomIso, lift_apply, Equiv.apply_symm_apply, boolEvalHom_apply, boolEvalHom_apply]

@[simp]
theorem boolIhomIso_inv_apply (Y : CompactlyGenerated.{u, 0}) (p : ↑(Y ⊗ Y)) (b : Bool) :
    ihomEquiv (of.{u, 0} Bool) Y ((boolIhomIso Y).inv p) b =
      Bool.rec (fst Y Y p) (snd Y Y p) b := by
  rw [boolIhomIso, curry_apply, boolCasesHom_apply, Equiv.apply_symm_apply]

end CompactlyGenerated

end
