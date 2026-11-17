/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
public import Mathlib.Topology.Category.TopCat.Monoidal
public import TauCeti.Topology.Convenient.Category
public import TauCeti.Topology.Convenient.HomSpace

/-!
# Cartesian monoidal closed structure on `GeneratedByTopCat`

For any generating family of topological spaces `X : ι → Type u`, the coreflective full
subcategory `GeneratedByTopCat.{v} X` of `X`-generated spaces in `TopCat.{v}` has chosen finite
products: the one-point space `PUnit` is terminal, and the binary product of `Y` and `Z` is the
`X`-generated refinement `WithGeneratedByTopology X (Y × Z)` of their topological product, with
projections factoring through the counit (`GeneratedByTopCat.instCartesianMonoidalCategory`). The
canonical comparison `CartesianMonoidalCategory.prodComparison toTopCat Y Z` in `TopCat` is the
counit on `Y × Z` (`GeneratedByTopCat.prodComparison_toTopCat`), so it is an isomorphism if and
only if `Y × Z` is already `X`-generated (`GeneratedByTopCat.isIso_prodComparison_toTopCat_iff`,
`GeneratedByTopCat.tensorHomeomorphProd`).

When each generator `X i` is locally compact and each product `X i × X j` is `X`-generated,
currying via `Topology.ContinuousMapGeneratedBy.curryEquiv` makes `GeneratedByTopCat.{v} X`
cartesian closed (`GeneratedByTopCat.instMonoidalClosed`): the internal hom `(ihom Y).obj Z` is
the `X`-generated refinement of `ContinuousMapGeneratedBy X Y Z`. Moreover:

* if either factor is locally compact, `Y × Z` is already `X`-generated and `Y ⊗ Z` has the
  ordinary product topology (`GeneratedByTopCat.tensorHomeomorphProdOfLocallyCompactRight`,
  `GeneratedByTopCat.tensorHomeomorphProdOfLocallyCompactLeft`);
* if every compact subset of `Y` is a finite union of continuous images of compact subsets of
  generators `X i`, then `(ihom Y).obj Z` is canonically isomorphic to the `X`-generated refinement
  of the compact-open mapping space `C(Y, Z)`
  (`GeneratedByTopCat.ihomIsoCompactOpenOfExistsIUnionIsCompactImageEq`).

## References

* M. Escardó, J. Lawson, and A. Simpson, *Comparing Cartesian closed categories of (core)
  compactly generated spaces*, Topology Appl. 143 (2004), 105–145.
* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Arch. Math.
  (Basel) 22 (1971), 545–555.
-/

public section

universe w v t u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Topology

namespace GeneratedByTopCat

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]

/-- `PUnit` is terminal in `GeneratedByTopCat`. -/
def isTerminalPUnit : IsTerminal (of (X := X) PUnit.{v + 1}) :=
  IsTerminal.ofUniqueHom
    (fun _ ↦ ofHom ⟨fun _ ↦ PUnit.unit, continuous_const⟩) (fun _ _ ↦ by ext)

/-- The explicit binary fan of `Y` and `Z` in `GeneratedByTopCat X` with apex
`WithGeneratedByTopology X (Y × Z)`.

Exposed so that downstream modules and code generation agree on the carrier type of `Y ⊗ Z`. -/
@[expose] def prodBinaryFan (Y Z : GeneratedByTopCat.{v} X) : BinaryFan Y Z :=
  BinaryFan.mk (P := of (X := X) (WithGeneratedByTopology X (Y × Z)))
    (ofHom ⟨fun p ↦ (WithGeneratedByTopology.equiv (X := X) (Y := Y × Z) p).1,
      continuous_fst.comp (WithGeneratedByTopology.continuous_equiv (X := X) (Y := Y × Z))⟩)
    (ofHom ⟨fun p ↦ (WithGeneratedByTopology.equiv (X := X) (Y := Y × Z) p).2,
      continuous_snd.comp (WithGeneratedByTopology.continuous_equiv (X := X) (Y := Y × Z))⟩)

theorem prodBinaryFan_pt (Y Z : GeneratedByTopCat.{v} X) :
    (prodBinaryFan Y Z).pt = of (X := X) (WithGeneratedByTopology X (Y × Z)) := (rfl)

@[simp] theorem prodBinaryFan_fst_apply (Y Z : GeneratedByTopCat.{v} X)
    (p : ↑(prodBinaryFan Y Z).pt) :
    (prodBinaryFan Y Z).fst p = (WithGeneratedByTopology.equiv (X := X) (Y := Y × Z) p).1 := (rfl)

@[simp] theorem prodBinaryFan_snd_apply (Y Z : GeneratedByTopCat.{v} X)
    (p : ↑(prodBinaryFan Y Z).pt) :
    (prodBinaryFan Y Z).snd p = (WithGeneratedByTopology.equiv (X := X) (Y := Y × Z) p).2 := (rfl)

private def prodBinaryFanLift {W Y Z : GeneratedByTopCat.{v} X} (f : W ⟶ Y) (g : W ⟶ Z) :
    W ⟶ (prodBinaryFan Y Z).pt :=
  ofHom ((f.hom.hom.prodMk g.hom.hom).toGeneratedBy X)

private theorem equiv_prodBinaryFanLift_apply {W Y Z : GeneratedByTopCat.{v} X}
    (f : W ⟶ Y) (g : W ⟶ Z) (w : W) :
    WithGeneratedByTopology.equiv (X := X) (Y := Y × Z) (prodBinaryFanLift f g w) = (f w, g w) :=
  (congrArg (WithGeneratedByTopology.equiv (X := X) (Y := Y × Z))
    (ContinuousMap.toGeneratedBy_apply (f.hom.hom.prodMk g.hom.hom) w)).trans
    (Equiv.apply_symm_apply _ _)

/-- `WithGeneratedByTopology X (Y × Z)` is a binary product of `Y` and `Z` in
`GeneratedByTopCat X`. -/
def prodBinaryFanIsLimit (Y Z : GeneratedByTopCat.{v} X) : IsLimit (prodBinaryFan Y Z) :=
  BinaryFan.IsLimit.mk _
    (fun {_} f g ↦ prodBinaryFanLift f g)
    (fun f g ↦ by ext w; rw [comp_apply, prodBinaryFan_fst_apply, equiv_prodBinaryFanLift_apply])
    (fun f g ↦ by ext w; rw [comp_apply, prodBinaryFan_snd_apply, equiv_prodBinaryFanLift_apply])
    (fun {_} f g m h₁ h₂ ↦ by
      ext w
      apply (WithGeneratedByTopology.equiv (X := X) (Y := Y × Z)).injective
      rw [equiv_prodBinaryFanLift_apply]
      exact Prod.ext
        ((prodBinaryFan_fst_apply Y Z (m w)).symm.trans (ConcreteCategory.congr_hom h₁ w))
        ((prodBinaryFan_snd_apply Y Z (m w)).symm.trans (ConcreteCategory.congr_hom h₂ w)))

instance instCartesianMonoidalCategory : CartesianMonoidalCategory (GeneratedByTopCat.{v} X) :=
  .ofChosenFiniteProducts ⟨_, isTerminalPUnit⟩
    (fun Y Z ↦ ⟨prodBinaryFan Y Z, prodBinaryFanIsLimit Y Z⟩)

instance instBraidedCategory : BraidedCategory (GeneratedByTopCat.{v} X) :=
  .ofCartesianMonoidalCategory

instance : Subsingleton ↑(𝟙_ (GeneratedByTopCat.{v} X)) :=
  inferInstanceAs (Subsingleton PUnit.{v + 1})

instance (Y Z : GeneratedByTopCat.{v} X) [T2Space Y] [T2Space Z] : T2Space ↑(Y ⊗ Z) :=
  inferInstanceAs (T2Space (WithGeneratedByTopology X (Y × Z)))

instance (Y Z : GeneratedByTopCat.{v} X) [Small.{w} Y] [Small.{w} Z] : Small.{w} ↑(Y ⊗ Z) :=
  inferInstanceAs (Small.{w} (WithGeneratedByTopology X (Y × Z)))

/-- The underlying bijection between the convenient product `Y ⊗ Z` and `Y × Z`. -/
def tensorEquiv (Y Z : GeneratedByTopCat.{v} X) : ↑(Y ⊗ Z) ≃ Y × Z :=
  WithGeneratedByTopology.equiv (X := X) (Y := Y × Z)

@[continuity, fun_prop]
theorem continuous_tensorEquiv (Y Z : GeneratedByTopCat.{v} X) : Continuous (tensorEquiv Y Z) :=
  WithGeneratedByTopology.continuous_equiv

section Pointwise

variable {W Y Z : GeneratedByTopCat.{v} X}

@[simp] theorem tensorEquiv_fst (p : ↑(Y ⊗ Z)) : (tensorEquiv Y Z p).1 = fst Y Z p := (rfl)

@[simp] theorem tensorEquiv_snd (p : ↑(Y ⊗ Z)) : (tensorEquiv Y Z p).2 = snd Y Z p := (rfl)

@[simp] theorem fst_tensorEquiv_symm (y : Y) (z : Z) :
    fst Y Z ((tensorEquiv Y Z).symm (y, z)) = y := by
  rw [← tensorEquiv_fst, Equiv.apply_symm_apply]

@[simp] theorem snd_tensorEquiv_symm (y : Y) (z : Z) :
    snd Y Z ((tensorEquiv Y Z).symm (y, z)) = z := by
  rw [← tensorEquiv_snd, Equiv.apply_symm_apply]

@[simp] theorem tensorEquiv_symm_fst_snd (p : ↑(Y ⊗ Z)) :
    (tensorEquiv Y Z).symm (fst Y Z p, snd Y Z p) = p := by
  rw [← tensorEquiv_fst, ← tensorEquiv_snd, Prod.mk.eta, Equiv.symm_apply_apply]

@[ext] theorem tensorObj_ext {p q : ↑(Y ⊗ Z)}
    (h₁ : fst Y Z p = fst Y Z q) (h₂ : snd Y Z p = snd Y Z q) : p = q :=
  (tensorEquiv Y Z).injective (Prod.ext (by simpa using h₁) (by simpa using h₂))

@[simp] theorem lift_apply (f : W ⟶ Y) (g : W ⟶ Z) (w : W) :
    lift f g w = (tensorEquiv Y Z).symm (f w, g w) := by
  apply (tensorEquiv Y Z).injective; ext <;> simp [← comp_apply]

theorem tensorEquiv_lift_apply (f : W ⟶ Y) (g : W ⟶ Z) (w : W) :
    tensorEquiv Y Z (lift f g w) = (f w, g w) := by simp

@[simp] theorem tensorHom_apply {W₁ W₂ Y₁ Y₂ : GeneratedByTopCat.{v} X}
    (f : W₁ ⟶ W₂) (g : Y₁ ⟶ Y₂) (p : ↑(W₁ ⊗ Y₁)) :
    (f ⊗ₘ g) p = (tensorEquiv W₂ Y₂).symm (f (fst W₁ Y₁ p), g (snd W₁ Y₁ p)) := by
  apply (tensorEquiv W₂ Y₂).injective; ext <;> simp [← comp_apply]

@[simp] theorem braiding_hom_apply (p : ↑(Y ⊗ Z)) :
    (β_ Y Z).hom p = (tensorEquiv Z Y).symm (snd Y Z p, fst Y Z p) := by
  apply (tensorEquiv Z Y).injective; ext <;> simp [← comp_apply]

@[simp] theorem braiding_inv_apply (p : ↑(Z ⊗ Y)) :
    (β_ Y Z).inv p = (tensorEquiv Y Z).symm (snd Z Y p, fst Z Y p) := by
  apply (tensorEquiv Y Z).injective; ext <;> simp [← comp_apply]

@[simp] theorem leftUnitor_hom_apply (p : ↑(𝟙_ (GeneratedByTopCat.{v} X) ⊗ Y)) :
    (λ_ Y).hom p = snd _ Y p := (rfl)

@[simp] theorem leftUnitor_inv_apply (y : Y) :
    (λ_ Y).inv y = (tensorEquiv _ Y).symm (PUnit.unit, y) := by
  ext; exacts [Subsingleton.elim _ _, by simp [← comp_apply]]

@[simp] theorem rightUnitor_hom_apply (p : ↑(Y ⊗ 𝟙_ (GeneratedByTopCat.{v} X))) :
    (ρ_ Y).hom p = fst Y _ p := (rfl)

@[simp] theorem rightUnitor_inv_apply (y : Y) :
    (ρ_ Y).inv y = (tensorEquiv Y _).symm (y, PUnit.unit) := by
  ext; exacts [by simp [← comp_apply], Subsingleton.elim _ _]

@[simp] theorem associator_hom_apply (p : ↑((W ⊗ Y) ⊗ Z)) :
    (α_ W Y Z).hom p =
      (tensorEquiv W (Y ⊗ Z)).symm
        (fst W Y (fst (W ⊗ Y) Z p),
          (tensorEquiv Y Z).symm (snd W Y (fst (W ⊗ Y) Z p), snd (W ⊗ Y) Z p)) := by
  ext
  · rw [← comp_apply, associator_hom_fst]; simp
  · rw [← comp_apply, ← comp_apply, associator_hom_snd_fst]; simp
  · rw [← comp_apply, ← comp_apply, associator_hom_snd_snd]; simp

@[simp] theorem associator_inv_apply (p : ↑(W ⊗ (Y ⊗ Z))) :
    (α_ W Y Z).inv p =
      (tensorEquiv (W ⊗ Y) Z).symm
        ((tensorEquiv W Y).symm (fst W (Y ⊗ Z) p, fst Y Z (snd W (Y ⊗ Z) p)),
          snd Y Z (snd W (Y ⊗ Z) p)) := by
  ext
  · rw [← comp_apply, ← comp_apply, associator_inv_fst_fst]; simp
  · rw [← comp_apply, ← comp_apply, associator_inv_fst_snd]; simp
  · rw [← comp_apply, associator_inv_snd]; simp

end Pointwise

@[simp] theorem whiskerLeft_apply (W : GeneratedByTopCat.{v} X) {Y Z : GeneratedByTopCat.{v} X}
    (f : Y ⟶ Z) (p : ↑(W ⊗ Y)) :
    (W ◁ f) p = (tensorEquiv W Z).symm (fst W Y p, f (snd W Y p)) := by
  apply (tensorEquiv W Z).injective; ext <;> simp [← comp_apply]

@[simp] theorem whiskerRight_apply {W Y : GeneratedByTopCat.{v} X} (f : W ⟶ Y)
    (Z : GeneratedByTopCat.{v} X) (p : ↑(W ⊗ Z)) :
    (f ▷ Z) p = (tensorEquiv Y Z).symm (f (fst W Z p), snd W Z p) := by
  apply (tensorEquiv Y Z).injective; ext <;> simp [← comp_apply]

section ProdComparison

variable (Y Z : GeneratedByTopCat.{v} X)

/-- The canonical product comparison `toTopCat.obj (Y ⊗ Z) ⟶ toTopCat.obj Y ⊗ toTopCat.obj Z` in
`TopCat` is the generated-topology counit on `Y × Z`. -/
theorem prodComparison_toTopCat :
    CartesianMonoidalCategory.prodComparison toTopCat Y Z =
      (adjCounit (X := X)).app (Y.obj ⊗ Z.obj) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [CartesianMonoidalCategory.prodComparison_fst]; ext p; exact (tensorEquiv_fst p).symm
  · rw [CartesianMonoidalCategory.prodComparison_snd]; ext p; exact (tensorEquiv_snd p).symm

@[simp] theorem prodComparison_toTopCat_apply (p : ↑(Y ⊗ Z)) :
    ConcreteCategory.hom (X := (Y ⊗ Z).obj) (Y := Y.obj ⊗ Z.obj)
      (CartesianMonoidalCategory.prodComparison toTopCat Y Z) p = tensorEquiv Y Z p := by
  rw [prodComparison_toTopCat]; rfl

/-- The convenient product `Y ⊗ Z` has the ordinary product topology if and only if `Y × Z` is
`X`-generated. -/
theorem isIso_prodComparison_toTopCat_iff :
    IsIso (CartesianMonoidalCategory.prodComparison toTopCat Y Z) ↔ IsGeneratedBy X (Y × Z) := by
  rw [prodComparison_toTopCat]; exact isIso_adjCounit_app_iff X (Y.obj ⊗ Z.obj)

/-- When `Y × Z` is `X`-generated, the product comparison in `TopCat` is an isomorphism. -/
instance instIsIsoProdComparisonToTopCat [IsGeneratedBy X (Y × Z)] :
    IsIso (CartesianMonoidalCategory.prodComparison toTopCat Y Z) :=
  (isIso_prodComparison_toTopCat_iff Y Z).2 inferInstance

/-- When `Y × Z` is `X`-generated, the convenient product `Y ⊗ Z` is homeomorphic to the ordinary
product `Y × Z` via `tensorEquiv`. -/
def tensorHomeomorphProd [IsGeneratedBy X (Y × Z)] : ↑(Y ⊗ Z) ≃ₜ Y × Z :=
  IsGeneratedBy.homeomorph (X := X) (Y := Y × Z)

@[simp] theorem coe_tensorHomeomorphProd [IsGeneratedBy X (Y × Z)] :
    ⇑(tensorHomeomorphProd Y Z) = tensorEquiv Y Z := (rfl)

@[simp] theorem coe_tensorHomeomorphProd_symm [IsGeneratedBy X (Y × Z)] :
    ⇑(tensorHomeomorphProd Y Z).symm = (tensorEquiv Y Z).symm := (rfl)

end ProdComparison

/-- Any continuous map from an `X`-generated space into `Y × Z` lifts continuously into `Y ⊗ Z` via
`(tensorEquiv Y Z).symm`. -/
theorem continuous_tensorEquiv_symm_comp {A : Type*} [TopologicalSpace A] [IsGeneratedBy X A]
    {Y Z : GeneratedByTopCat.{v} X} {g : A → Y × Z} (hg : Continuous g) :
    Continuous ((tensorEquiv Y Z).symm ∘ g) :=
  (IsGeneratedBy.equiv_symm_comp_continuous_iff (X := X) g).2 hg

/-- A morphism out of the convenient product `Y ⊗ Z` defines an `X`-continuous map out of
`Y × Z`. -/
theorem continuousGeneratedBy_comp_tensorEquiv_symm
    {Y Z T : GeneratedByTopCat.{v} X} (f : Y ⊗ Z ⟶ T) :
    ContinuousGeneratedBy X (f ∘ (tensorEquiv Y Z).symm) :=
  fun _ g ↦ f.hom.hom.continuous.comp (continuous_tensorEquiv_symm_comp g.continuous)

section MonoidalClosed

variable [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]

section LocallyCompact

variable (Y Z : GeneratedByTopCat.{v} X)

/-- When all test spaces `X i` are locally compact, their pairwise products are `X`-generated, and
`Z` is locally compact, the product comparison in `TopCat` is an isomorphism. -/
instance instIsIsoProdComparisonToTopCatOfLocallyCompactRight [LocallyCompactSpace Z] :
    IsIso (CartesianMonoidalCategory.prodComparison toTopCat Y Z) := by
  have := IsGeneratedBy.prod_of_locallyCompactSpace_right (X := X) Y Z; infer_instance

/-- When all test spaces `X i` are locally compact, their pairwise products are `X`-generated, and
`Y` is locally compact, the product comparison in `TopCat` is an isomorphism. -/
instance instIsIsoProdComparisonToTopCatOfLocallyCompactLeft [LocallyCompactSpace Y] :
    IsIso (CartesianMonoidalCategory.prodComparison toTopCat Y Z) := by
  have := IsGeneratedBy.prod_of_locallyCompactSpace_left (X := X) Y Z; infer_instance

/-- When all test spaces `X i` are locally compact, their pairwise products are `X`-generated, and
`Z` is locally compact, the convenient product `Y ⊗ Z` is homeomorphic to the ordinary product
`Y × Z` via `tensorEquiv`. -/
def tensorHomeomorphProdOfLocallyCompactRight [LocallyCompactSpace Z] : ↑(Y ⊗ Z) ≃ₜ Y × Z :=
  have := IsGeneratedBy.prod_of_locallyCompactSpace_right (X := X) Y Z
  tensorHomeomorphProd Y Z

@[simp] theorem coe_tensorHomeomorphProdOfLocallyCompactRight [LocallyCompactSpace Z] :
    ⇑(tensorHomeomorphProdOfLocallyCompactRight Y Z) = tensorEquiv Y Z := (rfl)

@[simp] theorem coe_tensorHomeomorphProdOfLocallyCompactRight_symm [LocallyCompactSpace Z] :
    ⇑(tensorHomeomorphProdOfLocallyCompactRight Y Z).symm = (tensorEquiv Y Z).symm := (rfl)

/-- When all test spaces `X i` are locally compact, their pairwise products are `X`-generated, and
`Y` is locally compact, the convenient product `Y ⊗ Z` is homeomorphic to the ordinary product
`Y × Z` via `tensorEquiv`. -/
def tensorHomeomorphProdOfLocallyCompactLeft [LocallyCompactSpace Y] : ↑(Y ⊗ Z) ≃ₜ Y × Z :=
  have := IsGeneratedBy.prod_of_locallyCompactSpace_left (X := X) Y Z
  tensorHomeomorphProd Y Z

@[simp] theorem coe_tensorHomeomorphProdOfLocallyCompactLeft [LocallyCompactSpace Y] :
    ⇑(tensorHomeomorphProdOfLocallyCompactLeft Y Z) = tensorEquiv Y Z := (rfl)

@[simp] theorem coe_tensorHomeomorphProdOfLocallyCompactLeft_symm [LocallyCompactSpace Y] :
    ⇑(tensorHomeomorphProdOfLocallyCompactLeft Y Z).symm = (tensorEquiv Y Z).symm := (rfl)

end LocallyCompact

/-- The internal hom functor `Z ↦ WithGeneratedByTopology X (ContinuousMapGeneratedBy X Y Z)` on
`GeneratedByTopCat X`.

Exposed so that downstream modules and code generation agree on the carrier type of
`(ihom Y).obj Z`. -/
@[expose] def internalHom (Y : GeneratedByTopCat.{v} X) :
    GeneratedByTopCat.{v} X ⥤ GeneratedByTopCat.{v} X where
  obj Z := of (X := X) (WithGeneratedByTopology X (ContinuousMapGeneratedBy X Y Z))
  map g := ofHom (ContinuousMapGeneratedBy.postcomp
    ⟨g, g.hom.hom.continuous.continuousGeneratedBy⟩).prop.continuousMap

private def internalHomToContinuousMapGeneratedBy (Y Z : GeneratedByTopCat.{v} X) :
    ↑((internalHom Y).obj Z) ≃ ContinuousMapGeneratedBy X Y Z :=
  WithGeneratedByTopology.equiv (X := X) (Y := ContinuousMapGeneratedBy X Y Z)

private def internalHomEquiv (Y Z : GeneratedByTopCat.{v} X) :
    ↑((internalHom Y).obj Z) ≃ C(Y, Z) :=
  (internalHomToContinuousMapGeneratedBy Y Z).trans ContinuousMapGeneratedBy.equivContinuousMap

section InternalHom

variable {Y Z T : GeneratedByTopCat.{v} X}

private def curryHom (f : Y ⊗ Z ⟶ T) : Z ⟶ (internalHom Y).obj T :=
  let f₀ : ContinuousMapGeneratedBy X (Y × Z) T :=
    ⟨f ∘ (tensorEquiv Y Z).symm, continuousGeneratedBy_comp_tensorEquiv_symm f⟩
  ofHom ((ContinuousMapGeneratedBy.curryEquiv f₀).toContinuousMap.toGeneratedBy X)

private def uncurryHom (g : Z ⟶ (internalHom Y).obj T) : Y ⊗ Z ⟶ T :=
  let g₀ : C(Z, ContinuousMapGeneratedBy X Y T) :=
    (WithGeneratedByTopology.counit X (ContinuousMapGeneratedBy X Y T)).comp g.hom.hom
  let h : ContinuousMapGeneratedBy X (Y × Z) T :=
    ContinuousMapGeneratedBy.curryEquiv.symm (g₀.toContinuousMapGeneratedBy X)
  ConcreteCategory.ofHom ⟨fun p ↦ h (tensorEquiv Y Z p),
    (IsGeneratedBy.continuous_iff X _).2
      (h.prop.comp (continuous_tensorEquiv Y Z).continuousGeneratedBy)⟩

private theorem internalHomEquiv_map_apply (g : Z ⟶ T) (f : ↑((internalHom Y).obj Z)) (y : Y) :
    internalHomEquiv Y T (((internalHom Y).map g) f) y = g (internalHomEquiv Y Z f y) := by
  simp only [internalHomEquiv, Equiv.trans_apply, ContinuousMapGeneratedBy.equivContinuousMap_apply,
    ContinuousMapGeneratedBy.toContinuousMap_apply]
  exact congrArg (fun k : ContinuousMapGeneratedBy X Y T ↦ k y)
    ((WithGeneratedByTopology.equiv (X := X)).apply_symm_apply _)

private theorem internalHomToContinuousMapGeneratedBy_curryHom_apply (f : Y ⊗ Z ⟶ T) (z : Z) :
    internalHomToContinuousMapGeneratedBy Y T (curryHom f z) =
      ContinuousMapGeneratedBy.curryEquiv
        ⟨f ∘ (tensorEquiv Y Z).symm, continuousGeneratedBy_comp_tensorEquiv_symm f⟩ z :=
  ((congrArg (WithGeneratedByTopology.equiv (X := X))
    (ContinuousMap.toGeneratedBy_apply (ContinuousMapGeneratedBy.curryEquiv
      ⟨f ∘ (tensorEquiv Y Z).symm, continuousGeneratedBy_comp_tensorEquiv_symm f⟩).toContinuousMap
      z)).trans (Equiv.apply_symm_apply _ _)).trans
    (ContinuousMapGeneratedBy.toContinuousMap_apply _ z)

private theorem internalHomEquiv_curryHom_apply (f : Y ⊗ Z ⟶ T) (z : Z) (y : Y) :
    internalHomEquiv Y T (curryHom f z) y = f ((tensorEquiv Y Z).symm (y, z)) := by
  simp [internalHomEquiv, internalHomToContinuousMapGeneratedBy_curryHom_apply]

private theorem uncurryHom_apply (g : Z ⟶ (internalHom Y).obj T) (p : ↑(Y ⊗ Z)) :
    uncurryHom g p = internalHomEquiv Y T (g (snd Y Z p)) (fst Y Z p) := by
  have hp : tensorEquiv Y Z p = (fst Y Z p, snd Y Z p) :=
    Prod.ext (tensorEquiv_fst p) (tensorEquiv_snd p)
  dsimp only [uncurryHom]
  rw [ConcreteCategory.hom_ofHom, ContinuousMap.coe_mk, hp,
    ContinuousMapGeneratedBy.curryEquiv_symm_apply,
    ContinuousMap.toContinuousMapGeneratedBy_apply_apply]
  simp only [internalHomEquiv, Equiv.trans_apply, ContinuousMapGeneratedBy.equivContinuousMap_apply,
    ContinuousMapGeneratedBy.toContinuousMap_apply]
  let c := WithGeneratedByTopology.counit X (ContinuousMapGeneratedBy X Y T)
  exact congrArg (fun k : ContinuousMapGeneratedBy X Y T ↦ k (fst Y Z p)) <|
    (ContinuousMap.comp_apply c g.hom.hom (snd Y Z p)).trans <|
      (congrArg c (hom_apply g (snd Y Z p))).trans
        (WithGeneratedByTopology.counit_apply X (X := ContinuousMapGeneratedBy X Y T)
          (g (snd Y Z p)))

end InternalHom

private def curryEquiv (Y Z T : GeneratedByTopCat.{v} X) :
    (Y ⊗ Z ⟶ T) ≃ (Z ⟶ (internalHom Y).obj T) where
  toFun := curryHom
  invFun := uncurryHom
  left_inv f := by
    ext p; rw [uncurryHom_apply, internalHomEquiv_curryHom_apply]
    exact congrArg f ((tensorEquiv Y Z).symm_apply_apply p)
  right_inv g := by
    ext z; apply (internalHomEquiv Y T).injective; ext y
    rw [internalHomEquiv_curryHom_apply, uncurryHom_apply, fst_tensorEquiv_symm,
      snd_tensorEquiv_symm]

/-- The adjunction `Y ⊗ - ⊣ internalHom Y` in `GeneratedByTopCat X`. -/
def tensorLeftAdjunction (Y : GeneratedByTopCat.{v} X) : tensorLeft Y ⊣ internalHom Y :=
  Adjunction.mkOfHomEquiv
    { homEquiv := curryEquiv Y
      homEquiv_naturality_left_symm f g := by ext p; simp [curryEquiv, uncurryHom_apply]
      homEquiv_naturality_right f g := by
        ext z; apply (internalHomEquiv Y _).injective; ext y
        simp [curryEquiv, internalHomEquiv_curryHom_apply, internalHomEquiv_map_apply] }

/-- When all test spaces `X i` are locally compact and their pairwise products are `X`-generated,
`GeneratedByTopCat X` is cartesian closed. -/
instance instMonoidalClosed : MonoidalClosed (GeneratedByTopCat.{v} X) where
  closed Y := ⟨internalHom Y, tensorLeftAdjunction Y⟩

/-- Elements of `(ihom Y).obj Z` correspond bijectively to continuous maps `C(Y, Z)`. -/
def ihomEquiv (Y Z : GeneratedByTopCat.{v} X) : ↑((ihom Y).obj Z) ≃ C(Y, Z) :=
  internalHomEquiv Y Z

private theorem ihom_adjunction_homEquiv_eq (Y Z T : GeneratedByTopCat.{v} X) :
    (ihom.adjunction Y).homEquiv Z T = curryEquiv Y Z T :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _

section IhomPointwise

variable {W Y Z T : GeneratedByTopCat.{v} X}

@[simp] theorem ihomEquiv_ihom_adjunction_homEquiv_apply (f : Y ⊗ Z ⟶ T) (z : Z) (y : Y) :
    dsimp% ihomEquiv Y T (((ihom.adjunction Y).homEquiv Z T f) z) y =
      f ((tensorEquiv Y Z).symm (y, z)) := by
  rw [ihom_adjunction_homEquiv_eq]; exact internalHomEquiv_curryHom_apply f z y

@[simp] theorem ihom_adjunction_homEquiv_symm_apply (g : Z ⟶ (ihom Y).obj T) (p : ↑(Y ⊗ Z)) :
    dsimp% (((ihom.adjunction Y).homEquiv Z T).symm g) p =
      ihomEquiv Y T (g (snd Y Z p)) (fst Y Z p) := by
  rw [ihom_adjunction_homEquiv_eq]; exact uncurryHom_apply g p

@[ext] theorem ihom_obj_ext {f g : ↑((ihom Y).obj Z)}
    (h : ∀ y, ihomEquiv Y Z f y = ihomEquiv Y Z g y) : f = g :=
  (ihomEquiv Y Z).injective (ContinuousMap.ext h)

@[simp] theorem ihomEquiv_ihom_map_apply (g : Z ⟶ T) (f : ↑((ihom Y).obj Z)) (y : Y) :
    ihomEquiv Y T (((ihom Y).map g) f) y = g (ihomEquiv Y Z f y) :=
  internalHomEquiv_map_apply g f y

@[simp] theorem ihomEquiv_curry_apply (f : Y ⊗ Z ⟶ T) (z : Z) (y : Y) :
    ihomEquiv Y T (MonoidalClosed.curry f z) y = f ((tensorEquiv Y Z).symm (y, z)) := by
  rw [← MonoidalClosed.homEquiv_apply_eq]; exact ihomEquiv_ihom_adjunction_homEquiv_apply f z y

@[simp] theorem uncurry_apply (g : Z ⟶ (ihom Y).obj T) (p : ↑(Y ⊗ Z)) :
    MonoidalClosed.uncurry g p = ihomEquiv Y T (g (snd Y Z p)) (fst Y Z p) := by
  rw [← MonoidalClosed.homEquiv_symm_apply_eq]; exact ihom_adjunction_homEquiv_symm_apply g p

/-- Evaluation in `GeneratedByTopCat X` applies the underlying continuous map to a point. -/
@[simp] theorem ihom_ev_app_apply (p : ↑(Y ⊗ (ihom Y).obj Z)) :
    ConcreteCategory.hom (X := Y ⊗ (ihom Y).obj Z) (Y := Z) ((ihom.ev Y).app Z) p =
      ihomEquiv Y Z (snd Y _ p) (fst Y _ p) := by
  rw [← MonoidalClosed.uncurry_id_eq_ev, uncurry_apply]; rfl

/-- Coevaluation in `GeneratedByTopCat X` sends `z` to the slice map `y ↦ (y, z)`. -/
@[simp] theorem ihomEquiv_ihom_coev_app_apply (z : Z) (y : Y) :
    ihomEquiv Y (Y ⊗ Z)
      (ConcreteCategory.hom (X := Z) (Y := (ihom Y).obj (Y ⊗ Z)) ((ihom.coev Y).app Z) z) y =
      (tensorEquiv Y Z).symm (y, z) := by
  rw [← MonoidalClosed.curry_id_eq_coev, ihomEquiv_curry_apply]; rfl

@[simp] theorem ihomEquiv_pre_app_apply (f : W ⟶ Y) (g : ↑((ihom Y).obj Z)) (w : W) :
    ihomEquiv W Z (((MonoidalClosed.pre f).app Z) g) w = ihomEquiv Y Z g (f w) := by
  have h := ConcreteCategory.congr_hom (MonoidalClosed.uncurry_pre f Z)
    ((tensorEquiv W _).symm (w, g))
  rw [uncurry_apply, comp_apply, whiskerRight_apply] at h
  simpa using h.trans (ihom_ev_app_apply _)

@[simp] theorem ihomEquiv_ihomCurry_apply (f : ↑((ihom (W ⊗ Y)).obj Z)) (y : Y) (w : W) :
    ihomEquiv W Z (ihomEquiv Y ((ihom W).obj Z) (MonoidalClosed.ihomCurry W Y Z f) y) w =
      ihomEquiv (W ⊗ Y) Z f ((tensorEquiv W Y).symm (w, y)) := by
  simp [MonoidalClosed.ihomCurry]

@[simp] theorem ihomEquiv_ihomUncurry_apply
    (g : ↑((ihom Y).obj ((ihom W).obj Z))) (p : ↑(W ⊗ Y)) :
    ihomEquiv (W ⊗ Y) Z (MonoidalClosed.ihomUncurry W Y Z g) p =
      ihomEquiv W Z (ihomEquiv Y ((ihom W).obj Z) g (snd W Y p)) (fst W Y p) := by
  simp [MonoidalClosed.ihomUncurry]

end IhomPointwise

/-- Canonical morphism from the `X`-generated refinement of the compact-open mapping space
`C(Y, Z)` into the internal hom `(ihom Y).obj Z`. -/
def compactOpenToIhom (Y Z : GeneratedByTopCat.{v} X) :
    of (X := X) (WithGeneratedByTopology X C(Y, Z)) ⟶ (ihom Y).obj Z :=
  (TopCat.toGeneratedByTopCat (X := X)).map
    (TopCat.ofHom (ContinuousMap.toContinuousMapGeneratedBy X))

@[simp] theorem compactOpenToIhom_apply (Y Z : GeneratedByTopCat.{v} X)
    (f : WithGeneratedByTopology X C(Y, Z)) :
    dsimp% compactOpenToIhom Y Z f =
      (ihomEquiv Y Z).symm (WithGeneratedByTopology.equiv (X := X) (Y := C(Y, Z)) f) := by
  apply (ihomEquiv Y Z).injective
  rw [Equiv.apply_symm_apply]
  refine (ContinuousMapGeneratedBy.equivContinuousMap_apply _).trans <|
    (congrArg ContinuousMapGeneratedBy.toContinuousMap <|
      (congrArg (WithGeneratedByTopology.equiv (X := X) (Y := ContinuousMapGeneratedBy X Y Z))
        (TopCat.toGeneratedByTopCat_map_apply X
          (TopCat.ofHom (ContinuousMap.toContinuousMapGeneratedBy X)) f)).trans
        (Equiv.apply_symm_apply _ _)).trans
      (ContinuousMapGeneratedBy.toContinuousMap_toContinuousMapGeneratedBy _)

section CompactOpen

variable {Y : GeneratedByTopCat.{v} X}
  (hK : ∀ ⦃K : Set Y⦄, IsCompact K →
    ∃ (m : ℕ) (i : Fin m → ι) (L : ∀ j, Set (X (i j))) (f : ∀ j, C(X (i j), Y)),
      (∀ j, IsCompact (L j)) ∧ ⋃ j, f j '' L j = K)

include hK

/-- When every compact subset of `Y` is a finite union of images of compact subsets of generators
`X i` under continuous maps, the internal hom `(ihom Y).obj Z` is canonically isomorphic to the
`X`-generated refinement of the compact-open mapping space `C(Y, Z)`. -/
def ihomIsoCompactOpenOfExistsIUnionIsCompactImageEq (Z : GeneratedByTopCat.{v} X) :
    (ihom Y).obj Z ≅ of (X := X) (WithGeneratedByTopology X C(Y, Z)) :=
  (TopCat.toGeneratedByTopCat (X := X)).mapIso <|
    TopCat.isoOfHomeo
      (X := TopCat.of (ContinuousMapGeneratedBy X Y Z)) (Y := TopCat.of C(Y, Z)) <|
      ContinuousMapGeneratedBy.homeomorphContinuousMapOfExistsIUnionIsCompactImageEq
        (X := X) (Z := Z) hK

@[simp] theorem ihomIsoCompactOpenOfExistsIUnionIsCompactImageEq_inv (Z : GeneratedByTopCat.{v} X) :
    (ihomIsoCompactOpenOfExistsIUnionIsCompactImageEq hK Z).inv = compactOpenToIhom Y Z :=
  congrArg (TopCat.toGeneratedByTopCat (X := X)).map <|
    TopCat.ext fun g ↦
      ContinuousMapGeneratedBy.homeomorphContinuousMapOfExistsIUnionIsCompactImageEq_symm_apply hK g

@[simp] theorem ihomIsoCompactOpenOfExistsIUnionIsCompactImageEq_hom_apply
    (Z : GeneratedByTopCat.{v} X) (f : ↑((ihom Y).obj Z)) :
    dsimp% (ihomIsoCompactOpenOfExistsIUnionIsCompactImageEq hK Z).hom f =
      (WithGeneratedByTopology.equiv (X := X) (Y := C(Y, Z))).symm (ihomEquiv Y Z f) := by
  have h := (ihomIsoCompactOpenOfExistsIUnionIsCompactImageEq hK Z).inv_hom_id_apply
    ((WithGeneratedByTopology.equiv (X := X) (Y := C(Y, Z))).symm (ihomEquiv Y Z f))
  rw [ihomIsoCompactOpenOfExistsIUnionIsCompactImageEq_inv, compactOpenToIhom_apply,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply] at h
  exact h

end CompactOpen

end MonoidalClosed

end GeneratedByTopCat
