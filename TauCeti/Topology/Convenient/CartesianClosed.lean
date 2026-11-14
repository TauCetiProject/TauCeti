/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
public import Mathlib.Topology.Category.TopCat.Monoidal
public import TauCeti.Topology.Convenient.HomSpace

/-!
# Cartesian monoidal closed structure on `GeneratedByTopCat`

For any generating family of topological spaces `X : ι → Type u`, the coreflective full
subcategory `GeneratedByTopCat.{v} X` of `X`-generated spaces in `TopCat.{v}` has chosen finite
products: the one-point space `PUnit` is terminal, and the binary product of `Y` and `Z` is the
`X`-generated refinement `WithGeneratedByTopology X (Y × Z)` of their topological product, with
projections factoring through the counit (`GeneratedByTopCat.instCartesianMonoidalCategory`). The
canonical comparison `(Y ⊗ Z).obj ⟶ Y.obj ⊗ Z.obj` in `TopCat` is the counit on `Y × Z`, so it is
an isomorphism if and only if `Y × Z` is already `X`-generated
(`GeneratedByTopCat.isIso_prodComparisonToTop_iff`).

When each generator `X i` is locally compact and each product `X i × X j` is `X`-generated,
currying via `Topology.ContinuousMapGeneratedBy.curryEquiv` makes `GeneratedByTopCat.{v} X`
cartesian closed (`GeneratedByTopCat.instMonoidalClosed`): the internal hom `(ihom Y).obj Z` is
the `X`-generated refinement of `ContinuousMapGeneratedBy X Y Z`. Moreover:

* if either factor is locally compact, `Y × Z` is already `X`-generated and `Y ⊗ Z` has the
  ordinary product topology (`GeneratedByTopCat.tensorHomeomorphProdOfLocallyCompactRight`,
  `GeneratedByTopCat.tensorHomeomorphProdOfLocallyCompactLeft`);
* if compact subsets of `Y` lift to compact subsets of the generators `X i`, then `(ihom Y).obj Z`
  is canonically isomorphic to the `X`-generated refinement of the compact-open mapping space
  `C(Y, Z)` (`GeneratedByTopCat.ihomIsoCompactOpenOfCompactLift`).

## References

* M. Escardó, J. Lawson, and A. Simpson, *Comparing Cartesian closed categories of (core)
  compactly generated spaces*, Topology Appl. 143 (2004), 105–145.
* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Arch. Math.
  (Basel) 22 (1971), 545–555.
-/

public section

universe v t u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Topology

namespace GeneratedByTopCat

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]

section Morphisms

/-- Construct a morphism in `GeneratedByTopCat` from a `ContinuousMap`. -/
abbrev homMk {Y Z : GeneratedByTopCat.{v} X} (f : C(Y.obj, Z.obj)) : Y ⟶ Z :=
  ConcreteCategory.ofHom f

@[simp]
theorem hom_apply {Y Z : GeneratedByTopCat.{v} X} (f : Y ⟶ Z) (y : Y) :
    f.hom y = f y :=
  (rfl)

theorem hom_hom_apply {Y Z : GeneratedByTopCat.{v} X} (f : Y ⟶ Z) (y : Y) :
    f.hom.hom y = f y :=
  (rfl)

@[ext]
theorem hom_ext {Y Z : GeneratedByTopCat.{v} X} {f g : Y ⟶ Z} (h : ∀ y, f y = g y) : f = g :=
  InducedCategory.hom_ext (TopCat.ext h)

/-- Construct a morphism between `of`-objects in `GeneratedByTopCat` from a `ContinuousMap`. -/
abbrev ofHom {Y Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    [IsGeneratedBy X Y] [IsGeneratedBy X Z] (f : C(Y, Z)) :
    of (X := X) Y ⟶ of (X := X) Z :=
  ConcreteCategory.ofHom f

end Morphisms

section CartesianMonoidal

/-- `PUnit` is terminal in `GeneratedByTopCat`. -/
def isTerminalPUnit : IsTerminal (of (X := X) PUnit.{v + 1}) :=
  IsTerminal.ofUniqueHom
    (fun _ ↦ homMk ⟨fun _ ↦ PUnit.unit, continuous_const⟩)
    (fun _ _ ↦ by ext)

/-- The explicit binary fan of `Y` and `Z` in `GeneratedByTopCat X` with apex
`WithGeneratedByTopology X (Y × Z)`.

Exposed so that downstream modules and code generation agree on the carrier type of `Y ⊗ Z`. -/
@[expose]
def prodBinaryFan (Y Z : GeneratedByTopCat.{v} X) : BinaryFan Y Z :=
  BinaryFan.mk (P := of (X := X) (WithGeneratedByTopology X (Y × Z)))
    (homMk ⟨fun p ↦ (WithGeneratedByTopology.equiv (X := X) (Y := Y × Z) p).1,
      continuous_fst.comp (WithGeneratedByTopology.continuous_equiv (X := X) (Y := Y × Z))⟩)
    (homMk ⟨fun p ↦ (WithGeneratedByTopology.equiv (X := X) (Y := Y × Z) p).2,
      continuous_snd.comp (WithGeneratedByTopology.continuous_equiv (X := X) (Y := Y × Z))⟩)

/-- `WithGeneratedByTopology X (Y × Z)` is a binary product of `Y` and `Z` in
`GeneratedByTopCat X`. -/
def prodBinaryFanIsLimit (Y Z : GeneratedByTopCat.{v} X) : IsLimit (prodBinaryFan Y Z) :=
  BinaryFan.IsLimit.mk _
    (fun {_} f g ↦ homMk ((f.hom.hom.prodMk g.hom.hom).toGeneratedBy X))
    (fun f g ↦ by
      ext w
      change (WithGeneratedByTopology.equiv (X := X) (Y := Y × Z)
        (((f.hom.hom.prodMk g.hom.hom).toGeneratedBy X) w)).1 = f w
      simp)
    (fun f g ↦ by
      ext w
      change (WithGeneratedByTopology.equiv (X := X) (Y := Y × Z)
        (((f.hom.hom.prodMk g.hom.hom).toGeneratedBy X) w)).2 = g w
      simp)
    (fun {_} f g m h₁ h₂ ↦ by
      ext w
      apply (WithGeneratedByTopology.equiv (X := X) (Y := Y × Z)).injective
      have hm₁ : (WithGeneratedByTopology.equiv (X := X) (Y := Y × Z) (m w)).1 = f w := by
        have h := ConcreteCategory.congr_hom h₁ w
        exact h
      have hm₂ : (WithGeneratedByTopology.equiv (X := X) (Y := Y × Z) (m w)).2 = g w := by
        have h := ConcreteCategory.congr_hom h₂ w
        exact h
      have hfg : WithGeneratedByTopology.equiv (X := X) (Y := Y × Z)
          (((f.hom.hom.prodMk g.hom.hom).toGeneratedBy X) w) = (f w, g w) := by simp
      exact (Prod.ext hm₁ hm₂).trans hfg.symm)

instance instCartesianMonoidalCategory : CartesianMonoidalCategory (GeneratedByTopCat.{v} X) :=
  .ofChosenFiniteProducts ⟨_, isTerminalPUnit⟩
    (fun Y Z ↦ ⟨prodBinaryFan Y Z, prodBinaryFanIsLimit Y Z⟩)

instance instBraidedCategory : BraidedCategory (GeneratedByTopCat.{v} X) :=
  .ofCartesianMonoidalCategory

instance (Y Z : GeneratedByTopCat.{v} X) [T2Space Y] [T2Space Z] : T2Space ↑(Y ⊗ Z) :=
  inferInstanceAs (T2Space (WithGeneratedByTopology X (Y × Z)))

instance (Y Z : GeneratedByTopCat.{v} X) [Small.{w} Y] [Small.{w} Z] :
    Small.{w} ↑(Y ⊗ Z) :=
  inferInstanceAs (Small.{w} (WithGeneratedByTopology X (Y × Z)))

/-- The underlying bijection between the convenient product `Y ⊗ Z` and `Y × Z`. -/
def tensorEquiv (Y Z : GeneratedByTopCat.{v} X) : ↑(Y ⊗ Z) ≃ Y × Z :=
  WithGeneratedByTopology.equiv (X := X) (Y := Y × Z)

@[simp]
theorem tensorEquiv_fst {Y Z : GeneratedByTopCat.{v} X} (p : ↑(Y ⊗ Z)) :
    (tensorEquiv Y Z p).1 = fst Y Z p :=
  (rfl)

@[simp]
theorem tensorEquiv_snd {Y Z : GeneratedByTopCat.{v} X} (p : ↑(Y ⊗ Z)) :
    (tensorEquiv Y Z p).2 = snd Y Z p :=
  (rfl)

@[simp]
theorem fst_tensorEquiv_symm {Y Z : GeneratedByTopCat.{v} X} (y : Y) (z : Z) :
    fst Y Z ((tensorEquiv Y Z).symm (y, z)) = y :=
  (rfl)

@[simp]
theorem snd_tensorEquiv_symm {Y Z : GeneratedByTopCat.{v} X} (y : Y) (z : Z) :
    snd Y Z ((tensorEquiv Y Z).symm (y, z)) = z :=
  (rfl)

@[ext]
theorem tensorObj_ext {Y Z : GeneratedByTopCat.{v} X} {p q : ↑(Y ⊗ Z)}
    (h₁ : fst Y Z p = fst Y Z q) (h₂ : snd Y Z p = snd Y Z q) : p = q :=
  (tensorEquiv Y Z).injective (Prod.ext (by simpa using h₁) (by simpa using h₂))

@[simp]
theorem lift_apply {W Y Z : GeneratedByTopCat.{v} X} (f : W ⟶ Y) (g : W ⟶ Z) (w : W) :
    lift f g w = (tensorEquiv Y Z).symm (f w, g w) := by
  apply (tensorEquiv Y Z).injective
  ext <;> simp [← comp_apply]

theorem tensorEquiv_lift_apply {W Y Z : GeneratedByTopCat.{v} X} (f : W ⟶ Y) (g : W ⟶ Z) (w : W) :
    tensorEquiv Y Z (lift f g w) = (f w, g w) := by
  simp

@[simp]
theorem tensorHom_apply {W₁ W₂ Y₁ Y₂ : GeneratedByTopCat.{v} X}
    (f : W₁ ⟶ W₂) (g : Y₁ ⟶ Y₂) (p : ↑(W₁ ⊗ Y₁)) :
    (f ⊗ₘ g) p = (tensorEquiv W₂ Y₂).symm (f (fst W₁ Y₁ p), g (snd W₁ Y₁ p)) := by
  apply (tensorEquiv W₂ Y₂).injective
  ext <;> simp [← comp_apply]

@[simp]
theorem whiskerLeft_apply (W : GeneratedByTopCat.{v} X) {Y Z : GeneratedByTopCat.{v} X}
    (f : Y ⟶ Z) (p : ↑(W ⊗ Y)) :
    (W ◁ f) p = (tensorEquiv W Z).symm (fst W Y p, f (snd W Y p)) := by
  apply (tensorEquiv W Z).injective
  ext <;> simp [← comp_apply]

@[simp]
theorem whiskerRight_apply {W Y : GeneratedByTopCat.{v} X} (f : W ⟶ Y)
    (Z : GeneratedByTopCat.{v} X) (p : ↑(W ⊗ Z)) :
    (f ▷ Z) p = (tensorEquiv Y Z).symm (f (fst W Z p), snd W Z p) := by
  apply (tensorEquiv Y Z).injective
  ext <;> simp [← comp_apply]

@[simp]
theorem braiding_hom_apply {Y Z : GeneratedByTopCat.{v} X} (p : ↑(Y ⊗ Z)) :
    (β_ Y Z).hom p = (tensorEquiv Z Y).symm (snd Y Z p, fst Y Z p) := by
  apply (tensorEquiv Z Y).injective
  ext <;> simp [← comp_apply]

@[simp]
theorem braiding_inv_apply {Y Z : GeneratedByTopCat.{v} X} (p : ↑(Z ⊗ Y)) :
    (β_ Y Z).inv p = (tensorEquiv Y Z).symm (snd Z Y p, fst Z Y p) := by
  apply (tensorEquiv Y Z).injective
  ext <;> simp [← comp_apply]

@[simp]
theorem leftUnitor_hom_apply {Y : GeneratedByTopCat.{v} X}
    (p : ↑(𝟙_ (GeneratedByTopCat.{v} X) ⊗ Y)) :
    (λ_ Y).hom p = snd _ Y p :=
  (rfl)

@[simp]
theorem rightUnitor_hom_apply {Y : GeneratedByTopCat.{v} X}
    (p : ↑(Y ⊗ 𝟙_ (GeneratedByTopCat.{v} X))) :
    (ρ_ Y).hom p = fst Y _ p :=
  (rfl)

/-- The canonical comparison from the underlying space of the convenient product `Y ⊗ Z` to the
ordinary topological product `Y × Z` in `TopCat`, given by the generated-topology counit. -/
def prodComparisonToTop (Y Z : GeneratedByTopCat.{v} X) :
    (Y ⊗ Z).obj ⟶ Y.obj ⊗ Z.obj :=
  (adjCounit (X := X)).app (Y.obj ⊗ Z.obj)

@[simp]
theorem prodComparisonToTop_apply (Y Z : GeneratedByTopCat.{v} X) (p : ↑(Y ⊗ Z)) :
    prodComparisonToTop Y Z p = tensorEquiv Y Z p :=
  (rfl)

@[reassoc (attr := simp)]
theorem prodComparisonToTop_fst (Y Z : GeneratedByTopCat.{v} X) :
    prodComparisonToTop Y Z ≫ fst Y.obj Z.obj = (fst Y Z).hom :=
  (rfl)

@[reassoc (attr := simp)]
theorem prodComparisonToTop_snd (Y Z : GeneratedByTopCat.{v} X) :
    prodComparisonToTop Y Z ≫ snd Y.obj Z.obj = (snd Y Z).hom :=
  (rfl)

/-- The product comparison in `TopCat` equals the canonical pairing of the underlying
projections. -/
theorem prodComparisonToTop_eq_lift (Y Z : GeneratedByTopCat.{v} X) :
    prodComparisonToTop Y Z = lift (fst Y Z).hom (snd Y Z).hom :=
  CartesianMonoidalCategory.hom_ext _ _
    (prodComparisonToTop_fst Y Z) (prodComparisonToTop_snd Y Z)

/-- The convenient product `Y ⊗ Z` has the ordinary product topology if and only if `Y × Z` is
`X`-generated. -/
theorem isIso_prodComparisonToTop_iff (Y Z : GeneratedByTopCat.{v} X) :
    IsIso (prodComparisonToTop Y Z) ↔ IsGeneratedBy X (Y × Z) :=
  isIso_adjCounit_app_iff X (Y.obj ⊗ Z.obj)

/-- A morphism out of the convenient product `Y ⊗ Z` defines an `X`-continuous map out of
`Y × Z`. -/
theorem continuousGeneratedBy_comp_tensorEquiv_symm
    {Y Z T : GeneratedByTopCat.{v} X} (f : Y ⊗ Z ⟶ T) :
    ContinuousGeneratedBy X (f ∘ (tensorEquiv Y Z).symm) := by
  let g : C(WithGeneratedByTopology X (↑Y × ↑Z), ↑T) := f.hom.hom
  exact (WithGeneratedByTopology.continuous_from_iff g).1 g.continuous

end CartesianMonoidal

section MonoidalClosed

variable [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]

/-- When `Z` is locally compact, the product comparison `(Y ⊗ Z).obj ⟶ Y.obj ⊗ Z.obj` in `TopCat`
is an isomorphism. -/
instance instIsIsoProdComparisonToTopOfLocallyCompactRight
    (Y Z : GeneratedByTopCat.{v} X) [LocallyCompactSpace Z] :
    IsIso (prodComparisonToTop Y Z) :=
  (isIso_prodComparisonToTop_iff Y Z).2 (IsGeneratedBy.prod_of_locallyCompactSpace_right Y Z)

/-- When `Y` is locally compact, the product comparison `(Y ⊗ Z).obj ⟶ Y.obj ⊗ Z.obj` in `TopCat`
is an isomorphism. -/
instance instIsIsoProdComparisonToTopOfLocallyCompactLeft
    (Y Z : GeneratedByTopCat.{v} X) [LocallyCompactSpace Y] :
    IsIso (prodComparisonToTop Y Z) :=
  (isIso_prodComparisonToTop_iff Y Z).2 (IsGeneratedBy.prod_of_locallyCompactSpace_left Y Z)

/-- When `Z` is locally compact, the convenient product `Y ⊗ Z` is homeomorphic to the ordinary
product `Y × Z` via `tensorEquiv`. -/
def tensorHomeomorphProdOfLocallyCompactRight
    (Y Z : GeneratedByTopCat.{v} X) [LocallyCompactSpace Z] :
    ↑(Y ⊗ Z) ≃ₜ Y × Z :=
  have : IsGeneratedBy X (Y × Z) := IsGeneratedBy.prod_of_locallyCompactSpace_right Y Z
  IsGeneratedBy.homeomorph (X := X) (Y := Y × Z)

@[simp]
theorem coe_tensorHomeomorphProdOfLocallyCompactRight
    (Y Z : GeneratedByTopCat.{v} X) [LocallyCompactSpace Z] :
    ⇑(tensorHomeomorphProdOfLocallyCompactRight Y Z) = tensorEquiv Y Z :=
  (rfl)

/-- When `Y` is locally compact, the convenient product `Y ⊗ Z` is homeomorphic to the ordinary
product `Y × Z` via `tensorEquiv`. -/
def tensorHomeomorphProdOfLocallyCompactLeft
    (Y Z : GeneratedByTopCat.{v} X) [LocallyCompactSpace Y] :
    ↑(Y ⊗ Z) ≃ₜ Y × Z :=
  have : IsGeneratedBy X (Y × Z) := IsGeneratedBy.prod_of_locallyCompactSpace_left Y Z
  IsGeneratedBy.homeomorph (X := X) (Y := Y × Z)

@[simp]
theorem coe_tensorHomeomorphProdOfLocallyCompactLeft
    (Y Z : GeneratedByTopCat.{v} X) [LocallyCompactSpace Y] :
    ⇑(tensorHomeomorphProdOfLocallyCompactLeft Y Z) = tensorEquiv Y Z :=
  (rfl)

/-- The internal hom functor `Z ↦ WithGeneratedByTopology X (ContinuousMapGeneratedBy X Y Z)` on
`GeneratedByTopCat X`.

Exposed so that downstream modules and code generation agree on the carrier type of
`(ihom Y).obj Z`. -/
@[expose]
def internalHom (Y : GeneratedByTopCat.{v} X) :
    GeneratedByTopCat.{v} X ⥤ GeneratedByTopCat.{v} X where
  obj Z := of (X := X) (WithGeneratedByTopology X (ContinuousMapGeneratedBy X Y Z))
  map g := homMk (ContinuousMapGeneratedBy.postcomp
    ⟨g, g.hom.hom.continuous.continuousGeneratedBy⟩).prop.continuousMap

private def internalHomEquiv (Y Z : GeneratedByTopCat.{v} X) : ↑((internalHom Y).obj Z) ≃ C(Y, Z) :=
  (WithGeneratedByTopology.equiv (X := X) (Y := ContinuousMapGeneratedBy X Y Z)).trans
    ContinuousMapGeneratedBy.equivContinuousMap

private def curryHom {Y Z T : GeneratedByTopCat.{v} X} (f : Y ⊗ Z ⟶ T) :
    Z ⟶ (internalHom Y).obj T :=
  let f₀ : ContinuousMapGeneratedBy X (Y × Z) T :=
    ⟨f ∘ (tensorEquiv Y Z).symm, continuousGeneratedBy_comp_tensorEquiv_symm f⟩
  homMk ((ContinuousMapGeneratedBy.curryEquiv f₀).toContinuousMap.toGeneratedBy X)

private def uncurryHom {Y Z T : GeneratedByTopCat.{v} X} (g : Z ⟶ (internalHom Y).obj T) :
    Y ⊗ Z ⟶ T :=
  let g₀ : C(Z, ContinuousMapGeneratedBy X Y T) :=
    (WithGeneratedByTopology.counit X (ContinuousMapGeneratedBy X Y T)).comp g.hom.hom
  let h : ContinuousMapGeneratedBy X (Y × Z) T :=
    ContinuousMapGeneratedBy.curryEquiv.symm (g₀.toContinuousMapGeneratedBy X)
  homMk ((WithGeneratedByTopology.counit X T).comp h.prop.continuousMap)

private theorem internalHomEquiv_map_apply {Y Z T : GeneratedByTopCat.{v} X}
    (g : Z ⟶ T) (f : ↑((internalHom Y).obj Z)) (y : Y) :
    internalHomEquiv Y T (((internalHom Y).map g) f) y = g (internalHomEquiv Y Z f y) := by
  let f₀ : WithGeneratedByTopology X (ContinuousMapGeneratedBy X Y Z) := f
  let p : ContinuousMapGeneratedBy X Z T := ⟨g, g.hom.hom.continuous.continuousGeneratedBy⟩
  change ContinuousMapGeneratedBy.equivContinuousMap
      (WithGeneratedByTopology.equiv (X := X) (p.postcomp.prop.continuousMap f₀)) y =
    g (ContinuousMapGeneratedBy.equivContinuousMap (WithGeneratedByTopology.equiv (X := X) f₀) y)
  simp [p]
  rfl

private theorem internalHomEquiv_curryHom_apply {Y Z T : GeneratedByTopCat.{v} X}
    (f : Y ⊗ Z ⟶ T) (z : Z) (y : Y) :
    internalHomEquiv Y T (curryHom f z) y = f ((tensorEquiv Y Z).symm (y, z)) := by
  let f₀ : ContinuousMapGeneratedBy X (Y × Z) T :=
    ⟨f ∘ (tensorEquiv Y Z).symm, continuousGeneratedBy_comp_tensorEquiv_symm f⟩
  change ContinuousMapGeneratedBy.equivContinuousMap
      (WithGeneratedByTopology.equiv (X := X)
        (((ContinuousMapGeneratedBy.curryEquiv f₀).toContinuousMap.toGeneratedBy X) z)) y =
    f ((tensorEquiv Y Z).symm (y, z))
  simp [f₀]
  rfl

private theorem uncurryHom_apply {Y Z T : GeneratedByTopCat.{v} X}
    (g : Z ⟶ (internalHom Y).obj T) (p : ↑(Y ⊗ Z)) :
    uncurryHom g p = internalHomEquiv Y T (g (snd Y Z p)) (fst Y Z p) := by
  let q : WithGeneratedByTopology X (↑Y × ↑Z) := p
  let g' : C(Z, WithGeneratedByTopology X (ContinuousMapGeneratedBy X Y T)) := g.hom.hom
  let g₀ : C(Z, ContinuousMapGeneratedBy X Y T) :=
    (WithGeneratedByTopology.counit X (ContinuousMapGeneratedBy X Y T)).comp g'
  let h : ContinuousMapGeneratedBy X (Y × Z) T :=
    ContinuousMapGeneratedBy.curryEquiv.symm (g₀.toContinuousMapGeneratedBy X)
  change WithGeneratedByTopology.counit X T (h.prop.continuousMap q) =
    ContinuousMapGeneratedBy.equivContinuousMap
      (WithGeneratedByTopology.equiv (X := X)
        (g' (WithGeneratedByTopology.equiv (X := X) (Y := ↑Y × ↑Z) q).2))
      (WithGeneratedByTopology.equiv (X := X) (Y := ↑Y × ↑Z) q).1
  simp [h, g₀, ContinuousMapGeneratedBy.curryEquiv]

/-- Currying in `GeneratedByTopCat X`, obtained from `ContinuousMapGeneratedBy.curryEquiv` through
the `X`-generated coreflection. -/
def curryEquiv (Y Z T : GeneratedByTopCat.{v} X) :
    (Y ⊗ Z ⟶ T) ≃ (Z ⟶ (internalHom Y).obj T) where
  toFun := curryHom
  invFun := uncurryHom
  left_inv f := by
    ext p
    rw [uncurryHom_apply, internalHomEquiv_curryHom_apply]
    exact congrArg f ((tensorEquiv Y Z).symm_apply_apply p)
  right_inv g := by
    ext z
    apply (internalHomEquiv Y T).injective
    ext y
    rw [internalHomEquiv_curryHom_apply, uncurryHom_apply, fst_tensorEquiv_symm,
      snd_tensorEquiv_symm]

/-- The adjunction `Y ⊗ - ⊣ internalHom Y` in `GeneratedByTopCat X`. -/
def tensorLeftAdjunction (Y : GeneratedByTopCat.{v} X) :
    tensorLeft Y ⊣ internalHom Y :=
  Adjunction.mkOfHomEquiv
    { homEquiv := curryEquiv Y
      homEquiv_naturality_left_symm f g := by ext p; simp [curryEquiv, uncurryHom_apply]
      homEquiv_naturality_right f g := by
        ext z
        apply (internalHomEquiv Y _).injective
        ext y
        simp [curryEquiv, internalHomEquiv_curryHom_apply, internalHomEquiv_map_apply] }

/-- When all test spaces `X i` are locally compact and their pairwise products are `X`-generated,
`GeneratedByTopCat X` is cartesian closed. -/
instance instMonoidalClosed : MonoidalClosed (GeneratedByTopCat.{v} X) where
  closed Y :=
    { rightAdj := internalHom Y
      adj := tensorLeftAdjunction Y }

/-- Elements of `(ihom Y).obj Z` correspond bijectively to continuous maps `C(Y, Z)`. -/
def ihomEquiv (Y Z : GeneratedByTopCat.{v} X) : ↑((ihom Y).obj Z) ≃ C(Y, Z) :=
  internalHomEquiv Y Z

/-- The hom-set bijection of the tensor–hom adjunction in `GeneratedByTopCat X` is `curryEquiv`. -/
theorem homEquiv_def (Y Z T : GeneratedByTopCat.{v} X) :
    (ihom.adjunction Y).homEquiv Z T = curryEquiv Y Z T :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _

@[simp]
theorem ihomEquiv_curryEquiv_apply {Y Z T : GeneratedByTopCat.{v} X}
    (f : Y ⊗ Z ⟶ T) (z : Z) (y : Y) :
    ihomEquiv Y T (curryEquiv Y Z T f z) y = f ((tensorEquiv Y Z).symm (y, z)) :=
  internalHomEquiv_curryHom_apply f z y

@[simp]
theorem curryEquiv_symm_apply {Y Z T : GeneratedByTopCat.{v} X}
    (g : Z ⟶ (ihom Y).obj T) (p : ↑(Y ⊗ Z)) :
    (curryEquiv Y Z T).symm g p = ihomEquiv Y T (g (snd Y Z p)) (fst Y Z p) :=
  uncurryHom_apply g p

@[ext]
theorem ihom_obj_ext {Y Z : GeneratedByTopCat.{v} X} {f g : ↑((ihom Y).obj Z)}
    (h : ∀ y, ihomEquiv Y Z f y = ihomEquiv Y Z g y) : f = g :=
  (ihomEquiv Y Z).injective (ContinuousMap.ext h)

@[simp]
theorem ihomEquiv_map_apply {Y Z T : GeneratedByTopCat.{v} X}
    (g : Z ⟶ T) (f : ↑((ihom Y).obj Z)) (y : Y) :
    ihomEquiv Y T (((ihom Y).map g) f) y = g (ihomEquiv Y Z f y) :=
  internalHomEquiv_map_apply g f y

@[simp]
theorem ihomEquiv_curry_apply {Y Z T : GeneratedByTopCat.{v} X}
    (f : Y ⊗ Z ⟶ T) (z : Z) (y : Y) :
    ihomEquiv Y T (MonoidalClosed.curry f z) y = f ((tensorEquiv Y Z).symm (y, z)) := by
  rw [← MonoidalClosed.homEquiv_apply_eq, homEquiv_def]
  exact ihomEquiv_curryEquiv_apply f z y

@[simp]
theorem uncurry_apply {Y Z T : GeneratedByTopCat.{v} X}
    (g : Z ⟶ (ihom Y).obj T) (p : ↑(Y ⊗ Z)) :
    MonoidalClosed.uncurry g p = ihomEquiv Y T (g (snd Y Z p)) (fst Y Z p) := by
  rw [← MonoidalClosed.homEquiv_symm_apply_eq, homEquiv_def]
  exact curryEquiv_symm_apply g p

/-- Evaluation in `GeneratedByTopCat X` applies the underlying continuous map to a point. -/
theorem ihom_ev_app_apply {Y Z : GeneratedByTopCat.{v} X} (p : ↑(Y ⊗ (ihom Y).obj Z)) :
    ((ihom.ev Y).app Z) p = ihomEquiv Y Z (snd Y _ p) (fst Y _ p) := by
  rw [← MonoidalClosed.uncurry_id_eq_ev, uncurry_apply]
  rfl

/-- Coevaluation in `GeneratedByTopCat X` sends `z` to the slice map `y ↦ (y, z)`. -/
theorem ihomEquiv_ihom_coev_app_apply {Y Z : GeneratedByTopCat.{v} X} (z : Z) (y : Y) :
    ihomEquiv Y (Y ⊗ Z) (((ihom.coev Y).app Z) z) y = (tensorEquiv Y Z).symm (y, z) := by
  rw [← MonoidalClosed.curry_id_eq_coev, ihomEquiv_curry_apply]
  rfl

@[simp]
theorem ihomEquiv_ihomCurry_apply {W Y Z : GeneratedByTopCat.{v} X}
    (f : ↑((ihom (W ⊗ Y)).obj Z)) (y : Y) (w : W) :
    ihomEquiv W Z (ihomEquiv Y ((ihom W).obj Z) (MonoidalClosed.ihomCurry W Y Z f) y) w =
      ihomEquiv (W ⊗ Y) Z f ((tensorEquiv W Y).symm (w, y)) := by
  rw [MonoidalClosed.ihomCurry, ihomEquiv_curry_apply, ihomEquiv_curry_apply, comp_apply,
    ihom_ev_app_apply]
  set q := (tensorEquiv W (Y ⊗ (ihom (W ⊗ Y)).obj Z)).symm
    (w, (tensorEquiv Y ((ihom (W ⊗ Y)).obj Z)).symm (y, f))
  have hfst : fst (W ⊗ Y) _ ((α_ W Y _).inv q) = (tensorEquiv W Y).symm (w, y) := by
    ext
    · rw [← comp_apply, ← comp_apply, associator_inv_fst_fst]
      simp [q]
    · rw [← comp_apply, ← comp_apply, associator_inv_fst_snd]
      simp [q]
  have hsnd : snd (W ⊗ Y) _ ((α_ W Y _).inv q) = f := by
    rw [← comp_apply, associator_inv_snd, comp_apply]
    simp [q]
  rw [hfst, hsnd]

/-- Canonical morphism from the `X`-generated refinement of the compact-open mapping space
`C(Y, Z)` into the internal hom `(ihom Y).obj Z`. -/
def compactOpenToIhom (Y Z : GeneratedByTopCat.{v} X) :
    of (X := X) (WithGeneratedByTopology X C(Y, Z)) ⟶ (ihom Y).obj Z :=
  ofHom (ContinuousMap.toContinuousMapGeneratedBy X).continuous.continuousGeneratedBy.continuousMap

@[simp]
theorem ihomEquiv_compactOpenToIhom_apply (Y Z : GeneratedByTopCat.{v} X)
    (f : WithGeneratedByTopology X C(Y, Z)) :
    ihomEquiv Y Z (compactOpenToIhom Y Z f) =
      WithGeneratedByTopology.equiv (X := X) (Y := C(Y, Z)) f := by
  ext y
  let c := (ContinuousMap.toContinuousMapGeneratedBy X (Y := Y) (Z := Z)).continuous
  change ContinuousMapGeneratedBy.equivContinuousMap
      (WithGeneratedByTopology.equiv (X := X) (c.continuousGeneratedBy.continuousMap f)) y =
    WithGeneratedByTopology.equiv (X := X) (Y := C(Y, Z)) f y
  simp

private def ihomToCompactOpenOfCompactLift {Y : GeneratedByTopCat.{v} X}
    (hK : ∀ ⦃K : Set Y⦄, IsCompact K →
      ∃ (i : ι) (L : Set (X i)) (f : C(X i, Y)), IsCompact L ∧ f '' L = K)
    (Z : GeneratedByTopCat.{v} X) :
    (ihom Y).obj Z ⟶ of (X := X) (WithGeneratedByTopology X C(Y, Z)) :=
  ofHom (ContinuousMapGeneratedBy.homeomorphContinuousMapOfCompactLift
    (X := X) (Z := Z) hK).continuous.continuousGeneratedBy.continuousMap

private theorem equiv_ihomToCompactOpenOfCompactLift_apply {Y : GeneratedByTopCat.{v} X}
    (hK : ∀ ⦃K : Set Y⦄, IsCompact K →
      ∃ (i : ι) (L : Set (X i)) (f : C(X i, Y)), IsCompact L ∧ f '' L = K)
    (Z : GeneratedByTopCat.{v} X) (f : ↑((ihom Y).obj Z)) :
    WithGeneratedByTopology.equiv (X := X) (Y := C(Y, Z))
      (ihomToCompactOpenOfCompactLift hK Z f) = ihomEquiv Y Z f := by
  let f₀ : WithGeneratedByTopology X (ContinuousMapGeneratedBy X Y Z) := f
  ext y
  change WithGeneratedByTopology.equiv (X := X) (Y := C(Y, Z))
      ((ContinuousMapGeneratedBy.homeomorphContinuousMapOfCompactLift
        (X := X) (Z := Z) hK).continuous.continuousGeneratedBy.continuousMap f₀) y =
    ContinuousMapGeneratedBy.equivContinuousMap (WithGeneratedByTopology.equiv (X := X) f₀) y
  simp

/-- When every compact subset of `Y` lifts to a compact subset of some generator `X i`, the
internal hom `(ihom Y).obj Z` is canonically isomorphic to the `X`-generated refinement of the
compact-open mapping space `C(Y, Z)`. -/
def ihomIsoCompactOpenOfCompactLift {Y : GeneratedByTopCat.{v} X}
    (hK : ∀ ⦃K : Set Y⦄, IsCompact K →
      ∃ (i : ι) (L : Set (X i)) (f : C(X i, Y)), IsCompact L ∧ f '' L = K)
    (Z : GeneratedByTopCat.{v} X) :
    (ihom Y).obj Z ≅ of (X := X) (WithGeneratedByTopology X C(Y, Z)) where
  hom := ihomToCompactOpenOfCompactLift hK Z
  inv := compactOpenToIhom Y Z
  hom_inv_id := by
    ext f y
    simp only [comp_apply, id_apply]
    rw [ihomEquiv_compactOpenToIhom_apply, equiv_ihomToCompactOpenOfCompactLift_apply]
  inv_hom_id := by
    ext f
    apply (WithGeneratedByTopology.equiv (X := X) (Y := C(Y, Z))).injective
    simp only [comp_apply, id_apply]
    rw [equiv_ihomToCompactOpenOfCompactLift_apply, ihomEquiv_compactOpenToIhom_apply]

@[simp]
theorem ihomIsoCompactOpenOfCompactLift_inv {Y : GeneratedByTopCat.{v} X}
    (hK : ∀ ⦃K : Set Y⦄, IsCompact K →
      ∃ (i : ι) (L : Set (X i)) (f : C(X i, Y)), IsCompact L ∧ f '' L = K)
    (Z : GeneratedByTopCat.{v} X) :
    (ihomIsoCompactOpenOfCompactLift hK Z).inv = compactOpenToIhom Y Z :=
  (rfl)

@[simp]
theorem equiv_ihomIsoCompactOpenOfCompactLift_hom_apply {Y : GeneratedByTopCat.{v} X}
    (hK : ∀ ⦃K : Set Y⦄, IsCompact K →
      ∃ (i : ι) (L : Set (X i)) (f : C(X i, Y)), IsCompact L ∧ f '' L = K)
    (Z : GeneratedByTopCat.{v} X) (f : ↑((ihom Y).obj Z)) :
    WithGeneratedByTopology.equiv (X := X) (Y := C(Y, Z))
      ((ihomIsoCompactOpenOfCompactLift hK Z).hom f) = ihomEquiv Y Z f :=
  equiv_ihomToCompactOpenOfCompactLift_apply hK Z f

end MonoidalClosed

end GeneratedByTopCat
