/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.CompactlyGenerated.Basic
public import TauCeti.Topology.Convenient.CartesianClosed

/-!
# Cartesian monoidal closed structure on `CompactlyGenerated`

Transporting the convenient-category structure on `GeneratedByTopCat` along the strict equivalence
`CompactlyGenerated.equivGeneratedByTopCat` equips `CompactlyGenerated.{u, w}` with a computable
cartesian monoidal closed structure, with test-space universe `u` independent of the carrier
universe `w`:

* **Cartesian monoidal structure and product comparisons**
  (`CompactlyGenerated.instCartesianMonoidalCategory`,
  `CompactlyGenerated.prodComparison_compactlyGeneratedToTop`,
  `CompactlyGenerated.tensorHomeomorphProd`): the convenient product `X ⊗ Y` refines `X × Y` by
  compact Hausdorff spaces in `Type u`, and agrees with the ordinary topological product if and only
  if `X × Y` is `u`-compactly generated—in particular whenever either factor is locally compact
  (`CompactlyGenerated.tensorHomeomorphProdOfLocallyCompactRight`,
  `CompactlyGenerated.tensorHomeomorphProdOfLocallyCompactLeft`).
* **Cartesian closed structure** (`CompactlyGenerated.instMonoidalClosed`,
  `CompactlyGenerated.ihomEquiv`): the internal hom `(ihom X).obj Z` refines
  `ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) X Z`, with elements corresponding
  bijectively to `C(X, Z)`.
* **Compact-open comparisons and exponential law**: when `X` is `u`-small and Hausdorff,
  `(ihom X).obj Z` is canonically isomorphic to the `u`-compactly generated refinement of the
  compact-open mapping space `C(X, Z)` (`CompactlyGenerated.ihomIsoCompactOpen`). When `Y` is also
  `u`-small and Hausdorff, internal currying gives the convenient compact-open exponential
  isomorphism and homeomorphism (`CompactlyGenerated.compactOpenTensorIso`,
  `CompactlyGenerated.compactOpenTensorHomeomorph`) of Steenrod and Vogt.

## References

* N. E. Steenrod, *A convenient category of topological spaces*, Michigan Math. J. 14 (1967),
  133–152.
* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Arch. Math.
  (Basel) 22 (1971), 545–555.
* M. Escardó, J. Lawson, and A. Simpson, *Comparing Cartesian closed categories of (core)
  compactly generated spaces*, Topology Appl. 143 (2004), 105–145.
-/

public section

universe u v w

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Topology

namespace CompactlyGenerated

/-- `PUnit` is terminal in `CompactlyGenerated`. -/
def isTerminalPUnit : IsTerminal (of PUnit.{w + 1} : CompactlyGenerated.{u, w}) :=
  IsTerminal.ofUniqueHom (fun _ ↦ homMk ⟨fun _ ↦ PUnit.unit, continuous_const⟩) (fun _ _ ↦ by ext)

/-- The explicit binary fan of `X` and `Y` in `CompactlyGenerated.{u, w}` with apex
`WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (X × Y)`.

Exposed so that downstream modules and code generation agree on the carrier type of `X ⊗ Y`. -/
@[expose]
def prodBinaryFan (X Y : CompactlyGenerated.{u, w}) : BinaryFan X Y :=
  BinaryFan.mk
    (P := of (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (X × Y)))
    (fromGeneratedByTopCat.map
      (GeneratedByTopCat.prodBinaryFan (toGeneratedByTopCat.obj X) (toGeneratedByTopCat.obj Y)).fst)
    (fromGeneratedByTopCat.map
      (GeneratedByTopCat.prodBinaryFan (toGeneratedByTopCat.obj X) (toGeneratedByTopCat.obj Y)).snd)

/-- `WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (X × Y)` is a binary product of `X` and `Y`
in `CompactlyGenerated.{u, w}`. -/
def prodBinaryFanIsLimit (X Y : CompactlyGenerated.{u, w}) : IsLimit (prodBinaryFan X Y) :=
  BinaryFan.IsLimit.mk _
    (fun {_} f g ↦ fromGeneratedByTopCat.map <|
      (GeneratedByTopCat.prodBinaryFanIsLimit
        (toGeneratedByTopCat.obj X) (toGeneratedByTopCat.obj Y)).lift
        (BinaryFan.mk (toGeneratedByTopCat.map f) (toGeneratedByTopCat.map g)))
    (fun f g ↦ congrArg fromGeneratedByTopCat.map <|
      (GeneratedByTopCat.prodBinaryFanIsLimit
        (toGeneratedByTopCat.obj X) (toGeneratedByTopCat.obj Y)).fac
        (BinaryFan.mk (toGeneratedByTopCat.map f) (toGeneratedByTopCat.map g)) ⟨.left⟩)
    (fun f g ↦ congrArg fromGeneratedByTopCat.map <|
      (GeneratedByTopCat.prodBinaryFanIsLimit
        (toGeneratedByTopCat.obj X) (toGeneratedByTopCat.obj Y)).fac
        (BinaryFan.mk (toGeneratedByTopCat.map f) (toGeneratedByTopCat.map g)) ⟨.right⟩)
    (fun {_} f g m h₁ h₂ ↦ congrArg fromGeneratedByTopCat.map <|
      (GeneratedByTopCat.prodBinaryFanIsLimit
        (toGeneratedByTopCat.obj X) (toGeneratedByTopCat.obj Y)).uniq
        (BinaryFan.mk (toGeneratedByTopCat.map f) (toGeneratedByTopCat.map g))
        (toGeneratedByTopCat.map m) fun ⟨j⟩ ↦ by
          cases j
          · exact congrArg toGeneratedByTopCat.map h₁
          · exact congrArg toGeneratedByTopCat.map h₂)

instance instCartesianMonoidalCategory : CartesianMonoidalCategory CompactlyGenerated.{u, w} :=
  .ofChosenFiniteProducts ⟨_, isTerminalPUnit⟩
    (fun X Y ↦ ⟨prodBinaryFan X Y, prodBinaryFanIsLimit X Y⟩)

instance instBraidedCategory : BraidedCategory CompactlyGenerated.{u, w} :=
  .ofCartesianMonoidalCategory

instance : Subsingleton ↑(𝟙_ CompactlyGenerated.{u, w}) :=
  inferInstanceAs (Subsingleton PUnit.{w + 1})

instance (X Y : CompactlyGenerated.{u, w}) [T2Space X] [T2Space Y] : T2Space ↑(X ⊗ Y) :=
  inferInstanceAs (T2Space (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (X × Y)))

instance (X Y : CompactlyGenerated.{u, w}) [Small.{v} X] [Small.{v} Y] :
    Small.{v} ↑(X ⊗ Y) :=
  inferInstanceAs (Small.{v} (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) (X × Y)))

/-- The underlying bijection between the convenient product `X ⊗ Y` and `X × Y`. -/
def tensorEquiv (X Y : CompactlyGenerated.{u, w}) : ↑(X ⊗ Y) ≃ X × Y :=
  GeneratedByTopCat.tensorEquiv (toGeneratedByTopCat.obj X) (toGeneratedByTopCat.obj Y)

@[continuity, fun_prop]
theorem continuous_tensorEquiv (X Y : CompactlyGenerated.{u, w}) :
    Continuous (tensorEquiv X Y) :=
  GeneratedByTopCat.continuous_tensorEquiv (toGeneratedByTopCat.obj X) (toGeneratedByTopCat.obj Y)

@[simp]
theorem tensorEquiv_fst {X Y : CompactlyGenerated.{u, w}} (p : ↑(X ⊗ Y)) :
    (tensorEquiv X Y p).1 = fst X Y p :=
  GeneratedByTopCat.tensorEquiv_fst (Y := toGeneratedByTopCat.obj X)
    (Z := toGeneratedByTopCat.obj Y) p

@[simp]
theorem tensorEquiv_snd {X Y : CompactlyGenerated.{u, w}} (p : ↑(X ⊗ Y)) :
    (tensorEquiv X Y p).2 = snd X Y p :=
  GeneratedByTopCat.tensorEquiv_snd (Y := toGeneratedByTopCat.obj X)
    (Z := toGeneratedByTopCat.obj Y) p

@[simp]
theorem fst_tensorEquiv_symm {X Y : CompactlyGenerated.{u, w}} (x : X) (y : Y) :
    fst X Y ((tensorEquiv X Y).symm (x, y)) = x :=
  GeneratedByTopCat.fst_tensorEquiv_symm (Y := toGeneratedByTopCat.obj X)
    (Z := toGeneratedByTopCat.obj Y) x y

@[simp]
theorem snd_tensorEquiv_symm {X Y : CompactlyGenerated.{u, w}} (x : X) (y : Y) :
    snd X Y ((tensorEquiv X Y).symm (x, y)) = y :=
  GeneratedByTopCat.snd_tensorEquiv_symm (Y := toGeneratedByTopCat.obj X)
    (Z := toGeneratedByTopCat.obj Y) x y

@[simp]
theorem tensorEquiv_symm_fst_snd {X Y : CompactlyGenerated.{u, w}} (p : ↑(X ⊗ Y)) :
    (tensorEquiv X Y).symm (fst X Y p, snd X Y p) = p :=
  GeneratedByTopCat.tensorEquiv_symm_fst_snd (Y := toGeneratedByTopCat.obj X)
    (Z := toGeneratedByTopCat.obj Y) p

@[ext]
theorem tensorObj_ext {X Y : CompactlyGenerated.{u, w}} {p q : ↑(X ⊗ Y)}
    (h₁ : fst X Y p = fst X Y q) (h₂ : snd X Y p = snd X Y q) : p = q :=
  GeneratedByTopCat.tensorObj_ext (X := fun K : CompHaus.{u} ↦ K)
    (Y := toGeneratedByTopCat.obj X) (Z := toGeneratedByTopCat.obj Y) h₁ h₂

@[simp]
theorem lift_apply {W X Y : CompactlyGenerated.{u, w}} (f : W ⟶ X) (g : W ⟶ Y) (w : W) :
    lift f g w = (tensorEquiv X Y).symm (f w, g w) :=
  GeneratedByTopCat.lift_apply (toGeneratedByTopCat.map f) (toGeneratedByTopCat.map g) w

theorem tensorEquiv_lift_apply {W X Y : CompactlyGenerated.{u, w}}
    (f : W ⟶ X) (g : W ⟶ Y) (w : W) :
    tensorEquiv X Y (lift f g w) = (f w, g w) :=
  GeneratedByTopCat.tensorEquiv_lift_apply (toGeneratedByTopCat.map f)
    (toGeneratedByTopCat.map g) w

@[simp]
theorem tensorHom_apply {W₁ W₂ X₁ X₂ : CompactlyGenerated.{u, w}}
    (f : W₁ ⟶ W₂) (g : X₁ ⟶ X₂) (p : ↑(W₁ ⊗ X₁)) :
    (f ⊗ₘ g) p = (tensorEquiv W₂ X₂).symm (f (fst W₁ X₁ p), g (snd W₁ X₁ p)) :=
  GeneratedByTopCat.tensorHom_apply (toGeneratedByTopCat.map f) (toGeneratedByTopCat.map g) p

@[simp]
theorem whiskerLeft_apply (W : CompactlyGenerated.{u, w}) {X Y : CompactlyGenerated.{u, w}}
    (f : X ⟶ Y) (p : ↑(W ⊗ X)) :
    (W ◁ f) p = (tensorEquiv W Y).symm (fst W X p, f (snd W X p)) :=
  GeneratedByTopCat.whiskerLeft_apply (toGeneratedByTopCat.obj W) (toGeneratedByTopCat.map f) p

@[simp]
theorem whiskerRight_apply {W X : CompactlyGenerated.{u, w}} (f : W ⟶ X)
    (Y : CompactlyGenerated.{u, w}) (p : ↑(W ⊗ Y)) :
    (f ▷ Y) p = (tensorEquiv X Y).symm (f (fst W Y p), snd W Y p) :=
  GeneratedByTopCat.whiskerRight_apply (toGeneratedByTopCat.map f) (toGeneratedByTopCat.obj Y) p

@[simp]
theorem braiding_hom_apply {X Y : CompactlyGenerated.{u, w}} (p : ↑(X ⊗ Y)) :
    (β_ X Y).hom p = (tensorEquiv Y X).symm (snd X Y p, fst X Y p) :=
  GeneratedByTopCat.braiding_hom_apply (Y := toGeneratedByTopCat.obj X)
    (Z := toGeneratedByTopCat.obj Y) p

@[simp]
theorem braiding_inv_apply {X Y : CompactlyGenerated.{u, w}} (p : ↑(Y ⊗ X)) :
    (β_ X Y).inv p = (tensorEquiv X Y).symm (snd Y X p, fst Y X p) :=
  GeneratedByTopCat.braiding_inv_apply (Y := toGeneratedByTopCat.obj X)
    (Z := toGeneratedByTopCat.obj Y) p

@[simp]
theorem leftUnitor_hom_apply {X : CompactlyGenerated.{u, w}}
    (p : ↑(𝟙_ CompactlyGenerated.{u, w} ⊗ X)) :
    (λ_ X).hom p = snd _ X p :=
  (rfl)

@[simp]
theorem leftUnitor_inv_apply {X : CompactlyGenerated.{u, w}} (x : X) :
    (λ_ X).inv x = (tensorEquiv _ X).symm (PUnit.unit, x) := by
  ext
  · exact Subsingleton.elim _ _
  · simp [← comp_apply]

@[simp]
theorem rightUnitor_hom_apply {X : CompactlyGenerated.{u, w}}
    (p : ↑(X ⊗ 𝟙_ CompactlyGenerated.{u, w})) :
    (ρ_ X).hom p = fst X _ p :=
  (rfl)

@[simp]
theorem rightUnitor_inv_apply {X : CompactlyGenerated.{u, w}} (x : X) :
    (ρ_ X).inv x = (tensorEquiv X _).symm (x, PUnit.unit) := by
  ext
  · simp [← comp_apply]
  · exact Subsingleton.elim _ _

@[simp]
theorem associator_hom_apply {W X Y : CompactlyGenerated.{u, w}} (p : ↑((W ⊗ X) ⊗ Y)) :
    (α_ W X Y).hom p =
      (tensorEquiv W (X ⊗ Y)).symm
        (fst W X (fst (W ⊗ X) Y p),
          (tensorEquiv X Y).symm (snd W X (fst (W ⊗ X) Y p), snd (W ⊗ X) Y p)) :=
  GeneratedByTopCat.associator_hom_apply (W := toGeneratedByTopCat.obj W)
    (Y := toGeneratedByTopCat.obj X) (Z := toGeneratedByTopCat.obj Y) p

@[simp]
theorem associator_inv_apply {W X Y : CompactlyGenerated.{u, w}} (p : ↑(W ⊗ (X ⊗ Y))) :
    (α_ W X Y).inv p =
      (tensorEquiv (W ⊗ X) Y).symm
        ((tensorEquiv W X).symm (fst W (X ⊗ Y) p, fst X Y (snd W (X ⊗ Y) p)),
          snd X Y (snd W (X ⊗ Y) p)) :=
  GeneratedByTopCat.associator_inv_apply (W := toGeneratedByTopCat.obj W)
    (Y := toGeneratedByTopCat.obj X) (Z := toGeneratedByTopCat.obj Y) p

/-- The canonical product comparison `(X ⊗ Y).toTop ⟶ X.toTop ⊗ Y.toTop` in `TopCat` is the
compact-generation counit on `X × Y`. -/
theorem prodComparison_compactlyGeneratedToTop (X Y : CompactlyGenerated.{u, w}) :
    CartesianMonoidalCategory.prodComparison compactlyGeneratedToTop X Y =
      adjCounit.app (X.toTop ⊗ Y.toTop) :=
  (GeneratedByTopCat.prodComparison_toTopCat
    (toGeneratedByTopCat.obj X) (toGeneratedByTopCat.obj Y)).trans
    (adjCounit_app (X.toTop ⊗ Y.toTop)).symm

@[simp]
theorem prodComparison_compactlyGeneratedToTop_apply (X Y : CompactlyGenerated.{u, w})
    (p : ↑(X ⊗ Y)) :
    CartesianMonoidalCategory.prodComparison compactlyGeneratedToTop X Y p = tensorEquiv X Y p :=
  GeneratedByTopCat.prodComparison_toTopCat_apply (toGeneratedByTopCat.obj X)
    (toGeneratedByTopCat.obj Y) p

/-- The convenient product `X ⊗ Y` has the ordinary product topology if and only if `X × Y` is
`u`-compactly generated. -/
theorem isIso_prodComparison_compactlyGeneratedToTop_iff (X Y : CompactlyGenerated.{u, w}) :
    IsIso (CartesianMonoidalCategory.prodComparison compactlyGeneratedToTop X Y) ↔
      UCompactlyGeneratedSpace.{u} (X × Y) :=
  (GeneratedByTopCat.isIso_prodComparison_toTopCat_iff
    (toGeneratedByTopCat.obj X) (toGeneratedByTopCat.obj Y)).trans
    (Topology.isGeneratedBy_compHaus_iff (X × Y))

/-- When `X × Y` is `u`-compactly generated, the product comparison in `TopCat` is an
isomorphism. -/
instance instIsIsoProdComparisonCompactlyGeneratedToTop
    (X Y : CompactlyGenerated.{u, w}) [UCompactlyGeneratedSpace.{u} (X × Y)] :
    IsIso (CartesianMonoidalCategory.prodComparison compactlyGeneratedToTop X Y) :=
  (isIso_prodComparison_compactlyGeneratedToTop_iff X Y).2 inferInstance

private instance (X Y : CompactlyGenerated.{u, w}) [UCompactlyGeneratedSpace.{u} (X × Y)] :
    IsGeneratedBy (fun K : CompHaus.{u} ↦ K)
      (↑(toGeneratedByTopCat.obj X) × ↑(toGeneratedByTopCat.obj Y)) :=
  inferInstanceAs (IsGeneratedBy _ (X × Y))

/-- When `X × Y` is `u`-compactly generated, the convenient product `X ⊗ Y` is homeomorphic to the
ordinary product `X × Y` via `tensorEquiv`. -/
def tensorHomeomorphProd (X Y : CompactlyGenerated.{u, w})
    [UCompactlyGeneratedSpace.{u} (X × Y)] :
    ↑(X ⊗ Y) ≃ₜ X × Y :=
  GeneratedByTopCat.tensorHomeomorphProd (toGeneratedByTopCat.obj X) (toGeneratedByTopCat.obj Y)

@[simp]
theorem coe_tensorHomeomorphProd (X Y : CompactlyGenerated.{u, w})
    [UCompactlyGeneratedSpace.{u} (X × Y)] :
    ⇑(tensorHomeomorphProd X Y) = tensorEquiv X Y :=
  GeneratedByTopCat.coe_tensorHomeomorphProd (toGeneratedByTopCat.obj X) (toGeneratedByTopCat.obj Y)

@[simp]
theorem coe_tensorHomeomorphProd_symm (X Y : CompactlyGenerated.{u, w})
    [UCompactlyGeneratedSpace.{u} (X × Y)] :
    ⇑(tensorHomeomorphProd X Y).symm = (tensorEquiv X Y).symm :=
  GeneratedByTopCat.coe_tensorHomeomorphProd_symm
    (toGeneratedByTopCat.obj X) (toGeneratedByTopCat.obj Y)

/-- Any continuous map from a `u`-compactly generated space into `X × Y` lifts continuously into
`X ⊗ Y` via `(tensorEquiv X Y).symm`. -/
theorem continuous_tensorEquiv_symm_comp {A : Type*} [TopologicalSpace A]
    [UCompactlyGeneratedSpace.{u} A] {X Y : CompactlyGenerated.{u, w}}
    {g : A → X × Y} (hg : Continuous g) :
    Continuous ((tensorEquiv X Y).symm ∘ g) :=
  GeneratedByTopCat.continuous_tensorEquiv_symm_comp
    (Y := toGeneratedByTopCat.obj X) (Z := toGeneratedByTopCat.obj Y) hg

/-- When `Y` is locally compact, the product comparison in `TopCat` is an isomorphism. -/
instance instIsIsoProdComparisonCompactlyGeneratedToTopOfLocallyCompactRight
    (X Y : CompactlyGenerated.{u, w}) [LocallyCompactSpace Y] :
    IsIso (CartesianMonoidalCategory.prodComparison compactlyGeneratedToTop X Y) := by
  have := TauCeti.uCompactlyGeneratedSpace_prod_of_locallyCompactSpace_right.{u} X Y
  infer_instance

/-- When `X` is locally compact, the product comparison in `TopCat` is an isomorphism. -/
instance instIsIsoProdComparisonCompactlyGeneratedToTopOfLocallyCompactLeft
    (X Y : CompactlyGenerated.{u, w}) [LocallyCompactSpace X] :
    IsIso (CartesianMonoidalCategory.prodComparison compactlyGeneratedToTop X Y) := by
  have := TauCeti.uCompactlyGeneratedSpace_prod_of_locallyCompactSpace_left.{u} X Y
  infer_instance

/-- When `Y` is locally compact, the convenient product `X ⊗ Y` is homeomorphic to the ordinary
product `X × Y` via `tensorEquiv`. -/
def tensorHomeomorphProdOfLocallyCompactRight
    (X Y : CompactlyGenerated.{u, w}) [LocallyCompactSpace Y] :
    ↑(X ⊗ Y) ≃ₜ X × Y :=
  have := TauCeti.uCompactlyGeneratedSpace_prod_of_locallyCompactSpace_right.{u} X Y
  tensorHomeomorphProd X Y

@[simp]
theorem coe_tensorHomeomorphProdOfLocallyCompactRight
    (X Y : CompactlyGenerated.{u, w}) [LocallyCompactSpace Y] :
    ⇑(tensorHomeomorphProdOfLocallyCompactRight X Y) = tensorEquiv X Y :=
  have := TauCeti.uCompactlyGeneratedSpace_prod_of_locallyCompactSpace_right.{u} X Y
  coe_tensorHomeomorphProd X Y

@[simp]
theorem coe_tensorHomeomorphProdOfLocallyCompactRight_symm
    (X Y : CompactlyGenerated.{u, w}) [LocallyCompactSpace Y] :
    ⇑(tensorHomeomorphProdOfLocallyCompactRight X Y).symm = (tensorEquiv X Y).symm :=
  have := TauCeti.uCompactlyGeneratedSpace_prod_of_locallyCompactSpace_right.{u} X Y
  coe_tensorHomeomorphProd_symm X Y

/-- When `X` is locally compact, the convenient product `X ⊗ Y` is homeomorphic to the ordinary
product `X × Y` via `tensorEquiv`. -/
def tensorHomeomorphProdOfLocallyCompactLeft
    (X Y : CompactlyGenerated.{u, w}) [LocallyCompactSpace X] :
    ↑(X ⊗ Y) ≃ₜ X × Y :=
  have := TauCeti.uCompactlyGeneratedSpace_prod_of_locallyCompactSpace_left.{u} X Y
  tensorHomeomorphProd X Y

@[simp]
theorem coe_tensorHomeomorphProdOfLocallyCompactLeft
    (X Y : CompactlyGenerated.{u, w}) [LocallyCompactSpace X] :
    ⇑(tensorHomeomorphProdOfLocallyCompactLeft X Y) = tensorEquiv X Y :=
  have := TauCeti.uCompactlyGeneratedSpace_prod_of_locallyCompactSpace_left.{u} X Y
  coe_tensorHomeomorphProd X Y

@[simp]
theorem coe_tensorHomeomorphProdOfLocallyCompactLeft_symm
    (X Y : CompactlyGenerated.{u, w}) [LocallyCompactSpace X] :
    ⇑(tensorHomeomorphProdOfLocallyCompactLeft X Y).symm = (tensorEquiv X Y).symm :=
  have := TauCeti.uCompactlyGeneratedSpace_prod_of_locallyCompactSpace_left.{u} X Y
  coe_tensorHomeomorphProd_symm X Y

/-- The internal hom functor on `CompactlyGenerated.{u, w}`.

Exposed so that downstream modules and code generation agree on the carrier type of
`(ihom X).obj Z`. -/
@[expose]
def internalHom (X : CompactlyGenerated.{u, w}) :
    CompactlyGenerated.{u, w} ⥤ CompactlyGenerated.{u, w} :=
  toGeneratedByTopCat ⋙ GeneratedByTopCat.internalHom (toGeneratedByTopCat.obj X) ⋙
    fromGeneratedByTopCat

/-- The adjunction `X ⊗ - ⊣ internalHom X` in `CompactlyGenerated.{u, w}`, transported from
`GeneratedByTopCat.tensorLeftAdjunction` along `equivGeneratedByTopCat`. -/
def tensorLeftAdjunction (X : CompactlyGenerated.{u, w}) :
    tensorLeft X ⊣ internalHom X where
  unit :=
    { app Y := fromGeneratedByTopCat.map
        ((GeneratedByTopCat.tensorLeftAdjunction (toGeneratedByTopCat.obj X)).unit.app
          (toGeneratedByTopCat.obj Y))
      naturality _ _ f := congrArg fromGeneratedByTopCat.map <|
        (GeneratedByTopCat.tensorLeftAdjunction (toGeneratedByTopCat.obj X)).unit.naturality
          (toGeneratedByTopCat.map f) }
  counit :=
    { app Z := fromGeneratedByTopCat.map
        ((GeneratedByTopCat.tensorLeftAdjunction (toGeneratedByTopCat.obj X)).counit.app
          (toGeneratedByTopCat.obj Z))
      naturality _ _ g := congrArg fromGeneratedByTopCat.map <|
        (GeneratedByTopCat.tensorLeftAdjunction (toGeneratedByTopCat.obj X)).counit.naturality
          (toGeneratedByTopCat.map g) }
  left_triangle_components Y := congrArg fromGeneratedByTopCat.map <|
    (GeneratedByTopCat.tensorLeftAdjunction
      (toGeneratedByTopCat.obj X)).left_triangle_components (toGeneratedByTopCat.obj Y)
  right_triangle_components Z := congrArg fromGeneratedByTopCat.map <|
    (GeneratedByTopCat.tensorLeftAdjunction
      (toGeneratedByTopCat.obj X)).right_triangle_components (toGeneratedByTopCat.obj Z)

/-- `CompactlyGenerated.{u, w}` is cartesian closed for any test-space universe `u` and carrier
universe `w`. -/
instance instMonoidalClosed : MonoidalClosed CompactlyGenerated.{u, w} where
  closed X :=
    { rightAdj := internalHom X
      adj := tensorLeftAdjunction X }

/-- Elements of `(ihom X).obj Z` correspond bijectively to continuous maps `C(X, Z)`. -/
def ihomEquiv (X Z : CompactlyGenerated.{u, w}) : ↑((ihom X).obj Z) ≃ C(X, Z) :=
  GeneratedByTopCat.ihomEquiv (toGeneratedByTopCat.obj X) (toGeneratedByTopCat.obj Z)

@[simp]
theorem ihomEquiv_ihom_adjunction_homEquiv_apply {X Y Z : CompactlyGenerated.{u, w}}
    (f : X ⊗ Y ⟶ Z) (y : Y) (x : X) :
    dsimp% ihomEquiv X Z (((ihom.adjunction X).homEquiv Y Z f) y) x =
      f ((tensorEquiv X Y).symm (x, y)) :=
  GeneratedByTopCat.ihomEquiv_ihom_adjunction_homEquiv_apply
    (Y := toGeneratedByTopCat.obj X) (Z := toGeneratedByTopCat.obj Y)
    (T := toGeneratedByTopCat.obj Z) (toGeneratedByTopCat.map f) y x

@[simp]
theorem ihom_adjunction_homEquiv_symm_apply {X Y Z : CompactlyGenerated.{u, w}}
    (g : Y ⟶ (ihom X).obj Z) (p : ↑(X ⊗ Y)) :
    dsimp% (((ihom.adjunction X).homEquiv Y Z).symm g) p =
      ihomEquiv X Z (g (snd X Y p)) (fst X Y p) :=
  GeneratedByTopCat.ihom_adjunction_homEquiv_symm_apply (toGeneratedByTopCat.map g) p

@[ext]
theorem ihom_obj_ext {X Z : CompactlyGenerated.{u, w}} {f g : ↑((ihom X).obj Z)}
    (h : ∀ x, ihomEquiv X Z f x = ihomEquiv X Z g x) : f = g :=
  GeneratedByTopCat.ihom_obj_ext (X := fun K : CompHaus.{u} ↦ K)
    (Y := toGeneratedByTopCat.obj X) (Z := toGeneratedByTopCat.obj Z) h

@[simp]
theorem ihomEquiv_ihom_map_apply {X Y Z : CompactlyGenerated.{u, w}}
    (g : Y ⟶ Z) (f : ↑((ihom X).obj Y)) (x : X) :
    ihomEquiv X Z (((ihom X).map g) f) x = g (ihomEquiv X Y f x) :=
  GeneratedByTopCat.ihomEquiv_ihom_map_apply (toGeneratedByTopCat.map g) f x

@[simp]
theorem ihomEquiv_curry_apply {X Y Z : CompactlyGenerated.{u, w}}
    (f : X ⊗ Y ⟶ Z) (y : Y) (x : X) :
    ihomEquiv X Z (MonoidalClosed.curry f y) x = f ((tensorEquiv X Y).symm (x, y)) :=
  GeneratedByTopCat.ihomEquiv_curry_apply
    (Y := toGeneratedByTopCat.obj X) (Z := toGeneratedByTopCat.obj Y)
    (T := toGeneratedByTopCat.obj Z) (toGeneratedByTopCat.map f) y x

@[simp]
theorem uncurry_apply {X Y Z : CompactlyGenerated.{u, w}}
    (g : Y ⟶ (ihom X).obj Z) (p : ↑(X ⊗ Y)) :
    MonoidalClosed.uncurry g p = ihomEquiv X Z (g (snd X Y p)) (fst X Y p) :=
  GeneratedByTopCat.uncurry_apply (toGeneratedByTopCat.map g) p

/-- Evaluation in `CompactlyGenerated` applies the underlying continuous map to a point. -/
@[simp]
theorem ihom_ev_app_apply {X Z : CompactlyGenerated.{u, w}} (p : ↑(X ⊗ (ihom X).obj Z)) :
    ConcreteCategory.hom (X := X ⊗ (ihom X).obj Z) (Y := Z) ((ihom.ev X).app Z) p =
      ihomEquiv X Z (snd X _ p) (fst X _ p) :=
  GeneratedByTopCat.ihom_ev_app_apply (Y := toGeneratedByTopCat.obj X)
    (Z := toGeneratedByTopCat.obj Z) p

/-- Coevaluation in `CompactlyGenerated` sends `y` to the slice map `x ↦ (x, y)`. -/
@[simp]
theorem ihomEquiv_ihom_coev_app_apply {X Y : CompactlyGenerated.{u, w}} (y : Y) (x : X) :
    ihomEquiv X (X ⊗ Y)
      (ConcreteCategory.hom (X := Y) (Y := (ihom X).obj (X ⊗ Y)) ((ihom.coev X).app Y) y) x =
      (tensorEquiv X Y).symm (x, y) :=
  GeneratedByTopCat.ihomEquiv_ihom_coev_app_apply (Y := toGeneratedByTopCat.obj X)
    (Z := toGeneratedByTopCat.obj Y) y x

@[simp]
theorem ihomEquiv_pre_app_apply {W X Z : CompactlyGenerated.{u, w}}
    (f : W ⟶ X) (g : ↑((ihom X).obj Z)) (w : W) :
    ihomEquiv W Z (((MonoidalClosed.pre f).app Z) g) w = ihomEquiv X Z g (f w) :=
  GeneratedByTopCat.ihomEquiv_pre_app_apply (Z := toGeneratedByTopCat.obj Z)
    (toGeneratedByTopCat.map f) g w

@[simp]
theorem ihomEquiv_ihomCurry_apply {X Y Z : CompactlyGenerated.{u, w}}
    (f : ↑((ihom (X ⊗ Y)).obj Z)) (y : Y) (x : X) :
    ihomEquiv X Z (ihomEquiv Y ((ihom X).obj Z) (MonoidalClosed.ihomCurry X Y Z f) y) x =
      ihomEquiv (X ⊗ Y) Z f ((tensorEquiv X Y).symm (x, y)) :=
  GeneratedByTopCat.ihomEquiv_ihomCurry_apply (W := toGeneratedByTopCat.obj X)
    (Y := toGeneratedByTopCat.obj Y) (Z := toGeneratedByTopCat.obj Z) f y x

@[simp]
theorem ihomEquiv_ihomUncurry_apply {X Y Z : CompactlyGenerated.{u, w}}
    (g : ↑((ihom Y).obj ((ihom X).obj Z))) (p : ↑(X ⊗ Y)) :
    ihomEquiv (X ⊗ Y) Z (MonoidalClosed.ihomUncurry X Y Z g) p =
      ihomEquiv X Z (ihomEquiv Y ((ihom X).obj Z) g (snd X Y p)) (fst X Y p) :=
  GeneratedByTopCat.ihomEquiv_ihomUncurry_apply (W := toGeneratedByTopCat.obj X)
    (Y := toGeneratedByTopCat.obj Y) (Z := toGeneratedByTopCat.obj Z) g p

/-- Canonical morphism from the `u`-compactly generated refinement of the compact-open mapping
space `C(X, Z)` into `(ihom X).obj Z`. -/
def compactOpenToIhom (X Z : CompactlyGenerated.{u, w}) :
    of (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) C(X, Z)) ⟶ (ihom X).obj Z :=
  fromGeneratedByTopCat.map <|
    GeneratedByTopCat.compactOpenToIhom (toGeneratedByTopCat.obj X) (toGeneratedByTopCat.obj Z)

@[simp]
theorem compactOpenToIhom_apply (X Z : CompactlyGenerated.{u, w})
    (f : WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) C(X, Z)) :
    dsimp% compactOpenToIhom X Z f =
      (ihomEquiv X Z).symm
        (WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := C(X, Z)) f) :=
  GeneratedByTopCat.compactOpenToIhom_apply
    (toGeneratedByTopCat.obj X) (toGeneratedByTopCat.obj Z) f

/-- When `X` is `u`-small and Hausdorff, the internal hom `(ihom X).obj Z` is canonically
isomorphic to the `u`-compactly generated refinement of the compact-open mapping space `C(X, Z)`. -/
def ihomIsoCompactOpen (X Z : CompactlyGenerated.{u, w}) [Small.{u} X] [T2Space X] :
    (ihom X).obj Z ≅ of (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) C(X, Z)) :=
  fromGeneratedByTopCat.mapIso <|
    GeneratedByTopCat.ihomIsoCompactOpenOfExistsIUnionIsCompactImageEq
      (Y := toGeneratedByTopCat.obj X)
      (fun _ hKc ↦ by
        obtain ⟨S, L, f, hLc, hEq⟩ := hKc.exists_compHaus_isCompact_image_eq
        exact ⟨1, fun _ ↦ S, fun _ ↦ L, fun _ ↦ f, fun _ ↦ hLc,
          by simpa [Set.iUnion_const] using hEq⟩)
      (toGeneratedByTopCat.obj Z)

@[simp]
theorem ihomIsoCompactOpen_inv (X Z : CompactlyGenerated.{u, w}) [Small.{u} X] [T2Space X] :
    (ihomIsoCompactOpen X Z).inv = compactOpenToIhom X Z :=
  congrArg fromGeneratedByTopCat.map <|
    GeneratedByTopCat.ihomIsoCompactOpenOfExistsIUnionIsCompactImageEq_inv
      (Y := toGeneratedByTopCat.obj X) _ (toGeneratedByTopCat.obj Z)

@[simp]
theorem ihomIsoCompactOpen_hom_apply (X Z : CompactlyGenerated.{u, w})
    [Small.{u} X] [T2Space X] (f : ↑((ihom X).obj Z)) :
    dsimp% (ihomIsoCompactOpen X Z).hom f =
      (WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := C(X, Z))).symm
        (ihomEquiv X Z f) :=
  GeneratedByTopCat.ihomIsoCompactOpenOfExistsIUnionIsCompactImageEq_hom_apply
    (Y := toGeneratedByTopCat.obj X) _ (toGeneratedByTopCat.obj Z) f

/-- **Convenient compact-open exponential isomorphism** (Steenrod, Theorem 5.6; Vogt, 1971): for
`u`-small Hausdorff `u`-compactly generated spaces `X` and `Y` and any `u`-compactly generated
space `Z`, the `u`-compactly generated refinement of `C(↑(X ⊗ Y), Z)` is canonically isomorphic in
`CompactlyGenerated.{u, w}` to the `u`-compactly generated refinement of
`C(Y, WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) C(X, Z))`. -/
def compactOpenTensorIso (X Y Z : CompactlyGenerated.{u, w})
    [Small.{u} X] [T2Space X] [Small.{u} Y] [T2Space Y] :
    of (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) C(↑(X ⊗ Y), Z)) ≅
      of (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K)
        C(Y, WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) C(X, Z))) :=
  (ihomIsoCompactOpen (X ⊗ Y) Z).symm ≪≫ MonoidalClosed.ihomCurryIso X Y Z ≪≫
    (ihom Y).mapIso (ihomIsoCompactOpen X Z) ≪≫ ihomIsoCompactOpen Y _

/-- **Convenient compact-open exponential homeomorphism** (Steenrod, Theorem 5.6; Vogt, 1971):
underlying homeomorphism of `CompactlyGenerated.compactOpenTensorIso`. -/
def compactOpenTensorHomeomorph (X Y Z : CompactlyGenerated.{u, w})
    [Small.{u} X] [T2Space X] [Small.{u} Y] [T2Space Y] :
    WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) C(↑(X ⊗ Y), Z) ≃ₜ
      WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K)
        C(Y, WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) C(X, Z)) :=
  homeoOfIso (compactOpenTensorIso X Y Z)

@[simp]
theorem compactOpenTensorIso_hom_apply (X Y Z : CompactlyGenerated.{u, w})
    [Small.{u} X] [T2Space X] [Small.{u} Y] [T2Space Y]
    (f : WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) C(↑(X ⊗ Y), Z)) :
    (compactOpenTensorIso X Y Z).hom f = compactOpenTensorHomeomorph X Y Z f :=
  (rfl)

@[simp]
theorem compactOpenTensorIso_inv_apply (X Y Z : CompactlyGenerated.{u, w})
    [Small.{u} X] [T2Space X] [Small.{u} Y] [T2Space Y]
    (g : WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K)
      C(Y, WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) C(X, Z))) :
    (compactOpenTensorIso X Y Z).inv g = (compactOpenTensorHomeomorph X Y Z).symm g :=
  (rfl)

@[simp]
theorem equiv_equiv_compactOpenTensorHomeomorph_apply (X Y Z : CompactlyGenerated.{u, w})
    [Small.{u} X] [T2Space X] [Small.{u} Y] [T2Space Y]
    (f : WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) C(↑(X ⊗ Y), Z)) (y : Y) (x : X) :
    WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := C(X, Z))
      (WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K)
        (Y := C(Y, WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) C(X, Z)))
        (compactOpenTensorHomeomorph X Y Z f) y) x =
      WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := C(↑(X ⊗ Y), Z)) f
        ((tensorEquiv X Y).symm (x, y)) := by
  rw [compactOpenTensorHomeomorph, homeoOfIso_apply, compactOpenTensorIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, MonoidalClosed.ihomCurryIso_hom,
    ConcreteCategory.comp_apply]
  rw [ihomIsoCompactOpen_hom_apply, Equiv.apply_symm_apply, ihomEquiv_ihom_map_apply]
  simp

@[simp]
theorem equiv_compactOpenTensorHomeomorph_symm_apply (X Y Z : CompactlyGenerated.{u, w})
    [Small.{u} X] [T2Space X] [Small.{u} Y] [T2Space Y]
    (g : WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K)
      C(Y, WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) C(X, Z)))
    (p : ↑(X ⊗ Y)) :
    WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := C(↑(X ⊗ Y), Z))
      ((compactOpenTensorHomeomorph X Y Z).symm g) p =
    WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := C(X, Z))
      (WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K)
        (Y := C(Y, WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) C(X, Z))) g (snd X Y p))
      (fst X Y p) := by
  conv_rhs => rw [← (compactOpenTensorHomeomorph X Y Z).apply_symm_apply g]
  rw [equiv_equiv_compactOpenTensorHomeomorph_apply, tensorEquiv_symm_fst_snd]

end CompactlyGenerated
