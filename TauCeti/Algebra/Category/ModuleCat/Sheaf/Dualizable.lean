/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.LocalDuality
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.LocalIsomorphism
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.FinitePresentationDescent
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.FiniteLocallyFree
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Closed
public import TauCeti.CategoryTheory.Monoidal.Rigid.Functor

/-!
# Finite locally free sheaves of modules are dualizable

Let `M` be a locally free sheaf of modules of finite type. Its dual-tensor comparison
`𝓗om(M, 𝒪) ⊗ N ⟶ 𝓗om(M, N)` is an isomorphism for every `N`
(`SheafOfModules.isIso_dualTensorIhom_of_isLocallyFree`). By the dual-basis criterion
`TauCeti.exactPairingOfIsIsoDualTensorIhom`, `𝓗om(M, 𝒪)` is therefore a left dual of `M`, with
evaluation the evaluation of the internal Hom.

Whether a morphism of sheaves is invertible can be checked on a cover
(`SheafOfModules.isIso_of_coversTop`). Take a cover by charts on which `M` is finite free; there
the dual-tensor comparison is invertible
(`SheafOfModules.IsLocallyFree.exists_isLocallyFreeData_isFiniteType_isIso_dualTensorIhom`).
Restriction to a chart is strong monoidal and commutes with internal Hom
(`SheafOfModules.isIso_overIhomComparison`), so it carries the global comparison to the local one
(`CategoryTheory.Functor.isIso_map_dualTensorIhom_app`).

The same charts show that the dual `𝓗om(M, 𝒪)` is again finite locally free
(`SheafOfModules.isFiniteLocallyFree_ihom_unit`), and hence so is `𝓗om(M, N) ≅ 𝓗om(M, 𝒪) ⊗ N`
for finite locally free `M` and `N` (`SheafOfModules.isFiniteLocallyFree_ihom`).
-/

public section

open CategoryTheory Limits MonoidalCategory MonoidalClosed

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

variable {C : Type u} [SmallCategory C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, (J.over X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasPullbacks C]
  {R : Sheaf J CommRingCat.{u}}
  (M : _root_.SheafOfModules.{u} (ringCatSheaf R))

/-- The monoidal structure on sheaves of modules over the restriction of `R` to `X`. -/
local instance (X : C) : MonoidalCategory
    (_root_.SheafOfModules.{u} ((ringCatSheaf R).over X)) :=
  monoidalCategory (R.over X)

/-- The closed monoidal structure on sheaves of modules over the restriction of `R` to `X`. -/
local instance (X : C) : MonoidalClosed
    (_root_.SheafOfModules.{u} ((ringCatSheaf R).over X)) :=
  monoidalClosed (R.over X)

/-- The dual-tensor comparison `𝓗om(M, 𝒪) ⊗ N ⟶ 𝓗om(M, N)` of a locally free sheaf of modules of
finite type is an isomorphism. By `TauCeti.exactPairingOfIsIsoDualTensorIhom`, `𝓗om(M, 𝒪)` is
then a left dual of `M`. -/
instance _root_.SheafOfModules.isIso_dualTensorIhom_of_isLocallyFree
    [M.IsLocallyFree] [M.IsFiniteType] : IsIso (dualTensorIhom M) := by
  obtain ⟨q, -, -, hq⟩ :=
    IsLocallyFree.exists_isLocallyFreeData_isFiniteType_isIso_dualTensorIhom (M := M)
  rw [NatTrans.isIso_iff_isIso_app]
  intro Z
  -- Check invertibility on the finite free charts, where restriction carries the comparison to
  -- the local one through its invertible internal Hom comparison.
  refine isIso_of_coversTop q.coversTop _ fun i ↦ ?_
  have : IsIso ((overFunctor (ringCatSheaf R) (q.X i)).ihomComparison M).natTrans := by
    rw [← overIhomComparison_def]
    infer_instance
  have := hq i
  exact Functor.isIso_map_dualTensorIhom_app (overFunctor (ringCatSheaf R) (q.X i)) M Z

variable [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The dual `𝓗om(M, 𝒪)` of a locally free sheaf of modules of finite type is finite locally
free. -/
theorem _root_.SheafOfModules.isFiniteLocallyFree_ihom_unit [M.IsLocallyFree] [M.IsFiniteType] :
    isFiniteLocallyFree (ringCatSheaf R) ((ihom M).obj (𝟙_ _)) := by
  obtain ⟨q, hq, hq'⟩ := IsLocallyFree.exists_isLocallyFreeData_isFiniteType M
  -- On each finite free chart, the dual restricts to the internal Hom from a finite free sheaf.
  have h (i : q.I) : isFiniteLocallyFree ((ringCatSheaf R).over (q.X i))
      (((ihom M).obj (𝟙_ _)).over (q.X i)) := by
    have := hq.isIso i
    have := hq'.isFiniteType i
    have : HasBinaryProducts (Over (q.X i)) :=
      Over.ConstructProducts.over_binaryProduct_of_pullback
    exact (isFiniteLocallyFree _).prop_of_iso (M.overDualIso R (q.X i)).symm
      (isFiniteLocallyFree_ihom_chart i _
        (isFiniteLocallyFree (ringCatSheaf (R.over (q.X i)))).prop_unit)
  have (i : q.I) := (h i).1
  have (i : q.I) := (h i).2
  exact ⟨IsLocallyFree.of_coversTop q.X q.coversTop,
    IsFinitePresentation.of_coversTop _ q.X q.coversTop⟩

/-- The internal Hom between finite locally free sheaves of modules is finite locally free. -/
theorem _root_.SheafOfModules.isFiniteLocallyFree_ihom [HasBinaryProducts C]
    {N : _root_.SheafOfModules.{u} (ringCatSheaf R)}
    (hM : isFiniteLocallyFree (ringCatSheaf R) M) (hN : isFiniteLocallyFree (ringCatSheaf R) N) :
    isFiniteLocallyFree (ringCatSheaf R) ((ihom M).obj N) := by
  have := hM.1
  have := hM.2
  exact (isFiniteLocallyFree _).prop_of_iso (asIso ((dualTensorIhom M).app N))
    ((isFiniteLocallyFree _).prop_tensor (isFiniteLocallyFree_ihom_unit M) hN)

end SheafOfModules

end

end TauCeti
