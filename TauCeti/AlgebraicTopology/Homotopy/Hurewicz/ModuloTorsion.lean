/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute
public import TauCeti.AlgebraicTopology.Singular.Coefficients.FlatBaseChange
import TauCeti.Algebra.Module.LocalizedModule.BaseChange
import TauCeti.Algebra.Module.Torsion.Int
import TauCeti.AlgebraicTopology.EilenbergMacLane.Torsion
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.SerreClass
import TauCeti.LinearAlgebra.TensorProduct.ScalarExtension

/-!
# The Hurewicz theorem modulo localization torsion

Let `S : Submonoid ℤ` be a multiplicative submonoid of `ℤ` and `A` a localization of `ℤ` at `S`
(e.g. `S = nonZeroDivisors ℤ`, `A = ℚ` for torsion, or `S = Submonoid.powers d` for `d`-power
torsion). This file proves **Serre's Hurewicz theorem modulo `S`-torsion** (Serre 1953, Theorem 1)
for every simply connected topological space `Y`, together with its rational specialization.

## Proof outline

The `S`-torsion abelian groups form a Serre class `AddCommGrpCat.isSubmonoidTorsion S` satisfying
Serre's axiom on Eilenberg--Mac Lane spaces (`satisfiesEilenbergMacLaneAxiom_isSubmonoidTorsion`),
so the general Serre-class Hurewicz theorems
(`TauCeti.isoModSerre_hurewiczModuleCatHom_of_prop_homotopyGroup` and
`TauCeti.prop_singularHomology_of_prop_homotopyGroup`) apply without CW or Hausdorff hypotheses
on `Y`:
* `HomotopyGroup.hurewiczModuleCatHom` is an isomorphism modulo `S`-torsion, giving `S`-torsion
  kernel and cokernel via `ModuleCat.kernelIsoKer` and `ModuleCat.cokernelIsoRangeQuotient`.
* Base change to any localization `A` of `ℤ` at `S` preserves injectivity and surjectivity
  exactly when kernel and cokernel are `S`-torsion
  (`LinearMap.baseChange_injective_iff_isTorsion'_ker`,
  `LinearMap.baseChange_surjective_iff_isTorsion'_quotient_range`), yielding the localized Hurewicz
  isomorphism in degree `n + 2`, and strong induction gives the reverse direction of the
  connectivity equivalence.

## Main results

* `HomotopyGroup.bijective_hurewiczModuleCatHom_baseChange`,
  `HomotopyGroup.hurewiczLocalizationLinearEquiv`: the Hurewicz isomorphism after localization at
  `S`, natural in based maps (`HomotopyGroup.singularHomologyMap_hurewiczLocalizationLinearEquiv`).
* `HomotopyGroup.isTorsion'_ker_hurewiczModuleCatHom`,
  `HomotopyGroup.isTorsion'_quotient_range_hurewiczModuleCatHom`: kernel and cokernel of the
  integral Hurewicz map are `S`-torsion.
* `TauCeti.forall_isTorsion'_homotopyGroup_iff_singularHomology`,
  `TauCeti.forall_isTorsion'_homotopyGroup_iff_subsingleton_singularHomology`: Serre's
  connectivity equivalence modulo `S`-torsion.
* `HomotopyGroup.hurewiczRatLinearEquiv`,
  `HomotopyGroup.isAddTorsion_ker_hurewiczModuleCatHom`,
  `HomotopyGroup.isAddTorsion_quotient_range_hurewiczModuleCatHom`,
  `TauCeti.forall_isAddTorsion_homotopyGroup_iff_singularHomology`,
  `TauCeti.forall_isAddTorsion_homotopyGroup_iff_subsingleton_rat`: the rational Hurewicz theorem.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  Chapter III, Theorem 1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.3, Whitehead towers.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Theorem 5.12.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory TensorProduct
open scoped Topology Topology.Homotopy

/-! ### Serre's Hurewicz isomorphism modulo `S`-torsion -/

namespace HomotopyGroup

open TauCeti

section Localization

variable {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y] {y : Y} [Subsingleton (π_ 1 Y y)]
  {S : Submonoid ℤ} {n : ℕ}

/-- The integral Hurewicz homomorphism is an isomorphism modulo `S`-torsion when `π_{m + 2}(Y, y)`
is `S`-torsion for all `m < n`. -/
private lemma isoModSerre_hurewiczModuleCatHom
    (hπ : ∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S) :
    ((AddCommGrpCat.isSubmonoidTorsion S).inverseImage
      (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat)).isoModSerre
        (hurewiczModuleCatHom Y y n) := by
  have : Subsingleton (FundamentalGroup Y y) :=
    pi1MulEquivFundamentalGroup.symm.toEquiv.subsingleton
  have : SimplyConnectedSpace Y := simplyConnectedSpace_of_subsingleton_fundamentalGroup y
  exact isoModSerre_hurewiczModuleCatHom_of_prop_homotopyGroup _ n
    (satisfiesEilenbergMacLaneAxiom_isSubmonoidTorsion S (n + 2)) y
    fun i hi ↦ (AddCommGrpCat.prop_inverseImage_isSubmonoidTorsion_iff S _).2 (hπ i hi)

/-- **The kernel of the integral Hurewicz homomorphism is `S`-torsion** when `Y` is simply connected
and `π_{m + 2}(Y, y)` is `S`-torsion for all `m < n`. -/
theorem isTorsion'_ker_hurewiczModuleCatHom
    (hπ : ∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S) :
    Module.IsTorsion' (LinearMap.ker (hurewiczModuleCatHom Y y n).hom) S :=
  (AddCommGrpCat.prop_inverseImage_isSubmonoidTorsion_iff S _).1 <|
    (((AddCommGrpCat.isSubmonoidTorsion S).inverseImage
      (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat)).prop_iff_of_iso
        (ModuleCat.kernelIsoKer (hurewiczModuleCatHom Y y n))).1
      ((ObjectProperty.monoModSerre_iff _ _).1 (isoModSerre_hurewiczModuleCatHom hπ).1)

/-- **The cokernel of the integral Hurewicz homomorphism is `S`-torsion** when `Y` is simply
connected and `π_{m + 2}(Y, y)` is `S`-torsion for all `m < n`. -/
theorem isTorsion'_quotient_range_hurewiczModuleCatHom
    (hπ : ∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S) :
    Module.IsTorsion'
      ((((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj (ModuleCat.of ℤ ℤ)).obj
          (TopCat.of Y)) ⧸
        LinearMap.range (hurewiczModuleCatHom Y y n).hom) S :=
  (AddCommGrpCat.prop_inverseImage_isSubmonoidTorsion_iff S _).1 <|
    (((AddCommGrpCat.isSubmonoidTorsion S).inverseImage
      (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat)).prop_iff_of_iso
        (ModuleCat.cokernelIsoRangeQuotient (hurewiczModuleCatHom Y y n))).1
      ((ObjectProperty.epiModSerre_iff _ _).1 (isoModSerre_hurewiczModuleCatHom hπ).2)

/-- **Hurewicz isomorphism modulo `S`-torsion (bijectivity of base change).** Let `Y` be a simply
connected space whose homotopy groups `π_{m + 2}(Y, y)` are `S`-torsion for all `m < n`, and let
`A` be a localization of `ℤ` at `S`. Then the base-changed Hurewicz homomorphism
`A ⊗[ℤ] Additive (π_{n + 2}(Y, y)) → A ⊗[ℤ] H_{n + 2}(Y; ℤ)` is bijective. -/
theorem bijective_hurewiczModuleCatHom_baseChange
    (hπ : ∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S)
    (A : Type) [CommRing A] [Algebra ℤ A] [IsLocalization S A] :
    Function.Bijective ((hurewiczModuleCatHom Y y n).hom.baseChange A) :=
  ⟨((hurewiczModuleCatHom Y y n).hom.baseChange_injective_iff_isTorsion'_ker S A).2
      (isTorsion'_ker_hurewiczModuleCatHom hπ),
    ((hurewiczModuleCatHom Y y n).hom.baseChange_surjective_iff_isTorsion'_quotient_range S A).2
      -- `isTorsion'_quotient_range_hurewiczModuleCatHom` uses `AddCommGroup.toIntModule`,
      -- whereas `baseChange_surjective_iff_isTorsion'_quotient_range` uses
      -- `Submodule.Quotient.module`.
      (Module.isTorsion'_of_intModule (AddCommGroup.toIntModule _) (Submodule.Quotient.module _)
        (isTorsion'_quotient_range_hurewiczModuleCatHom hπ))⟩

/-- Localized Hurewicz equivalence using the `Algebra.toModule` `ℤ`-module structure on `A`. -/
private def hurewiczLocalizationLinearEquivAux
    (hπ : ∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S)
    (A : Type) [CommRing A] [Algebra ℤ A] [IsLocalization S A] :
    (@TensorProduct ℤ _ A (Additive (HomotopyGroup (Fin (n + 2)) Y y)) _ _ Algebra.toModule _)
        ≃ₗ[A]
      ((singularChains A).obj (TopCat.of Y)).homology (n + 2) :=
  have := IsLocalization.flat A S
  (LinearEquiv.ofBijective ((hurewiczModuleCatHom Y y n).hom.baseChange A)
      (bijective_hurewiczModuleCatHom_baseChange hπ A)).trans
    (singularHomologyTensorIso ℤ A (TopCat.of Y) (n + 2)).toLinearEquiv

/-- Action of `hurewiczLocalizationLinearEquivAux` on a pure tensor. -/
private lemma hurewiczLocalizationLinearEquivAux_tmul
    (hπ : ∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S)
    (A : Type) [CommRing A] [Algebra ℤ A] [IsLocalization S A]
    (a : A) (x : Additive (HomotopyGroup (Fin (n + 2)) Y y)) :
    hurewiczLocalizationLinearEquivAux hπ A
      (@TensorProduct.tmul ℤ _ A _ _ _ Algebra.toModule _ a x) =
      (@singularHomologyTensorIso ℤ A _ _ _ (IsLocalization.flat A S)
          (TopCat.of Y) (n + 2)).hom.hom
        (@TensorProduct.tmul ℤ _ A _ _ _ Algebra.toModule _ a
          ((hurewiczModuleCatHom Y y n).hom x)) :=
  rfl

/-- **Hurewicz isomorphism modulo `S`-torsion.** Under the hypotheses of
`HomotopyGroup.bijective_hurewiczModuleCatHom_baseChange`, base change of the integral Hurewicz
homomorphism composed with `TauCeti.singularHomologyTensorIso` yields an `A`-linear isomorphism
`A ⊗[ℤ] Additive (π_{n + 2}(Y, y)) ≃ₗ[A] H_{n + 2}(Y; A)`. -/
def hurewiczLocalizationLinearEquiv
    (hπ : ∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S)
    (A : Type) [CommRing A] [Algebra ℤ A] [IsLocalization S A] :
    A ⊗[ℤ] Additive (HomotopyGroup (Fin (n + 2)) Y y) ≃ₗ[A]
      ((singularChains A).obj (TopCat.of Y)).homology (n + 2) :=
  (TensorProduct.congrIntModule A _ (AddCommGroup.toIntModule A) Algebra.toModule).trans
    (hurewiczLocalizationLinearEquivAux hπ A)

-- `S` is not an `outParam` of `IsLocalization`, so `IsLocalization.flat A S` cannot be a local
-- instance, and for abstract `A`, `Algebra.toModule` is not definitionally equal to
-- `AddCommGroup.toIntModule A`.

/-- Action of `HomotopyGroup.hurewiczLocalizationLinearEquiv` on a pure tensor `a ⊗ₜ[ℤ] x`. -/
@[simp]
theorem hurewiczLocalizationLinearEquiv_tmul
    (hπ : ∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S)
    (A : Type) [CommRing A] [Algebra ℤ A] [IsLocalization S A]
    (a : A) (x : Additive (HomotopyGroup (Fin (n + 2)) Y y)) :
    hurewiczLocalizationLinearEquiv hπ A (a ⊗ₜ[ℤ] x) =
      (@singularHomologyTensorIso ℤ A _ _ _ (IsLocalization.flat A S)
          (TopCat.of Y) (n + 2)).hom.hom
        (@TensorProduct.tmul ℤ _ A _ _ _ Algebra.toModule _ a
          ((hurewiczModuleCatHom Y y n).hom x)) := by
  rw [hurewiczLocalizationLinearEquiv, LinearEquiv.trans_apply, TensorProduct.congrIntModule_tmul,
    hurewiczLocalizationLinearEquivAux_tmul]

/-- **Naturality of the localized Hurewicz isomorphism** with respect to based continuous maps. -/
theorem singularHomologyMap_hurewiczLocalizationLinearEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace X]
    [PathConnectedSpace Y] {x : X} {y : Y} [Subsingleton (π_ 1 X x)] [Subsingleton (π_ 1 Y y)]
    {S : Submonoid ℤ} {n : ℕ}
    (hπX : ∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) X x)) S)
    (hπY : ∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S)
    (A : Type) [CommRing A] [Algebra ℤ A] [IsLocalization S A]
    (f : C(X, Y)) (hf : f x = y)
    (z : A ⊗[ℤ] Additive (HomotopyGroup (Fin (n + 2)) X x)) :
    (HomologicalComplex.homologyMap ((singularChains A).map (TopCat.ofHom f)) (n + 2)).hom
        (hurewiczLocalizationLinearEquiv hπX A z) =
      hurewiczLocalizationLinearEquiv hπY A
        ((HomotopyGroup.mapHom (N := Fin (n + 2)) f hf).toAdditive.toIntLinearMap.lTensor A z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a γ =>
    have := IsLocalization.flat A S
    rw [LinearMap.lTensor_tmul, hurewiczLocalizationLinearEquiv_tmul,
      hurewiczLocalizationLinearEquiv_tmul]
    have hnat := singularHomologyTensorIso_hom_naturality ℤ A (TopCat.ofHom f) (n + 2)
    have hnat_apply := congrArg (fun g ↦ g.hom
      (@TensorProduct.tmul ℤ _ A _ _ _ Algebra.toModule _ a
        ((hurewiczModuleCatHom X x n).hom γ))) hnat
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at hnat_apply
    rw [← hnat_apply]
    exact congrArg (fun w ↦ (singularHomologyTensorIso ℤ A (TopCat.of Y) (n + 2)).hom.hom
        (@TensorProduct.tmul ℤ _ A _ _ _ Algebra.toModule _ a w))
      (congrArg (fun g ↦ g γ) (singularHomologyMap_comp_hurewiczModuleCatHom f hf n))
  | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂]

end Localization

end HomotopyGroup

/-! ### Serre's connectivity equivalence modulo `S`-torsion -/

namespace TauCeti

section ConnectivityEquivalence

variable {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y] (y : Y) [Subsingleton (π_ 1 Y y)]

/-- If `Y` is simply connected and `π_{m + 2}(Y, y)` is `S`-torsion for all `m < n`, then
`H_{m + 2}(Y; A) = 0` for every localization `A` of `ℤ` at `S` and all `m < n`. -/
theorem subsingleton_singularHomology_of_forall_isTorsion'_homotopyGroup
    (S : Submonoid ℤ) (A : Type) [CommRing A] [Algebra ℤ A] [IsLocalization S A] {n : ℕ}
    (hπ : ∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S)
    {m : ℕ} (hm : m < n) :
    Subsingleton (((singularChains A).obj (TopCat.of Y)).homology (m + 2)) := by
  have : Subsingleton (FundamentalGroup Y y) :=
    HomotopyGroup.pi1MulEquivFundamentalGroup.symm.toEquiv.subsingleton
  have : SimplyConnectedSpace Y := simplyConnectedSpace_of_subsingleton_fundamentalGroup y
  refine (isTorsion'_singularChains_int_homology_iff S A (TopCat.of Y) (m + 2)).1 ?_
  rw [← singularHomologyFunctor_obj_obj]
  exact (AddCommGrpCat.prop_inverseImage_isSubmonoidTorsion_iff S _).1 <|
    prop_singularHomology_of_prop_homotopyGroup _ (n + 1)
      (satisfiesEilenbergMacLaneAxiom_isSubmonoidTorsion S (n + 1)) y
      (fun j hj ↦ (AddCommGrpCat.prop_inverseImage_isSubmonoidTorsion_iff S _).2
        (hπ j (by omega)))
      (Nat.succ_ne_zero _) (by omega)

/-- **Serre's connectivity equivalence modulo `S`-torsion (localized homology form).** For a
simply connected space `(Y, y)`, a submonoid `S : Submonoid ℤ`, a localization `A` of `ℤ` at `S`,
and any `n : ℕ`, the homotopy groups `π_{m + 2}(Y, y)` are `S`-torsion for all `m < n` if and
only if `H_{m + 2}(Y; A) = 0` for all `m < n`. -/
theorem forall_isTorsion'_homotopyGroup_iff_subsingleton_singularHomology
    (S : Submonoid ℤ) (A : Type) [CommRing A] [Algebra ℤ A] [IsLocalization S A] (n : ℕ) :
    (∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S) ↔
      ∀ m < n, Subsingleton (((singularChains A).obj (TopCat.of Y)).homology (m + 2)) := by
  refine ⟨fun hπ m hm ↦
    subsingleton_singularHomology_of_forall_isTorsion'_homotopyGroup y S A hπ hm, fun hH m hm ↦ ?_⟩
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    have : Subsingleton (((singularChains A).obj (TopCat.of Y)).homology (m + 2)) := hH m hm
    exact (S.isTorsion'_iff_subsingleton_tensorProduct A).2
      (HomotopyGroup.hurewiczLocalizationLinearEquivAux
        (fun j hj ↦ ih j hj (lt_trans hj hm)) A).toEquiv.subsingleton

/-- **Serre's connectivity equivalence modulo `S`-torsion (integral homology form, Serre 1953
Theorem 1).** For a simply connected space `(Y, y)`, a submonoid `S : Submonoid ℤ`, and any
`n : ℕ`, `π_{m + 2}(Y, y)` is `S`-torsion for all `m < n` if and only if `H_{m + 2}(Y; ℤ)` is
`S`-torsion for all `m < n`. -/
theorem forall_isTorsion'_homotopyGroup_iff_singularHomology (S : Submonoid ℤ) (n : ℕ) :
    (∀ m < n, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S) ↔
      ∀ m < n,
        Module.IsTorsion' (((singularChains ℤ).obj (TopCat.of Y)).homology (m + 2)) S := by
  have : IsLocalization S (Localization S) := Localization.isLocalization
  rw [forall_isTorsion'_homotopyGroup_iff_subsingleton_singularHomology y S (Localization S) n]
  exact forall_congr' fun m ↦ imp_congr_right fun _ ↦
    (isTorsion'_singularChains_int_homology_iff S (Localization S) (TopCat.of Y) (m + 2)).symm

/-- **All-degrees connectivity equivalence modulo `S`-torsion**: all higher homotopy groups
`π_{m + 2}(Y, y)` of a simply connected space `Y` are `S`-torsion if and only if all higher
integral homology groups `H_{m + 2}(Y; ℤ)` are `S`-torsion. -/
theorem forall_isTorsion'_homotopyGroup_iff_forall_singularHomology (S : Submonoid ℤ) :
    (∀ m : ℕ, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S) ↔
      ∀ m : ℕ, Module.IsTorsion' (((singularChains ℤ).obj (TopCat.of Y)).homology (m + 2)) S :=
  ⟨fun h m ↦ (forall_isTorsion'_homotopyGroup_iff_singularHomology y S (m + 1)).1
    (fun j _ ↦ h j) m (Nat.lt_succ_self m),
   fun h m ↦ (forall_isTorsion'_homotopyGroup_iff_singularHomology y S (m + 1)).2
    (fun j _ ↦ h j) m (Nat.lt_succ_self m)⟩

/-- **All-degrees connectivity equivalence modulo `S`-torsion (localized form)**: all higher
homotopy groups `π_{m + 2}(Y, y)` of a simply connected space `Y` are `S`-torsion if and only if
`H_{m + 2}(Y; A) = 0` for all `m : ℕ`. -/
theorem forall_isTorsion'_homotopyGroup_iff_forall_subsingleton_singularHomology
    (S : Submonoid ℤ) (A : Type) [CommRing A] [Algebra ℤ A] [IsLocalization S A] :
    (∀ m : ℕ, Module.IsTorsion' (Additive (π_ (m + 2) Y y)) S) ↔
      ∀ m : ℕ, Subsingleton (((singularChains A).obj (TopCat.of Y)).homology (m + 2)) :=
  ⟨fun h m ↦ (forall_isTorsion'_homotopyGroup_iff_subsingleton_singularHomology y S A (m + 1)).1
    (fun j _ ↦ h j) m (Nat.lt_succ_self m),
   fun h m ↦ (forall_isTorsion'_homotopyGroup_iff_subsingleton_singularHomology y S A (m + 1)).2
    (fun j _ ↦ h j) m (Nat.lt_succ_self m)⟩

end ConnectivityEquivalence

end TauCeti

/-! ### Rational Hurewicz theorem -/

namespace HomotopyGroup

open TauCeti

section Rational

local instance : @Module.Flat ℤ ℚ _ _ Algebra.toModule :=
  IsLocalization.flat ℚ (nonZeroDivisors ℤ)

variable {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y] {y : Y} [Subsingleton (π_ 1 Y y)]
  {n : ℕ}

/-- **The rational Hurewicz theorem** (homotopy-group hypothesis). If `Y` is simply connected and
`π_{m + 2}(Y, y)` is torsion for all `m < n`, then the rationalized Hurewicz map is a `ℚ`-linear
isomorphism `ℚ ⊗[ℤ] Additive (π_{n + 2}(Y, y)) ≃ₗ[ℚ] H_{n + 2}(Y; ℚ)`. -/
def hurewiczRatLinearEquiv
    (hπ : ∀ m < n, IsAddTorsion (Additive (HomotopyGroup (Fin (m + 2)) Y y))) :
    ℚ ⊗[ℤ] Additive (HomotopyGroup (Fin (n + 2)) Y y) ≃ₗ[ℚ]
      ((singularChains ℚ).obj (TopCat.of Y)).homology (n + 2) :=
  hurewiczLocalizationLinearEquiv (S := nonZeroDivisors ℤ)
    (fun m hm ↦ isAddTorsion_iff_isTorsion_int.1 (hπ m hm)) ℚ

/-- Action of `HomotopyGroup.hurewiczRatLinearEquiv` on a pure tensor `a ⊗ₜ[ℤ] x`. -/
@[simp]
theorem hurewiczRatLinearEquiv_tmul
    (hπ : ∀ m < n, IsAddTorsion (Additive (HomotopyGroup (Fin (m + 2)) Y y)))
    (a : ℚ) (x : Additive (HomotopyGroup (Fin (n + 2)) Y y)) :
    hurewiczRatLinearEquiv hπ (a ⊗ₜ[ℤ] x) =
      (singularHomologyTensorIso ℤ ℚ (TopCat.of Y) (n + 2)).hom.hom
        (a ⊗ₜ[ℤ] ((hurewiczModuleCatHom Y y n).hom x)) :=
  hurewiczLocalizationLinearEquiv_tmul _ ℚ a x

/-- **Naturality of `HomotopyGroup.hurewiczRatLinearEquiv`** with respect to based continuous
maps. -/
theorem singularHomologyMap_hurewiczRatLinearEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace X]
    [PathConnectedSpace Y] {x : X} {y : Y} [Subsingleton (π_ 1 X x)] [Subsingleton (π_ 1 Y y)]
    {n : ℕ}
    (hπX : ∀ m < n, IsAddTorsion (Additive (HomotopyGroup (Fin (m + 2)) X x)))
    (hπY : ∀ m < n, IsAddTorsion (Additive (HomotopyGroup (Fin (m + 2)) Y y)))
    (f : C(X, Y)) (hf : f x = y)
    (z : ℚ ⊗[ℤ] Additive (HomotopyGroup (Fin (n + 2)) X x)) :
    (HomologicalComplex.homologyMap ((singularChains ℚ).map (TopCat.ofHom f)) (n + 2)).hom
        (hurewiczRatLinearEquiv hπX z) =
      hurewiczRatLinearEquiv hπY
        ((HomotopyGroup.mapHom (N := Fin (n + 2)) f hf).toAdditive.toIntLinearMap.lTensor ℚ z) :=
  singularHomologyMap_hurewiczLocalizationLinearEquiv _ _ ℚ f hf z

/-- If `Y` is simply connected and `π_{m + 2}(Y, y)` is torsion for all `m < n`, then the kernel
of the integral Hurewicz map in degree `n + 2` is torsion. -/
theorem isAddTorsion_ker_hurewiczModuleCatHom
    (hπ : ∀ m < n, IsAddTorsion (Additive (HomotopyGroup (Fin (m + 2)) Y y))) :
    IsAddTorsion (LinearMap.ker (hurewiczModuleCatHom Y y n).hom) :=
  isAddTorsion_iff_isTorsion_int.2 <|
    isTorsion'_ker_hurewiczModuleCatHom (S := nonZeroDivisors ℤ)
      (fun m hm ↦ isAddTorsion_iff_isTorsion_int.1 (hπ m hm))

/-- If `Y` is simply connected and `π_{m + 2}(Y, y)` is torsion for all `m < n`, then the cokernel
of the integral Hurewicz map in degree `n + 2` is torsion. -/
theorem isAddTorsion_quotient_range_hurewiczModuleCatHom
    (hπ : ∀ m < n, IsAddTorsion (Additive (HomotopyGroup (Fin (m + 2)) Y y))) :
    IsAddTorsion
      ((((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj (ModuleCat.of ℤ ℤ)).obj
          (TopCat.of Y)) ⧸
        LinearMap.range (hurewiczModuleCatHom Y y n).hom) :=
  isAddTorsion_iff_isTorsion_int.2 <|
    isTorsion'_quotient_range_hurewiczModuleCatHom (S := nonZeroDivisors ℤ)
      (fun m hm ↦ isAddTorsion_iff_isTorsion_int.1 (hπ m hm))

end Rational

end HomotopyGroup

namespace TauCeti

section RationalConnectivity

variable {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y] (y : Y) [Subsingleton (π_ 1 Y y)]

/-- **Rational connectivity equivalence (rational homology form).** For a simply connected space
`(Y, y)`, `π_{m + 2}(Y, y)` is torsion for all `m < n` if and only if `H_{m + 2}(Y; ℚ) = 0` for
all `m < n`. -/
theorem forall_isAddTorsion_homotopyGroup_iff_subsingleton_rat (n : ℕ) :
    (∀ m < n, IsAddTorsion (Additive (π_ (m + 2) Y y))) ↔
      ∀ m < n, Subsingleton (((singularChains ℚ).obj (TopCat.of Y)).homology (m + 2)) := by
  simp only [isAddTorsion_iff_isTorsion_int]
  exact
    forall_isTorsion'_homotopyGroup_iff_subsingleton_singularHomology y (nonZeroDivisors ℤ) ℚ n

/-- **Rational connectivity equivalence (integral homology form).** For a simply connected space
`(Y, y)`, `π_{m + 2}(Y, y)` is torsion for all `m < n` if and only if `H_{m + 2}(Y; ℤ)` is
torsion for all `m < n`. -/
theorem forall_isAddTorsion_homotopyGroup_iff_singularHomology (n : ℕ) :
    (∀ m < n, IsAddTorsion (Additive (π_ (m + 2) Y y))) ↔
      ∀ m < n, IsAddTorsion (((singularChains ℤ).obj (TopCat.of Y)).homology (m + 2)) := by
  rw [forall_isAddTorsion_homotopyGroup_iff_subsingleton_rat y n]
  exact forall_congr' fun m ↦ imp_congr_right fun _ ↦
    (isAddTorsion_singularChains_homology_iff (TopCat.of Y) (m + 2)).symm

/-- A simply connected space `Y` has all higher homotopy groups torsion if and only if its
positive-degree rational homology vanishes. -/
theorem forall_isAddTorsion_homotopyGroup_iff_forall_subsingleton_rat :
    (∀ m : ℕ, IsAddTorsion (Additive (π_ (m + 2) Y y))) ↔
      ∀ m : ℕ, Subsingleton (((singularChains ℚ).obj (TopCat.of Y)).homology (m + 2)) := by
  simp only [isAddTorsion_iff_isTorsion_int]
  exact forall_isTorsion'_homotopyGroup_iff_forall_subsingleton_singularHomology y
    (nonZeroDivisors ℤ) ℚ

end RationalConnectivity

end TauCeti
