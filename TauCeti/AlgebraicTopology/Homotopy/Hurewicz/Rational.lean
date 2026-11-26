/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.SerreClass
public import TauCeti.AlgebraicTopology.Singular.Coefficients.FlatBaseChange
import TauCeti.Algebra.Module.Torsion.Localization

/-!
# The rational Hurewicz theorem

For a pointed space `(X, x)`, tensoring the integral Hurewicz morphism
`πₙ₊₂(X, x) → Hₙ₊₂(X; ℤ)` (`HomotopyGroup.hurewiczModuleCatHom`) with `ℚ` and following it by the
flat base change `ℚ ⊗ Hₙ₊₂(X; ℤ) ≅ Hₙ₊₂(X; ℚ)` (`TauCeti.singularHomologyTensorIso`) gives the
**rational Hurewicz map** `ℚ ⊗ πₙ₊₂(X, x) → Hₙ₊₂(X; ℚ)` (`HomotopyGroup.rationalHurewicz`). It is
natural in based maps (`HomotopyGroup.rationalHurewicz_naturality`).

**Theorem** (Serre). Let `Y` be a simply connected space.

* If the homotopy groups `πᵢ(Y)` are torsion groups for `2 ≤ i ≤ n + 1`, the rational Hurewicz map
  `ℚ ⊗ πₙ₊₂(Y) → Hₙ₊₂(Y; ℚ)` is bijective
  (`TauCeti.bijective_rationalHurewicz_of_isMulTorsion_homotopyGroup`).
* The homotopy groups `πᵢ(Y)` are torsion groups for `2 ≤ i ≤ k` exactly when the rational
  homology `Hᵢ(Y; ℚ)` vanishes for `1 ≤ i ≤ k`
  (`TauCeti.forall_isMulTorsion_homotopyGroup_iff_forall_subsingleton_singularHomology`).

So the first rational homotopy group `ℚ ⊗ πₙ(Y)` that does not vanish, `n ≥ 2`, and the first
positive-degree rational homology group that does not vanish sit in the same degree, and the
rational Hurewicz map identifies them.

The first statement is Serre's Hurewicz theorem modulo the class of torsion groups
(`TauCeti.isoModSerre_hurewiczModuleCatHom_of_isMulTorsion_homotopyGroup`): an isomorphism modulo
torsion is exactly a morphism that becomes bijective after tensoring with `ℚ`
(`AddCommGrpCat.isoModSerre_inverseImage_isTorsion_iff`). In the second, torsion homotopy groups
give torsion integral homology
(`TauCeti.isAddTorsion_singularHomology_of_isMulTorsion_homotopyGroup`), that is, vanishing
rational homology (`TauCeti.isAddTorsion_singularChains_homology_iff`). Conversely, if the rational
homology vanishes in degrees `1, …, k`, induction on the degree shows that the homotopy groups are
torsion: once they are torsion below degree `i ≤ k`, the rational Hurewicz map embeds `ℚ ⊗ πᵢ(Y)`
in `Hᵢ(Y; ℚ) = 0`, so `πᵢ(Y)` is torsion as well
(`TauCeti.isAddTorsion_iff_subsingleton_rat_tensorProduct`).

## Main definitions

* `HomotopyGroup.rationalHurewicz`: the rational Hurewicz map `ℚ ⊗ πₙ₊₂(X, x) → Hₙ₊₂(X; ℚ)`.

## Main results

* `HomotopyGroup.rationalHurewicz_naturality`: the rational Hurewicz map is natural in based maps.
* `TauCeti.bijective_rationalHurewicz_of_isMulTorsion_homotopyGroup`: the rational Hurewicz
  theorem.
* `TauCeti.forall_isMulTorsion_homotopyGroup_iff_forall_subsingleton_singularHomology`: a simply
  connected space has torsion homotopy groups through degree `k` exactly when its rational
  homology vanishes in the positive degrees through `k`.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294, Chapter III.
* A. Hatcher, *Spectral Sequences*, Chapter 1, Serre classes.
-/

public section

noncomputable section

open CategoryTheory TensorProduct

open scoped Topology Topology.Homotopy

namespace HomotopyGroup

open TauCeti

/-- **The rational Hurewicz map** `ℚ ⊗ πₙ₊₂(X, x) → Hₙ₊₂(X; ℚ)`: the integral Hurewicz morphism
`HomotopyGroup.hurewiczModuleCatHom` tensored with `ℚ`, followed by the flat base change
`ℚ ⊗ Hₙ₊₂(X; ℤ) ≅ Hₙ₊₂(X; ℚ)` (`TauCeti.singularHomologyTensorIso`). -/
def rationalHurewicz (X : Type) [TopologicalSpace X] (x : X) (n : ℕ) :
    ℚ ⊗[ℤ] Additive (π_ (n + 2) X x) →ₗ[ℚ]
      ((singularChains ℚ).obj (TopCat.of X)).homology (n + 2) :=
  (singularHomologyTensorIso ℤ ℚ (TopCat.of X) (n + 2)).hom.hom ∘ₗ
    (hurewiczModuleCatHom X x n).hom.baseChange ℚ

/-- The rational Hurewicz map sends `q ⊗ a` to the image of `q ⊗ h(a)` under the flat base change
`ℚ ⊗ Hₙ₊₂(X; ℤ) ≅ Hₙ₊₂(X; ℚ)`, where `h(a)` is the integral Hurewicz class of `a`. -/
@[simp]
theorem rationalHurewicz_tmul (X : Type) [TopologicalSpace X] (x : X) (n : ℕ) (q : ℚ)
    (a : Additive (π_ (n + 2) X x)) :
    rationalHurewicz X x n (q ⊗ₜ a) =
      (singularHomologyTensorIso ℤ ℚ (TopCat.of X) (n + 2)).hom.hom
        (q ⊗ₜ hurewiczIntHom X x (n + 1) a) := by
  -- The codomain of the Hurewicz morphism is `Hₙ₊₂(X; ℤ)` written through
  -- `singularHomologyFunctor`, the domain of the flat base change is the same module written as
  -- the homology of `singularChains ℤ` (`singularHomologyFunctor_obj_obj`), so the composite is
  -- evaluated through `congrArg` rather than by rewriting.
  have h : (hurewiczModuleCatHom X x n).hom.baseChange ℚ (q ⊗ₜ a) =
      q ⊗ₜ hurewiczIntHom X x (n + 1) a := by
    rw [LinearMap.baseChange_tmul, hurewiczModuleCatHom_apply]
  exact congrArg (singularHomologyTensorIso ℤ ℚ (TopCat.of X) (n + 2)).hom.hom h

/-- **Naturality of the rational Hurewicz map**: for a based map `f : (X, x) → (Y, y)`, the square
formed by `ℚ ⊗ f_* : ℚ ⊗ πₙ₊₂(X, x) → ℚ ⊗ πₙ₊₂(Y, y)`, `f_* : Hₙ₊₂(X; ℚ) → Hₙ₊₂(Y; ℚ)` and the two
rational Hurewicz maps commutes. -/
theorem rationalHurewicz_naturality {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (hf : f x = y) (n : ℕ) :
    rationalHurewicz Y y n ∘ₗ
        (mapHom (N := Fin (n + 2)) f hf).toAdditive.toIntLinearMap.baseChange ℚ =
      (HomologicalComplex.homologyMap ((singularChains ℚ).map (TopCat.ofHom f)) (n + 2)).hom ∘ₗ
        rationalHurewicz X x n := by
  refine TensorProduct.AlgebraTensorModule.ext fun q a ↦ ?_
  -- On `q ⊗ a`, this is the naturality of the integral Hurewicz class followed by that of the flat
  -- base change.
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (singularHomologyTensorIso_hom_naturality ℤ ℚ (TopCat.ofHom f) (n + 2)))
    (q ⊗ₜ hurewiczIntHom X x (n + 1) a)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply] at h
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, rationalHurewicz_tmul, ← h]
  -- `hurewiczIntHom_map` states the integral naturality through the map of
  -- `singularHomologyFunctor`, which is by definition the homology map of `singularChains ℤ`
  -- (`singularHomologyFunctor_obj_obj`); `e` restates it in the latter form.
  have e : hurewiczIntHom Y y (n + 1) (Additive.ofMul (map f hf a.toMul)) =
      (HomologicalComplex.homologyMap ((singularChains ℤ).map (TopCat.ofHom f)) (n + 2)).hom
        (hurewiczIntHom X x (n + 1) a) := by
    rw [hurewiczIntHom_map, ofMul_toMul]
    rfl
  rw [AddMonoidHom.coe_toIntLinearMap, MonoidHom.toAdditive_apply_apply, mapHom_apply, e]
  exact congrArg (singularHomologyTensorIso ℤ ℚ (TopCat.of Y) (n + 2)).hom.hom
    (LinearMap.baseChange_tmul _ _ _).symm

end HomotopyGroup

namespace TauCeti

/-- **The rational Hurewicz theorem** (Serre). Let `Y` be a simply connected space whose homotopy
groups `πᵢ(Y)` are torsion groups for `2 ≤ i ≤ n + 1`. Then the rational Hurewicz map
`ℚ ⊗ πₙ₊₂(Y) → Hₙ₊₂(Y; ℚ)` is bijective. -/
theorem bijective_rationalHurewicz_of_isMulTorsion_homotopyGroup {Y : Type} [TopologicalSpace Y]
    [SimplyConnectedSpace Y] (y : Y) (n : ℕ) (hY : ∀ i, i < n → IsMulTorsion (π_ (i + 2) Y y)) :
    Function.Bijective (HomotopyGroup.rationalHurewicz Y y n) :=
  (singularHomologyTensorIso ℤ ℚ (TopCat.of Y) (n + 2)).toLinearEquiv.bijective.comp
    ((AddCommGrpCat.isoModSerre_inverseImage_isTorsion_iff _).1
      (isoModSerre_hurewiczModuleCatHom_of_isMulTorsion_homotopyGroup y n hY))

/-- **Torsion homotopy groups are detected by rational homology** (Serre). A simply connected
space `Y` has torsion homotopy groups `πᵢ(Y)` for `2 ≤ i ≤ k` exactly when its rational homology
`Hᵢ(Y; ℚ)` vanishes for `1 ≤ i ≤ k`. -/
theorem forall_isMulTorsion_homotopyGroup_iff_forall_subsingleton_singularHomology {Y : Type}
    [TopologicalSpace Y] [SimplyConnectedSpace Y] (y : Y) (k : ℕ) :
    (∀ j, j + 2 ≤ k → IsMulTorsion (π_ (j + 2) Y y)) ↔
      ∀ i, i ≠ 0 → i ≤ k → Subsingleton (((singularChains ℚ).obj (TopCat.of Y)).homology i) := by
  refine ⟨fun h i hi0 hik ↦ (isAddTorsion_singularChains_homology_iff _ i).1
    (isAddTorsion_singularHomology_of_isMulTorsion_homotopyGroup y k h hi0 hik), fun h j hj ↦ ?_⟩
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    -- The homotopy groups below degree `j + 2` are torsion, so `ℚ ⊗ πⱼ₊₂(Y)` embeds in
    -- `Hⱼ₊₂(Y; ℚ)`, which vanishes.
    have := h (j + 2) (by omega) hj
    have hinj := (bijective_rationalHurewicz_of_isMulTorsion_homotopyGroup y j
      fun i hi ↦ ih i hi (by omega)).injective
    have ht := isAddTorsion_iff_subsingleton_rat_tensorProduct.2 hinj.subsingleton
    exact fun g ↦ isOfFinAddOrder_ofMul_iff.1 (ht (Additive.ofMul g))

end TauCeti
