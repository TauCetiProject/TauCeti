/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Flat base change for sections of the structure sheaf

Let `X` be a scheme over a commutative ring `R`, let `R → R'` be a ring map, and let
`Y = X ×_R R'` be the base change, given as a pullback square `H` over `Spec R' ⟶ Spec R`, with
projection `g : Y ⟶ X`. The sections of the structure sheaf over opens are algebras over the base
ring through `Scheme.baseRingToStructurePresheaf`. This file records that pulling back sections
along `g` is compatible with these base-ring maps, and packages it as an `R`-linear map
`Γ(X, W) → Γ(Y, W')`, where `R` acts on `Γ(Y, W')` through `R → R'`.

When `R → R'` is flat and `W` is quasi-compact and quasi-separated, Mathlib's
`AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` says that
`Γ(Y, g⁻¹ W) = R' ⊗_R Γ(X, W)`. This file restates it in terms of the base-ring maps, as a pushout
square of commutative rings and as `IsBaseChange` for the linear map above.

## Main definitions and results

* `TauCeti.AlgebraicGeometry.baseRingToStructurePresheaf_app_comp_appLE_of_isPullback`: pulling
  back sections along `g` commutes with the base-ring maps.
* `TauCeti.AlgebraicGeometry.isPushout_baseRingToStructurePresheaf_app_of_flat`: flat base change
  for sections of the structure sheaf, as a pushout square of commutative rings.
* `TauCeti.AlgebraicGeometry.sectionsBaseChange`: pulling back sections along `g`, as an `R`-linear
  map.
* `TauCeti.AlgebraicGeometry.isBaseChange_sectionsBaseChange`: flat base change for sections of
  the structure sheaf, as `IsBaseChange`.

## References

* [The Stacks Project, Lemma 30.5.2](https://stacks.math.columbia.edu/tag/02KH), flat base change.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

namespace TauCeti.AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]
  {R' : Type u} [CommRing R'] [Algebra R R']
  {Y : Scheme.{u}} [Y.Over (Spec (.of R'))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (.of R')) (X ↘ Spec (.of R))
    (Spec.map (CommRingCat.ofHom (algebraMap R R'))))

include H in
/-- Pulling back sections along the base change `g` is compatible with the base-ring maps on both
sides. -/
lemma baseRingToStructurePresheaf_app_comp_appLE_of_isPullback {W : X.Opens} {W' : Y.Opens}
    (hW : W' ≤ g ⁻¹ᵁ W) :
    (X.baseRingToStructurePresheaf R).app (op W) ≫ g.appLE W W' hW =
      CommRingCat.ofHom (algebraMap R R') ≫ (Y.baseRingToStructurePresheaf R').app (op W') := by
  rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE R X,
    Scheme.baseRingToStructurePresheaf_app_eq_appLE R' Y, Category.assoc]
  -- The map `appLE` on sections depends only on the morphism, whatever the inclusion proofs.
  have hw : ∀ e₁ e₂, (g ≫ X ↘ Spec (.of R)).appLE ⊤ W' e₁ =
      (Y ↘ Spec (.of R') ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))).appLE ⊤ W' e₂ := by
    rw [H.w]
    exact fun _ _ ↦ rfl
  refine (congrArg _ ((Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ((hw _
    (le_top.trans_eq (Scheme.Hom.preimage_top _).symm)).trans
    (Scheme.Hom.comp_appLE _ _ _ _ (le_top.trans_eq (Scheme.Hom.preimage_top _).symm))))).trans ?_
  -- The open `Spec.map φ ⁻¹ᵁ ⊤` is `⊤` only up to definitional unfolding.
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R R'))).symm).trans
      (Category.assoc _ _ _))

include H in
/-- **Flat base change for sections of the structure sheaf**, as a pushout square of commutative
rings: for a flat ring map `R → R'` and a quasi-compact quasi-separated open `W` of `X`,
`Γ(Y, g⁻¹ W) = R' ⊗_R Γ(X, W)`. -/
lemma isPushout_baseRingToStructurePresheaf_app_of_flat [Module.Flat R R'] {W : X.Opens}
    (hW : IsCompact (W : Set X)) (hW' : IsQuasiSeparated (W : Set X)) {W' : Y.Opens}
    (hW'eq : W' = g ⁻¹ᵁ W) :
    IsPushout ((X.baseRingToStructurePresheaf R).app (op W)) (CommRingCat.ofHom (algebraMap R R'))
      (g.appLE W W' hW'eq.le) ((Y.baseRingToStructurePresheaf R').app (op W')) := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have h := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H (US := ⊤) (UT := ⊤)
    (UX := W) (le_top.trans_eq (Scheme.Hom.preimage_top _).symm)
    (le_top.trans_eq (Scheme.Hom.preimage_top _).symm) (UY := W') (by simp [hW'eq])
    (isAffineOpen_top _) (isAffineOpen_top _) hW hW'
  refine ((isIso_pushoutSection_iff ..).mp h).of_iso (Scheme.ΓSpecIso _) (Iso.refl _)
    (Scheme.ΓSpecIso _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Scheme.baseRingToStructurePresheaf_app_eq_appLE, Iso.hom_inv_id_assoc,
      Iso.refl_hom, Category.comp_id]
  · exact Category.comp_id _ |>.trans (Scheme.ΓSpecIso_naturality _)
  · simp
  · simp only [Scheme.baseRingToStructurePresheaf_app_eq_appLE, Iso.hom_inv_id_assoc,
      Iso.refl_hom, Category.comp_id]

/-- Pulling back sections of the structure sheaf along the base change `g`, as an `R`-linear map.
Here `R` and `R'` act on sections through `Scheme.baseRingToStructurePresheaf`, and `R` acts on
the sections of `Y` through `R → R'`. -/
def sectionsBaseChange {W : X.Opens} {W' : Y.Opens} (hW : W' ≤ g ⁻¹ᵁ W) :
    letI : Algebra R Γ(X, W) := ((X.baseRingToStructurePresheaf R).app (op W)).hom.toAlgebra
    letI : Algebra R' Γ(Y, W') := ((Y.baseRingToStructurePresheaf R').app (op W')).hom.toAlgebra
    letI : Module R Γ(Y, W') := Module.compHom _ (algebraMap R R')
    Γ(X, W) →ₗ[R] Γ(Y, W') :=
  letI : Algebra R Γ(X, W) := ((X.baseRingToStructurePresheaf R).app (op W)).hom.toAlgebra
  letI : Algebra R' Γ(Y, W') := ((Y.baseRingToStructurePresheaf R').app (op W')).hom.toAlgebra
  letI : Module R Γ(Y, W') := Module.compHom _ (algebraMap R R')
  { toFun := g.appLE W W' hW
    map_add' := map_add _
    map_smul' r s := by
      rw [Algebra.smul_def, map_mul, RingHom.id_apply]
      exact congrArg (· * _)
        congr($(baseRingToStructurePresheaf_app_comp_appLE_of_isPullback H hW) r) }

/-- `sectionsBaseChange` pulls back sections along `g`. -/
@[simp]
lemma sectionsBaseChange_apply {W : X.Opens} {W' : Y.Opens} (hW : W' ≤ g ⁻¹ᵁ W) :
    letI : Algebra R Γ(X, W) := ((X.baseRingToStructurePresheaf R).app (op W)).hom.toAlgebra
    letI : Algebra R' Γ(Y, W') := ((Y.baseRingToStructurePresheaf R').app (op W')).hom.toAlgebra
    letI : Module R Γ(Y, W') := Module.compHom _ (algebraMap R R')
    ∀ s : Γ(X, W), sectionsBaseChange H hW s = g.appLE W W' hW s := by
  intro s
  rfl

include H in
/-- **Flat base change for sections of the structure sheaf**: for a flat ring map `R → R'` and a
quasi-compact quasi-separated open `W` of `X`, pulling back sections exhibits `Γ(Y, g⁻¹ W)` as
the base change `R' ⊗_R Γ(X, W)`. -/
theorem isBaseChange_sectionsBaseChange [Module.Flat R R'] {W : X.Opens}
    (hW : IsCompact (W : Set X)) (hW' : IsQuasiSeparated (W : Set X)) {W' : Y.Opens}
    (hW'eq : W' = g ⁻¹ᵁ W) :
    letI : Algebra R Γ(X, W) := ((X.baseRingToStructurePresheaf R).app (op W)).hom.toAlgebra
    letI : Algebra R' Γ(Y, W') := ((Y.baseRingToStructurePresheaf R').app (op W')).hom.toAlgebra
    letI : Module R Γ(Y, W') := Module.compHom _ (algebraMap R R')
    haveI : IsScalarTower R R' Γ(Y, W') := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    IsBaseChange R' (sectionsBaseChange H hW'eq.le) := by
  let : Algebra R Γ(X, W) := ((X.baseRingToStructurePresheaf R).app (op W)).hom.toAlgebra
  let : Algebra R' Γ(Y, W') := ((Y.baseRingToStructurePresheaf R').app (op W')).hom.toAlgebra
  let : Algebra Γ(X, W) Γ(Y, W') := (g.appLE W W' hW'eq.le).hom.toAlgebra
  let : Algebra R Γ(Y, W') := ((algebraMap R' Γ(Y, W')).comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' Γ(Y, W') := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R Γ(X, W) Γ(Y, W') := IsScalarTower.of_algebraMap_eq fun r ↦
    congr($(baseRingToStructurePresheaf_app_comp_appLE_of_isPullback H hW'eq.le) r).symm
  have := (CommRingCat.isPushout_iff_isPushout (R := R) (R' := Γ(X, W)) (S := R')
    (S' := Γ(Y, W'))).mp (isPushout_baseRingToStructurePresheaf_app_of_flat H hW hW' hW'eq)
  -- The `R`-module structure of the algebra `Γ(Y, W')` is the one restricted along `R → R'`.
  exact this.symm.out

end TauCeti.AlgebraicGeometry
