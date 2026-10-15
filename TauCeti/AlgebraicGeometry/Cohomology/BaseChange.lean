/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.SectionsQuotient.Linear
public import TauCeti.AlgebraicGeometry.Cohomology.Genus
public import TauCeti.AlgebraicGeometry.Cohomology.Trivial
public import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact

/-!
# Flat base change for the cohomology of the structure sheaf

Let `X` be a scheme over a commutative ring `R`, let `R → R'` be a flat ring map, and let
`Y = X ×_R R'` be the base change, given as a pullback square `H` over `Spec R' ⟶ Spec R`. This
file proves flat base change for the cohomology of the structure sheaf in degrees `0` and `1`:

* `H⁰(Y, 𝒪_Y) ≅ R' ⊗_R H⁰(X, 𝒪_X)` when `X` is quasi-compact and quasi-separated;
* `H¹(Y, 𝒪_Y) ≅ R' ⊗_R H¹(X, 𝒪_X)` when `X` and `Y` are locally Noetherian and `X` is covered
  by two affine opens.

Over a field `k` and a field extension `K / k`, these say that `dim_k H⁰(X, 𝒪_X)` and, for `X`
locally of finite type over `k` and covered by two affine opens, `dim_k H¹(X, 𝒪_X)` do not change
under base change to `K`; when moreover `H¹(X, 𝒪_X)` is finite-dimensional, so is `H¹` after base
change, and the genus does not change either. Smooth proper curves are covered by two affine
opens, so this applies to them (`TauCeti.AlgebraicGeometry.Curves.GenusBaseChange`).

The structure sheaf is written as the trivial line bundle `(InvertibleSheaf.trivial X).obj`, as for
the genus `Scheme.genus`. The isomorphisms are stated as `Nonempty` linear equivalences: in degree
one the construction depends on the chosen cover, and no naturality is claimed.

On sections, flat base change is
`AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`: for a quasi-compact
quasi-separated open `W ⊆ X`, `Γ(Y, g⁻¹ W) = R' ⊗_R Γ(X, W)`. For a cover `X = U ∪ V` whose
members have vanishing first cohomology, the Mayer–Vietoris sequence presents `H¹(X, 𝒪_X)` as
the cokernel of `Γ(U) × Γ(V) → Γ(U ∩ V)`
(`TauCeti.AlgebraicGeometry.ker_mayerVietorisBoundaryLinear`), and tensor products preserve
cokernels (`IsBaseChange.of_right_exact`). Affine opens with Noetherian rings of sections have
vanishing higher cohomology by Serre's vanishing theorem, before and after base change.

## Main results

* `TauCeti.AlgebraicGeometry.nonempty_linearEquiv_tensor_cohomology_zero_trivial`,
  `TauCeti.AlgebraicGeometry.nonempty_linearEquiv_tensor_cohomology_one_trivial`: flat base
  change for `H⁰` and `H¹` of the structure sheaf.
* `TauCeti.AlgebraicGeometry.finrank_cohomology_zero_trivial_eq_of_isPullback`,
  `TauCeti.AlgebraicGeometry.finrank_cohomology_one_trivial_eq_of_isPullback`,
  `TauCeti.AlgebraicGeometry.genus_eq_of_isPullback`: invariance of `h⁰(𝒪_X)`, `h¹(𝒪_X)` and of
  the genus under extension of the base field.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition III.9.3 (flat base change).
* [The Stacks Project, Lemma 30.5.2](https://stacks.math.columbia.edu/tag/02KH), flat base change.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry TensorProduct Module Opposite
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry

section FlatBaseChange

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

/-- The `R`-algebra structure on the sections of the structure sheaf over an open `W` of a scheme
over `R`, given by `Scheme.baseRingToStructurePresheaf`. -/
private abbrev sectionsAlgebra (W : X.Opens) : Algebra R Γ(X, W) :=
  ((X.baseRingToStructurePresheaf R).app (op W)).hom.toAlgebra

attribute [local instance] sectionsAlgebra

variable {R X}

variable {R' : Type u} [CommRing R'] [Algebra R R']
  {Y : Scheme.{u}} [Y.Over (Spec (.of R'))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (.of R')) (X ↘ Spec (.of R))
    (Spec.map (CommRingCat.ofHom (algebraMap R R'))))

include H in
/-- Pulling back sections along `g` is compatible with the base-ring structures on both sides. -/
private lemma comm_sections {W : X.Opens} {W' : Y.Opens} (hW : W' ≤ g ⁻¹ᵁ W) :
    CommRingCat.ofHom (algebraMap R Γ(X, W)) ≫ g.appLE W W' hW =
      CommRingCat.ofHom (algebraMap R R') ≫ CommRingCat.ofHom (algebraMap R' Γ(Y, W')) := by
  rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom,
    CommRingCat.ofHom_hom, Scheme.baseRingToStructurePresheaf_app_eq_appLE R X,
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
private lemma isPushout_sections [Module.Flat R R'] {W : X.Opens} (hW : IsCompact (W : Set X))
    (hW' : IsQuasiSeparated (W : Set X)) {W' : Y.Opens} (hW'eq : W' = g ⁻¹ᵁ W) :
    IsPushout (CommRingCat.ofHom (algebraMap R Γ(X, W))) (CommRingCat.ofHom (algebraMap R R'))
      (g.appLE W W' hW'eq.le) (CommRingCat.ofHom (algebraMap R' Γ(Y, W'))) := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have h := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H (US := ⊤) (UT := ⊤)
    (UX := W) (le_top.trans_eq (Scheme.Hom.preimage_top _).symm)
    (le_top.trans_eq (Scheme.Hom.preimage_top _).symm) (UY := W') (by simp [hW'eq])
    (isAffineOpen_top _) (isAffineOpen_top _) hW hW'
  refine ((isIso_pushoutSection_iff ..).mp h).of_iso (Scheme.ΓSpecIso _) (Iso.refl _)
    (Scheme.ΓSpecIso _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom,
      Scheme.baseRingToStructurePresheaf_app_eq_appLE, Iso.hom_inv_id_assoc, Iso.refl_hom,
      Category.comp_id]
  · exact Category.comp_id _ |>.trans (Scheme.ΓSpecIso_naturality _)
  · simp
  · simp only [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom,
      Scheme.baseRingToStructurePresheaf_app_eq_appLE, Iso.hom_inv_id_assoc, Iso.refl_hom,
      Category.comp_id]

/-- Pulling back sections of the structure sheaf along the base change `g`, as an `R`-linear map
to the sections of `Y`, which are an `R`-module through `R → R'`. -/
private def sectionsBaseChange {W : X.Opens} {W' : Y.Opens} (hW : W' ≤ g ⁻¹ᵁ W) :
    letI : Module R Γ(Y, W') := Module.compHom _ (algebraMap R R')
    Γ(X, W) →ₗ[R] Γ(Y, W') :=
  letI : Module R Γ(Y, W') := Module.compHom _ (algebraMap R R')
  { toFun := g.appLE W W' hW
    map_add' := map_add _
    map_smul' r s := by
      rw [Algebra.smul_def, map_mul, RingHom.id_apply]
      exact congrArg (· * _) (congr($(comm_sections H hW) r)) }

include H in
private lemma isBaseChange_sectionsBaseChange [Module.Flat R R'] {W : X.Opens}
    (hW : IsCompact (W : Set X)) (hW' : IsQuasiSeparated (W : Set X)) {W' : Y.Opens}
    (hW'eq : W' = g ⁻¹ᵁ W) :
    letI : Module R Γ(Y, W') := Module.compHom _ (algebraMap R R')
    haveI : IsScalarTower R R' Γ(Y, W') := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    IsBaseChange R' (sectionsBaseChange H hW'eq.le) := by
  let : Algebra Γ(X, W) Γ(Y, W') := (g.appLE W W' hW'eq.le).hom.toAlgebra
  let : Algebra R Γ(Y, W') := ((algebraMap R' Γ(Y, W')).comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' Γ(Y, W') := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R Γ(X, W) Γ(Y, W') :=
    IsScalarTower.of_algebraMap_eq fun r ↦ congr($(comm_sections H hW'eq.le) r).symm
  have := (CommRingCat.isPushout_iff_isPushout (R := R) (R' := Γ(X, W)) (S := R')
    (S' := Γ(Y, W'))).mp (isPushout_sections H hW hW' hW'eq)
  -- The `R`-module structure of the algebra `Γ(Y, W')` is the one restricted along `R → R'`.
  exact this.symm.out

/-- The structure sheaf of `Z` as a sheaf of modules over itself. The ascription to `Z.Modules`
lets instance search find the module structures on its cohomology. -/
private abbrev structureModule (Z : Scheme.{u}) : Z.Modules := SheafOfModules.unit Z.ringCatSheaf

section TwoOpens

section Instances

variable {S : Type u} [CommRing S] {Z : Scheme.{u}} [Z.Over (Spec (.of S))]

/-- The sections of the structure sheaf as a module over the base ring, through
`Scheme.baseRingToStructurePresheaf` as in `Scheme.Modules.isScalarTower_sections`, so that the
Mayer–Vietoris maps restrict to the base ring. -/
private abbrev structureModuleSectionsModule (W : Z.Opens) : Module S Γ(structureModule Z, W) :=
  Module.compHom _ ((Z.baseRingToStructurePresheaf S).app (op W)).hom

end Instances

attribute [local instance] structureModuleSectionsModule isScalarTower_sections
  isScalarTower_cohomology

section CohomologyOne

variable (U V : X.Opens) (hUV : U ⊔ V = ⊤)

include H hUV in
/-- The core comparison: under flat base change, the first cohomology of the structure sheaf of a
scheme covered by two quasi-compact opens with vanishing first cohomology, before and after base
change, is the base change of that of `X`. -/
private lemma nonempty_linearEquiv_tensor_cohomology_one_structureModule [Module.Flat R R']
    [QuasiSeparatedSpace X] (hUc : IsCompact (U : Set X)) (hVc : IsCompact (V : Set X))
    (hU : Subsingleton (cohomologyOn (structureModule X) 1 U))
    (hV : Subsingleton (cohomologyOn (structureModule X) 1 V))
    (hU' : Subsingleton (cohomologyOn (structureModule Y) 1 (g ⁻¹ᵁ U)))
    (hV' : Subsingleton (cohomologyOn (structureModule Y) 1 (g ⁻¹ᵁ V))) :
    Nonempty (R' ⊗[R] Cohomology (structureModule X) 1 ≃ₗ[R']
      Cohomology (structureModule Y) 1) := by
  let : ∀ W' : Y.Opens, Module R Γ(Y, W') := fun _ ↦ Module.compHom _ (algebraMap R R')
  have : ∀ W' : Y.Opens, IsScalarTower R R' Γ(Y, W') :=
    fun _ ↦ IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module R (Cohomology (structureModule Y) 1) := Module.compHom _ (algebraMap R R')
  have : IsScalarTower R R' (Cohomology (structureModule Y) 1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hUV' : g ⁻¹ᵁ U ⊔ g ⁻¹ᵁ V = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, hUV, Scheme.Hom.preimage_top]
  have hUVc : IsCompact ((U ⊓ V : X.Opens) : Set X) := hUc.inter_of_isOpen hVc U.2 V.2
  -- The exact rows `Γ(U) × Γ(V) → Γ(U ⊓ V) → H¹ → 0` on `X` and on `Y`: the Mayer–Vietoris maps
  -- of the structure sheaf, restricted to the base ring.
  let d : (Γ(X, U) × Γ(X, V)) →ₗ[R] Γ(X, U ⊓ V) :=
    (mayerVietorisSectionsDifferenceLinear (structureModule X) U V).restrictScalars R
  let d' : (Γ(Y, g ⁻¹ᵁ U) × Γ(Y, g ⁻¹ᵁ V)) →ₗ[R'] Γ(Y, g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V) :=
    (mayerVietorisSectionsDifferenceLinear (structureModule Y) _ _).restrictScalars R'
  let δ : Γ(X, U ⊓ V) →ₗ[R] Cohomology (structureModule X) 1 :=
    (mayerVietorisBoundaryLinear (structureModule X) U V hUV).restrictScalars R
  let δ' : Γ(Y, g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V) →ₗ[R'] Cohomology (structureModule Y) 1 :=
    (mayerVietorisBoundaryLinear (structureModule Y) _ _ hUV').restrictScalars R'
  have hδ : Function.Surjective δ := mayerVietorisBoundaryLinear_surjective _ U V hUV hU hV
  have hδ' : Function.Surjective δ' := mayerVietorisBoundaryLinear_surjective _ _ _ hUV' hU' hV'
  have hex : Function.Exact d δ :=
    (LinearMap.exact_iff (f := mayerVietorisSectionsDifferenceLinear (structureModule X) U V)
      (g := mayerVietorisBoundaryLinear _ U V hUV)).mpr (ker_mayerVietorisBoundaryLinear _ U V hUV)
  have hex' : Function.Exact d' δ' :=
    (LinearMap.exact_iff (f := mayerVietorisSectionsDifferenceLinear (structureModule Y) _ _)
      (g := mayerVietorisBoundaryLinear _ _ _ hUV')).mpr
        (ker_mayerVietorisBoundaryLinear _ _ _ hUV')
  -- The vertical maps pull back sections along `g`.
  let σU := sectionsBaseChange H (W := U) (W' := g ⁻¹ᵁ U) le_rfl
  let σV := sectionsBaseChange H (W := V) (W' := g ⁻¹ᵁ V) le_rfl
  let σUV := sectionsBaseChange H (W := U ⊓ V) (W' := g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)
    (Scheme.Hom.preimage_inf (f := g)).ge
  have comm₁ : σUV.comp d = (d'.restrictScalars R).comp (σU.prodMap σV) := by
    refine LinearMap.ext fun ⟨s, t⟩ ↦ ?_
    -- Both rows are differences of restrictions, which commute with pulling back along `g`.
    have hX := (mayerVietorisSectionsDifferenceLinear_apply (structureModule X) U V s t).trans
      (mayerVietorisSectionsDifference_apply (structureModule X) U V s t)
    have hY := (mayerVietorisSectionsDifferenceLinear_apply (structureModule Y) (g ⁻¹ᵁ U)
      (g ⁻¹ᵁ V) (σU s) (σV t)).trans (mayerVietorisSectionsDifference_apply _ _ _ _ _)
    have hres {W₁ W₂ : X.Opens} {W₂' : Y.Opens} (h₂ : W₂' ≤ g ⁻¹ᵁ W₂) (hW : W₂ ≤ W₁)
        (hW' : W₂' ≤ g ⁻¹ᵁ W₁) (s : Γ(X, W₁)) :
        g.appLE W₂ W₂' h₂ (X.presheaf.map (homOfLE hW).op s) =
          Y.presheaf.map (homOfLE hW').op (g.appLE W₁ (g ⁻¹ᵁ W₁) le_rfl s) := by
      simp only [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
    exact (congrArg σUV hX).trans (((map_sub _ _ _).trans (congrArg₂ (· - ·)
      (hres _ inf_le_left _ s) (hres _ inf_le_right _ t))).trans hY.symm)
  -- The induced map on first cohomology.
  have hker : LinearMap.ker δ ≤ LinearMap.ker ((δ'.restrictScalars R).comp σUV) := by
    intro x hx
    obtain ⟨y, rfl⟩ := (hex x).mp hx
    exact (congrArg δ' congr($comm₁ y)).trans (hex'.apply_apply_eq_zero _)
  let φ := δ.liftOfSurjective hδ ⟨(δ'.restrictScalars R).comp σUV, hker⟩
  have comm₂ : φ.comp δ = (δ'.restrictScalars R).comp σUV :=
    LinearMap.ext fun _ ↦ LinearMap.equivOfSurjective_apply hδ hker
  have hσU := isBaseChange_sectionsBaseChange H hUc (.of_quasiSeparatedSpace _) (W' := g ⁻¹ᵁ U) rfl
  have hσV := isBaseChange_sectionsBaseChange H hVc (.of_quasiSeparatedSpace _) (W' := g ⁻¹ᵁ V) rfl
  have hσUV := isBaseChange_sectionsBaseChange H hUVc (.of_quasiSeparatedSpace _)
    (W' := g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V) (Scheme.Hom.preimage_inf g).symm
  have hb₁ := IsBaseChange.prodMap (S := R') σU σV hσU hσV
  have key := IsBaseChange.of_right_exact R' _ _ φ comm₁ comm₂ hb₁ hσUV hex hδ hex' hδ'
  exact ⟨key.equiv⟩

include H in
/-- **Flat base change for `H¹(X, 𝒪_X)` on a two-affine cover.** Let `X` be a locally Noetherian
scheme over `R` covered by two affine opens, and let `Y = X ×_R R'` be its base change along a
flat ring map `R → R'`, also locally Noetherian. Then `H¹(Y, 𝒪_Y) ≅ R' ⊗_R H¹(X, 𝒪_X)` as
`R'`-modules. -/
theorem nonempty_linearEquiv_tensor_cohomology_one_trivial [Module.Flat R R']
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤) :
    Nonempty (R' ⊗[R] Cohomology (InvertibleSheaf.trivial X).obj 1 ≃ₗ[R']
      Cohomology (InvertibleSheaf.trivial Y).obj 1) := by
  -- `g` is affine, as a base change of `Spec R' ⟶ Spec R`.
  have : IsAffineHom g := MorphismProperty.of_isPullback H.flip inferInstance
  have hU' := hU.preimage g
  have hV' := hV.preimage g
  have := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have := IsLocallyNoetherian.component_noetherian ⟨g ⁻¹ᵁ U, hU'⟩
  have := IsLocallyNoetherian.component_noetherian ⟨g ⁻¹ᵁ V, hV'⟩
  obtain ⟨e⟩ := nonempty_linearEquiv_tensor_cohomology_one_structureModule H U V hUV
    hU.isCompact hV.isCompact
    (Scheme.Modules.subsingleton_cohomologyOn_succ_of_isAffineOpen _ hU 0)
    (Scheme.Modules.subsingleton_cohomologyOn_succ_of_isAffineOpen _ hV 0)
    (Scheme.Modules.subsingleton_cohomologyOn_succ_of_isAffineOpen _ hU' 0)
    (Scheme.Modules.subsingleton_cohomologyOn_succ_of_isAffineOpen _ hV' 0)
  let MX : X.Modules := structureModule X
  let MY : Y.Modules := structureModule Y
  let eX : Cohomology (InvertibleSheaf.trivial X).obj 1 ≃ₗ[R] Cohomology MX 1 :=
    trivialCohomologyBaseLinearEquiv R X 1
  let eY : Cohomology (InvertibleSheaf.trivial Y).obj 1 ≃ₗ[R'] Cohomology MY 1 :=
    trivialCohomologyBaseLinearEquiv R' Y 1
  exact ⟨(eX.baseChange R R' _ _).trans (e.trans eY.symm)⟩

end CohomologyOne

end TwoOpens

include H in
/-- **Flat base change for `H⁰(X, 𝒪_X)`.** For a quasi-compact quasi-separated scheme `X` over
`R` and its base change `Y = X ×_R R'` along a flat ring map `R → R'`,
`H⁰(Y, 𝒪_Y) ≅ R' ⊗_R H⁰(X, 𝒪_X)` as `R'`-modules. -/
theorem nonempty_linearEquiv_tensor_cohomology_zero_trivial [Module.Flat R R'] [CompactSpace X]
    [QuasiSeparatedSpace X] :
    Nonempty (R' ⊗[R] Cohomology (InvertibleSheaf.trivial X).obj 0 ≃ₗ[R']
      Cohomology (InvertibleSheaf.trivial Y).obj 0) := by
  let : Module R Γ(Y, ⊤) := Module.compHom _ (algebraMap R R')
  have : IsScalarTower R R' Γ(Y, ⊤) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have h := isBaseChange_sectionsBaseChange H (W := ⊤) isCompact_univ isQuasiSeparated_univ
    (W' := ⊤) (Scheme.Hom.preimage_top g).symm
  let eX := (trivialCohomologyBaseLinearEquiv R X 0).trans
    ((cohomologyZeroBaseLinearEquiv R X (structureModule X)).trans
      (structureSheafSectionsBaseLinearEquiv R X))
  let eY := (trivialCohomologyBaseLinearEquiv R' Y 0).trans
    ((cohomologyZeroBaseLinearEquiv R' Y (structureModule Y)).trans
      (structureSheafSectionsBaseLinearEquiv R' Y))
  exact ⟨(eX.baseChange R R' _ _).trans (h.equiv.trans eY.symm)⟩

end FlatBaseChange

section Field

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of K))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K))))

include H in
/-- Over a field, `H¹(X_K, 𝒪) ≅ K ⊗_k H¹(X, 𝒪)` for a scheme `X` locally of finite type over `k`
covered by two affine opens, and a field extension `K / k`. -/
private theorem nonempty_linearEquiv_tensor_cohomology_one_trivial_of_field
    [LocallyOfFiniteType (X ↘ Spec (.of k))] {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤) :
    Nonempty (K ⊗[k] Cohomology (InvertibleSheaf.trivial X).obj 1 ≃ₗ[K]
      Cohomology (InvertibleSheaf.trivial Y).obj 1) := by
  have : LocallyOfFiniteType (Y ↘ Spec (.of K)) := MorphismProperty.of_isPullback H inferInstance
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of K))
  exact nonempty_linearEquiv_tensor_cohomology_one_trivial H hU hV hUV

include H in
/-- The dimension of `H¹(X, 𝒪_X)` does not change under extension of the base field, for a scheme
locally of finite type over a field and covered by two affine opens. -/
theorem finrank_cohomology_one_trivial_eq_of_isPullback [LocallyOfFiniteType (X ↘ Spec (.of k))]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤) :
    finrank K (Cohomology (InvertibleSheaf.trivial Y).obj 1) =
      finrank k (Cohomology (InvertibleSheaf.trivial X).obj 1) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_tensor_cohomology_one_trivial_of_field H hU hV hUV
  rw [← e.finrank_eq, Module.finrank_baseChange]

include H in
/-- `H¹(X, 𝒪_X)` stays finite-dimensional under extension of the base field, for a scheme locally
of finite type over a field and covered by two affine opens. -/
theorem finiteDimensional_cohomology_one_trivial_of_isPullback
    [LocallyOfFiniteType (X ↘ Spec (.of k))] {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj 1)] :
    FiniteDimensional K (Cohomology (InvertibleSheaf.trivial Y).obj 1) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_tensor_cohomology_one_trivial_of_field H hU hV hUV
  exact Module.Finite.equiv e

include H in
/-- **The genus does not change under extension of the base field**, for a scheme locally of
finite type over a field, covered by two affine opens, and with finite-dimensional `H¹(X, 𝒪_X)`.
The finite-dimensionality of `H¹` after base change, needed to form the genus of `Y`, follows
from that before, by `finiteDimensional_cohomology_one_trivial_of_isPullback`. -/
theorem genus_eq_of_isPullback [LocallyOfFiniteType (X ↘ Spec (.of k))] {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj 1)] :
    haveI := finiteDimensional_cohomology_one_trivial_of_isPullback H hU hV hUV
    Y.genus K = X.genus k := by
  rw [Scheme.genus_def, Scheme.genus_def,
    finrank_cohomology_one_trivial_eq_of_isPullback H hU hV hUV]

include H in
/-- The dimension of `H⁰(X, 𝒪_X)` does not change under extension of the base field, for a
quasi-compact quasi-separated scheme over a field. -/
theorem finrank_cohomology_zero_trivial_eq_of_isPullback [CompactSpace X] [QuasiSeparatedSpace X] :
    finrank K (Cohomology (InvertibleSheaf.trivial Y).obj 0) =
      finrank k (Cohomology (InvertibleSheaf.trivial X).obj 0) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_tensor_cohomology_zero_trivial H
  rw [← e.finrank_eq, Module.finrank_baseChange]

end Field

end TauCeti.AlgebraicGeometry
