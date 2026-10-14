/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.SectionsQuotient.Linear
public import TauCeti.AlgebraicGeometry.Cohomology.Genus
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion
public import TauCeti.AlgebraicGeometry.LineBundle.Basic
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
locally of finite type over `k` and covered by two affine opens, the genus `dim_k H¹(X, 𝒪_X)`
do not change under base change to `K`. Smooth proper curves are covered by two affine opens, so
this applies to them (`TauCeti.AlgebraicGeometry.Curves.GenusBaseChange`).

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

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry TensorProduct Module
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry

section FlatBaseChange

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

/-- The `R`-algebra structure on the sections of the structure sheaf over an open `W` of a scheme
over `R`: the base ring maps to global functions, which restrict to `W`. -/
private abbrev sectionsAlgebra (W : X.Opens) : Algebra R Γ(X, W) :=
  ((X.presheaf.map W.leTop.op).hom.comp (baseRingToGlobalSections R X)).toAlgebra

attribute [local instance] sectionsAlgebra

variable {R X}

/-- The base ring maps to sections over `W` through `R ≅ Γ(Spec R, ⊤)` and the structure
morphism. -/
private lemma algebraMap_sections_eq (W : X.Opens) :
    CommRingCat.ofHom (algebraMap R Γ(X, W)) = (Scheme.ΓSpecIso (.of R)).inv ≫
      (X ↘ Spec (.of R)).appLE ⊤ W (le_top.trans_eq (Scheme.Hom.preimage_top _).symm) := by
  ext r
  simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, baseRingToGlobalSections_apply,
    CommRingCat.hom_ofHom, CommRingCat.hom_comp]
  rfl

/-- On global sections, the base-ring algebra structure is `baseRingToGlobalSections`. -/
private lemma algebraMap_top (r : R) : algebraMap R Γ(X, ⊤) r = baseRingToGlobalSections R X r := by
  rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
    show (TopologicalSpace.Opens.leTop (⊤ : X.Opens)).op = 𝟙 _ from rfl, X.presheaf.map_id]
  rfl

/-- Restriction of sections of the structure sheaf is `R`-linear. -/
private def restrictLinear {V W : X.Opens} (h : V ≤ W) : Γ(X, W) →ₗ[R] Γ(X, V) where
  toFun := X.presheaf.map (homOfLE h).op
  map_add' := map_add _
  map_smul' r s := by
    simp only [Algebra.smul_def, map_mul, RingHom.id_apply]
    congr 1
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, ← CommRingCat.comp_apply,
      ← Functor.map_comp]
    rfl

variable {R' : Type u} [CommRing R'] [Algebra R R']
  {Y : Scheme.{u}} [Y.Over (Spec (.of R'))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (.of R')) (X ↘ Spec (.of R))
    (Spec.map (CommRingCat.ofHom (algebraMap R R'))))

/-- The ring map `h.appLE U W' e` on sections depends only on the morphism `h`, so equal morphisms
induce equal maps whatever the proofs `e`. -/
private lemma appLE_eq_of_eq {T : Scheme.{u}} {h₁ h₂ : Y ⟶ T} (e : h₁ = h₂) (U : T.Opens)
    (W' : Y.Opens) (e₁ : W' ≤ h₁ ⁻¹ᵁ U) (e₂ : W' ≤ h₂ ⁻¹ᵁ U) :
    h₁.appLE U W' e₁ = h₂.appLE U W' e₂ := by
  subst e; rfl

include H in
/-- Pulling back sections along `g` is compatible with the base-ring structures on both sides. -/
private lemma comm_sections {W : X.Opens} {W' : Y.Opens} (hW : W' ≤ g ⁻¹ᵁ W) :
    CommRingCat.ofHom (algebraMap R Γ(X, W)) ≫ g.appLE W W' hW =
      CommRingCat.ofHom (algebraMap R R') ≫ CommRingCat.ofHom (algebraMap R' Γ(Y, W')) := by
  rw [algebraMap_sections_eq, algebraMap_sections_eq, Category.assoc,
    Scheme.Hom.appLE_comp_appLE]
  refine (congrArg _ ((appLE_eq_of_eq H.w _ _ _
    (le_top.trans_eq (Scheme.Hom.preimage_top _).symm)).trans
    (Scheme.Hom.comp_appLE _ _ _ _ (le_top.trans_eq (Scheme.Hom.preimage_top _).symm)))).trans ?_
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
  · simp [algebraMap_sections_eq]
  · exact Category.comp_id _ |>.trans (Scheme.ΓSpecIso_naturality _)
  · simp
  · simp [algebraMap_sections_eq]

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

variable (R) (X) in
/-- The cohomology of the trivial line bundle is that of the structure sheaf. -/
private def trivialCohomologyLinearEquiv (i : ℕ) :
    Cohomology (InvertibleSheaf.trivial X).obj i ≃ₗ[R] Cohomology (structureModule X) i :=
  cohomologyBaseLinearEquivOfIso R (M := (InvertibleSheaf.trivial X).obj)
    (N := structureModule X) (eqToIso (InvertibleSheaf.trivial_obj X) ≪≫
      TauCeti.SheafOfModules.freePUnitIsoUnit X.ringCatSheaf) i

section Difference

variable {S : Type u} [CommRing S] {Z : Scheme.{u}} [Z.Over (Spec (.of S))] (U V : Z.Opens)

/-- The difference of restrictions `(s, t) ↦ s|_{U ⊓ V} - t|_{U ⊓ V}` of sections of the
structure sheaf, linear over the base ring. -/
private def ringDifference : (Γ(Z, U) × Γ(Z, V)) →ₗ[S] Γ(Z, U ⊓ V) :=
  (restrictLinear inf_le_left).comp (LinearMap.fst _ _ _) -
    (restrictLinear inf_le_right).comp (LinearMap.snd _ _ _)

/-- The ring-level difference map is the Mayer–Vietoris difference map of the structure
sheaf. -/
private lemma ringDifference_eq (x : Γ(Z, U) × Γ(Z, V)) :
    ringDifference (S := S) U V x =
      mayerVietorisSectionsDifferenceLinear (structureModule Z) U V x :=
  -- The sections of the structure sheaf as a module are the sections of the structure sheaf.
  ((mayerVietorisSectionsDifferenceLinear_apply (structureModule Z) U V x.1 x.2).trans
    (mayerVietorisSectionsDifference_apply (structureModule Z) U V x.1 x.2)).symm

variable (hUV : U ⊔ V = ⊤)
include hUV

/-- The Mayer–Vietoris boundary of the structure sheaf, linear over the base ring. -/
private def boundaryBase :
    Γ(Z, U ⊓ V) →ₗ[S] Cohomology (structureModule Z) 1 where
  toFun := mayerVietorisBoundaryLinear (structureModule Z) U V hUV
  map_add' := map_add _
  map_smul' r s :=
    (mayerVietorisBoundaryLinear (structureModule Z) U V hUV).map_smul
      (baseRingToGlobalSections S Z r) s

private lemma exact_ringDifference_boundaryBase :
    Function.Exact (ringDifference (S := S) U V) (boundaryBase (S := S) U V hUV) := by
  intro s
  -- Both maps are the Mayer–Vietoris maps of the structure sheaf, restricted to the base ring.
  refine LinearMap.mem_ker.symm.trans ((Iff.of_eq
    congr(s ∈ $(ker_mayerVietorisBoundaryLinear (structureModule Z) U V hUV))).trans ?_)
  exact ⟨fun ⟨x, hx⟩ ↦ ⟨x, (ringDifference_eq U V x).trans hx⟩,
    fun ⟨x, hx⟩ ↦ ⟨x, (ringDifference_eq U V x).symm.trans hx⟩⟩

private lemma boundaryBase_surjective
    (hU : Subsingleton (cohomologyOn (structureModule Z) 1 U))
    (hV : Subsingleton (cohomologyOn (structureModule Z) 1 V)) :
    Function.Surjective (boundaryBase (S := S) U V hUV) :=
  mayerVietorisBoundaryLinear_surjective _ U V hUV hU hV

omit hUV

end Difference

/-- Restricting and then pulling back sections agrees with pulling back and then restricting. -/
private lemma appLE_restrict {W₁ W₂ : X.Opens} {W₁' W₂' : Y.Opens} (h₁ : W₁' ≤ g ⁻¹ᵁ W₁)
    (h₂ : W₂' ≤ g ⁻¹ᵁ W₂) (hW : W₂ ≤ W₁) (hW' : W₂' ≤ W₁') (s : Γ(X, W₁)) :
    g.appLE W₂ W₂' h₂ (X.presheaf.map (homOfLE hW).op s) =
      Y.presheaf.map (homOfLE hW').op (g.appLE W₁ W₁' h₁ s) := by
  simp only [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

section CohomologyOne

variable (U V : X.Opens) (hUV : U ⊔ V = ⊤)

include hUV in
private lemma preimage_sup_eq_top : g ⁻¹ᵁ U ⊔ g ⁻¹ᵁ V = ⊤ := by
  rw [← Scheme.Hom.preimage_sup, hUV, Scheme.Hom.preimage_top]

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
  have hUV' := preimage_sup_eq_top (g := g) U V hUV
  have hUVc : IsCompact ((U ⊓ V : X.Opens) : Set X) := hUc.inter_of_isOpen hVc U.2 V.2
  -- The exact rows `Γ(U) × Γ(V) → Γ(U ⊓ V) → H¹ → 0` on `X` and on `Y`.
  let δ := boundaryBase (S := R) U V hUV
  let δ' := boundaryBase (S := R') (g ⁻¹ᵁ U) (g ⁻¹ᵁ V) hUV'
  have hδ := boundaryBase_surjective (S := R) U V hUV hU hV
  have hex := exact_ringDifference_boundaryBase (S := R) U V hUV
  have hex' := exact_ringDifference_boundaryBase (S := R') (g ⁻¹ᵁ U) (g ⁻¹ᵁ V) hUV'
  -- The vertical maps pull back sections along `g`.
  let σU := sectionsBaseChange H (W := U) (W' := g ⁻¹ᵁ U) le_rfl
  let σV := sectionsBaseChange H (W := V) (W' := g ⁻¹ᵁ V) le_rfl
  let σUV := sectionsBaseChange H (W := U ⊓ V) (W' := g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)
    (Scheme.Hom.preimage_inf (f := g)).ge
  have comm₁ : σUV.comp (ringDifference U V) =
      ((ringDifference (S := R') (g ⁻¹ᵁ U) (g ⁻¹ᵁ V)).restrictScalars R).comp
        (σU.prodMap σV) := by
    refine LinearMap.ext fun ⟨s, t⟩ ↦ ?_
    exact (map_sub _ _ _).trans (congrArg₂ (· - ·) (appLE_restrict le_rfl _ _ _ s)
      (appLE_restrict le_rfl _ _ _ t))
  -- The induced map on first cohomology.
  have hker : LinearMap.ker δ ≤ LinearMap.ker ((δ'.restrictScalars R).comp σUV) := by
    intro x hx
    obtain ⟨y, rfl⟩ := (hex x).mp hx
    exact (congrArg δ' congr($comm₁ y)).trans (hex'.apply_apply_eq_zero _)
  let φ := ((LinearMap.ker δ).liftQ _ hker).comp (δ.quotKerEquivOfSurjective hδ).symm.toLinearMap
  have comm₂ : φ.comp δ = (δ'.restrictScalars R).comp σUV := by
    ext s
    simp [φ]
  have hσU := isBaseChange_sectionsBaseChange H hUc (.of_quasiSeparatedSpace _) (W' := g ⁻¹ᵁ U) rfl
  have hσV := isBaseChange_sectionsBaseChange H hVc (.of_quasiSeparatedSpace _) (W' := g ⁻¹ᵁ V) rfl
  have hσUV := isBaseChange_sectionsBaseChange H hUVc (.of_quasiSeparatedSpace _)
    (W' := g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V) (Scheme.Hom.preimage_inf g).symm
  have hb₁ := IsBaseChange.prodMap (S := R') σU σV hσU hσV
  have key := IsBaseChange.of_right_exact R' _ _ φ comm₁ comm₂ hb₁ hσUV hex hδ hex'
    (boundaryBase_surjective (S := R') _ _ hUV' hU' hV')
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
  exact ⟨((trivialCohomologyLinearEquiv R X 1).baseChange R R' _ _).trans
    (e.trans (trivialCohomologyLinearEquiv R' Y 1).symm)⟩

end CohomologyOne

variable (R) (X) in
/-- The global sections of the structure sheaf as a module are its ring of global functions, as
modules over the base ring. -/
private def globalSectionsLinearEquiv : Γ(structureModule X, ⊤) ≃ₗ[R] Γ(X, ⊤) where
  toFun s := s
  invFun s := s
  map_add' _ _ := rfl
  -- Both actions multiply by the global function `baseRingToGlobalSections R X r`.
  map_smul' r s := (congrArg (· * (show Γ(X, ⊤) from s)) (algebraMap_top r)).symm
  left_inv _ := rfl
  right_inv _ := rfl

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
  let eX := (trivialCohomologyLinearEquiv R X 0).trans
    ((cohomologyZeroBaseLinearEquiv R X _).trans (globalSectionsLinearEquiv R X))
  let eY := (trivialCohomologyLinearEquiv R' Y 0).trans
    ((cohomologyZeroBaseLinearEquiv R' Y _).trans (globalSectionsLinearEquiv R' Y))
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
finite type over a field and covered by two affine opens. The finite-dimensionality of `H¹`
after base change follows from that before, by
`finiteDimensional_cohomology_one_trivial_of_isPullback`. -/
theorem genus_eq_of_isPullback [LocallyOfFiniteType (X ↘ Spec (.of k))] {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj 1)]
    [FiniteDimensional K (Cohomology (InvertibleSheaf.trivial Y).obj 1)] :
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
