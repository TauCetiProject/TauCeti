/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections

public import TauCeti.AlgebraicGeometry.Cohomology.SectionsQuotient.Linear
public import TauCeti.AlgebraicGeometry.Cohomology.Genus
public import TauCeti.AlgebraicGeometry.Cohomology.Trivial
public import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct
public import TauCeti.AlgebraicGeometry.Scheme.SectionsBaseChange
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact

/-!
# Flat base change for cohomology

Let `X` be a scheme over a commutative ring `R`, let `R → R'` be a flat ring map, and let
`Y = X ×_R R'` be the base change, given as a pullback square `H` over `Spec R' ⟶ Spec R`. This
file proves base change in degree zero for quasicoherent sheaves on a quasi-compact
quasi-separated scheme, and in degree one on a two-affine cover, and records the structure-sheaf
consequences:

* `H⁰(Y, g^* M) ≅ R' ⊗_R H⁰(X, M)` for flat `R → R'`, when `X` is quasi-compact and
  quasi-separated, using the canonical pullback of global sections;
* `H¹(Y, g^* M) ≅ R' ⊗_R H¹(X, M)` for a quasicoherent `M` and an arbitrary base-ring
  map, when `X` and `Y` are locally Noetherian and `X` has a two-affine cover with affine
  intersection;
* `H⁰(Y, 𝒪_Y) ≅ R' ⊗_R H⁰(X, 𝒪_X)` when `X` is quasi-compact and quasi-separated;
* `H¹(Y, 𝒪_Y) ≅ R' ⊗_R H¹(X, 𝒪_X)` under the same two-affine hypotheses.

Over a field `k` and a field extension `K / k`, these say that `dim_k H⁰(X, 𝒪_X)` and, for `X`
locally of finite type over `k` and covered by two affine opens, `dim_k H¹(X, 𝒪_X)` do not change
under base change to `K`; when moreover `H¹(X, 𝒪_X)` is finite-dimensional, so is `H¹` after base
change, and the genus does not change either. Smooth proper curves are covered by two affine
opens, so this applies to them (`TauCeti.AlgebraicGeometry.Curves.Genus.BaseChange`).

The structure sheaf is written as the trivial line bundle `(InvertibleSheaf.trivial X).obj`, as for
the genus `Scheme.genus`. The degree-one isomorphisms are stated as `Nonempty` linear
equivalences: their construction depends on the chosen cover, and no naturality is claimed.
The degree-zero coefficient equivalence is canonical and has the expected section equation on
`1 ⊗ x`. Coefficient comparisons use the canonical pullback `(Scheme.Modules.pullback g).obj M`.

On sections, flat base change is
`AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`: for a quasi-compact
quasi-separated open `W ⊆ X`, `Γ(Y, g⁻¹ W) = R' ⊗_R Γ(X, W)`, restated over the base ring as
`TauCeti.AlgebraicGeometry.isBaseChange_sectionsBaseChange`. For quasicoherent coefficients it is
`AlgebraicGeometry.Scheme.Hom.isBaseChange_pullbackSections_of_isQuasiSeparated`. For a cover
`X = U ∪ V` whose members have vanishing first cohomology, the Mayer–Vietoris sequence presents
`H¹(X, 𝒪_X)` as the cokernel of `Γ(U) × Γ(V) → Γ(U ∩ V)`
(`TauCeti.AlgebraicGeometry.ker_mayerVietorisBoundaryLinear`), and tensor products preserve
cokernels (`IsBaseChange.of_right_exact`). Affine opens with Noetherian rings of sections have
vanishing higher cohomology by Serre's vanishing theorem, before and after base change.

## Main results

* `TauCeti.AlgebraicGeometry.linearEquivTensorCohomologyZeroPullback`: canonical flat base
  change for `H⁰` of quasicoherent coefficients on a quasi-compact quasi-separated scheme.
* `TauCeti.AlgebraicGeometry.nonempty_linearEquiv_tensor_cohomology_zero_trivial`,
  `TauCeti.AlgebraicGeometry.nonempty_linearEquiv_tensor_cohomology_one_trivial`: flat base
  change for `H⁰` and `H¹` of the structure sheaf.
* `TauCeti.AlgebraicGeometry.nonempty_linearEquiv_tensor_cohomology_one_pullback`: base change
  for `H¹` of a quasicoherent sheaf on a two-affine cover, along any base-ring map.
* `TauCeti.AlgebraicGeometry.finrank_cohomology_zero_pullback_eq_of_isPullback`,
  `TauCeti.AlgebraicGeometry.finrank_cohomology_one_pullback_eq_of_isPullback` and
  `TauCeti.AlgebraicGeometry.finiteDimensional_cohomology_one_pullback_of_isPullback`: dimension
  and finiteness consequences over field extensions.
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

variable (g) in
/-- Pulling back sections along `g` commutes with the Mayer–Vietoris difference of restrictions.
The intersection of the preimages is definitionally the preimage of the intersection
(`Scheme.Hom.preimage_inf`). -/
private lemma pullbackSections_mayerVietorisSectionsDifference (M : X.Modules) (U V : X.Opens)
    (s : Γ(M, U)) (t : Γ(M, V)) :
    g.pullbackSections M (U ⊓ V) (mayerVietorisSectionsDifference M U V (s, t)) =
      mayerVietorisSectionsDifference ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U) (g ⁻¹ᵁ V)
        (g.pullbackSections M U s, g.pullbackSections M V t) := by
  rw [mayerVietorisSectionsDifference_apply, mayerVietorisSectionsDifference_apply]
  exact (map_sub _ _ _).trans <| congrArg₂ (· - ·)
    (g.pullbackSections_restrict M U (homOfLE inf_le_left) s).symm
    (g.pullbackSections_restrict M V (homOfLE inf_le_right) t).symm

section CohomologyOne

variable (U V : X.Opens) (hUV : U ⊔ V = ⊤)

include hUV in
/-- The cokernel comparison shared by the coefficient and structure-sheaf cases. Let `X = U ∪ V`
and `Y = U' ∪ V'` be covers whose members have vanishing first cohomology, so that the
Mayer–Vietoris sequences present `H¹` as cokernels of the section differences. Section maps over
the members and over the intersections that commute with these differences and are scalar
extensions from `R` to `R'` induce `H¹(Y, N) ≅ R' ⊗_R H¹(X, M)`. -/
private lemma nonempty_linearEquiv_tensor_cohomology_one_of_isBaseChange
    (M : X.Modules) (N : Y.Modules) {U' V' : Y.Opens} (hUV' : U' ⊔ V' = ⊤)
    [∀ W : X.Opens, Module R Γ(M, W)] [∀ W : X.Opens, IsScalarTower R Γ(X, ⊤) Γ(M, W)]
    [∀ W' : Y.Opens, Module R' Γ(N, W')] [∀ W' : Y.Opens, IsScalarTower R' Γ(Y, ⊤) Γ(N, W')]
    [∀ W' : Y.Opens, Module R Γ(N, W')] [∀ W' : Y.Opens, IsScalarTower R R' Γ(N, W')]
    (hU : Subsingleton (cohomologyOn M 1 U)) (hV : Subsingleton (cohomologyOn M 1 V))
    (hU' : Subsingleton (cohomologyOn N 1 U')) (hV' : Subsingleton (cohomologyOn N 1 V'))
    (σU : Γ(M, U) →ₗ[R] Γ(N, U')) (σV : Γ(M, V) →ₗ[R] Γ(N, V'))
    (σUV : Γ(M, U ⊓ V) →ₗ[R] Γ(N, U' ⊓ V'))
    (comm : ∀ s t, σUV (mayerVietorisSectionsDifference M U V (s, t)) =
      mayerVietorisSectionsDifference N U' V' (σU s, σV t))
    (hσU : IsBaseChange R' σU) (hσV : IsBaseChange R' σV) (hσUV : IsBaseChange R' σUV) :
    Nonempty (R' ⊗[R] Cohomology M 1 ≃ₗ[R'] Cohomology N 1) := by
  let : Module R (Cohomology N 1) := Module.compHom _ (algebraMap R R')
  have : IsScalarTower R R' (Cohomology N 1) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  -- The exact rows `Γ(U) × Γ(V) → Γ(U ⊓ V) → H¹ → 0` on `X` and on `Y`: the Mayer–Vietoris maps,
  -- restricted to the base ring.
  let d : (Γ(M, U) × Γ(M, V)) →ₗ[R] Γ(M, U ⊓ V) :=
    (mayerVietorisSectionsDifferenceLinear M U V).restrictScalars R
  let d' : (Γ(N, U') × Γ(N, V')) →ₗ[R'] Γ(N, U' ⊓ V') :=
    (mayerVietorisSectionsDifferenceLinear N U' V').restrictScalars R'
  let δ : Γ(M, U ⊓ V) →ₗ[R] Cohomology M 1 :=
    (mayerVietorisBoundaryLinear M U V hUV).restrictScalars R
  let δ' : Γ(N, U' ⊓ V') →ₗ[R'] Cohomology N 1 :=
    (mayerVietorisBoundaryLinear N U' V' hUV').restrictScalars R'
  have hδ : Function.Surjective δ := mayerVietorisBoundaryLinear_surjective M U V hUV hU hV
  have hδ' : Function.Surjective δ' :=
    mayerVietorisBoundaryLinear_surjective N U' V' hUV' hU' hV'
  have hex : Function.Exact d δ :=
    (LinearMap.exact_iff (f := mayerVietorisSectionsDifferenceLinear M U V)
      (g := mayerVietorisBoundaryLinear M U V hUV)).mpr (ker_mayerVietorisBoundaryLinear M U V hUV)
  have hex' : Function.Exact d' δ' :=
    (LinearMap.exact_iff (f := mayerVietorisSectionsDifferenceLinear N U' V')
      (g := mayerVietorisBoundaryLinear N U' V' hUV')).mpr
        (ker_mayerVietorisBoundaryLinear N U' V' hUV')
  have comm₁ : σUV.comp d = (d'.restrictScalars R).comp (σU.prodMap σV) :=
    LinearMap.ext fun ⟨s, t⟩ ↦ by simpa [d, d'] using comm s t
  -- The induced map on first cohomology.
  have hker : LinearMap.ker δ ≤ LinearMap.ker ((δ'.restrictScalars R).comp σUV) := by
    intro x hx
    obtain ⟨y, rfl⟩ := (hex x).mp hx
    exact (congrArg δ' congr($comm₁ y)).trans (hex'.apply_apply_eq_zero _)
  let φ := δ.liftOfSurjective hδ ⟨(δ'.restrictScalars R).comp σUV, hker⟩
  have comm₂ : φ.comp δ = (δ'.restrictScalars R).comp σUV :=
    LinearMap.ext fun _ ↦ LinearMap.equivOfSurjective_apply hδ hker
  have hb₁ := IsBaseChange.prodMap (S := R') σU σV hσU hσV
  exact ⟨(IsBaseChange.of_right_exact R' _ _ φ comm₁ comm₂ hb₁ hσUV hex hδ hex' hδ').equiv⟩

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
  let : ∀ W' : Y.Opens, Module R Γ(structureModule Y, W') :=
    fun _ ↦ Module.compHom _ (algebraMap R R')
  have : ∀ W' : Y.Opens, IsScalarTower R R' Γ(structureModule Y, W') :=
    fun _ ↦ IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hUV' : g ⁻¹ᵁ U ⊔ g ⁻¹ᵁ V = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, hUV, Scheme.Hom.preimage_top]
  have hUVc : IsCompact ((U ⊓ V : X.Opens) : Set X) := hUc.inter_of_isOpen hVc U.2 V.2
  -- The vertical maps pull back sections along `g`.
  let σU : Γ(structureModule X, U) →ₗ[R] Γ(structureModule Y, g ⁻¹ᵁ U) :=
    sectionsBaseChange H (W := U) (W' := g ⁻¹ᵁ U) le_rfl
  let σV : Γ(structureModule X, V) →ₗ[R] Γ(structureModule Y, g ⁻¹ᵁ V) :=
    sectionsBaseChange H (W := V) (W' := g ⁻¹ᵁ V) le_rfl
  let σUV : Γ(structureModule X, U ⊓ V) →ₗ[R] Γ(structureModule Y, g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V) :=
    sectionsBaseChange H (W := U ⊓ V) (W' := g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)
      (Scheme.Hom.preimage_inf (f := g)).ge
  -- Restriction commutes with pulling back along `g`.
  have hres {W₁ W₂ : X.Opens} {W₂' : Y.Opens} (h₂ : W₂' ≤ g ⁻¹ᵁ W₂) (hW : W₂ ≤ W₁)
      (hW' : W₂' ≤ g ⁻¹ᵁ W₁) (s : Γ(X, W₁)) :
      sectionsBaseChange H h₂ (X.presheaf.map (homOfLE hW).op s) =
        Y.presheaf.map (homOfLE hW').op (sectionsBaseChange H (W' := g ⁻¹ᵁ W₁) le_rfl s) := by
    simp only [sectionsBaseChange_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
      Scheme.Hom.appLE_map]
  exact nonempty_linearEquiv_tensor_cohomology_one_of_isBaseChange U V hUV
    (structureModule X) (structureModule Y) hUV' hU hV hU' hV' σU σV σUV
    (fun s t ↦ by
      rw [mayerVietorisSectionsDifference_apply, mayerVietorisSectionsDifference_apply]
      exact (map_sub σUV _ _).trans <|
        congrArg₂ (· - ·) (hres _ inf_le_left _ s) (hres _ inf_le_right _ t))
    (isBaseChange_sectionsBaseChange H hUc (.of_quasiSeparatedSpace _) rfl)
    (isBaseChange_sectionsBaseChange H hVc (.of_quasiSeparatedSpace _) rfl)
    (isBaseChange_sectionsBaseChange H hUVc (.of_quasiSeparatedSpace _)
      (Scheme.Hom.preimage_inf g).symm)

include H hUV in
/-- The core coefficient comparison: base change preserves first cohomology for a quasicoherent
sheaf on a two-affine cover with affine intersection. -/
private lemma nonempty_linearEquiv_tensor_cohomology_one_pullback_aux
    (M : X.Modules) [M.IsQuasicoherent] [IsLocallyNoetherian X]
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hInter : IsAffineOpen (U ⊓ V))
    (hU' : Subsingleton (cohomologyOn ((Scheme.Modules.pullback g).obj M) 1 (g ⁻¹ᵁ U)))
    (hV' : Subsingleton (cohomologyOn ((Scheme.Modules.pullback g).obj M) 1 (g ⁻¹ᵁ V))) :
  Nonempty (R' ⊗[R] Cohomology M 1 ≃ₗ[R']
      Cohomology ((Scheme.Modules.pullback g).obj M) 1) := by
  let N := (Scheme.Modules.pullback g).obj M
  let : ∀ W : X.Opens, Module R Γ(M, W) := fun W ↦
    Module.compHom _ ((X.baseRingToStructurePresheaf R).app (op W)).hom
  have : ∀ W : X.Opens, IsScalarTower R Γ(X, W) Γ(M, W) :=
    fun _ ↦ IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : ∀ W' : Y.Opens, Module R' Γ(N, W') := fun W' ↦
    Module.compHom _ ((Y.baseRingToStructurePresheaf R').app (op W')).hom
  have : ∀ W' : Y.Opens, IsScalarTower R' Γ(Y, W') Γ(N, W') :=
    fun _ ↦ IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : ∀ W' : Y.Opens, Module R Γ(N, W') := fun _ ↦ Module.compHom _ (algebraMap R R')
  have : ∀ W' : Y.Opens, IsScalarTower R R' Γ(N, W') :=
    fun _ ↦ IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hUV' : g ⁻¹ᵁ U ⊔ g ⁻¹ᵁ V = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, hUV, Scheme.Hom.preimage_top]
  have hU₁ : Subsingleton (cohomologyOn M 1 U) := by
    have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    exact Scheme.Modules.subsingleton_cohomologyOn_succ_of_isAffineOpen M hU 0
  have hV₁ : Subsingleton (cohomologyOn M 1 V) := by
    have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    exact Scheme.Modules.subsingleton_cohomologyOn_succ_of_isAffineOpen M hV 0
  -- Over the intersection, `g ⁻¹ᵁ (U ⊓ V)` is definitionally `g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V`
  -- (`Scheme.Hom.preimage_inf` is `rfl`), so the pullback of sections needs no transport.
  exact nonempty_linearEquiv_tensor_cohomology_one_of_isBaseChange U V hUV M N hUV'
    hU₁ hV₁ hU' hV' (g.pullbackSectionsBaseLinear M U H.toCommSq)
    (g.pullbackSectionsBaseLinear M V H.toCommSq)
    (g.pullbackSectionsBaseLinear M (U ⊓ V) H.toCommSq)
    (fun s t ↦ (g.pullbackSectionsBaseLinear_apply M (U ⊓ V) H.toCommSq _).trans <|
      (pullbackSections_mayerVietorisSectionsDifference g M U V s t).trans <| congrArg _ <|
        Prod.ext (g.pullbackSectionsBaseLinear_apply M U H.toCommSq s).symm
          (g.pullbackSectionsBaseLinear_apply M V H.toCommSq t).symm)
    (g.isBaseChange_pullbackSections M U H hU) (g.isBaseChange_pullbackSections M V H hV)
    (g.isBaseChange_pullbackSections M (U ⊓ V) H hInter)

include H in
/-- **Base change for `H¹` of a quasicoherent sheaf on a two-affine cover.** Let `X` be a
locally Noetherian scheme over `R`, covered by affine opens `U` and `V` whose intersection is
affine. Let `Y = X ×_R R'` be a locally Noetherian base change along any ring map. Then the
first cohomology of the pullback of a quasicoherent sheaf `M` is the scalar extension of
`H¹(X, M)` from `R` to `R'`.

No flatness hypothesis is imposed on `R → R'`, and no finiteness or flatness hypothesis is
imposed on `M`. -/
theorem nonempty_linearEquiv_tensor_cohomology_one_pullback
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (M : X.Modules) [M.IsQuasicoherent]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hInter : IsAffineOpen (U ⊓ V)) (hUV : U ⊔ V = ⊤) :
    Nonempty (R' ⊗[R] Cohomology M 1 ≃ₗ[R']
      Cohomology ((Scheme.Modules.pullback g).obj M) 1) := by
  have : IsAffineHom g := MorphismProperty.of_isPullback H.flip inferInstance
  have hU' := hU.preimage g
  have hV' := hV.preimage g
  have : IsNoetherianRing Γ(Y, g ⁻¹ᵁ U) :=
    IsLocallyNoetherian.component_noetherian ⟨g ⁻¹ᵁ U, hU'⟩
  have hU₁ : Subsingleton
      (cohomologyOn ((Scheme.Modules.pullback g).obj M) 1 (g ⁻¹ᵁ U)) :=
    Scheme.Modules.subsingleton_cohomologyOn_succ_of_isAffineOpen _ hU' 0
  have : IsNoetherianRing Γ(Y, g ⁻¹ᵁ V) :=
    IsLocallyNoetherian.component_noetherian ⟨g ⁻¹ᵁ V, hV'⟩
  have hV₁ : Subsingleton
      (cohomologyOn ((Scheme.Modules.pullback g).obj M) 1 (g ⁻¹ᵁ V)) :=
    Scheme.Modules.subsingleton_cohomologyOn_succ_of_isAffineOpen _ hV' 0
  exact nonempty_linearEquiv_tensor_cohomology_one_pullback_aux H U V hUV M hU hV hInter hU₁ hV₁

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

attribute [local instance] isScalarTower_cohomology

include H in
/-- **Flat base change for `H⁰`.** The canonical equivalence `R' ⊗_R H⁰(X, M) ≃ H⁰(Y, g^* M)` for
a quasi-coherent sheaf `M` on a quasi-compact quasi-separated scheme `X` over `R` and a flat ring
map `R → R'`. Neither Noetherianity nor finiteness of the coefficients is required. Its action on
`1 ⊗ x` is characterized by `linearEquivTensorCohomologyZeroPullback_one_tmul`. -/
def linearEquivTensorCohomologyZeroPullback [Module.Flat R R'] [CompactSpace X]
    [QuasiSeparatedSpace X] (M : X.Modules) [M.IsQuasicoherent] :
    R' ⊗[R] Cohomology M 0 ≃ₗ[R'] Cohomology ((Scheme.Modules.pullback g).obj M) 0 := by
  let N := (Scheme.Modules.pullback g).obj M
  -- Use the canonical base-ring actions on top sections, and restrict the target action along
  -- `R → R'`. The native action of global functions on top sections is retained.
  let : Module R Γ(M, ⊤) := Module.compHom _ ((X.baseRingToStructurePresheaf R).app (op ⊤)).hom
  have : IsScalarTower R Γ(X, ⊤) Γ(M, ⊤) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  -- The target actions are given on every open, so that they also apply to sections over the
  -- inverse image `g ⁻¹ᵁ ⊤` of top, on which pullback of sections lands.
  let : ∀ W' : Y.Opens, Module R' Γ(N, W') := fun W' ↦
    Module.compHom _ ((Y.baseRingToStructurePresheaf R').app (op W')).hom
  have : ∀ W' : Y.Opens, IsScalarTower R' Γ(Y, W') Γ(N, W') :=
    fun _ ↦ IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower R' Γ(Y, ⊤) Γ(N, ⊤) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : ∀ W' : Y.Opens, Module R Γ(N, W') := fun _ ↦ Module.compHom _ (algebraMap R R')
  have : ∀ W' : Y.Opens, IsScalarTower R R' Γ(N, W') :=
    fun _ ↦ IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  -- Pullback lands in sections over `g ⁻¹ᵁ ⊤`, which is `⊤` by definition.
  let σtop : Γ(M, ⊤) →ₗ[R] Γ(N, ⊤) := g.pullbackSectionsBaseLinear M ⊤ H.toCommSq
  have hσ : IsBaseChange R' σtop :=
    g.isBaseChange_pullbackSections_of_isQuasiSeparated M H isCompact_univ isQuasiSeparated_univ
  let eX := (cohomologyZeroLinearEquiv M).restrictScalars R
  let eY := (cohomologyZeroLinearEquiv N).restrictScalars R'
  exact (eX.baseChange R R' _ _).trans (hσ.equiv.trans eY.symm)

/-- The zeroth-cohomology comparison sends `1 ⊗ x` to the pullback of the section represented
by `x`. -/
@[simp]
lemma linearEquivTensorCohomologyZeroPullback_one_tmul [Module.Flat R R'] [CompactSpace X]
    [QuasiSeparatedSpace X] (M : X.Modules) [M.IsQuasicoherent] (x : Cohomology M 0) :
    cohomologyZeroEquiv ((Scheme.Modules.pullback g).obj M)
        (linearEquivTensorCohomologyZeroPullback H M ((1 : R') ⊗ₜ[R] x)) =
      g.pullbackSections M ⊤ (cohomologyZeroEquiv M x) := by
  let N := (Scheme.Modules.pullback g).obj M
  let : Module R Γ(M, ⊤) := Module.compHom _ ((X.baseRingToStructurePresheaf R).app (op ⊤)).hom
  have : IsScalarTower R Γ(X, ⊤) Γ(M, ⊤) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  -- The target actions are given on every open, so that they also apply to sections over the
  -- inverse image `g ⁻¹ᵁ ⊤` of top, on which pullback of sections lands.
  let : ∀ W' : Y.Opens, Module R' Γ(N, W') := fun W' ↦
    Module.compHom _ ((Y.baseRingToStructurePresheaf R').app (op W')).hom
  have : ∀ W' : Y.Opens, IsScalarTower R' Γ(Y, W') Γ(N, W') :=
    fun _ ↦ IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower R' Γ(Y, ⊤) Γ(N, ⊤) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : ∀ W' : Y.Opens, Module R Γ(N, W') := fun _ ↦ Module.compHom _ (algebraMap R R')
  have : ∀ W' : Y.Opens, IsScalarTower R R' Γ(N, W') :=
    fun _ ↦ IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  rw [← cohomologyZeroLinearEquiv_apply]
  simp only [linearEquivTensorCohomologyZeroPullback, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul, LinearEquiv.restrictScalars_apply,
    LinearEquiv.restrictScalars_symm_apply, LinearEquiv.apply_symm_apply,
    cohomologyZeroLinearEquiv_apply]
  -- The tensor comparison uses the native top-section carrier, whereas pullback is initially
  -- expressed on the inverse image of top. The characteristic equations identify these maps.
  erw [IsBaseChange.equiv_tmul, Scheme.Hom.pullbackSectionsBaseLinear_apply]
  exact one_smul R' (g.pullbackSections M ⊤ (cohomologyZeroEquiv M x))

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
/-- The dimension of zeroth cohomology of quasicoherent coefficients on a quasi-compact
quasi-separated scheme over a field is invariant under extension of the base field. -/
theorem finrank_cohomology_zero_pullback_eq_of_isPullback [CompactSpace X]
    [QuasiSeparatedSpace X] (M : X.Modules) [M.IsQuasicoherent] :
    finrank K (Cohomology ((Scheme.Modules.pullback g).obj M) 0) =
      finrank k (Cohomology M 0) := by
  let e := linearEquivTensorCohomologyZeroPullback H M
  rw [← e.finrank_eq, Module.finrank_baseChange]

include H in
/-- Over a field, `H¹(X_K, g^*M) ≅ K ⊗_k H¹(X, M)` for quasicoherent coefficients on a
scheme locally of finite type over `k` with a two-affine cover having affine intersection. -/
private theorem nonempty_linearEquiv_tensor_cohomology_one_pullback_of_field
    [LocallyOfFiniteType (X ↘ Spec (.of k))] (M : X.Modules) [M.IsQuasicoherent]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hInter : IsAffineOpen (U ⊓ V)) (hUV : U ⊔ V = ⊤) :
    Nonempty (K ⊗[k] Cohomology M 1 ≃ₗ[K]
      Cohomology ((Scheme.Modules.pullback g).obj M) 1) := by
  have : LocallyOfFiniteType (Y ↘ Spec (.of K)) := MorphismProperty.of_isPullback H inferInstance
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of K))
  exact nonempty_linearEquiv_tensor_cohomology_one_pullback H M hU hV hInter hUV

include H in
/-- The dimension of `H¹` of a quasicoherent sheaf does not change under extension of the base
field, when the scheme is locally of finite type and has a two-affine cover with affine
intersection. The coefficients after base change are the canonical pullback sheaf. -/
theorem finrank_cohomology_one_pullback_eq_of_isPullback
    [LocallyOfFiniteType (X ↘ Spec (.of k))] (M : X.Modules) [M.IsQuasicoherent]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hInter : IsAffineOpen (U ⊓ V)) (hUV : U ⊔ V = ⊤) :
    finrank K (Cohomology ((Scheme.Modules.pullback g).obj M) 1) =
      finrank k (Cohomology M 1) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_tensor_cohomology_one_pullback_of_field
    H M hU hV hInter hUV
  rw [← e.finrank_eq, Module.finrank_baseChange]

include H in
/-- First cohomology of a quasicoherent sheaf stays finite-dimensional under extension of the
base field, when the scheme is locally of finite type and has a two-affine cover with affine
intersection. -/
theorem finiteDimensional_cohomology_one_pullback_of_isPullback
    [LocallyOfFiniteType (X ↘ Spec (.of k))] (M : X.Modules) [M.IsQuasicoherent]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hInter : IsAffineOpen (U ⊓ V)) (hUV : U ⊔ V = ⊤)
    [FiniteDimensional k (Cohomology M 1)] :
    FiniteDimensional K (Cohomology ((Scheme.Modules.pullback g).obj M) 1) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_tensor_cohomology_one_pullback_of_field
    H M hU hV hInter hUV
  exact Module.Finite.equiv e

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
