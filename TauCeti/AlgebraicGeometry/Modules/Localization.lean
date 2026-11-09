/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Topology.QuasiSeparated
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Restriction
public import TauCeti.AlgebraicGeometry.Scheme.Opens
import TauCeti.Algebra.Group.Action.Pow

/-!
# Sections of quasi-coherent modules over basic opens

Let `M` be a quasi-coherent `𝒪_X`-module on a scheme `X`, let `U` be an affine open of `X` and
let `f ∈ Γ(X, U)`. Then the sections of `M` over the basic open `X.basicOpen f` are the
localization of the sections over `U` at the powers of `f`: the restriction map
`Γ(M, U) ⟶ Γ(M, X.basicOpen f)` is a localization of `Γ(X, U)`-modules. This is the module
counterpart of `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen` for the structure sheaf.

This is the affine-local description of quasi-coherent modules needed to build objects over `X`
from their sections over affine opens. For instance, it is the condition making a quasi-coherent
sheaf of algebras coequifibered over the structure sheaf on the small affine Zariski site, which
is the input of `AlgebraicGeometry.AffineZariskiSite.relativeGluingData`.

Over `Spec R` the statement is Mathlib's `AlgebraicGeometry.isIso_fromTildeΓ_iff_isLocalizing`;
this module extends that affine result to arbitrary schemes. Conversely, an `𝒪_X`-module whose
sections over the basic opens of the members of an affine open cover are such localizations is
quasi-coherent. This is how quasi-coherence is checked for modules built from explicit sections,
such as the twisting sheaves on `Proj`.

More generally, the restriction is a localization over every quasi-compact quasi-separated open
`U`. Sections over `U` are determined by their restrictions to a finite affine cover, and are
glued from sections that agree on the pairwise intersections, which are quasi-compact. On each
affine member a section over `X.basicOpen f` extends after multiplication by a power of `f`, and
on the quasi-compact intersections the extensions agree after multiplication by a further power.
This is the input for the quasi-coherence of pushforwards along quasi-compact quasi-separated
morphisms.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.moduleBasicOpen`: for `f ∈ Γ(X, U)`, the sections
  `Γ(M, X.basicOpen f)` form a `Γ(X, U)`-module by restriction of scalars;
* `AlgebraicGeometry.Scheme.Modules.basicOpenRestrict`: the restriction map
  `Γ(M, U) ⟶ Γ(M, X.basicOpen f)` as a `Γ(X, U)`-linear map;
* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict`: for quasi-coherent
  `M` and affine `U`, this restriction map is the localization at the powers of `f`.
* `AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_map`: for quasi-coherent `M` and affine
  `U`, a section over `X.basicOpen f` times a power of `f` extends to `U`.
* `AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_zero_of_isCompact`: for quasi-coherent `M`
  and quasi-compact `U`, a section over `U` vanishing on `X.basicOpen f` is killed by a power of
  `f`.
* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict_of_qcqs`: for
  quasi-coherent `M` and quasi-compact quasi-separated `U`, the restriction map
  `Γ(M, U) ⟶ Γ(M, X.basicOpen f)` is the localization at the powers of `f`.
* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocalizedModule`: conversely, `M` is
  quasi-coherent if these restriction maps are localizations on the members of an affine open
  cover; `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_iff_isLocalizedModule` is the
  resulting characterization.

## References

* R. Hartshorne, *Algebraic Geometry*, Lemma II.5.3.
* R. Vakil, *The Rising Sea*, the qcqs lemma; Mathlib's
  `AlgebraicGeometry.isLocalization_basicOpen_of_qcqs` is the structure-sheaf case.
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I* (1971),
  Théorème 1.4.1.
-/

public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace TauCeti

universe u

noncomputable section

variable {X : Scheme.{u}} {U : X.Opens}

variable (M : X.Modules)

/-- For `f ∈ Γ(X, U)`, the sections of an `𝒪_X`-module over `X.basicOpen f` form a
`Γ(X, U)`-module by restriction of scalars along `Γ(X, U) ⟶ Γ(X, X.basicOpen f)`. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.moduleBasicOpen (f : Γ(X, U)) :
    Module Γ(X, U) Γ(M, X.basicOpen f) :=
  Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen f))

/-- The `Γ(X, U)`-module structure on `Γ(M, X.basicOpen f)` factors through
`Γ(X, X.basicOpen f)`. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isScalarTower_basicOpen (f : Γ(X, U)) :
    IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) :=
  IsScalarTower.of_compHom _ _ _

/-- A function `r` on `U` acts on sections over `X.basicOpen f` through its restriction to
`X.basicOpen f`. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.basicOpen_smul_def (f r : Γ(X, U))
    (y : Γ(M, X.basicOpen f)) :
    r • y = X.presheaf.map (homOfLE (X.basicOpen_le f)).op r • y :=
  rfl

/-- The restriction of sections of an `𝒪_X`-module from `U` to `X.basicOpen f`, as a
`Γ(X, U)`-linear map. -/
def _root_.AlgebraicGeometry.Scheme.Modules.basicOpenRestrict (f : Γ(X, U)) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen f) where
  toFun := M.presheaf.map (homOfLE (X.basicOpen_le f)).op
  map_add' := map_add _
  map_smul' r x := M.map_smul _ r x

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.basicOpenRestrict_apply (f : Γ(X, U))
    (x : Γ(M, U)) :
    M.basicOpenRestrict f x = M.presheaf.map (homOfLE (X.basicOpen_le f)).op x :=
  (rfl)

/-- A section `f ∈ Γ(X, U)` acts invertibly on the sections of an `𝒪_X`-module over the basic
open `X.basicOpen f`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isUnit_algebraMap_end_basicOpen (f : Γ(X, U)) :
    IsUnit (algebraMap Γ(X, U) (Module.End Γ(X, U) Γ(M, X.basicOpen f)) f) := by
  rw [Module.End.isUnit_iff]
  -- by `moduleBasicOpen`, `f` acts through its restriction to `X.basicOpen f`, a unit there
  have : ⇑(algebraMap Γ(X, U) (Module.End Γ(X, U) Γ(M, X.basicOpen f)) f) =
      algebraMap Γ(X, X.basicOpen f) (Module.End Γ(X, X.basicOpen f) Γ(M, X.basicOpen f))
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) :=
    (rfl)
  rw [this, ← Module.End.isUnit_iff]
  exact (X.toRingedSpace.isUnit_res_basicOpen f).map _

/-- For an affine open `U`, the sections of an `𝒪_X`-module `M` over `U` are the global sections
of its restriction to the affine chart `Spec Γ(X, U) ⟶ X`, as `Γ(X, U)`-modules. Here
`Γ(X, U)` acts on the global sections of a module on `Spec Γ(X, U)` as their ring of
global functions. -/
def _root_.AlgebraicGeometry.Scheme.Modules.fromSpecSectionsEquiv (hU : IsAffineOpen U) :
    Γ(M, U) ≃ₗ[Γ(X, U)] Γ(M.restrict hU.fromSpec, ⊤) :=
  have h : hU.fromSpec ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  have : IsIso (homOfLE h.le) := homOfLE_isIso_of_eq _ h
  LinearEquiv.ofBijective
    { toFun := M.presheaf.map (homOfLE h.le).op ≫ (M.restrictAppIso hU.fromSpec ⊤).inv
      map_add' := map_add _
      -- Linearity is `presheaf_map_fromSpec_appIso_hom` at `⊤`.
      map_smul' r x := by
        rw [RingHom.id_apply, Scheme.Modules.smul_Spec_def, ConcreteCategory.comp_apply,
          M.map_smul, Scheme.Modules.smul_restrictAppIso_inv_apply,
          ← ConcreteCategory.comp_apply, hU.presheaf_map_fromSpec_appIso_hom ⊤]
        rfl }
    (ConcreteCategory.bijective_of_isIso
      (M.presheaf.map (homOfLE h.le).op ≫ (M.restrictAppIso hU.fromSpec ⊤).inv))

/-- The identification `Γ(M, U) ≃ Γ(M.restrict hU.fromSpec, ⊤)` is restriction of sections to
the image of the affine chart, which is `U`. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.fromSpecSectionsEquiv_apply (hU : IsAffineOpen U)
    (x : Γ(M, U)) :
    M.fromSpecSectionsEquiv hU x = (M.restrictAppIso hU.fromSpec ⊤).inv
      (M.presheaf.map (homOfLE (by
        rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec])).op x) :=
  (rfl)

/-- The affine-chart identification of sections commutes with maps of module sheaves. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.Hom.fromSpecSectionsEquiv_naturality
    {N : X.Modules} (f : M ⟶ N) (hU : IsAffineOpen U) (x : Γ(M, U)) :
    ((Scheme.Modules.restrictFunctor hU.fromSpec).map f).app ⊤
        (M.fromSpecSectionsEquiv hU x) =
      N.fromSpecSectionsEquiv hU (f.app U x) := by
  rw [Scheme.Modules.fromSpecSectionsEquiv_apply,
    Scheme.Modules.fromSpecSectionsEquiv_apply]
  -- The restriction functor and its section isomorphism only change scalar structures.
  -- Their underlying maps are the components of `f` on the image open.
  exact PresheafOfModules.naturality_apply f.val _ x

open Scheme.Modules in
/-- For an affine open `U`, the restriction of `M` to the affine chart `Spec Γ(X, U)` is
localizing in the sense of Mathlib's `AlgebraicGeometry.IsLocalizing` iff, for every
`f ∈ Γ(X, U)`, the restriction of sections of `M` from `U` to `X.basicOpen f` is a localization
at `f`. -/
private theorem isLocalizing_restrict_fromSpec_iff (hU : IsAffineOpen U) :
    IsLocalizing (modulesSpecToSheaf.obj (M.restrict hU.fromSpec)) ↔
      ∀ f : Γ(X, U), IsLocalizedModule.Away f (M.basicOpenRestrict f) := by
  refine forall_congr' fun f ↦ ?_
  -- Compare the restriction maps along the identifications of `U` and `X.basicOpen f` with the
  -- images of `⊤` and `D(f)` under `hU.fromSpec`.
  let N := M.restrict hU.fromSpec
  let D : (Spec Γ(X, U)).Opens := PrimeSpectrum.basicOpen f
  have h₁ : hU.fromSpec ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  have h₂ : hU.fromSpec ''ᵁ D = X.basicOpen f := hU.fromSpec_image_basicOpen f
  -- `e₁` identifies `Γ(M, U)` with `Γ(N, ⊤)`.
  let e₁ : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, ⊤) := (M.fromSpecSectionsEquiv hU).toLinearMap
  -- `e₂` identifies `Γ(N, D(f))` with `Γ(M, X.basicOpen f)`; its linearity is
  -- `presheaf_map_fromSpec_appIso_hom` at `D(f)`, followed by restriction to `X.basicOpen f`.
  let e₂ : Γ(N, D) →ₗ[Γ(X, U)] Γ(M, X.basicOpen f) :=
    { toFun := (M.restrictAppIso hU.fromSpec D).hom ≫ M.presheaf.map (homOfLE h₂.ge).op
      map_add' := map_add _
      map_smul' r x := by
        rw [RingHom.id_apply, smul_Spec_def, ConcreteCategory.comp_apply,
          smul_restrictAppIso_hom_apply, M.map_smul, ← algebraMap_smul Γ(X, X.basicOpen f) r]
        congr 1
        have hr : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map D.leTop.op ≫
            (hU.fromSpec.appIso D).inv ≫ X.presheaf.map (homOfLE h₂.ge).op =
            X.presheaf.map (homOfLE (X.basicOpen_le f)).op := by
          rw [← Category.assoc, ← Category.assoc, ← hU.presheaf_map_fromSpec_appIso_hom D]
          simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp]
          rfl
        have := ConcreteCategory.congr_hom hr r
        simp only [ConcreteCategory.comp_apply] at this
        exact this }
  -- The restriction map of `N`.
  let φ : Γ(N, ⊤) →ₗ[Γ(X, U)] Γ(N, D) :=
    { toFun := N.presheaf.map D.leTop.op
      map_add' := map_add _
      map_smul' r x := N.map_smul_Spec _ r x }
  -- The restriction map of `M` is `φ` transported along the bijections `e₁` and `e₂`.
  have he : M.basicOpenRestrict f = e₂ ∘ₗ φ ∘ₗ e₁ := by
    have h : M.presheaf.map (homOfLE (X.basicOpen_le f)).op =
        (M.presheaf.map (homOfLE h₁.le).op ≫ (M.restrictAppIso hU.fromSpec ⊤).inv) ≫
          (M.restrict hU.fromSpec).presheaf.map D.leTop.op ≫
            (M.restrictAppIso hU.fromSpec D).hom ≫ M.presheaf.map (homOfLE h₂.ge).op := by
      simp only [Category.assoc, map_restrictAppIso_hom_assoc, Iso.inv_hom_id_assoc,
        ← Functor.map_comp]
      rfl
    exact LinearMap.ext fun x ↦ ConcreteCategory.congr_hom h x
  have h₂iso : IsIso (M.presheaf.map (homOfLE h₂.ge).op) := by
    have : IsIso (homOfLE h₂.ge) := homOfLE_isIso_of_eq _ h₂.symm
    infer_instance
  have he₁ : Function.Bijective e₁ := (M.fromSpecSectionsEquiv hU).bijective
  have he₂ : Function.Bijective e₂ := ConcreteCategory.bijective_of_isIso
    ((M.restrictAppIso hU.fromSpec D).hom ≫ M.presheaf.map (homOfLE h₂.ge).op)
  have key : IsLocalizedModule.Away f (M.basicOpenRestrict f) ↔ IsLocalizedModule.Away f φ := by
    unfold IsLocalizedModule.Away
    rw [he, IsLocalizedModule.comp_iff_of_bijective_left,
      IsLocalizedModule.comp_iff_of_bijective_right]
    exacts [he₁, he₂]
  -- `φ` is the restriction map of `modulesSpecToSheaf.obj N` from `⊤` to `D(f)`
  exact key.symm

open Scheme.Modules in
/-- The sections of a quasi-coherent `𝒪_X`-module over the basic open `X.basicOpen f` of an
affine open `U` are the localization of its sections over `U` at the powers of `f`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict
    [M.IsQuasicoherent] (hU : IsAffineOpen U) (f : Γ(X, U)) :
    IsLocalizedModule.Away f (M.basicOpenRestrict f) :=
  (isLocalizing_restrict_fromSpec_iff M hU).1
    ((isIso_fromTildeΓ_iff_isLocalizing (M.restrict hU.fromSpec)).1 inferInstance) f

/-- **Quasi-coherence on an affine chart from localizations.** If, for an affine open `U`, the
sections of `M` over every basic open `X.basicOpen f` are the localization at `f` of the sections
over `U`, then the restriction of `M` to the affine chart `Spec Γ(X, U)` is quasi-coherent. This
is the converse of `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrict_fromSpec
    (hU : IsAffineOpen U) (h : ∀ f : Γ(X, U), IsLocalizedModule.Away f (M.basicOpenRestrict f)) :
    (M.restrict hU.fromSpec).IsQuasicoherent :=
  (isQuasicoherent_iff_isIso_fromTildeΓ _).2
    ((isIso_fromTildeΓ_iff_isLocalizing _).2 ((isLocalizing_restrict_fromSpec_iff M hU).2 h))

/-- **Quasi-coherence from localizations on an affine open cover.** An `𝒪_X`-module `M` is
quasi-coherent as soon as `X` is covered by affine opens `U i` such that, for every
`f ∈ Γ(X, U i)`, the sections of `M` over `X.basicOpen f` are the localization at `f` of the
sections over `U i`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocalizedModule
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
    (h : ∀ i (f : Γ(X, U i)), IsLocalizedModule.Away f (M.basicOpenRestrict f)) :
    M.IsQuasicoherent := by
  refine AlgebraicGeometry.isQuasicoherent_of_isQuasicoherent_restrict M U hcov fun i ↦ ?_
  have := M.isQuasicoherent_restrict_fromSpec (hU i) (h i)
  -- `U i` is isomorphic to the affine chart, through which `U.ι` factors
  have := Scheme.Modules.isQuasicoherent_restrictFunctor (hU i).isoSpec.hom
    (M.restrict (hU i).fromSpec)
  exact (SheafOfModules.isQuasicoherent (U i).toScheme.ringCatSheaf).prop_of_iso
    (((Scheme.Modules.restrictFunctorComp (hU i).isoSpec.hom (hU i).fromSpec).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (hU i).isoSpec_hom_fromSpec).app M) this

/-- An `𝒪_X`-module is quasi-coherent iff, for every affine open `U` and every `f ∈ Γ(X, U)`,
its sections over `X.basicOpen f` are the localization at `f` of its sections over `U`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_iff_isLocalizedModule :
    M.IsQuasicoherent ↔ ∀ U : X.Opens, IsAffineOpen U →
      ∀ f : Γ(X, U), IsLocalizedModule.Away f (M.basicOpenRestrict f) :=
  ⟨fun _ _ hU f ↦ M.isLocalizedModule_basicOpenRestrict hU f, fun h ↦
    M.isQuasicoherent_of_isLocalizedModule (fun U : X.affineOpens ↦ U.1) (fun U ↦ U.2)
      (iSup_affineOpens_eq_top X) fun U ↦ h U.1 U.2⟩

open Scheme.Modules in
/-- **Sections over a basic open extend after multiplication by a power of the function.** For a
quasi-coherent `𝒪_X`-module `M`, an affine open `U` and `f ∈ Γ(X, U)`, every section `x` of `M`
over the basic open `V = X.basicOpen f` has some `f ^ n • x` equal to the restriction of a
section over `U`. The open `V` is arbitrary up to the equality `X.basicOpen f = V`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_map [M.IsQuasicoherent]
    (hU : IsAffineOpen U) (f : Γ(X, U)) {V : X.Opens} (hV : X.basicOpen f = V) (hVU : V ≤ U)
    (x : Γ(M, V)) : ∃ (n : ℕ) (y : Γ(M, U)),
      X.presheaf.map (homOfLE hVU).op f ^ n • x = M.presheaf.map (homOfLE hVU).op y := by
  subst hV
  have := M.isLocalizedModule_basicOpenRestrict hU f
  obtain ⟨⟨y, _, n, rfl⟩, hy⟩ :=
    IsLocalizedModule.surj (Submonoid.powers f) (M.basicOpenRestrict f) x
  -- `f ^ n` acts on sections over `X.basicOpen f` through its restriction
  simp only [Submonoid.smul_def] at hy
  rw [← IsScalarTower.algebraMap_smul Γ(X, X.basicOpen f), map_pow,
    basicOpenRestrict_apply] at hy
  exact ⟨n, y, hy⟩

open Scheme.Modules in
/-- **Sections vanishing on a basic open are killed by a power of the function.** For a
quasi-coherent `𝒪_X`-module `M`, a quasi-compact open `U` and `f ∈ Γ(X, U)`, a section of `M`
over `U` whose restriction to `X.basicOpen f` vanishes is killed by a power of `f`. For the
structure sheaf this is
`AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_zero_of_isCompact
    [M.IsQuasicoherent] (hU : IsCompact (U : Set X)) (f : Γ(X, U)) (x : Γ(M, U))
    (hx : M.basicOpenRestrict f x = 0) : ∃ n : ℕ, f ^ n • x = 0 := by
  obtain ⟨s, _, hVU, hUV⟩ := X.exists_finite_affineOpens_cover hU
  cases nonempty_fintype s
  -- On each affine `V i ≤ U`, the restriction of `x` is killed by a power of `f`.
  have H (i : s) : ∃ n : ℕ, X.presheaf.map (homOfLE (hVU i)).op f ^ n •
      M.presheaf.map (homOfLE (hVU i)).op x = 0 := by
    have := M.isLocalizedModule_basicOpenRestrict i.1.2 (X.presheaf.map (homOfLE (hVU i)).op f)
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalizedModule.exists_of_eq
      (S := Submonoid.powers (X.presheaf.map (homOfLE (hVU i)).op f))
      (f := M.basicOpenRestrict _) (x₁ := M.presheaf.map (homOfLE (hVU i)).op x) (x₂ := 0) (by
        have hle : X.basicOpen (X.presheaf.map (homOfLE (hVU i)).op f) ≤ X.basicOpen f :=
          X.basicOpen_restrict (homOfLE (hVU i)) f
        simpa only [basicOpenRestrict_apply, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp,
          map_zero] using
          congrArg (M.presheaf.map (homOfLE hle).op) hx)
    exact ⟨n, by simpa [Submonoid.smul_def] using hn⟩
  choose n hn using H
  -- The largest of these powers kills `x` on every `V i`, hence on `U`.
  refine ⟨Finset.univ.sup n, TopCat.Sheaf.eq_of_locally_eq'
    (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X) (fun i : s ↦ (i.1 : X.Opens)) U
    (fun i ↦ homOfLE (hVU i)) hUV _ _ fun i ↦ ?_⟩
  -- The restriction maps of the sheaf `⟨M.presheaf, M.isSheaf⟩` are those of `M`.
  change M.presheaf.map _ _ = M.presheaf.map _ _
  rw [map_zero, M.map_smul, map_pow]
  exact pow_smul_eq_zero_of_le (Finset.le_sup (f := n) (Finset.mem_univ i)) (hn i)

open Scheme.Modules in
/-- Let the opens `V i ≤ U` cover `U`, with quasi-compact pairwise intersections. Sections `x i`
over the `V i` whose restrictions to the opens `V i ⊓ V j ⊓ X.basicOpen f` agree glue to a
section over `U` after multiplication by a power of `f`. -/
private lemma exists_pow_smul_eq_of_isCompact_inf [M.IsQuasicoherent] {ι : Type*} [Finite ι]
    (V : ι → X.Opens) (hVU : ∀ i, V i ≤ U) (hUV : U ≤ ⨆ i, V i)
    (hV : ∀ i j, IsCompact ((V i ⊓ V j : X.Opens) : Set X)) (f : Γ(X, U))
    (x : ∀ i, Γ(M, V i))
    (hx : ∀ i j, M.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
        V i ⊓ V j ⊓ X.basicOpen f ≤ V i)).op (x i) =
      M.presheaf.map (homOfLE (inf_le_left.trans inf_le_right :
        V i ⊓ V j ⊓ X.basicOpen f ≤ V j)).op (x j)) :
    ∃ (m : ℕ) (g : Γ(M, U)), ∀ i,
      M.presheaf.map (homOfLE (hVU i)).op g = X.presheaf.map (homOfLE (hVU i)).op f ^ m • x i := by
  cases nonempty_fintype ι
  have hWU (p : ι × ι) : V p.1 ⊓ V p.2 ≤ U := inf_le_left.trans (hVU p.1)
  -- The restrictions of `x i` and `x j` to `V i ⊓ V j` agree after multiplication by a power of
  -- `f`, since their difference vanishes on `X.basicOpen (f|V i ⊓ V j)`.
  have H (p : ι × ι) : ∃ m : ℕ, X.presheaf.map (homOfLE (hWU p)).op f ^ m •
      (M.presheaf.map (homOfLE inf_le_left).op (x p.1) -
        M.presheaf.map (homOfLE inf_le_right).op (x p.2)) = 0 := by
    refine M.exists_pow_smul_eq_zero_of_isCompact (hV p.1 p.2) _ _ ?_
    have hle : X.basicOpen (X.presheaf.map (homOfLE (hWU p)).op f) ≤
        V p.1 ⊓ V p.2 ⊓ X.basicOpen f := (X.basicOpen_res _ _).le
    simpa only [basicOpenRestrict_apply, map_sub, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp,
      sub_eq_zero] using
      congrArg (M.presheaf.map (homOfLE hle).op) (hx p.1 p.2)
  choose m hm using H
  -- After multiplication by the largest of these powers, the sections are compatible.
  let K := Finset.univ.sup m
  let z (i : ι) : Γ(M, V i) := X.presheaf.map (homOfLE (hVU i)).op f ^ K • x i
  have hc : TopCat.Presheaf.IsCompatible M.presheaf V z := by
    intro i j
    have h := pow_smul_eq_zero_of_le (Finset.le_sup (f := m) (Finset.mem_univ (i, j))) (hm (i, j))
    rw [smul_sub, sub_eq_zero] at h
    -- The inclusions of `V i ⊓ V j` in `V i` and `V j` are `homOfLE`.
    change M.presheaf.map (homOfLE inf_le_left).op _ = M.presheaf.map (homOfLE inf_le_right).op _
    simpa only [z, M.map_smul, map_pow, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp] using h
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X) V U (fun i ↦ homOfLE (hVU i)) hUV z
    hc
  exact ⟨K, g, hg⟩

open Scheme.Modules in
/-- For a quasi-coherent `𝒪_X`-module `M`, a quasi-compact quasi-separated open `U` and
`f ∈ Γ(X, U)`, every section of `M` over `X.basicOpen f` has some `f ^ n • y` equal to the
restriction of a section over `U`. -/
private theorem exists_pow_smul_eq_basicOpenRestrict [M.IsQuasicoherent]
    (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X)) (f : Γ(X, U))
    (y : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (x : Γ(M, U)), f ^ n • y = M.basicOpenRestrict f x := by
  obtain ⟨s, _, hVU, hUV⟩ := X.exists_finite_affineOpens_cover hU
  cases nonempty_fintype s
  have hDV (i : s) : (i.1 : X.Opens) ⊓ X.basicOpen f ≤ i.1 := inf_le_left
  have hDf (i : s) : (i.1 : X.Opens) ⊓ X.basicOpen f ≤ X.basicOpen f := inf_le_right
  -- On each affine `V i`, some `f ^ n i • y` extends to a section `x i`.
  have H (i : s) := M.exists_pow_smul_eq_map i.1.2 (X.presheaf.map (homOfLE (hVU i)).op f)
    (X.basicOpen_res _ _) (hDV i) (M.presheaf.map (homOfLE (hDf i)).op y)
  choose n x hx using H
  simp only [← Functor.map_comp_apply, ← op_comp, homOfLE_comp] at hx
  -- After multiplication by powers of `f`, the `x i` extend the same multiple `f ^ N • y`.
  let N := Finset.univ.sup n
  let x' (i : s) : Γ(M, i.1) := X.presheaf.map (homOfLE (hVU i)).op f ^ (N - n i) • x i
  have hx' (i : s) : M.presheaf.map (homOfLE (hDV i)).op (x' i) =
      X.presheaf.map (homOfLE ((hDV i).trans (hVU i))).op f ^ N •
        M.presheaf.map (homOfLE (hDf i)).op y := by
    simp only [x', M.map_smul, map_pow, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp]
    rw [← hx i, smul_smul, pow_sub_mul_pow _ (Finset.le_sup (f := n) (Finset.mem_univ i))]
  -- Since `U` is quasi-separated, the `x' i` glue after multiplication by a further power.
  obtain ⟨K, g, hg⟩ := exists_pow_smul_eq_of_isCompact_inf M (fun i : s ↦ (i.1 : X.Opens)) hVU
    hUV (fun i j ↦ hU' _ _ (hVU i) i.1.1.isOpen i.1.2.isCompact (hVU j) j.1.1.isOpen
      j.1.2.isCompact) f x' fun i j ↦ by
    have hi : (i.1 : X.Opens) ⊓ j.1 ⊓ X.basicOpen f ≤ (i.1 : X.Opens) ⊓ X.basicOpen f :=
      inf_le_inf_right _ inf_le_left
    have hj : (i.1 : X.Opens) ⊓ j.1 ⊓ X.basicOpen f ≤ (j.1 : X.Opens) ⊓ X.basicOpen f :=
      inf_le_inf_right _ inf_le_right
    -- Restrict `hx' i` and `hx' j` further to `V i ⊓ V j ⊓ X.basicOpen f`.
    have hi' := congrArg (M.presheaf.map (homOfLE hi).op) (hx' i)
    have hj' := congrArg (M.presheaf.map (homOfLE hj).op) (hx' j)
    simp only [M.map_smul, map_pow, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp] at hi' hj'
    rw [hi', hj']
  -- The glued section restricts to `f ^ (N + K) • y` on each `V i ⊓ X.basicOpen f`.
  refine ⟨N + K, g, TopCat.Sheaf.eq_of_locally_eq'
    (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (fun i : s ↦ (i.1 : X.Opens) ⊓ X.basicOpen f) (X.basicOpen f) (fun i ↦ homOfLE (hDf i))
    (by rw [← iSup_inf_eq]; exact le_inf ((X.basicOpen_le f).trans hUV) le_rfl) _ _
    fun i ↦ ?_⟩
  -- The restriction maps of the sheaf `⟨M.presheaf, M.isSheaf⟩` are those of `M`.
  change M.presheaf.map _ _ = M.presheaf.map _ _
  -- Restrict the gluing identity `hg i` further to `V i ⊓ X.basicOpen f`.
  have hg' := congrArg (M.presheaf.map (homOfLE (hDV i)).op) (hg i)
  rw [M.map_smul, hx', smul_smul] at hg'
  rw [basicOpenRestrict_apply, ← IsScalarTower.algebraMap_smul Γ(X, X.basicOpen f), M.map_smul]
  simpa only [map_pow, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp, ← pow_add, add_comm K,
    RingHom.algebraMap_toAlgebra] using hg'.symm

open Scheme.Modules in
/-- **The qcqs lemma for quasi-coherent modules.** The sections of a quasi-coherent
`𝒪_X`-module over the basic open `X.basicOpen f` of a quasi-compact quasi-separated open `U` are
the localization of its sections over `U` at the powers of `f`. This is the module counterpart of
`AlgebraicGeometry.isLocalization_basicOpen_of_qcqs`, and generalizes
`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict` from affine opens. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict_of_qcqs
    [M.IsQuasicoherent] (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X))
    (f : Γ(X, U)) : IsLocalizedModule.Away f (M.basicOpenRestrict f) where
  map_units := by
    rintro ⟨_, n, rfl⟩
    rw [map_pow]
    exact (M.isUnit_algebraMap_end_basicOpen f).pow n
  surj y := by
    obtain ⟨n, x, h⟩ := exists_pow_smul_eq_basicOpenRestrict M hU hU' f y
    exact ⟨⟨x, ⟨_, n, rfl⟩⟩, h⟩
  exists_of_eq {x₁ x₂} h := by
    obtain ⟨n, hn⟩ := M.exists_pow_smul_eq_zero_of_isCompact hU f (x₁ - x₂) (by
      rw [map_sub, h, sub_self])
    exact ⟨⟨_, n, rfl⟩, by simpa [Submonoid.smul_def, smul_sub, sub_eq_zero] using hn⟩

end

end TauCeti
