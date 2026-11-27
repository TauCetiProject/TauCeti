/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
public import TauCeti.AlgebraicGeometry.Modules.Localization
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels

import Mathlib.Algebra.Module.LocalizedModule.Away

/-!
# Quasi-coherent submodules from submodules of sections over affine opens

Let `M` be a quasi-coherent `𝒪_X`-module on a scheme `X`. Suppose that for every affine open `U`
of `X` we are given a `Γ(X, U)`-submodule `N(U)` of the sections `Γ(M, U)`, compatibly with
restriction: for affine opens `V ≤ U`, the submodule `N(V)` is spanned over `Γ(X, V)` by the
restrictions of the elements of `N(U)`
(`AlgebraicGeometry.Scheme.Modules.AffineSubmoduleData`). Since restriction of sections of a
quasi-coherent module exhibits `Γ(M, V)` as the base change of `Γ(M, U)`, this says that `N(V)` is
the image of the base change of `N(U)`.

Such a family is the family of sections over affine opens of a unique quasi-coherent submodule `N`
of `M`: over an arbitrary open `W`, a section of `M` lies in `N` when its restriction to every
affine open inside `W` lies in the given submodule. Membership is local because the submodule over
a basic open `D(f)` of an affine open `U` is the localization at `f` of the submodule over `U`, so
a section over `U` whose restrictions to the members of a cover of `U` by basic opens lie in the
given submodules lies in `N(U)` after multiplication by a power of each `f`, hence in `N(U)`. The
same localization statement makes `N` quasi-coherent.

The cokernel `M ⟶ M / N` is then a quasi-coherent quotient of `M` whose sections over each affine
open `U` are `Γ(M, U) ⧸ N(U)`. This is how quotients of a quasi-coherent module with prescribed
kernels over affine opens are built, such as the universal quotient over a Grassmannian, where the
kernel over an affine open is the point of the Grassmannian that the open classifies.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.AffineSubmoduleData M`: submodules of the sections of `M` over
  the affine opens of `X`, compatible with restriction.
* `AlgebraicGeometry.Scheme.Modules.AffineSubmoduleData.sections D W`: the sections over an
  arbitrary open `W` of the submodule.
* `AlgebraicGeometry.Scheme.Modules.AffineSubmoduleData.sheaf D`: the submodule as an
  `𝒪_X`-module, with its inclusion `AffineSubmoduleData.ι D` into `M`.
* `AlgebraicGeometry.Scheme.Modules.AffineSubmoduleData.quotient D`: the quotient `M / N`, with its
  projection `AffineSubmoduleData.π D`.
* `AlgebraicGeometry.Scheme.Modules.AffineSubmoduleData.sectionsQuotientEquiv D U`: over an affine
  open `U`, the sections of the quotient are `Γ(M, U) ⧸ N(U)`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.AffineSubmoduleData.sections_eq`: over an affine open, the
  sections of the submodule are the given submodule.
* `AlgebraicGeometry.Scheme.Modules.AffineSubmoduleData.mem_submodule_of_span_eq_top`: membership
  in the given submodule over an affine open `U` can be checked on basic opens `D(f)` for `f`
  generating the unit ideal.
* `AlgebraicGeometry.Scheme.Modules.AffineSubmoduleData.isQuasicoherent_sheaf`: the submodule is
  quasi-coherent, and so is the quotient.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} (M : X.Modules)

/-- **Submodules of sections over affine opens, compatible with restriction.** For each affine
open `U` of `X`, a `Γ(X, U)`-submodule `N(U)` of the sections `Γ(M, U)`, such that for affine opens
`V ≤ U` the submodule `N(V)` is spanned over `Γ(X, V)` by the restrictions of the elements of
`N(U)`. For quasi-coherent `M` these are the sections over affine opens of a quasi-coherent
submodule of `M` (`AlgebraicGeometry.Scheme.Modules.AffineSubmoduleData.sheaf`). -/
structure AffineSubmoduleData where
  /-- The submodule of the sections over an affine open. -/
  submodule (U : X.affineOpens) : Submodule Γ(X, U) Γ(M, U)
  /-- Over affine opens `V ≤ U`, the submodule over `V` is spanned by the restrictions of the
  elements of the submodule over `U`. -/
  submodule_eq_span {U V : X.affineOpens} (h : (V : X.Opens) ≤ U) :
    submodule V = Submodule.span Γ(X, V) (M.presheaf.map (homOfLE h).op '' submodule U)

namespace AffineSubmoduleData

variable {M} (D : M.AffineSubmoduleData)

/-- The restriction of an element of the submodule over an affine open `U` to an affine open
`V ≤ U` lies in the submodule over `V`. -/
theorem map_mem_submodule {U V : X.affineOpens} (h : (V : X.Opens) ≤ U) {s : Γ(M, U)}
    (hs : s ∈ D.submodule U) : M.presheaf.map (homOfLE h).op s ∈ D.submodule V := by
  rw [D.submodule_eq_span h]
  exact Submodule.subset_span ⟨s, hs, rfl⟩

/-- The sections over an open `W` of the submodule: the sections of `M` over `W` whose restriction
to every affine open inside `W` lies in the given submodule. Over an affine open these are the
given submodule (`AlgebraicGeometry.Scheme.Modules.AffineSubmoduleData.sections_eq`). -/
def sections (W : X.Opens) : Submodule Γ(X, W) Γ(M, W) where
  carrier := {s | ∀ (V : X.affineOpens) (h : (V : X.Opens) ≤ W),
    M.presheaf.map (homOfLE h).op s ∈ D.submodule V}
  add_mem' {a b} ha hb V h := by
    rw [map_add]
    exact add_mem (ha V h) (hb V h)
  zero_mem' V h := by
    rw [map_zero]
    exact zero_mem _
  smul_mem' r s hs V h := by
    rw [map_smul]
    exact Submodule.smul_mem _ _ (hs V h)

/-- A section lies in the submodule over `W` when its restriction to every affine open inside `W`
lies in the given submodule. -/
theorem mem_sections_iff {W : X.Opens} {s : Γ(M, W)} :
    s ∈ D.sections W ↔ ∀ (V : X.affineOpens) (h : (V : X.Opens) ≤ W),
      M.presheaf.map (homOfLE h).op s ∈ D.submodule V :=
  Iff.rfl

/-- Sections of the submodule restrict to sections of the submodule. -/
theorem map_mem_sections {W W' : X.Opens} (i : W' ⟶ W) {s : Γ(M, W)} (hs : s ∈ D.sections W) :
    M.presheaf.map i.op s ∈ D.sections W' := by
  intro V h
  have := hs V (h.trans (leOfHom i))
  rwa [← ConcreteCategory.comp_apply, ← Functor.map_comp]

/-- **Over an affine open, the sections of the submodule are the given submodule.** -/
@[simp]
theorem sections_eq (U : X.affineOpens) : D.sections U = D.submodule U := by
  ext s
  refine ⟨fun hs ↦ ?_, fun hs V h ↦ D.map_mem_submodule h hs⟩
  have := hs U le_rfl
  rwa [show (homOfLE (le_refl (U : X.Opens))).op = 𝟙 (op (U : X.Opens)) from rfl,
    CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] at this

section Quasicoherent

variable [M.IsQuasicoherent]

/-- **Membership in the given submodule is local on basic opens.** A section of `M` over an affine
open `U` lies in the given submodule as soon as its restrictions to the basic opens `D(f)`, for `f`
in a set generating the unit ideal of `Γ(X, U)`, lie in the given submodules. -/
theorem mem_submodule_of_span_eq_top (U : X.affineOpens) {t : Set Γ(X, U)}
    (ht : Ideal.span t = ⊤) {s : Γ(M, U)}
    (hs : ∀ f ∈ t, M.presheaf.map (homOfLE (X.basicOpen_le f)).op s ∈
      D.submodule ⟨X.basicOpen f, U.property.basicOpen f⟩) :
    s ∈ D.submodule U := by
  have hU : IsAffineOpen (U : X.Opens) := U.property
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ t ht s fun ⟨f, hf⟩ ↦ ?_
  have := M.isLocalizedModule_basicOpenRestrict hU f
  have := hU.isLocalization_basicOpen f
  have h := hs f hf
  -- over `D(f)` the given submodule is the localization at `f` of the one over `U`
  have hloc : D.submodule ⟨X.basicOpen f, hU.basicOpen f⟩ =
      (D.submodule U).localized' Γ(X, X.basicOpen f) (Submonoid.powers f)
        (M.basicOpenRestrict f) := by
    rw [Submodule.localized'_eq_span, D.submodule_eq_span (U := U) (X.basicOpen_le f)]
    congr 1
    exact Set.image_congr fun x _ ↦ (M.basicOpenRestrict_apply f x).symm
  rw [hloc, Submodule.mem_localized'] at h
  obtain ⟨m, hm, ⟨_, n, rfl⟩, hmk⟩ := h
  -- `f ^ n • s` and `m` have the same image in the localization, so they agree after
  -- multiplication by a further power of `f`
  have heq : M.basicOpenRestrict f (f ^ n • s) = M.basicOpenRestrict f m := by
    rw [LinearMap.map_smul, M.basicOpenRestrict_apply, ← hmk]
    exact IsLocalizedModule.mk'_cancel' _ _ (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
  obtain ⟨⟨_, j, rfl⟩, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) heq
  refine ⟨j + n, ?_⟩
  rw [pow_add, mul_smul]
  exact (congrArg (· ∈ D.submodule U) hc).mpr (Submodule.smul_mem _ _ hm)

/-- **Membership in the submodule is local.** A section of `M` over `W` lies in the submodule as
soon as every point of `W` has an open neighbourhood inside `W` on which the restriction lies in
the submodule. -/
theorem mem_sections_of_forall_exists {W : X.Opens} {s : Γ(M, W)}
    (hs : ∀ x ∈ W, ∃ (V : X.Opens) (i : V ⟶ W), x ∈ V ∧ M.presheaf.map i.op s ∈ D.sections V) :
    s ∈ D.sections W := by
  intro V hVW
  -- the functions on `V` whose basic open lies in an open on which `s` lies in the submodule
  let t : Set Γ(X, V) := {f | ∃ (W' : X.Opens) (i : W' ⟶ W), X.basicOpen f ≤ W' ∧
    M.presheaf.map i.op s ∈ D.sections W'}
  have ht : Ideal.span t = ⊤ := by
    refine V.property.self_le_iSup_basicOpen_iff.mp fun x hxV ↦ ?_
    obtain ⟨W', i, hxW', hW'⟩ := hs x (hVW hxV)
    obtain ⟨f, hfW', hxf⟩ := V.property.exists_basicOpen_le ⟨x, hxW'⟩ hxV
    exact Opens.mem_iSup.mpr ⟨⟨f, W', i, hfW', hW'⟩, hxf⟩
  refine D.mem_submodule_of_span_eq_top V ht fun f ⟨W', i, hfW', hW'⟩ ↦ ?_
  have := hW' ⟨X.basicOpen f, V.property.basicOpen f⟩ hfW'
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp] at this ⊢
  convert this using 4

/-- The submodule of `M` whose sections over an open `W` are `D.sections W`. -/
@[expose]
def submoduleSheaf : SheafOfModules.Submodule M where
  obj W := D.sections W.unop
  map i _ hs := D.map_mem_sections i.unop hs
  isSheaf {W} s hs := D.mem_sections_of_forall_exists fun x hx ↦ by
    obtain ⟨V, i, hi, hxV⟩ := hs x hx
    exact ⟨V, i, hxV, hi⟩

/-- The component of the submodule at an open `W` is `D.sections W`. -/
@[simp]
theorem submoduleSheaf_obj (W : X.Opensᵒᵖ) :
    D.submoduleSheaf.toSubmodule.obj W = D.sections W.unop :=
  (rfl)

/-- The quasi-coherent submodule of `M` determined by `D`, as an `𝒪_X`-module. Its sections over
an affine open `U` are the given submodule `D.submodule U` (`AffineSubmoduleData.range_ι_app`). -/
@[expose]
def sheaf : X.Modules :=
  D.submoduleSheaf.toSheafOfModules

/-- The inclusion of the submodule determined by `D` into `M`. -/
@[expose]
def ι : D.sheaf ⟶ M :=
  D.submoduleSheaf.ι

instance : Mono D.ι :=
  SheafOfModules.Submodule.instMonoι D.submoduleSheaf

/-- The sections of the submodule over `W` are sections of `M` lying in `D.sections W`. -/
theorem ι_app_mem (W : X.Opens) (s : Γ(D.sheaf, W)) : D.ι.app W s ∈ D.sections W :=
  (show ↥(D.sections W) from s).property

/-- A section of `M` lying in `D.sections W`, as a section of the submodule over `W`. -/
def sectionMk {W : X.Opens} (s : Γ(M, W)) (hs : s ∈ D.sections W) : Γ(D.sheaf, W) :=
  (⟨s, hs⟩ : D.sections W)

/-- Including a section built from a section of `M` recovers that section. -/
@[simp]
theorem ι_app_sectionMk {W : X.Opens} (s : Γ(M, W)) (hs : s ∈ D.sections W) :
    D.ι.app W (D.sectionMk s hs) = s :=
  (rfl)

/-- Over every open `W`, the inclusion of the submodule is injective on sections. -/
theorem ι_app_injective (W : X.Opens) : Function.Injective (D.ι.app W) :=
  fun _ _ h ↦ Subtype.val_injective h

/-- Over an open `W`, the image of the inclusion of the submodule on sections is `D.sections W`. -/
theorem range_ι_app (W : X.Opens) :
    LinearMap.range ((sectionsFunctor W).map D.ι).hom = D.sections W := by
  ext s
  exact ⟨fun ⟨t, ht⟩ ↦ ht ▸ D.ι_app_mem W t, fun hs ↦ ⟨D.sectionMk s hs, rfl⟩⟩

/-- **The submodule determined by `D` is quasi-coherent**: over a basic open `D(f)` of an affine
open `U`, its sections are the localization at `f` of its sections over `U`, because the given
submodule over `D(f)` is spanned by the restrictions of the given submodule over `U` and
restriction of sections of `M` from `U` to `D(f)` is the localization at `f`. -/
instance isQuasicoherent_sheaf : D.sheaf.IsQuasicoherent := by
  refine D.sheaf.isQuasicoherent_iff_isLocalizedModule.2 fun U hU f ↦ ?_
  obtain ⟨U, rfl⟩ : ∃ U' : X.affineOpens, U'.val = U := ⟨⟨U, hU⟩, rfl⟩
  have := M.isLocalizedModule_basicOpenRestrict hU f
  refine .mk_of_addCommGroup (D.sheaf.isUnit_algebraMap_end_basicOpen f) (fun y ↦ ?_)
    fun x hx ↦ ?_
  · -- a section of the submodule over `D(f)` is a fraction `m / f ^ n` with `m` over `U`
    have hy : D.ι.app _ y ∈
        Submodule.span Γ(X, X.basicOpen f) (M.basicOpenRestrict f '' D.submodule U) := by
      have := (D.sections_eq ⟨X.basicOpen f, hU.basicOpen f⟩).le (D.ι_app_mem _ y)
      rw [D.submodule_eq_span (U := U) (X.basicOpen_le f)] at this
      convert this using 2
      exact Set.image_congr fun x _ ↦ M.basicOpenRestrict_apply f x
    have := hU.isLocalization_basicOpen f
    rw [← Submodule.localized'_eq_span Γ(X, X.basicOpen f) (Submonoid.powers f),
      Submodule.mem_localized'] at hy
    obtain ⟨m, hm, ⟨_, n, rfl⟩, hmk⟩ := hy
    refine ⟨n, D.sectionMk m ((D.sections_eq U).ge hm), D.ι_app_injective _ ?_⟩
    rw [Scheme.Modules.basicOpenRestrict_apply]
    change f ^ n • D.ι.app _ y = M.presheaf.map _ m
    rw [← M.basicOpenRestrict_apply, ← hmk]
    exact IsLocalizedModule.mk'_cancel' _ _ (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
  · -- a section of the submodule vanishing on `D(f)` is killed by a power of `f`
    have hx' : M.basicOpenRestrict f (D.ι.app U x) = M.basicOpenRestrict f 0 := by
      have := congrArg (D.ι.app _) hx
      rw [Scheme.Modules.basicOpenRestrict_apply, map_zero] at this
      rw [Scheme.Modules.basicOpenRestrict_apply, map_zero]
      exact this
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) hx'
    exact ⟨n, D.ι_app_injective _ (hn.trans (smul_zero _))⟩

/-- The quotient `M / N` of `M` by the quasi-coherent submodule `N` determined by `D`: the
cokernel of the inclusion `N ⟶ M`. Its sections over an affine open `U` are
`Γ(M, U) ⧸ D.submodule U` (`AffineSubmoduleData.sectionsQuotientEquiv`). -/
@[expose]
def quotient : X.Modules :=
  cokernel D.ι

/-- The projection `M ⟶ M / N` onto the quotient by the submodule determined by `D`. -/
@[expose]
def π : M ⟶ D.quotient :=
  cokernel.π D.ι

instance : Epi D.π :=
  inferInstanceAs (Epi (cokernel.π D.ι))

/-- The projection onto the quotient kills the submodule. -/
@[reassoc (attr := simp)]
theorem ι_π : D.ι ≫ D.π = 0 :=
  cokernel.condition D.ι

/-- The quotient by the submodule determined by `D` is quasi-coherent. -/
instance isQuasicoherent_quotient : D.quotient.IsQuasicoherent :=
  inferInstanceAs (cokernel D.ι).IsQuasicoherent

/-- **Sections of the quotient over an affine open.** Over an affine open `U`, the sections of the
quotient `M / N` are `Γ(M, U) ⧸ D.submodule U`, `Γ(X, U)`-linearly. -/
def sectionsQuotientEquiv (U : X.affineOpens) :
    Γ(D.quotient, U) ≃ₗ[Γ(X, U)] Γ(M, U) ⧸ D.submodule U :=
  sectionsCokernelEquiv D.ι U.property ≪≫ₗ
    Submodule.quotEquivOfEq _ _ ((D.range_ι_app U).trans (D.sections_eq U))

/-- Under `sectionsQuotientEquiv`, the projection onto the quotient is the quotient map. -/
@[simp]
theorem sectionsQuotientEquiv_π_app (U : X.affineOpens) (s : Γ(M, U)) :
    D.sectionsQuotientEquiv U (D.π.app U s) = Submodule.Quotient.mk s := by
  have h := sectionsCokernelEquiv_π_app D.ι U.property s
  exact (congrArg (Submodule.quotEquivOfEq _ _ ((D.range_ι_app U).trans (D.sections_eq U)))
    h).trans rfl

end Quasicoherent

end AffineSubmoduleData

end AlgebraicGeometry.Scheme.Modules

end
