/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.PrimaryComponent
public import TauCeti.AlgebraicGeometry.AffineScheme.Basic
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic
public import TauCeti.Topology.Sheaves.SupportedCohomology.Sections
import TauCeti.Algebra.Module.Torsion.PrimaryComponent

/-!
# Degree-zero supported sheaf cohomology on an affine scheme

For a ring `R`, ideal `I`, and `R`-module `M`, a global section `m ∈ M ≅ Γ(Spec R, M~)` restricts
to zero on `Spec R \ V(I)` iff every `f ∈ I` annihilates `m` at some power
(`tilde_toOpen_top_mem_supportedSubmodule_iff`). When `I` is finitely generated, this holds iff
`m ∈ I.primaryComponent M`, yielding `primaryComponentEquivSupportedSubmoduleTop` and
`tildeCompSupportedSubmoduleSectionsTopIso`.

## Main definitions

* `TauCeti.AlgebraicGeometry.primaryComponentEquivSupportedSubmoduleTop`: the `R`-linear
  equivalence `I.primaryComponent M ≃ₗ[R] Γ_{V(I)}(Spec R, M~)` for finitely generated `I`.
* `TauCeti.AlgebraicGeometry.tildeCompSupportedSubmoduleSectionsTopIso`: the degree-zero natural
  isomorphism `M ↦ Γ_{V(I)}(Spec R, M~) ≅ Γ_I(M)` for finitely generated `I`.

## Main results

* `TauCeti.AlgebraicGeometry.tilde_toOpen_top_mem_supportedSubmodule_iff`: membership of
  `tilde.toOpen M ⊤ m` in `Γ_{V(s)}(Spec R, M~)` is power-annihilation by every `f ∈ s`.
* `TauCeti.AlgebraicGeometry.tilde_toOpen_top_mem_supportedSubmodule_iff_mem_primaryComponent`: for
  finitely generated `I`, membership in `Γ_{V(I)}(Spec R, M~)` is membership in
  `I.primaryComponent M`.

## References

* [The Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
* A. Grothendieck, *Local Cohomology*, Lecture Notes in Mathematics 41, Proposition 2.2.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

open PrimeSpectrum CategoryTheory.Sheaf

section DegreeZero

variable {R : CommRingCat.{u}}

/-- For any set `s ⊆ R` and element `m : M`, the global section `tilde.toOpen M ⊤ m` of `M~` is
supported in `V(s)` if and only if every `f ∈ s` annihilates `m` at some power. -/
theorem tilde_toOpen_top_mem_supportedSubmodule_iff (s : Set R) (M : ModuleCat.{u} R) (m : M) :
    tilde.toOpen M ⊤ m ∈
        (modulesSpecToSheaf.obj (tilde M)).supportedSubmodule
          (Spec.zeroLocusClosed (R := R) s) ⊤ ↔
      ∀ f ∈ s, ∃ n : ℕ, f ^ n • m = 0 := by
  let Z : Closeds (Spec R) := Spec.zeroLocusClosed s
  let F := modulesSpecToSheaf.obj (tilde M)
  rw [F.mem_supportedSubmodule_iff]
  have hres : F.obj.map (Z.complInclusion ⊤).op (tilde.toOpen M ⊤ m) =
      tilde.toOpen M (⊤ ⊓ Z.compl) m :=
    ConcreteCategory.congr_hom (tilde.toOpen_res M ⊤ (⊤ ⊓ Z.compl) (Z.complInclusion ⊤)) m
  let U (f : s) : Opens (Spec R) := basicOpen f.val
  have hU : (⊤ ⊓ Z.compl : Opens (Spec R)) = ⨆ f ∈ s, (basicOpen f : Opens (Spec R)) := by
    rw [top_inf_eq]; exact Spec.compl_zeroLocusClosed_eq_iSup_basicOpen s
  have hle (f : s) : U f ≤ ⊤ ⊓ Z.compl :=
    hU ▸ le_iSup₂ (f := fun f (_ : f ∈ s) ↦ (basicOpen f : Opens (Spec R))) f.val f.property
  have hresf (f : s) : F.obj.map (homOfLE (hle f)).op (tilde.toOpen M (⊤ ⊓ Z.compl) m) =
      tilde.toOpen M (U f) m :=
    ConcreteCategory.congr_hom (tilde.toOpen_res M (⊤ ⊓ Z.compl) (U f) (homOfLE (hle f))) m
  rw [hres]
  refine ⟨fun hm f hf ↦ ?_, fun hm ↦ ?_⟩
  · obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (.powers f)
      (tilde.toOpen M (basicOpen f)).hom).mp (by rw [← hresf ⟨f, hf⟩, hm, map_zero])
    exact ⟨n, hn⟩
  · apply TopCat.Sheaf.eq_of_locally_eq' F U (⊤ ⊓ Z.compl) (fun f ↦ homOfLE (hle f))
    · rw [hU]; exact iSup₂_le fun f hf ↦ le_iSup U ⟨f, hf⟩
    · intro f; obtain ⟨n, hn⟩ := hm f.val f.property; rw [map_zero, hresf f]
      exact (IsLocalizedModule.eq_zero_iff (.powers f.val)
        (tilde.toOpen M (basicOpen f.val)).hom).mpr ⟨⟨_, n, rfl⟩, hn⟩

/-- For a finitely generated ideal `I` of `R`, the global section `tilde.toOpen M ⊤ m` is
supported in `V(I)` if and only if `m ∈ I.primaryComponent M`. -/
theorem tilde_toOpen_top_mem_supportedSubmodule_iff_mem_primaryComponent
    {I : Ideal R} (hI : I.FG) (M : ModuleCat.{u} R) (m : M) :
    tilde.toOpen M ⊤ m ∈
        (modulesSpecToSheaf.obj (tilde M)).supportedSubmodule
          (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤ ↔
      m ∈ I.primaryComponent M := by
  obtain ⟨G, hG⟩ := hI
  rw [show Spec.zeroLocusClosed (R := R) (I : Set R) = Spec.zeroLocusClosed (G : Set R) by
    rw [← hG, Spec.zeroLocusClosed_span], tilde_toOpen_top_mem_supportedSubmodule_iff,
    ← hG, Ideal.mem_primaryComponent_span_iff]; rfl

/-- For a finitely generated ideal `I`, the `I`-primary component `Γ_I(M)` is `R`-linearly
equivalent to the global sections of `M~` supported in `V(I)`. -/
def primaryComponentEquivSupportedSubmoduleTop {I : Ideal R} (hI : I.FG) (M : ModuleCat.{u} R) :
    I.primaryComponent M ≃ₗ[R]
      (modulesSpecToSheaf.obj (tilde M)).supportedSubmodule
        (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤ :=
  let e := (tilde.isoTop M).toLinearEquiv
  let S := (modulesSpecToSheaf.obj (tilde M)).supportedSubmodule
    (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤
  (LinearEquiv.ofEq (I.primaryComponent M) (S.comap e.toLinearMap) (Submodule.ext fun m ↦
    (tilde_toOpen_top_mem_supportedSubmodule_iff_mem_primaryComponent hI M m).symm)).trans
    (e.ofSubmodule' S)

/-- Under `primaryComponentEquivSupportedSubmoduleTop`, an element `m` maps to the global section
`tilde.toOpen M ⊤ m`. -/
@[simp]
lemma coe_primaryComponentEquivSupportedSubmoduleTop_apply
    {I : Ideal R} (hI : I.FG) (M : ModuleCat.{u} R) (m : I.primaryComponent M) :
    (primaryComponentEquivSupportedSubmoduleTop hI M m :
        (modulesSpecToSheaf.obj (tilde M)).obj.obj (op ⊤)) = tilde.toOpen M ⊤ m.val := (rfl)

private def primaryComponentEquivSupportedSubmoduleTopIso
    {I : Ideal R} (hI : I.FG) (M : ModuleCat.{u} R) :
    ModuleCat.of R (I.primaryComponent M) ≅
      (tildeSheafFunctor R ⋙
        supportedSubmoduleSectionsFunctor (R := R)
          (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤).obj M :=
  (primaryComponentEquivSupportedSubmoduleTop hI M).toModuleIso

private def primaryComponentIsoSupportedSubmoduleTop
    {I : Ideal R} (hI : I.FG) (M : ModuleCat.{u} R) :
    I.primaryComponentFunctor.obj M ≅
      (tildeSheafFunctor R ⋙
        supportedSubmoduleSectionsFunctor (R := R)
          (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤).obj M :=
  I.primaryComponentFunctorObjIso M ≪≫ primaryComponentEquivSupportedSubmoduleTopIso hI M

private lemma primaryComponentIsoSupportedSubmoduleTop_hom_comp_ι
    {I : Ideal R} (hI : I.FG) (M : ModuleCat.{u} R) :
    (primaryComponentIsoSupportedSubmoduleTop hI M).hom ≫
        (((tildeSheafFunctor R).obj M).supportedSubmoduleι
          (Spec.zeroLocusClosed (R := R) (I : Set R))).hom.app (op ⊤) =
      I.primaryComponentFunctorι.app M ≫ tilde.toOpen M ⊤ := by
  have he : (primaryComponentEquivSupportedSubmoduleTopIso hI M).hom ≫
      (((tildeSheafFunctor R).obj M).supportedSubmoduleι
        (Spec.zeroLocusClosed (R := R) (I : Set R))).hom.app (op ⊤) =
      ModuleCat.ofHom (I.primaryComponent M).subtype ≫ tilde.toOpen M ⊤ := by
    ext m; exact (((tildeSheafFunctor R).obj M).supportedSubmoduleι_hom_app_apply _ (op ⊤)
      (primaryComponentEquivSupportedSubmoduleTop hI M m)).trans
      (coe_primaryComponentEquivSupportedSubmoduleTop_apply hI M m)
  have hcomp : (primaryComponentIsoSupportedSubmoduleTop hI M).hom =
      (I.primaryComponentFunctorObjIso M).hom ≫
        (primaryComponentEquivSupportedSubmoduleTopIso hI M).hom := rfl
  rw [hcomp, Category.assoc, he]
  exact I.primaryComponentFunctorObjIso_hom_comp_subtype_assoc M (tilde.toOpen M ⊤)

/-- For a finitely generated ideal `I` of `R`, `M ↦ Γ_{V(I)}(Spec R, M~)` is naturally isomorphic
to the `I`-power torsion functor `I.primaryComponentFunctor`. -/
def tildeCompSupportedSubmoduleSectionsTopIso {I : Ideal R} (hI : I.FG) :
    tildeSheafFunctor R ⋙
        supportedSubmoduleSectionsFunctor (R := R)
          (Spec.zeroLocusClosed (R := R) (I : Set R)) ⊤ ≅
      I.primaryComponentFunctor :=
  (NatIso.ofComponents (primaryComponentIsoSupportedSubmoduleTop hI) fun {M N} f ↦ by
    refine (cancel_mono
      ((((tildeSheafFunctor R).obj N).supportedSubmoduleι
        (Spec.zeroLocusClosed (R := R) (I : Set R))).hom.app (op ⊤))).1 ?_
    have hcomm : I.primaryComponentFunctor.map f ≫ I.primaryComponentFunctorι.app N ≫
        tilde.toOpen N ⊤ =
      I.primaryComponentFunctorι.app M ≫ tilde.toOpen M ⊤ ≫
        (modulesSpecToSheaf.map (tilde.map f)).hom.app (op ⊤) := by
      rw [← Category.assoc, I.primaryComponentFunctorι.naturality, Functor.id_map, Category.assoc]
      exact (congrArg (I.primaryComponentFunctorι.app M ≫ ·)
        (tilde.toOpen_map_app f ⊤).symm).trans (Category.assoc _ _ _).symm
    simp only [Category.assoc]
    rw [Functor.comp_map, supportedSubmoduleSectionsFunctor_map_ι_hom_app,
      ← Category.assoc (primaryComponentIsoSupportedSubmoduleTop hI M).hom,
      primaryComponentIsoSupportedSubmoduleTop_hom_comp_ι hI M,
      primaryComponentIsoSupportedSubmoduleTop_hom_comp_ι hI N,
      tildeSheafFunctor_map]
    exact hcomm).symm

/-- Under the inverse of `tildeCompSupportedSubmoduleSectionsTopIso`, the inclusion of supported
global sections of `M~` agrees with `I.primaryComponentFunctorι` followed by `tilde.toOpen`. -/
@[reassoc (attr := simp)]
lemma tildeCompSupportedSubmoduleSectionsTopIso_inv_app_comp_supportedSubmoduleι
    {I : Ideal R} (hI : I.FG) (M : ModuleCat.{u} R) :
    (tildeCompSupportedSubmoduleSectionsTopIso hI).inv.app M ≫
        ((modulesSpecToSheaf.obj ((tilde.functor R).obj M)).supportedSubmoduleι
          (Spec.zeroLocusClosed (R := R) (I : Set R))).hom.app (op ⊤) =
      I.primaryComponentFunctorι.app M ≫ tilde.toOpen M ⊤ :=
  primaryComponentIsoSupportedSubmoduleTop_hom_comp_ι hI M

end DegreeZero

end TauCeti.AlgebraicGeometry
