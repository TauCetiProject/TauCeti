/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule

/-!
# The ideal sheaf as a sheaf of modules

Mathlib's `Scheme.IdealSheafData` records an ideal sheaf `I ⊆ 𝒪_X` through its ideals
`I(U) ⊆ Γ(X, U)` on the affine opens `U` only. This file turns it into an `𝒪_X`-submodule of the
structure sheaf. Over an arbitrary open `U`, its sections are the regular functions on `U` that
vanish on the closed subscheme `V(I)`, that is, the kernel of the restriction
`Γ(X, U) ⟶ Γ(V(I), U ∩ V(I))` along the closed immersion `I.subschemeι`. Over an affine open this
kernel is the ideal `I(U)` (Mathlib's `Scheme.IdealSheafData.ker_subschemeι_app`). Vanishing on
`V(I)` is a local condition, so these ideals form a submodule of the sheaf `𝒪_X`.

## Main declarations

* `Scheme.IdealSheafData.sections I U`: the ideal of sections of `I` over an open `U`, with
  `mem_sections_iff` and `sections_eq_ideal` describing it on arbitrary and on affine opens;
* `Scheme.IdealSheafData.submodule I`: the submodule `I ⊆ 𝒪_X` of the sheaf of modules `𝒪_X`;
* `Scheme.IdealSheafData.sheaf I`: the ideal sheaf as an `𝒪_X`-module, with its inclusion
  `Scheme.IdealSheafData.sheafι I : I ⟶ 𝒪_X`, which is injective on sections
  (`sheafι_app_injective`) with image `sections I U` over `U` (`range_sheafι_app`), and
  `Scheme.IdealSheafData.sectionMk` building a section of `I` from an element of `sections I U`;
* `Scheme.IdealSheafData.isIso_sheafι_top`: the unit ideal sheaf, which cuts out the empty closed
  subscheme, is the whole structure sheaf.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.9: the ideal sheaf of a closed subscheme
  is a quasi-coherent sheaf of ideals.
-/

public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The sections over an open `U` of the ideal sheaf `I`: the regular functions on `U` vanishing on
the closed subscheme cut out by `I`, i.e. the kernel of `Γ(X, U) ⟶ Γ(V(I), U ∩ V(I))`. Over an
affine open `U` this is the ideal `I.ideal U` (`sections_eq_ideal`). -/
def sections (U : X.Opens) : Ideal Γ(X, U) :=
  RingHom.ker (I.subschemeι.app U).hom

/-- A section lies in `I` exactly when it restricts to zero on the closed subscheme `V(I)`. -/
lemma mem_sections_iff {U : X.Opens} {s : Γ(X, U)} :
    s ∈ I.sections U ↔ I.subschemeι.app U s = 0 :=
  RingHom.mem_ker

/-- Over an affine open, the sections of the ideal sheaf are the ideal it records there. -/
@[simp]
lemma sections_eq_ideal (U : X.affineOpens) : I.sections U = I.ideal U :=
  I.ker_subschemeι_app U

/-- Sections of the ideal sheaf restrict to sections of the ideal sheaf. -/
lemma map_mem_sections {U V : X.Opens} (i : V ⟶ U) {s : Γ(X, U)} (hs : s ∈ I.sections U) :
    X.presheaf.map i.op s ∈ I.sections V := by
  rw [mem_sections_iff] at hs ⊢
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.naturality, ConcreteCategory.comp_apply, hs,
    map_zero]

/-- Membership in the ideal sheaf is local: a section whose restrictions to the members of an open
cover of `U` lie in `I` lies in `I`. -/
lemma mem_sections_of_forall_exists {U : X.Opens} {s : Γ(X, U)}
    (hs : ∀ x ∈ U, ∃ (V : X.Opens) (i : V ⟶ U), x ∈ V ∧ X.presheaf.map i.op s ∈ I.sections V) :
    s ∈ I.sections U := by
  rw [mem_sections_iff]
  refine I.subscheme.IsSheaf.section_ext fun z hz ↦ ?_
  obtain ⟨V, i, hxV, hV⟩ := hs (I.subschemeι z) hz
  refine ⟨I.subschemeι ⁻¹ᵁ V, I.subschemeι.preimage_mono i.le, hxV, ?_⟩
  rw [mem_sections_iff] at hV
  rw [map_zero, ← hV, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    Scheme.Hom.naturality]
  -- Both sides restrict along the inclusion `I.subschemeι ⁻¹ᵁ V ≤ I.subschemeι ⁻¹ᵁ U`; the two
  -- morphisms of opens agree since morphisms in a preorder are unique.
  rfl

/-- The ideal sheaf `I ⊆ 𝒪_X` as a submodule of the sheaf of modules `𝒪_X`. -/
def submodule : (SheafOfModules.unit X.ringCatSheaf).Submodule where
  obj U := I.sections U.unop
  map i _ hs := I.map_mem_sections i.unop hs
  isSheaf {U} s hs := I.mem_sections_of_forall_exists fun x hx ↦ by
    obtain ⟨V, i, hi, hxV⟩ := hs x hx
    exact ⟨V, i, hxV, hi⟩

/-- The component of the submodule `I ⊆ 𝒪_X` at an open is `sections I`. -/
@[simp]
lemma submodule_obj (U : X.Opensᵒᵖ) : I.submodule.toSubmodule.obj U = I.sections U.unop :=
  (rfl)

/-- The ideal sheaf `I ⊆ 𝒪_X` as an `𝒪_X`-module. -/
def sheaf : X.Modules :=
  I.submodule.toSheafOfModules

/-- The inclusion `I ⟶ 𝒪_X` of the ideal sheaf into the structure sheaf. -/
def sheafι : I.sheaf ⟶ SheafOfModules.unit X.ringCatSheaf :=
  I.submodule.ι

instance : Mono I.sheafι :=
  SheafOfModules.Submodule.instMonoι I.submodule

/-- A regular function lying in `sections I U`, as a section of the ideal sheaf over `U`. -/
def sectionMk {U : X.Opens} (s : Γ(X, U)) (hs : s ∈ I.sections U) : Γ(I.sheaf, U) :=
  ⟨s, hs⟩

/-- Including a section built from a regular function recovers that function. -/
@[simp]
lemma sheafι_app_sectionMk {U : X.Opens} (s : Γ(X, U)) (hs : s ∈ I.sections U) :
    Scheme.Modules.Hom.app I.sheafι U (I.sectionMk s hs) = s :=
  (rfl)

/-- The inclusion `I ⟶ 𝒪_X` commutes with restriction to a smaller open. -/
@[simp]
lemma sheafι_app_map {U V : X.Opens} (i : V ⟶ U) (t : Γ(I.sheaf, U)) :
    Scheme.Modules.Hom.app I.sheafι V (I.sheaf.presheaf.map i.op t) =
      X.presheaf.map i.op (Scheme.Modules.Hom.app I.sheafι U t) :=
  (rfl)

/-- The inclusion `I ⟶ 𝒪_X` sends a section of the ideal sheaf over `U` into `sections I U`. -/
lemma sheafι_app_mem (U : X.Opens) (t : Γ(I.sheaf, U)) :
    Scheme.Modules.Hom.app I.sheafι U t ∈ I.sections U :=
  t.2

/-- The inclusion of the ideal sheaf into `𝒪_X` is injective on sections. -/
lemma sheafι_app_injective (U : X.Opens) : Function.Injective (Scheme.Modules.Hom.app I.sheafι U) :=
  Subtype.val_injective

/-- The image of the sections of the ideal sheaf in `Γ(X, U)` is `sections I U`. -/
@[simp]
lemma range_sheafι_app (U : X.Opens) :
    Set.range (Scheme.Modules.Hom.app I.sheafι U) = (I.sections U : Set Γ(X, U)) := by
  ext s
  exact ⟨fun ⟨t, ht⟩ ↦ ht ▸ I.sheafι_app_mem U t, fun hs ↦ ⟨I.sectionMk s hs, rfl⟩⟩

/-- Every regular function is a section of the unit ideal sheaf, which cuts out the empty closed
subscheme. -/
@[simp]
lemma sections_top (U : X.Opens) : (⊤ : X.IdealSheafData).sections U = ⊤ :=
  -- The closed subscheme cut out by `⊤` is empty, so its rings of sections are zero.
  eq_top_iff.mpr fun _ _ ↦ (mem_sections_iff _).mpr (Subsingleton.elim _ _)

/-- The inclusion of the unit ideal sheaf into `𝒪_X` is an isomorphism. -/
instance isIso_sheafι_top : IsIso (⊤ : X.IdealSheafData).sheafι := by
  refine Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun U ↦ ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨sheafι_app_injective _ U, fun s ↦ ⟨sectionMk _ s ?_, rfl⟩⟩
  rw [sections_top]
  exact Submodule.mem_top

end

end AlgebraicGeometry.Scheme.IdealSheafData
