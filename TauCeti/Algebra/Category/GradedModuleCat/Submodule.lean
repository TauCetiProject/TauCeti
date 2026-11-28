/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Basic
public import TauCeti.Algebra.Module.GradedModule.Quotient

/-!
# Homogeneous submodules as graded modules

A homogeneous `A`-submodule `U` of a graded `𝒜`-module `M` inherits an internal grading whose
degree-`p` piece is `U ∩ Mₚ`, together with a compatible graded `A`-action. This file packages `U`
as an object `TauCeti.GradedModuleCat.submoduleObj M U hU` of `GradedModuleCat 𝒜`.

## Main definitions

* `TauCeti.GradedModuleCat.submoduleObj`: a homogeneous `A`-submodule packaged as a graded
  `𝒜`-module.
* `TauCeti.GradedModuleCat.submoduleι`: the canonical inclusion morphism `M.submoduleObj U hU ⟶ M`.
* `TauCeti.GradedModuleCat.submoduleCodRestrict`: the graded codomain restriction of a morphism
  whose values lie in `U`.

## Main results

* `TauCeti.GradedModuleCat.mem_submoduleObj_piece_iff`: degree-`p` membership in
  `M.submoduleObj U hU` is ambient degree-`p` membership in `M`.
* `TauCeti.GradedModuleCat.hom_submoduleι`: `(submoduleι M U hU).hom = U.subtype`.
* `TauCeti.GradedModuleCat.submoduleCodRestrict_comp_submoduleι`: composing the codomain
  restriction with `submoduleι` recovers the original morphism.
* `TauCeti.GradedModuleCat.mono_submoduleι` and
  `TauCeti.GradedModuleCat.eq_submoduleCodRestrict_of_comp_submoduleι`: monicity of `submoduleι`
  and uniqueness of the factorization through `M.submoduleObj U hU`.
-/

public section

namespace TauCeti.GradedModuleCat

open CategoryTheory

universe v uk uA

variable {k : Type uk} {A : Type uA} [CommRing k] [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

/-- A homogeneous `A`-submodule of a graded `𝒜`-module, packaged as a graded `𝒜`-module with the
induced internal grading. -/
noncomputable abbrev submoduleObj (M : GradedModuleCat.{v} 𝒜) (U : Submodule A M)
    (hU : _root_.DirectSum.SetLike.IsHomogeneous M.grading.piece U) : GradedModuleCat.{v} 𝒜 where
  carrier := U
  isAddCommGroup := Submodule.addCommGroup _
  isModule := Submodule.module _
  isModuleBase := Submodule.module' _
  grading := M.grading.submodule U hU
  gradedSMul := ⟨fun {_ _} _ _ ha hx ↦ by
    rw [InternalGrading.mem_submodule_piece] at hx ⊢
    exact SetLike.GradedSMul.smul_mem (B := M.grading.piece) ha hx⟩

/-- An element of a homogeneous submodule `M.submoduleObj U hU` has degree `p` exactly when its
underlying element has degree `p` in `M`. This is not a simp lemma:
`InternalGrading.submodule_piece` and `Submodule.mem_comap` already simplify its left side. -/
theorem mem_submoduleObj_piece_iff (M : GradedModuleCat.{v} 𝒜) (U : Submodule A M)
    (hU : _root_.DirectSum.SetLike.IsHomogeneous M.grading.piece U) {p : ℤ}
    {x : M.submoduleObj U hU} :
    x ∈ (M.submoduleObj U hU).grading.piece p ↔ x.val ∈ M.grading.piece p :=
  InternalGrading.mem_submodule_piece _ _ _

/-- The canonical inclusion morphism of a homogeneous submodule into the ambient graded module. -/
@[expose]
noncomputable def submoduleι (M : GradedModuleCat.{v} 𝒜) (U : Submodule A M)
    (hU : _root_.DirectSum.SetLike.IsHomogeneous M.grading.piece U) :
    M.submoduleObj U hU ⟶ M :=
  ofHom U.subtype (M.grading.isHomogeneous_subtype U hU)

/-- The underlying linear map of `submoduleι` is the submodule inclusion `U.subtype`. -/
@[simp]
theorem hom_submoduleι (M : GradedModuleCat.{v} 𝒜) (U : Submodule A M)
    (hU : _root_.DirectSum.SetLike.IsHomogeneous M.grading.piece U) :
    (submoduleι M U hU).hom = U.subtype :=
  rfl

/-- The inclusion `submoduleι` of a homogeneous submodule is a monomorphism in
`GradedModuleCat 𝒜`. -/
instance mono_submoduleι (M : GradedModuleCat.{v} 𝒜) (U : Submodule A M)
    (hU : _root_.DirectSum.SetLike.IsHomogeneous M.grading.piece U) :
    Mono (submoduleι M U hU) where
  right_cancellation _ _ hgh := hom_ext <| LinearMap.ext fun x ↦ Subtype.ext <|
    LinearMap.congr_fun (congrArg Hom.hom hgh) x

/-- Graded codomain restriction of a morphism `f : N ⟶ M` whose range lies in a homogeneous
submodule `U`. -/
@[expose]
noncomputable def submoduleCodRestrict {N M : GradedModuleCat.{v} 𝒜} (U : Submodule A M)
    (hU : _root_.DirectSum.SetLike.IsHomogeneous M.grading.piece U)
    (f : N ⟶ M) (hf : ∀ x, f.hom x ∈ U) :
    N ⟶ M.submoduleObj U hU :=
  ofHom (LinearMap.codRestrict U f.hom hf)
    (LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ by
      rw [add_zero, mem_submoduleObj_piece_iff]
      exact map_mem f hx)

/-- The underlying linear map of `submoduleCodRestrict` is `LinearMap.codRestrict`. -/
@[simp]
theorem hom_submoduleCodRestrict {N M : GradedModuleCat.{v} 𝒜} (U : Submodule A M)
    (hU : _root_.DirectSum.SetLike.IsHomogeneous M.grading.piece U)
    (f : N ⟶ M) (hf : ∀ x, f.hom x ∈ U) :
    (submoduleCodRestrict U hU f hf).hom = LinearMap.codRestrict U f.hom hf :=
  rfl

/-- Composing `submoduleCodRestrict` with the submodule inclusion `submoduleι` recovers `f`. -/
@[reassoc (attr := simp)]
theorem submoduleCodRestrict_comp_submoduleι {N M : GradedModuleCat.{v} 𝒜} (U : Submodule A M)
    (hU : _root_.DirectSum.SetLike.IsHomogeneous M.grading.piece U)
    (f : N ⟶ M) (hf : ∀ x, f.hom x ∈ U) :
    submoduleCodRestrict U hU f hf ≫ submoduleι M U hU = f :=
  hom_ext (by simp [LinearMap.subtype_comp_codRestrict])

/-- Any morphism into `M.submoduleObj U hU` whose composite with `submoduleι` is `f` equals
`submoduleCodRestrict U hU f hf`. -/
theorem eq_submoduleCodRestrict_of_comp_submoduleι {N M : GradedModuleCat.{v} 𝒜}
    (U : Submodule A M) (hU : _root_.DirectSum.SetLike.IsHomogeneous M.grading.piece U)
    {f : N ⟶ M} (hf : ∀ x, f.hom x ∈ U) {g : N ⟶ M.submoduleObj U hU}
    (hg : g ≫ submoduleι M U hU = f) :
    g = submoduleCodRestrict U hU f hf :=
  (cancel_mono (submoduleι M U hU)).mp
    (hg.trans (submoduleCodRestrict_comp_submoduleι U hU f hf).symm)

end TauCeti.GradedModuleCat
