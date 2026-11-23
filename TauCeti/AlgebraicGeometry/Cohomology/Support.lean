/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Module.Opens
public import TauCeti.Topology.Sheaves.SupportedCohomology

/-!
# Cohomology with supports on a scheme

Let `X` be a scheme, `M` a sheaf of `𝒪_X`-modules and `Z` a closed subset of `X`, with open
complement `U = X ∖ Z`. The global sections of `M` *supported in `Z`* are those whose restriction
to `U` vanishes, `Γ_Z(X, M) = ker(Γ(X, M) → Γ(U, M))`; they form a submodule over the ring
`Γ(X, 𝒪_X)` of global functions (`Scheme.Modules.sectionsWithSupport`). The cohomology of `M` with
supports in `Z` is `H^q_Z(X, M)` (`Scheme.Modules.cohomologyWithSupport`), the relative cohomology
`H^q(X, U; M)` of the underlying abelian sheaf, that is main's topological
`CategoryTheory.Sheaf.supportedH` on the whole space (Stacks, Section 20.21 (0A39)).

Global functions act on `H^q_Z(X, M)` through the maps induced by multiplication on `M`, as they do
on `H^q(X, M)` (`TauCeti.AlgebraicGeometry.Cohomology.Module.Basic`), so `H^q_Z(X, M)` is a
`Γ(X, 𝒪_X)`-module (`Scheme.Modules.cohomologyWithSupportModule`). In degree zero it is the module
of sections supported in `Z` (`Scheme.Modules.cohomologyWithSupportZeroLinearEquiv`); for `Z = ∅`
it vanishes (`Scheme.Modules.subsingleton_cohomologyWithSupport_bot`). The long exact sequence of
supports

`⋯ ⟶ H^q_Z(X, M) ⟶ H^q(X, M) ⟶ H^q(U, M) ⟶ H^{q+1}_Z(X, M) ⟶ ⋯`

is an exact sequence of `Γ(X, 𝒪_X)`-modules (Stacks, Lemma 20.34.5 (0G6Y)), with the cohomology of
the opens `X = ⊤` and `U = ⊤ ⊓ Zᶜ` written as `Scheme.Modules.cohomologyOn`.

## Main declarations

* `Scheme.Modules.sectionsWithSupport M Z`: the submodule `Γ_Z(X, M)` of `Γ(M, ⊤)`.
* `Scheme.Modules.cohomologyWithSupport M Z q`: the group `H^q_Z(X, M)`, with its module structure
  over global functions `Scheme.Modules.cohomologyWithSupportModule`.
* `Scheme.Modules.cohomologyWithSupportZeroLinearEquiv`: `H⁰_Z(X, M) ≃ₗ Γ_Z(X, M)`.
* `Scheme.Modules.cohomologyWithSupportToCohomologyOn`, `Scheme.Modules.cohomologyWithSupportδ`:
  the linear maps of the long exact sequence of supports, whose exactness is
  `Scheme.Modules.exact_cohomologyWithSupportToCohomologyOn_cohomologyOnResLinear`,
  `Scheme.Modules.exact_cohomologyOnResLinear_cohomologyWithSupportδ` and
  `Scheme.Modules.exact_cohomologyWithSupportδ_cohomologyWithSupportToCohomologyOn`.

## References

* [Stacks Project, Section 20.21](https://stacks.math.columbia.edu/tag/0A39)
* [Stacks Project, Lemma 20.34.5](https://stacks.math.columbia.edu/tag/0G6Y)
* A. Grothendieck, *Local cohomology*, Lecture Notes in Mathematics 41, §1.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Scheme.Modules Opposite

universe u

namespace TauCeti

namespace AlgebraicGeometry

noncomputable section

namespace Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) (Z : Closeds X)

/-- On global sections, multiplication by a global function `r` is the scalar action of `r`. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsSmul_app_top_apply (r : Γ(X, ⊤))
    (s : Γ(M, ⊤)) : (M.globalSectionsSmul r).app ⊤ s = r • s := by
  rw [globalSectionsSmul_app]
  have h : X.presheaf.map (⊤ : X.Opens).leTop.op r = r := by
    have hf : (⊤ : X.Opens).leTop.op = 𝟙 (op (⊤ : X.Opens)) := Subsingleton.elim _ _
    rw [hf]
    exact ConcreteCategory.congr_hom (X.presheaf.map_id _) r
  rw [h]
  exact M.smul_apply r s

/-- The global sections of `M` supported in the closed subset `Z`, those whose restriction to the
complement of `Z` vanishes, as a submodule over global functions. -/
def _root_.AlgebraicGeometry.Scheme.Modules.sectionsWithSupport : Submodule Γ(X, ⊤) Γ(M, ⊤) where
  __ := ((toSheaf X).obj M).supportedSections Z ⊤
  smul_mem' r s hs := by
    have := Sheaf.map_mem_supportedSections ((toSheaf X).map (M.globalSectionsSmul r)) hs
    rwa [← M.globalSectionsSmul_app_top_apply r s]

lemma _root_.AlgebraicGeometry.Scheme.Modules.mem_sectionsWithSupport_iff {s : Γ(M, ⊤)} :
    s ∈ M.sectionsWithSupport Z ↔ s ∈ ((toSheaf X).obj M).supportedSections Z ⊤ :=
  Iff.rfl

/-- The cohomology `H^q_Z(X, M)` of `M` with supports in the closed subset `Z`: the relative
cohomology `H^q(X, X ∖ Z; M)` of the underlying abelian sheaf
(`CategoryTheory.Sheaf.supportedH` on the whole space). -/
abbrev _root_.AlgebraicGeometry.Scheme.Modules.cohomologyWithSupport (q : ℕ) : Type u :=
  ((toSheaf X).obj M).supportedH Z ⊤ q

/-- The action of global functions on cohomology with supports, bundled as a ring homomorphism
into additive endomorphisms: `r` acts through the map induced by multiplication by `r` on `M`. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportAction (q : ℕ) :
    Γ(X, ⊤) →+* AddMonoid.End (M.cohomologyWithSupport Z q) where
  toFun r := (Abelian.Ext.mk₀ ((toSheaf X).map (M.globalSectionsSmul r))).postcomp _ (add_zero q)
  map_one' := by
    ext x
    change x.comp (Abelian.Ext.mk₀ ((toSheaf X).map (M.globalSectionsSmul 1))) (add_zero q) = x
    rw [globalSectionsSmul_one, CategoryTheory.Functor.map_id]
    exact Abelian.Ext.comp_mk₀_id x
  map_mul' r s := by
    ext x
    change x.comp (Abelian.Ext.mk₀ ((toSheaf X).map (M.globalSectionsSmul (r * s))))
        (add_zero q) =
      (x.comp (Abelian.Ext.mk₀ ((toSheaf X).map (M.globalSectionsSmul s))) (add_zero q)).comp
        (Abelian.Ext.mk₀ ((toSheaf X).map (M.globalSectionsSmul r))) (add_zero q)
    rw [Abelian.Ext.comp_assoc x _ _ (add_zero q) (add_zero 0) (by simp),
      Abelian.Ext.mk₀_comp_mk₀, globalSectionsSmul_mul, Functor.map_comp]
  map_zero' := by
    ext x
    change x.comp (Abelian.Ext.mk₀ ((toSheaf X).map (M.globalSectionsSmul 0))) (add_zero q) = 0
    rw [globalSectionsSmul_zero, Functor.map_zero, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]
  map_add' r s := by
    ext x
    change x.comp (Abelian.Ext.mk₀ ((toSheaf X).map (M.globalSectionsSmul (r + s)))) (add_zero q) =
      x.comp (Abelian.Ext.mk₀ ((toSheaf X).map (M.globalSectionsSmul r))) (add_zero q) +
        x.comp (Abelian.Ext.mk₀ ((toSheaf X).map (M.globalSectionsSmul s))) (add_zero q)
    rw [globalSectionsSmul_add, Functor.map_add, Abelian.Ext.mk₀_add, Abelian.Ext.comp_add]

/-- Cohomology with supports is a module over the ring of global functions. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportModule (q : ℕ) :
    Module Γ(X, ⊤) (M.cohomologyWithSupport Z q) :=
  Module.compHom _ (M.cohomologyWithSupportAction Z q)

/-- A global function `r` acts on `H^q_Z(X, M)` by postcomposition with multiplication by `r`. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyWithSupport_smul_def (q : ℕ)
    (r : Γ(X, ⊤)) (x : M.cohomologyWithSupport Z q) :
    r • x = x.comp (Abelian.Ext.mk₀ ((toSheaf X).map (M.globalSectionsSmul r))) (add_zero q) :=
  (rfl)

/-- In degree zero, cohomology with supports in `Z` is the module of global sections supported in
`Z`. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportZeroLinearEquiv :
    M.cohomologyWithSupport Z 0 ≃ₗ[Γ(X, ⊤)] M.sectionsWithSupport Z where
  toFun x := ⟨(((toSheaf X).obj M).supportedHZeroEquiv Z ⊤ x).val,
    (((toSheaf X).obj M).supportedHZeroEquiv Z ⊤ x).property⟩
  invFun s := (((toSheaf X).obj M).supportedHZeroEquiv Z ⊤).symm ⟨s.val, s.property⟩
  left_inv x := (((toSheaf X).obj M).supportedHZeroEquiv Z ⊤).symm_apply_apply x
  right_inv s := Subtype.ext (congrArg Subtype.val
    ((((toSheaf X).obj M).supportedHZeroEquiv Z ⊤).apply_symm_apply ⟨s.val, s.property⟩))
  map_add' x y := Subtype.ext (congrArg Subtype.val
    (map_add (((toSheaf X).obj M).supportedHZeroEquiv Z ⊤) x y))
  map_smul' r x := by
    ext
    simp only [RingHom.id_apply, SetLike.val_smul, cohomologyWithSupport_smul_def,
      Sheaf.coe_supportedHZeroEquiv_apply, Sheaf.relativeH'.coe_zeroEquiv_naturality_right]
    exact M.globalSectionsSmul_app_top_apply r _

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.coe_cohomologyWithSupportZeroLinearEquiv_apply
    (x : M.cohomologyWithSupport Z 0) :
    (M.cohomologyWithSupportZeroLinearEquiv Z x).val =
      (((toSheaf X).obj M).supportedHZeroEquiv Z ⊤ x).val :=
  (rfl)

/-- Cohomology with supports in the empty set vanishes. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.subsingleton_cohomologyWithSupport_bot
    (q : ℕ) : Subsingleton (M.cohomologyWithSupport ⊥ q) :=
  ((toSheaf X).obj M).subsingleton_supportedH_of_le_compl ⊥
    (fun x _ => show x ∉ ((⊥ : Closeds X) : Set X) by simp) q

section supportSequence

/-- The map `H^q_Z(X, M) ⟶ H^q(X, M)` of the long exact sequence of supports, forgetting the
support, as a linear map over global functions. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportToCohomologyOn (q : ℕ) :
    M.cohomologyWithSupport Z q →ₗ[Γ(X, ⊤)] cohomologyOn M q ⊤ where
  toFun := Sheaf.relativeH'.toH' ((toSheaf X).obj M) (Z.complInclusion ⊤) q
  map_add' := map_add _
  map_smul' r x := by
    apply (Sheaf.H'AddEquivExt ((toSheaf X).obj M) q ⊤).injective
    refine (Sheaf.relativeH'.H'AddEquivExt_toH' _ _ _).trans
      (Eq.trans ?_ (H'AddEquivExt_cohomologyOn_smul M q ⊤ r
        (Sheaf.relativeH'.toH' ((toSheaf X).obj M) (Z.complInclusion ⊤) q x)).symm)
    rw [Sheaf.relativeH'.H'AddEquivExt_toH', cohomologyWithSupport_smul_def]
    exact (Abelian.Ext.comp_assoc _ _ _ (zero_add q) (add_zero q) (by simp)).symm

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportToCohomologyOn_apply (q : ℕ)
    (x : M.cohomologyWithSupport Z q) :
    M.cohomologyWithSupportToCohomologyOn Z q x =
      Sheaf.relativeH'.toH' ((toSheaf X).obj M) (Z.complInclusion ⊤) q x :=
  (rfl)

/-- The connecting map `H^q(X ∖ Z, M) ⟶ H^{q+1}_Z(X, M)` of the long exact sequence of supports,
as a linear map over global functions. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportδ {q₀ q₁ : ℕ}
    (h : 1 + q₀ = q₁) :
    cohomologyOn M q₀ (⊤ ⊓ Z.compl) →ₗ[Γ(X, ⊤)] M.cohomologyWithSupport Z q₁ where
  toFun := Sheaf.relativeH'.δ ((toSheaf X).obj M) (Z.complInclusion ⊤) h
  map_add' := map_add _
  map_smul' r x := by
    change Sheaf.relativeH'.δ ((toSheaf X).obj M) (Z.complInclusion ⊤) h (r • x) =
      (Sheaf.relativeH'.δ ((toSheaf X).obj M) (Z.complInclusion ⊤) h x).comp
        (Abelian.Ext.mk₀ ((toSheaf X).map (M.globalSectionsSmul r))) (add_zero q₁)
    refine (Sheaf.relativeH'.δ_apply _ _ h _).trans ?_
    rw [H'AddEquivExt_cohomologyOn_smul]
    refine Eq.trans ?_ (congrArg (fun y => Abelian.Ext.comp y
      (Abelian.Ext.mk₀ ((toSheaf X).map (M.globalSectionsSmul r))) (add_zero q₁))
      (Sheaf.relativeH'.δ_apply ((toSheaf X).obj M) (Z.complInclusion ⊤) h x)).symm
    exact (Abelian.Ext.comp_assoc _ _ _ h (add_zero q₀) (by omega)).symm

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportδ_apply {q₀ q₁ : ℕ}
    (h : 1 + q₀ = q₁) (x : cohomologyOn M q₀ (⊤ ⊓ Z.compl)) :
    M.cohomologyWithSupportδ Z h x =
      Sheaf.relativeH'.δ ((toSheaf X).obj M) (Z.complInclusion ⊤) h x :=
  (rfl)

end supportSequence

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) (Z : Closeds X)

/-- The long exact sequence of supports is exact at `H^q(X, M)`: a class comes from cohomology
with supports in `Z` exactly when its restriction to `X ∖ Z` vanishes. -/
theorem exact_cohomologyWithSupportToCohomologyOn_cohomologyOnResLinear
    (q : ℕ) :
    Function.Exact (M.cohomologyWithSupportToCohomologyOn Z q)
      (cohomologyOnResLinear M q (inf_le_left : ⊤ ⊓ Z.compl ≤ ⊤)) := by
  have hres : ⇑(cohomologyOnResLinear M q (inf_le_left : ⊤ ⊓ Z.compl ≤ ⊤)) =
      cohomologyOnRes M q (inf_le_left : ⊤ ⊓ Z.compl ≤ ⊤) :=
    funext (cohomologyOnResLinear_apply M q _)
  rw [hres]
  exact Sheaf.relativeH'.exact_toH'_cohomologyPresheaf_map _ _ q

/-- The long exact sequence of supports is exact at `H^q(X ∖ Z, M)`: the kernel of the connecting
map consists of the restrictions of classes on `X`. -/
theorem exact_cohomologyOnResLinear_cohomologyWithSupportδ
    {q₀ q₁ : ℕ} (h : 1 + q₀ = q₁) :
    Function.Exact (cohomologyOnResLinear M q₀ (inf_le_left : ⊤ ⊓ Z.compl ≤ ⊤))
      (M.cohomologyWithSupportδ Z h) := by
  have hres : ⇑(cohomologyOnResLinear M q₀ (inf_le_left : ⊤ ⊓ Z.compl ≤ ⊤)) =
      cohomologyOnRes M q₀ (inf_le_left : ⊤ ⊓ Z.compl ≤ ⊤) :=
    funext (cohomologyOnResLinear_apply M q₀ _)
  rw [hres]
  exact Sheaf.relativeH'.exact_cohomologyPresheaf_map_δ _ _ h

/-- The long exact sequence of supports is exact at `H^{q+1}_Z(X, M)`. -/
theorem exact_cohomologyWithSupportδ_cohomologyWithSupportToCohomologyOn
    {q₀ q₁ : ℕ} (h : 1 + q₀ = q₁) :
    Function.Exact (M.cohomologyWithSupportδ Z h) (M.cohomologyWithSupportToCohomologyOn Z q₁) :=
  Sheaf.relativeH'.exact_δ_toH' _ _ h

end AlgebraicGeometry.Scheme.Modules
