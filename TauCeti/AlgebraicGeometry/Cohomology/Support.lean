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
supports in `Z` on an open `W` is `H^q_Z(W, M)` (`Scheme.Modules.cohomologyWithSupport`), the
relative cohomology `H^q(W, W ∖ Z; M)` of the underlying abelian sheaf, that is the topological
`CategoryTheory.Sheaf.supportedH` (Stacks, Tag 0A39); `W = ⊤` gives `H^q_Z(X, M)`.

Global functions act on `H^q_Z(W, M)` through the maps induced by multiplication on `M`, as they do
on `H^q(W, M)` (`TauCeti.AlgebraicGeometry.Cohomology.Module.Basic`), so `H^q_Z(W, M)` is a
`Γ(X, 𝒪_X)`-module (`Scheme.Modules.cohomologyWithSupportModule`). In degree zero and for
`W = ⊤` it is the module of global sections supported in `Z`
(`Scheme.Modules.cohomologyWithSupportZeroLinearEquiv`); it vanishes when `W` does not meet `Z`
(`Scheme.Modules.subsingleton_cohomologyWithSupport_of_le_compl`), in particular for `Z = ∅`, and
it is `H^q(W, M)` when `W ⊆ Z` (`Scheme.Modules.cohomologyWithSupportLinearEquivOfSubset`), in
particular for `Z = X`. The long exact sequence of supports

`⋯ ⟶ H^q_Z(W, M) ⟶ H^q(W, M) ⟶ H^q(W ∖ Z, M) ⟶ H^{q+1}_Z(W, M) ⟶ ⋯`

is an exact sequence of `Γ(X, 𝒪_X)`-modules (Stacks, Tag 0G6Y), with the cohomology of the opens
`W` and `W ∖ Z = W ⊓ Zᶜ` written as `Scheme.Modules.cohomologyOn`.

## Main declarations

* `Scheme.Modules.sectionsWithSupport M Z`: the submodule `Γ_Z(X, M)` of `Γ(M, ⊤)`.
* `Scheme.Modules.cohomologyWithSupport M Z W q`: the group `H^q_Z(W, M)`, with its module structure
  over global functions `Scheme.Modules.cohomologyWithSupportModule`.
* `Scheme.Modules.cohomologyWithSupportZeroLinearEquiv`: `H⁰_Z(X, M) ≃ₗ Γ_Z(X, M)`.
* `Scheme.Modules.subsingleton_cohomologyWithSupport_of_le_compl`: `H^q_Z(W, M) = 0` when
  `W ∩ Z = ∅`.
* `Scheme.Modules.cohomologyWithSupportLinearEquivOfSubset`: `H^q_Z(W, M) ≃ₗ H^q(W, M)` when
  `W ⊆ Z`, for instance `H^q_X(W, M) ≃ₗ H^q(W, M)`.
* `Scheme.Modules.cohomologyWithSupportToCohomologyOn`, `Scheme.Modules.cohomologyWithSupportδ`:
  the linear maps of the long exact sequence of supports, whose exactness is
  `Scheme.Modules.exact_cohomologyWithSupportToCohomologyOn_cohomologyOnResLinear`,
  `Scheme.Modules.exact_cohomologyOnResLinear_cohomologyWithSupportδ` and
  `Scheme.Modules.exact_cohomologyWithSupportδ_cohomologyWithSupportToCohomologyOn`.

## References

* [Stacks Project, Tag 0A39](https://stacks.math.columbia.edu/tag/0A39)
* [Stacks Project, Tag 0G6Y](https://stacks.math.columbia.edu/tag/0G6Y)
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

/-- The global sections of `M` supported in the closed subset `Z`, those whose restriction to the
complement of `Z` vanishes, as a submodule over global functions. -/
def _root_.AlgebraicGeometry.Scheme.Modules.sectionsWithSupport : Submodule Γ(X, ⊤) Γ(M, ⊤) where
  __ := ((toSheaf X).obj M).supportedSections Z ⊤
  smul_mem' r s hs := by
    have := Sheaf.map_mem_supportedSections ((toSheaf X).map (M.globalSectionsSmul r)) hs
    rwa [← M.globalSectionsSmul_app_top_apply r s]

/-- A global section is supported in `Z` exactly when its restriction to the complement of `Z`
vanishes. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.mem_sectionsWithSupport_iff {s : Γ(M, ⊤)} :
    s ∈ M.sectionsWithSupport Z ↔ ((toSheaf X).obj M).obj.map (Z.complInclusion ⊤).op s = 0 :=
  Sheaf.mem_supportedSections_iff _

variable (W : X.Opens)

/-- The cohomology `H^q_Z(W, M)` of `M` on the open `W` with supports in the closed subset `Z`:
the relative cohomology `H^q(W, W ∖ Z; M)` of the underlying abelian sheaf
(`CategoryTheory.Sheaf.supportedH`). For `W = ⊤` it is `H^q_Z(X, M)`. -/
abbrev _root_.AlgebraicGeometry.Scheme.Modules.cohomologyWithSupport (q : ℕ) : Type u :=
  ((toSheaf X).obj M).supportedH Z W q

/-- The action of global functions on cohomology with supports, bundled as a ring homomorphism
into additive endomorphisms: `r` acts through the map induced by multiplication by `r` on `M`. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportAction (q : ℕ) :
    Γ(X, ⊤) →+* AddMonoid.End (M.cohomologyWithSupport Z W q) where
  toFun r := (Abelian.Ext.mk₀ ((toSheaf X).map (M.globalSectionsSmul r))).postcomp _ (add_zero q)
  -- In each field, `Abelian.Ext.postcomp` (an abbreviation for a flipped bilinear composition)
  -- applied to `x` is `x.comp`, which has the composition lemmas; the `change` steps record this.
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
    Module Γ(X, ⊤) (M.cohomologyWithSupport Z W q) :=
  Module.compHom _ (M.cohomologyWithSupportAction Z W q)

/-- A global function `r` acts on `H^q_Z(W, M)` by postcomposition with multiplication by `r`. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyWithSupport_smul_def (q : ℕ)
    (r : Γ(X, ⊤)) (x : M.cohomologyWithSupport Z W q) :
    r • x = x.comp (Abelian.Ext.mk₀ ((toSheaf X).map (M.globalSectionsSmul r))) (add_zero q) :=
  (rfl)

/-- In degree zero, cohomology with supports in `Z` is the module of global sections supported in
`Z`. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportZeroLinearEquiv :
    M.cohomologyWithSupport Z ⊤ 0 ≃ₗ[Γ(X, ⊤)] M.sectionsWithSupport Z where
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
    (x : M.cohomologyWithSupport Z ⊤ 0) :
    (M.cohomologyWithSupportZeroLinearEquiv Z x).val =
      (((toSheaf X).obj M).supportedHZeroEquiv Z ⊤ x).val :=
  (rfl)

/-- Cohomology on `W` with supports in `Z` vanishes when `W` does not meet `Z`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.subsingleton_cohomologyWithSupport_of_le_compl
    {W : X.Opens} (hW : W ≤ Z.compl) (q : ℕ) : Subsingleton (M.cohomologyWithSupport Z W q) :=
  ((toSheaf X).obj M).subsingleton_supportedH_of_le_compl Z hW q

/-- Cohomology with supports in the empty set vanishes. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.subsingleton_cohomologyWithSupport_bot
    (q : ℕ) : Subsingleton (M.cohomologyWithSupport ⊥ W q) :=
  -- The complement of `⊥` is everything: membership in it unfolds to `x ∉ (⊥ : Set X)`.
  M.subsingleton_cohomologyWithSupport_of_le_compl ⊥
    (fun x _ => show x ∉ ((⊥ : Closeds X) : Set X) by simp) q

section supportSequence

/-- The map `H^q_Z(W, M) ⟶ H^q(W, M)` of the long exact sequence of supports, forgetting the
support, as a linear map over global functions. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportToCohomologyOn (q : ℕ) :
    M.cohomologyWithSupport Z W q →ₗ[Γ(X, ⊤)] cohomologyOn M q W where
  toFun := Sheaf.relativeH'.toH' ((toSheaf X).obj M) (Z.complInclusion W) q
  map_add' := map_add _
  map_smul' r x := by
    apply (Sheaf.H'AddEquivExt ((toSheaf X).obj M) q W).injective
    refine (Sheaf.relativeH'.H'AddEquivExt_toH' _ _ _).trans
      (Eq.trans ?_ (H'AddEquivExt_cohomologyOn_smul M q W r
        (Sheaf.relativeH'.toH' ((toSheaf X).obj M) (Z.complInclusion W) q x)).symm)
    rw [Sheaf.relativeH'.H'AddEquivExt_toH', cohomologyWithSupport_smul_def]
    exact (Abelian.Ext.comp_assoc _ _ _ (zero_add q) (add_zero q) (by simp)).symm

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportToCohomologyOn_apply (q : ℕ)
    (x : M.cohomologyWithSupport Z W q) :
    M.cohomologyWithSupportToCohomologyOn Z W q x =
      Sheaf.relativeH'.toH' ((toSheaf X).obj M) (Z.complInclusion W) q x :=
  (rfl)

/-- Cohomology on `W` with supports in a closed `Z` containing `W` is cohomology: the map
`H^q_Z(W, M) ⟶ H^q(W, M)` of the long exact sequence of supports is a linear equivalence over
global functions. For `Z = X` this says `H^q_X(W, M) ≃ₗ H^q(W, M)`. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportLinearEquivOfSubset {W : X.Opens}
    (hW : (W : Set X) ⊆ Z) (q : ℕ) : M.cohomologyWithSupport Z W q ≃ₗ[Γ(X, ⊤)] cohomologyOn M q W :=
  LinearEquiv.ofBijective (M.cohomologyWithSupportToCohomologyOn Z W q) <| by
    -- by their `_apply` lemmas, both maps evaluate to `relativeH'.toH'`
    have h : ⇑(M.cohomologyWithSupportToCohomologyOn Z W q) =
        ⇑(((toSheaf X).obj M).supportedHEquivOfSubset Z hW q) :=
      funext fun x ↦ (M.cohomologyWithSupportToCohomologyOn_apply Z W q x).trans
        (Sheaf.supportedHEquivOfSubset_apply _ Z hW x).symm
    rw [h]
    exact (((toSheaf X).obj M).supportedHEquivOfSubset Z hW q).bijective

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportLinearEquivOfSubset_apply
    {W : X.Opens} (hW : (W : Set X) ⊆ Z) (q : ℕ) (x : M.cohomologyWithSupport Z W q) :
    M.cohomologyWithSupportLinearEquivOfSubset Z hW q x =
      M.cohomologyWithSupportToCohomologyOn Z W q x :=
  (rfl)

/-- The connecting map `H^q(W ∖ Z, M) ⟶ H^{q+1}_Z(W, M)` of the long exact sequence of supports,
as a linear map over global functions. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportδ {q₀ q₁ : ℕ}
    (h : 1 + q₀ = q₁) :
    cohomologyOn M q₀ (W ⊓ Z.compl) →ₗ[Γ(X, ⊤)] M.cohomologyWithSupport Z W q₁ where
  toFun := Sheaf.relativeH'.δ ((toSheaf X).obj M) (Z.complInclusion W) h
  map_add' := map_add _
  map_smul' r x := by
    rw [RingHom.id_apply, cohomologyWithSupport_smul_def]
    refine (Sheaf.relativeH'.δ_apply _ _ h _).trans ?_
    rw [H'AddEquivExt_cohomologyOn_smul]
    refine Eq.trans ?_ (congrArg (fun y => Abelian.Ext.comp y
      (Abelian.Ext.mk₀ ((toSheaf X).map (M.globalSectionsSmul r))) (add_zero q₁))
      (Sheaf.relativeH'.δ_apply ((toSheaf X).obj M) (Z.complInclusion W) h x)).symm
    exact (Abelian.Ext.comp_assoc _ _ _ h (add_zero q₀) (by omega)).symm

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportδ_apply {q₀ q₁ : ℕ}
    (h : 1 + q₀ = q₁) (x : cohomologyOn M q₀ (W ⊓ Z.compl)) :
    M.cohomologyWithSupportδ Z W h x =
      Sheaf.relativeH'.δ ((toSheaf X).obj M) (Z.complInclusion W) h x :=
  (rfl)

end supportSequence

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) (Z : Closeds X) (W : X.Opens)

/-- The long exact sequence of supports is exact at `H^q(W, M)`: a class comes from cohomology
with supports in `Z` exactly when its restriction to `W ∖ Z` vanishes. -/
theorem exact_cohomologyWithSupportToCohomologyOn_cohomologyOnResLinear (q : ℕ) :
    Function.Exact (M.cohomologyWithSupportToCohomologyOn Z W q)
      (cohomologyOnResLinear M q (inf_le_left : W ⊓ Z.compl ≤ W)) := by
  rw [coe_cohomologyOnResLinear]
  exact Sheaf.relativeH'.exact_toH'_cohomologyPresheaf_map _ _ q

/-- The long exact sequence of supports is exact at `H^q(W ∖ Z, M)`: the kernel of the connecting
map consists of the restrictions of classes on `W`. -/
theorem exact_cohomologyOnResLinear_cohomologyWithSupportδ {q₀ q₁ : ℕ} (h : 1 + q₀ = q₁) :
    Function.Exact (cohomologyOnResLinear M q₀ (inf_le_left : W ⊓ Z.compl ≤ W))
      (M.cohomologyWithSupportδ Z W h) := by
  rw [coe_cohomologyOnResLinear]
  exact Sheaf.relativeH'.exact_cohomologyPresheaf_map_δ _ _ h

/-- The long exact sequence of supports is exact at `H^{q+1}_Z(W, M)`. -/
theorem exact_cohomologyWithSupportδ_cohomologyWithSupportToCohomologyOn
    {q₀ q₁ : ℕ} (h : 1 + q₀ = q₁) :
    Function.Exact (M.cohomologyWithSupportδ Z W h)
      (M.cohomologyWithSupportToCohomologyOn Z W q₁) :=
  Sheaf.relativeH'.exact_δ_toH' _ _ h

end AlgebraicGeometry.Scheme.Modules
