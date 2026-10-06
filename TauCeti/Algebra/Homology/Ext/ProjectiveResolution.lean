/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import TauCeti.Algebra.Homology.Opposite
public import TauCeti.Algebra.Homology.ShortComplex.Linear

/-!
# Computing `Ext` from projective resolutions

Mathlib's `CategoryTheory.ProjectiveResolution.isoExt` computes `Extⁿ(X, Y)` from any projective
resolution `P` of `X`. When two resolutions of `X` are related by a chain map lying over the
identity of `X`, `isoExt_hom_comp_homologyMap` identifies the resulting computations.

Mathlib computes `Extⁿ(X, Y)` from a projective resolution `R` of `X` as the `n`-th cohomology of
the complex `Hom(R, Y)`: `CategoryTheory.ProjectiveResolution.extMk` builds a class from a cocycle,
`extMk_surjective` says every class arises that way, and `extMk_eq_zero_iff` identifies the
coboundaries.

This file records the degenerate case of that computation. If the two differentials of `R`
adjacent to a degree `n + 1` die against `Y` -- that is, if `d (n + 2) (n + 1) ≫ f = 0` for every
`f : Rₙ₊₁ ⟶ Y` and `d (n + 1) n ≫ g = 0` for every `g : Rₙ ⟶ Y` -- then in that degree no cocycle
condition and no coboundary survives, and `Extⁿ⁺¹(X, Y)` *is* the term `Hom(Rₙ₊₁, Y)`, linearly
over the coefficient ring.

In degree `0`, precomposition with the augmentation identifies `Hom(X, Y)` with `Hom(R₀, Y)`
when the first differential dies against `Y`. This identification needs no `HasExt` assumption.

## Main definitions

* `CategoryTheory.ProjectiveResolution.extLinearEquiv`: the linear equivalence
  `Hom(Rₙ₊₁, Y) ≃ₗ Extⁿ⁺¹(X, Y)`, sending `f` to its class.
* `TauCeti.projectiveResolutionExtLinearEquivOfIso`: the same computation using an object
  isomorphic to the resolution term.
* `TauCeti.projectiveResolutionHomLinearEquivOfCompEqZero`: the degree-zero Hom identification
  when the first differential vanishes against the target.

## Main results

* `CategoryTheory.ProjectiveResolution.isoExt_hom_comp_homologyMap`: computing `Ext` from two
  resolutions related by a chain map agrees with the induced map on cohomology.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Sections 2.2 and 2.4, for independence of
  `Ext` from the resolution, and Section 2.5, for `Ext` computed from a projective resolution.
-/

public section

namespace CategoryTheory.ProjectiveResolution

open CategoryTheory.Abelian

section Comparison

variable {R : Type*} [Ring R] {D : Type*} [Category* D] [Abelian D] [Linear R D]
  [EnoughProjectives D]

/-- **`Ext` computed from two resolutions related by a chain map.** If `φ : P ⟶ Q` is a chain map
between projective resolutions of `X` lying over the identity of `X`, then computing `Extⁿ(X, Y)`
from `Q` and precomposing with `φ` gives the computation from `P`. -/
theorem isoExt_hom_comp_homologyMap {X : D} (P Q : ProjectiveResolution X)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0) (n : ℕ) (Y : D) :
    (Q.isoExt n Y).hom ≫ HomologicalComplex.homologyMap
      ((HomologicalComplex.unopFunctor _ _).map
        ((((linearYoneda R D).obj Y).rightOp.mapHomologicalComplex _).map φ).op) n =
      (P.isoExt n Y).hom := by
  have h := isoLeftDerivedObj_hom_naturality (𝟙 X) P Q φ
    (comm.trans (Category.comp_id _).symm) ((linearYoneda R D).obj Y).rightOp n
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  have hP := congrArg Quiver.Hom.unop ((Iso.comp_inv_eq _).2 ((Iso.eq_inv_comp _).2 h.symm))
  have hn := TauCeti.HomologicalComplex.homologyUnop_inv_naturality
    ((((linearYoneda R D).obj Y).rightOp.mapHomologicalComplex _).map φ) n
  -- `isoExt` is by definition the inverse of `isoLeftDerivedObj`, unopposed, followed by the
  -- inverse of `homologyUnop`; its two constituents are what the two naturality squares govern.
  have e : (Q.isoExt n Y).hom =
      (Q.isoLeftDerivedObj ((linearYoneda R D).obj Y).rightOp n).inv.unop ≫
        (HomologicalComplex.homologyUnop _ n).inv := rfl
  rw [e]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hn.symm).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hP)))

end Comparison

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type t} [Ring k] [Linear k C]
  [HasExt.{w} C] {X Y : C}

omit [Ring k] [Linear k C] in
/-- If the degree-`n` term of a projective resolution has no nonzero morphism to `Y`, then
`Extⁿ(X,Y)` vanishes. No condition on the neighboring terms is needed. -/
theorem subsingleton_ext_of_subsingleton_hom (R : ProjectiveResolution X) (n : ℕ)
    [Subsingleton (R.complex.X n ⟶ Y)] : Subsingleton (Ext.{w} X Y n) := by
  apply subsingleton_of_forall_eq 0
  intro α
  obtain ⟨f, hf, rfl⟩ := R.extMk_surjective α (n + 1) rfl
  obtain rfl : f = 0 := Subsingleton.elim _ _
  simp

/-- If the two differentials of a projective resolution `R` of `X` adjacent to degree `n + 1`
become zero after applying `Hom(-, Y)`, then `Extⁿ⁺¹(X, Y)` is the degree `n + 1` term of that
`Hom`-complex, `k`-linearly. The class of `f` is `CategoryTheory.ProjectiveResolution.extMk f`. -/
noncomputable def extLinearEquiv (R : ProjectiveResolution X) (n : ℕ)
    (h₁ : ∀ f : R.complex.X (n + 1) ⟶ Y, R.complex.d (n + 2) (n + 1) ≫ f = 0)
    (h₂ : ∀ g : R.complex.X n ⟶ Y, R.complex.d (n + 1) n ≫ g = 0) :
    (R.complex.X (n + 1) ⟶ Y) ≃ₗ[k] Ext.{w} X Y (n + 1) := by
  refine LinearEquiv.ofBijective
    { toFun := fun f => R.extMk f (n + 2) rfl (h₁ f)
      map_add' := fun f g => (R.add_extMk f g (n + 2) rfl (h₁ f) (h₁ g)).symm
      map_smul' := fun c f => ?_ } ⟨?_, ?_⟩
  · dsimp
    rw [Ext.smul_eq_comp_mk₀, R.extMk_comp_mk₀]
    congr 1
    rw [Linear.comp_smul, Category.comp_id]
  · rw [← LinearMap.ker_eq_bot]
    ext f
    simp only [LinearMap.mem_ker, Submodule.mem_bot, LinearMap.coe_mk, AddHom.coe_mk]
    rw [R.extMk_eq_zero_iff f (n + 2) rfl (h₁ f) n rfl]
    exact ⟨fun ⟨g, hg⟩ ↦ hg ▸ h₂ g, fun hf ↦ ⟨0, by simp [hf]⟩⟩
  · intro α
    obtain ⟨f, hf, rfl⟩ := R.extMk_surjective α (n + 2) rfl
    exact ⟨f, rfl⟩

@[simp]
theorem extLinearEquiv_apply (R : ProjectiveResolution X) (n : ℕ)
    (h₁ : ∀ f : R.complex.X (n + 1) ⟶ Y, R.complex.d (n + 2) (n + 1) ≫ f = 0)
    (h₂ : ∀ g : R.complex.X n ⟶ Y, R.complex.d (n + 1) n ≫ g = 0)
    (f : R.complex.X (n + 1) ⟶ Y) :
    extLinearEquiv (k := k) R n h₁ h₂ f = R.extMk f (n + 2) rfl (h₁ f) :=
  (rfl)

end CategoryTheory.ProjectiveResolution

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type t} [Ring k] [Linear k C]
  {X Y Z : C}

/-- Precomposition with a projective resolution's augmentation identifies Hom from the resolved
object with Hom from its zeroth term when the first differential vanishes against the target. -/
noncomputable def projectiveResolutionHomLinearEquivOfCompEqZero
    (R : CategoryTheory.ProjectiveResolution X)
    (h : ∀ f : R.complex.X 0 ⟶ Y, R.complex.d 1 0 ≫ f = 0) :
    (X ⟶ Y) ≃ₗ[k] (R.complex.X 0 ⟶ Y) :=
  homLinearEquivOfExact R.exact₀ h

/-- The degree-zero Hom identification is precomposition with the augmentation. -/
@[simp]
theorem projectiveResolutionHomLinearEquivOfCompEqZero_apply
    (R : CategoryTheory.ProjectiveResolution X)
    (h : ∀ f : R.complex.X 0 ⟶ Y, R.complex.d 1 0 ≫ f = 0) (f : X ⟶ Y) :
    projectiveResolutionHomLinearEquivOfCompEqZero (k := k) R h f = R.π.f 0 ≫ f :=
  homLinearEquivOfExact_apply R.exact₀ h f

variable [HasExt.{w} C]

/-- Compute positive-degree Ext from an object isomorphic to a resolution term when both
adjacent differentials vanish against the target. -/
noncomputable def projectiveResolutionExtLinearEquivOfIso
    (R : CategoryTheory.ProjectiveResolution X) (n : ℕ)
    (e : R.complex.X (n + 1) ≅ Z)
    (h₁ : ∀ f : R.complex.X (n + 1) ⟶ Y, R.complex.d (n + 2) (n + 1) ≫ f = 0)
    (h₂ : ∀ g : R.complex.X n ⟶ Y, R.complex.d (n + 1) n ≫ g = 0) :
    (Z ⟶ Y) ≃ₗ[k] Ext.{w} X Y (n + 1) :=
  (Linear.homCongr k e.symm (Iso.refl Y)).trans (R.extLinearEquiv n h₁ h₂)

/-- The transported Ext computation sends a map to the class of its precomposition with
the term isomorphism. -/
@[simp]
theorem projectiveResolutionExtLinearEquivOfIso_apply
    (R : CategoryTheory.ProjectiveResolution X) (n : ℕ)
    (e : R.complex.X (n + 1) ≅ Z)
    (h₁ : ∀ f : R.complex.X (n + 1) ⟶ Y, R.complex.d (n + 2) (n + 1) ≫ f = 0)
    (h₂ : ∀ g : R.complex.X n ⟶ Y, R.complex.d (n + 1) n ≫ g = 0) (f : Z ⟶ Y) :
    projectiveResolutionExtLinearEquivOfIso (k := k) R n e h₁ h₂ f =
      R.extMk (e.hom ≫ f) (n + 2) rfl (h₁ _) := by
  simp only [projectiveResolutionExtLinearEquivOfIso, LinearEquiv.trans_apply,
    CategoryTheory.ProjectiveResolution.extLinearEquiv_apply, Linear.homCongr_apply,
    Iso.symm_inv, Iso.refl_hom, Category.comp_id]

end TauCeti
