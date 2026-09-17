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

Degree `0` is deliberately excluded: there `Ext⁰(X, Y)` is `Hom(X, Y)`, which need not be
`Hom(R₀, Y)`.

## Main definitions

* `CategoryTheory.ProjectiveResolution.extLinearEquiv`: the linear equivalence
  `Hom(Rₙ₊₁, Y) ≃ₗ Extⁿ⁺¹(X, Y)`, sending `f` to its class.

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
