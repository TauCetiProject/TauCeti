/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Single

/-!
# Two-term presentation complexes

A short complex `S : S.X₁ ⟶ S.X₂ ⟶ S.X₃` determines the chain complex
`⋯ ⟶ 0 ⟶ S.X₁ ⟶ S.X₂`, augmented to `S.X₃`. This file constructs the complex, its augmentation,
and the chain maps induced by morphisms of short complexes in any category with zero morphisms
and a zero object.

For a short exact presentation by projective objects in an abelian category, this is the complex
of the projective resolution used to compute left derived functors in
`TauCeti.CategoryTheory.Abelian.LeftDerived`.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Section 2.4.
-/

public section

noncomputable section

namespace CategoryTheory

open Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {S S' : ShortComplex C}

namespace ShortComplex

/-- The chain complex `⋯ ⟶ 0 ⟶ S.X₁ ⟶ S.X₂` with `S.X₂` in degree `0` and `S.X₁` in degree `1`,
whose only nonzero differential is `S.f`. In an abelian category, when `S` is short exact and
`S.X₁`, `S.X₂` are projective, it underlies the projective resolution of `S.X₃`. -/
@[expose]
def resolutionComplex (S : ShortComplex C) : ChainComplex C ℕ where
  X n := match n with | 0 => S.X₂ | 1 => S.X₁ | _ + 2 => 0
  d i j := match i, j with | 1, 0 => S.f | _, _ => 0
  shape i j h := by
    obtain _ | _ | i := i <;> obtain _ | j := j <;> first | rfl | simp at h
  d_comp_d' i j k hij hjk := by
    simp only [ComplexShape.down_Rel] at hij hjk
    subst hij hjk
    obtain _ | k := k <;> exact zero_comp

/-- The differential of `S.resolutionComplex` from degree `1` to degree `0` is `S.f`. -/
@[simp]
lemma resolutionComplex_d_one_zero (S : ShortComplex C) : S.resolutionComplex.d 1 0 = S.f :=
  (rfl)

/-- `S.resolutionComplex` is `S.X₂` in degree `0`. -/
@[simp]
lemma resolutionComplex_X_zero (S : ShortComplex C) : S.resolutionComplex.X 0 = S.X₂ :=
  (rfl)

/-- `S.resolutionComplex` is `S.X₁` in degree `1`. -/
@[simp]
lemma resolutionComplex_X_one (S : ShortComplex C) : S.resolutionComplex.X 1 = S.X₁ :=
  (rfl)

/-- `S.resolutionComplex` vanishes in degrees at least `2`. -/
lemma isZero_resolutionComplex_X_add_two (S : ShortComplex C) (n : ℕ) :
    IsZero (S.resolutionComplex.X (n + 2)) :=
  isZero_zero C

/-- The augmentation `S.g : S.X₂ ⟶ S.X₃` of `S.resolutionComplex`, as a chain map to the single
complex on `S.X₃`. -/
def resolutionπ (S : ShortComplex C) :
    S.resolutionComplex ⟶ (ChainComplex.single₀ C).obj S.X₃ :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨S.g, S.zero⟩

/-- In degree `0`, the augmentation of `S.resolutionComplex` is `S.g`. -/
@[simp]
lemma resolutionπ_f_zero (S : ShortComplex C) : S.resolutionπ.f 0 = S.g :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- A morphism of short complexes induces the chain map of the associated complexes given by its
first two components. -/
def resolutionComplexMap (φ : S ⟶ S') : S.resolutionComplex ⟶ S'.resolutionComplex :=
  ChainComplex.ofHom (fun n => match n with | 0 => φ.τ₂ | 1 => φ.τ₁ | _ + 2 => 0)
    (fun n => by
      obtain _ | _ | n := n
      · exact φ.comm₁₂
      · exact (S.isZero_resolutionComplex_X_add_two 0).eq_of_src _ _
      · exact (S.isZero_resolutionComplex_X_add_two (n + 1)).eq_of_src _ _)

/-- In degree `0`, the chain map induced by `φ` is `φ.τ₂`. -/
@[simp]
lemma resolutionComplexMap_f_zero (φ : S ⟶ S') : (resolutionComplexMap φ).f 0 = φ.τ₂ :=
  (rfl)

/-- In degree `1`, the chain map induced by `φ` is `φ.τ₁`. -/
@[simp]
lemma resolutionComplexMap_f_one (φ : S ⟶ S') : (resolutionComplexMap φ).f 1 = φ.τ₁ :=
  (rfl)

/-- The chain map induced by `φ` lies over `φ.τ₃`. -/
@[reassoc (attr := simp)]
lemma resolutionComplexMap_comp_resolutionπ (φ : S ⟶ S') :
    resolutionComplexMap φ ≫ S'.resolutionπ =
      S.resolutionπ ≫ (ChainComplex.single₀ C).map φ.τ₃ := by
  ext
  simp only [HomologicalComplex.comp_f, resolutionComplexMap_f_zero, resolutionπ_f_zero,
    ChainComplex.single₀_map_f_zero]
  exact φ.comm₂₃

end ShortComplex

end CategoryTheory
