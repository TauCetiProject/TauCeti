/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Double

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
`S.X₁`, `S.X₂` are projective, it underlies the projective resolution of `S.X₃`.

This model has definitionally specified objects and differential in degrees `0` and `1`, so the
kernel formulas for derived functors involve `F.map S.f` directly. In these degrees the chain map
`resolutionComplexMap φ` has components `φ.τ₂` and `φ.τ₁` (`resolutionComplexMap_f_zero`,
`resolutionComplexMap_f_one`). Mathlib's `double` instead uses classical equality tests on degrees;
the comparison `resolutionComplexIsoDouble` identifies the two models. -/
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

/-- Two chain maps out of `S.resolutionComplex` agree as soon as they agree in degrees `0` and `1`,
since the complex vanishes in higher degrees. -/
@[ext]
lemma from_resolutionComplex_hom_ext {K : ChainComplex C ℕ} {f g : S.resolutionComplex ⟶ K}
    (h₀ : f.f 0 = g.f 0) (h₁ : f.f 1 = g.f 1) : f = g := by
  ext (_ | _ | n)
  · exact h₀
  · exact h₁
  · exact (S.isZero_resolutionComplex_X_add_two n).eq_of_src _ _

/-- The normalized presentation complex is Mathlib's two-term complex on `S.f`. -/
def resolutionComplexIsoDouble (S : ShortComplex C) :
    S.resolutionComplex ≅ HomologicalComplex.double S.f (c := ComplexShape.down ℕ)
      (i₀ := 1) (i₁ := 0) rfl :=
  HomologicalComplex.Hom.isoOfComponents (fun n => match n with
    | 0 => (HomologicalComplex.doubleXIso₁ S.f rfl (by decide)).symm
    | 1 => (HomologicalComplex.doubleXIso₀ S.f rfl).symm
    | n + 2 => (S.isZero_resolutionComplex_X_add_two n).iso
        (HomologicalComplex.isZero_double_X S.f rfl (n + 2) (by omega) (by omega))) (by
    rintro i j hij
    obtain rfl : j + 1 = i := by simpa only [ComplexShape.down_Rel] using hij
    obtain _ | j := j
    · -- `rw` cannot match through the component-family match. Reduce its degree-one branch
      -- and `Iso.symm_hom` to expose the inverse of `doubleXIso₀` before rewriting `double_d`.
      change (HomologicalComplex.doubleXIso₀ S.f _).inv ≫ _ = _
      rw [HomologicalComplex.double_d S.f (c := ComplexShape.down ℕ) (i₀ := 1) (i₁ := 0)
        rfl (by decide)]
      exact Iso.inv_hom_id_assoc _ _
    · exact (S.isZero_resolutionComplex_X_add_two j).eq_of_src _ _)

/-- The comparison isomorphism in degree zero is the inverse of Mathlib's degree-zero
identification for the two-term complex. -/
@[simp]
lemma resolutionComplexIsoDouble_hom_f_zero (S : ShortComplex C) :
    S.resolutionComplexIsoDouble.hom.f 0 =
      (HomologicalComplex.doubleXIso₁ S.f rfl (by decide)).inv := by
  rfl

/-- The comparison isomorphism in degree one is the inverse of Mathlib's degree-one
identification for the two-term complex. -/
@[simp]
lemma resolutionComplexIsoDouble_hom_f_one (S : ShortComplex C) :
    S.resolutionComplexIsoDouble.hom.f 1 =
      (HomologicalComplex.doubleXIso₀ S.f rfl).inv := by
  rfl

/-- The inverse comparison in degree zero is Mathlib's degree-zero identification. -/
@[simp]
lemma resolutionComplexIsoDouble_inv_f_zero (S : ShortComplex C) :
    S.resolutionComplexIsoDouble.inv.f 0 =
      (HomologicalComplex.doubleXIso₁ S.f rfl (by decide)).hom := by
  rfl

/-- The inverse comparison in degree one is Mathlib's degree-one identification. -/
@[simp]
lemma resolutionComplexIsoDouble_inv_f_one (S : ShortComplex C) :
    S.resolutionComplexIsoDouble.inv.f 1 =
      (HomologicalComplex.doubleXIso₀ S.f rfl).hom := by
  rfl

/-- The augmentation `S.g : S.X₂ ⟶ S.X₃` of `S.resolutionComplex`, as a chain map to the single
complex on `S.X₃`. -/
def resolutionπ (S : ShortComplex C) :
    S.resolutionComplex ⟶ (ChainComplex.single₀ C).obj S.X₃ :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨S.g, S.zero⟩

/-- In degree `0`, the augmentation of `S.resolutionComplex` is `S.g`. -/
@[simp]
lemma resolutionπ_f_zero (S : ShortComplex C) : S.resolutionπ.f 0 = S.g :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- In positive degrees, the augmentation of `S.resolutionComplex` vanishes, since its target
does. -/
@[simp]
lemma resolutionπ_f_succ (S : ShortComplex C) (n : ℕ) : S.resolutionπ.f (n + 1) = 0 :=
  (HomologicalComplex.isZero_single_obj_X _ 0 S.X₃ (n + 1) n.succ_ne_zero).eq_of_tgt _ _

/-- A morphism of short complexes induces the chain map of the associated complexes given by its
first two components. -/
def resolutionComplexMap (φ : S ⟶ S') : S.resolutionComplex ⟶ S'.resolutionComplex :=
  ChainComplex.ofHom (fun n => match n with | 0 => φ.τ₂ | 1 => φ.τ₁ | _ + 2 => 0) fun
    | 0 => φ.comm₁₂
    | j + 1 => (S.isZero_resolutionComplex_X_add_two j).eq_of_src _ _

/-- In degree `0`, the chain map induced by `φ` is `φ.τ₂`. -/
@[simp]
lemma resolutionComplexMap_f_zero (φ : S ⟶ S') : (resolutionComplexMap φ).f 0 = φ.τ₂ :=
  (rfl)

/-- In degree `1`, the chain map induced by `φ` is `φ.τ₁`. -/
@[simp]
lemma resolutionComplexMap_f_one (φ : S ⟶ S') : (resolutionComplexMap φ).f 1 = φ.τ₁ :=
  (rfl)

/-- In degrees at least `2`, the chain map induced by `φ` vanishes. -/
@[simp]
lemma resolutionComplexMap_f_add_two (φ : S ⟶ S') (n : ℕ) :
    (resolutionComplexMap φ).f (n + 2) = 0 :=
  (rfl)

/-- The induced map of the identity short-complex morphism is the identity chain map. -/
@[simp]
lemma resolutionComplexMap_id (S : ShortComplex C) :
    resolutionComplexMap (𝟙 S) = 𝟙 S.resolutionComplex := by
  ext <;> exact (rfl)

/-- The induced chain maps preserve composition of short-complex morphisms. -/
@[simp]
lemma resolutionComplexMap_comp {S'' : ShortComplex C} (φ : S ⟶ S') (ψ : S' ⟶ S'') :
    resolutionComplexMap (φ ≫ ψ) = resolutionComplexMap φ ≫ resolutionComplexMap ψ := by
  ext <;> exact (rfl)

/-- The chain map induced by `φ` lies over `φ.τ₃`. -/
@[reassoc (attr := simp)]
lemma resolutionComplexMap_comp_resolutionπ (φ : S ⟶ S') :
    resolutionComplexMap φ ≫ S'.resolutionπ =
      S.resolutionπ ≫ (ChainComplex.single₀ C).map φ.τ₃ := by
  -- Chain maps to a single complex are determined in degree `0`, where this is `φ.comm₂₃`.
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, resolutionComplexMap_f_zero, resolutionπ_f_zero,
    ChainComplex.single₀_map_f_zero]
  exact φ.comm₂₃

end ShortComplex

end CategoryTheory
