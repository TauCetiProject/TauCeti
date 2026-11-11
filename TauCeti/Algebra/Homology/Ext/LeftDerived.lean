/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
import TauCeti.Algebra.Homology.LinearYoneda

/-!
# Vanishing of the two `Ext` functors

Mathlib has two constructions of `Ext` in an abelian category `C` with enough projectives. The
functor `Ext k C n : Cᵒᵖ ⥤ C ⥤ ModuleCat k` of `Mathlib.CategoryTheory.Abelian.Ext` is the left
derived functor of `Hom(-, Y)`, computed from a projective resolution `P` of `X` as the
cohomology of the complex `Hom(P, Y)` (`CategoryTheory.ProjectiveResolution.isoExt`). The groups
`CategoryTheory.Abelian.Ext X Y n` are morphisms in the derived category. Mathlib's module
`localCohomology` is built from the first construction, while depth (`Ideal.depth`) and most of
the homological algebra of modules use the second.

This file shows that the two constructions vanish together: both are zero exactly when the
complex `Hom(P, Y)` is exact in degree `n`. In degree `n + 1` this says that every cocycle
`f : Pₙ₊₁ ⟶ Y` is a coboundary. In degree `0` it says that every morphism `P₀ ⟶ Y` killed by
`P₁ ⟶ P₀` is zero; as `X` is the cokernel of `P₁ ⟶ P₀`, these morphisms are the morphisms
`X ⟶ Y`. The matching descriptions of the exactness of `Hom(P, Y)` are
`ChainComplex.exactAt_linearYonedaObj_zero_iff` and
`ChainComplex.exactAt_linearYonedaObj_succ_iff` in `TauCeti.Algebra.Homology.LinearYoneda`.
This lets vanishing results proved for the derived-category `Ext`, such as the vanishing of
`Ext (R ⧸ I) M` below the depth, be used for the left derived functor, and hence for local
cohomology.

## Main results

* `CategoryTheory.ProjectiveResolution.subsingleton_ext_iff_exactAt`: `Ext X Y n` vanishes if and
  only if `Hom(P, Y)` is exact in degree `n`.
* `CategoryTheory.ProjectiveResolution.isZero_Ext_iff_exactAt`: the same for the left derived
  functor `Ext k C n`.
* `CategoryTheory.Abelian.Ext.subsingleton_iff_isZero_Ext`: the two constructions of `Ext` vanish
  together.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 2.5 (`Ext` via projective
  resolutions) and Section 10.7 (`Ext` as morphisms in the derived category).
-/

public section

universe w v u t

open CategoryTheory Limits

namespace CategoryTheory.ProjectiveResolution

open Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {X Y : C}
  (P : ProjectiveResolution X)

/-- `Ext⁰(X, Y) = Hom(X, Y)` vanishes exactly when every morphism `P₀ ⟶ Y` killed by the
differential `P₁ ⟶ P₀` of a projective resolution `P` of `X` is zero. -/
theorem subsingleton_ext_zero_iff :
    Subsingleton (Ext.{w} X Y 0) ↔ ∀ f : P.complex.X 0 ⟶ Y, P.complex.d 1 0 ≫ f = 0 → f = 0 := by
  rw [Ext.homEquiv₀.subsingleton_congr]
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 X
  refine ⟨fun _ f hf ↦ ?_, fun h ↦ ⟨fun g g' ↦ ?_⟩⟩
  · -- `X` is the cokernel of `P₁ ⟶ P₀`, so `f` factors through `X`.
    obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc' P.isColimitCokernelCofork f hf
    rw [← hl, ← e.hom_inv_id_assoc l, Subsingleton.elim (e.inv ≫ l) 0]
    simp
  · refine sub_eq_zero.1 ((cancel_epi (P.π.f 0 ≫ e.hom)).1 ?_)
    rw [comp_zero]
    exact h _ (by simp only [Category.assoc, P.complex_d_comp_π_f_zero_assoc, zero_comp])

/-- `Extⁿ⁺¹(X, Y)` vanishes exactly when, for a projective resolution `P` of `X`, every cocycle
`Pₙ₊₁ ⟶ Y` of the complex `Hom(P, Y)` is a coboundary. -/
theorem subsingleton_ext_succ_iff (n : ℕ) :
    Subsingleton (Ext.{w} X Y (n + 1)) ↔
      ∀ f : P.complex.X (n + 1) ⟶ Y, P.complex.d (n + 2) (n + 1) ≫ f = 0 →
        ∃ g : P.complex.X n ⟶ Y, P.complex.d (n + 1) n ≫ g = f := by
  refine ⟨fun _ f hf ↦ ?_, fun h ↦ subsingleton_of_forall_eq 0 fun α ↦ ?_⟩
  · exact (P.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).1 (Subsingleton.elim _ _)
  · obtain ⟨f, hf, rfl⟩ := P.extMk_surjective α (n + 2) rfl
    exact (P.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).2 (h f hf)

variable (k : Type t) [Ring k] [Linear k C]

/-- `Ext X Y n` vanishes exactly when the complex `Hom(P, Y)` is exact in degree `n`, for any
projective resolution `P` of `X`. -/
theorem subsingleton_ext_iff_exactAt (n : ℕ) :
    Subsingleton (Ext.{w} X Y n) ↔ (P.complex.linearYonedaObj k Y).ExactAt n := by
  cases n with
  | zero => rw [subsingleton_ext_zero_iff P, ChainComplex.exactAt_linearYonedaObj_zero_iff]
  | succ n => rw [subsingleton_ext_succ_iff P, ChainComplex.exactAt_linearYonedaObj_succ_iff]

omit [HasExt.{w} C] in
/-- The left derived functor `Ext k C n` vanishes on `(X, Y)` exactly when the complex
`Hom(P, Y)` is exact in degree `n`, for any projective resolution `P` of `X`. -/
theorem isZero_Ext_iff_exactAt [EnoughProjectives C] (n : ℕ) :
    IsZero (((_root_.Ext k C n).obj (Opposite.op X)).obj Y) ↔
      (P.complex.linearYonedaObj k Y).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ⟨fun h ↦ h.of_iso (P.isoExt n Y).symm, fun h ↦ h.of_iso (P.isoExt n Y)⟩

end CategoryTheory.ProjectiveResolution

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [EnoughProjectives C]
  (k : Type t) [Ring k] [Linear k C]

/-- The derived-category `Ext X Y n` vanishes if and only if the left derived functor
`Ext k C n` vanishes on `(X, Y)`. -/
theorem subsingleton_iff_isZero_Ext (X Y : C) (n : ℕ) :
    Subsingleton (Ext.{w} X Y n) ↔ IsZero (((_root_.Ext k C n).obj (Opposite.op X)).obj Y) := by
  rw [(projectiveResolution X).subsingleton_ext_iff_exactAt k,
    (projectiveResolution X).isZero_Ext_iff_exactAt k]

end CategoryTheory.Abelian.Ext
