/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.HomCocycle.Range
public import TauCeti.Algebra.Module.HomCocycle.Presentation
public import TauCeti.Algebra.Homology.Ext.Presentation
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import TauCeti.Algebra.Category.ModuleCat.Quotient
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Hom cocycles compute Ext¹

For `f : P₁ → P₀` with `P₀` projective, maps `P₁ → N` killing `ker f`,
modulo maps extending across `f`, compute `Ext¹(P₀ / range f,N)`. No
injectivity of `f`, projectivity of `P₁`, or minimality is required.

The comparison descends cocycles to `range f`, then applies
`TauCeti.homCokernelEquivExt` to the short exact sequence
`0 → range f → P₀ → P₀ / range f → 0`. This connects the cocycle form
of the Auslander–Reiten pairing to the usual extension group.
Precomposition by a square of presentations agrees with pullback along its
induced cokernel map; postcomposition agrees with pushforward in the coefficients.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.2.
-/

public section

namespace LinearMap

open TauCeti CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra

universe u v w

variable {k : Type u} {A : Type v} [CommRing k] [Ring A] [Algebra k A]
  {P₀ P₁ : Type max u v w}
  [AddCommGroup P₀] [Module A P₀] [Module.Projective A P₀]
  [AddCommGroup P₁] [Module A P₁]

/-- Hom cocycles modulo coboundaries compute the first extension group of the
cokernel of `f`, provided its middle term is projective. -/
noncomputable def homCocycleQuotientEquivExt (f : P₁ →ₗ[A] P₀)
    (N : ModuleCat.{max u v w} A) :
    HomCocycleQuotient (k := k) f N ≃ₗ[k]
      Ext (ModuleCat.of A (P₀ ⧸ range f)) N 1 := by
  let e : (range f →ₗ[A] N) ≃ₗ[k] (ModuleCat.of A (range f) ⟶ N) :=
    (ModuleCat.homLinearEquiv (M := ModuleCat.of A (range f)) (N := N) (S := k)).symm
  have hmap : (range ((range f).subtype.lcomp k N)).map e.toLinearMap =
      (Linear.leftComp k N (ModuleCat.ofHom (range f).subtype)).range := by
    ext h
    constructor
    · rintro ⟨g, ⟨a, rfl⟩, rfl⟩
      exact ⟨ModuleCat.ofHom a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a.hom.comp (range f).subtype, ⟨a.hom, rfl⟩, rfl⟩
  exact (homCocycleQuotientEquivRange (k := k) f).trans
    ((Submodule.Quotient.equiv _ _ e hmap).trans
      (homCokernelEquivExt k (range f).shortExact_quotientShortComplex N))

/-- A map on the image represents the pushout of the image short exact sequence. -/
@[simp]
theorem homCocycleQuotientEquivExt_mk (f : P₁ →ₗ[A] P₀)
    (N : ModuleCat.{max u v w} A) (h : range f →ₗ[A] N) :
    homCocycleQuotientEquivExt (k := k) f N
        (Submodule.Quotient.mk (rangeHomEquivCocycles (k := k) f h)) =
      (range f).shortExact_quotientShortComplex.extClass.comp
        (Ext.mk₀ (ModuleCat.ofHom h)) (add_zero 1) := by
  simp only [homCocycleQuotientEquivExt, LinearEquiv.trans_apply,
    homCocycleQuotientEquivRange_mk, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  exact homCokernelEquivExt_mk k _ N _

/-- The inverse comparison represents a pushout extension by its Hom cocycle. -/
@[simp]
theorem homCocycleQuotientEquivExt_symm_comp_mk₀ (f : P₁ →ₗ[A] P₀)
    (N : ModuleCat.{max u v w} A) (h : range f →ₗ[A] N) :
    (homCocycleQuotientEquivExt (k := k) f N).symm
        ((range f).shortExact_quotientShortComplex.extClass.comp
          (Ext.mk₀ (ModuleCat.ofHom h)) (add_zero 1)) =
      Submodule.Quotient.mk (rangeHomEquivCocycles (k := k) f h) := by
  rw [← homCocycleQuotientEquivExt_mk (k := k) f N h, LinearEquiv.symm_apply_apply]

/-- Postcomposition on cocycle classes agrees with pushforward on extension classes. -/
@[simp]
theorem homCocycleQuotientEquivExt_naturality (f : P₁ →ₗ[A] P₀)
    {N N' : ModuleCat.{max u v w} A} (g : N ⟶ N')
    (x : HomCocycleQuotient (k := k) f N) :
    homCocycleQuotientEquivExt (k := k) f N' (homCocycleQuotientMap f g.hom x) =
      (homCocycleQuotientEquivExt (k := k) f N x).comp (Ext.mk₀ g) (add_zero 1) := by
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
    obtain ⟨h, rfl⟩ := (rangeHomEquivCocycles (k := k) f).surjective a
    have hmap : homCocycleQuotientMap (k := k) f g.hom
        (Submodule.Quotient.mk (rangeHomEquivCocycles (k := k) f h)) =
        Submodule.Quotient.mk (rangeHomEquivCocycles (k := k) f (g.hom.comp h)) := by
      rw [homCocycleQuotientMap_mk]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      simp only [rangeHomEquivCocycles_apply_val, comp_assoc]
    rw [hmap, homCocycleQuotientEquivExt_mk, homCocycleQuotientEquivExt_mk]
    simp

section Presentation

variable {Q₀ Q₁ : Type max u v w}
  [AddCommGroup Q₀] [Module A Q₀] [Module.Projective A Q₀]
  [AddCommGroup Q₁] [Module A Q₁]
  {p : P₁ →ₗ[A] P₀} {q : Q₁ →ₗ[A] Q₀}

/-- Precomposition by a presentation square computes pullback of extension classes
along its induced cokernel map. -/
theorem homCocycleQuotientEquivExt_precomp
    (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁) (hf : f₀.comp p = q.comp f₁)
    (g : (P₀ ⧸ range p) →ₗ[A] (Q₀ ⧸ range q))
    (hg : g.comp (range p).mkQ = (range q).mkQ.comp f₀)
    (N : ModuleCat.{max u v w} A) (x : HomCocycleQuotient (k := k) q N) :
    homCocycleQuotientEquivExt (k := k) p N (homCocycleQuotientPrecomp f₀ f₁ hf x) =
      (Ext.mk₀ (ModuleCat.ofHom g)).comp
        (homCocycleQuotientEquivExt (k := k) q N x) (zero_add 1) := by
  let r : range p →ₗ[A] range q := (f₀.comp (range p).subtype).codRestrict _ (by
    rintro ⟨_, y, rfl⟩
    exact ⟨f₁ y, (LinearMap.congr_fun hf y).symm⟩)
  let φ : (range p).quotientShortComplex ⟶ (range q).quotientShortComplex :=
    { τ₁ := ModuleCat.ofHom r
      τ₂ := ModuleCat.ofHom f₀
      τ₃ := ModuleCat.ofHom g
      comm₁₂ := by ext; rfl
      comm₂₃ := ModuleCat.hom_ext hg.symm }
  have hclass := (range p).shortExact_quotientShortComplex.extClass_naturality
    (range q).shortExact_quotientShortComplex φ
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
    obtain ⟨h, rfl⟩ := (rangeHomEquivCocycles (k := k) q).surjective a
    have hmap : homCocycleQuotientPrecomp f₀ f₁ hf
        (Submodule.Quotient.mk (rangeHomEquivCocycles (k := k) q h)) =
        Submodule.Quotient.mk (rangeHomEquivCocycles (k := k) p (h.comp r)) := by
      rw [homCocycleQuotientPrecomp_mk]
      congr 1
      apply Subtype.ext
      ext y
      simp only [rangeHomEquivCocycles_apply_val, comp_apply]
      congr 1
      exact Subtype.ext (LinearMap.congr_fun hf y).symm
    rw [hmap, homCocycleQuotientEquivExt_mk, homCocycleQuotientEquivExt_mk]
    simpa [φ] using congrArg
      (fun α ↦ α.comp (Ext.mk₀ (ModuleCat.ofHom h)) (add_zero 1)) hclass

end Presentation

/-- The first extension group of a cokernel is finite-dimensional when its presenting
source and the coefficient module are finite-dimensional. The presenting arrow need
not be injective, and its source need not be projective. -/
theorem finiteDimensional_ext_cokernel {K : Type u} [Field K] [Algebra K A]
    [Module K P₁] [IsScalarTower K A P₁]
    [Module.Finite K P₁] (f : P₁ →ₗ[A] P₀) (N : ModuleCat.{max u v w} A)
    [Module.Finite K N] :
    Module.Finite K (Ext (ModuleCat.of A (P₀ ⧸ range f)) N 1) := by
  let := Module.Finite.of_injective (restrictScalarsₗ K A P₁ N K)
    (restrictScalars_injective K)
  exact (homCocycleQuotientEquivExt (k := K) f N).finiteDimensional

end LinearMap
