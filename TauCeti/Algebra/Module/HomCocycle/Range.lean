/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.HomCocycle.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Descending Hom cocycles to the image

A map vanishing on the kernel of `f : P₁ → P₀` descends uniquely to `range f`.
This identifies Hom cocycles modulo coboundaries with the cokernel of restriction
`Hom(P₀,N) → Hom(range f,N)`. In a projective presentation this is the syzygy
model of `Ext¹`, including presentations whose leftmost arrow is not injective.

The descent uses Mathlib's `LinearMap.liftOfSurjective`. No exactness,
projectivity or finiteness assumption is needed.
-/

public section

namespace LinearMap

variable {k A P₀ P₁ N : Type*} [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup P₀] [Module A P₀] [AddCommGroup P₁] [Module A P₁]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]

/-- Precomposition with the surjection onto `range f` identifies maps on the image
with maps vanishing on `ker f`. -/
noncomputable def rangeHomEquivCocycles (f : P₁ →ₗ[A] P₀) :
    (range f →ₗ[A] N) ≃ₗ[k] ker ((ker f).subtype.lcomp k N) := by
  let F : (range f →ₗ[A] N) →ₗ[k] ker ((ker f).subtype.lcomp k N) :=
    (f.rangeRestrict.lcomp k N).codRestrict _ fun h ↦ by
      apply mem_ker.mpr
      ext x
      simp only [lcomp_apply, Submodule.subtype_apply, zero_apply]
      have hx : f.rangeRestrict x.val = 0 := Subtype.ext (mem_ker.mp x.property)
      simp only [hx, map_zero]
  apply LinearEquiv.ofBijective F
  constructor
  · intro g h heq
    exact lcomp_injective_of_surjective (S := k) (N := N) f.rangeRestrict
      f.surjective_rangeRestrict (congrArg Subtype.val heq)
  · intro h
    have hh : ker f.rangeRestrict ≤ ker h.val := by
      intro x hx
      have hx' : x ∈ ker f := by simpa using hx
      have hz := LinearMap.congr_fun (mem_ker.mp h.property) ⟨x, hx'⟩
      exact mem_ker.mpr (by simpa only [lcomp_apply, zero_apply, Submodule.subtype_apply] using hz)
    refine ⟨f.rangeRestrict.liftOfSurjective f.surjective_rangeRestrict ⟨h.val, hh⟩, ?_⟩
    apply Subtype.ext
    ext x
    exact equivOfSurjective_apply f.surjective_rangeRestrict hh

/-- On a map defined on the image, the cocycle comparison is precomposition. -/
@[simp]
theorem rangeHomEquivCocycles_apply_val (f : P₁ →ₗ[A] P₀) (h : range f →ₗ[A] N) :
    (rangeHomEquivCocycles (k := k) f h).val = h.comp f.rangeRestrict :=
  (rfl)

/-- Descent evaluates at `f x` by evaluating the original cocycle at `x`. -/
@[simp]
theorem rangeHomEquivCocycles_symm_apply_rangeRestrict (f : P₁ →ₗ[A] P₀)
    (h : ker ((ker f).subtype.lcomp k N)) (x : P₁) :
    (rangeHomEquivCocycles (k := k) f).symm h (f.rangeRestrict x) = h.val x := by
  have heq := congrArg (fun z ↦ z.val x)
    ((rangeHomEquivCocycles (k := k) f).apply_symm_apply h)
  simpa only [rangeHomEquivCocycles_apply_val, comp_apply] using heq

/-- Hom cocycles modulo coboundaries are maps on the image modulo maps extending
to the presenting middle term. -/
noncomputable def homCocycleQuotientEquivRange (f : P₁ →ₗ[A] P₀) :
    HomCocycleQuotient (k := k) f N ≃ₗ[k]
      (range f →ₗ[A] N) ⧸ range ((range f).subtype.lcomp k N) := by
  let e := rangeHomEquivCocycles (k := k) (N := N) f
  refine (Submodule.Quotient.equiv _ _ e ?_).symm
  ext h
  constructor
  · rintro ⟨g, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, by simp [e, lcomp_apply', comp_assoc]⟩
  · rintro ⟨a, ha⟩
    refine ⟨a.comp (range f).subtype, ⟨a, rfl⟩, ?_⟩
    apply Subtype.ext
    simpa [e, lcomp_apply', comp_assoc] using ha

/-- The inverse comparison pulls a map on the image back to its cocycle class. -/
@[simp]
theorem homCocycleQuotientEquivRange_symm_mk (f : P₁ →ₗ[A] P₀)
    (h : range f →ₗ[A] N) :
    (homCocycleQuotientEquivRange (k := k) f).symm (Submodule.Quotient.mk h) =
      Submodule.Quotient.mk (rangeHomEquivCocycles (k := k) f h) := by
  simp [homCocycleQuotientEquivRange, Submodule.Quotient.equiv_apply]

/-- A cocycle obtained from a map on the image descends to that map's class. -/
@[simp]
theorem homCocycleQuotientEquivRange_mk (f : P₁ →ₗ[A] P₀) (h : range f →ₗ[A] N) :
    homCocycleQuotientEquivRange (k := k) f
        (Submodule.Quotient.mk (rangeHomEquivCocycles (k := k) f h)) =
      Submodule.Quotient.mk h := by
  apply (homCocycleQuotientEquivRange (k := k) f).symm.injective
  simp

end LinearMap
