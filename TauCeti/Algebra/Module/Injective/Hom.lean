/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Exactness of Hom into an injective module

A map into an injective module factors through `f` exactly when it vanishes on
`ker f`. In particular, precomposition with `f` has image the kernel of restriction
to `ker f`. This applies to presenting maps that are not monomorphisms, as occur in
projective presentations over non-hereditary algebras.
-/

public section

namespace LinearMap

universe u v w t s

variable {R : Type u} [Ring R] {P : Type v} {Q : Type w} {I : Type t}
  [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
  [AddCommGroup I] [Module R I] [Small.{t} R] [Module.Injective R I]

/-- A map into an injective module factors through `f` exactly when it kills `ker f`. -/
theorem exists_comp_eq_iff_ker_le (f : P →ₗ[R] Q) (g : P →ₗ[R] I) :
    (∃ h : Q →ₗ[R] I, h.comp f = g) ↔ ker f ≤ ker g := by
  constructor
  · rintro ⟨h, rfl⟩ x hx
    simp [mem_ker.mp hx]
  · intro hg
    let g' := (ker f).liftQ g hg |>.comp f.quotKerEquivRange.symm.toLinearMap
    obtain ⟨h, hh⟩ := Module.Injective.extension_property R I _ _
      (range f).subtype (range f).injective_subtype g'
    refine ⟨h, LinearMap.ext fun x ↦ ?_⟩
    have hx := LinearMap.congr_fun hh ⟨f x, mem_range_self f x⟩
    simpa [g', quotKerEquivRange_symm_apply_image] using hx

variable {k : Type s} [CommRing k] [Algebra k R] [Module k I] [IsScalarTower k R I]

/-- Precomposition into an injective module has image exactly the maps vanishing on
the kernel of the original map. The Hom spaces are linear over the ground ring. -/
theorem range_lcomp_eq_ker_lcomp_ker_subtype (f : P →ₗ[R] Q) :
    range (f.lcomp k I) = ker ((ker f).subtype.lcomp k I) := by
  ext g
  rw [mem_range, mem_ker]
  simp only [lcomp_apply']
  rw [exists_comp_eq_iff_ker_le]
  simpa only [Submodule.range_subtype] using
    (range_le_ker_iff (f := (ker f).subtype) (g := g))

variable {N : Type*} [AddCommGroup N] [Module R N]
  [Module k N] [IsScalarTower k R N]

/-- After embedding the coefficient module into an injective module, the inverse image
of the precomposition range is exactly the maps vanishing on the original kernel. -/
theorem comap_range_lcomp_compRight (f : P →ₗ[R] Q) (j : N →ₗ[R] I)
    (hj : Function.Injective j) :
    (range (f.lcomp k I)).comap (j.compRight k) =
      ker ((ker f).subtype.lcomp k N) := by
  rw [range_lcomp_eq_ker_lcomp_ker_subtype]
  ext F
  simp only [Submodule.mem_comap, mem_ker, lcomp_apply', compRight_apply]
  constructor
  · intro h
    ext x
    apply hj
    simpa using LinearMap.congr_fun h x
  · intro h
    ext x
    have hx : F x = 0 := LinearMap.congr_fun h x
    simpa only [comp_apply, Submodule.subtype_apply, zero_apply, map_zero] using congrArg j hx

end LinearMap
