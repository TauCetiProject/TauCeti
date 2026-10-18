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
projective presentations over non-hereditary algebras. As a further consequence, an
annihilator inclusion characterizes the existence of a linear map with one prescribed value.
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
  · rintro ⟨h, rfl⟩
    exact ker_le_ker_comp f h
  · intro hg
    let g' := (ker f).liftQ g hg |>.comp f.quotKerEquivRange.symm.toLinearMap
    obtain ⟨h, hh⟩ := Module.Injective.extension_property R I _ _
      (range f).subtype (range f).injective_subtype g'
    refine ⟨h, LinearMap.ext fun x ↦ ?_⟩
    have hx := LinearMap.congr_fun hh ⟨f x, mem_range_self f x⟩
    simpa [g', quotKerEquivRange_symm_apply_image] using hx

variable {k : Type s} [Semiring k] [Module k I] [SMulCommClass R k I]

/-- Precomposition into an injective module has image exactly the maps vanishing on
the kernel of the original map. The Hom spaces are linear over a semiring whose action
commutes with the module action. -/
theorem range_lcomp_eq_ker_lcomp_ker_subtype (f : P →ₗ[R] Q) :
    range (f.lcomp k I) = ker ((ker f).subtype.lcomp k I) := by
  ext g
  simp only [mem_range, mem_ker, lcomp_apply', exists_comp_eq_iff_ker_le,
    le_ker_iff_comp_subtype_eq_zero]

variable {N : Type*} [AddCommGroup N] [Module R N]
  [Module k N] [SMulCommClass R k N] [CompatibleSMul N I k R]

/-- After embedding the coefficient module into an injective module, the inverse image
of the precomposition range is exactly the maps vanishing on the original kernel. -/
theorem comap_range_lcomp_compRight (f : P →ₗ[R] Q) (j : N →ₗ[R] I)
    (hj : Function.Injective j) :
    (range (f.lcomp k I)).comap (j.compRight k) =
      ker ((ker f).subtype.lcomp k N) := by
  rw [range_lcomp_eq_ker_lcomp_ker_subtype]
  ext F
  simp only [Submodule.mem_comap, mem_ker, lcomp_apply', compRight_apply]
  simpa only [comp_assoc, comp_zero] using
    (cancel_left (f := j) (g := F.comp (ker f).subtype) (g' := 0) hj)

end LinearMap

namespace TauCeti

universe u v w

/-- A linear map into an injective module can send `a` to `x` exactly when every scalar
killing `a` also kills `x`. -/
theorem exists_linearMap_apply_eq_iff_forall_smul_eq_zero {S : Type u} [Ring S]
    {M : Type w} [AddCommGroup M] [Module S M] {Q : Type v}
    [AddCommGroup Q] [Module S Q] [Small.{v} S] [Module.Injective S Q]
    {a : M} {x : Q} :
    (∃ f : M →ₗ[S] Q, f a = x) ↔ ∀ s : S, s • a = 0 → s • x = 0 := by
  simpa only [LinearMap.comp_toSpanSingleton,
    (LinearMap.toSpanSingleton_injective S Q).eq_iff, IsConcreteLE.le_iff,
    LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] using
    (LinearMap.exists_comp_eq_iff_ker_le
      (LinearMap.toSpanSingleton S M a) (LinearMap.toSpanSingleton S Q x))

end TauCeti
