/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Hom cocycles modulo coboundaries

For an arrow `f : P₁ → P₀`, Hom cocycles with coefficients in `N` are the maps
`P₁ → N` vanishing on `ker f`. Coboundaries are the maps obtained by precomposition
with `f`. Postcomposition induces a covariant map on their quotient.
The quotient map, induction principle and universal property are those of `Submodule`.

For a projective presentation, the cocycle condition distinguishes the quotient
computing `Ext¹` from the full Hom cokernel. Its scalar dual is the coefficient
side of the Auslander–Reiten pairing. The construction itself needs neither
projectivity nor an exactness or finiteness hypothesis.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.2.
-/

public section

namespace LinearMap

variable {k A P₀ P₁ N N' N'' : Type*} [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup P₀] [Module A P₀] [AddCommGroup P₁] [Module A P₁]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  [AddCommGroup N'] [Module A N'] [Module k N'] [IsScalarTower k A N']
  [AddCommGroup N''] [Module A N''] [Module k N''] [IsScalarTower k A N'']

/-- Maps vanishing on the kernel of `f`, modulo maps extending across `f`. -/
abbrev HomCocycleQuotient (f : P₁ →ₗ[A] P₀) (N : Type*)
    [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N] :=
  ker ((ker f).subtype.lcomp k N) ⧸
    (range (f.lcomp k N)).comap (ker ((ker f).subtype.lcomp k N)).subtype

/-- Postcomposition on Hom cocycles modulo coboundaries. -/
def homCocycleQuotientMap (f : P₁ →ₗ[A] P₀) (g : N →ₗ[A] N') :
    HomCocycleQuotient (k := k) f N →ₗ[k] HomCocycleQuotient (k := k) f N' := by
  let Z := ker ((ker f).subtype.lcomp k N)
  let Z' := ker ((ker f).subtype.lcomp k N')
  let F := ((g.compRight k).comp Z.subtype).codRestrict Z' fun h ↦ by
    apply mem_ker.mpr
    simpa only [comp_apply, compRight_apply, Submodule.subtype_apply, lcomp_apply',
      comp_assoc, comp_zero]
      using congrArg (g.comp ·) (mem_ker.mp h.property)
  exact ((range (f.lcomp k N)).comap Z.subtype).mapQ
    ((range (f.lcomp k N')).comap Z'.subtype) F (by
      rintro h ⟨a, ha⟩
      refine ⟨g.comp a, ?_⟩
      simpa only [F, codRestrict_apply, comp_apply, compRight_apply,
        Submodule.subtype_apply, lcomp_apply',
        comp_assoc] using congrArg (g.comp ·) ha)

/-- Postcomposition sends a cocycle class to the class of the composite. -/
@[simp]
theorem homCocycleQuotientMap_mk (f : P₁ →ₗ[A] P₀) (g : N →ₗ[A] N')
    (h : ker ((ker f).subtype.lcomp k N)) :
    homCocycleQuotientMap f g (Submodule.Quotient.mk h) =
      Submodule.Quotient.mk
        (⟨g.comp h.val, by
          apply mem_ker.mpr
          simpa only [lcomp_apply', comp_assoc, comp_zero]
            using congrArg (g.comp ·) (mem_ker.mp h.property)⟩ :
          ker ((ker f).subtype.lcomp k N')) := by
  simp only [homCocycleQuotientMap, Submodule.mapQ_apply]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  simp [codRestrict_apply, compRight_apply]

/-- Postcomposition with the identity preserves cocycle classes. -/
@[simp]
theorem homCocycleQuotientMap_id (f : P₁ →ₗ[A] P₀) :
    homCocycleQuotientMap (k := k) f (LinearMap.id : N →ₗ[A] N) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ h => simp

/-- Postcomposition on cocycle classes respects composition. -/
@[simp]
theorem homCocycleQuotientMap_comp (f : P₁ →ₗ[A] P₀)
    (g : N →ₗ[A] N') (h : N' →ₗ[A] N'') :
    homCocycleQuotientMap (k := k) f (h.comp g) =
      (homCocycleQuotientMap f h).comp (homCocycleQuotientMap f g) := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ a => simp [comp_assoc]

end LinearMap
