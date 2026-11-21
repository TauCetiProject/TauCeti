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

/-- Postcomposition preserves the Hom cocycle condition. -/
theorem homCocycleComp_mem {f : P₁ →ₗ[A] P₀} (g : N →ₗ[A] N') {h : P₁ →ₗ[A] N}
    (hh : h ∈ ker ((ker f).subtype.lcomp k N)) :
    g.comp h ∈ ker ((ker f).subtype.lcomp k N') := by
  simp only [mem_ker, lcomp_apply'] at hh ⊢
  rw [comp_assoc, hh, comp_zero]

/-- Postcomposition on Hom cocycles modulo coboundaries. -/
def homCocycleQuotientMap (f : P₁ →ₗ[A] P₀) (g : N →ₗ[A] N') :
    HomCocycleQuotient (k := k) f N →ₗ[k] HomCocycleQuotient (k := k) f N' :=
  Submodule.mapQ _ _ ((g.compRight k).restrict fun _ hh ↦ by
    simpa only [compRight_apply] using homCocycleComp_mem g hh) <| by
    rintro h ⟨a, ha⟩
    refine ⟨g.comp a, ?_⟩
    simp only [lcomp_apply', Submodule.subtype_apply, coe_restrict_apply, compRight_apply] at ha ⊢
    rw [comp_assoc, ha]

/-- Postcomposition sends a cocycle class to the class of the composite. -/
@[simp]
theorem homCocycleQuotientMap_mk (f : P₁ →ₗ[A] P₀) (g : N →ₗ[A] N')
    (h : ker ((ker f).subtype.lcomp k N)) :
    homCocycleQuotientMap f g (Submodule.Quotient.mk h) =
      Submodule.Quotient.mk
        (⟨g.comp h.val, homCocycleComp_mem g h.property⟩ :
          ker ((ker f).subtype.lcomp k N')) := by
  simp [homCocycleQuotientMap, restrict_apply]

/-- Postcomposition with the identity preserves cocycle classes. -/
@[simp]
theorem homCocycleQuotientMap_id (f : P₁ →ₗ[A] P₀) :
    homCocycleQuotientMap (k := k) f (LinearMap.id : N →ₗ[A] N) = LinearMap.id := by
  ext
  simp

/-- Postcomposition on cocycle classes respects composition. -/
@[simp]
theorem homCocycleQuotientMap_comp (f : P₁ →ₗ[A] P₀)
    (g : N →ₗ[A] N') (h : N' →ₗ[A] N'') :
    homCocycleQuotientMap (k := k) f (h.comp g) =
      (homCocycleQuotientMap f h).comp (homCocycleQuotientMap f g) := by
  ext
  simp [comp_assoc]

end LinearMap
