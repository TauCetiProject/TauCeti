/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Effectivity
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.Basic

/-!
# Effective representatives of line bundles

On a proper regular integral curve with constant global functions and finite first cohomology
of its structure sheaf, every line bundle of degree at least the genus is the sheaf of an
effective Weil divisor, over `k` itself. Neither an algebraically closed ground field nor a
rational point is needed. The representative has the same degree as the line bundle, with
residue-field degrees included in divisor degree.

This is the effective-representative input to surjectivity of the Abel maps. Divisors in this
file are Weil divisors, or Cartier divisors given by local rational equations; no relative
closed subscheme or representability assertion is made.

The construction uses `SchemeWeilDivisor.exists_nonempty_iso_sheaf` to pass to divisor sheaves
and `SchemeWeilDivisor.nonempty_completeLinearSystem_of_genus_le_relativeDegree` for effectivity.
The Weil–Cartier correspondence then gives an effective Cartier divisor representative.

## References

* R. Hartshorne, *Algebraic Geometry*, II.6.11 and IV.1.3 (Riemann–Roch).
* J. S. Milne, *Jacobian Varieties*, Section 5 (surjectivity of the Abel maps).
-/

public section

open CategoryTheory AlgebraicGeometry Order
open Module (finrank)

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

universe u

variable {X : Scheme.{u}} [IsIntegral X]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]

variable {k : Type u} [Field k] [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]
  (hdim : ∀ x : X, coheight x ≤ 1)
  [FiniteDimensional k (Scheme.Modules.Cohomology (trivial X).obj 1)]
  (hφ : Function.Surjective (Scheme.Modules.baseRingToGlobalSections k X))

include hdim hφ in
/-- On a proper regular integral curve with constant global functions, a line bundle of degree
at least the genus is represented by an effective Weil divisor of that degree, with the same
line-bundle class. -/
theorem exists_isEffective_iso_sheaf_of_genus_le_eulerDegree (L : InvertibleSheaf X)
    (hL : (finrank k (Scheme.Modules.Cohomology (trivial X).obj 1) : ℤ) ≤ L.eulerDegree k) :
    letI : IsNoetherian X :=
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
        toCompactSpace := compactSpace_of_universallyClosed (X ↘ Spec (.of k)) }
    ∃ D : SchemeWeilDivisor X, WeilDivisor.IsEffective D ∧
      Nonempty (L.obj ≅ SchemeWeilDivisor.sheaf D) ∧
        SchemeWeilDivisor.relativeDegree (X ↘ Spec (.of k)) D = L.eulerDegree k ∧
          SchemeWeilDivisor.toLineBundleClass hdim D = LineBundleClass.mk L := by
  have : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
      toCompactSpace := compactSpace_of_universallyClosed (X ↘ Spec (.of k)) }
  obtain ⟨D, ⟨e⟩⟩ := SchemeWeilDivisor.exists_nonempty_iso_sheaf hdim L
  have hdegree := eulerDegree_eq_relativeDegree k hdim e
  obtain ⟨E, hE⟩ := SchemeWeilDivisor.nonempty_completeLinearSystem_of_genus_le_relativeDegree
    k hdim hφ (D := D) (by simpa only [Scheme.genus_def, ← hdegree] using hL)
  obtain ⟨hEff, hlin⟩ := (WeilDivisor.OrderSystem.ofScheme X).mem_completeLinearSystem.mp hE
  obtain ⟨eE⟩ := SchemeWeilDivisor.nonempty_iso_sheaf_of_linearlyEquivalent hlin
  refine ⟨E, hEff, ⟨e ≪≫ eE⟩, (eulerDegree_eq_relativeDegree k hdim (e ≪≫ eE)).symm, ?_⟩
  apply (SchemeWeilDivisor.toLineBundleClass_eq_mk_iff hdim).mpr
  exact ⟨eqToIso (SchemeWeilDivisor.toInvertibleSheaf_obj hdim E) ≪≫ (e ≪≫ eE).symm⟩

include hdim hφ in
/-- A line bundle of degree at least the genus on a proper regular curve with constant global
functions has an effective Cartier divisor representative. Cartier divisors here are local rational
equations, and the assertion concerns their line-bundle classes. -/
theorem exists_isEffective_cartierDivisor_of_genus_le_eulerDegree (L : InvertibleSheaf X)
    (hL : (finrank k (Scheme.Modules.Cohomology (trivial X).obj 1) : ℤ) ≤ L.eulerDegree k) :
    ∃ D : Scheme.CartierDivisor X, D.IsEffective ∧ D.toLineBundleClass = LineBundleClass.mk L := by
  have : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
      toCompactSpace := compactSpace_of_universallyClosed (X ↘ Spec (.of k)) }
  obtain ⟨D, hD, -, -, hclass⟩ :=
    exists_isEffective_iso_sheaf_of_genus_le_eulerDegree hdim hφ L hL
  refine ⟨SchemeWeilDivisor.equivCartierDivisor hdim D,
    (SchemeWeilDivisor.isEffective_equivCartierDivisor_iff hdim D).mpr hD, ?_⟩
  rw [Scheme.CartierDivisor.toLineBundleClass_eq_toWeilDivisor hdim,
    ← SchemeWeilDivisor.equivCartierDivisor_symm_apply hdim,
    AddEquiv.symm_apply_apply]
  exact hclass

end TauCeti.AlgebraicGeometry.InvertibleSheaf
