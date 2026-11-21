/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Effectivity
public import TauCeti.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.LineBundle.SectionDegree
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

For proper integral curves, including singular curves, the section-theoretic construction also
produces an actual effective Cartier ideal of colength `deg L`, assuming finite-dimensional
`H⁰(𝒪_X)` and `H¹(𝒪_X)` but not constant global functions. This is the form needed by the
functor of relative effective Cartier divisors, rather than just the Weil divisor dictionary.

## References

* R. Hartshorne, *Algebraic Geometry*, II.6.11 and IV.1.3 (Riemann–Roch).
* J. S. Milne, *Jacobian Varieties*, Section 5 (surjectivity of the Abel maps).
-/

public section

open CategoryTheory AlgebraicGeometry Order
open Module (finrank)

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

universe u

section CartierIdeal

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsProper (X ↘ Spec (.of k))] [RelativeDimensionLE 1 (X ↘ Spec (.of k))]
  [FiniteDimensional k (Scheme.Modules.Cohomology (trivial X).obj 0)]
  [FiniteDimensional k (Scheme.Modules.Cohomology (trivial X).obj 1)]

/-- On a proper integral curve with finite-dimensional `H⁰(𝒪_X)` and `H¹(𝒪_X)`, a line bundle
of degree at least `dim H¹(𝒪_X)` has an effective Cartier zero subscheme of that degree. The
ideal sheaf of this subscheme has class `L⁻¹`. Neither regularity, constant global functions,
nor a rational point is required. -/
theorem exists_isEffectiveCartier_eulerDegree_eq_of_genus_le (L : InvertibleSheaf X)
    (hL : (finrank k (Scheme.Modules.Cohomology (trivial X).obj 1) : ℤ) ≤ L.eulerDegree k) :
    ∃ (I : X.IdealSheafData) (hI : I.IsEffectiveCartier),
      LineBundleClass.mk hI.toInvertibleSheaf = (LineBundleClass.mk L)⁻¹ ∧
        L.eulerDegree k = (I.subschemeι ≫ X ↘ Spec (.of k)).finrank default := by
  let _ : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.choice inferInstance, by simp⟩⟩
  let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have : Nontrivial Γ(M, ⊤) := inferInstanceAs (Nontrivial Γ(X, ⊤))
  have : Nontrivial (Scheme.Modules.Cohomology M 0) :=
    (Scheme.Modules.cohomologyZeroEquiv M).toEquiv.nontrivial
  have : FiniteDimensional k (Scheme.Modules.Cohomology M 0) :=
    (Scheme.Modules.finiteDimensional_cohomology_congr k (trivialObjIsoUnit X) 0).mp inferInstance
  have h₀ : 0 < finrank k (Scheme.Modules.Cohomology (trivial X).obj 0) := by
    rw [Scheme.Modules.finrank_cohomology_congr k (trivialObjIsoUnit X) 0]
    exact Module.finrank_pos
  have hdeg := L.eulerDegree_eq_finrank_sub k
  have hpos : 0 < finrank k (Scheme.Modules.Cohomology L.obj 0) := by omega
  have := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨s, hs⟩ := exists_ne (0 : Scheme.Modules.Cohomology L.obj 0)
  exact L.exists_isEffectiveCartier_eulerDegree_eq_of_ne_zero k
    (Scheme.Modules.cohomologyZeroEquiv L.obj s)
    (by simpa using hs)

end CartierIdeal

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
theorem exists_nonneg_iso_sheaf_of_genus_le_eulerDegree (L : InvertibleSheaf X)
    (hL : (finrank k (Scheme.Modules.Cohomology (trivial X).obj 1) : ℤ) ≤ L.eulerDegree k) :
    letI : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
    ∃ D : SchemeWeilDivisor X, 0 ≤ D ∧
      Nonempty (L.obj ≅ SchemeWeilDivisor.sheaf D) ∧
        SchemeWeilDivisor.relativeDegree (X ↘ Spec (.of k)) D = L.eulerDegree k ∧
          SchemeWeilDivisor.toLineBundleClass hdim D = LineBundleClass.mk L := by
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
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
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  obtain ⟨D, hD, -, -, hclass⟩ :=
    exists_nonneg_iso_sheaf_of_genus_le_eulerDegree hdim hφ L hL
  refine ⟨SchemeWeilDivisor.equivCartierDivisor hdim D,
    (SchemeWeilDivisor.isEffective_equivCartierDivisor_iff hdim D).mpr hD, ?_⟩
  rw [Scheme.CartierDivisor.toLineBundleClass_eq_toWeilDivisor hdim,
    ← SchemeWeilDivisor.equivCartierDivisor_symm_apply hdim,
    AddEquiv.symm_apply_apply]
  exact hclass

end TauCeti.AlgebraicGeometry.InvertibleSheaf
