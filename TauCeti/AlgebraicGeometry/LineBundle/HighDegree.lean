/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.SerreDuality
public import TauCeti.FieldTheory.FunctionField.Consequences.HighDegree

/-!
# Cohomology of line bundles of high degree

On a proper integral curve with discrete valuation stalks and constant field `k`, a line bundle
`L` of degree greater than `2g - 2` has `H¹(X, L) = 0` and `dim H⁰(X, L) = deg L + 1 - g`.
These are the fibrewise vanishing and dimension calculations for the large-degree Abel maps.
No rational point is required.

The degree is the Euler-characteristic degree, identified with divisor degree by the
line-bundle dictionary. The proof transports the function-field high-degree theorem through
`SchemeWeilDivisor.finrank_cohomology_zero_sheaf_eq_dim` and
`SchemeWeilDivisor.cohomologyOneDualEquivWeilDifferentialFiltration`. In particular, the
vanishing conclusion is actual subsingleton cohomology, rather than a potentially junk value
of `finrank`.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter IV, Corollary 1.3.4.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Theorem 1.5.17.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Order
open Module (finrank)

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]

variable [IsIntegral X]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
  (hdim : ∀ x : X, coheight x ≤ 1)
  (hF : IsFunctionField k X.functionField) (hk : IsIntegrallyClosedIn k X.functionField)

include hdim hF hk

/-- A line bundle of degree greater than `2g - 2` on a proper integral curve with constant field
`k` has no first cohomology. The genus is `dim H¹(X, 𝒪_X)`; a rational point is not needed. -/
theorem subsingleton_cohomology_one_of_two_mul_genus_sub_two_lt_eulerDegree
    (L : InvertibleSheaf X)
    (hL : 2 * (finrank k (Scheme.Modules.Cohomology (trivial X).obj 1) : ℤ) - 2 <
      L.eulerDegree k) :
    Subsingleton (Scheme.Modules.Cohomology L.obj 1) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := compactSpace_of_universallyClosed (X ↘ Spec (.of k))
  have : IsNoetherian X := {}
  have : X.IsSeparated :=
    ⟨by rw [← terminal.comp_from (X ↘ Spec (.of k))]; infer_instance⟩
  let hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)) :=
    (UniversallyClosed.eq_valuativeCriterion ▸
      (inferInstance : UniversallyClosed (X ↘ Spec (.of k)))).1
  have := (Scheme.Modules.finiteDimensional_cohomology_congr k
    (SchemeWeilDivisor.sheafZeroIsoTrivial hdim) 1).mp
      (SchemeWeilDivisor.finiteDimensional_cohomology_one_sheaf_of_isFunctionField hex hdim hF 0)
  obtain ⟨D, ⟨e⟩⟩ := SchemeWeilDivisor.exists_nonempty_iso_sheaf hdim L
  have hdeg : 2 * (genus k X.functionField : ℤ) - 1 ≤
      Divisor.degree (SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim D) := by
    rw [SchemeWeilDivisor.degree_equivFunctionFieldDivisor hex hdim,
      ← eulerDegree_eq_relativeDegree k hdim e,
      ← SchemeWeilDivisor.genus_eq_genus_functionField hex hdim hF hk, Scheme.genus_def]
    omega
  have hzero := Divisor.indexOfSpecialty_eq_zero_of_two_mul_genus_sub_one_le_degree hF hk hdeg
  have hdimzero := finrank_weilDifferentialFiltration hF hk
    (SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim D)
  rw [hzero] at hdimzero
  have := SchemeWeilDivisor.finiteDimensional_cohomology_one_sheaf_of_isFunctionField hex hdim hF D
  have hdual := (SchemeWeilDivisor.cohomologyOneDualEquivWeilDifferentialFiltration
    hex hdim hF D).finrank_eq
  rw [Subspace.dual_finrank_eq] at hdual
  have hDzero : finrank k (Scheme.Modules.Cohomology (SchemeWeilDivisor.sheaf D) 1) = 0 := by
    omega
  have hLzero : finrank k (Scheme.Modules.Cohomology L.obj 1) = 0 :=
    (Scheme.Modules.finrank_cohomology_congr k e 1).trans hDzero
  have := finiteDimensional_cohomology_one k hdim L
  exact Module.finrank_zero_iff.mp hLzero

/-- On a proper integral curve with constant field `k`, a line bundle of degree greater than
`2g - 2` has `dim H⁰(X, L) = deg L + 1 - g`, without requiring a rational point. The equality
uses integers, so subtraction is not truncated. -/
theorem finrank_cohomology_zero_eq_eulerDegree_add_one_sub_genus
    (L : InvertibleSheaf X)
    (hL : 2 * (finrank k (Scheme.Modules.Cohomology (trivial X).obj 1) : ℤ) - 2 <
      L.eulerDegree k) :
    (finrank k (Scheme.Modules.Cohomology L.obj 0) : ℤ) = L.eulerDegree k + 1 -
      finrank k (Scheme.Modules.Cohomology (trivial X).obj 1) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := compactSpace_of_universallyClosed (X ↘ Spec (.of k))
  have : IsNoetherian X := {}
  have : X.IsSeparated :=
    ⟨by rw [← terminal.comp_from (X ↘ Spec (.of k))]; infer_instance⟩
  let hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)) :=
    (UniversallyClosed.eq_valuativeCriterion ▸
      (inferInstance : UniversallyClosed (X ↘ Spec (.of k)))).1
  have := (Scheme.Modules.finiteDimensional_cohomology_congr k
    (SchemeWeilDivisor.sheafZeroIsoTrivial hdim) 1).mp
      (SchemeWeilDivisor.finiteDimensional_cohomology_one_sheaf_of_isFunctionField hex hdim hF 0)
  obtain ⟨D, ⟨e⟩⟩ := SchemeWeilDivisor.exists_nonempty_iso_sheaf hdim L
  have hdeg : 2 * (genus k X.functionField : ℤ) - 1 ≤
      Divisor.degree (SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim D) := by
    rw [SchemeWeilDivisor.degree_equivFunctionFieldDivisor hex hdim,
      ← eulerDegree_eq_relativeDegree k hdim e,
      ← SchemeWeilDivisor.genus_eq_genus_functionField hex hdim hF hk, Scheme.genus_def]
    omega
  rw [Scheme.Modules.finrank_cohomology_congr k e 0,
    SchemeWeilDivisor.finrank_cohomology_zero_sheaf_eq_dim hex hdim]
  have h := Divisor.dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree hF hk hdeg
  rw [SchemeWeilDivisor.degree_equivFunctionFieldDivisor hex hdim,
    ← eulerDegree_eq_relativeDegree k hdim e,
    ← SchemeWeilDivisor.genus_eq_genus_functionField hex hdim hF hk, Scheme.genus_def] at h
  exact h

end TauCeti.AlgebraicGeometry.InvertibleSheaf
