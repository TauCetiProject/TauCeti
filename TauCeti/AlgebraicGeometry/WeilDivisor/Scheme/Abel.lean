/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Effective

/-!
# Surjectivity of the normalized Abel map on line-bundle classes

Let `X` be a proper regular integral curve over `k` with constant global functions and finite
first cohomology of its structure sheaf, and fix a divisor `B` of
degree `d ≥ g`. Every degree-zero line-bundle class is `𝒪_X(E - B)` for an effective divisor `E`
of degree `d`. In particular, taking `B = d[x₀]` gives the class-level surjectivity assertion
underlying the normalized degree-`d` Abel map. The normalization need not itself be effective,
and a rational point is not required if a divisor `B` of the desired degree is already given.

The statement is over the ground field, with residue-degree-weighted divisor degree. It concerns
actual line bundles, rather than all points of the fppf Picard sheaf. It does not assert
surjectivity of a morphism of schemes or identify effective divisors with relative closed
subschemes. Those comparisons are needed to pass from this result to a scheme-level Abel map.

The proof applies the effective-representative theorem to `L ⊗ 𝒪_X(B)`, where `L` represents the
given degree-zero class, and uses the divisor/line-bundle degree comparison.

## References

* J. S. Milne, *Jacobian Varieties*, Section 5.
* R. Hartshorne, *Algebraic Geometry*, IV.1.3.
-/

public section

open CategoryTheory AlgebraicGeometry Order
open Module (finrank)

namespace TauCeti.AlgebraicGeometry.SchemeWeilDivisor

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsIntegral X] [IsNoetherian X] [IsProper (X ↘ Spec (.of k))]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
  (hdim : ∀ x : X, coheight x ≤ 1)
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
  (hφ : Function.Surjective (Scheme.Modules.baseRingToGlobalSections k X))

include hφ in
/-- The normalized Abel map on line-bundle classes is onto when the normalization divisor has
degree at least the genus. The effective preimage has the same degree as the normalization. -/
theorem exists_isEffective_toLineBundleClass_div_eq (B : SchemeWeilDivisor X)
    (hB : (finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) : ℤ) ≤
      relativeDegree (X ↘ Spec (.of k)) B)
    (a : LineBundleClass X) (ha : LineBundleClass.eulerDegree k a = 0) :
    ∃ E : SchemeWeilDivisor X, WeilDivisor.IsEffective E ∧
      relativeDegree (X ↘ Spec (.of k)) E = relativeDegree (X ↘ Spec (.of k)) B ∧
        toLineBundleClass hdim E / toLineBundleClass hdim B = a := by
  obtain ⟨L, hL⟩ := LineBundleClass.mk_surjective (a * toLineBundleClass hdim B)
  have hdegree : L.eulerDegree k = relativeDegree (X ↘ Spec (.of k)) B := by
    rw [← LineBundleClass.eulerDegree_mk, hL,
      LineBundleClass.eulerDegree_mul k hdim, ha,
      LineBundleClass.eulerDegree_toLineBundleClass, zero_add]
  obtain ⟨E, hE, ⟨e⟩, hdegE⟩ :=
    InvertibleSheaf.exists_isEffective_iso_sheaf_of_genus_le_eulerDegree hdim hφ L
      (hdegree.symm ▸ hB)
  refine ⟨E, hE, hdegE.trans hdegree, ?_⟩
  have hclass : toLineBundleClass hdim E = LineBundleClass.mk L := by
    apply (toLineBundleClass_eq_mk_iff hdim).mpr
    exact ⟨eqToIso (toInvertibleSheaf_obj hdim E) ≪≫ e.symm⟩
  rw [hclass, hL, mul_div_cancel_right]

end TauCeti.AlgebraicGeometry.SchemeWeilDivisor
