/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Geometrically.GlobalSections
public import TauCeti.AlgebraicGeometry.Cohomology.Genus
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.Finiteness

/-!
# Riemann–Roch without a rational point

On a geometrically integral proper curve with discrete valuation stalks, every divisor `D`
satisfies `dim H⁰(𝒪_X(D)) - dim H¹(𝒪_X(D)) = deg D + 1 - g`. Here the degree is the
residue-degree-weighted divisor degree and the genus is `dim H¹(𝒪_X)`.

No rational point or perfectness assumption on the ground field is needed. Finiteness of the
cohomology follows from properness and the divisor-sheaf finiteness theorems. Geometric
integrality supplies the constant term `1`, through the bijectivity of the canonical map to
global functions. Consequently every divisor of degree at least the genus is linearly
equivalent to an effective divisor, even on a curve without a rational point. This is the
point-free effectivity input for Abel maps from spaces of effective divisors.

The proof uses `SchemeWeilDivisor.eulerCharBelow_sheaf_eq_relativeDegree_add` and
`Scheme.baseRingToGlobalSections_bijective_of_geometricallyIntegral`.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter IV, Theorem 1.3 and Corollary 1.3.2.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Chapter 7, Theorem 3.17.
-/

public section

open CategoryTheory AlgebraicGeometry Order
open Module (finrank)

namespace TauCeti.AlgebraicGeometry.SchemeWeilDivisor

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsIntegral X] [IsProper (X ↘ Spec (.of k))]
  [GeometricallyIntegral (X ↘ Spec (.of k))]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  (hdim : topologicalKrullDim X = 1)

include hdim

/-- Riemann–Roch on a geometrically integral proper curve with discrete valuation stalks,
without a rational point. Both cohomology groups are finite dimensional under these hypotheses.
The genus is written as a dimension so callers need not supply a finiteness instance. -/
theorem finrank_cohomology_zero_sheaf_sub_finrank_cohomology_one_sheaf_of_geometricallyIntegral
    (D : SchemeWeilDivisor X) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    (finrank k (Scheme.Modules.Cohomology (sheaf D) 0) : ℤ) -
        (finrank k (Scheme.Modules.Cohomology (sheaf D) 1) : ℤ) =
      relativeDegree (X ↘ Spec (.of k)) D + 1 -
        finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) := by
  let _ : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have hcoheight (x : X) : coheight x ≤ 1 := by
    exact_mod_cast (coheight_le_topologicalKrullDim x).trans hdim.le
  have := finiteDimensional_cohomology_one_trivial_of_isProper k hdim
  rw [← Scheme.Modules.eulerCharBelow_two,
    eulerCharBelow_sheaf_eq_relativeDegree_add k hcoheight D,
    Scheme.Modules.eulerCharBelow_two,
    finrank_cohomology_zero_trivial_eq_one_of_surjective k
      (X.baseRingToGlobalSections_bijective_of_geometricallyIntegral k).surjective]
  push_cast
  ring

/-- Riemann's inequality on a geometrically integral proper curve, without assuming a rational
point: a divisor has at least `deg D + 1 - g` independent global sections. -/
theorem relativeDegree_add_one_sub_genus_le_finrank_cohomology_zero_sheaf_of_geometricallyIntegral
    (D : SchemeWeilDivisor X) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    relativeDegree (X ↘ Spec (.of k)) D + 1 -
        finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) ≤
      (finrank k (Scheme.Modules.Cohomology (sheaf D) 0) : ℤ) := by
  let _ : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have h :=
    finrank_cohomology_zero_sheaf_sub_finrank_cohomology_one_sheaf_of_geometricallyIntegral
      k hdim D
  have := Int.natCast_nonneg (finrank k (Scheme.Modules.Cohomology (sheaf D) 1))
  omega

/-- Every divisor of degree at least the genus on a geometrically integral proper curve with
discrete valuation stalks is linearly equivalent to an effective divisor. A rational point is
not required. -/
theorem nonempty_completeLinearSystem_of_genus_le_relativeDegree_of_geometricallyIntegral
    {D : SchemeWeilDivisor X}
    (hD : (finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) : ℤ) ≤
      relativeDegree (X ↘ Spec (.of k)) D) :
    letI : IsNoetherian X :=
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
        toCompactSpace := compactSpace_of_universallyClosed (X ↘ Spec (.of k)) }
    ((WeilDivisor.OrderSystem.ofScheme X).completeLinearSystem D).Nonempty := by
  let _ : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
      toCompactSpace := compactSpace_of_universallyClosed (X ↘ Spec (.of k)) }
  have hcoheight (x : X) : coheight x ≤ 1 := by
    exact_mod_cast (coheight_le_topologicalKrullDim x).trans hdim.le
  have := finiteDimensional_globalSections_sheaf k hcoheight D
  rw [nonempty_completeLinearSystem_iff_nontrivial_globalSections_sheaf,
    ← Module.finrank_pos_iff_of_free (R := k),
    ← Scheme.Modules.finrank_cohomology_zero_eq_finrank_globalSections]
  have h :=
    relativeDegree_add_one_sub_genus_le_finrank_cohomology_zero_sheaf_of_geometricallyIntegral
      k hdim D
  omega

end TauCeti.AlgebraicGeometry.SchemeWeilDivisor
