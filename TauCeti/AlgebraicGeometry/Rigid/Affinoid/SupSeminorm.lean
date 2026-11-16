/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.Presheaf
public import TauCeti.RingTheory.Affinoid.SupSeminorm

import TauCeti.RingTheory.Affinoid.MaximumModulus

/-!
# The supremum norm on an affinoid subdomain

For an affinoid subdomain `U` of `Sp B`, the supremum norm of a function on `U` is the supremum
seminorm of its restriction to the chosen algebra of sections over `U`. Since the classical
points of that algebra are exactly the points of `U`, this supremum norm is computed at the
classical points of `U`; for strict bounds this uses the maximum modulus principle.

## Main results

* `TauCeti.AffinoidSubdomain.supSeminorm_toSections_lt_iff`: the supremum norm of a function on
  an affinoid subdomain is less than `r` exactly when its absolute values at the classical points
  of the subdomain are.
* `TauCeti.AffinoidSubdomain.supSeminorm_toSections_le_iff`: the same for non-strict bounds.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§6.2.1 and
  7.2.2.
-/

public section

namespace TauCeti

namespace AffinoidSubdomain

universe u

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {B : Type u} [CommRing B] [Algebra K B]

/-- **The supremum norm on an affinoid subdomain is computed at its classical points.** For an
affinoid subdomain `U` of `Sp B` and `r > 0`, the restriction of `b` to `U` has supremum
seminorm less than `r` exactly when `|b(y)| < r` at every classical point `y` of `U`. -/
theorem supSeminorm_toSections_lt_iff (hB : IsAffinoidAlgebra K B) (U : AffinoidSubdomain K B)
    (b : B) {r : ℝ} (hr : 0 < r) :
    supSeminorm K (U.toSections b) < r ↔ ∀ y ∈ U, pointNorm K y b < r := by
  have hU (y : MaximalSpectrum B) :
      y ∈ U ↔ y ∈ Set.range (U.isAffinoidAlgebra.maximalSpectrumComap U.toSections) := by
    rw [U.isAffinoidSubdomainMap.range_maximalSpectrumComap hB, SetLike.mem_coe]
  simp_rw [U.isAffinoidAlgebra.supSeminorm_lt_iff hr, hU, Set.forall_mem_range,
    IsAffinoidAlgebra.pointNorm_maximalSpectrumComap]

/-- For an affinoid subdomain `U` of `Sp B` and `r ≥ 0`, the restriction of `b` to `U` has
supremum seminorm at most `r` exactly when `|b(y)| ≤ r` at every classical point `y` of `U`. -/
theorem supSeminorm_toSections_le_iff (hB : IsAffinoidAlgebra K B) (U : AffinoidSubdomain K B)
    (b : B) {r : ℝ} (hr : 0 ≤ r) :
    supSeminorm K (U.toSections b) ≤ r ↔ ∀ y ∈ U, pointNorm K y b ≤ r := by
  have hU (y : MaximalSpectrum B) :
      y ∈ U ↔ y ∈ Set.range (U.isAffinoidAlgebra.maximalSpectrumComap U.toSections) := by
    rw [U.isAffinoidSubdomainMap.range_maximalSpectrumComap hB, SetLike.mem_coe]
  simp_rw [U.isAffinoidAlgebra.supSeminorm_le_iff hr, hU, Set.forall_mem_range,
    IsAffinoidAlgebra.pointNorm_maximalSpectrumComap]

end AffinoidSubdomain

end TauCeti
