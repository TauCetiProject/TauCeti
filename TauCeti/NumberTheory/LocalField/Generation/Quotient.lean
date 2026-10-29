/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.WildInertia
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Quotient

/-!
# Finite local Galois quotients through the arithmetic class-module extension

Let `P_K` be wild inertia and `U` an open normal subgroup of the absolute Galois group
`G_K`. If `⁅P_K, P_K⁆ ≤ U`, the image of `V = P_K U` in `G_K/U` is an abelian
`p`-group, for `p` the residue characteristic. Consequently `G_K/U` is a quotient of
`G_K / ker(V → Vᵃᵇ(p))`.

This is the last quotient in the integral generator argument: a surjection from a free
profinite group onto the arithmetic class-module extension supplies a generating tuple
in `G_K/U` by composition with `QuotientGroup.mapOfLE`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  proof of (7.4.1).
-/

public section

open ValuativeRel

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (p : ℕ) [CharP 𝓀[K] p]

/-- If a finite local Galois quotient kills the commutator of wild inertia, it is a
quotient of the arithmetic pro-`p` class-module extension at `P_K U`. -/
theorem abelianizationProPExtensionKernel_le_of_commutator_wildInertiaSubgroup_le
    (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (hU : ⁅wildInertiaSubgroup K, wildInertiaSubgroup K⁆ ≤ U.toSubgroup) :
    abelianizationProPExtensionKernel p (Field.absoluteGaloisGroup K)
      (wildInertiaSubgroup K ⊔ U.toSubgroup) ≤ U.toSubgroup := by
  let q := QuotientGroup.mk' U.toSubgroup
  have hmap : (wildInertiaSubgroup K ⊔ U.toSubgroup).map q =
      (wildInertiaSubgroup K).map q := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  apply abelianizationProPExtensionKernel_le_of_isPGroup_map
  · rw [hmap]
    exact (isProP_wildInertiaSubgroup K p).isPGroup_map_mk' U
  · have hcomm :
        ⁅wildInertiaSubgroup K ⊔ U.toSubgroup,
          wildInertiaSubgroup K ⊔ U.toSubgroup⁆.map q = ⊥ := by
      rw [Subgroup.map_commutator, hmap, ← Subgroup.map_commutator]
      exact (Subgroup.map_eq_bot_iff _).mpr (by simpa [q] using hU)
    simpa [q] using (Subgroup.map_eq_bot_iff _).mp hcomm

end TauCeti
