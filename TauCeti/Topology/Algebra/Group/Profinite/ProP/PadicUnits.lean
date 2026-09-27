/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.PrincipalUnits
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic

/-!
# Pro-`p` groups and the unit group `ℤ_pˣ`

Every open normal subgroup of `ℤ_2ˣ` contains a principal unit group `U^(f) = 1 + 2^f ℤ_2`,
whose index is `2 ^ (f - 1)`, so every continuous finite quotient of `ℤ_2ˣ` is a `2`-group. This
is what makes `ℤ_2ˣ` an admissible target for continuous characters of pro-`2` groups, such as
the orientation character of a dyadic Demushkin group. For odd `p` the unit group `ℤ_pˣ` is not
pro-`p`, since it contains the roots of unity of order `p - 1`. In the other direction, a
continuous character of a pro-`p` group into `ℤ_pˣ` has pro-`p` range, so it takes values in the
principal units `1 + pℤ_p`.

## Main results

* `TauCeti.isProP_units_padicInt_two`: `ℤ_2ˣ` is a pro-`2` group.
* `TauCeti.IsProP.mem_unitsPrincipal_one`: a continuous character of a pro-`p` group into `ℤ_pˣ`
  takes values in the principal units `1 + pℤ_p`.
-/

public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [TopologicalSpace G]

/-- A continuous character of a pro-`p` group takes values in the principal units `1 + pℤ_p`: its
range is a pro-`p` subgroup of `ℤ_pˣ`. -/
theorem IsProP.mem_unitsPrincipal_one (hG : IsProP p G) (χ : G →ₜ* ℤ_[p]ˣ) (g : G) :
    χ g ∈ unitsPrincipal p 1 :=
  have : IsProP p χ.toMonoidHom.range :=
    hG.of_surjective χ.toMonoidHom.rangeRestrict (continuous_induced_rng.mpr χ.continuous)
      χ.toMonoidHom.rangeRestrict_surjective
  this.le_unitsPrincipal_one ⟨g, rfl⟩

/-- **`ℤ_2ˣ` is pro-`2`**: every open normal subgroup contains a principal unit group `U^(f)`, of
index `2 ^ (f - 1)`. -/
theorem isProP_units_padicInt_two : IsProP 2 ℤ_[2]ˣ := by
  refine isProP_iff.mpr fun U ↦ ?_
  obtain ⟨f, -, hf⟩ := (hasBasis_nhds_one_unitsPrincipal 2).mem_iff.mp
    (U.isOpen.mem_nhds (one_mem _))
  refine IsPGroup.of_card_dvd_pow (n := f - 1) ?_
  rw [← Subgroup.index_eq_card, ← index_unitsPrincipal_two f]
  exact Subgroup.index_dvd_of_le hf

end TauCeti
