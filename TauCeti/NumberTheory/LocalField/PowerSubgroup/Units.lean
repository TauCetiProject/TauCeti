/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.RootsOfUnity.Torsion

/-!
# Power classes of the units of a local field

Let `K` be a nonarchimedean local field and let `n` be invertible in `𝒪[K]`, that is, prime to
the residue characteristic. This file counts the `n`-th power classes of the units
`U(K,0) = 𝒪[K]ˣ`, the depth-zero step of the unit filtration:

`#(U(K,0) ⧸ U(K,0)ⁿ) = #μ_n(K)`.

The Teichmüller splitting `U(K,0) ≃ μ_{q-1}(K) × U(K,1)` reduces the count to the finite factor.
The `n`-th power map is a bijection of the principal units `U(K,1)`. In the finite group
`μ_{q-1}(K)` the `n`-th powers have index equal to the number of `n`-torsion elements, and these
are the `n`-th roots of unity of `K`. Compared with `TauCeti.card_powerClasses_of_isUnit`,
`#(Kˣ ⧸ (Kˣ)ⁿ) = n · #μ_n(K)`, the missing factor `n` is the contribution of the valuation.

When `K` contains the `n`-th roots of unity, the count is `n`. This is the size of each local
factor of the target of the map from global `S`-units to unit power classes at an auxiliary set of
places, in the Kummer-theoretic proof of the second fundamental inequality.

## Main results

* `TauCeti.card_unitFiltration_zero_powerClasses_of_isUnit`: `#(U(K,0) ⧸ U(K,0)ⁿ) = #μ_n(K)` for
  `n` invertible in `𝒪[K]`.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §2.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §6.
-/

public section

open IsLocalRing ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **The number of `n`-th power classes of units away from the residue characteristic.** For
`n` invertible in `𝒪[K]`, the quotient of the units `U(K,0)` by their `n`-th powers has
`#μ_n(K)` elements, where `μ_n(K)` is the group of `n`-th roots of unity of `K`. -/
theorem card_unitFiltration_zero_powerClasses_of_isUnit {n : ℕ} (hn : IsUnit (n : 𝒪[K])) :
    Nat.card (unitFiltration K 0 ⧸
        (powMonoidHom n : unitFiltration K 0 →* unitFiltration K 0).range) =
      Nat.card (rootsOfUnity n K) := by
  set μ := rootsOfUnity (Nat.card 𝓀[K] - 1) K
  set V := unitFiltration K 1
  have : Finite μ := .of_equiv _
    (TauCeti.rootsOfUnityAlgebraMulEquivUnitsResidueField 𝒪[K] K).symm.toEquiv
  -- On `μ_{q-1}(K) × U(K,1)` the power map is componentwise, and it is onto `U(K,1)`.
  have hrange : (powMonoidHom n : μ × V →* μ × V).range =
      (powMonoidHom n : μ →* μ).range.prod ⊤ := by
    have hprod : (powMonoidHom n : μ × V →* μ × V) =
        (powMonoidHom n).prodMap (powMonoidHom n) := by
      ext <;> simp
    rw [hprod, MonoidHom.range_prodMap, MonoidHom.range_eq_top.mpr
      (powMonoidHom_unitFiltration_succ_bijective_of_isUnit hn 0).2]
  -- The `n`-torsion of `μ_{q-1}(K)` is `μ_n(K)`, all of which lies in `μ_{q-1}(K)`.
  have hker : (powMonoidHom n : μ →* μ).ker = (rootsOfUnity n K).subgroupOf μ := by
    ext x
    simp [Subgroup.mem_subgroupOf, mem_rootsOfUnity, Subtype.ext_iff]
  rw [← Subgroup.index_eq_card,
    ← Subgroup.index_map_equiv _ (unitFiltrationZeroEquivProd K).toMulEquiv,
    MulEquiv.map_range_powMonoidHom, hrange, Subgroup.index_prod, Subgroup.index_top, mul_one,
    Subgroup.index_range, hker]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (rootsOfUnity_le_rootsOfUnity_natCard_residueField_sub_one hn)).toEquiv

end TauCeti
