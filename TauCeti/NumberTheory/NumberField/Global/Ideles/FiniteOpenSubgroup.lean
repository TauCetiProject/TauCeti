/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.TotallyPositive
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup
import Mathlib.NumberTheory.NumberField.ClassNumber
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Topology
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

/-!
# Open subgroups of the finite ideles of a number field

Let `K` be a number field, `𝔸_{K,f}ˣ` its finite ideles, and `Kˣ ⊂ 𝔸_{K,f}ˣ` the principal finite
ideles. An open subgroup `H` of `𝔸_{K,f}ˣ` that contains the principal finite ideles of the totally
positive elements of `K` has finite index. Total positivity stands in for the archimedean
components, which the finite ideles do not see.

The proof climbs from `H` to `𝔸_{K,f}ˣ` in three steps of finite index. The first,
`H ≤ H · Kˣ`, has index at most that of the totally positive elements in `Kˣ`, which is finite
(`NumberField.finiteIndex_totallyPositiveUnits`, the sign group at the real places). The second,
`H · Kˣ ≤ H · Kˣ · 𝒪̂ˣ`, has index at most that of the open subgroup `H ∩ 𝒪̂ˣ` of the compact
group `𝒪̂ˣ` of everywhere-integral units. The last is above `Kˣ · 𝒪̂ˣ`, whose quotient is the
finite class group
(`IsDedekindDomain.FiniteAdeleRing.finiteIndex_integralUnits_sup_range_unitEmbedding`).

Together with the facts already in the library this gives the standard facts about open subgroups
of the finite ideles: the group `U^S` of finite ideles that are local units outside `S` is open
(`TauCeti.isOpen_sIntegralUnits`) and compact for `S = ∅` (`TauCeti.isCompact_integralUnits`),
and a character with open kernel is trivial on `𝒪_vˣ` for almost every `v`
(`IsDedekindDomain.FiniteAdeleRing.eventually_unitsOfAdicCompletion_mem_of_isOpen`).

## Main results

* `NumberField.finiteIndex_of_isOpen_of_totallyPositiveUnits_le`: an open subgroup of the finite
  ideles containing the totally positive principal finite ideles has finite index.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic
PBC), file `src/Lib/ClassField/Places/Ideles.lean`, `New.finiteIndex_idele_subgroup_of_isOpen`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §16.
-/

public section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open scoped NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Open subgroups of the finite ideles containing the totally positive principal ideles have
finite index.** If `H` is an open subgroup of `𝔸_{K,f}ˣ` and the principal finite idele of every
totally positive `x ∈ Kˣ` lies in `H`, then `H` has finite index. -/
theorem finiteIndex_of_isOpen_of_totallyPositiveUnits_le
    {H : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ} (hH : IsOpen (H : Set (FiniteAdeleRing (𝓞 K) K)ˣ))
    (hpos : totallyPositiveUnits ≤ H.comap (unitEmbedding (𝓞 K) K)) : H.FiniteIndex := by
  set P := (unitEmbedding (𝓞 K) K).range
  set U := integralUnits (𝓞 K) K
  -- `[H ⊔ P : H] = [P : H ⊓ P]`, the index of the preimage of `H` in `Kˣ`.
  have h₁ : H.relIndex (H ⊔ P) ≠ 0 := by
    rw [Subgroup.relIndex_sup_left, ← Subgroup.index_comap]
    exact (Subgroup.finiteIndex_of_le hpos).index_ne_zero
  -- `[H ⊔ P ⊔ U : H ⊔ P] = [U : (H ⊔ P) ⊓ U]`, finite as `U` is compact and `H ⊔ P` open.
  have h₂ : (H ⊔ P).relIndex (H ⊔ P ⊔ U) ≠ 0 := by
    rw [Subgroup.relIndex_sup_left]
    exact Subgroup.relIndex_ne_zero_of_isOpen_of_isCompact
      (Subgroup.isOpen_mono le_sup_left hH) (TauCeti.isCompact_integralUnits (𝓞 K) K)
  -- `H ⊔ P ⊔ U` contains `U ⊔ P`, the kernel of the map to the finite class group.
  have h₃ : (H ⊔ P ⊔ U).FiniteIndex :=
    have := finiteIndex_integralUnits_sup_range_unitEmbedding (𝓞 K) K
    Subgroup.finiteIndex_of_le (sup_le le_sup_right (le_sup_right.trans le_sup_left))
  rw [Subgroup.finiteIndex_iff, ← Subgroup.relIndex_mul_index (le_sup_left : H ≤ H ⊔ P),
    ← Subgroup.relIndex_mul_index (le_sup_left : H ⊔ P ≤ H ⊔ P ⊔ U)]
  exact mul_ne_zero h₁ (mul_ne_zero h₂ h₃.index_ne_zero)

end NumberField
