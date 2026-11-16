/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.Valuation.Discrete.Basic
import TauCeti.RingTheory.Valuation.NontrivialComap

/-!
# Restriction of rank-one discrete valuations

Pulling back a valuation `v` on `S` along a ring homomorphism `f : R →+* S` produces a valuation
`v.comap f` whose value group is a subgroup of the value group of `v`. When `v` is rank-one
discrete, its value group is cyclic, so the value group of `v.comap f` is automatically cyclic;
thus `v.comap f` is rank-one discrete if and only if it is nontrivial.

Without a finiteness or integrality condition on `f`, the pullback can collapse to the trivial
valuation (for instance, the `t`-adic valuation on `K(t)` restricts trivially to `K`). Along an
integral algebra `L / K`, nontriviality is preserved (`Valuation.isNontrivial_comap_algebraMap`),
so a rank-one discrete valuation on `L` restricts to a rank-one discrete valuation on `K`.

## Main results

* `Valuation.valueGroup_comap_le`: the value group of `v.comap f` is a subgroup of the value group
  of `v`.
* `Valuation.isRankOneDiscrete_comap` and `Valuation.isRankOneDiscrete_comap_iff`: the pullback of
  a rank-one discrete valuation along a ring homomorphism is rank-one discrete if and only if it is
  nontrivial.
* `Valuation.isRankOneDiscrete_comap_algebraMap`: the restriction of a rank-one discrete valuation
  along an integral algebra is rank-one discrete.

## References

* [A. J. Engler and A. Prestel, *Valued Fields*][engler2005].
-/

public section

namespace Valuation

section RingHom

variable {R S Γ : Type*} [Ring R] [Ring S] [LinearOrderedCommGroupWithZero Γ]

/-- The value group of the pullback `v.comap f` is a subgroup of the value group of `v`. -/
theorem valueGroup_comap_le (v : Valuation S Γ) (f : R →+* S) :
    (v.comap f).valueGroup ≤ v.valueGroup :=
  (Subgroup.closure_le v.valueGroup).mpr fun _ ⟨r, hr⟩ ↦
    MonoidWithZeroHom.mem_valueGroup _ ⟨f r, hr⟩

/-- The pullback of a rank-one discrete valuation along a ring homomorphism is rank-one discrete
whenever it is nontrivial. -/
theorem isRankOneDiscrete_comap (v : Valuation S Γ) [v.IsRankOneDiscrete] (f : R →+* S)
    [(v.comap f).IsNontrivial] : (v.comap f).IsRankOneDiscrete :=
  have : IsCyclic (v.comap f).valueGroup :=
    isCyclic_of_injective (Subgroup.inclusion (v.valueGroup_comap_le f))
      (Subgroup.inclusion_injective _)
  .mk' (v.comap f)

/-- The pullback of a rank-one discrete valuation along a ring homomorphism is rank-one discrete
if and only if it is nontrivial. -/
theorem isRankOneDiscrete_comap_iff (v : Valuation S Γ) [v.IsRankOneDiscrete] (f : R →+* S) :
    (v.comap f).IsRankOneDiscrete ↔ (v.comap f).IsNontrivial :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ v.isRankOneDiscrete_comap f⟩

end RingHom

section Integral

variable {K L Γ : Type*} [CommRing K] [Ring L] [Algebra K L]
  [LinearOrderedCommGroupWithZero Γ]

/-- **The restriction of a rank-one discrete valuation along an integral algebra is rank-one
discrete.** -/
theorem isRankOneDiscrete_comap_algebraMap [Algebra.IsIntegral K L] (v : Valuation L Γ)
    [v.IsRankOneDiscrete] : (v.comap (algebraMap K L)).IsRankOneDiscrete :=
  have : (v.comap (algebraMap K L)).IsNontrivial := v.isNontrivial_comap_algebraMap
  v.isRankOneDiscrete_comap (algebraMap K L)

end Integral

end Valuation
