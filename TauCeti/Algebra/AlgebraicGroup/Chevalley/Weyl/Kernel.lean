/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.TitsSystem

/-!
# The kernel of the Chevalley Weyl projection

For a Chevalley datum `D` and a field `k`, let `N = D.weylSubgroup k` be the subgroup generated
by the actual torus `T = T_D(k)` and the pinned simple Weyl representatives `nᵢ = nᵢ(1)`, and let
`B = D.borelSubgroup k`. Over every field the kernel of the Weyl projection `N → W` is exactly `T`
(`TauCeti.DynkinType.ChevalleyDatum.ker_weylProjection`), and `B ∩ N = T`
(`TauCeti.DynkinType.ChevalleyDatum.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints`). This
file records the pointwise form of the first statement and the normality of `B ∩ N` in `N` that
follows from the second.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.weylProjection_eq_one_iff_mem_range_torusPoints`: a point of
  `N` has trivial Weyl projection exactly when it is a torus point.
* `TauCeti.DynkinType.ChevalleyDatum.normal_borelSubgroup_subgroupOf_weylSubgroup`: `B ∩ N` is
  normal in `N`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3.
* R. W. Carter, *Simple Groups of Lie Type*, §7.2 and §8.1.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (k : Type v) [Field k]

/-- A point of `N` has trivial Weyl projection exactly when it is a torus point. -/
theorem weylProjection_eq_one_iff_mem_range_torusPoints (g : D.weylSubgroup k) :
    D.weylProjection k g = 1 ↔ (g : D.points k) ∈ (D.torusPoints k).range := by
  rw [← MonoidHom.mem_ker, ker_weylProjection, Subgroup.mem_subgroupOf]

/-- `B ∩ N` is normal in `N`: it is the actual torus, which `N` normalizes. This is the normality
axiom of a Tits system with these subgroups. -/
instance normal_borelSubgroup_subgroupOf_weylSubgroup :
    ((D.borelSubgroup k).subgroupOf (D.weylSubgroup k)).Normal := by
  rw [← Subgroup.inf_subgroupOf_left, inf_comm,
    D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints k]
  infer_instance

end TauCeti.DynkinType.ChevalleyDatum
