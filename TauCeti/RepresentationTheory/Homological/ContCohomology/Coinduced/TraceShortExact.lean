/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.FiniteIndex
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Torsion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ShortExact
public import TauCeti.Topology.Algebra.GroupAction.QuotientAddGroup

/-!
# The trace short exact sequence of an open subgroup

For an open subgroup `U` of finite index in a topological group `G` and a discrete `G`-module `M`,
the trace `Coind_U^G M → M` of `TauCeti.DiscreteCoind.trace` is surjective
(`TauCeti.DiscreteCoind.trace_surjective`). Its kernel `TauCeti.DiscreteCoind.traceKer` is a
`G`-stable additive subgroup of the coinduced module, hence a discrete `G`-module in its own right,
and the three fit into the short exact sequence

```text
0 → traceKer G U M → Coind_U^G M → M → 0
```

of discrete `G`-modules, `TauCeti.DiscreteCoind.traceShortExact`. Its long exact cohomology
sequence compares `Hⁿ(G, Coind_U^G M) ≅ Hⁿ(U, M)` with `Hⁿ(G, M)` through the cohomology of the
kernel; this is how the cohomological dimension of `G` is bounded by that of an open subgroup
(Serre, *Galois Cohomology*, Ch. I, §3.3, Prop. 14).

## Main definitions

* `TauCeti.DiscreteCoind.traceKer`: the kernel of the trace, a `G`-stable additive subgroup of
  `Coind_U^G M`, with the restricted action of `G` and its continuity as instances.
* `TauCeti.DiscreteCoind.traceShortExact`: the short exact sequence
  `0 → traceKer G U M → Coind_U^G M → M → 0` for an open subgroup `U`.

## Main results

* `TauCeti.DiscreteCoind.isPPrimaryTorsion_traceKer`: over a compact group the kernel of the trace
  of a discrete `p`-primary torsion module is `p`-primary torsion.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.3, Prop. 14.
-/

public section

namespace TauCeti.DiscreteCoind

universe u v

variable (G : Type u) [Group G] [TopologicalSpace G] [ContinuousMul G] (U : Subgroup G)
  [U.FiniteIndex] (M : Type v) [AddCommGroup M] [DistribMulAction G M]

/-! ### The kernel of the trace -/

/-- **The kernel of the trace** `Coind_U^G M → M`, as an additive subgroup of the coinduced
module. It is `G`-stable (`TauCeti.DiscreteCoind.smul_mem_traceKer`), and carries the restricted
action of `G` as an instance. -/
noncomputable def traceKer : AddSubgroup (DiscreteCoind G U M) := (trace G U M).toAddMonoidHom.ker

variable {G U M}

@[simp]
theorem mem_traceKer_iff {f : DiscreteCoind G U M} : f ∈ traceKer G U M ↔ trace G U M f = 0 :=
  Iff.rfl

/-- The kernel of the trace is stable under the action of `G`, the trace being equivariant. -/
theorem smul_mem_traceKer (g : G) {f : DiscreteCoind G U M} (hf : f ∈ traceKer G U M) :
    g • f ∈ traceKer G U M := by
  rw [mem_traceKer_iff] at hf ⊢
  rw [_root_.map_smul, hf, smul_zero]

variable (G U M)

/-- The action of `G` on the kernel of the trace, by restriction. -/
noncomputable instance : DistribMulAction G (traceKer G U M) :=
  (traceKer G U M).restrictDistribMulAction fun g _ hf ↦ smul_mem_traceKer g hf

/-- The inclusion of the kernel of the trace in `Coind_U^G M` is equivariant. -/
@[simp]
theorem coe_smul_traceKer (g : G) (f : traceKer G U M) :
    ((g • f : traceKer G U M) : DiscreteCoind G U M) = g • (f : DiscreteCoind G U M) :=
  rfl

/-- Over a compact group, the kernel of the trace of a discrete `p`-primary torsion module is
`p`-primary torsion, as a subgroup of the `p`-primary torsion module `Coind_U^G M`. -/
theorem isPPrimaryTorsion_traceKer {p : ℕ} [CompactSpace G] [TopologicalSpace M]
    [DiscreteTopology M] (hM : IsPPrimaryTorsion p M) : IsPPrimaryTorsion p (traceKer G U M) :=
  (isPPrimaryTorsion_discreteCoind G U M hM).of_injective (traceKer G U M).subtype
    Subtype.val_injective

/-! ### The short exact sequence -/

variable [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- **The trace short exact sequence** `0 → traceKer G U M → Coind_U^G M → M → 0` of discrete
`G`-modules, for an open subgroup `U` of finite index and a discrete `G`-module `M`. The second
map is the trace, surjective because `U` is open. -/
noncomputable def traceShortExact (hU : IsOpen (U : Set G)) :
    ContCohomology.DiscreteShortExact G (traceKer G U M) (DiscreteCoind G U M) M where
  incl := (traceKer G U M).subtype
  proj := (trace G U M).toAddMonoidHom
  incl_equivariant _ _ := rfl
  proj_equivariant g f := _root_.map_smul (trace G U M) g f
  incl_injective := Subtype.val_injective
  proj_surjective := trace_surjective hU
  exact f := ⟨fun hf ↦ ⟨⟨f, hf⟩, rfl⟩, by rintro ⟨a, rfl⟩; exact a.2⟩

variable (hU : IsOpen (U : Set G))

/-- The first map of the trace short exact sequence is the inclusion of the kernel. -/
@[simp]
theorem traceShortExact_incl : (traceShortExact G U M hU).incl = (traceKer G U M).subtype :=
  (rfl)

/-- The second map of the trace short exact sequence is the trace. -/
@[simp]
theorem traceShortExact_proj :
    (traceShortExact G U M hU).proj = (trace G U M).toAddMonoidHom :=
  (rfl)

section Compact

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (U : Subgroup G) [U.FiniteIndex] (M : Type v) [AddCommGroup M] [DistribMulAction G M]

/-- Over a compact group the restricted action on the kernel of the trace is continuous, the
kernel being a discrete module. -/
instance : ContinuousSMul G (traceKer G U M) :=
  (traceKer G U M).restrictDistribMulAction_continuousSMul fun g _ hf ↦ smul_mem_traceKer g hf

end Compact

end TauCeti.DiscreteCoind
