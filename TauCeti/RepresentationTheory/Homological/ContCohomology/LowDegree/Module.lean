/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AddSubgroupQuotient
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree

/-!
# Scalar actions on the explicit `H¹` and `H²`

The explicit groups `H¹(G, M) = Z¹/B¹` and `H²(G, M) = Z²/B²` of
`TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree` are defined for a bare
topological abelian group `M` with a continuous action of `G`; no coefficient ring enters the
definition. When `M` is moreover a module over a semiring `R`, the action of `G` commutes with
that of `R` and each scalar acts continuously, the scalar `r` acts on `H¹(G, M)` and `H²(G, M)`
through the coefficient map of the equivariant endomorphism `r • ·` of `M`, that is, by
`r • [z] = [r • z]` on the class of a cocycle `z`. This file installs these actions as instances,
so that the explicit groups, not a copy of them, carry the `R`-module structure.

## Main definitions

* `TauCeti.ContCohomology.H1.instModule` and `TauCeti.ContCohomology.H2.instModule`: `H¹(G, M)`
  and `H²(G, M)` are `R`-modules.

## Main results

* `TauCeti.ContCohomology.H1.smul_mk` and `TauCeti.ContCohomology.H2.smul_mk`: a scalar acts on
  the class of a cocycle as on the cocycle.
* `TauCeti.ContCohomology.smul_mem_Z1`, `smul_mem_B1`, `smul_mem_Z2`, `smul_mem_B2`: cocycles and
  coboundaries are stable under the scalars.

## Implementation notes

The module structure is built from explicit stability proofs by `AddSubgroup.quotientModule`, and
the instances only supply those proofs. Two instances built this way for the same scalar action
on `M` are therefore definitionally equal whatever proofs they were given. The `ZMod n`-module
structures `TauCeti.instModuleH1` and `TauCeti.ContCohomology.instModuleZModH2` are
`H1.instModule` and `H2.instModule` at `R = ZMod n`, so they agree with them by `rfl`.

At `R = ℤ` the instances differ from the `ℤ`-module structure `AddCommGroup.toIntModule` that
every abelian group carries: the two agree only propositionally, by Mathlib's `int_smul_eq_zsmul`
or `AddCommGroup.uniqueIntModule`. The instances therefore have low priority, so that
`Module ℤ (H1 G M)` and `ℤ`-scalar multiplication keep resolving to the structure of the abelian
group.
## References

The design, in which the cohomology is defined once for abelian groups and the `R`-module
structure is supplied by instances where it exists, follows David Loeffler's advice in
[#Riemann-Hypothesis > Library design discrepancies between RH/Mathlib/TauCeti](https://leanprover.zulipchat.com/#narrow/channel/658556-Riemann-Hypothesis/topic/Library.20design.20discrepancies.20between.20RH.2FMathlib.2FTauCeti/near/643780293).
It builds on the explicit groups of the existing Tau Ceti file
`TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree`.
-/

public section

namespace TauCeti.ContCohomology

universe u v w

/-! ### Stability of cocycles and coboundaries -/

section Stability

variable {R : Type w} {G : Type u} {M : Type v} [AddCommGroup M] [DistribSMul R M]

/-- `d⁰` commutes with the scalars when the action of `G` does. -/
theorem d0_smul [DistribSMul G M] [SMulCommClass G R M] (r : R) (m : M) :
    d0 G M (r • m) = r • d0 G M m := by
  ext g
  exact (map_d0_apply (DistribSMul.toAddMonoidHom M r) (fun g m ↦ (smul_comm g r m).symm) m g).symm

/-- `d¹` commutes with the scalars when the action of `G` does. -/
theorem d1_smul [Mul G] [DistribSMul G M] [SMulCommClass G R M] (r : R) (f : G → M) :
    d1 G M (r • f) = r • d1 G M f := by
  ext ⟨g, h⟩
  exact (map_d1_apply (DistribSMul.toAddMonoidHom M r) (fun g m ↦ (smul_comm g r m).symm)
    f g h).symm

/-- `d²` commutes with the scalars when the action of `G` does. -/
theorem d2_smul [Mul G] [DistribSMul G M] [SMulCommClass G R M] (r : R) (f : G × G → M) :
    d2 G M (r • f) = r • d2 G M f := by
  ext ⟨g, h, j⟩
  simp [d2_apply, smul_add, smul_sub, smul_comm g r]

/-- The `1`-coboundaries are stable under the scalars. -/
theorem smul_mem_B1 [DistribSMul G M] [SMulCommClass G R M] (r : R) {f : G → M}
    (hf : f ∈ B1 G M) : r • f ∈ B1 G M := by
  obtain ⟨m, hm⟩ := mem_B1_iff.1 hf
  obtain rfl : d0 G M m = f := funext fun g ↦ (d0_apply m g).trans (hm g)
  rw [← d0_smul]
  exact d0_mem_B1 _

variable [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M]

/-- The continuous `1`-cocycles are stable under continuous scalars. -/
theorem smul_mem_Z1 [Mul G] [DistribSMul G M] [SMulCommClass G R M] (r : R) {f : G → M}
    (hf : f ∈ Z1 G M) : r • f ∈ Z1 G M := by
  obtain ⟨hc, hd⟩ := mem_Z1_iff.1 hf
  refine mem_Z1_iff.2 ⟨hc.const_smul r, d1_apply_eq_zero_iff.1 ?_⟩
  rw [d1_smul, d1_apply_eq_zero_iff.2 hd, smul_zero]

/-- The continuous `2`-cocycles are stable under continuous scalars. -/
theorem smul_mem_Z2 [Mul G] [DistribSMul G M] [SMulCommClass G R M] (r : R) {f : G × G → M}
    (hf : f ∈ Z2 G M) : r • f ∈ Z2 G M := by
  obtain ⟨hc, hd⟩ := mem_Z2_iff.1 hf
  refine mem_Z2_iff.2 ⟨hc.const_smul r, d2_apply_eq_zero_iff.1 ?_⟩
  rw [d2_smul, d2_apply_eq_zero_iff.2 hd, smul_zero]

/-- The `2`-coboundaries are stable under continuous scalars. -/
theorem smul_mem_B2 [Mul G] [DistribSMul G M] [SMulCommClass G R M] (r : R) {f : G × G → M}
    (hf : f ∈ B2 G M) : r • f ∈ B2 G M := by
  obtain ⟨c, hc, rfl⟩ := mem_B2_iff.1 hf
  exact mem_B2_iff.2 ⟨r • c, hc.const_smul r, d1_smul r c⟩

end Stability

/-! ### The module structures -/

section Instances

variable {R : Type w} [Semiring R] {G : Type u} [Monoid G] [TopologicalSpace G]
  {M : Type v} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- **`H¹(G, M)` is an `R`-module** when `M` is one, with continuous scalars commuting with the
action of `G`: `r` acts on the class of a cocycle `z` as the class of `r • z`. -/
instance (priority := 100) H1.instModule [SMulCommClass G R M] [ContinuousConstSMul R M] :
    Module R (H1 G M) :=
  AddSubgroup.quotientModule (Z1 G M) (B1 G M) (fun r _ hz ↦ smul_mem_Z1 r hz)
    (fun r _ hb ↦ smul_mem_B1 r hb)

/-- A scalar acts on the class of a `1`-cocycle as on the cocycle. -/
@[simp]
theorem H1.smul_mk [SMulCommClass G R M] [ContinuousConstSMul R M] (r : R) (z : Z1 G M) :
    r • (z : H1 G M) = ((⟨r • (z : G → M), smul_mem_Z1 r z.property⟩ : Z1 G M) : H1 G M) :=
  AddSubgroup.quotientModule_smul_mk _ _ _ _ r z

variable [ContinuousMul G]

/-- **`H²(G, M)` is an `R`-module** when `M` is one, with continuous scalars commuting with the
action of `G`: `r` acts on the class of a cocycle `z` as the class of `r • z`. -/
instance (priority := 100) H2.instModule [SMulCommClass G R M] [ContinuousConstSMul R M] :
    Module R (H2 G M) :=
  AddSubgroup.quotientModule (Z2 G M) (B2 G M) (fun r _ hz ↦ smul_mem_Z2 r hz)
    (fun r _ hb ↦ smul_mem_B2 r hb)

/-- A scalar acts on the class of a `2`-cocycle as on the cocycle. -/
@[simp]
theorem H2.smul_mk [SMulCommClass G R M] [ContinuousConstSMul R M] (r : R) (z : Z2 G M) :
    r • (z : H2 G M) = ((⟨r • (z : G × G → M), smul_mem_Z2 r z.property⟩ : Z2 G M) : H2 G M) :=
  AddSubgroup.quotientModule_smul_mk _ _ _ _ r z

end Instances

end TauCeti.ContCohomology
