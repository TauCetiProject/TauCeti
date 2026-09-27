/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Topology.Instances.ZMod
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree

/-!
# `H²(G, ZMod n)` as a `ZMod n`-module

A continuous `2`-cocycle with values in an abelian group killed by `n` is itself killed by `n`,
and so is its class, so `H²(G, M)` is an abelian group of exponent dividing `n`
(`TauCeti.ContCohomology.nsmul_H2_eq_zero`). That statement is made for a general coefficient
module, so that it also covers coefficients such as the invariants `M ^ N` carried by the
cohomology of a quotient group. For the coefficients `M = ZMod n` it makes `H²(G, ZMod n)` a
module over `ZMod n`, and for `n` a prime `p` an `𝔽_p`-vector space, so that `Module.rank`,
`Module.finrank` and `Module.Finite` apply to it. For a pro-`p` group `G` that dimension is the
relation rank of `G`.

The module structure is the canonical one: `Module (ZMod n) A` is a subsingleton on an abelian
group `A` (`ZMod.instSubsingletonModule`), so it agrees with every other way of producing one,
and scalar multiplication by a natural number is the iterated sum (`Nat.cast_smul_eq_nsmul`).

## Main results

* `TauCeti.ContCohomology.nsmul_H2_eq_zero`: `H²(G, M)` is killed by `n` when the coefficients
  are.
* `TauCeti.ContCohomology.instModuleZModH2`: `H²(G, ZMod n)` is a `ZMod n`-module.
-/

public section

namespace TauCeti.ContCohomology

universe u v

variable {n : ℕ} {G : Type u} [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- **`H²` inherits the exponent of its coefficients.** If `n` kills the coefficient module `M`,
then it kills every class in `H²(G, M)`. -/
theorem nsmul_H2_eq_zero (h : ∀ m : M, n • m = 0) (x : H2 G M) : n • x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    have hc : n • c = 0 := Subtype.ext (funext fun _ ↦ by simp [h])
    rw [← QuotientAddGroup.mk_nsmul, hc, QuotientAddGroup.mk_zero]

/-- `H²(G, ZMod n)` is a `ZMod n`-module, for any continuous action of `G` on `ZMod n`. -/
instance instModuleZModH2 [DistribMulAction G (ZMod n)] [ContinuousSMul G (ZMod n)] :
    Module (ZMod n) (H2 G (ZMod n)) :=
  AddCommGroup.zmodModule
    (nsmul_H2_eq_zero fun m ↦ by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul])

end TauCeti.ContCohomology
