/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZMod
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree

/-!
# `H²(G, M)` as a `ZMod n`-module

Multiplication by `n` is zero on any `ZMod n`-module, so `n` kills the coefficients of
`H²(G, M)`, hence `H²(G, M)` itself (`TauCeti.ContCohomology.nsmul_H2_eq_zero`), which makes it a
`ZMod n`-module in turn (`TauCeti.ContCohomology.instModuleZModH2`). The coefficients are left
general, so that the instance also covers coefficients such as the invariants `M ^ N` carried by
the cohomology of a quotient group, and `M = ZMod n` itself is the case that makes
`H²(G, ZMod n)` a `ZMod n`-module, and for `n` a prime `p` an `𝔽_p`-vector space, so that
`Module.rank`, `Module.finrank` and `Module.Finite` apply to it. For a pro-`p` group `G` that
dimension is the relation rank of `G`.

The module structure is the canonical one: `Module (ZMod n) A` is a subsingleton on an abelian
group `A` (`ZMod.instSubsingletonModule`), so it agrees with every other way of producing one,
and scalar multiplication by a natural number is the iterated sum (`Nat.cast_smul_eq_nsmul`).

## Main results

* `TauCeti.ContCohomology.instModuleZModH2`: `H²(G, M)` is a `ZMod n`-module whenever `M` is.
* `TauCeti.ContCohomology.zmod_smul_mk_cast`: on the class of a cocycle, a scalar `c : ZMod n`
  acts as the `c.cast`-fold integer multiple of the cocycle, for every `n`.
-/

public section

namespace TauCeti.ContCohomology

universe u v

variable {n : ℕ} {G : Type u} [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- `H²(G, M)` is a `ZMod n`-module whenever the coefficients `M` are; in particular
`H²(G, ZMod n)` is one, for any continuous action of `G` on `ZMod n`. -/
instance instModuleZModH2 [Module (ZMod n) M] : Module (ZMod n) (H2 G M) :=
  AddCommGroup.zmodModule (nsmul_H2_eq_zero (ZModModule.char_nsmul_eq_zero n))

/-- Scalar multiplication by `c : ZMod n` on the class of a `2`-cocycle is the class of its
`c.cast`-fold integer multiple: the scalar action of `ZMod n` on `H²(G, M)` is computed on cocycles
through the integer action, so it holds for every `n`, including `n = 0`. -/
theorem zmod_smul_mk_cast [Module (ZMod n) M] (c : ZMod n) (z : Z2 G M) :
    c • (z : H2 G M) = (((c.cast : ℤ) • z : Z2 G M) : H2 G M) := by
  rw [QuotientAddGroup.mk_zsmul, ← Int.cast_smul_eq_zsmul (ZMod n), ZMod.intCast_zmod_cast]

end TauCeti.ContCohomology
