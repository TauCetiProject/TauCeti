/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# The `𝔽_p`-dual of an additive group killed by a prime

An additive commutative group `M` killed by a prime `p` is an `𝔽_p`-vector space, through
`AddCommGroup.zmodModule`, and its additive homomorphisms to `ZMod p` are exactly its linear
functionals. This file records the consequence of linear algebra over `𝔽_p` that the duality of
finite `𝔽_p[G]`-modules rests on, phrased on `M →+ ZMod p` so that no module instance has to be
installed by the caller: for finite `M` there are exactly as many homomorphisms `M →+ ZMod p` as
elements of `M`.

## Main results

* `TauCeti.natCard_addMonoidHom_zmod`: `Nat.card (M →+ ZMod p) = Nat.card M` for finite `M` killed
  by `p`.
-/

public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {M : Type*} [AddCommGroup M]

/-- **The `𝔽_p`-dual of a finite group killed by `p` has the same order.** If `p` is prime and `M`
is finite and killed by `p`, then `Nat.card (M →+ ZMod p) = Nat.card M`: the homomorphisms to
`ZMod p` are the linear functionals on the finite-dimensional `𝔽_p`-vector space `M`, and the dual
of a finite-dimensional vector space has the same dimension. -/
theorem natCard_addMonoidHom_zmod [Finite M] (hM : ∀ x : M, p • x = 0) :
    Nat.card (M →+ ZMod p) = Nat.card M := by
  classical
  have _i : Module (ZMod p) M := AddCommGroup.zmodModule hM
  exact (Nat.card_congr (AddMonoidHom.toZModLinearMapEquiv p (M := M) (M₁ := ZMod p)).toEquiv).trans
    (Nat.card_congr (Module.Basis.ofVectorSpace (ZMod p) M).toDualEquiv.toEquiv).symm

end TauCeti
