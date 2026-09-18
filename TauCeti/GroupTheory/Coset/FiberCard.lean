/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.SetTheory.Cardinal.Finite
-- Proof-only: `smulAddHom`, the `n • ·` homomorphism the zsmul case is read through.
import Mathlib.Algebra.Module.End

/-!
# A nonempty fiber of a group homomorphism has as many elements as the kernel

Mathlib's `AddMonoidHom.fiberEquivKer` exhibits a nonempty fiber of `f` as a coset of `ker f`.
Counting both sides turns that into an equality of cardinalities, in the subtype form
`{a // f a = b}` a caller usually meets rather than the set-preimage form the equivalence is
stated in.

The multiplication map `n • ·` of an additive commutative group is the case the counting arguments
for isogenies use: each of its nonempty fibers has as many elements as the `n`-torsion. Emptiness
is not excluded by fiat — `n • ·` need not be surjective — so a preimage is an argument, and it is
the only thing either statement asks for.

## Main results

* `AddMonoidHom.card_fiber_eq_card_ker` (and `MonoidHom.card_fiber_eq_card_ker`): a nonempty
  fiber has as many elements as the kernel.
* `TauCeti.card_zsmul_fiber_eq_card_zsmul_eq_zero`: the same for `n • ·` on an additive commutative
  group, with the kernel written as the `n`-torsion.
-/

public section

/-- **A nonempty fiber has as many elements as the kernel.** -/
@[to_additive
/-- **A nonempty fiber has as many elements as the kernel.** -/]
theorem MonoidHom.card_fiber_eq_card_ker {G H : Type*} [Group G] [Group H] (f : G →* H)
    {b : H} {a : G} (ha : f a = b) :
    Nat.card {x : G // f x = b} = Nat.card f.ker :=
  Nat.card_congr <|
    (Equiv.subtypeEquivRight fun _ ↦ by simp [← ha]).trans (f.fiberEquivKer a)

namespace TauCeti

/-- **A nonempty fiber of `n • ·` has as many elements as the `n`-torsion.** -/
theorem card_zsmul_fiber_eq_card_zsmul_eq_zero {G : Type*} [AddCommGroup G] {n : ℤ} {T P₀ : G}
    (hP₀ : n • P₀ = T) :
    Nat.card {P : G // n • P = T} = Nat.card {P : G // n • P = 0} :=
  ((smulAddHom ℤ G n).card_fiber_eq_card_ker hP₀).trans <|
    Nat.card_congr <| Equiv.subtypeEquivRight fun _ ↦ by simp

end TauCeti

end
