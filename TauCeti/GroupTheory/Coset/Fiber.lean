/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.SetTheory.Cardinal.Finite
-- Proof-only: `smulAddHom`, the `n • ·` homomorphism the zsmul case is read through.
import Mathlib.Algebra.Module.End

/-!
# A nonempty fiber of a group homomorphism is a copy of the kernel

A nonempty fiber of `f` is a coset of `ker f`. Mathlib's `AddMonoidHom.fiberEquivKer` says this in
the set-preimage form `f ⁻¹' {f a}`, with the attained value written as a value of `f`, and over an
additive *group*. A caller usually meets the fiber as the subtype `{a // f a = b}` instead and
holds `f a = b` separately, and a kernel asks only `AddZeroClass` of the codomain, so
`subtypeFiberEquivKer` is built here at that generality: `x ↦ x - a`, with `a + ·` back. Three
consequences follow from it: the fiber is counted, made finite, and a sum over it is reindexed as a
sum over the kernel.

Finiteness is the one of the three that needs no preimage: an empty fiber is finite as well, so the
statement is available before any point of the fiber is known, which is what a caller quantifying
over all values of `f` wants.

The multiplication map `n • ·` of an additive commutative group is the case the counting arguments
for isogenies use: each of its nonempty fibers has as many elements as the `n`-torsion. Emptiness
is not excluded by fiat — `n • ·` need not be surjective — so a preimage is an argument, and it is
the only thing either statement asks for.

## Main results

* `AddMonoidHom.subtypeFiberEquivKer` (and `MonoidHom.subtypeFiberEquivKer`): the fiber over an
  attained value, as a subtype, is equivalent to the kernel, translating by `-a` and its inverse
  by `a`.
* `AddMonoidHom.card_fiber_eq_card_ker` (and `MonoidHom.card_fiber_eq_card_ker`): a nonempty
  fiber has as many elements as the kernel.
* `AddMonoidHom.finite_fiber` (and `MonoidHom.finite_fiber`): every fiber is finite when the
  kernel is.
* `AddMonoidHom.sum_fiber_eq_sum_ker` (and `MonoidHom.prod_fiber_eq_prod_ker`): summing over a
  nonempty fiber is summing `a + t` over the kernel.
* `TauCeti.card_zsmul_fiber_eq_card_zsmul_eq_zero`: the same for `n • ·` on an additive commutative
  group, with the kernel written as the `n`-torsion.

## Provenance

Generalized from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0)
pinned at `a302aeacd86053f9d5f991fbbf664e1cc1051d08`: `HasseWeil/HasseBound/WeilPairing/Fiber.lean`,
declarations `fiberEquivKer`, `fiber_finite` and `fiber_card_eq_ker_card`, and
`HasseWeil/HasseBound/WeilPairing/SigmaBridge.lean`, declaration `fiber_sum_eq_ker_sum`. There they
are stated for an endomorphism of the point group of an elliptic curve; here they hold of any
homomorphism of groups, the commutative hypothesis appearing only where an unordered product is
taken. The source builds its fiber equivalence by hand, where this one is Mathlib's
`fiberEquivKer` composed with the change of presentation.
-/

public section

/-- **A nonempty fiber is a copy of the kernel**, in the subtype form: given `ha : f a = b`, the
fiber over `b` is `a` times the kernel. Mathlib's `MonoidHom.fiberEquivKer` is the same map at
`[Group H]`, stated on the set preimage `f ⁻¹' {f a}`; the codomain of a kernel needs only
`MulOneClass`, which is where this is built. -/
@[to_additive
/-- **A nonempty fiber is a copy of the kernel**, in the subtype form: given `ha : f a = b`, the
fiber over `b` is `a` plus the kernel. Mathlib's `AddMonoidHom.fiberEquivKer` is the same map at
`[AddGroup H]`, stated on the set preimage `f ⁻¹' {f a}`; the codomain of a kernel needs only
`AddZeroClass`, which is where this is built. -/]
def MonoidHom.subtypeFiberEquivKer {G H : Type*} [Group G] [MulOneClass H] (f : G →* H) {b : H}
    {a : G} (ha : f a = b) : {x : G // f x = b} ≃ f.ker where
  toFun x := ⟨a⁻¹ * x, by
    rw [MonoidHom.mem_ker, map_mul, x.2, ← ha, ← map_mul, inv_mul_cancel, map_one]⟩
  invFun t := ⟨a * t, by rw [map_mul, MonoidHom.mem_ker.mp t.2, mul_one, ha]⟩
  left_inv _ := Subtype.ext (mul_inv_cancel_left a _)
  right_inv _ := Subtype.ext (inv_mul_cancel_left a _)

/-- **The equivalence translates by `a⁻¹`.** -/
@[to_additive (attr := simp)
/-- **The equivalence translates by `-a`.** -/]
theorem MonoidHom.coe_subtypeFiberEquivKer_apply {G H : Type*} [Group G] [MulOneClass H]
    (f : G →* H) {b : H} {a : G} (ha : f a = b) (x : {x : G // f x = b}) :
    ((f.subtypeFiberEquivKer ha x : f.ker) : G) = a⁻¹ * (x : G) := by
  simp [MonoidHom.subtypeFiberEquivKer]

/-- **Its inverse translates by `a`.** -/
@[to_additive (attr := simp)
/-- **Its inverse translates by `a`.** -/]
theorem MonoidHom.coe_subtypeFiberEquivKer_symm_apply {G H : Type*} [Group G] [MulOneClass H]
    (f : G →* H) {b : H} {a : G} (ha : f a = b) (t : f.ker) :
    (((f.subtypeFiberEquivKer ha).symm t : {x : G // f x = b}) : G) = a * (t : G) := by
  simp [MonoidHom.subtypeFiberEquivKer]

/-- **A nonempty fiber has as many elements as the kernel.** -/
@[to_additive
/-- **A nonempty fiber has as many elements as the kernel.** -/]
theorem MonoidHom.card_fiber_eq_card_ker {G H : Type*} [Group G] [MulOneClass H] (f : G →* H)
    {b : H} {a : G} (ha : f a = b) :
    Nat.card {x : G // f x = b} = Nat.card f.ker :=
  Nat.card_congr (f.subtypeFiberEquivKer ha)

/-- **Every fiber is finite when the kernel is.** The empty fiber is covered too, so no preimage
has to be produced first. -/
@[to_additive
/-- **Every fiber is finite when the kernel is.** The empty fiber is covered too, so no preimage
has to be produced first. -/]
theorem MonoidHom.finite_fiber {G H : Type*} [Group G] [MulOneClass H] (f : G →* H) [Finite f.ker]
    (b : H) : Finite {x : G // f x = b} := by
  rcases isEmpty_or_nonempty {x : G // f x = b} with _ | ⟨⟨a, ha⟩⟩
  · infer_instance
  · exact Finite.of_equiv _ (f.subtypeFiberEquivKer ha).symm

/-- **A product over a nonempty fiber is a product over the kernel**, translated by any point of
the fiber. Only the kernel is assumed finite: the equivalence carries that to the fiber, and the
`Fintype` the product needs there is the transported one. -/
@[to_additive
/-- **A sum over a nonempty fiber is a sum over the kernel**, translated by any point of the
fiber. Only the kernel is assumed finite: the equivalence carries that to the fiber, and the
`Fintype` the sum needs there is the transported one. -/]
theorem MonoidHom.prod_fiber_eq_prod_ker {G H : Type*} [CommGroup G] [MulOneClass H] (f : G →* H)
    {b : H} {a : G} (ha : f a = b) [Fintype f.ker] :
    letI : Fintype {x : G // f x = b} := Fintype.ofEquiv f.ker (f.subtypeFiberEquivKer ha).symm
    (∏ x : {x : G // f x = b}, (x : G)) = ∏ t : f.ker, a * (t : G) :=
  letI : Fintype {x : G // f x = b} := Fintype.ofEquiv f.ker (f.subtypeFiberEquivKer ha).symm
  Fintype.prod_equiv (f.subtypeFiberEquivKer ha) _ _ fun _ ↦ by simp

namespace TauCeti

/-- **A nonempty fiber of `n • ·` has as many elements as the `n`-torsion.** -/
theorem card_zsmul_fiber_eq_card_zsmul_eq_zero {G : Type*} [AddCommGroup G] {n : ℤ} {T P₀ : G}
    (hP₀ : n • P₀ = T) :
    Nat.card {P : G // n • P = T} = Nat.card {P : G // n • P = 0} :=
  ((smulAddHom ℤ G n).card_fiber_eq_card_ker hP₀).trans <|
    Nat.card_congr <| Equiv.subtypeEquivRight fun _ ↦ by simp

end TauCeti

end
