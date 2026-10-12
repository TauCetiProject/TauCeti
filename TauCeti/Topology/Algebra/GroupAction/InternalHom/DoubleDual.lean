/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZMod.Dual
public import TauCeti.Topology.Algebra.GroupAction.InternalHom.Basic

/-!
# Double duality for internal homs of discrete modules

Let a group `G` act on additive monoids `M` and `N`, and let `InternalHom G M N` be the internal
hom `M →+ N` with its conjugation action. Evaluation

`eval : m ↦ (φ ↦ φ m)`

is a `G`-equivariant additive homomorphism from `M` to the double internal dual
`InternalHom G (InternalHom G M N) N`, and it is natural in `M`: precomposing twice with an
equivariant `f : M →+[G] M'` carries `eval m` to `eval (f m)`. When `N = ZMod n` for `n ≠ 0` and
`M` is killed by `n`, evaluation is injective, because the homomorphisms to `ZMod n` separate the
points of `M`; when `M` is moreover finite it is bijective, by counting: the internal hom
`InternalHom G M (ZMod n)` has the order of `M`. So a finite discrete `G`-module killed by `n` is
canonically and equivariantly its own double dual, which is what identifies the dual of the dual
of a short exact sequence of such modules with the sequence itself, and what turns the duality
statements about a module `M` into statements about its dual `InternalHom G M (ZMod n)`. The
coefficient systems `ℤ/pⁱ` of a pro-`p` group are the case `n = pⁱ`.

## Main definitions

* `TauCeti.InternalHom.eval`: the evaluation map `M →+[G] InternalHom G (InternalHom G M N) N`,
  with `TauCeti.InternalHom.evalPairing_eval` as its defining equation and
  `TauCeti.InternalHom.precomp_precomp_eval` as its naturality.

## Main results

* `TauCeti.InternalHom.natCard_of_addEquiv_zmod`: `Nat.card (InternalHom G M N) = Nat.card M` for
  finite `M` killed by `n ≠ 0` and values in any additive group `N ≃+ ZMod n`.
* `TauCeti.InternalHom.eval_injective_of_addEquiv_zmod` and
  `TauCeti.InternalHom.eval_bijective_of_addEquiv_zmod`: evaluation into the double dual with
  values in any additive group `N ≃+ ZMod n`, whatever the action of `G` on `N`, is injective on a
  module killed by `n ≠ 0`, and bijective when that module is finite. The untwisted coefficients
  `ZMod n` are the case `e = AddEquiv.refl _`, and the twisted coefficients `ℤ/pⁱ` of a character
  are the case in use.
-/

public section

namespace TauCeti.InternalHom

section Eval

variable (G : Type*) [Group G] (M : Type*) [AddMonoid M] [DistribMulAction G M]
  (N : Type*) [AddCommMonoid N] [DistribMulAction G N]

/-- **Evaluation into the double dual.** The equivariant additive homomorphism
`M →+[G] InternalHom G (InternalHom G M N) N` sending `m` to `φ ↦ φ m`. Its values are
characterized by `evalPairing_eval`, and it is natural in `M` by `precomp_precomp_eval`. -/
def eval : M →+[G] InternalHom G (InternalHom G M N) N where
  toFun m := of G ((evalPairing G).flip m)
  map_smul' g m := by
    ext φ
    simp [homAction_apply]
  map_zero' := by
    ext
    simp
  map_add' _ _ := by
    ext
    simp

variable {G M N}

/-- Forgetting the action, `eval m` is the flipped evaluation pairing at `m`, the additive
homomorphism `φ ↦ φ m` on `InternalHom G M N`. -/
@[simp]
theorem toAddMonoidHom_eval (m : M) :
    (eval G M N m).toAddMonoidHom = (evalPairing G).flip m := (rfl)

/-- Evaluation into the double dual evaluates: `(eval m) φ = φ m`. Not a `simp` lemma, since
`evalPairing_apply` already rewrites its left-hand side to `toAddMonoidHom_eval`. -/
theorem evalPairing_eval (m : M) (φ : InternalHom G M N) :
    evalPairing G (eval G M N m) φ = evalPairing G φ m := by
  rw [evalPairing_apply, toAddMonoidHom_eval, AddMonoidHom.flip_apply]

/-- Evaluation into the double dual is natural in the module: for an equivariant `f : M →+[G] M'`,
precomposing twice with `f` carries `eval m` to `eval (f m)`. -/
theorem precomp_precomp_eval {M' : Type*} [AddMonoid M'] [DistribMulAction G M'] (f : M →+[G] M')
    (m : M) : precomp G (precomp G f) (eval G M N m) = eval G M' N (f m) := by
  ext φ
  simp

end Eval

section ZMod

variable {G : Type*} {M : Type*} [AddCommGroup M] {n : ℕ} [NeZero n]

section AddEquivZMod

variable {N : Type*} [AddCommGroup N] (e : N ≃+ ZMod n)
include e

/-- **The internal dual of a finite module killed by `n` has the same order**, for values in any
additive group `N ≃+ ZMod n`. -/
theorem natCard_of_addEquiv_zmod [Finite M] (hM : ∀ x : M, n • x = 0) :
    Nat.card (InternalHom G M N) = Nat.card M := by
  rw [← e.natCard_addMonoidHom_zmod hM]
  exact Nat.card_congr ⟨toAddMonoidHom, of G, fun _ => rfl, fun _ => rfl⟩

variable [Group G] [DistribMulAction G M] [DistribMulAction G N]

/-- For a module `M` killed by `n ≠ 0`, evaluation into the double dual with values in any additive
group `N ≃+ ZMod n` is injective: the homomorphisms `M →+ N` separate the points of `M`. -/
theorem eval_injective_of_addEquiv_zmod (hM : ∀ x : M, n • x = 0) :
    Function.Injective (eval G M N) := by
  refine (injective_iff_map_eq_zero _).2 fun m hm => by_contra fun hne => ?_
  obtain ⟨f, hf⟩ := exists_addMonoidHom_zmod_apply_ne_zero hM hne
  refine hf ((AddEquiv.map_eq_zero_iff e.symm).1 ?_)
  have := congrArg (fun χ : InternalHom G (InternalHom G M N) N =>
    evalPairing G χ (of G (e.symm.toAddMonoidHom.comp f))) hm
  simpa only [evalPairing_apply, toAddMonoidHom_eval, AddMonoidHom.flip_apply, map_zero,
    AddMonoidHom.zero_apply, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom] using this

/-- **Double duality.** For a finite module `M` killed by `n ≠ 0`, evaluation into the double dual
with values in any additive group `N ≃+ ZMod n` is bijective: `M` is equivariantly its own double
dual. -/
theorem eval_bijective_of_addEquiv_zmod [Finite M] (hM : ∀ x : M, n • x = 0) :
    Function.Bijective (eval G M N) := by
  have : Finite N := Finite.of_equiv _ e.symm.toEquiv
  have hN : ∀ y : N, n • y = 0 := fun y => by
    rw [← e.map_eq_zero_iff, map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  refine (eval_injective_of_addEquiv_zmod e hM).bijective_of_nat_card_le ?_
  rw [natCard_of_addEquiv_zmod e (nsmul_eq_zero hN), natCard_of_addEquiv_zmod e hM]

end AddEquivZMod

end ZMod

end TauCeti.InternalHom
