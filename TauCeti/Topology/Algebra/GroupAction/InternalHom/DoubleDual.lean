/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZMod.Dual
public import TauCeti.Topology.Algebra.GroupAction.InternalHom.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Double duality for internal homs of discrete modules

Let a group `G` act on additive monoids `M` and `N`, and let `InternalHom G M N` be the internal
hom `M →+ N` with its conjugation action. Evaluation

`eval : m ↦ (φ ↦ φ m)`

is a `G`-equivariant additive homomorphism from `M` to the double internal dual
`InternalHom G (InternalHom G M N) N`, and it is natural in `M`: precomposing twice with an
equivariant `f : M →+[G] M'` carries `eval m` to `eval (f m)`. When `N = ZMod p` for a prime `p` and
`M` is killed by `p`, evaluation is injective, because it is evaluation of the `𝔽_p`-vector space
`M` into its double dual; when `M` is moreover finite it is bijective, by counting: the internal
hom `InternalHom G M (ZMod p)` has the order of `M`. So a finite discrete `G`-module killed
by `p` is canonically and equivariantly its own double dual, which is what identifies the dual of
the dual of a short exact sequence of such modules with the sequence itself, and what turns the
duality statements about a module `M` into statements about its dual `InternalHom G M (ZMod p)`.

## Main definitions

* `TauCeti.InternalHom.eval`: the evaluation map `M →+[G] InternalHom G (InternalHom G M N) N`,
  with `TauCeti.InternalHom.evalPairing_eval` as its defining equation and
  `TauCeti.InternalHom.precomp_precomp_eval` as its naturality.

## Main results

* `TauCeti.InternalHom.natCard_zmod`: `Nat.card (InternalHom G M (ZMod p)) = Nat.card M` for
  finite `M` killed by the prime `p`.
* `TauCeti.InternalHom.eval_injective` and `TauCeti.InternalHom.eval_bijective`: evaluation into the
  double dual with values in `ZMod p` is injective on a module killed by `p`, and bijective when
  that module is finite.
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

variable {G : Type*} {M : Type*} [AddCommGroup M] {p : ℕ} [Fact p.Prime]

/-- **The internal dual of a finite module killed by `p` has the same order.** -/
theorem natCard_zmod [Finite M] (hM : ∀ x : M, p • x = 0) :
    Nat.card (InternalHom G M (ZMod p)) = Nat.card M := by
  rw [← natCard_addMonoidHom_zmod hM]
  exact Nat.card_congr ⟨toAddMonoidHom, of G, fun _ => rfl, fun _ => rfl⟩

variable [Group G] [DistribMulAction G M] [DistribMulAction G (ZMod p)]

/-- For a module `M` killed by a prime `p`, evaluation into the double dual with values in `ZMod p`
is injective: it is evaluation of the `𝔽_p`-vector space `M` into its double dual. -/
theorem eval_injective (hM : ∀ x : M, p • x = 0) : Function.Injective (eval G M (ZMod p)) := by
  have _i : Module (ZMod p) M := AddCommGroup.zmodModule hM
  intro m₁ m₂ h
  refine Module.eval_apply_injective (ZMod p) (LinearMap.ext fun ψ => ?_)
  have := congrArg (fun χ : InternalHom G (InternalHom G M (ZMod p)) (ZMod p) =>
    evalPairing G χ (of G ψ.toAddMonoidHom)) h
  simpa only [evalPairing_apply, toAddMonoidHom_eval, AddMonoidHom.flip_apply,
    LinearMap.toAddMonoidHom_coe, Module.Dual.eval_apply] using this

/-- **Double duality.** For a finite module `M` killed by a prime `p`, evaluation into the double
dual with values in `ZMod p` is bijective: `M` is equivariantly its own double dual. -/
theorem eval_bijective [Finite M] (hM : ∀ x : M, p • x = 0) :
    Function.Bijective (eval G M (ZMod p)) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine (eval_injective hM).bijective_of_nat_card_le ?_
  rw [natCard_zmod (nsmul_eq_zero fun x : ZMod p => by
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]), natCard_zmod hM]

end ZMod

end TauCeti.InternalHom
