/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.GroupTheory.ExponentialGroup.FreeCompletion
public import TauCeti.GroupTheory.ExponentialGroup.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Polynomial.Basic
import TauCeti.GroupTheory.Finiteness

/-!
# Completions with exponents in `ℤ[t]`

A `ℤ[t]`-group structure is determined by its `t`-th power, which can be any map that commutes with
conjugation and is multiplicative on commuting elements
(`TauCeti.IsExponentialGroup.isExponentialGroup_polynomialPow`). So a `ℤ[t]`-completion of a group
`G` is the universal group over `G` with such a map. Evaluating `t` at an integer shows that in the
tensor `ℤ[t]`-completion the powers `g ^ p`, `p ≠ 0`, of an element `g` of infinite order of `G`
are nontrivial, so that the powers `g ^ (t ^ k)` generate a subgroup that is not finitely
generated.

## Main results

* `TauCeti.IsExponentialGroup.IsCompletion.existsUnique_lift_map_pow_X`: the universal property
  of a `ℤ[t]`-completion in terms of the `t`-th power. For the tensor completion, apply it to
  `TauCeti.ExponentialGroup.Completion.isCompletion_of`.
* `TauCeti.IsExponentialGroup.not_fg_closure_range_pow_X_pow`: in a `ℤ[t]`-group, the powers
  `x ^ (t ^ k)` of an element `x` whose powers `x ^ p` are pairwise distinct generate a subgroup
  that is not finitely generated.
* `TauCeti.ExponentialGroup.Completion.of_pow_ne_one_of_ne_zero`: in the tensor
  `ℤ[t]`-completion, the powers `g ^ p`, `p ≠ 0`, of an element `g` of infinite order of `G` are
  nontrivial.
* `TauCeti.ExponentialGroup.Completion.not_fg_closure_range_pow_X_pow`: the powers `g ^ (t ^ k)`
  of an element of infinite order of `G` generate a subgroup of the tensor `ℤ[t]`-completion that
  is not finitely generated.

## References

* A. G. Myasnikov, V. N. Remeslennikov, *Exponential groups. II. Extensions of centralizers and
  tensor completion of CSA-groups*, Internat. J. Algebra Comput. 6 (1996), Definition 1 and §2.
* A. G. Myasnikov, V. N. Remeslennikov, D. E. Serbin, *Regular free length functions on Lyndon's
  free `ℤ[t]`-group `F^{ℤ[t]}`*, §2.1.
-/

public section

open Polynomial

universe w

namespace TauCeti.IsExponentialGroup

variable {G : Type*} [Group G]

/-- **The universal property of a `ℤ[t]`-completion in terms of the `t`-th power.** For a
`ℤ[t]`-completion `μ : G →* K` and a map `T : H → H` that commutes with conjugation and is
multiplicative on commuting elements, every homomorphism `φ : G →* H` extends uniquely along `μ`
to a homomorphism `ψ : K →* H` with `ψ (x ^ t) = T (ψ x)`. -/
theorem IsCompletion.existsUnique_lift_map_pow_X {K : Type*} [Group K] [Pow K ℤ[X]]
    [IsExponentialGroup ℤ[X] K] {μ : G →* K} (hμ : IsCompletion.{w} ℤ[X] μ) {H : Type w}
    [Group H] {T : H → H} (hconj : ∀ g h : H, T (g * h * g⁻¹) = g * T h * g⁻¹)
    (hmul : ∀ g h : H, Commute g h → T (g * h) = T g * T h) (φ : G →* H) :
    ∃! ψ : K →* H, ψ.comp μ = φ ∧ ∀ x : K, ψ (x ^ (X : ℤ[X])) = T (ψ x) := by
  let := polynomialPow T
  have := isExponentialGroup_polynomialPow hconj hmul
  refine ⟨(hμ.lift φ).toMonoidHom, ⟨hμ.lift_comp φ, fun x => ?_⟩, fun ψ hψ => ?_⟩
  · rw [ExponentialHom.coe_toMonoidHom, ExponentialHom.map_pow, polynomialPow_X]
  · have hpow := ψ.map_pow_of_map_pow_X fun x => by rw [hψ.2, polynomialPow_X]
    exact congrArg ExponentialHom.toMonoidHom (hμ.eq_lift (ψ := ⟨ψ, hpow⟩) hψ.1)

open scoped MultiplicativePow in
/-- In a `ℤ[t]`-group, if the powers `x ^ p` of an element `x` are pairwise distinct, the powers
`x ^ (t ^ k)` generate a subgroup that is not finitely generated. -/
theorem not_fg_closure_range_pow_X_pow [Pow G ℤ[X]] [IsExponentialGroup ℤ[X] G] {x : G}
    (hx : Function.Injective (powHom ℤ[X] x)) :
    ¬(Subgroup.closure (Set.range fun k : ℕ => x ^ (X ^ k : ℤ[X]))).FG := by
  -- the powers of `x` with exponents of degree at most `N`, an increasing chain
  let P (N : ℕ) := (degreeLE ℤ N).toAddSubgroup.toSubgroup.map (powHom ℤ[X] x).toMonoidHom
  have hP : Monotone P := fun _ _ hNM => Subgroup.map_mono <| AddSubgroup.toSubgroup.monotone <|
    Submodule.toAddSubgroup_mono <| degreeLE_mono <| WithBot.coe_le_coe.2 hNM
  have hk (k : ℕ) : x ^ (X ^ k : ℤ[X]) ∈ P k :=
    Subgroup.mem_map.2 ⟨.ofAdd (X ^ k), mem_degreeLE.2 (degree_X_pow_le k), by simp⟩
  intro hfg
  -- a finitely generated subgroup of the union of the chain lies in one stage `P N`
  obtain ⟨N, hN⟩ := hfg.exists_le_of_le_iSup_of_directed hP.directed_le <|
    (Subgroup.closure_le _).2 <| Set.range_subset_iff.2 fun k => Subgroup.mem_iSup_of_mem k (hk k)
  -- but `x ^ (t ^ (N + 1))` is a power of `x` with an exponent of degree `N + 1` only
  obtain ⟨q, hq, h⟩ := Subgroup.mem_map.1 (hN (Subgroup.subset_closure ⟨N + 1, rfl⟩))
  obtain rfl : q = .ofAdd (X ^ (N + 1)) := hx (by simpa using h)
  have hdeg := (mem_degreeLE (f := X ^ (N + 1))).1 hq
  rw [degree_X_pow] at hdeg
  exact (WithBot.coe_le_coe.1 hdeg).not_gt N.lt_succ_self

end TauCeti.IsExponentialGroup

namespace TauCeti.ExponentialGroup.Completion

open IsExponentialGroup
open scoped TauCeti.ExponentialGroup.Completion

variable {G : Type*} [Group G]

/-- In the `ℤ[t]`-completion, the powers of an element of `G` of infinite order with nonzero
exponents are nontrivial. -/
theorem of_pow_ne_one_of_ne_zero {g : G} (hg : ¬IsOfFinOrder g) {p : ℤ[X]} (hp : p ≠ 0) :
    (of g : Completion ℤ[X] G) ^ p ≠ 1 := by
  -- a nonzero integer polynomial does not vanish at some integer `m`
  obtain ⟨m, hm⟩ : ∃ m : ℤ, p.eval m ≠ 0 := by
    by_contra! H
    exact hp (Polynomial.funext fun m => by simpa using H m)
  exact of_pow_ne_one (evalRingHom m) fun h => hg (isOfFinOrder_iff_zpow_eq_one.2 ⟨_, hm, h⟩)

open scoped MultiplicativePow in
/-- The polynomial powers `g ^ (t ^ k)` of an element of infinite order of `G` generate a subgroup
of the `ℤ[t]`-completion of `G` that is not finitely generated. -/
theorem not_fg_closure_range_pow_X_pow {g : G} (hg : ¬IsOfFinOrder g) : ¬(Subgroup.closure
    (Set.range fun k : ℕ => (of g : Completion ℤ[X] G) ^ (X ^ k : ℤ[X]))).FG :=
  IsExponentialGroup.not_fg_closure_range_pow_X_pow <| (injective_iff_map_eq_one _).2 fun p hp =>
    by_contra fun hp' => of_pow_ne_one_of_ne_zero hg (p := p.toAdd) (by simpa using hp')
      (by simpa using hp)

end TauCeti.ExponentialGroup.Completion
