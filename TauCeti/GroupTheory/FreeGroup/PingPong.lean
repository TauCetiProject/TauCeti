/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.CoprodI
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group

/-!
# The ping-pong lemma for cyclic subgroups

Mathlib's free-group ping-pong lemma `FreeGroup.injective_lift_of_ping_pong` asks for two sets
`X i` and `Y i` per generator, with `a i` mapping the complement of `Y i` into `X i` and
`(a i)⁻¹` mapping the complement of `X i` into `Y i`. In the classical cyclic form (de la Harpe,
*Topics in geometric group theory*, §II.B) there is one set `X i` per generator, and every
nonzero power of `a i` maps every other `X j` into `X i`. This form is the one that applies
directly to the matrices `[[1, 2], [0, 1]]` and `[[1, 0], [2, 1]]` acting on `ℤ²`. It is deduced
here from Mathlib's ping-pong lemma for free products,
`Monoid.CoprodI.lift_injective_of_ping_pong`, through `freeGroupEquivCoprodI`, following
Mathlib's own proof of `FreeGroup.injective_lift_of_ping_pong`.

A second statement turns one ping-pong pair into infinitely many: if `a` and `b` play ping-pong
on two disjoint sets, then the conjugates `bᵏ a b⁻ᵏ`, for distinct integers `k`, freely generate
a free group. This is how free groups of every countable rank are found inside a free group of
rank two, and inside `SL(2, ℤ)`.

## Main results

* `FreeGroup.injective_lift_of_ping_pong_zpow`: the cyclic ping-pong lemma.
* `FreeGroup.injective_lift_of_ping_pong_pair`: its two-generator form.
* `FreeGroup.injective_lift_conj_zpow_of_ping_pong`: conjugates of a ping-pong partner by
  distinct powers of the other one are a free basis of the subgroup they generate.

## References

* P. de la Harpe, *Topics in geometric group theory*, University of Chicago Press, 2000,
  §II.B (the table-tennis lemma).
-/

public section

open scoped Pointwise Function

namespace FreeGroup

variable {ι G α : Type*} [Group G] [MulAction G α]

/-- **The ping-pong lemma, cyclic form.** Suppose there are at least two indices. If every
nonzero power of `a i` maps every set `X j` with `j ≠ i` into `X i`, where the sets `X i` are
nonempty and pairwise disjoint, then the `a i` freely generate a free subgroup:
`FreeGroup.lift a` is injective. -/
theorem injective_lift_of_ping_pong_zpow [Nontrivial ι] (a : ι → G) (X : ι → Set α)
    (hX : ∀ i, (X i).Nonempty) (hXdisj : Pairwise (Disjoint on X))
    (hpp : Pairwise fun i j => ∀ n : ℤ, n ≠ 0 → a i ^ n • X j ⊆ X i) :
    Function.Injective (FreeGroup.lift a) := by
  -- Factor `FreeGroup.lift a` through the free product of the cyclic groups `⟨a i⟩`.
  have hlift : FreeGroup.lift a =
      (Monoid.CoprodI.lift fun i => FreeGroup.lift fun _ : Unit => a i).comp
        (freeGroupEquivCoprodI (ι := ι)).toMonoidHom := by
    ext i
    simp
  rw [hlift, MonoidHom.coe_comp]
  refine Function.Injective.comp ?_ (MulEquiv.injective _)
  refine Monoid.CoprodI.lift_injective_of_ping_pong _ ?_ X hX hXdisj ?_
  · inhabit ι
    refine Or.inr ⟨default, ?_⟩
    rw [freeGroupUnitEquivInt.cardinal_eq, Cardinal.mk_denumerable]
    exact Cardinal.natCast_le_aleph0
  · intro i j hij h hh
    -- Every element of `FreeGroup Unit` is a power of the generator.
    obtain ⟨n, rfl⟩ : ∃ n : ℤ, FreeGroup.of () ^ n = h :=
      ⟨freeGroupUnitEquivInt h, freeGroupUnitEquivInt.symm_apply_apply h⟩
    have hn : n ≠ 0 := by
      rintro rfl
      exact hh (zpow_zero _)
    simpa using hpp hij n hn

/-- **The ping-pong lemma for two elements.** If every nonzero power of `a` maps `Y` into `X`,
and every nonzero power of `b` maps `X` into `Y`, where `X` is nonempty and `X` and `Y` are
disjoint, then `a` and `b` freely generate a free group of rank two. -/
theorem injective_lift_of_ping_pong_pair {a b : G} {X Y : Set α} (hX : X.Nonempty)
    (hXY : Disjoint X Y) (ha : ∀ n : ℤ, n ≠ 0 → a ^ n • Y ⊆ X)
    (hb : ∀ n : ℤ, n ≠ 0 → b ^ n • X ⊆ Y) :
    Function.Injective (FreeGroup.lift ![a, b]) := by
  have hY : Y.Nonempty := (hX.smul_set (a := b)).mono (by simpa using hb 1 one_ne_zero)
  refine injective_lift_of_ping_pong_zpow _ ![X, Y] (fun i => ?_) (fun i j hij => ?_)
    (fun i j hij => ?_)
  · fin_cases i
    exacts [hX, hY]
  · fin_cases i <;> fin_cases j
    exacts [absurd rfl hij, hXY, hXY.symm, absurd rfl hij]
  · fin_cases i <;> fin_cases j
    exacts [absurd rfl hij, ha, hb, absurd rfl hij]

/-- **Free subgroups from conjugates.** Let `a` and `b` play ping-pong on disjoint sets `X` and
`Y` with `X` nonempty: every nonzero power of `a` maps `Y` into `X`, and every nonzero power of
`b` maps `X` into `Y`. Then for an injective family of exponents `k : ι → ℤ`, the conjugates
`b ^ k i * a * (b ^ k i)⁻¹` freely generate a free subgroup. -/
theorem injective_lift_conj_zpow_of_ping_pong {a b : G} {X Y : Set α} (hX : X.Nonempty)
    (hXY : Disjoint X Y) (ha : ∀ n : ℤ, n ≠ 0 → a ^ n • Y ⊆ X)
    (hb : ∀ n : ℤ, n ≠ 0 → b ^ n • X ⊆ Y) {k : ι → ℤ} (hk : Function.Injective k) :
    Function.Injective (FreeGroup.lift fun i => b ^ k i * a * (b ^ k i)⁻¹) := by
  -- The integer-indexed family plays cyclic ping-pong on the translates `b ^ m • X`.
  have hsub : ∀ m m' : ℤ, m ≠ m' → b ^ (m' - m) • X ⊆ Y := fun m m' hmm' =>
    hb _ (sub_ne_zero.mpr hmm'.symm)
  have hℤ : Function.Injective (FreeGroup.lift fun m : ℤ => b ^ m * a * (b ^ m)⁻¹) := by
    refine injective_lift_of_ping_pong_zpow _ (fun m : ℤ => b ^ m • X) (fun m => hX.smul_set)
      (fun m m' hmm' => ?_) (fun m m' hmm' n hn => ?_)
    · rw [Function.onFun, show b ^ m' = b ^ m * b ^ (m' - m) by rw [← zpow_add, add_sub_cancel],
        mul_smul, Set.disjoint_smul_set]
      exact hXY.mono_right (hsub m m' hmm')
    · calc (b ^ m * a * (b ^ m)⁻¹) ^ n • b ^ m' • X
          = b ^ m • a ^ n • b ^ (m' - m) • X := by
            rw [conj_zpow, smul_smul, smul_smul, smul_smul]
            congr 1
            group
        _ ⊆ b ^ m • X :=
          Set.smul_set_mono ((Set.smul_set_mono (hsub m m' hmm')).trans (ha n hn))
  have hcomp : (FreeGroup.lift fun i => b ^ k i * a * (b ^ k i)⁻¹) =
      (FreeGroup.lift fun m : ℤ => b ^ m * a * (b ^ m)⁻¹).comp (FreeGroup.map k) := by
    ext i
    simp
  rw [hcomp, MonoidHom.coe_comp]
  exact hℤ.comp (FreeGroup.map_injective hk)

end FreeGroup
