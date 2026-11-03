/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import TauCeti.Analysis.AbsoluteValue.Evertse
import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.NumberTheory.NumberField.Global.Approximation.SInteger
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Evertse's lemma over a number field

Let `K` be a number field, `S₀` a finite set of finite places, and `x 0, …, x (m - 1)` a basis of
a `K`-vector space `V`. At every infinite place and every place of `S₀` let `m` linearly
independent linear forms `L v k` on `V`, weights `ν v k > 0` and a nondecreasing sequence `μ v`
satisfy `|L v k (x j)|_v ≤ ν v k * μ v j`. **Evertse's lemma** (`NumberField.exists_evertse`)
corrects the basis to

`y j = x j + ∑ l < j, ξ j l • x l`, with every `ξ j l` integral outside `S₀`,

and reorders the forms at each place by a permutation `π v`, so that

`|L v (π v i) (y j)|_v ≤ C * ν v (π v i) * min (μ v i) (μ v j)`

at the infinite places and the same bound without `C` at the places of `S₀`. The constant `C`
depends only on `K` and `m`: it is chosen before `S₀`, the space, the forms and the basis.
`NumberField.exists_evertse_unweighted` is the case `ν = 1`.

In the proof of Schmidt's Subspace Theorem the lemma is applied to a family realizing the
successive minima of a parallelepiped, with weights `ν v i = Q ^ c v i` that change with the
level `Q`; this is why the constant must be uniform. It replaces Mahler's theorem on compound
bodies and Davenport's lemma in Schmidt's original argument. The proof is the general
`AbsoluteValue.exists_evertse_of_approx`, fed with simultaneous approximation by `S₀`-integers,
`NumberField.exists_forall_apply_add_le`.

## Main results

* `NumberField.exists_evertse`: Evertse's lemma with weights.
* `NumberField.exists_evertse_unweighted`: Evertse's lemma without weights.

## References

* J.-H. Evertse, *An improvement of the quantitative Subspace theorem*, Compositio Math. 101
  (1996), 225–311.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  Lemma 7.5.29.
-/

public section

open Finset

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Evertse's lemma** (Evertse; Bombieri–Gubler, Lemma 7.5.29). There is a constant `C`,
depending only on `K` and `m`, with the following property. Let `S₀` be a finite set of finite
places, `x` a basis of a `K`-vector space `V` indexed by `Fin m`, and at every infinite place and
every place of `S₀` let the forms `L v k` be linearly independent, the weights `ν v k` positive
and `μ v` nondecreasing, with `|L v k (x j)|_v ≤ ν v k * μ v j`. Then there are `ξ j l ∈ K`,
integral outside `S₀`, and permutations `π v`, such that `y j = x j + ∑ l < j, ξ j l • x l`
satisfies `|L v (π v i) (y j)|_v ≤ C * (ν v (π v i) * min (μ v i) (μ v j))` at every infinite
place and `|L v (π v i) (y j)|_v ≤ ν v (π v i) * min (μ v i) (μ v j)` at every place of `S₀`. -/
theorem exists_evertse (m : ℕ) :
    ∃ C : ℝ, ∀ (V : Type*) [AddCommGroup V] [Module K V] (Sfin : Finset (FinitePlace K))
      (L : AbsoluteValue K ℝ → Fin m → Module.Dual K V) (x : Module.Basis (Fin m) K V)
      (ν μ : AbsoluteValue K ℝ → Fin m → ℝ),
      (∀ v : InfinitePlace K, LinearIndependent K (L v.1)) →
      (∀ v ∈ Sfin, LinearIndependent K (L v.1)) →
      (∀ (v : InfinitePlace K) k, 0 < ν v.1 k) → (∀ v ∈ Sfin, ∀ k, 0 < ν v.1 k) →
      (∀ v : InfinitePlace K, Monotone (μ v.1)) → (∀ v ∈ Sfin, Monotone (μ v.1)) →
      (∀ (v : InfinitePlace K) k j, v (L v.1 k (x j)) ≤ ν v.1 k * μ v.1 j) →
      (∀ v ∈ Sfin, ∀ k j, v (L v.1 k (x j)) ≤ ν v.1 k * μ v.1 j) →
      ∃ (ξ : Fin m → Fin m → K) (π : AbsoluteValue K ℝ → Equiv.Perm (Fin m)),
        (∀ j l, ∀ u : FinitePlace K, u ∉ Sfin → u (ξ j l) ≤ 1) ∧
        (∀ (v : InfinitePlace K) i j,
          v (L v.1 (π v.1 i) (x j + ∑ l ∈ univ.filter (· < j), ξ j l • x l)) ≤
            C * (ν v.1 (π v.1 i) * min (μ v.1 i) (μ v.1 j))) ∧
        ∀ v ∈ Sfin, ∀ i j,
          v (L v.1 (π v.1 i) (x j + ∑ l ∈ univ.filter (· < j), ξ j l • x l)) ≤
            ν v.1 (π v.1 i) * min (μ v.1 i) (μ v.1 j) := by
  classical
  obtain ⟨A₀, hA₀⟩ := exists_forall_apply_add_le (K := K)
  refine ⟨2 ^ (2 * m + 1) * max 1 A₀, fun V _ _ Sfin L x ν μ hLinf hLfin hνinf hνfin hμinf
    hμfin hinf hfin ↦ ?_⟩
  have : FiniteDimensional K V := Module.Finite.of_basis x
  have hcard : Fintype.card (Fin m) = Module.finrank K V := by
    rw [Module.finrank_eq_card_basis x]
  -- The places of the statement, as underlying absolute values.
  set T : Set (AbsoluteValue K ℝ) :=
    {v | (∃ w : InfinitePlace K, w.1 = v) ∨ ∃ u ∈ Sfin, u.1 = v} with hT
  have hinfT (w : InfinitePlace K) : w.1 ∈ T := Or.inl ⟨w, rfl⟩
  have hfinT (u : FinitePlace K) (hu : u ∈ Sfin) : u.1 ∈ T := Or.inr ⟨u, hu, rfl⟩
  -- The approximation constant: `1` at the finite places, `A₀` at the infinite ones.
  set A : AbsoluteValue K ℝ → ℝ := fun v ↦ if IsNonarchimedean v then 1 else A₀ with hA
  have hAinf (w : InfinitePlace K) : A w.1 = A₀ := by simp [hA, w.not_isNonarchimedean]
  have hAfin (u : FinitePlace K) : A u.1 = 1 := by
    simp only [hA, ite_eq_left_iff]
    exact fun h ↦ absurd u.add_le h
  have happrox (γ : AbsoluteValue K ℝ → K) :
      ∃ ξ ∈ {ξ : K | ∀ u : FinitePlace K, u ∉ Sfin → u ξ ≤ 1}, ∀ v ∈ T, v (ξ + γ v) ≤ A v := by
    obtain ⟨ξ, hout, hS, hinf'⟩ := hA₀ Sfin γ
    refine ⟨ξ, hout, ?_⟩
    rintro v (⟨w, rfl⟩ | ⟨u, hu, rfl⟩)
    · rw [hAinf]
      exact hinf' w
    · rw [hAfin]
      exact hS u hu
  obtain ⟨ξ, π, hξ, hbound, hbound_na⟩ := AbsoluteValue.exists_evertse_of_approx happrox
    (L := L) (x := x) (ν := ν) (μ := μ)
    (by
      rintro v (⟨w, rfl⟩ | ⟨u, hu, rfl⟩) z hz
      · exact (hLinf w).eq_zero_of_forall_apply_eq_zero hcard hz
      · exact (hLfin u hu).eq_zero_of_forall_apply_eq_zero hcard hz)
    x.linearIndependent
    (by
      rintro v (⟨w, rfl⟩ | ⟨u, hu, rfl⟩)
      · exact hνinf w
      · exact hνfin u hu)
    (by
      rintro v (⟨w, rfl⟩ | ⟨u, hu, rfl⟩)
      · exact hμinf w
      · exact hμfin u hu)
    (by
      rintro v (⟨w, rfl⟩ | ⟨u, hu, rfl⟩)
      · exact hinf w
      · exact hfin u hu)
  refine ⟨ξ, π, fun j l ↦ hξ j l, fun w i j ↦ ?_, fun u hu i j ↦ ?_⟩
  · have h := hbound w.1 (hinfT w) i j
    rwa [hAinf] at h
  · exact hbound_na u.1 (hfinT u hu) u.add_le (hAfin u).le i j

/-- **Evertse's lemma without weights** (Evertse; Bombieri–Gubler, Lemma 7.5.29): the case
`ν = 1` of `NumberField.exists_evertse`. If `|L v k (x j)|_v ≤ μ v j` with `μ v` nondecreasing,
then the corrected basis satisfies `|L v (π v i) (y j)|_v ≤ C * min (μ v i) (μ v j)` at the
infinite places and `|L v (π v i) (y j)|_v ≤ min (μ v i) (μ v j)` at the places of `S₀`. -/
theorem exists_evertse_unweighted (m : ℕ) :
    ∃ C : ℝ, ∀ (V : Type*) [AddCommGroup V] [Module K V] (Sfin : Finset (FinitePlace K))
      (L : AbsoluteValue K ℝ → Fin m → Module.Dual K V) (x : Module.Basis (Fin m) K V)
      (μ : AbsoluteValue K ℝ → Fin m → ℝ),
      (∀ v : InfinitePlace K, LinearIndependent K (L v.1)) →
      (∀ v ∈ Sfin, LinearIndependent K (L v.1)) →
      (∀ v : InfinitePlace K, Monotone (μ v.1)) → (∀ v ∈ Sfin, Monotone (μ v.1)) →
      (∀ (v : InfinitePlace K) k j, v (L v.1 k (x j)) ≤ μ v.1 j) →
      (∀ v ∈ Sfin, ∀ k j, v (L v.1 k (x j)) ≤ μ v.1 j) →
      ∃ (ξ : Fin m → Fin m → K) (π : AbsoluteValue K ℝ → Equiv.Perm (Fin m)),
        (∀ j l, ∀ u : FinitePlace K, u ∉ Sfin → u (ξ j l) ≤ 1) ∧
        (∀ (v : InfinitePlace K) i j,
          v (L v.1 (π v.1 i) (x j + ∑ l ∈ univ.filter (· < j), ξ j l • x l)) ≤
            C * min (μ v.1 i) (μ v.1 j)) ∧
        ∀ v ∈ Sfin, ∀ i j,
          v (L v.1 (π v.1 i) (x j + ∑ l ∈ univ.filter (· < j), ξ j l • x l)) ≤
            min (μ v.1 i) (μ v.1 j) := by
  obtain ⟨C, hC⟩ := exists_evertse (K := K) m
  refine ⟨C, fun V _ _ Sfin L x μ hLinf hLfin hμinf hμfin hinf hfin ↦ ?_⟩
  obtain ⟨ξ, π, hξ, hbinf, hbfin⟩ := hC V Sfin L x (fun _ _ ↦ 1) μ hLinf hLfin
    (fun _ _ ↦ one_pos) (fun _ _ _ ↦ one_pos) hμinf hμfin (by simpa using hinf)
    (by simpa using hfin)
  exact ⟨ξ, π, hξ, by simpa using hbinf, by simpa using hbfin⟩

end NumberField
