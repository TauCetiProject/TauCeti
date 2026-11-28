/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Ramsey.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Dist

/-!
# Schur's theorem from Ramsey numbers

Schur's theorem states that any colouring of `{1, …, N}` with finitely many colours contains a
monochromatic solution to `x + y = z` (with `x = y` allowed) as soon as `N + 1` is at least the
multicolour triangle Ramsey number `R(3, …, 3)`.

Given `c : ℕ → κ`, we colour each edge `{i, j}` of the complete graph on `Fin (N + 1)` by
`c (Nat.dist i j)` (`SimpleGraph.EdgeLabeling.mk`). A monochromatic triangle ordered by
`Finset.orderEmbOfFin` as `i < j < l` yields `x = j - i`, `y = l - j`, and `x + y = l - i ≤ N`,
all of the same colour. The Ramsey-property version `TauCeti.exists_add_eq_of_ramseyProp` needs no
finiteness hypothesis on `κ`; for finite `κ`, combining it with
`TauCeti.ramseyProp_iff_ramseyNumber_le` gives `TauCeti.exists_add_eq_of_ramseyNumber_le`.

## Main results

* `TauCeti.exists_add_eq_of_ramseyProp`: Schur's theorem from the triangle Ramsey property on
  `N + 1` vertices, for any colour type `κ`.
* `TauCeti.exists_add_eq_of_ramseyNumber_le`: Schur's theorem with the explicit bound
  `ramseyNumber (fun _ : κ ↦ 3) ≤ N + 1` for finite `κ`.

## References

* I. Schur (1916), as attributed in Diestel and Radziszowski below.
* R. Diestel, *Graph Theory*, Chapter 9, Exercise 14, p. 320 (existence of a monochromatic solution
  to `x + y = z`).
* S. P. Radziszowski, *Small Ramsey numbers*, Electronic Journal of Combinatorics, Dynamic Survey
  DS1, §6.2, item (i), p. 58 (the Ramsey-number bound `R(3, …, 3) ≥ S + 2`).
-/

public section

open Finset SimpleGraph

namespace TauCeti

/-- **Schur's theorem** (Ramsey-property form): for any type of colours `κ`, if every `κ`-colouring
of the edges of the complete graph on `N + 1` vertices has a monochromatic triangle, then every
colouring `c : ℕ → κ` admits positive `x`, `y` with `x + y ≤ N` and `c x = c y = c (x + y)`
(`x = y` is allowed). -/
theorem exists_add_eq_of_ramseyProp {κ : Type*} (c : ℕ → κ) (N : ℕ)
    (hN : RamseyProp (fun _ : κ ↦ 3) (N + 1)) :
    ∃ x y, 0 < x ∧ 0 < y ∧ x + y ≤ N ∧ c x = c y ∧ c (x + y) = c x := by
  let C : TopEdgeLabeling (Fin (N + 1)) κ :=
    EdgeLabeling.mk (fun i j _ ↦ c (Nat.dist i j)) fun i j _ ↦ by rw [Nat.dist_comm]
  obtain ⟨k, s, hs⟩ := ramseyProp_iff.1 hN C
  let e : Fin 3 ↪o Fin (N + 1) := s.orderEmbOfFin hs.card_eq
  have hcol {p q : Fin 3} (hpq : p < q) : c ((e q : ℕ) - e p) = k := by
    have hadj : (C.labelGraph k).Adj (e p) (e q) :=
      hs.isClique (orderEmbOfFin_mem s hs.card_eq p) (orderEmbOfFin_mem s hs.card_eq q)
        (e.injective.ne hpq.ne)
    rw [TopEdgeLabeling.labelGraph_adj] at hadj
    obtain ⟨_, hk⟩ := hadj
    rw [EdgeLabeling.get_mk, Nat.dist_eq_sub_of_le (e.strictMono hpq).le] at hk
    exact hk
  have h01 : (e 0 : ℕ) < e 1 := e.strictMono (by decide : (0 : Fin 3) < 1)
  have h12 : (e 1 : ℕ) < e 2 := e.strictMono (by decide : (1 : Fin 3) < 2)
  have hsum : (e 1 - e 0 : ℕ) + (e 2 - e 1) = e 2 - e 0 := by omega
  refine ⟨e 1 - e 0, e 2 - e 1, by omega, by omega, by have := (e 2).isLt; omega, ?_, ?_⟩
  · rw [hcol (by decide : (0 : Fin 3) < 1), hcol (by decide : (1 : Fin 3) < 2)]
  · rw [hsum, hcol (by decide : (0 : Fin 3) < 2), hcol (by decide : (0 : Fin 3) < 1)]

/-- **Schur's theorem** with the Ramsey bound: if `κ` is finite and `R(3, …, 3)`, with demand `3`
for every colour in `κ`, is at most `N + 1`, then every colouring `c : ℕ → κ` admits positive `x`,
`y` with `x + y ≤ N` and `c x = c y = c (x + y)` (`x = y` is allowed). -/
theorem exists_add_eq_of_ramseyNumber_le {κ : Type*} [Finite κ] (c : ℕ → κ) (N : ℕ)
    (hN : ramseyNumber (fun _ : κ ↦ 3) ≤ N + 1) :
    ∃ x y, 0 < x ∧ 0 < y ∧ x + y ≤ N ∧ c x = c y ∧ c (x + y) = c x :=
  exists_add_eq_of_ramseyProp c N (ramseyProp_iff_ramseyNumber_le.2 hN)

end TauCeti
