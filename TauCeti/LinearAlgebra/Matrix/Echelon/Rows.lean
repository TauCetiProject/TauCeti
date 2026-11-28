/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Fin.Rev
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Order.Interval.Finset.Fin

/-!
# Echelon row vectors and hyperplane-intersection counts over finite division rings

For a finite division ring `k` and an index `r : Fin N`, the finset `TauCeti.echelonRows k r`
consists of the row vectors `u : Fin N → k` with `u r = 1` and `u i = 0` for all `i < r`.
Counting how many such echelon rows lie in a subspace `L ≤ (Fin N → k)` whose elements vanish on
coordinates `< r` is a core combinatorial step in computing Iwahori–Hecke partial sums and
Satake's formula.

* `TauCeti.echelonRows`: the finset of echelon row vectors with pivot `1` at `r : Fin N`.
* `TauCeti.mem_echelonRows`: membership characterization `u r = 1 ∧ ∀ i < r, u i = 0`.
* `TauCeti.card_echelonRows`: `#(echelonRows k r) = Fintype.card k ^ r.rev.val`.
* `Fin.card_echelonRows_mem_submodule`: for a subspace `L ≤ (Fin N → k)` vanishing on
  coordinates `< r`, `#{u ∈ TauCeti.echelonRows k r | u ∈ L}` is `0` if every `u ∈ L` has
  `u r = 0`, and `Fintype.card k ^ (Module.finrank k L - 1)` otherwise.

## References

* I. G. Macdonald, *Spherical functions on a group of `p`-adic type*, Publications of the
  Ramanujan Institute 2 (1971).

## Provenance

* Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
  PBC), file `src/Lib/LocalGL/Iwahori/HeckeDegrees.lean` (`New.echelonRows`,
  `New.mem_echelonRows`, `New.card_echelonRows`, `New.card_echelonRows_mem_residueKer`).
-/

public section

open Finset

namespace TauCeti

section Basic

variable (k : Type*) [Fintype k] [Zero k] [One k] {N : ℕ} (r : Fin N)

/-- The finset of echelon row vectors `(0, …, 0, 1, *, …, *)` in `Fin N → k` with entry `1` at
`r` and `0` at all indices `< r`. -/
def echelonRows : Finset (Fin N → k) :=
  Fintype.piFinset fun i ↦ if r < i then univ else {if r = i then (1 : k) else 0}

/-- A vector `u : Fin N → k` belongs to `echelonRows k r` iff `u r = 1` and `u i = 0` for all
`i < r`. -/
@[simp, grind =]
theorem mem_echelonRows {u : Fin N → k} :
    u ∈ echelonRows k r ↔ u r = 1 ∧ ∀ i < r, u i = 0 := by
  simp only [echelonRows, Fintype.mem_piFinset]
  refine ⟨fun hu ↦ ⟨?_, fun i hi ↦ ?_⟩, fun ⟨h_one, h_zero⟩ i ↦ ?_⟩
  · simpa using hu r
  · simpa [hi.asymm, hi.ne'] using hu i
  · obtain hi | rfl | hi := lt_trichotomy i r
    · simp [hi.asymm, hi.ne', h_zero i hi]
    · simp [h_one]
    · simp [hi]

/-- There are `Fintype.card k ^ r.rev.val` echelon rows with pivot `1` at `r : Fin N`. -/
@[simp]
theorem card_echelonRows : #(echelonRows k r) = Fintype.card k ^ r.rev.val := by
  simp [echelonRows, apply_ite card, prod_ite, Finset.filter_lt_eq_Ioi, Fin.card_Ioi,
    Fin.val_rev, tsub_add_eq_tsub_tsub_swap]

end Basic

end TauCeti

namespace Fin

section Submodule

variable {k : Type*} [DivisionRing k] [Fintype k] {N : ℕ}

/-- Let `L : Submodule k (Fin N → k)` be a subspace whose elements vanish on all coordinates `< r`.
Then the number of echelon rows in `TauCeti.echelonRows k r` belonging to `L` is `0` if every
`u ∈ L` satisfies `u r = 0`, and `Fintype.card k ^ (Module.finrank k L - 1)` otherwise. -/
theorem card_echelonRows_mem_submodule [DecidableEq k] (r : Fin N) (L : Submodule k (Fin N → k))
    (hL : ∀ u ∈ L, ∀ i < r, u i = 0) [DecidablePred (· ∈ L)] :
    #{u ∈ TauCeti.echelonRows k r | u ∈ L} =
      if ∀ u ∈ L, u r = 0 then 0 else Fintype.card k ^ (Module.finrank k L - 1) := by
  classical
  split_ifs with hzero
  · rw [Finset.card_eq_zero, filter_eq_empty_iff]
    intro u hu huL
    exact one_ne_zero (((TauCeti.mem_echelonRows k r).mp hu).left.symm.trans (hzero u huL))
  · push Not at hzero
    obtain ⟨v₀, hv₀L, hv₀r⟩ := hzero
    let p : L →ₗ[k] k := (LinearMap.proj r).comp L.subtype
    have hp : p ≠ 0 := fun h ↦ hv₀r (by simpa [p] using LinearMap.congr_fun h ⟨v₀, hv₀L⟩)
    have hp_surj : Function.Surjective p := LinearMap.surjective hp
    have h_dim : Module.finrank k (LinearMap.ker p) = Module.finrank k L - 1 := by
      have := Module.Dual.finrank_ker_add_one_of_ne_zero hp
      omega
    have h_card_ker : Nat.card (LinearMap.ker p) = Fintype.card k ^ (Module.finrank k L - 1) := by
      rw [Module.natCard_eq_pow_finrank (K := k), Nat.card_eq_fintype_card, h_dim]
    have h_fibre : Nat.card (p.toAddMonoidHom ⁻¹' {1}) =
        Fintype.card k ^ (Module.finrank k L - 1) := by
      rw [Nat.card_congr (p.toAddMonoidHom.fiberEquivKerOfSurjective hp_surj 1)]
      exact h_card_ker
    let e : {u : Fin N → k // u ∈ {u ∈ TauCeti.echelonRows k r | u ∈ L}} ≃
        (p.toAddMonoidHom ⁻¹' {1}) :=
      { toFun u := ⟨⟨u.val, (mem_filter.mp u.property).right⟩,
          ((TauCeti.mem_echelonRows k r).mp (mem_filter.mp u.property).left).left⟩
        invFun u := ⟨u.val.val, mem_filter.mpr
          ⟨(TauCeti.mem_echelonRows k r).mpr ⟨u.property, hL u.val.val u.val.property⟩,
            u.val.property⟩⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card, Nat.card_congr e, h_fibre]

end Submodule

end Fin
