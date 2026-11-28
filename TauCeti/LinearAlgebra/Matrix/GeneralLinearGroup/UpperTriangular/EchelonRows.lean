/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Order.Interval.Finset.Fin

/-!
# Echelon row vectors and hyperplane-intersection counts over finite fields

For a finite field `k` and an index `r : Fin N`, the finset `TauCeti.echelonRows k r` consists of
the row vectors `u : Fin N → k` with `u r = 1` and `u i = 0` for all `i < r`. Counting how many
such echelon rows lie in a subspace `L ≤ (Fin N → k)` whose elements vanish on coordinates `< r`
is a core combinatorial step in computing Iwahori–Hecke partial sums and Satake's formula).

* `TauCeti.echelonRows`: the finset of echelon row vectors with pivot `1` at `r : Fin N`.
* `TauCeti.mem_echelonRows`: membership characterization `u r = 1 ∧ ∀ i < r, u i = 0`.
* `TauCeti.card_echelonRows`: `#(echelonRows k r) = Fintype.card k ^ r.rev.val`.
* `TauCeti.card_echelonRows_mem_submodule`: for a subspace `L ≤ (Fin N → k)` vanishing on
  coordinates `< r`, `#{u ∈ echelonRows k r | u ∈ L}` is `0` if every `u ∈ L` has `u r = 0`, and
  `Fintype.card k ^ (Module.finrank k L - 1)` otherwise.

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
theorem card_echelonRows : #(echelonRows k r) = Fintype.card k ^ r.rev.val := by
  simp [echelonRows, apply_ite card, prod_ite, Finset.filter_lt_eq_Ioi, Fin.card_Ioi,
    Fin.val_rev, tsub_add_eq_tsub_tsub_swap]

end Basic

section Submodule

variable {k : Type*} [Field k] [Fintype k] {N : ℕ}

/-- Let `L : Submodule k (Fin N → k)` be a subspace whose elements vanish on all coordinates `< r`.
Then the number of echelon rows in `echelonRows k r` belonging to `L` is `0` if every `u ∈ L`
satisfies `u r = 0`, and `Fintype.card k ^ (Module.finrank k L - 1)` otherwise. -/
theorem card_echelonRows_mem_submodule [DecidableEq k] (r : Fin N) (L : Submodule k (Fin N → k))
    (hL : ∀ u ∈ L, ∀ i < r, u i = 0) [DecidablePred (· ∈ L)] :
    #{u ∈ echelonRows k r | u ∈ L} =
      if ∀ u ∈ L, u r = 0 then 0 else Fintype.card k ^ (Module.finrank k L - 1) := by
  classical
  split_ifs with hzero
  · rw [Finset.card_eq_zero, filter_eq_empty_iff]
    intro u hu huL
    exact one_ne_zero (((mem_echelonRows k r).mp hu).left.symm.trans (hzero u huL))
  · push Not at hzero
    obtain ⟨v₀, hv₀L, hv₀r⟩ := hzero
    let p : L →ₗ[k] k := (LinearMap.proj r).comp L.subtype
    have hp_surj : Function.Surjective p := fun c ↦
      ⟨(c * (v₀ r)⁻¹) • ⟨v₀, hv₀L⟩, by simp [p, hv₀r]⟩
    have h_dim : Module.finrank k (LinearMap.ker p) = Module.finrank k L - 1 := by
      have h_rk := Submodule.finrank_quotient_add_finrank (LinearMap.ker p)
      rw [(p.quotKerEquivOfSurjective hp_surj).finrank_eq, Module.finrank_self] at h_rk
      omega
    have h_card_ker : Nat.card (LinearMap.ker p) = Fintype.card k ^ (Module.finrank k L - 1) := by
      have : Module.Free k (LinearMap.ker p) :=
        Module.Free.of_basis (Module.Basis.ofVectorSpace k (LinearMap.ker p))
      rw [Nat.card_congr (Module.finBasis k (LinearMap.ker p)).equivFun.toEquiv,
        Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, h_dim]
    have h_fibre : Nat.card (p.toAddMonoidHom ⁻¹' {1}) =
        Fintype.card k ^ (Module.finrank k L - 1) := by
      rw [Nat.card_congr (p.toAddMonoidHom.fiberEquivKerOfSurjective hp_surj 1)]
      exact h_card_ker
    let e : {u : Fin N → k // u ∈ {u ∈ echelonRows k r | u ∈ L}} ≃ (p.toAddMonoidHom ⁻¹' {1}) :=
      { toFun u := ⟨⟨u.val, (mem_filter.mp u.property).right⟩,
          ((mem_echelonRows k r).mp (mem_filter.mp u.property).left).left⟩
        invFun u := ⟨u.val.val, mem_filter.mpr
          ⟨(mem_echelonRows k r).mpr ⟨u.property, hL u.val.val u.val.property⟩, u.val.property⟩⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card, Nat.card_congr e, h_fibre]

end Submodule

end TauCeti
