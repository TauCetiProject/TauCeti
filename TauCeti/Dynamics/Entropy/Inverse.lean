/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy
public import Mathlib.Topology.Homeomorph.Defs

/-!
# Topological entropy of the inverse of a bijection

A bijection `e : X ≃ X` and its inverse have the same topological entropy on every invariant set:
`coverEntropy e.symm F = coverEntropy e F` when `e '' F = F`, in particular on `univ`, and the
same holds for `coverEntropyInf`. No continuity is needed, so this applies to every homeomorphism
of a uniform space.

Two points are close for `n + 1` steps of `e.symm` exactly when their images under
`e.symm^[n]` are close for `n + 1` steps of `e` (`TauCeti.dynEntourage_symm`): both conditions say
that `e^[j] x` and `e^[j] y` are close for `-n ≤ j ≤ 0`, read in the two time directions. Pushing
dynamical covers forward by `e.symm^[n]` and back by `e^[n]` matches the minimal covers
(`TauCeti.coverMincard_symm`).

## Main results

* `TauCeti.dynEntourage_symm`: the identity above.
* `TauCeti.coverMincard_symm`: minimal dynamical covers of `e.symm` and of `e`.
* `TauCeti.coverEntropy_symm`, `TauCeti.coverEntropyInf_symm`: equality of the entropies on a set
  `F` with `e '' F = F`, `TauCeti.coverEntropy_symm_univ` on the whole space, and
  `TauCeti.coverEntropy_homeomorph_symm` for a homeomorphism.
-/

public section

namespace TauCeti

open Dynamics Set
open scoped Uniformity

variable {X : Type*}

/-- `e^[j]` undoes `j` of the `n` steps of `e.symm^[n]`. -/
private lemma iterate_iterate_symm (e : X ≃ X) {j n : ℕ} (hj : j ≤ n) (x : X) :
    e^[j] (e.symm^[n] x) = e.symm^[n - j] x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
  have h : Function.LeftInverse e e.symm := e.apply_symm_apply
  rw [Nat.add_sub_cancel_left, Function.iterate_add_apply, h.iterate j]

/-- Two points are close for `n + 1` steps of `e.symm` exactly when their images under
`e.symm^[n]` are close for `n + 1` steps of `e`. -/
theorem dynEntourage_symm (e : X ≃ X) (U : SetRel X X) (n : ℕ) :
    dynEntourage e.symm U (n + 1) =
      Prod.map (e.symm^[n]) (e.symm^[n]) ⁻¹' dynEntourage e U (n + 1) := by
  ext ⟨x, y⟩
  simp only [mem_preimage, Prod.map_apply, mem_dynEntourage, Nat.lt_succ_iff]
  constructor
  · intro h j hj
    rw [iterate_iterate_symm e hj, iterate_iterate_symm e hj]
    exact h _ (Nat.sub_le n j)
  · intro h k hk
    have := h (n - k) (Nat.sub_le n k)
    rwa [iterate_iterate_symm e (Nat.sub_le n k), iterate_iterate_symm e (Nat.sub_le n k),
      Nat.sub_sub_self hk] at this

/-- Minimal dynamical covers of `F` for `e.symm` correspond to minimal dynamical covers of
`e.symm^[n] '' F` for `e`, at time `n + 1`. -/
theorem coverMincard_symm (e : X ≃ X) (F : Set X) (U : SetRel X X) (n : ℕ) :
    coverMincard e.symm F U (n + 1) = coverMincard e (e.symm^[n] '' F) U (n + 1) := by
  classical
  have hinv : ∀ x, e.symm^[n] (e^[n] x) = x :=
    (show Function.LeftInverse e.symm e from e.symm_apply_apply).iterate n
  refine le_antisymm (le_iInf₂ fun t ht ↦ ?_) (le_iInf₂ fun s hs ↦ ?_)
  · -- push a cover of `e.symm^[n] '' F` for `e` back by `e^[n]`
    refine ((?_ : IsDynCoverOf e.symm F U (n + 1) (t.image (e^[n]))).coverMincard_le_card).trans
      (by exact_mod_cast Finset.card_image_le)
    intro y hy
    obtain ⟨x, hx, hxy⟩ := ht (mem_image_of_mem _ hy)
    refine ⟨e^[n] x, by simpa using ⟨x, hx, rfl⟩, ?_⟩
    rw [dynEntourage_symm, mem_preimage, Prod.map_apply, hinv]
    exact hxy
  · -- push a cover of `F` for `e.symm` forward by `e.symm^[n]`
    refine ((?_ : IsDynCoverOf e (e.symm^[n] '' F) U (n + 1)
      (s.image (e.symm^[n]))).coverMincard_le_card).trans (by exact_mod_cast Finset.card_image_le)
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hs hy
    refine ⟨e.symm^[n] x, by simpa using ⟨x, hx, rfl⟩, ?_⟩
    have : (y, x) ∈ dynEntourage e.symm U (n + 1) := hxy
    rwa [dynEntourage_symm] at this

/-- If `e '' F = F`, the iterates of `e.symm` also map `F` onto itself. -/
private lemma image_iterate_symm_of_image_eq {e : X ≃ X} {F : Set X} (hF : e '' F = F) (n : ℕ) :
    e.symm^[n] '' F = F := by
  have h1 : e.symm '' F = F := by
    conv_lhs => rw [← hF]
    rw [image_image]
    simp
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ', image_comp, ih, h1]

/-- On a set `F` with `e '' F = F`, minimal dynamical covers of `e.symm` and of `e` have the same
cardinality. -/
theorem coverMincard_symm_of_image_eq {e : X ≃ X} {F : Set X} (hF : e '' F = F)
    (U : SetRel X X) (n : ℕ) : coverMincard e.symm F U n = coverMincard e F U n := by
  rcases n with _ | n
  · simp only [coverMincard, IsDynCoverOf, dynEntourage, not_lt_zero, iInter_of_empty,
      iInter_univ]
  · rw [coverMincard_symm, image_iterate_symm_of_image_eq hF]

/-- On a set `F` with `e '' F = F`, the cover entropy of `e.symm` at an entourage is that of `e`. -/
theorem coverEntropyEntourage_symm {e : X ≃ X} {F : Set X} (hF : e '' F = F) (U : SetRel X X) :
    coverEntropyEntourage e.symm F U = coverEntropyEntourage e F U := by
  simp only [coverEntropyEntourage, coverMincard_symm_of_image_eq hF]

/-- On a set `F` with `e '' F = F`, the `liminf` cover entropy of `e.symm` at an entourage is that
of `e`. -/
theorem coverEntropyInfEntourage_symm {e : X ≃ X} {F : Set X} (hF : e '' F = F)
    (U : SetRel X X) : coverEntropyInfEntourage e.symm F U = coverEntropyInfEntourage e F U := by
  simp only [coverEntropyInfEntourage, coverMincard_symm_of_image_eq hF]

variable [UniformSpace X]

/-- A bijection and its inverse have the same topological entropy on every set `F` with
`e '' F = F`. -/
theorem coverEntropy_symm {e : X ≃ X} {F : Set X} (hF : e '' F = F) :
    coverEntropy e.symm F = coverEntropy e F := by
  simp only [coverEntropy, coverEntropyEntourage_symm hF]

/-- A bijection and its inverse have the same `liminf` topological entropy on every set `F` with
`e '' F = F`. -/
theorem coverEntropyInf_symm {e : X ≃ X} {F : Set X} (hF : e '' F = F) :
    coverEntropyInf e.symm F = coverEntropyInf e F := by
  simp only [coverEntropyInf, coverEntropyInfEntourage_symm hF]

/-- A bijection and its inverse have the same topological entropy. In particular a homeomorphism
`h` satisfies `coverEntropy h.symm univ = coverEntropy h univ`. -/
theorem coverEntropy_symm_univ (e : X ≃ X) : coverEntropy e.symm univ = coverEntropy e univ :=
  coverEntropy_symm (by rw [image_univ, e.range_eq_univ])

/-- A homeomorphism and its inverse have the same topological entropy. -/
theorem coverEntropy_homeomorph_symm (h : X ≃ₜ X) :
    coverEntropy h.symm univ = coverEntropy h univ :=
  coverEntropy_symm_univ h.toEquiv

end TauCeti
