/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Reductive.Basic
public import TauCeti.Algebra.Lie.AdjointAction.Basic
public import TauCeti.Algebra.Lie.AdjointAction.InvariantZeroLocus
import TauCeti.Algebra.Lie.Killing.AdNilpotent
import TauCeti.Algebra.Lie.TracePowerPolynomial

/-!
# The common zeros of the invariants of a reductive Lie algebra

Let `L` be a finite-dimensional reductive Lie algebra over a field `K` of characteristic zero, so
that `L = Z(L) ⊕ ⁅L, L⁆` with `⁅L, L⁆` semisimple. The invariant polynomial functions on `L`
(`TauCeti.SymmetricAlgebra.lieInvariants`) of positive degree include the linear functions
vanishing on `⁅L, L⁆`, the *central coordinates*, and their common zero locus is therefore
smaller than the set of `ad`-nilpotent elements. This file computes the common zero locus and
compares it with the `ad`-nilpotent elements.

* The common zeros of the invariants of positive degree are the `ad`-nilpotent elements of the
  derived ideal (`TauCeti.mem_derivedSeries_and_isNilpotent_ad_iff_forall_lift_eval_eq_zero`).
  Writing `x = z + y` with `z` central and `y ∈ ⁅L, L⁆`, the element `x` is a common zero exactly
  when its central coordinate `z` vanishes and `y` is `ad`-nilpotent
  (`TauCeti.forall_lift_eval_add_eq_zero_iff`).
* The `ad`-nilpotent elements are the sums `z + y` of an arbitrary central element `z` and an
  `ad`-nilpotent element `y` of `⁅L, L⁆` (`TauCeti.isNilpotent_ad_iff_exists_mem_center_add`, in
  `TauCeti.Algebra.Lie.Reductive.Basic`), and `y` is `ad`-nilpotent in `L` exactly when it is
  `ad`-nilpotent in the semisimple Lie algebra `⁅L, L⁆` (`LieIdeal.isNilpotent_ad_iff`).

So the zero locus of the invariants of positive degree is `{0} × 𝒩(⁅L, L⁆)`, while the
`ad`-nilpotent locus is the larger set `Z(L) × 𝒩(⁅L, L⁆)`, where `𝒩(⁅L, L⁆)` is the set of
`ad`-nilpotent elements of the derived ideal. For a semisimple Lie algebra the centre vanishes and
both are the `ad`-nilpotent elements (`TauCeti.isNilpotent_ad_iff_forall_lift_eval_eq_zero`).

A common zero lies in `⁅L, L⁆` because the central coordinates are invariants
(`TauCeti.mem_derivedSeries_of_forall_lift_eval_eq_zero`), and it is `ad`-nilpotent by the trace
criterion. Conversely an `ad`-nilpotent element `x` of the semisimple Lie algebra `⁅L, L⁆` is a
bracket `x = ⁅x, t⁆` with some `t ∈ ⁅L, L⁆` (`TauCeti.exists_lie_eq_self_of_isNilpotent_ad`), that
is an eigenvector of `ad t` for the eigenvalue `-1`, and invariants of positive degree vanish at
such eigenvectors.

## Main results

* `TauCeti.mem_derivedSeries_and_isNilpotent_ad_iff_forall_lift_eval_eq_zero`: in a reductive Lie
  algebra, the common zeros of the invariants of positive degree are the `ad`-nilpotent elements
  of the derived ideal.
* `TauCeti.forall_lift_eval_add_eq_zero_iff`: the same in the coordinates of `Z(L) ⊕ ⁅L, L⁆`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §6.4.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.1.
* B. Kostant, *Lie group representations on polynomial rings*, Amer. J. Math. 85 (1963),
  327–404.
-/

public section

open LieAlgebra LieModule Module _root_.SymmetricAlgebra

namespace TauCeti

open SymmetricAlgebra

section Reductive

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [HasCentralRadical K L]

/-- **The common zeros of the invariants of a reductive Lie algebra.** In a finite-dimensional
reductive Lie algebra over a field of characteristic zero, every invariant polynomial function with
zero constant term vanishes at `x` exactly when `x` lies in the derived ideal `⁅L, L⁆` and `ad x` is
nilpotent. The central elements, which are `ad`-nilpotent, are not common zeros unless they vanish
(`TauCeti.forall_lift_eval_add_eq_zero_iff`). -/
theorem mem_derivedSeries_and_isNilpotent_ad_iff_forall_lift_eval_eq_zero {x : L} :
    x ∈ derivedSeries K L 1 ∧ IsNilpotent (ad K L x) ↔
      ∀ p ∈ lieInvariants K L (Dual K L), algebraMapInv p = 0 → lift (Dual.eval K L x) p = 0 := by
  refine ⟨fun ⟨hx, hnil⟩ p hp hp₀ ↦ ?_, fun h ↦ ⟨mem_derivedSeries_of_forall_lift_eval_eq_zero h,
    isNilpotent_toEnd_of_forall_lift_eval_eq_zero L h⟩⟩
  -- the derived ideal is semisimple, so there `x` is a bracket `x = ⁅x, t⁆`
  obtain ⟨t, ht⟩ := exists_lie_eq_self_of_isNilpotent_ad (K := K) (L := derivedSeries K L 1)
    (x := ⟨x, hx⟩) ((LieIdeal.isNilpotent_ad_iff _).mpr hnil)
  refine lift_eval_eq_zero_of_mem_lieInvariants hp hp₀ (y := (t : L)) (a := -1) ?_
    (neg_ne_zero.mpr one_ne_zero)
  rw [← lie_skew, neg_one_smul]
  exact congrArg (fun w : derivedSeries K L 1 ↦ -(w : L)) ht

/-- **The zero locus of the invariants in the coordinates `Z(L) ⊕ ⁅L, L⁆`.** In a
finite-dimensional reductive Lie algebra over a field of characteristic zero, let `z` be central
and `y ∈ ⁅L, L⁆`. Every invariant polynomial function with zero constant term vanishes at `z + y`
exactly when the central coordinate `z` is zero and `ad y` is nilpotent. -/
theorem forall_lift_eval_add_eq_zero_iff {z y : L} (hz : z ∈ center K L)
    (hy : y ∈ derivedSeries K L 1) :
    (∀ p ∈ lieInvariants K L (Dual K L), algebraMapInv p = 0 →
      lift (Dual.eval K L (z + y)) p = 0) ↔ z = 0 ∧ IsNilpotent (ad K L y) := by
  rw [← mem_derivedSeries_and_isNilpotent_ad_iff_forall_lift_eval_eq_zero,
    LieAlgebra.isNilpotent_ad_add_iff_of_mem_center_left hz, add_mem_cancel_right hy]
  refine and_congr_left fun _ ↦ ⟨fun hz' ↦ ?_, fun h ↦ h ▸ zero_mem _⟩
  have h := center_inf_derivedSeries_eq_bot K L
  rw [← LieSubmodule.mem_bot (R := K) (L := L) z, ← h]
  exact ⟨hz, hz'⟩

end Reductive

end TauCeti
