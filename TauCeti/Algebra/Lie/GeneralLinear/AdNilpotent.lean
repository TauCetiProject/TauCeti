/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.Algebra.Lie.GeneralLinear.Basic
import TauCeti.Algebra.Lie.AdjointAction.JordanChevalley

/-!
# Ad-nilpotent matrices in `gl n` and `sl n`

This file compares the type-`A` nilpotent cone, defined through the adjoint action, with nilpotent
matrices, both in `gl n K` and in its trace-zero subalgebra `sl n K`.

In the reductive Lie algebra `gl n K` the adjoint action ignores the centre, so ad-nilpotence alone
allows an arbitrary scalar component: over a perfect field, `ad X` is nilpotent exactly when
`X - c • 1` is a nilpotent matrix for some scalar `c`. Inside `sl n K`, when the size of the
matrices is nonzero in `K`, the trace forces `c = 0`. So the elements of `sl n K` with nilpotent
adjoint action are exactly the nilpotent matrices, and since nilpotent matrices have trace zero,
these are all the nilpotent `n × n` matrices.

The corresponding comparison of centralizers, `TauCeti.finrank_ker_ad_sl_add_one`, needs no
nilpotence and lives with the other dimension counts in `TauCeti.Algebra.Lie.GeneralLinear.Finrank`.

## Main statements

* `TauCeti.isNilpotent_ad_matrix_iff`: `ad X` is nilpotent iff `X` is a scalar plus a nilpotent
  matrix.
* `TauCeti.isNilpotent_ad_of_isNilpotent_ad_sl`: ad-nilpotence of `x ∈ sl n K` on `sl n K` implies
  ad-nilpotence on `gl n K`.
* `TauCeti.isNilpotent_ad_sl_iff`: for `x ∈ sl n K`, `ad x` is nilpotent iff `x` is a nilpotent
  matrix.
* `TauCeti.image_setOf_isNilpotent_ad_sl`: the ad-nilpotent elements of `sl n K`, viewed as
  matrices, are exactly the nilpotent matrices.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §4.2.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Chapter 6.
-/

public section

namespace TauCeti

open _root_.LieAlgebra Module

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

/-- **Ad-nilpotent matrices.** Over a perfect field, the adjoint action of a square matrix `X` on
`gl n K` is nilpotent exactly when `X` is a scalar matrix plus a nilpotent matrix. -/
theorem isNilpotent_ad_matrix_iff [PerfectField K] {X : Matrix n n K} :
    IsNilpotent (ad K (Matrix n n K) X) ↔ ∃ c : K, IsNilpotent (X - c • 1) := by
  let e : Matrix n n K ≃ₐ[K] End K (n → K) := Matrix.toLinAlgEquiv'
  have he : IsNilpotent (ad K (Matrix n n K) X) ↔ IsNilpotent (ad K (End K (n → K)) (e X)) := by
    rw [← AlgEquiv.toLieEquiv_apply, ← conj_ad_apply]
    exact (IsNilpotent.map_iff e.toLieEquiv.toLinearEquiv.conjRingEquiv.injective).symm
  rw [he, LieAlgebra.isNilpotent_ad_iff_exists_isNilpotent_sub_algebraMap]
  refine exists_congr fun c ↦ ?_
  rw [← IsNilpotent.map_iff e.injective, map_sub, map_smul, map_one, Algebra.algebraMap_eq_smul_one]

/-- If the size of the matrices is nonzero in `K` (or `n` is empty), an element of `sl n K` with
nilpotent adjoint action on `sl n K` also has nilpotent adjoint action on `gl n K`: `gl n K` is
`sl n K` plus the scalars, and `ad x` kills the scalars. -/
theorem isNilpotent_ad_of_isNilpotent_ad_sl (hn : Nonempty n → (Fintype.card n : K) ≠ 0)
    {x : SpecialLinear.sl n K} (hx : IsNilpotent (ad K (SpecialLinear.sl n K) x)) :
    IsNilpotent (ad K (Matrix n n K) (x : Matrix n n K)) := by
  obtain ⟨k, hk⟩ := hx
  refine ⟨k + 1, LinearMap.ext fun A ↦ ?_⟩
  obtain ⟨Y, r, rfl⟩ := exists_sl_add_smul_one_eq (fun h ↦ (hn h).isUnit) A
  have hY := LinearMap.congr_fun
    (End.commute_pow_left_of_commute ((SpecialLinear.sl n K).ad_comp_incl_eq x) (k + 1)) Y
  have h1 : ⁅(x : Matrix n n K), (1 : Matrix n n K)⁆ = 0 := by
    simp [LieRing.of_associative_ring_bracket]
  simpa [pow_succ, hk, h1] using hY

/-- **Ad-nilpotent elements of `sl n`.** Over a perfect field in which the size of the matrices is
nonzero, an element of `sl n K` has nilpotent adjoint action on `sl n K` exactly when it is a
nilpotent matrix. The hypothesis cannot be dropped: in characteristic `p` the identity matrix of
size `p` lies in `sl p K` and has zero adjoint action. -/
theorem isNilpotent_ad_sl_iff [PerfectField K] (hn : Nonempty n → (Fintype.card n : K) ≠ 0)
    {x : SpecialLinear.sl n K} :
    IsNilpotent (ad K (SpecialLinear.sl n K) x) ↔ IsNilpotent (x : Matrix n n K) := by
  refine ⟨fun hx ↦ ?_, isNilpotent_ad_of_isNilpotent⟩
  cases isEmpty_or_nonempty n with
  | inl _ => exact ⟨1, Subsingleton.elim _ _⟩
  | inr hne =>
    -- The scalar component has trace zero, so it vanishes.
    obtain ⟨c, hc⟩ := isNilpotent_ad_matrix_iff.mp (isNilpotent_ad_of_isNilpotent_ad_sl hn hx)
    have htr : c * Fintype.card n = 0 := by
      simpa [Matrix.trace_sub, (SpecialLinear.mem_sl_iff).mp x.2] using
        (Matrix.isNilpotent_trace_of_isNilpotent hc).eq_zero
    simpa [(mul_eq_zero.mp htr).resolve_right (hn hne)] using hc

/-- **The nilpotent cone of `sl n`.** Over a perfect field in which the size of the matrices is
nonzero, the elements of `sl n K` with nilpotent adjoint action, viewed as matrices, are exactly
the nilpotent `n × n` matrices. -/
theorem image_setOf_isNilpotent_ad_sl [PerfectField K]
    (hn : Nonempty n → (Fintype.card n : K) ≠ 0) :
    (↑) '' {x : SpecialLinear.sl n K | IsNilpotent (ad K (SpecialLinear.sl n K) x)} =
      {X : Matrix n n K | IsNilpotent X} := by
  ext X
  simp only [Set.mem_image, Set.mem_ofPred_eq, isNilpotent_ad_sl_iff hn]
  refine ⟨fun ⟨x, hx, hxX⟩ ↦ hxX ▸ hx, fun hX ↦ ⟨⟨X, ?_⟩, hX, rfl⟩⟩
  exact (SpecialLinear.mem_sl_iff).mpr (Matrix.isNilpotent_trace_of_isNilpotent hX).eq_zero

end TauCeti
