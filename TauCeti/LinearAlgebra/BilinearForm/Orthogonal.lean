/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Orthogonal complements of bilinear forms

This file records two facts about the orthogonal complement `LinearMap.BilinForm.orthogonal` that
Mathlib lacks. A vector lies in the orthogonal complement of the span of two vectors exactly when
it is orthogonal to both. Adjoining an orthogonal vector whose self-pairing is a right
non-zero-divisor to a left-separating subspace of a reflexive bilinear space produces a
nondegenerate restriction; this is the structural step used when a Cartan--Dieudonne argument
enlarges a fixed subspace.

## Main results

* `LinearMap.BilinForm.mem_orthogonal_span_pair_iff`: membership in the orthogonal complement of
  the span of two vectors.
* `TauCeti.BilinForm.restrict_nondegenerate_sup_span_singleton`: adjoining an orthogonal vector
  to a left-separating subspace produces a nondegenerate restriction.
-/

public section

namespace LinearMap.BilinForm

variable {K V : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V]

/-- A vector is orthogonal to the span of two vectors exactly when it is orthogonal to both. -/
theorem mem_orthogonal_span_pair_iff (B : LinearMap.BilinForm K V) {x y z : V} :
    z ∈ B.orthogonal (Submodule.span K {x, y}) ↔ B x z = 0 ∧ B y z = 0 := by
  constructor
  · intro hz
    exact ⟨hz x (Submodule.subset_span (by simp)), hz y (Submodule.subset_span (by simp))⟩
  · rintro ⟨hx, hy⟩ n hn
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hn
    simp [hx, hy]

end LinearMap.BilinForm

namespace TauCeti

open LinearMap (BilinForm)

namespace BilinForm

variable {K V : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V]

/-- Adjoining a vector whose self-pairing is a right non-zero-divisor from the orthogonal complement
of a left-separating subspace preserves nondegeneracy. -/
theorem restrict_nondegenerate_sup_span_singleton
    (B : BilinForm K V) (hB : B.IsRefl) (W : Submodule K V)
    (hW : (B.restrict W).SeparatingLeft) (x : V) (hxx : B x x ∈ nonZeroDivisorsRight K)
    (hx : x ∈ B.orthogonal W) :
    (B.restrict (W ⊔ Submodule.span K {x})).Nondegenerate := by
  let S : Submodule K V := W ⊔ Submodule.span K {x}
  have hleft : (B.restrict S).SeparatingLeft := by
    intro y hy
    obtain ⟨w, hw, z, hz, hsum⟩ := Submodule.mem_sup.mp y.2
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hwzero : ∀ w' : W, B w w' = 0 := by
      intro w'
      have hBxw' : B x w' = 0 := hB.eq_zero (hx w' w'.2)
      have hyw := hy ⟨w', Submodule.mem_sup_left w'.2⟩
      -- Expose the ambient bilinear form under its restriction to `S`.
      change B y w' = 0 at hyw
      rw [← hsum] at hyw
      simpa [hBxw'] using hyw
    have hw0 : w = 0 := congrArg Subtype.val (hW ⟨w, hw⟩ hwzero)
    have hxS : x ∈ S := Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
    have hyx := hy ⟨x, hxS⟩
    -- Expose the ambient bilinear form under its restriction to `S`.
    change B y x = 0 at hyx
    rw [← hsum, hw0, zero_add] at hyx
    have ha : a = 0 := by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at hyx
      exact hxx a (by simpa using hyx)
    apply Subtype.ext
    simp [← hsum, hw0, ha]
  refine ⟨hleft, fun y hy ↦ hleft y fun z ↦ ?_⟩
  exact (hB.domRestrict S).eq_zero (hy z)

end BilinForm

end TauCeti
