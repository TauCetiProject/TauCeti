/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Extending left-separating subspaces by an orthogonal vector

This file records that adjoining an orthogonal vector whose self-pairing is a right non-zero-divisor
to a left-separating subspace of a reflexive bilinear space produces a nondegenerate restriction.
It is the structural step used when a Cartan--Dieudonne argument enlarges a fixed subspace.

## Main result

* `TauCeti.BilinForm.restrict_nondegenerate_sup_span_singleton`: adjoining an orthogonal vector
  to a left-separating subspace produces a nondegenerate restriction.
-/

public section

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

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A proper nondegenerate orthogonal complement contains a vector with nonzero self-pairing. -/
theorem _root_.LinearMap.BilinForm.exists_mem_orthogonal_self_ne_zero
    [FiniteDimensional K V] [Invertible (2 : K)]
    (B : BilinForm K V) (hB : B.Nondegenerate)
    (hBsymm : B.IsSymm) (W : Submodule K V) (hW : (B.restrict W).Nondegenerate)
    (hne : W ≠ ⊤) :
    ∃ x : V, x ∈ B.orthogonal W ∧ B x x ≠ 0 := by
  have horth_ne : B.orthogonal W ≠ ⊥ :=
    mt (B.orthogonal_eq_bot_iff hBsymm.isRefl hW hB).mp hne
  have hcomp : IsCompl W (B.orthogonal W) :=
    B.isCompl_orthogonal_of_restrict_nondegenerate hBsymm.isRefl hW
  have horth_nondegenerate : (B.restrict (B.orthogonal W)).Nondegenerate := by
    rw [B.restrict_nondegenerate_iff_isCompl_orthogonal hBsymm.isRefl,
      B.orthogonal_orthogonal hB hBsymm.isRefl W]
    exact hcomp.symm
  let _ : Nontrivial (B.orthogonal W) := Submodule.nontrivial_iff_ne_bot.mpr horth_ne
  obtain ⟨x, hxx⟩ :=
    LinearMap.BilinForm.exists_bilinForm_self_ne_zero horth_nondegenerate.ne_zero
      (LinearMap.BilinForm.isSymm_iff.mp (hBsymm.restrict _))
  exact ⟨x, x.2, hxx⟩

end Field

end BilinForm

end TauCeti
