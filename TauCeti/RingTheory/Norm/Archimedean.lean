/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Norm.Complex
public import TauCeti.RingTheory.Norm.Equiv
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Norm groups of finite real extensions

Every finite extension of `ℝ` is isomorphic to `ℝ` or `ℂ`, by Mathlib's
`Real.nonempty_algEquiv_or`. Its norm group is therefore all real units in degree one,
and the positive units in degree two. In both cases its norm index equals its degree.
The degree-two computation uses `TauCeti.normGroup_real_complex` and Mathlib's
`Units.index_posSubgroup`.
-/

public section

namespace TauCeti

/-- The norm group of a finite real extension is all real units in degree one and the
positive real units in degree two. -/
theorem normGroup_real_eq (L : Type*) [Field L] [Algebra ℝ L] [FiniteDimensional ℝ L] :
    normGroup ℝ L = if Module.finrank ℝ L = 1 then ⊤ else Units.posSubgroup ℝ := by
  rcases Real.nonempty_algEquiv_or L with h | h
  · obtain ⟨e⟩ := h
    rw [e.normGroup_eq, e.toLinearEquiv.finrank_eq, Module.finrank_self, ite_eq_left rfl,
      normGroup_self]
  · obtain ⟨e⟩ := h
    rw [e.normGroup_eq, e.toLinearEquiv.finrank_eq, Complex.finrank_real_complex,
      ite_eq_right (by decide), normGroup_real_complex]

/-- The norm index of every finite extension of the reals equals its degree. -/
@[simp]
theorem index_normGroup_real (L : Type*) [Field L] [Algebra ℝ L] [FiniteDimensional ℝ L] :
    (normGroup ℝ L).index = Module.finrank ℝ L := by
  rcases Real.nonempty_algEquiv_or L with h | h
  · obtain ⟨e⟩ := h
    rw [normGroup_real_eq, e.toLinearEquiv.finrank_eq, Module.finrank_self, ite_eq_left rfl,
      Subgroup.index_top]
  · obtain ⟨e⟩ := h
    rw [normGroup_real_eq, e.toLinearEquiv.finrank_eq, Complex.finrank_real_complex,
      ite_eq_right (by decide), Units.index_posSubgroup]

end TauCeti
