/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.LeviForm
public import TauCeti.Analysis.Calculus.DerivativeTest

/-!
# The Levi form at a local maximum

At a local maximum of a real `C²` function on a complex normed space, the Levi form is
nonpositive on every diagonal. Thus even one strictly positive Levi direction excludes a local
maximum. Applied in holomorphic charts, this is the maximum test that obstructs compact
positive-dimensional complex submanifolds in strictly plurisubharmonic domains.

## References

* R. Hain, *Notes on the Morse theory of complex manifolds*.
-/

public section

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : V → ℝ} {x : V}

/-- At a local maximum of a real `C²` function, the Levi form is nonpositive on the diagonal. -/
theorem re_leviForm_nonpos_of_isLocalMax (hf : ContDiffAt ℝ 2 f x)
    (hmax : IsLocalMax f x) (v : V) : (leviForm f x v v).re ≤ 0 := by
  rw [re_leviForm_apply]
  exact div_nonpos_of_nonpos_of_nonneg
    (add_nonpos (fderiv_fderiv_self_nonpos_of_isLocalMax hf hmax v)
      (fderiv_fderiv_self_nonpos_of_isLocalMax hf hmax (Complex.I • v))) (by norm_num)

/-- A strictly positive Levi direction rules out a local maximum. Positive definiteness is not
needed for this local test. -/
theorem not_isLocalMax_of_re_leviForm_pos (hf : ContDiffAt ℝ 2 f x)
    (hpos : ∃ v, 0 < (leviForm f x v v).re) : ¬ IsLocalMax f x := by
  obtain ⟨v, hv⟩ := hpos
  exact fun hmax ↦ (not_lt_of_ge (re_leviForm_nonpos_of_isLocalMax hf hmax v)) hv

end TauCeti
