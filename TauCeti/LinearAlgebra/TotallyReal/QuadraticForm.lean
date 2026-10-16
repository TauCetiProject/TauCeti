/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.LinearAlgebra.TotallyReal.Basic
import Mathlib.Tactic.Linarith

/-!
# Negative subspaces of quadratic forms are totally real

Let `Q` be a real quadratic form and `J` a real linear endomorphism. If `Q(v) + Q(Jv)` is
positive for every nonzero `v`, then every subspace on which `Q` is negative definite is totally
real for `J`. No almost-complex identity, finite-dimensionality, or inner product is required.

The dimension and inertia consequences for almost complex structures are in
`TauCeti.Geometry.Symplectic.QuadraticForm`.

## Main declarations

* `QuadraticForm.isTotallyReal_of_add_comp_posDef`: a negative subspace is totally real for a
  linear endomorphism `J` when the sum of a quadratic form and its pullback by `J` is positive
  definite.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
-/

public section

namespace QuadraticForm

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (Q : QuadraticForm ℝ E)
variable {W : Submodule ℝ E}

/-- A negative-definite subspace of `Q` is totally real for a linear endomorphism `J` if
`Q(v) + Q(Jv)` is positive for every nonzero `v`.

Indeed, a nonzero vector `Jv` in both `W` and `J(W)` would make both `Q(v)` and `Q(Jv)` negative,
contradicting the positivity assumption. -/
theorem isTotallyReal_of_add_comp_posDef (J : E →ₗ[ℝ] E)
    (hQJ : (Q + Q.comp J).PosDef)
    (hW : ((-Q).restrict W).PosDef) :
    TauCeti.IsTotallyReal J W := by
  rw [TauCeti.isTotallyReal_iff, disjoint_iff_inf_le]
  intro x hx
  rw [Submodule.mem_bot]
  obtain ⟨hxW, hxJW⟩ := hx
  obtain ⟨v, hvW, rfl⟩ := hxJW
  by_contra hJv
  have hv : v ≠ 0 := fun hv ↦ hJv (by simp [hv])
  have hv' : (⟨v, hvW⟩ : W) ≠ 0 := by
    intro h
    exact hv (Subtype.ext_iff.mp h)
  have hJv' : (⟨J v, hxW⟩ : W) ≠ 0 := by
    intro h
    exact hJv (Subtype.ext_iff.mp h)
  have hnegv := hW ⟨v, hvW⟩ hv'
  have hnegJv := hW ⟨J v, hxW⟩ hJv'
  have hpos := hQJ v hv
  simp only [add_apply, QuadraticMap.comp_apply, neg_apply,
    QuadraticMap.restrict_apply] at hnegv hnegJv hpos
  linarith

end QuadraticForm
