/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Complex

/-!
# Twisting cocycles on two generators

Let `m` be a twisting cocycle on two generators `p` and `q` with `ind q < ind p`, such as the
Barraud–Cornea cocycle of a Morse function with exactly two critical points. By one-sidedness its
only possibly nonzero entry is `x = m p q`, which is then a cycle
(`TauCeti.TwistingCocycle.d_m_eq_zero_of_forall_eq_or_eq`). The twisted differential on
`ℳ ⊗ ⟨p, q⟩` is

`D(α ⊗ p) = dα ⊗ p + (-1)^{|α|} α x ⊗ q`,  `D(β ⊗ q) = dβ ⊗ q`

(`TauCeti.TwistingCocycle.twistedDifferential_apply_left_of_forall_eq_or_eq` and
`TauCeti.TwistingCocycle.twistedDifferential_apply_right_of_forall_eq_or_eq`, on the functions
from the generators to the coefficients): the complex of one cell `p` attached along `x` to `q`.

## Main results

* `TauCeti.TwistingCocycle.d_m_eq_zero_of_forall_eq_or_eq`: the entry `m p q` is a cycle.
* `TauCeti.TwistingCocycle.twistedDifferential_apply_left_of_forall_eq_or_eq`,
  `TauCeti.TwistingCocycle.twistedDifferential_apply_right_of_forall_eq_or_eq`: the two
  coefficients of the twisted differential.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Section 1.4.
-/

public section

open MulOpposite

namespace TauCeti

namespace TwistingCocycle

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] {𝒜 : ℤ → Submodule R A}
  {d : A →ₗ[R] A} {P : Type*} [Fintype P] {ind : P → ℤ} (m : TwistingCocycle 𝒜 d P ind)
  {p q : P} (hP : ∀ z, z = p ∨ z = q)
include hP

/-- **On two generators, the entry of a twisting cocycle is a cycle.** The diagonal entries
vanish, so the twisting equation for `m p q` has no nonzero term. -/
theorem d_m_eq_zero_of_forall_eq_or_eq : d (m.m p q) = 0 := by
  rw [m.twisting]
  refine Finset.sum_eq_zero fun z _ ↦ ?_
  rcases hP z with rfl | rfl <;> simp

variable [AddCommMonoid M] [Module R M] [Module Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] (dM : M →ₗ[R] M)

/-- **The twisted differential on two generators, at the lower generator.** The coefficient of
`q` in `D f` is `dM (f q) + κ (f p) · m p q`, where `κ` is the Koszul sign of the degree. -/
theorem twistedDifferential_apply_right_of_forall_eq_or_eq (f : P → M) :
    twistedDifferential m.m ℳ dM f q =
      dM (f q) + op (m.m p q) • (InternalGrading.ofDecomposition ℳ).koszulTwist 1 (f p) := by
  rw [twistedDifferential_apply, Fintype.sum_eq_single p fun z hz ↦ ?_]
  rw [(hP z).resolve_left hz, m.m_self, op_zero, zero_smul]

variable (hind : ind q < ind p)
include hind

/-- **The twisted differential on two generators, at the upper generator.** The coefficient of
`p` in `D f` is `dM (f p)`: no entry of the cocycle ends at `p`. -/
theorem twistedDifferential_apply_left_of_forall_eq_or_eq (f : P → M) :
    twistedDifferential m.m ℳ dM f p = dM (f p) := by
  rw [twistedDifferential_apply, Finset.sum_eq_zero fun z _ ↦ ?_, add_zero]
  rw [m.one_sided z p (by rcases hP z with rfl | rfl <;> omega), op_zero, zero_smul]

end TwistingCocycle

end TauCeti
