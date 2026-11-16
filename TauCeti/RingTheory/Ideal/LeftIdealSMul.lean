/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Span

/-!
# Ideal actions on submodules of a left ideal

For a two-sided ideal `J` of a ring `A` and a left ideal `P` of `A`, the submodules `J • N` of
`P` and `J • (J • P)` are read back in `A`: their elements lie in `J` and `J ^ 2` respectively.
Conversely, for the principal left ideal `Ag`, every element of `J ^ 2 g` comes from
`J • (J • Ag)`. These are the membership facts used to compare the first radical layer
`J P / J² P` of a left ideal with the quotient `A ⧸ J ^ 2`.

## Main results

* `TauCeti.coe_mem_of_mem_smul` and `TauCeti.coe_mem_sq_of_mem_smul`: the elements of `J • N`
  lie in `J`, and those of `J • K` lie in `J ^ 2` when `K ≤ J • N`, for submodules `N` and `K`
  of a left ideal.
* `TauCeti.exists_mem_smul_coe_eq_mul`: conversely, every element of `J ^ 2 g` comes from
  `J • (J • Ag)`.
-/

public section

namespace TauCeti

variable {A : Type*} [Ring A]

/-- The elements of `J • N` lie in `J`. -/
theorem coe_mem_of_mem_smul {J : Ideal A} [J.IsTwoSided]
    {P : Submodule A A} {N : Submodule A P} {y : P}
    (hy : y ∈ J • N) : (y : A) ∈ J :=
  Submodule.smul_induction_on hy (fun r hr n _ ↦ J.mul_mem_right _ hr)
    fun _ _ h₁ h₂ ↦ by simpa using J.add_mem h₁ h₂

/-- If `K ≤ J • N`, the elements of `J • K` lie in `J ^ 2`. -/
theorem coe_mem_sq_of_mem_smul {J : Ideal A} [J.IsTwoSided]
    {P : Submodule A A} {K : Submodule A P}
    {N : Submodule A P} (hK : K ≤ J • N) {y : K} (hy : y ∈ J • (⊤ : Submodule A K)) :
    ((y : P) : A) ∈ J ^ 2 :=
  Submodule.smul_induction_on hy
    (fun r hr n _ ↦ by
      rw [Submodule.pow_succ, Submodule.pow_one]
      exact Ideal.mul_mem_mul hr (coe_mem_of_mem_smul (hK n.property)))
    fun _ _ h₁ h₂ ↦ by simpa using (J ^ 2).add_mem h₁ h₂

/-- Every element of `J ^ 2 g` is the underlying element of some element of `J • (J • Ag)`. -/
theorem exists_mem_smul_coe_eq_mul {J : Ideal A} {g z : A}
    (hz : z ∈ J ^ 2) :
    ∃ t ∈ J • (⊤ : Submodule A ↥(J • (⊤ : Submodule A (Ideal.span {g} : Ideal A)))),
      ((t : (Ideal.span {g} : Ideal A)) : A) = z * g := by
  have h : z • (⟨g, Ideal.mem_span_singleton_self g⟩ : (Ideal.span {g} : Ideal A)) ∈
      J • J • (⊤ : Submodule A (Ideal.span {g} : Ideal A)) := by
    rw [Submodule.pow_succ, Submodule.pow_one] at hz
    rw [← Submodule.mul_smul]
    exact Submodule.smul_mem_smul hz Submodule.mem_top
  exact ⟨⟨_, Submodule.smul_le_right h⟩, (Submodule.mem_smul_top_iff _ _ _).mpr h, rfl⟩

end TauCeti
