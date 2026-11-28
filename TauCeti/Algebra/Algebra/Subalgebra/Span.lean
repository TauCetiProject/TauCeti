/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Spans over a subalgebra

A subalgebra `S` of a commutative algebra `A` acts on `A` by multiplication, so a subset of `A`
spans an `S`-submodule of `A`. For a unit `δ` of `A`, the `S`-span of `δ` is `δ S`: an element
`x` lies in it exactly when `δ⁻¹ x ∈ S`. For instance, for the integral adeles `Ô` of a number
field and a finite idele `δ`, the fractional ideal `δ Ô` consists of the adeles `x` with `δ⁻¹ x`
integral.

## Main results

* `Subalgebra.mem_span_singleton_iff_inv_mul_mem`: `x ∈ S ∙ δ ↔ δ⁻¹ x ∈ S` for a unit `δ`.
-/

public section

namespace Subalgebra

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- For a unit `δ` of a commutative algebra `A` and a subalgebra `S`, an element `x` lies in the
`S`-span of `δ` exactly when `δ⁻¹ x ∈ S`. -/
theorem mem_span_singleton_iff_inv_mul_mem (S : Subalgebra R A) (δ : Aˣ) {x : A} :
    x ∈ Submodule.span S {(δ : A)} ↔ ↑δ⁻¹ * x ∈ S := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    simp [smul_def, ← mul_assoc, mul_comm _ (c : A)]
  · intro h
    exact ⟨⟨_, h⟩, by simp [smul_def, mul_comm, ← mul_assoc]⟩

end Subalgebra
