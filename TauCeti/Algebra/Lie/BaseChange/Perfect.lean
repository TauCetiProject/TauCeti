/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.Solvable

/-!
# Brackets in the extension of scalars of a perfect Lie algebra

Let `L` be a perfect Lie algebra over `R`, that is `⁅L, L⁆ = L`, and let `A` be a commutative
`R`-algebra. In the extension of scalars `A ⊗[R] L`, every tensor `(a * b) ⊗ x` is an `R`-linear
combination of brackets `⁅a ⊗ y, b ⊗ z⁆`, because `x` is a combination of brackets `⁅y, z⁆` and
`⁅a ⊗ y, b ⊗ z⁆ = (a * b) ⊗ ⁅y, z⁆`. The coefficient factorization `a * b` is arbitrary, which is
what lets loop and current algebras split a mode or a current of high order into brackets of
modes or currents of lower order.

## Main results

* `TauCeti.LieAlgebra.ExtendScalars.mul_tmul_mem_span_lie`: for perfect `L`, `(a * b) ⊗ x` lies in
  the `R`-span of the brackets `⁅a ⊗ y, b ⊗ z⁆`.
-/

public section

open scoped TensorProduct

namespace TauCeti.LieAlgebra.ExtendScalars

open _root_.LieAlgebra

variable {R A L : Type*} [CommRing R] [CommRing A] [Algebra R A] [LieRing L] [LieAlgebra R L]

/-- **Tensors over a perfect Lie algebra are sums of brackets with prescribed coefficients.** If
`L` is perfect, then for all coefficients `a` and `b` every tensor `(a * b) ⊗ x` is an `R`-linear
combination of brackets `⁅a ⊗ y, b ⊗ z⁆`. -/
theorem mul_tmul_mem_span_lie (hL : derivedSeries R L 1 = ⊤) (a b : A) (x : L) :
    ((a * b) ⊗ₜ x : A ⊗[R] L) ∈
      Submodule.span R {u | ∃ y z : L, ⁅(a ⊗ₜ y : A ⊗[R] L), b ⊗ₜ z⁆ = u} := by
  have hx : x ∈ Submodule.span R {u | ∃ y z : L, ⁅y, z⁆ = u} := by
    rw [← coe_derivedSeries_one_eq, LieIdeal.toLieSubalgebra_toSubmodule, hL]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, z, rfl⟩ := hu
    exact Submodule.subset_span ⟨y, z, ExtendScalars.bracket_tmul ..⟩
  | zero => simp
  | add u v _ _ hu hv => simpa only [TensorProduct.tmul_add] using Submodule.add_mem _ hu hv
  | smul r u _ hu => simpa only [TensorProduct.tmul_smul] using Submodule.smul_mem _ r hu

end TauCeti.LieAlgebra.ExtendScalars
