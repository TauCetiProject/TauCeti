/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.DirectSum
public import TauCeti.Analysis.CStarAlgebra.Module.Self

/-!
# The standard Hilbert C⋆-module `H_A = ℓ²(ℕ, A)`

For a (possibly nonunital) C⋆-algebra `A`, the standard right Hilbert `A`-module
`TauCeti.StandardHilbertModule A` (commonly denoted `H_A` or `ℓ²(ℕ, A)`) is the countable Hilbert
direct sum `HilbertDirectSum Aᵐᵒᵖ (fun _ : ℕ ↦ A)` of copies of `A` equipped with the right
self-module structure `CStarModule Aᵐᵒᵖ A` from `TauCeti.Analysis.CStarAlgebra.Module.Self`.
Concretely, its elements are sequences `x : ℕ → A` for which `∑' n, star (x n) * x n` converges
unconditionally in the norm topology of `A`, with right action `(op a • x) n = x n * a`, `A`-valued
inner product `unop ⟪x, y⟫_{Aᵐᵒᵖ} = ∑' n, star (x n) * y n`, and norm
`‖x‖ = √‖∑' n, star (x n) * x n‖`. Like `A` itself, `StandardHilbertModule A` is full over `A`.

While the Banach `ℓ²` space `lp (fun _ : ℕ ↦ A) 2` of sequences satisfying
`Summable (fun n ↦ ‖x n‖ ^ 2)` includes contractively and injectively with dense range into
`StandardHilbertModule A` via `HilbertDirectSum.ofLp`, unconditional convergence of
`∑' n, star (x n) * x n` in the norm topology of `A` is strictly weaker than scalar
square-summability of `‖x n‖` in general; see
`TauCeti.Examples.Analysis.CStarAlgebra.Module.Standard` for Lance's compact-operator
counterexample on `K(ℓ²(ℕ, ℂ))`.

## Main declarations

* `TauCeti.StandardHilbertModule`: the standard right Hilbert `A`-module
  `HilbertDirectSum Aᵐᵒᵖ (fun _ : ℕ ↦ A)`.
* `TauCeti.StandardHilbertModule.mkOfSummable`: construct an element of `StandardHilbertModule A`
  from `f : ℕ → A` with `Summable fun n ↦ star (f n) * f n`.
* `TauCeti.StandardHilbertModule.unop_inner_eq_tsum`,
  `TauCeti.StandardHilbertModule.norm_eq_sqrt_norm_tsum`: explicit formulas for the `A`-valued
  inner product and norm on `StandardHilbertModule A`.
* `TauCeti.StandardHilbertModule.dense_range_unop_inner`,
  `TauCeti.StandardHilbertModule.topologicalClosure_span_range_unop_inner`: fullness of
  `StandardHilbertModule A` over `A`.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1,
  pp. 6–7.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Example 2.14.
-/

public section

noncomputable section

open MulOpposite

namespace TauCeti

/-- The standard right Hilbert `A`-module `H_A = ℓ²(ℕ, A)`, defined as the countable Hilbert direct
sum of copies of `A` as a right Hilbert module over itself (`CStarModule Aᵐᵒᵖ A`). -/
abbrev StandardHilbertModule (A : Type*)
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] : Type _ :=
  HilbertDirectSum Aᵐᵒᵖ (fun _ : ℕ ↦ A)

namespace StandardHilbertModule

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Construct an element of `StandardHilbertModule A` from a sequence `f : ℕ → A` whose squares
`star (f n) * f n` are unconditionally summable in the norm topology of `A`. -/
def mkOfSummable (f : ℕ → A) (hf : Summable fun n ↦ star (f n) * f n) :
    StandardHilbertModule A :=
  ⟨f, by simp_rw [CStarModule.inner_mulOpposite]; exact hf.op⟩

/-- Evaluating `mkOfSummable f hf` at `n` returns `f n`. -/
@[simp]
theorem mkOfSummable_apply (f : ℕ → A) (hf : Summable fun n ↦ star (f n) * f n) (n : ℕ) :
    mkOfSummable f hf n = f n := (rfl)

/-- For any `x : StandardHilbertModule A`, the sequence `star (x n) * x n` is unconditionally
summable in the norm topology of `A`. -/
theorem summable_star_mul_self (x : StandardHilbertModule A) :
    Summable fun n ↦ star (x n) * x n := by
  simpa only [Function.comp_def, CStarModule.unop_inner_mulOpposite] using
    summable_unop.mpr x.summable_inner_self

/-- For any `x, y : StandardHilbertModule A`, the sequence `star (x n) * y n` is unconditionally
summable in the norm topology of `A`. -/
theorem summable_star_mul (x y : StandardHilbertModule A) :
    Summable fun n ↦ star (x n) * y n := by
  simpa only [Function.comp_def, CStarModule.unop_inner_mulOpposite] using
    summable_unop.mpr (HilbertDirectSum.summable_inner x y)

/-- The `A`-valued inner product on `StandardHilbertModule A` is the unconditional norm sum of
`star (x n) * y n`. -/
theorem hasSum_unop_inner (x y : StandardHilbertModule A) :
    HasSum (fun n ↦ star (x n) * y n) (unop (inner Aᵐᵒᵖ x y)) := by
  simpa only [CStarModule.unop_inner_mulOpposite] using (HilbertDirectSum.hasSum_inner x y).unop

/-- The `A`-valued inner product on `StandardHilbertModule A` is `∑' n, star (x n) * y n`. -/
theorem unop_inner_eq_tsum (x y : StandardHilbertModule A) :
    unop (inner Aᵐᵒᵖ x y) = ∑' n, star (x n) * y n := by
  rw [HilbertDirectSum.inner_def, ← tsum_unop]
  simp

/-- The norm on `StandardHilbertModule A` is `√‖∑' n, star (x n) * x n‖`. -/
theorem norm_eq_sqrt_norm_tsum (x : StandardHilbertModule A) :
    ‖x‖ = √‖∑' n, star (x n) * x n‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Aᵐᵒᵖ) x, ← norm_unop, unop_inner_eq_tsum]

/-- The squared norm on `StandardHilbertModule A` is `‖∑' n, star (x n) * x n‖`. -/
theorem norm_sq_eq_norm_tsum (x : StandardHilbertModule A) :
    ‖x‖ ^ 2 = ‖∑' n, star (x n) * x n‖ := by
  rw [CStarModule.norm_sq_eq Aᵐᵒᵖ (x := x), ← norm_unop, unop_inner_eq_tsum]

/-- The `A`-valued inner products on `StandardHilbertModule A` form a dense subset of `A`. -/
theorem dense_range_unop_inner :
    Dense (Set.range fun p : StandardHilbertModule A × StandardHilbertModule A ↦
      unop (inner Aᵐᵒᵖ p.1 p.2)) := by
  refine CStarModule.dense_range_unop_inner_mulOpposite.mono ?_
  rintro _ ⟨⟨a, b⟩, rfl⟩
  exact ⟨(HilbertDirectSum.single Aᵐᵒᵖ (fun _ : ℕ ↦ A) 0 a,
      HilbertDirectSum.single Aᵐᵒᵖ (fun _ : ℕ ↦ A) 0 b), by simp⟩

/-- The standard Hilbert module `StandardHilbertModule A` is full over `A`: the closed complex
linear span of its `A`-valued inner products is all of `A`. -/
theorem topologicalClosure_span_range_unop_inner :
    (Submodule.span ℂ (Set.range fun p : StandardHilbertModule A × StandardHilbertModule A ↦
      unop (inner Aᵐᵒᵖ p.1 p.2))).topologicalClosure = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top.mp <|
    dense_range_unop_inner.mono Submodule.subset_span

end StandardHilbertModule

end TauCeti

end
