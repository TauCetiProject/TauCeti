/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.Analysis.InnerProductSpace.FoldedComplex
public import TauCeti.Analysis.Pseudodifferential.Elliptic

/-!
# Laplacians of complexes of homogeneous symbols

Let `⋯ → Γ(E₀) → Γ(E₁) → Γ(E₂) → ⋯` be a complex of differential operators `dᵢ` of a common
order `m`, with fibre metrics on the bundles `Eᵢ`. The complex is *elliptic* when the sequence of
principal symbols `σ(dᵢ)(x, ξ)` is exact at every nonzero covector `ξ`. Its Laplacians
`Δᵢ = dᵢ₋₁ dᵢ₋₁* + dᵢ* dᵢ` have order `2m`, with principal symbol
`σ(dᵢ₋₁) σ(dᵢ₋₁)† + σ(dᵢ)† σ(dᵢ)`, and the basic algebraic fact behind the Hodge theory of
elliptic complexes is that the complex is elliptic exactly when all of these Laplacians are
elliptic.

This file proves that fact for principal symbols, one position of the complex at a time. For
homogeneous symbols `a : U → V` and `b : V → W` of a common degree `m` between complex Hilbert
spaces,

* `TauCeti.HomogeneousSymbol.hodgeLaplacian a b` is the homogeneous symbol
  `a a† + b† b : V → V` of degree `2m`; its value at `(x, ξ)` is the Laplacian
  `ContinuousLinearMap.hodgeLaplacian` of the two values `a (x, ξ)` and `b (x, ξ)`;
* `TauCeti.HomogeneousSymbol.exact_of_isElliptic_hodgeLaplacian`: when `b a = 0` and `a a† + b† b`
  is elliptic, `a (x, ξ)` and `b (x, ξ)` are exact at every nonzero frequency;
* `TauCeti.HomogeneousSymbol.isElliptic_hodgeLaplacian`: for finite-dimensional `V`, if `a (x, ξ)`
  and `b (x, ξ)` are exact at every nonzero frequency, then `a a† + b† b` is elliptic;
* `TauCeti.HomogeneousSymbol.isElliptic_hodgeLaplacian_iff`: for finite-dimensional `V` and
  `b a = 0`, the Laplacian is elliptic exactly when the symbol sequence is exact at every nonzero
  frequency.

The Laplacian of the adjoint sequence `b†`, `a†` is the same symbol
(`TauCeti.HomogeneousSymbol.hodgeLaplacian_adjoint_adjoint`).

A complex of a common order folds into a two-periodic one, `p : U → V` on the terms of even degree
and `q : V → U` on the terms of odd degree, and its *folded symbol* is `p + q†`, the principal
symbol of the folded operator `d + d* : Γ(E_even) → Γ(E_odd)` whose index is the Euler
characteristic of the complex. By `TauCeti.HomogeneousSymbol.isElliptic_add_adjoint_iff`, for
finite-dimensional `V` the folded symbol is elliptic exactly when the two-periodic symbol
sequence is exact at every nonzero frequency.

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §7, pp. 520–522.
-/

public section

namespace TauCeti

namespace HomogeneousSymbol

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {U V W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
  [CompleteSpace U] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

section CompleteSpace

variable [CompleteSpace V] {m : ℝ} (a : HomogeneousSymbol X E U V m)
  (b : HomogeneousSymbol X E V W m)

/-- The Laplacian `a a† + b† b` of two composable homogeneous symbols `a : U → V` and `b : V → W`
of a common degree `m`, a homogeneous symbol on `V` of degree `2m`. -/
noncomputable def hodgeLaplacian : HomogeneousSymbol X E V V (2 * m) :=
  (a.comp a.adjoint + b.adjoint.comp b).castDegree (two_mul m).symm

/-- The value of the Laplacian of two symbols is the Laplacian of their values. -/
@[simp]
theorem coefficient_hodgeLaplacian (p : X × E) :
    (a.hodgeLaplacian b).coefficient p =
      (a.coefficient p).hodgeLaplacian (b.coefficient p) := by
  simp [hodgeLaplacian, ContinuousLinearMap.hodgeLaplacian_def]

/-- The adjoint symbol sequence `b†`, `a†` has the same Laplacian. -/
@[simp]
theorem hodgeLaplacian_adjoint_adjoint :
    b.adjoint.hodgeLaplacian a.adjoint = a.hodgeLaplacian b := by
  ext1; funext p; simp

/-- If `b a = 0` and the Laplacian `a a† + b† b` is elliptic, the sequence `a (x, ξ)`, `b (x, ξ)` is
exact at every nonzero frequency. -/
theorem exact_of_isElliptic_hodgeLaplacian (hba : b.comp a = 0)
    (h : (a.hodgeLaplacian b).IsElliptic) {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    Function.Exact (a.coefficient (x, ξ)) (b.coefficient (x, ξ)) := by
  refine (a.coefficient (x, ξ)).exact_of_surjective_hodgeLaplacian (b.coefficient (x, ξ)) ?_ ?_
  · exact coefficient_comp_coefficient_eq_zero hba _
  · rw [← coefficient_hodgeLaplacian]
    exact (isElliptic_iff.1 h x ξ hξ).surjective

end CompleteSpace

section FiniteDimensional

variable [FiniteDimensional ℂ V] {m : ℝ} (a : HomogeneousSymbol X E U V m)
  (b : HomogeneousSymbol X E V W m)

/-- **Exact symbol sequences have elliptic Laplacians.** For a finite-dimensional middle space `V`,
if the sequence `a (x, ξ)`, `b (x, ξ)` is exact at every nonzero frequency, the Laplacian
`a a† + b† b` is elliptic. -/
theorem isElliptic_hodgeLaplacian
    (h : ∀ x ξ, ξ ≠ 0 → Function.Exact (a.coefficient (x, ξ)) (b.coefficient (x, ξ))) :
    (a.hodgeLaplacian b).IsElliptic := isElliptic_iff.2 fun x ξ hξ ↦ by
  rw [coefficient_hodgeLaplacian, ← ContinuousLinearMap.exact_iff_isInvertible_hodgeLaplacian _ _
    (ContinuousLinearMap.ext (h x ξ hξ).apply_apply_eq_zero)]
  exact h x ξ hξ

/-- **A complex of symbols is elliptic exactly when its Laplacian is.** For homogeneous symbols
with `b a = 0` and a finite-dimensional middle space, the Laplacian `a a† + b† b` is elliptic
exactly when the sequence `a (x, ξ)`, `b (x, ξ)` is exact at every nonzero frequency. -/
theorem isElliptic_hodgeLaplacian_iff (hba : b.comp a = 0) :
    (a.hodgeLaplacian b).IsElliptic ↔
      ∀ x ξ, ξ ≠ 0 → Function.Exact (a.coefficient (x, ξ)) (b.coefficient (x, ξ)) :=
  ⟨fun h _ _ hξ ↦ exact_of_isElliptic_hodgeLaplacian a b hba h hξ,
    isElliptic_hodgeLaplacian a b⟩

/-! ### The folded symbol of a two-periodic complex -/

/-- **The folded symbol of a complex is elliptic exactly when the complex is.** For homogeneous
symbols `p : U → V` and `q : V → U` of a common degree with `p q = 0` and `q p = 0`, where `V` is
finite-dimensional, the folded symbol `p + q†` is elliptic exactly when the two-periodic
sequence `p (x, ξ)`, `q (x, ξ)` is exact at `U` and at `V` at every nonzero frequency. -/
theorem isElliptic_add_adjoint_iff
    {p : HomogeneousSymbol X E U V m} {q : HomogeneousSymbol X E V U m} (hpq : p.comp q = 0)
    (hqp : q.comp p = 0) :
    (p + q.adjoint).IsElliptic ↔ ∀ x ξ, ξ ≠ 0 →
      Function.Exact (q.coefficient (x, ξ)) (p.coefficient (x, ξ)) ∧
        Function.Exact (p.coefficient (x, ξ)) (q.coefficient (x, ξ)) := by
  refine isElliptic_iff.trans (forall₂_congr fun x ξ ↦ imp_congr_right fun _ ↦ ?_)
  rw [coefficient_add, Pi.add_apply, coefficient_adjoint,
    ContinuousLinearMap.isInvertible_iff_bijective,
    ContinuousLinearMap.bijective_add_adjoint_iff (coefficient_comp_coefficient_eq_zero hpq _)
      (coefficient_comp_coefficient_eq_zero hqp _) (Submodule.isClosed_of_finiteDimensional _)
      (Submodule.isClosed_of_finiteDimensional _)]

end FiniteDimensional

end HomogeneousSymbol

end TauCeti
