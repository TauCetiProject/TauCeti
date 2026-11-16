/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeLaplacian
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
spaces, with `V` finite-dimensional,

* `TauCeti.HomogeneousSymbol.hodgeLaplacian a b` is the homogeneous symbol
  `a a† + b† b : V → V` of degree `2m`; its value at `(x, ξ)` is the Laplacian
  `ContinuousLinearMap.hodgeLaplacian` of the two values `a (x, ξ)` and `b (x, ξ)`;
* `TauCeti.HomogeneousSymbol.isElliptic_hodgeLaplacian`: if `a (x, ξ)` and `b (x, ξ)` are exact
  at every nonzero frequency, then `a a† + b† b` is elliptic;
* `TauCeti.HomogeneousSymbol.isElliptic_hodgeLaplacian_iff`: conversely, when `b a = 0`, the
  Laplacian is elliptic exactly when the symbol sequence is exact at every nonzero frequency.

The Laplacian of the adjoint sequence `b†`, `a†` is the same symbol
(`TauCeti.HomogeneousSymbol.hodgeLaplacian_adjoint_adjoint`).

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §7, pp. 520–522.
-/

public section

namespace TauCeti

namespace HomogeneousSymbol

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {U V W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
  [CompleteSpace U] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {m : ℝ}
  (a : HomogeneousSymbol X E U V m) (b : HomogeneousSymbol X E V W m)

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

/-- **Exact symbol sequences have elliptic Laplacians.** If the sequence `a (x, ξ)`, `b (x, ξ)` is
exact at every nonzero frequency, the Laplacian `a a† + b† b` is elliptic. -/
theorem isElliptic_hodgeLaplacian [FiniteDimensional ℂ V]
    (h : ∀ x ξ, ξ ≠ 0 → Function.Exact (a.coefficient (x, ξ)) (b.coefficient (x, ξ))) :
    (a.hodgeLaplacian b).IsElliptic := isElliptic_iff.2 fun x ξ hξ ↦ by
  rw [coefficient_hodgeLaplacian, ← ContinuousLinearMap.exact_iff_isInvertible_hodgeLaplacian _ _
    (ContinuousLinearMap.ext (h x ξ hξ).apply_apply_eq_zero)]
  exact h x ξ hξ

/-- If `b a = 0` and the Laplacian `a a† + b† b` is elliptic, the sequence `a (x, ξ)`, `b (x, ξ)` is
exact at every nonzero frequency. -/
theorem exact_of_isElliptic_hodgeLaplacian [FiniteDimensional ℂ V] (hba : b.comp a = 0)
    (h : (a.hodgeLaplacian b).IsElliptic) {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    Function.Exact (a.coefficient (x, ξ)) (b.coefficient (x, ξ)) := by
  have hBA : b.coefficient (x, ξ) ∘L a.coefficient (x, ξ) = 0 := by
    simpa using congrFun (congrArg coefficient hba) (x, ξ)
  rw [ContinuousLinearMap.exact_iff_isInvertible_hodgeLaplacian _ _ hBA,
    ← coefficient_hodgeLaplacian]
  exact isElliptic_iff.1 h x ξ hξ

/-- **A complex of symbols is elliptic exactly when its Laplacian is.** For homogeneous symbols
with `b a = 0` and a finite-dimensional middle space, the Laplacian `a a† + b† b` is elliptic
exactly when the sequence `a (x, ξ)`, `b (x, ξ)` is exact at every nonzero frequency. -/
theorem isElliptic_hodgeLaplacian_iff [FiniteDimensional ℂ V] (hba : b.comp a = 0) :
    (a.hodgeLaplacian b).IsElliptic ↔
      ∀ x ξ, ξ ≠ 0 → Function.Exact (a.coefficient (x, ξ)) (b.coefficient (x, ξ)) :=
  ⟨fun h _ _ hξ ↦ exact_of_isElliptic_hodgeLaplacian a b hba h hξ,
    isElliptic_hodgeLaplacian a b⟩

end HomogeneousSymbol

end TauCeti
