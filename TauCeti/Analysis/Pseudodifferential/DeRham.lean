/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Contraction
public import TauCeti.Analysis.Pseudodifferential.Symbol.FirstOrder

/-!
# The symbol complex of the de Rham complex

On `ℝⁿ`, write complex-valued `k`-forms as functions with values in the complexified exterior
power `Λᵏ = ℂ ⊗ ⋀ᵏ ℝⁿ`, with the Hermitian extension of the Gram inner product. The exterior
derivative is then the first-order differential operator `d u = ∑ⱼ eⱼ ∧ ∂ⱼ u`. Since `∂ⱼ` has
Fourier symbol `i ξⱼ`, its principal symbol is

`σ(d)(x, ξ) = i (ξ ∧ ·) : Λᵏ → Λᵏ⁺¹`.

This file constructs these symbols, as the case `L(ξ) = ξ ∧ ·` of the first-order symbols
`TauCeti.HomogeneousSymbol.ofRealLinear`, and proves the two facts that make the de Rham complex
an elliptic complex.

* The symbol sequence `Λᵏ → Λᵏ⁺¹ → Λᵏ⁺²` is exact at every nonzero covector, and `Λ⁰ → Λ¹` is
  injective there. This is exactness of exterior multiplication by a nonzero vector
  (`TauCeti.exact_wedgeLeft_of_isUnit`), a consequence of the Koszul homotopy identity
  `ξ ∧ ι_ξ + ι_ξ (ξ ∧ ·) = ‖ξ‖²`, where `ι_ξ` is the contraction by `⟪ξ, ·⟫`.
* The symbol of the Hodge Laplacian `Δ = d d* + d* d` is `‖ξ‖² Id` in every degree: with the
  adjoint `σ(d)† = -i ι_ξ`, the same identity gives `σ(d) σ(d)† + σ(d)† σ(d) = ‖ξ‖²`. In
  particular the Hodge Laplacians are elliptic.

The symbols are stated over an arbitrary finite-dimensional real inner product space `E` of
frequencies and an arbitrary space `X` of positions, on which they do not depend.

## Main definitions

* `TauCeti.HomogeneousSymbol.deRhamSymbol X k`: the homogeneous symbol `(x, ξ) ↦ i (ξ ∧ ·)` of
  degree `1`, from `ℂ ⊗ ⋀ᵏ E` to `ℂ ⊗ ⋀ᵏ⁺¹ E`.
* `TauCeti.ClassicalSymbol.extDeriv n k`: the classical symbol of order `1` of the exterior
  derivative `d u = ∑ⱼ eⱼ ∧ ∂ⱼ u` on `k`-forms on `ℝⁿ`.

## Main results

* `TauCeti.HomogeneousSymbol.deRhamSymbol_comp_deRhamSymbol`: the symbols form a complex.
* `TauCeti.HomogeneousSymbol.exact_coefficient_deRhamSymbol`: the symbol sequence is exact at
  every nonzero covector, and `TauCeti.HomogeneousSymbol.injective_coefficient_deRhamSymbol_zero`
  gives exactness at `Λ⁰`.
* `TauCeti.HomogeneousSymbol.adjoint_coefficient_deRhamSymbol`: the adjoint symbol, the symbol of
  `d*`, is `-i ι_ξ`.
* `TauCeti.HomogeneousSymbol.hodgeLaplacian_deRhamSymbol`: the Laplacian of the symbol sequence
  at `Λᵏ⁺¹` is `‖ξ‖² Id`, and `TauCeti.HomogeneousSymbol.adjoint_comp_deRhamSymbol_zero` gives the
  same at `Λ⁰`.
* `TauCeti.HomogeneousSymbol.isElliptic_hodgeLaplacian_deRhamSymbol`: these Laplacians are
  elliptic.
* `TauCeti.ClassicalSymbol.quantizeSchwartzValue_extDeriv`: the quantization of
  `ClassicalSymbol.extDeriv n k` is `u ↦ ∑ⱼ eⱼ ∧ ∂ⱼ u` on Schwartz input, and
  `TauCeti.ClassicalSymbol.principal_extDeriv`: its principal symbol is `deRhamSymbol`.

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §7, pp. 520–522.
-/

public section

noncomputable section

open scoped ContDiff RealInnerProductSpace LineDeriv SchwartzMap
open WithLp

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Exterior multiplication `ξ ↦ (ξ ∧ ·)`, as a bounded real-linear map of `ξ`. -/
private def wedgeLeftL (k : ℕ) : E →L[ℝ] (⋀[ℝ]^k E →L[ℝ] ⋀[ℝ]^(k + 1) E) :=
  LinearMap.toContinuousLinearMap
    { toFun ξ := LinearMap.toContinuousLinearMap (ExteriorAlgebra.wedgeLeft (R := ℝ) ξ k)
      map_add' ξ η := by rw [ExteriorAlgebra.wedgeLeft_add, map_add]
      map_smul' c ξ := by rw [ExteriorAlgebra.wedgeLeft_smul, map_smul, RingHom.id_apply] }

private theorem wedgeLeftL_apply (k : ℕ) (ξ : E) :
    wedgeLeftL k ξ = LinearMap.toContinuousLinearMap (ExteriorAlgebra.wedgeLeft (R := ℝ) ξ k) :=
  (rfl)

namespace HomogeneousSymbol

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The principal symbol `σ(d)(x, ξ) = i (ξ ∧ ·)` of the exterior derivative on `k`-forms, in the
Fourier convention where `∂ⱼ` has symbol `i ξⱼ`. It acts on the complexified exterior powers
`ℂ ⊗ ⋀ᵏ E → ℂ ⊗ ⋀ᵏ⁺¹ E` and does not depend on the position. -/
def deRhamSymbol (k : ℕ) :
    HomogeneousSymbol X E (WithLp 2 (Complexification (⋀[ℝ]^k E)))
      (WithLp 2 (Complexification (⋀[ℝ]^(k + 1) E))) 1 :=
  ofRealLinear X (wedgeLeftL k)

variable {X}

/-- The de Rham symbol acts by `v ↦ i (ξ ∧ v)`. -/
@[simp]
theorem coefficient_deRhamSymbol_apply (k : ℕ) (p : X × E)
    (v : WithLp 2 (Complexification (⋀[ℝ]^k E))) :
    (deRhamSymbol X k).coefficient p v = Complex.I •
      (LinearMap.toContinuousLinearMap (ExteriorAlgebra.wedgeLeft (R := ℝ) p.2 k)).complexifyL2
        v := by
  rw [deRhamSymbol, coefficient_ofRealLinear_apply, wedgeLeftL_apply]

variable (X) in
/-- The de Rham symbols form a complex, `σ(d) σ(d) = 0`, since `ξ ∧ ξ = 0`. -/
@[simp]
theorem deRhamSymbol_comp_deRhamSymbol (k : ℕ) :
    (deRhamSymbol X (E := E) (k + 1)).comp (deRhamSymbol X k) = 0 :=
  ofRealLinear_comp_ofRealLinear _ _ fun ξ ↦ ContinuousLinearMap.coe_injective <| by
    simpa [wedgeLeftL_apply] using ExteriorAlgebra.wedgeLeft_comp_wedgeLeft (R := ℝ) ξ k

/-- At a nonzero covector, the de Rham symbol on functions `Λ⁰ → Λ¹` is injective. -/
theorem injective_coefficient_deRhamSymbol_zero {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    Function.Injective ((deRhamSymbol X 0).coefficient (x, ξ)) :=
  injective_coefficient_ofRealLinear _ <|
    injective_wedgeLeft_zero_of_isUnit (φ := innerₗ E ξ) <| by simpa using hξ

/-- **The de Rham complex is elliptic**: at a nonzero covector `ξ` its symbol sequence
`Λᵏ → Λᵏ⁺¹ → Λᵏ⁺²`, whose maps are `i (ξ ∧ ·)`, is exact. -/
theorem exact_coefficient_deRhamSymbol (k : ℕ) {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    Function.Exact ((deRhamSymbol X k).coefficient (x, ξ))
      ((deRhamSymbol X (k + 1)).coefficient (x, ξ)) :=
  exact_coefficient_ofRealLinear _ _ <|
    exact_wedgeLeft_of_isUnit (φ := innerₗ E ξ) (by simpa using hξ) k

/-- The adjoint of the de Rham symbol is `-i ι_ξ`, with `ι_ξ` the contraction by `⟪ξ, ·⟫`: this is
the principal symbol of the formal adjoint `d*`. -/
theorem adjoint_coefficient_deRhamSymbol (k : ℕ) (p : X × E) :
    ContinuousLinearMap.adjoint ((deRhamSymbol X k).coefficient p) = -Complex.I •
      (LinearMap.toContinuousLinearMap (koszulDifferential (innerₗ E p.2) k)).complexifyL2 := by
  rw [deRhamSymbol, adjoint_coefficient_ofRealLinear, wedgeLeftL_apply,
    ← LinearMap.adjoint_toContinuousLinearMap, adjoint_wedgeLeft]

variable (X) in
/-- The Laplacian symbol `σ(d)† σ(d)` on functions is `‖ξ‖² Id`. -/
@[simp]
theorem adjoint_comp_deRhamSymbol_zero :
    (deRhamSymbol X (E := E) 0).adjoint.comp (deRhamSymbol X 0) =
      (normRpow X E _ 2).castDegree (by norm_num) :=
  adjoint_comp_ofRealLinear _ fun ξ ↦ ContinuousLinearMap.coe_injective <| by
    simpa [wedgeLeftL_apply, ← LinearMap.adjoint_toContinuousLinearMap] using
      adjoint_wedgeLeft_comp_wedgeLeft_zero ξ

variable (X) in
/-- **The symbol of the Hodge Laplacian** `Δ = d d* + d* d` on `(k + 1)`-forms is `‖ξ‖² Id`. -/
@[simp]
theorem hodgeLaplacian_deRhamSymbol (k : ℕ) :
    (deRhamSymbol X (E := E) k).hodgeLaplacian (deRhamSymbol X (k + 1)) =
      (normRpow X E _ 2).castDegree (by norm_num) :=
  hodgeLaplacian_ofRealLinear _ _ fun ξ ↦ ContinuousLinearMap.coe_injective <| by
    simpa [wedgeLeftL_apply, ← LinearMap.adjoint_toContinuousLinearMap] using
      wedgeLeft_comp_adjoint_add_adjoint_comp_wedgeLeft ξ k

variable (X) in
/-- The Hodge Laplacians of the de Rham complex are elliptic. -/
theorem isElliptic_hodgeLaplacian_deRhamSymbol (k : ℕ) :
    ((deRhamSymbol X (E := E) k).hodgeLaplacian (deRhamSymbol X (k + 1))).IsElliptic :=
  isElliptic_hodgeLaplacian _ _ fun _ _ hξ ↦ exact_coefficient_deRhamSymbol k hξ

end HomogeneousSymbol

/-! ### The exterior derivative on `ℝⁿ` -/

namespace ClassicalSymbol

variable (n k : ℕ)

/-- The classical symbol of order `1` of the exterior derivative `d u = ∑ⱼ eⱼ ∧ ∂ⱼ u` on `k`-forms
on `ℝⁿ`, written as functions with values in the complexified exterior power `ℂ ⊗ ⋀ᵏ ℝⁿ`. -/
def extDeriv :
    ClassicalSymbol n (WithLp 2 (Complexification (⋀[ℝ]^k (CoordinateSpace n))))
      (WithLp 2 (Complexification (⋀[ℝ]^(k + 1) (CoordinateSpace n)))) 1 :=
  ofRealLinear (wedgeLeftL k)

/-- The principal symbol of the exterior derivative is the de Rham symbol `i (ξ ∧ ·)`. -/
@[simp]
theorem principal_extDeriv :
    (extDeriv n k).principal = HomogeneousSymbol.deRhamSymbol (CoordinateSpace n) k :=
  principal_ofRealLinear _

/-- The quantization of `ClassicalSymbol.extDeriv n k` is the exterior derivative
`u ↦ ∑ⱼ eⱼ ∧ ∂ⱼ u` on Schwartz `k`-forms. -/
theorem quantizeSchwartzValue_extDeriv
    (u : 𝓢(CoordinateSpace n, WithLp 2 (Complexification (⋀[ℝ]^k (CoordinateSpace n)))))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (extDeriv n k).toSymbol.coefficient u x =
      ∑ j, (LinearMap.toContinuousLinearMap (ExteriorAlgebra.wedgeLeft (R := ℝ)
        (EuclideanSpace.single j 1 : CoordinateSpace n) k)).complexifyL2
          (∂_{(EuclideanSpace.single j (1 : ℝ) : CoordinateSpace n)} u x) :=
  quantizeSchwartzValue_ofRealLinear _ u x

end ClassicalSymbol

end TauCeti
