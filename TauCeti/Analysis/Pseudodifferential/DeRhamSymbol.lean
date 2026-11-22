/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Complexification
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Contraction
public import TauCeti.Analysis.Pseudodifferential.HodgeLaplacian
import TauCeti.Analysis.InnerProductSpace.OperatorIdentities

/-!
# The symbol complex of the de Rham complex

Let `E` be a finite-dimensional real inner product space, the frequency (cotangent) space of a
Euclidean space or of a Riemannian manifold at a point. Complex-valued `k`-forms at a point are
the complexification `(⋀ᵏ E)_ℂ` of the `k`-th exterior power, a complex Hilbert space. In the
Fourier convention `σ(∂ⱼ) = i ξⱼ`, the exterior derivative `d = ∑ⱼ dxⱼ ∧ ∂ⱼ` has principal symbol

`σ(d)(x, ξ) = i ε_ξ : (⋀ᵏ E)_ℂ → (⋀ᵏ⁺¹ E)_ℂ`,

the complexification of exterior multiplication `ε_ξ = ξ ∧ ·`, multiplied by `i`
(`TauCeti.HomogeneousSymbol.extDeriv`). It is a homogeneous symbol of degree `1` that does not
depend on the position. Its adjoint, the symbol of the codifferential `d*`, is `-i ι_ξ`, with
`ι_ξ` the contraction by `⟪ξ, ·⟫` (`TauCeti.HomogeneousSymbol.coefficient_adjoint_extDeriv`).

Since `ξ ∧ ξ = 0`, the symbols form a complex (`TauCeti.HomogeneousSymbol.extDeriv_comp_extDeriv`),
and the anticommutator identity `ε_ξ ι_ξ + ι_ξ ε_ξ = ‖ξ‖²` says that its Laplacian is the symbol of
the Hodge Laplacian `d d* + d* d`:

`σ(d) σ(d)† + σ(d)† σ(d) = ‖ξ‖² Id`

in every degree (`TauCeti.HomogeneousSymbol.hodgeLaplacian_extDeriv`, and
`TauCeti.HomogeneousSymbol.adjoint_comp_extDeriv_zero` on functions, where only `d* d` occurs).
In particular the Laplacian is invertible at every nonzero covector, so the **de Rham symbol
sequence is exact at every nonzero covector** (`TauCeti.HomogeneousSymbol.exact_extDeriv`), and
`σ(d)` is injective on functions (`TauCeti.HomogeneousSymbol.injective_extDeriv_zero`). Thus the
de Rham complex is an elliptic complex, and its Laplacians are elliptic
(`TauCeti.HomogeneousSymbol.isElliptic_hodgeLaplacian_extDeriv`).

A single exterior derivative is not elliptic in general: on functions, `σ(d)(ξ) : ℂ → E_ℂ` has
the one-dimensional image `ℂ ξ`, so it is invertible only in dimension at most one
(`TauCeti.HomogeneousSymbol.isElliptic_extDeriv_zero_iff`). For instance on `ℝ²` the symbol at
`ξ = (1, 0)` has image spanned by `dx`, while on `ℝ` it is the invertible scalar `i ξ`.

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §7, pp. 520–522 (elliptic complexes and the symbol sequence of the de Rham complex).
-/

public section

noncomputable section

open Module

namespace TauCeti

namespace HomogeneousSymbol

variable (X E : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The principal symbol of the exterior derivative** on `k`-forms, in the Fourier convention
`σ(∂ⱼ) = i ξⱼ`: at every position and every covector `ξ`, the complexification of `i (ξ ∧ ·)`,
from complex `k`-forms `(⋀ᵏ E)_ℂ` to complex `(k + 1)`-forms. It is homogeneous of degree `1`. -/
def extDeriv (k : ℕ) :
    HomogeneousSymbol X E (WithLp 2 (Complexification (⋀[ℝ]^k E)))
      (WithLp 2 (Complexification (⋀[ℝ]^(k + 1) E))) 1 :=
  ofLinear X <| Complex.I • ((ContinuousLinearMap.complexifyL2ₗᵢ _ _).toContinuousLinearMap ∘L
    LinearMap.toContinuousLinearMap
      (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ ExteriorAlgebra.wedgeLeftₗ ℝ E k))

variable {X E}

@[simp]
theorem coefficient_extDeriv (k : ℕ) (p : X × E) :
    (extDeriv X E k).coefficient p =
      Complex.I • (ExteriorAlgebra.wedgeLeft p.2 k).toContinuousLinearMap.complexifyL2 := by
  simp [extDeriv]

/-- The adjoint of the symbol of the exterior derivative, the symbol of the codifferential, is
`-i ι_ξ`, the complexified contraction by `⟪ξ, ·⟫` multiplied by `-i`. -/
theorem coefficient_adjoint_extDeriv (k : ℕ) (p : X × E) :
    (extDeriv X E k).adjoint.coefficient p =
      -Complex.I • (koszulDifferential (innerₗ E p.2) k).toContinuousLinearMap.complexifyL2 := by
  rw [coefficient_adjoint, coefficient_extDeriv, ← adjoint_wedgeLeft,
    LinearMap.adjoint_toContinuousLinearMap, ← ContinuousLinearMap.adjoint_complexifyL2]
  exact (ContinuousLinearMap.adjoint.map_smulₛₗ _ _).trans (by rw [Complex.conj_I])

/-- **The de Rham symbols form a complex**: `σ(d) σ(d) = 0`, since `ξ ∧ ξ = 0`. -/
@[simp]
theorem extDeriv_comp_extDeriv (k : ℕ) : (extDeriv X E (k + 1)).comp (extDeriv X E k) = 0 := by
  ext1
  funext p
  ext1 v
  simp [← ContinuousLinearMap.complexifyL2_comp]

/-- **The symbol of the Hodge Laplacian** on `(k + 1)`-forms: `σ(d) σ(d)† + σ(d)† σ(d) = ‖ξ‖² Id`,
from the anticommutator identity `ε_ξ ι_ξ + ι_ξ ε_ξ = ‖ξ‖²`. -/
theorem coefficient_hodgeLaplacian_extDeriv (k : ℕ) (p : X × E) :
    ((extDeriv X E k).hodgeLaplacian (extDeriv X E (k + 1))).coefficient p =
      (‖p.2‖ ^ 2 : ℝ) • ContinuousLinearMap.id ℂ _ := by
  simp [coefficient_hodgeLaplacian, ContinuousLinearMap.hodgeLaplacian_smul_smul,
    ContinuousLinearMap.hodgeLaplacian_complexifyL2, hodgeLaplacian_wedgeLeft]

/-- The Laplacian of the de Rham symbol complex on `(k + 1)`-forms is the symbol `‖ξ‖² Id` of
degree `2`. -/
theorem hodgeLaplacian_extDeriv (k : ℕ) :
    (extDeriv X E k).hodgeLaplacian (extDeriv X E (k + 1)) = normRpow X E _ (2 * 1) :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    rw [coefficient_hodgeLaplacian_extDeriv, coefficient_normRpow_of_ne_zero _ _ _ hξ, mul_one,
      Real.rpow_two]

/-- **The symbol of the Laplacian on functions**: `σ(d)† σ(d) = ‖ξ‖² Id` on complex `0`-forms,
from `ι_ξ ε_ξ = ‖ξ‖²`. -/
theorem coefficient_adjoint_comp_extDeriv_zero (p : X × E) :
    ((extDeriv X E 0).adjoint.comp (extDeriv X E 0)).coefficient p =
      (‖p.2‖ ^ 2 : ℝ) • ContinuousLinearMap.id ℂ _ := by
  rw [coefficient_comp, coefficient_adjoint, coefficient_extDeriv,
    ContinuousLinearMap.adjoint_smul_comp_smul]
  simp [ContinuousLinearMap.adjoint_complexifyL2, ← ContinuousLinearMap.complexifyL2_comp,
    adjoint_wedgeLeft_comp_wedgeLeft_zero]

/-- The Laplacian `σ(d)† σ(d)` on functions is the symbol `‖ξ‖² Id` of degree `2`. -/
theorem adjoint_comp_extDeriv_zero :
    (extDeriv X E 0).adjoint.comp (extDeriv X E 0) = normRpow X E _ (1 + 1) :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    rw [coefficient_adjoint_comp_extDeriv_zero, coefficient_normRpow_of_ne_zero _ _ _ hξ,
      one_add_one_eq_two, Real.rpow_two]

/-- **The de Rham complex is elliptic**: the Laplacian of its symbol complex is elliptic in every
positive degree. -/
theorem isElliptic_hodgeLaplacian_extDeriv (k : ℕ) :
    ((extDeriv X E k).hodgeLaplacian (extDeriv X E (k + 1))).IsElliptic := by
  rw [hodgeLaplacian_extDeriv]
  exact isElliptic_normRpow X E _ _

/-- The Laplacian `σ(d)† σ(d)` of the de Rham symbol complex on functions is elliptic. -/
theorem isElliptic_adjoint_comp_extDeriv_zero :
    ((extDeriv X E 0).adjoint.comp (extDeriv X E 0)).IsElliptic := by
  rw [adjoint_comp_extDeriv_zero]
  exact isElliptic_normRpow X E _ _

/-- **The de Rham symbol sequence is exact at every nonzero covector**:
`(⋀ᵏ E)_ℂ → (⋀ᵏ⁺¹ E)_ℂ → (⋀ᵏ⁺² E)_ℂ`, both maps given by `i ξ ∧ ·`, is exact for `ξ ≠ 0`. -/
theorem exact_extDeriv (k : ℕ) {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    Function.Exact ((extDeriv X E k).coefficient (x, ξ))
      ((extDeriv X E (k + 1)).coefficient (x, ξ)) :=
  exact_of_isElliptic_hodgeLaplacian (extDeriv X E k) (extDeriv X E (k + 1))
    (extDeriv_comp_extDeriv k) (isElliptic_hodgeLaplacian_extDeriv k) hξ

/-- On functions, the symbol `i ξ` of the exterior derivative is injective at every nonzero
covector: the de Rham symbol sequence `0 → ℂ → E_ℂ` is exact there. -/
theorem injective_extDeriv_zero {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    Function.Injective ((extDeriv X E 0).coefficient (x, ξ)) := by
  have h := (isElliptic_iff.1 isElliptic_adjoint_comp_extDeriv_zero x ξ hξ).injective
  rw [coefficient_comp, ContinuousLinearMap.coe_comp] at h
  exact h.of_comp

/-- **The exterior derivative on functions is elliptic only in dimension at most one.** At a
nonzero covector `ξ`, `σ(d)(ξ) : ℂ → E_ℂ` is injective with one-dimensional image, so it is
invertible exactly when `E` has dimension one; in dimension zero there is no nonzero covector. -/
theorem isElliptic_extDeriv_zero_iff [Nonempty X] :
    (extDeriv X E 0).IsElliptic ↔ finrank ℝ E ≤ 1 := by
  have h₀ : finrank ℂ (WithLp 2 (Complexification (⋀[ℝ]^0 E))) = 1 := by
    simp [WithLp.finrank_complexification]
  have h₁ : finrank ℂ (WithLp 2 (Complexification (⋀[ℝ]^(0 + 1) E))) = finrank ℝ E := by
    simp [WithLp.finrank_complexification]
  rw [isElliptic_iff]
  constructor
  · intro h
    by_contra hE
    have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
    obtain ⟨ξ, hξ⟩ := exists_ne (0 : E)
    obtain ⟨e, -⟩ := h (Classical.arbitrary X) ξ hξ
    have := e.toLinearEquiv.finrank_eq
    rw [h₀, h₁] at this
    omega
  · intro hE x ξ hξ
    have : Nontrivial E := ⟨⟨ξ, 0, hξ⟩⟩
    have hpos := Module.finrank_pos (R := ℝ) (M := E)
    have hdim : finrank ℂ (WithLp 2 (Complexification (⋀[ℝ]^0 E))) =
        finrank ℂ (WithLp 2 (Complexification (⋀[ℝ]^(0 + 1) E))) := by
      rw [h₀, h₁]
      omega
    refine ContinuousLinearMap.isInvertible_iff_bijective.2
      ⟨injective_extDeriv_zero hξ, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := ((extDeriv X E 0).coefficient (x, ξ) : _ →ₗ[ℂ] _))).1 (injective_extDeriv_zero hξ)

end HomogeneousSymbol

end TauCeti
