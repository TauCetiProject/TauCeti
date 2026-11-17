/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Complexification
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Contraction
public import TauCeti.Analysis.Pseudodifferential.HodgeLaplacian

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

/-- A real multiple of a complex-linear operator is the multiple by the real scalar viewed as a
complex number. Stated for arbitrary normed spaces, so that the real scalar action is the one the
structure of homogeneous symbols uses (the restriction of the complex one). -/
private theorem real_smul_eq_ofReal_smul {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (t : ℝ) (T : V →L[ℂ] W) : t • T = (t : ℂ) • T := by
  ext v
  simp only [FunLike.coe_smul, Pi.smul_apply]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) t (T v)

variable (X E : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The principal symbol of the exterior derivative** on `k`-forms, in the Fourier convention
`σ(∂ⱼ) = i ξⱼ`: at every position and every covector `ξ`, the complexification of `i (ξ ∧ ·)`,
from complex `k`-forms `(⋀ᵏ E)_ℂ` to complex `(k + 1)`-forms. It is homogeneous of degree `1`. -/
def extDeriv (k : ℕ) :
    HomogeneousSymbol X E (WithLp 2 (Complexification (⋀[ℝ]^k E)))
      (WithLp 2 (Complexification (⋀[ℝ]^(k + 1) E))) 1 :=
  ofLinear X
    { toFun ξ :=
        Complex.I • (ExteriorAlgebra.wedgeLeft (R := ℝ) ξ k).toContinuousLinearMap.complexifyL2
      map_add' ξ η := by
        rw [← ExteriorAlgebra.wedgeLeftₗ_apply, map_add, map_add,
          ContinuousLinearMap.complexifyL2_add]
        ext1 v
        simp [smul_add]
      map_smul' r ξ := by
        refine Eq.trans ?_ (real_smul_eq_ofReal_smul r _).symm
        rw [← ExteriorAlgebra.wedgeLeftₗ_apply, map_smul, map_smul,
          ContinuousLinearMap.complexifyL2_smul]
        -- Compare real and imaginary parts.
        ext1 v
        apply WithLp.ofLp_injective 2
        ext <;> simp only [FunLike.coe_smul, Pi.smul_apply, WithLp.ofLp_smul,
          Complexification.smul_re, Complexification.smul_im,
          ContinuousLinearMap.ofLp_complexifyL2_apply, ContinuousLinearMap.complexify_apply_re,
          ContinuousLinearMap.complexify_apply_im, Complexification.real_smul_re,
          Complexification.real_smul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_smul, one_smul, zero_sub, sub_zero, zero_add, add_zero,
          ExteriorAlgebra.wedgeLeftₗ_apply, smul_neg, neg_zero]
      cont := by
        have h : (fun ξ : E ↦ (ExteriorAlgebra.wedgeLeft (R := ℝ) ξ k).toContinuousLinearMap) =
            ⇑(LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
              ExteriorAlgebra.wedgeLeftₗ ℝ E k)) := by
          funext ξ
          simp
        have hc : Continuous fun ξ : E ↦
            (ExteriorAlgebra.wedgeLeft (R := ℝ) ξ k).toContinuousLinearMap := by
          rw [h]
          exact ContinuousLinearMap.continuous _
        exact (ContinuousLinearMap.continuous_complexifyL2.comp hc).const_smul Complex.I }

variable {X E}

@[simp]
theorem coefficient_extDeriv (k : ℕ) (p : X × E) :
    (extDeriv X E k).coefficient p =
      Complex.I • (ExteriorAlgebra.wedgeLeft p.2 k).toContinuousLinearMap.complexifyL2 := by
  rw [extDeriv, coefficient_ofLinear]
  rfl

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
  have h : (ExteriorAlgebra.wedgeLeft p.2 (k + 1)).toContinuousLinearMap.comp
      (ExteriorAlgebra.wedgeLeft (R := ℝ) p.2 k).toContinuousLinearMap = 0 :=
    ContinuousLinearMap.ext fun v ↦
      LinearMap.congr_fun (ExteriorAlgebra.wedgeLeft_comp_wedgeLeft p.2 k) v
  ext1 v
  simp only [coefficient_comp, coefficient_extDeriv, ContinuousLinearMap.comp_apply,
    FunLike.coe_smul, Pi.smul_apply, map_smul]
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.complexifyL2_comp, h,
    ContinuousLinearMap.complexifyL2_zero, zero_apply, smul_zero, smul_zero,
    coefficient_zero, Pi.zero_apply, zero_apply]

/-- **The symbol of the Hodge Laplacian** on `(k + 1)`-forms: `σ(d) σ(d)† + σ(d)† σ(d) = ‖ξ‖² Id`,
from the anticommutator identity `ε_ξ ι_ξ + ι_ξ ε_ξ = ‖ξ‖²`. -/
theorem coefficient_hodgeLaplacian_extDeriv (k : ℕ) (p : X × E) :
    ((extDeriv X E k).hodgeLaplacian (extDeriv X E (k + 1))).coefficient p =
      (‖p.2‖ ^ 2 : ℝ) • ContinuousLinearMap.id ℂ _ := by
  have h : (ExteriorAlgebra.wedgeLeft (R := ℝ) p.2 k).toContinuousLinearMap.hodgeLaplacian
      (ExteriorAlgebra.wedgeLeft (R := ℝ) p.2 (k + 1)).toContinuousLinearMap =
      (‖p.2‖ ^ 2 : ℝ) • ContinuousLinearMap.id ℝ _ :=
    ContinuousLinearMap.ext fun v ↦ by
      rw [ContinuousLinearMap.hodgeLaplacian_apply, ← LinearMap.adjoint_toContinuousLinearMap,
        ← LinearMap.adjoint_toContinuousLinearMap]
      simpa using LinearMap.congr_fun (wedgeLeft_comp_adjoint_add_adjoint_comp_wedgeLeft p.2 k) v
  rw [coefficient_hodgeLaplacian, coefficient_extDeriv, coefficient_extDeriv]
  refine (ContinuousLinearMap.hodgeLaplacian_smul_smul _ _ Complex.norm_I).trans ?_
  rw [ContinuousLinearMap.hodgeLaplacian_complexifyL2, h, ContinuousLinearMap.complexifyL2_smul,
    ContinuousLinearMap.complexifyL2_id]

/-- The Laplacian of the de Rham symbol complex on `(k + 1)`-forms is the symbol `‖ξ‖² Id` of
degree `2`. -/
theorem hodgeLaplacian_extDeriv (k : ℕ) :
    (extDeriv X E k).hodgeLaplacian (extDeriv X E (k + 1)) = normRpow X E _ (2 * 1) :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    rw [coefficient_hodgeLaplacian_extDeriv, coefficient_normRpow_of_ne_zero _ _ _ hξ, mul_one,
      Real.rpow_two]

/-- Multiplying an operator by the unimodular scalar `i` does not change `A† A`. -/
private theorem adjoint_I_smul_comp_I_smul {V W : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] (A : V →L[ℂ] W) :
    (ContinuousLinearMap.adjoint (Complex.I • A)).comp (Complex.I • A) =
      (ContinuousLinearMap.adjoint A).comp A := by
  simpa [ContinuousLinearMap.hodgeLaplacian_def] using
    ContinuousLinearMap.hodgeLaplacian_smul_smul (0 : V →L[ℂ] V) A Complex.norm_I

/-- **The symbol of the Laplacian on functions**: `σ(d)† σ(d) = ‖ξ‖² Id` on complex `0`-forms,
from `ι_ξ ε_ξ = ‖ξ‖²`. -/
theorem coefficient_adjoint_comp_extDeriv_zero (p : X × E) :
    ((extDeriv X E 0).adjoint.comp (extDeriv X E 0)).coefficient p =
      (‖p.2‖ ^ 2 : ℝ) • ContinuousLinearMap.id ℂ _ := by
  have h : (ContinuousLinearMap.adjoint
        (ExteriorAlgebra.wedgeLeft (R := ℝ) p.2 0).toContinuousLinearMap).comp
        (ExteriorAlgebra.wedgeLeft p.2 0).toContinuousLinearMap =
      (‖p.2‖ ^ 2 : ℝ) • ContinuousLinearMap.id ℝ _ :=
    ContinuousLinearMap.ext fun v ↦ by
      rw [ContinuousLinearMap.comp_apply, ← LinearMap.adjoint_toContinuousLinearMap]
      simpa using LinearMap.congr_fun (adjoint_wedgeLeft_comp_wedgeLeft_zero p.2) v
  rw [coefficient_comp, coefficient_adjoint, coefficient_extDeriv]
  refine (adjoint_I_smul_comp_I_smul _).trans ?_
  rw [ContinuousLinearMap.adjoint_complexifyL2, ← ContinuousLinearMap.complexifyL2_comp, h,
    ContinuousLinearMap.complexifyL2_smul, ContinuousLinearMap.complexifyL2_id]

/-- The Laplacian `σ(d)† σ(d)` on functions is the symbol `‖ξ‖² Id` of degree `2`. -/
theorem adjoint_comp_extDeriv_zero :
    (extDeriv X E 0).adjoint.comp (extDeriv X E 0) = normRpow X E _ (1 + 1) :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    rw [coefficient_adjoint_comp_extDeriv_zero, coefficient_normRpow_of_ne_zero _ _ _ hξ,
      one_add_one_eq_two, Real.rpow_two]

/-- A nonzero real multiple of the identity is invertible. -/
private theorem isInvertible_real_smul_id {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {r : ℝ} (hr : r ≠ 0) : (r • ContinuousLinearMap.id ℂ V).IsInvertible := by
  rw [real_smul_eq_ofReal_smul, ContinuousLinearMap.isInvertible_smul_iff
    (Complex.ofReal_ne_zero.2 hr)]
  exact ⟨ContinuousLinearEquiv.refl ℂ V, rfl⟩

/-- **The de Rham symbol sequence is exact at every nonzero covector**:
`(⋀ᵏ E)_ℂ → (⋀ᵏ⁺¹ E)_ℂ → (⋀ᵏ⁺² E)_ℂ`, both maps given by `i ξ ∧ ·`, is exact for `ξ ≠ 0`. -/
theorem exact_extDeriv (k : ℕ) {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    Function.Exact ((extDeriv X E k).coefficient (x, ξ))
      ((extDeriv X E (k + 1)).coefficient (x, ξ)) := by
  have hBA := congrFun (congrArg coefficient (extDeriv_comp_extDeriv (X := X) (E := E) k)) (x, ξ)
  rw [coefficient_comp, coefficient_zero, Pi.zero_apply] at hBA
  rw [ContinuousLinearMap.exact_iff_isInvertible_hodgeLaplacian _ _ hBA,
    ← coefficient_hodgeLaplacian, coefficient_hodgeLaplacian_extDeriv]
  exact isInvertible_real_smul_id (by positivity)

/-- On functions, the symbol `i ξ` of the exterior derivative is injective at every nonzero
covector: the de Rham symbol sequence `0 → ℂ → E_ℂ` is exact there. -/
theorem injective_extDeriv_zero {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    Function.Injective ((extDeriv X E 0).coefficient (x, ξ)) := by
  have h := coefficient_adjoint_comp_extDeriv_zero (X := X) (x, ξ)
  rw [coefficient_comp, coefficient_adjoint] at h
  intro v w hvw
  have hv := congrArg (ContinuousLinearMap.adjoint ((extDeriv X E 0).coefficient (x, ξ))) hvw
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, h] at hv
  exact (isInvertible_real_smul_id (by positivity)).injective hv

/-- **The de Rham complex is elliptic**: the Laplacian of its symbol complex is elliptic in every
positive degree. -/
theorem isElliptic_hodgeLaplacian_extDeriv (k : ℕ) :
    ((extDeriv X E k).hodgeLaplacian (extDeriv X E (k + 1))).IsElliptic :=
  isElliptic_hodgeLaplacian _ _ fun _ _ hξ ↦ exact_extDeriv k hξ

/-- The Laplacian `σ(d)† σ(d)` of the de Rham symbol complex on functions is elliptic. -/
theorem isElliptic_adjoint_comp_extDeriv_zero :
    ((extDeriv X E 0).adjoint.comp (extDeriv X E 0)).IsElliptic :=
  isElliptic_iff.2 fun x ξ hξ ↦ by
    rw [coefficient_adjoint_comp_extDeriv_zero]
    exact isInvertible_real_smul_id (by positivity)

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
