/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Complexification
public import TauCeti.Analysis.Pseudodifferential.HodgeLaplacian
public import TauCeti.Analysis.Pseudodifferential.Symbol.Differential

/-!
# First-order operators with constant real coefficients

Let `F` and `G` be real inner product spaces and `L : ℝⁿ →L[ℝ] (F →L[ℝ] G)` a real-linear family
of operators. The first-order differential operator `P u = ∑ⱼ L(eⱼ) ∂ⱼ u` with these constant real
coefficients acts on functions with values in the complexification `F_ℂ`, and since `∂ⱼ` has
Fourier symbol `i ξⱼ`, its symbol is

`σ(P)(x, ξ) = i L(ξ)_ℂ : F_ℂ → G_ℂ`.

The exterior derivative `d = ∑ⱼ eⱼ ∧ ∂ⱼ` on forms and Dirac operators `∑ⱼ c(eⱼ) ∂ⱼ` with
Clifford coefficients have this shape. This file builds these symbols and reduces their
algebraic properties to the real operators `L(ξ)`:

* `TauCeti.HomogeneousSymbol.ofRealLinear X L`: the homogeneous symbol `(x, ξ) ↦ i L(ξ)_ℂ` of
  degree `1`, for an arbitrary real normed space `E` of frequencies;
* `TauCeti.HomogeneousSymbol.adjoint_coefficient_ofRealLinear`: its adjoint is `-i (L(ξ)†)_ℂ`;
* `TauCeti.HomogeneousSymbol.ofRealLinear_comp_ofRealLinear`: if `L'(ξ) L(ξ) = 0` for every `ξ`,
  the two symbols form a complex;
* `TauCeti.HomogeneousSymbol.exact_coefficient_ofRealLinear` and
  `TauCeti.HomogeneousSymbol.injective_coefficient_ofRealLinear`: exactness and injectivity of
  the real operators pass to the symbols;
* `TauCeti.HomogeneousSymbol.hodgeLaplacian_ofRealLinear`: if
  `L(ξ) L(ξ)† + L'(ξ)† L'(ξ) = ‖ξ‖²` for every `ξ`, the Laplacian of the symbol sequence is
  `‖ξ‖² Id`; `TauCeti.HomogeneousSymbol.adjoint_comp_ofRealLinear` is the case of a single
  symbol;
* `TauCeti.ClassicalSymbol.ofRealLinear L`: the classical symbol of order `1` of
  `u ↦ ∑ⱼ L(eⱼ)_ℂ ∂ⱼ u` on `ℝⁿ`, which quantizes to this operator on Schwartz input
  (`TauCeti.ClassicalSymbol.quantizeSchwartzValue_ofRealLinear`) and whose principal symbol is
  `HomogeneousSymbol.ofRealLinear _ L` (`TauCeti.ClassicalSymbol.principal_ofRealLinear`).

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §5 and §7.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.1)–(1.4).
-/

public section

noncomputable section

open scoped ContDiff InnerProductSpace RealInnerProductSpace LineDeriv SchwartzMap
open WithLp

namespace TauCeti

variable {F G H : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [NormedAddCommGroup G]
  [InnerProductSpace ℝ G] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

namespace HomogeneousSymbol

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The homogeneous symbol `(x, ξ) ↦ i L(ξ)_ℂ` of degree `1` of a real-linear family
`L : E →L[ℝ] (F →L[ℝ] G)`, acting on the complexifications: the Fourier symbol of the first-order
operator `∑ⱼ L(eⱼ) ∂ⱼ` with constant real coefficients. It does not depend on the position. -/
def ofRealLinear (L : E →L[ℝ] F →L[ℝ] G) :
    HomogeneousSymbol X E (WithLp 2 (Complexification F)) (WithLp 2 (Complexification G)) 1 where
  coefficient p := Complex.I • (L p.2).complexifyL2
  zero_covector _ := by ext v; simp
  contDiffOn_coefficient := by
    -- The coefficient is `L` followed by `T ↦ i T_ℂ`, a bounded real-linear map.
    refine (((IsBoundedLinearMap.contDiff (𝕜 := ℝ)
      (f := fun T : F →L[ℝ] G ↦ Complex.I • T.complexifyL2) ?_).comp
        L.contDiff).comp contDiff_snd).contDiffOn
    refine IsLinearMap.with_bound ⟨fun S T ↦ ?_, fun c T ↦ ?_⟩ 1 fun T ↦ ?_
    · ext v; simp [smul_add]
    · ext v; simp [smul_comm Complex.I c]
    · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
      rw [smul_apply, norm_smul, Complex.norm_I, one_mul, one_mul,
        ← ContinuousLinearMap.norm_complexifyL2]
      exact ContinuousLinearMap.le_opNorm _ _
  homogeneous x ξ t _ := by ext v; simp [smul_comm Complex.I t]

variable {X}

theorem coefficient_ofRealLinear (L : E →L[ℝ] F →L[ℝ] G) (p : X × E) :
    (ofRealLinear X L).coefficient p = Complex.I • (L p.2).complexifyL2 :=
  (rfl)

@[simp]
theorem coefficient_ofRealLinear_apply (L : E →L[ℝ] F →L[ℝ] G) (p : X × E)
    (v : WithLp 2 (Complexification F)) :
    (ofRealLinear X L).coefficient p v = Complex.I • (L p.2).complexifyL2 v :=
  (rfl)

/-- If `L'(ξ) L(ξ) = 0` for every frequency, the symbols `i L(ξ)_ℂ` and `i L'(ξ)_ℂ` form a
complex. -/
theorem ofRealLinear_comp_ofRealLinear (L : E →L[ℝ] F →L[ℝ] G) (L' : E →L[ℝ] G →L[ℝ] H)
    (h : ∀ ξ, (L' ξ).comp (L ξ) = 0) : (ofRealLinear X L').comp (ofRealLinear X L) = 0 := by
  ext1; funext p; ext1 v
  have hv := congrArg (fun T ↦ T.complexifyL2 v) (h p.2)
  simp only [ContinuousLinearMap.complexifyL2_comp, ContinuousLinearMap.complexifyL2_zero,
    ContinuousLinearMap.comp_apply, zero_apply] at hv
  simp [hv]

/-- If `L(ξ)` is injective, so is the symbol `i L(ξ)_ℂ`. -/
theorem injective_coefficient_ofRealLinear (L : E →L[ℝ] F →L[ℝ] G) {x : X} {ξ : E}
    (h : Function.Injective (L ξ)) : Function.Injective ((ofRealLinear X L).coefficient (x, ξ)) :=
  fun v w hvw ↦ by
    have hC : (L ξ).complexifyL2 v = (L ξ).complexifyL2 w := by
      simpa [Complex.I_ne_zero] using hvw
    refine ofLp_injective 2 <| Complexification.ext (h ?_) (h ?_)
    · simpa using congrArg (fun z ↦ z.ofLp.re) hC
    · simpa using congrArg (fun z ↦ z.ofLp.im) hC

/-- If the real sequence `L(ξ)`, `L'(ξ)` is exact, so is the symbol sequence `i L(ξ)_ℂ`,
`i L'(ξ)_ℂ`. -/
theorem exact_coefficient_ofRealLinear (L : E →L[ℝ] F →L[ℝ] G) (L' : E →L[ℝ] G →L[ℝ] H)
    {x : X} {ξ : E} (h : Function.Exact (L ξ) (L' ξ)) :
    Function.Exact ((ofRealLinear X L).coefficient (x, ξ))
      ((ofRealLinear X L').coefficient (x, ξ)) := by
  have hC := ContinuousLinearMap.exact_complexifyL2_iff.2 h
  intro z
  simp only [coefficient_ofRealLinear_apply, smul_eq_zero, Complex.I_ne_zero, false_or, hC z,
    Set.mem_range]
  refine ⟨fun ⟨w, hw⟩ ↦ ⟨-Complex.I • w, ?_⟩, fun ⟨w, hw⟩ ↦ ⟨Complex.I • w, ?_⟩⟩
  · rw [map_smul, smul_smul]
    simp [hw]
  · rw [← hw, map_smul]

variable [CompleteSpace F] [CompleteSpace G] [CompleteSpace H]

/-- The adjoint of the symbol `i L(ξ)_ℂ` is `-i (L(ξ)†)_ℂ`. -/
theorem adjoint_coefficient_ofRealLinear (L : E →L[ℝ] F →L[ℝ] G) (p : X × E) :
    ContinuousLinearMap.adjoint ((ofRealLinear X L).coefficient p) =
      -Complex.I • (ContinuousLinearMap.adjoint (L p.2)).complexifyL2 := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun y v ↦ ?_).symm
  simp [inner_smul_left, inner_smul_right, ← ContinuousLinearMap.adjoint_complexifyL2,
    ContinuousLinearMap.adjoint_inner_left]

end NormedSpace

section InnerProductSpace

variable {X} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace F] [CompleteSpace G] [CompleteSpace H]

/-- If `L(ξ)† L(ξ) = ‖ξ‖²` for every frequency, then `σ† σ = ‖ξ‖² Id` for the symbol
`σ = i L(ξ)_ℂ`. -/
theorem adjoint_comp_ofRealLinear (L : E →L[ℝ] F →L[ℝ] G)
    (h : ∀ ξ, (ContinuousLinearMap.adjoint (L ξ)).comp (L ξ) =
      (‖ξ‖ ^ 2) • ContinuousLinearMap.id ℝ F) :
    (ofRealLinear X L).adjoint.comp (ofRealLinear X L) =
      (normRpow X E _ 2).castDegree (by norm_num) := by
  refine ext_of_ne_zero fun x ξ hξ ↦ ?_
  ext1 v
  have hv := congrArg (fun T ↦ T.complexifyL2 v) (h ξ)
  simp only [ContinuousLinearMap.complexifyL2_comp, ContinuousLinearMap.complexifyL2_smul,
    ContinuousLinearMap.complexifyL2_id] at hv
  simp only [coefficient_comp, coefficient_adjoint, adjoint_coefficient_ofRealLinear,
    coefficient_castDegree, coefficient_normRpow_of_ne_zero _ _ _ hξ, Real.rpow_two]
  simpa [smul_smul] using hv

/-- **The Laplacian of a first-order symbol sequence.** If
`L(ξ) L(ξ)† + L'(ξ)† L'(ξ) = ‖ξ‖²` for every frequency, the Laplacian `σ σ† + σ'† σ'` of the
symbols `σ = i L(ξ)_ℂ` and `σ' = i L'(ξ)_ℂ` is `‖ξ‖² Id`. -/
theorem hodgeLaplacian_ofRealLinear (L : E →L[ℝ] F →L[ℝ] G) (L' : E →L[ℝ] G →L[ℝ] H)
    (h : ∀ ξ, (L ξ).comp (ContinuousLinearMap.adjoint (L ξ)) +
      (ContinuousLinearMap.adjoint (L' ξ)).comp (L' ξ) = (‖ξ‖ ^ 2) • ContinuousLinearMap.id ℝ G) :
    (ofRealLinear X L).hodgeLaplacian (ofRealLinear X L') =
      (normRpow X E _ 2).castDegree (by norm_num) := by
  refine ext_of_ne_zero fun x ξ hξ ↦ ?_
  ext1 v
  have hv := congrArg (fun T ↦ T.complexifyL2 v) (h ξ)
  simp only [ContinuousLinearMap.complexifyL2_add, ContinuousLinearMap.complexifyL2_comp,
    ContinuousLinearMap.complexifyL2_smul, ContinuousLinearMap.complexifyL2_id] at hv
  simp only [coefficient_hodgeLaplacian, ContinuousLinearMap.hodgeLaplacian_apply,
    adjoint_coefficient_ofRealLinear, coefficient_castDegree,
    coefficient_normRpow_of_ne_zero _ _ _ hξ, Real.rpow_two]
  simpa [smul_smul] using hv

end InnerProductSpace

end HomogeneousSymbol

/-! ### The classical symbol on `ℝⁿ` -/

namespace ClassicalSymbol

variable {n : ℕ}

/-- The classical symbol of order `1` of the first-order operator `u ↦ ∑ⱼ L(eⱼ)_ℂ ∂ⱼ u` on `ℝⁿ`
with constant real coefficients, where `eⱼ` is the standard basis. -/
def ofRealLinear (L : CoordinateSpace n →L[ℝ] F →L[ℝ] G) :
    ClassicalSymbol n (WithLp 2 (Complexification F)) (WithLp 2 (Complexification G)) 1 :=
  inclusion 0 (by simp) <| ofDifferentialSymbol (k := fun _ : Fin n ↦ 1) 1 Finset.univ
    (fun j _ ↦ EuclideanSpace.single j 1) (fun j _ ↦ (L (EuclideanSpace.single j 1)).complexifyL2)
    (fun _ _ ↦ contDiff_const) fun _ _ ↦ le_rfl

/-- The differential symbol of `∑ⱼ L(eⱼ)_ℂ ∂ⱼ` is `i L(ξ)_ℂ`. -/
private theorem differentialSymbol_ofRealLinear (L : CoordinateSpace n →L[ℝ] F →L[ℝ] G)
    {s : Finset (Fin n)} (hs : s = Finset.univ) (p : CoordinateSpace n × CoordinateSpace n) :
    differentialSymbol (k := fun _ : Fin n ↦ 1) s (fun j _ ↦ EuclideanSpace.single j 1)
      (fun j _ ↦ (L (EuclideanSpace.single j 1)).complexifyL2) p =
        (HomogeneousSymbol.ofRealLinear (CoordinateSpace n) L).coefficient p := by
  subst hs
  ext1 v
  -- Expand `ξ = ∑ⱼ ξⱼ eⱼ` inside `L`.
  conv_rhs => rw [HomogeneousSymbol.coefficient_ofRealLinear_apply,
    ← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr' p.2, map_sum,
    ← AddMonoidHom.mk'_apply ContinuousLinearMap.complexifyL2 ContinuousLinearMap.complexifyL2_add,
    map_sum]
  simp [differentialSymbol_def, Finset.smul_sum, mul_smul, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right, EuclideanSpace.basisFun_apply]

/-- The full symbol of `ClassicalSymbol.ofRealLinear L` is `i L(ξ)_ℂ`. -/
@[simp]
theorem coefficient_toSymbol_ofRealLinear (L : CoordinateSpace n →L[ℝ] F →L[ℝ] G)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (ofRealLinear L).toSymbol.coefficient p =
      (HomogeneousSymbol.ofRealLinear (CoordinateSpace n) L).coefficient p := by
  rw [ofRealLinear, toSymbol_inclusion, Symbol.coefficient_inclusion,
    coefficient_toSymbol_ofDifferentialSymbol, differentialSymbol_ofRealLinear L rfl]

/-- The principal symbol of `ClassicalSymbol.ofRealLinear L` is `i L(ξ)_ℂ`. -/
@[simp]
theorem principal_ofRealLinear (L : CoordinateSpace n →L[ℝ] F →L[ℝ] G) :
    (ofRealLinear L).principal = HomogeneousSymbol.ofRealLinear (CoordinateSpace n) L :=
  HomogeneousSymbol.ext_of_ne_zero fun x ξ hξ ↦ by
    rw [ofRealLinear, coefficient_principal, term_inclusion_zero,
      HomogeneousSymbol.coefficient_castDegree, ← coefficient_principal,
      coefficient_principal_ofDifferentialSymbol _ _ _ _ _ _ hξ,
      differentialSymbol_ofRealLinear L (Finset.filter_true_of_mem fun _ _ ↦ rfl)]

/-- The quantization of `ClassicalSymbol.ofRealLinear L` is the operator `u ↦ ∑ⱼ L(eⱼ)_ℂ ∂ⱼ u` on
Schwartz input. -/
theorem quantizeSchwartzValue_ofRealLinear [CompleteSpace F] [CompleteSpace G]
    (L : CoordinateSpace n →L[ℝ] F →L[ℝ] G)
    (u : 𝓢(CoordinateSpace n, WithLp 2 (Complexification F))) (x : CoordinateSpace n) :
    quantizeSchwartzValue (ofRealLinear L).toSymbol.coefficient u x =
      ∑ j, (L (EuclideanSpace.single j 1)).complexifyL2
        (∂_{(EuclideanSpace.single j (1 : ℝ) : CoordinateSpace n)} u x) := by
  rw [ofRealLinear, toSymbol_inclusion]
  simp [LineDeriv.iteratedLineDerivOp_one]

end ClassicalSymbol

end TauCeti
