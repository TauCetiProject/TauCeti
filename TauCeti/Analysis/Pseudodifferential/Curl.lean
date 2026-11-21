/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.DeRhamSymbol
public import TauCeti.Analysis.Pseudodifferential.Symbol.Differential
import TauCeti.Analysis.InnerProductSpace.HodgeStar.Isometry

/-!
# The principal symbol of the curl in dimension three

On an oriented three-dimensional space the Hodge star `⋆ : ⋀² E → ⋀¹ E` turns the exterior
derivative of `1`-forms into an operator from `1`-forms to `1`-forms, the **curl** `curl = ⋆ d`
(on oriented Riemannian three-manifolds this is `TauCeti.SmoothForm.curl`). Identifying `1`-forms
with vector fields, `⋆ (ξ ∧ v)` is the cross product `ξ × v`, so in the Fourier convention
`σ(∂ⱼ) = i ξⱼ` the principal symbol of the curl is

`σ(curl)(x, ξ) = i ⋆ (ξ ∧ ·) : (⋀¹ E)_ℂ → (⋀¹ E)_ℂ`,

the symbol `i ξ × ·` (`TauCeti.HomogeneousSymbol.curl`). It is `⋆` composed with the symbol of the
exterior derivative on `1`-forms (`TauCeti.HomogeneousSymbol.coefficient_curl_eq_comp`).

This file places the curl in the calculus of homogeneous symbols, where ellipticity and exactness
of symbol sequences are formulated, and compares it with the de Rham symbols
`TauCeti.HomogeneousSymbol.extDeriv`:

* `TauCeti.HomogeneousSymbol.adjoint_curl`: the symbol is self-adjoint, because the cross product
  is skew-adjoint, as befits the formally self-adjoint curl;
* `TauCeti.HomogeneousSymbol.curl_comp_extDeriv_zero` and
  `TauCeti.HomogeneousSymbol.adjoint_extDeriv_zero_comp_curl`: `curl grad = 0` and
  `div curl = 0` on symbols;
* `TauCeti.HomogeneousSymbol.adjoint_curl_comp_curl`: `σ(curl)† σ(curl) = σ(d)† σ(d)` on
  `1`-forms, since `⋆` is an isometry;
* `TauCeti.HomogeneousSymbol.hodgeLaplacian_extDeriv_zero_curl` and
  `TauCeti.HomogeneousSymbol.curl_comp_curl_add_extDeriv_zero_comp_adjoint`: the Laplacian of the
  symbol sequence `ℂ → (⋀¹ E)_ℂ → (⋀¹ E)_ℂ` of `grad` and `curl` is `‖ξ‖² Id`, the symbol form of
  `curl curl - grad div = -Δ`;
* `TauCeti.HomogeneousSymbol.exact_extDeriv_zero_curl`: at a nonzero covector `ξ` the kernel of
  `σ(curl)(ξ)` is exactly the line `ℂ ξ`, the image of the symbol of the gradient;
* `TauCeti.HomogeneousSymbol.not_isElliptic_curl`: hence the curl is **not elliptic**.

Finally, on the coordinate space `ℝⁿ` with `n = 3`, the curl is the first-order differential
operator `curl u = ∑ⱼ ⋆ (eⱼ ∧ ∂ⱼ u)` on `(⋀¹ ℝⁿ)_ℂ`-valued functions. It is a classical symbol of
order `1` (`TauCeti.ClassicalSymbol.curl`) whose quantization is this differential operator on
Schwartz input (`TauCeti.ClassicalSymbol.quantizeSchwartzValue_curl`), with no smoothing remainder,
and whose principal symbol is `TauCeti.HomogeneousSymbol.curl`
(`TauCeti.ClassicalSymbol.principal_curl`). More generally, every first-order operator
`u ↦ -i ∑ⱼ L(eⱼ) ∂ⱼ u` with constant coefficients, given by a real-linear `L` of the frequency, is
the classical symbol `TauCeti.ClassicalSymbol.ofLinear L` with full and principal symbol `L ξ`.

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §7, pp. 520–522 (symbol sequences of complexes of differential operators).
* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1 (the Hodge star).
-/

public section

noncomputable section

open Module
open scoped ContDiff RealInnerProductSpace LineDeriv SchwartzMap

namespace TauCeti

/-- The symbol `ξ ↦ i ⋆ (ξ ∧ ·)` of the curl, as a real-linear function of the covector. -/
private def curlLinear {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fact (finrank ℝ E = 3)] (o : Orientation ℝ E (Fin 3)) :
    E →L[ℝ] (WithLp 2 (Complexification (⋀[ℝ]^1 E)) →L[ℂ]
      WithLp 2 (Complexification (⋀[ℝ]^1 E))) :=
  Complex.I • ((ContinuousLinearMap.complexifyL2ₗᵢ _ _).toContinuousLinearMap ∘L
    LinearMap.toContinuousLinearMap
      (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
        LinearMap.llcomp ℝ _ _ _ (o.hodgeStar (k := 2) (l := 1) (Fact.out : finrank ℝ E = 3).symm)
          ∘ₗ ExteriorAlgebra.wedgeLeftₗ ℝ E 1))

private theorem curlLinear_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fact (finrank ℝ E = 3)] (o : Orientation ℝ E (Fin 3))
    (h : 2 + 1 = finrank ℝ E) (ξ : E) :
    curlLinear o ξ = Complex.I • (LinearMap.toContinuousLinearMap
      ((o.hodgeStar h : ⋀[ℝ]^2 E →ₗ[ℝ] ⋀[ℝ]^1 E) ∘ₗ
        ExteriorAlgebra.wedgeLeft ξ 1)).complexifyL2 := by
  simp [curlLinear, LinearMap.llcomp_apply']

namespace HomogeneousSymbol

variable (X : Type*) {E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fact (finrank ℝ E = 3)]
  (o : Orientation ℝ E (Fin 3))

/-- **The principal symbol of the curl** of an oriented three-dimensional space, in the Fourier
convention `σ(∂ⱼ) = i ξⱼ`: at every position and every covector `ξ`, the complexification of
`i ⋆ (ξ ∧ ·)` on complex `1`-forms, the symbol `i ξ × ·` of `curl = ⋆ d`. It is homogeneous of
degree `1` and does not depend on the position. -/
def curl : HomogeneousSymbol X E (WithLp 2 (Complexification (⋀[ℝ]^1 E)))
    (WithLp 2 (Complexification (⋀[ℝ]^1 E))) 1 :=
  ofLinear X (curlLinear o)

variable {X o}

/-- The value of the symbol of the curl at `(x, ξ)` is the complexification of `i ⋆ (ξ ∧ ·)`. -/
theorem coefficient_curl (h : 2 + 1 = finrank ℝ E) (p : X × E) :
    (curl X o).coefficient p = Complex.I • (LinearMap.toContinuousLinearMap
      ((o.hodgeStar h : ⋀[ℝ]^2 E →ₗ[ℝ] ⋀[ℝ]^1 E) ∘ₗ
        ExteriorAlgebra.wedgeLeft p.2 1)).complexifyL2 := by
  rw [curl, coefficient_ofLinear, curlLinear_apply o h]

/-- **The curl is `⋆ d` on `1`-forms**: its symbol is the complexified Hodge star
`⋀² E → ⋀¹ E` composed with the symbol of the exterior derivative on `1`-forms. -/
theorem coefficient_curl_eq_comp (h : 2 + 1 = finrank ℝ E) (p : X × E) :
    (curl X o).coefficient p =
      (LinearMap.toContinuousLinearMap (o.hodgeStar h : ⋀[ℝ]^2 E →ₗ[ℝ] ⋀[ℝ]^1 E)).complexifyL2 ∘L
        (extDeriv X E 1).coefficient p := by
  rw [coefficient_curl h, coefficient_extDeriv, ContinuousLinearMap.comp_smul,
    ← ContinuousLinearMap.complexifyL2_comp]
  congr 2

/-- The real symbol `⋆ (ξ ∧ ·)` of the curl, the cross product with `ξ`, is skew-adjoint. -/
private theorem adjoint_hodgeStar_comp_wedgeLeft (h : 2 + 1 = finrank ℝ E) (ξ : E) :
    LinearMap.adjoint ((o.hodgeStar h : ⋀[ℝ]^2 E →ₗ[ℝ] ⋀[ℝ]^1 E) ∘ₗ
        ExteriorAlgebra.wedgeLeft ξ 1) =
      -((o.hodgeStar h : ⋀[ℝ]^2 E →ₗ[ℝ] ⋀[ℝ]^1 E) ∘ₗ ExteriorAlgebra.wedgeLeft ξ 1) := by
  refine ((LinearMap.eq_adjoint_iff _ _).2 fun x y ↦ ?_).symm
  simp [o.inner_hodgeStar_wedgeLeft ξ h h x y]

/-- **The symbol of the curl is self-adjoint**: `(i ξ × ·)† = -i (-ξ × ·)`. -/
@[simp]
theorem adjoint_curl : (curl X o).adjoint = curl X o := by
  have h : 2 + 1 = finrank ℝ E := (Fact.out : finrank ℝ E = 3).symm
  have hneg (T : ⋀[ℝ]^1 E →L[ℝ] ⋀[ℝ]^1 E) : (-T).complexifyL2 = -T.complexifyL2 := by
    rw [eq_neg_iff_add_eq_zero, ← ContinuousLinearMap.complexifyL2_add, neg_add_cancel,
      ContinuousLinearMap.complexifyL2_zero]
  ext1
  funext p
  rw [coefficient_adjoint, coefficient_curl h, ContinuousLinearMap.adjoint.map_smulₛₗ,
    ContinuousLinearMap.adjoint_complexifyL2, ← LinearMap.adjoint_toContinuousLinearMap,
    adjoint_hodgeStar_comp_wedgeLeft, Complex.conj_I, map_neg, hneg, smul_neg, neg_smul, neg_neg]

/-- **`curl grad = 0`** on symbols: `ξ × ξ = 0`, since `ξ ∧ ξ = 0`. -/
@[simp]
theorem curl_comp_extDeriv_zero : (curl X o).comp (extDeriv X E 0) = 0 := by
  have h : 2 + 1 = finrank ℝ E := (Fact.out : finrank ℝ E = 3).symm
  ext1
  funext p
  rw [coefficient_comp, coefficient_curl_eq_comp h, ContinuousLinearMap.comp_assoc,
    ← coefficient_comp, extDeriv_comp_extDeriv, coefficient_zero, Pi.zero_apply,
    ContinuousLinearMap.comp_zero, coefficient_zero, Pi.zero_apply]

/-- **`div curl = 0`** on symbols: the adjoint of the symbol of the gradient, the symbol of the
negative divergence, vanishes on the image of the symbol of the curl. -/
@[simp]
theorem adjoint_extDeriv_zero_comp_curl : (extDeriv X E 0).adjoint.comp (curl X o) = 0 := by
  -- Take the adjoint of `curl grad = 0`, using that the curl is self-adjoint.
  have h := congrArg adjoint (curl_comp_extDeriv_zero (X := X) (o := o))
  rw [adjoint_comp, adjoint_curl, adjoint_zero] at h
  ext1
  funext p
  simpa using congrFun (congrArg coefficient h) p

/-- **`curl* curl = d* d` on `1`-forms**: since the Hodge star is an isometry, the symbol of the
curl has the same square as the symbol of the exterior derivative on `1`-forms. -/
theorem adjoint_curl_comp_curl :
    (curl X o).adjoint.comp (curl X o) = (extDeriv X E 1).adjoint.comp (extDeriv X E 1) := by
  have h : 2 + 1 = finrank ℝ E := (Fact.out : finrank ℝ E = 3).symm
  -- The complexified star `S` satisfies `S† S = 1`.
  have hS : ContinuousLinearMap.adjoint
      (LinearMap.toContinuousLinearMap (o.hodgeStar h : ⋀[ℝ]^2 E →ₗ[ℝ] ⋀[ℝ]^1 E)).complexifyL2 ∘L
        (LinearMap.toContinuousLinearMap (o.hodgeStar h : ⋀[ℝ]^2 E →ₗ[ℝ] ⋀[ℝ]^1 E)).complexifyL2 =
      ContinuousLinearMap.id ℂ _ := by
    rw [ContinuousLinearMap.adjoint_complexifyL2, ← ContinuousLinearMap.complexifyL2_comp,
      ← ContinuousLinearMap.complexifyL2_id]
    congr 1
    ext1 x
    refine ext_inner_left ℝ fun y ↦ ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
    simp [o.inner_hodgeStar_hodgeStar]
  ext1
  funext p
  rw [coefficient_comp, coefficient_comp, coefficient_adjoint, coefficient_adjoint,
    coefficient_curl_eq_comp h, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc _ _ ((extDeriv X E 1).coefficient p), hS,
    ContinuousLinearMap.id_comp]

/-- **The Laplacian of `grad` and `curl`**: the Laplacian `σ(grad) σ(grad)† + σ(curl)† σ(curl)` of
the symbol sequence `ℂ → (⋀¹ E)_ℂ → (⋀¹ E)_ℂ` is `‖ξ‖² Id`, the symbol of the Hodge Laplacian on
`1`-forms. -/
theorem hodgeLaplacian_extDeriv_zero_curl :
    (extDeriv X E 0).hodgeLaplacian (curl X o) = normRpow X E _ (2 * 1) := by
  rw [← hodgeLaplacian_extDeriv 0]
  ext1
  funext p
  have hc := congrFun (congrArg coefficient (adjoint_curl_comp_curl (X := X) (o := o))) p
  rw [coefficient_comp, coefficient_comp, coefficient_adjoint, coefficient_adjoint] at hc
  rw [coefficient_hodgeLaplacian, coefficient_hodgeLaplacian,
    ContinuousLinearMap.hodgeLaplacian_def, ContinuousLinearMap.hodgeLaplacian_def]
  exact congrArg (_ + ·) hc

/-- **`curl curl - grad div = -Δ`** on symbols: `σ(curl)² + σ(grad) σ(grad)† = ‖ξ‖² Id`, where
`σ(grad)† = -σ(div)`. -/
theorem curl_comp_curl_add_extDeriv_zero_comp_adjoint :
    (curl X o).comp (curl X o) + (extDeriv X E 0).comp (extDeriv X E 0).adjoint =
      normRpow X E _ (1 + 1) :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    have hp := congrFun (congrArg coefficient (hodgeLaplacian_extDeriv_zero_curl (X := X) (o := o)))
      (x, ξ)
    rw [coefficient_hodgeLaplacian, ContinuousLinearMap.hodgeLaplacian_def,
      ← coefficient_adjoint (curl X o), adjoint_curl,
      coefficient_normRpow_of_ne_zero _ _ _ hξ] at hp
    rw [coefficient_add, Pi.add_apply, coefficient_comp, coefficient_comp, coefficient_adjoint,
      add_comm, hp, coefficient_normRpow_of_ne_zero _ _ _ hξ]
    norm_num

/-- **The kernel of the curl symbol is the image of the gradient symbol**: at every nonzero
covector `ξ`, the symbol sequence `ℂ → (⋀¹ E)_ℂ → (⋀¹ E)_ℂ`, `c ↦ i c ξ`, `v ↦ i ξ × v`, is
exact. -/
theorem exact_extDeriv_zero_curl {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    Function.Exact ((extDeriv X E 0).coefficient (x, ξ)) ((curl X o).coefficient (x, ξ)) := by
  refine exact_of_isElliptic_hodgeLaplacian _ _ curl_comp_extDeriv_zero ?_ hξ
  rw [hodgeLaplacian_extDeriv_zero_curl]
  exact isElliptic_normRpow X E _ _

/-- **The curl is not elliptic**: at every nonzero covector `ξ`, the symbol `i ξ × ·` kills the
nonzero `1`-form `ξ`. -/
theorem not_isElliptic_curl [Nonempty X] : ¬ (curl X o).IsElliptic := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [Fact.out (p := finrank ℝ E = 3)]; norm_num)
  have h₀ : finrank ℂ (WithLp 2 (Complexification (⋀[ℝ]^0 E))) = 1 := by
    simp [WithLp.finrank_complexification]
  have : Nontrivial (WithLp 2 (Complexification (⋀[ℝ]^0 E))) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : E)
  obtain ⟨c, hc⟩ := exists_ne (0 : WithLp 2 (Complexification (⋀[ℝ]^0 E)))
  intro hcurl
  have hinj := (isElliptic_iff.1 hcurl (Classical.arbitrary X) ξ hξ).injective
  have hzero : (curl X o).coefficient (Classical.arbitrary X, ξ)
      ((extDeriv X E 0).coefficient (Classical.arbitrary X, ξ) c) = 0 := by
    rw [← ContinuousLinearMap.comp_apply, ← coefficient_comp, curl_comp_extDeriv_zero,
      coefficient_zero, Pi.zero_apply, zero_apply]
  exact hc (injective_extDeriv_zero hξ (hinj (by rw [hzero, map_zero, map_zero])))

end HomogeneousSymbol

namespace ClassicalSymbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

/-! ### First-order operators with constant coefficients -/

/-- The classical symbol of order `1` with full symbol `L ξ`, for a continuous real-linear function
`L` of the frequency: the symbol of the first-order operator `u ↦ -i ∑ⱼ L(eⱼ) ∂ⱼ u` with constant
coefficients (`TauCeti.ClassicalSymbol.quantizeSchwartzValue_ofLinear`). Its principal symbol is
`HomogeneousSymbol.ofLinear L` (`TauCeti.ClassicalSymbol.principal_ofLinear`). -/
def ofLinear (L : CoordinateSpace n →L[ℝ] (V →L[ℂ] W)) : ClassicalSymbol n V W 1 :=
  ofContDiffHomogeneous (fun p ↦ L p.2) (L.contDiff.comp contDiff_snd)
    fun _ _ _ _ _ ↦ by rw [Real.rpow_one, map_smul]

/-- The full symbol of `ClassicalSymbol.ofLinear L` is `L ξ`. -/
@[simp]
theorem coefficient_toSymbol_ofLinear (L : CoordinateSpace n →L[ℝ] (V →L[ℂ] W))
    (p : CoordinateSpace n × CoordinateSpace n) :
    (ofLinear L).toSymbol.coefficient p = L p.2 := by
  rw [ofLinear, toSymbol_ofContDiffHomogeneous, Symbol.coefficient_ofContDiffHomogeneous]

/-- The principal symbol of `ClassicalSymbol.ofLinear L` is the homogeneous symbol `L ξ`. -/
@[simp]
theorem principal_ofLinear (L : CoordinateSpace n →L[ℝ] (V →L[ℂ] W)) :
    (ofLinear L).principal = HomogeneousSymbol.ofLinear _ L :=
  HomogeneousSymbol.ext_of_ne_zero fun x ξ hξ ↦ by
    rw [ofLinear, principal_ofContDiffHomogeneous,
      HomogeneousSymbol.coefficient_mk'_of_ne_zero _ _ _ hξ, HomogeneousSymbol.coefficient_ofLinear]

/-- The full symbol `L ξ` is the differential symbol of `u ↦ -i ∑ⱼ L(eⱼ) ∂ⱼ u`. -/
private theorem differentialSymbol_ofLinear (L : CoordinateSpace n →L[ℝ] (V →L[ℂ] W))
    (p : CoordinateSpace n × CoordinateSpace n) :
    differentialSymbol (k := fun _ : Fin n ↦ 1) Finset.univ (fun j _ ↦ EuclideanSpace.single j 1)
      (fun j _ ↦ -Complex.I • L (EuclideanSpace.single j 1)) p = L p.2 := by
  rw [differentialSymbol_def]
  conv_rhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr p.2]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [smul_smul, ← Complex.coe_smul]
  congr 1
  simp only [EuclideanSpace.inner_single_right, one_mul, RCLike.conj_to_real, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, pow_one]
  ring_nf
  simp

/-- **First-order operators with constant coefficients are pseudodifferential operators.** On
Schwartz input, the quantization of `ClassicalSymbol.ofLinear L` is `u ↦ -i ∑ⱼ L(eⱼ) ∂ⱼ u`, with no
smoothing remainder. -/
theorem quantizeSchwartzValue_ofLinear [CompleteSpace V] [CompleteSpace W]
    (L : CoordinateSpace n →L[ℝ] (V →L[ℂ] W)) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (ofLinear L).toSymbol.coefficient u x =
      -Complex.I • ∑ j, L (EuclideanSpace.single j 1)
        (∂_{(EuclideanSpace.single j 1 : CoordinateSpace n)} u x) := by
  have h : (ofLinear L).toSymbol.coefficient =
      differentialSymbol (k := fun _ : Fin n ↦ 1) Finset.univ
        (fun j _ ↦ EuclideanSpace.single j 1)
        (fun j _ ↦ -Complex.I • L (EuclideanSpace.single j 1)) :=
    funext fun p ↦ by rw [coefficient_toSymbol_ofLinear, differentialSymbol_ofLinear]
  rw [h, quantizeSchwartzValue_differentialSymbol, Finset.smul_sum]
  simp [LineDeriv.iteratedLineDerivOp_one]

/-! ### The curl on `ℝ³` -/

variable [Fact (finrank ℝ (CoordinateSpace n) = 3)] (o : Orientation ℝ (CoordinateSpace n) (Fin 3))

/-- **The curl** on the oriented three-dimensional coordinate space, acting on functions with values
in complex `1`-forms: the classical symbol of order `1` of `curl u = ∑ⱼ ⋆ (eⱼ ∧ ∂ⱼ u)`
(`TauCeti.ClassicalSymbol.quantizeSchwartzValue_curl`), with principal symbol
`HomogeneousSymbol.curl` (`TauCeti.ClassicalSymbol.principal_curl`). -/
def curl : ClassicalSymbol n (WithLp 2 (Complexification (⋀[ℝ]^1 (CoordinateSpace n))))
    (WithLp 2 (Complexification (⋀[ℝ]^1 (CoordinateSpace n)))) 1 :=
  ofLinear (curlLinear o)

/-- The principal symbol of the curl is `i ⋆ (ξ ∧ ·)`, the symbol `i ξ × ·`. -/
@[simp]
theorem principal_curl : (curl o).principal = HomogeneousSymbol.curl _ o := by
  rw [curl, principal_ofLinear, HomogeneousSymbol.curl]

/-- **The curl is a pseudodifferential operator**: on Schwartz input the quantization of
`ClassicalSymbol.curl` is the curl `u ↦ ∑ⱼ ⋆ (eⱼ ∧ ∂ⱼ u)`, with no smoothing remainder. -/
theorem quantizeSchwartzValue_curl (h : 2 + 1 = finrank ℝ (CoordinateSpace n))
    (u : 𝓢(CoordinateSpace n, WithLp 2 (Complexification (⋀[ℝ]^1 (CoordinateSpace n)))))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (curl o).toSymbol.coefficient u x =
      ∑ j, (LinearMap.toContinuousLinearMap
        ((o.hodgeStar h : ⋀[ℝ]^2 (CoordinateSpace n) →ₗ[ℝ] ⋀[ℝ]^1 (CoordinateSpace n)) ∘ₗ
          ExteriorAlgebra.wedgeLeft (EuclideanSpace.single j 1 : CoordinateSpace n) 1)).complexifyL2
            (∂_{(EuclideanSpace.single j 1 : CoordinateSpace n)} u x) := by
  rw [curl, quantizeSchwartzValue_ofLinear, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [curlLinear_apply o h, smul_apply, smul_smul]
  simp

/-- **The curl is not elliptic.** -/
theorem not_isElliptic_curl : ¬ (curl o).IsElliptic := by
  rw [isElliptic_def, principal_curl]
  exact HomogeneousSymbol.not_isElliptic_curl

end ClassicalSymbol

end TauCeti
