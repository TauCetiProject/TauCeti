/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Analysis.Pseudodifferential.Quantization
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical

/-!
# Quantization of polynomial differential symbols

A finite differential expression `u ↦ ∑ i ∈ s, bᵢ(x) (∂^{vᵢ} u)(x)` has left
Fourier symbol `∑ i ∈ s, (∏ j, i ⟪ξ, vᵢⱼ⟫) bᵢ(x)`. Here the directions are arbitrary
real vectors, the derivative orders may vary with the summand, and the coefficients are
continuous complex-linear maps between the input and output fibers.

`TauCeti.quantizeSchwartzValue_differentialSymbol` proves exact equality between this
expression and Kohn–Nirenberg quantization on Schwartz input. In particular the factor for
an order-`k` derivative is `i^k`, and there is no residual smoothing term. The frequency
rescaling by `2π` is the one in `TauCeti.quantizeSchwartzValue`.

No regularity or boundedness of the position-dependent coefficients is needed for the
pointwise identity or its absolute convergence: at a fixed position these are finitely
many fixed linear maps applied to Fourier transforms of Schwartz derivatives. Smooth
coefficients give smooth outputs. The support theorem records locality of these operators.

On `ℝⁿ`, the symbol of a differential expression of order at most `M` with smooth coefficients is
a classical symbol of order `M` (`TauCeti.ClassicalSymbol.ofDifferentialSymbol`), so differential
operators are classical pseudodifferential operators. Its homogeneous term of degree `M - j` is
the symbol of the summands with exactly `M - j` derivatives
(`TauCeti.ClassicalSymbol.coefficient_term_ofDifferentialSymbol`), and its principal symbol that
of the summands with `M` derivatives
(`TauCeti.ClassicalSymbol.coefficient_principal_ofDifferentialSymbol`). In this convention the
derivative `∂_v` has principal symbol `i ⟪ξ, v⟫`. The coefficients need no bounds, since the
estimates of classical symbols are only required on compact sets of positions. As an example, the
negative Laplacian `-Δ` (`TauCeti.ClassicalSymbol.negLaplacian`) has full and principal symbol
`‖ξ‖² id`, which is elliptic (`TauCeti.ClassicalSymbol.isElliptic_negLaplacian`), and its
quantization is `-Δ` on Schwartz input
(`TauCeti.ClassicalSymbol.quantizeSchwartzValue_negLaplacian`).

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (1.1)–(1.4), for quantization and its differential-operator convention, and (1.17) for
  classical symbols.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open scoped ContDiff FourierTransform SchwartzMap RealInnerProductSpace LineDeriv
open MeasureTheory Real FourierTransform

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  {ι : Type*} {k : ι → ℕ}

/-- The left Fourier symbol of a finite differential expression with coefficient maps `b`
and derivative directions `v`. Each directional derivative contributes `i ⟪ξ, v⟫`. -/
def differentialSymbol (s : Finset ι) (v : ∀ i, Fin (k i) → E)
    (b : ι → E → V →L[ℂ] W) : E × E → V →L[ℂ] W :=
  fun p ↦ ∑ i ∈ s, (∏ j, (Complex.I * (⟪p.2, v i j⟫ : ℂ))) • b i p.1

theorem differentialSymbol_def (s : Finset ι) (v : ∀ i, Fin (k i) → E)
    (b : ι → E → V →L[ℂ] W) (p : E × E) :
    differentialSymbol s v b p =
      ∑ i ∈ s, (∏ j, (Complex.I * (⟪p.2, v i j⟫ : ℂ))) • b i p.1 := (rfl)

/-- The Fourier symbol of a differential expression is `i^order` times its geometric
polynomial symbol, separately in each summand. -/
theorem differentialSymbol_eq_sum_pow_mul (s : Finset ι) (v : ∀ i, Fin (k i) → E)
    (b : ι → E → V →L[ℂ] W) (p : E × E) :
    differentialSymbol s v b p =
      ∑ i ∈ s, (Complex.I ^ k i * ∏ j, (⟪p.2, v i j⟫ : ℂ)) • b i p.1 := by
  simp [differentialSymbol, Finset.prod_mul_distrib]

@[simp]
theorem differentialSymbol_empty (v : ∀ i, Fin (k i) → E)
    (b : ι → E → V →L[ℂ] W) : differentialSymbol ∅ v b = 0 := by
  funext p
  simp [differentialSymbol]

@[simp]
theorem differentialSymbol_singleton (i : ι) (v : ∀ i, Fin (k i) → E)
    (b : ι → E → V →L[ℂ] W) (p : E × E) :
    differentialSymbol {i} v b p =
      (∏ j, (Complex.I * (⟪p.2, v i j⟫ : ℂ))) • b i p.1 := by
  simp [differentialSymbol]

@[simp]
theorem differentialSymbol_insert [DecidableEq ι] (s : Finset ι) (i : ι) (hi : i ∉ s)
    (v : ∀ i, Fin (k i) → E) (b : ι → E → V →L[ℂ] W) (p : E × E) :
    differentialSymbol (insert i s) v b p =
      (∏ j, (Complex.I * (⟪p.2, v i j⟫ : ℂ))) • b i p.1 +
        differentialSymbol s v b p := by
  simp [differentialSymbol, Finset.sum_insert hi]

@[simp]
theorem differentialSymbol_zero (s : Finset ι) (v : ∀ i, Fin (k i) → E) :
    differentialSymbol s v (0 : ι → E → V →L[ℂ] W) = 0 := by
  funext p
  simp [differentialSymbol]

@[simp]
theorem differentialSymbol_add (s : Finset ι) (v : ∀ i, Fin (k i) → E)
    (b c : ι → E → V →L[ℂ] W) (p : E × E) :
    differentialSymbol s v (b + c) p =
      differentialSymbol s v b p + differentialSymbol s v c p := by
  simp [differentialSymbol, smul_add, Finset.sum_add_distrib]

@[simp]
theorem differentialSymbol_smul (s : Finset ι) (v : ∀ i, Fin (k i) → E)
    (z : ℂ) (b : ι → E → V →L[ℂ] W) :
    differentialSymbol s v (z • b) = z • differentialSymbol s v b := by
  funext p
  simp [differentialSymbol, smul_comm _ z, Finset.smul_sum]

/-- A differential symbol with coefficients of class `C^N` is of class `C^N` in the position and
the frequency together. -/
theorem contDiff_differentialSymbol {N : WithTop ℕ∞} (s : Finset ι) (v : ∀ i, Fin (k i) → E)
    (b : ι → E → V →L[ℂ] W) (hb : ∀ i ∈ s, ContDiff ℝ N (b i)) :
    ContDiff ℝ N (differentialSymbol s v b) := by
  refine ContDiff.sum fun i hi ↦ ?_
  have hp : ContDiff ℝ N fun p : E × E ↦ ∏ j, (Complex.I * (⟪p.2, v i j⟫ : ℂ)) :=
    contDiff_prod fun j _ ↦ contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_snd.inner ℝ contDiff_const))
  exact hp.smul ((hb i hi).comp contDiff_fst)

/-- A differential symbol all of whose derivatives have order `d` is homogeneous of degree `d` in
the frequency: `σ(x, t ξ) = t ^ d σ(x, ξ)` for every real `t`. -/
theorem differentialSymbol_smul_snd {d : ℕ} (s : Finset ι) (v : ∀ i, Fin (k i) → E)
    (b : ι → E → V →L[ℂ] W) (hs : ∀ i ∈ s, k i = d) (x ξ : E) (t : ℝ) :
    differentialSymbol s v b (x, t • ξ) = t ^ d • differentialSymbol s v b (x, ξ) := by
  simp only [differentialSymbol_def, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have h : ∏ j, (Complex.I * (⟪t • ξ, v i j⟫ : ℂ)) =
      (t : ℂ) ^ d * ∏ j, (Complex.I * (⟪ξ, v i j⟫ : ℂ)) := by
    simp only [real_inner_smul_left, Complex.ofReal_mul, mul_left_comm Complex.I (t : ℂ),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hs i hi]
  rw [h, mul_smul, ← Complex.ofReal_pow, Complex.coe_smul]

/-! ### Differential symbols are classical symbols -/

section Classical

variable {n : ℕ} (M : ℕ) (s : Finset ι) (v : ∀ i, Fin (k i) → CoordinateSpace n)
  (b : ι → CoordinateSpace n → V →L[ℂ] W) (hb : ∀ i ∈ s, ContDiff ℝ ∞ (b i))
  (hk : ∀ i ∈ s, k i ≤ M)

include hk in
/-- The summands of a differential expression of order at most `M` with `j` derivatives fewer
than `M` form a symbol homogeneous of degree `M - j`; there are none when `j > M`. -/
private theorem differentialSymbol_filter_smul_snd (j : ℕ) (x ξ : CoordinateSpace n) (t : ℝ) :
    differentialSymbol {i ∈ s | M - k i = j} v b (x, t • ξ) =
      t ^ ((M : ℝ) - j) • differentialSymbol {i ∈ s | M - k i = j} v b (x, ξ) := by
  rcases le_or_gt j M with hj | hj
  · rw [differentialSymbol_smul_snd (d := M - j) _ v b (fun i hi ↦ ?_) x ξ t,
      ← Nat.cast_sub hj, Real.rpow_natCast]
    rw [Finset.mem_filter] at hi
    have := hk i hi.1
    omega
  · rw [Finset.filter_eq_empty_iff.2 fun i hi h ↦ by omega]
    simp

/-- The summands of a differential expression of order at most `M` with exactly `M - j` derivatives,
as a classical symbol of order `M` whose only nonzero homogeneous term is the `j`-th. -/
private def ClassicalSymbol.ofDifferentialSymbolPart (j : ℕ) : ClassicalSymbol n V W M :=
  ClassicalSymbol.inclusion j rfl
    (ClassicalSymbol.ofContDiff (differentialSymbol {i ∈ s | M - k i = j} v b)
      (contDiff_differentialSymbol _ v b fun i hi ↦ hb i (Finset.mem_filter.1 hi).1)
      fun x ξ t _ ↦ differentialSymbol_filter_smul_snd M s v b hk j x ξ t)

/-- The full symbol `σ(x, ξ) = ∑ i ∈ s, (∏ⱼ i ⟪ξ, vᵢⱼ⟫) bᵢ(x)` of a differential expression
`u ↦ ∑ i ∈ s, bᵢ (∂^{vᵢ} u)` of order at most `M` with smooth coefficients, as a classical symbol
of order `M`. Its homogeneous term of degree `M - j` collects the summands with exactly `M - j`
derivatives (`TauCeti.ClassicalSymbol.coefficient_term_ofDifferentialSymbol`); in particular its
principal symbol collects those with `M` derivatives
(`TauCeti.ClassicalSymbol.coefficient_principal_ofDifferentialSymbol`). No bound on the
coefficients is needed, since classical symbols only carry estimates on compact sets of
positions. -/
def ClassicalSymbol.ofDifferentialSymbol : ClassicalSymbol n V W M :=
  ∑ j ∈ Finset.range (M + 1), ClassicalSymbol.ofDifferentialSymbolPart M s v b hb hk j

namespace ClassicalSymbol

/-- Away from `ξ = 0`, the `j`-th homogeneous term of the `l`-th part is the symbol of the summands
with exactly `M - j` derivatives when `l = j`, and zero otherwise. -/
private theorem coefficient_term_ofDifferentialSymbolPart (l j : ℕ) {x ξ : CoordinateSpace n}
    (hξ : ξ ≠ 0) : ((ofDifferentialSymbolPart M s v b hb hk l).term j).coefficient (x, ξ) =
      if l = j then differentialSymbol {i ∈ s | M - k i = j} v b (x, ξ) else 0 := by
  rw [ofDifferentialSymbolPart, term_inclusion]
  split_ifs with h₁ h₂ h₂
  · subst h₂
    simp [coefficient_term_ofContDiff _ _ _ _ hξ]
  · rw [HomogeneousSymbol.coefficient_castDegree, coefficient_term_ofContDiff _ _ _ _ hξ]
    simp only [show j - l ≠ 0 by omega, ↓reduceIte]
  · omega
  · simp

/-- The full symbol of `ofDifferentialSymbol` is the differential symbol. -/
@[simp]
theorem coefficient_toSymbol_ofDifferentialSymbol :
    (ofDifferentialSymbol M s v b hb hk).toSymbol.coefficient = differentialSymbol s v b := by
  funext p
  simp only [ofDifferentialSymbol, ofDifferentialSymbolPart, toSymbol_sum, Symbol.coefficient_sum,
    Finset.sum_apply, toSymbol_inclusion, Symbol.coefficient_inclusion,
    coefficient_toSymbol_ofContDiff, differentialSymbol_def]
  exact Finset.sum_fiberwise_of_maps_to (fun i hi ↦ Finset.mem_range.2 (by omega)) _

/-- Away from `ξ = 0`, the homogeneous term of degree `M - j` of the classical symbol of a
differential expression is the symbol of its summands with exactly `M - j` derivatives. -/
theorem coefficient_term_ofDifferentialSymbol (j : ℕ) {x ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    ((ofDifferentialSymbol M s v b hb hk).term j).coefficient (x, ξ) =
      differentialSymbol {i ∈ s | M - k i = j} v b (x, ξ) := by
  simp only [ofDifferentialSymbol, term_sum, HomogeneousSymbol.coefficient_sum, Finset.sum_apply,
    coefficient_term_ofDifferentialSymbolPart M s v b hb hk _ j hξ, Finset.sum_ite_eq',
    Finset.mem_range]
  split_ifs with hj
  · rfl
  · rw [Finset.filter_eq_empty_iff.2 fun i _ h ↦ by omega]
    simp

/-- **The principal symbol of a differential operator.** Away from `ξ = 0`, the principal symbol
of the classical symbol of a differential expression of order at most `M` is the symbol
`∑ (∏ⱼ i ⟪ξ, vᵢⱼ⟫) bᵢ(x)` of its summands with exactly `M` derivatives. In particular the
derivative `∂_v` has principal symbol `i ⟪ξ, v⟫`. -/
theorem coefficient_principal_ofDifferentialSymbol {x ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    (ofDifferentialSymbol M s v b hb hk).principal.coefficient (x, ξ) =
      differentialSymbol {i ∈ s | k i = M} v b (x, ξ) := by
  rw [coefficient_principal, coefficient_term_ofDifferentialSymbol M s v b hb hk 0 hξ,
    Finset.filter_congr fun i hi ↦ (by have := hk i hi; omega : M - k i = 0 ↔ k i = M)]

/-! ### The negative Laplacian -/

/-- The differential symbol of `-∑ⱼ ∂ⱼ²` is `‖ξ‖² id`: each coordinate contributes
`-(i ξⱼ)² = ξⱼ²`. -/
private theorem differentialSymbol_negLaplacian (p : CoordinateSpace n × CoordinateSpace n) :
    differentialSymbol Finset.univ
        (fun j : Fin n ↦ ![EuclideanSpace.single j 1, EuclideanSpace.single j 1])
        (fun _ _ ↦ -ContinuousLinearMap.id ℂ V) p =
      ((‖p.2‖ ^ 2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V := by
  simp only [differentialSymbol_def, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul, EuclideanSpace.norm_sq_eq,
    Real.norm_eq_abs, sq_abs, smul_neg, ← neg_smul, ← Finset.sum_smul]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  linear_combination (-(p.2 j : ℂ) ^ 2) * Complex.I_sq

variable (V) in
/-- The classical symbol of order `2` of the negative Laplacian `-Δ = -∑ⱼ ∂ⱼ²` on `V`-valued
functions, where `∂ⱼ` is the derivative along the `j`-th coordinate vector. -/
def negLaplacian : ClassicalSymbol n V V 2 :=
  ofDifferentialSymbol 2 Finset.univ
    (fun j : Fin n ↦ ![EuclideanSpace.single j 1, EuclideanSpace.single j 1])
    (fun _ _ ↦ -ContinuousLinearMap.id ℂ V) (fun _ _ ↦ contDiff_const) fun _ _ ↦ le_rfl

/-- The full symbol of the negative Laplacian `-∑ⱼ ∂ⱼ²` is `‖ξ‖² id`. -/
@[simp]
theorem coefficient_toSymbol_negLaplacian (p : CoordinateSpace n × CoordinateSpace n) :
    (negLaplacian V).toSymbol.coefficient p =
      ((‖p.2‖ ^ 2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V := by
  rw [negLaplacian, coefficient_toSymbol_ofDifferentialSymbol, differentialSymbol_negLaplacian]

/-- Away from `ξ = 0`, the principal symbol of the negative Laplacian `-∑ⱼ ∂ⱼ²` is `‖ξ‖² id`. -/
theorem coefficient_principal_negLaplacian {x ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    (negLaplacian V).principal.coefficient (x, ξ) =
      ((‖ξ‖ ^ 2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V := by
  rw [negLaplacian, coefficient_principal_ofDifferentialSymbol _ _ _ _ _ _ hξ,
    Finset.filter_true_of_mem fun _ _ ↦ rfl, differentialSymbol_negLaplacian]

/-- **The negative Laplacian is elliptic**: its principal symbol `‖ξ‖² id` is invertible at every
nonzero frequency. -/
theorem isElliptic_negLaplacian : (negLaplacian (n := n) V).IsElliptic := by
  refine isElliptic_iff.2 fun x ξ hξ ↦ ?_
  rw [coefficient_principal_negLaplacian hξ, ContinuousLinearMap.isInvertible_smul_iff
    (by exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 hξ))]
  simpa using ContinuousLinearMap.isInvertible_equiv (f := .refl ℂ V)

end ClassicalSymbol

end Classical

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- After frequency rescaling, a differential monomial times `𝓕 u` is exactly the Fourier
transform of the corresponding derivative, with the coefficient map applied afterwards. -/
private theorem smul_apply_fourier_eq_apply_fourier_iteratedLineDerivOp {r : ℕ} (v : Fin r → E)
    (B : V →L[ℂ] W) (u : 𝓢(E, V)) (ζ : E) :
    ((∏ j, (Complex.I * (⟪(2 * π) • ζ, v j⟫ : ℂ))) • B) (𝓕 u ζ) =
      B (𝓕 (∂^{v} u) ζ) := by
  rw [smul_apply, SchwartzMap.fourier_iteratedLineDerivOp_apply,
    map_smul]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp only [real_inner_smul_left]
  push_cast
  ring

/-- Absolute convergence for a differential monomial follows from the Schwartz decay of
the Fourier transform of the derivative, regardless of the coefficient map. -/
private theorem integrable_quantizeSchwartzValue_integrand_prod_inner {r : ℕ}
    (v : Fin r → E) (B : V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) :
    Integrable (fun ζ ↦ 𝐞 ⟪ζ, x⟫ •
      ((∏ j, (Complex.I * (⟪(2 * π) • ζ, v j⟫ : ℂ))) • B) (𝓕 u ζ)) := by
  simp only [smul_apply_fourier_eq_apply_fourier_iteratedLineDerivOp]
  have h : Integrable (fun ζ ↦ 𝐞 ⟪ζ, x⟫ • 𝓕 (∂^{v} u) ζ) := by
    simpa [inner_neg_right] using
      (Real.fourierIntegral_convergent_iff (μ := volume) (-x)).2 (𝓕 (∂^{v} u)).integrable
  simpa only [Circle.smul_def, map_smul] using B.integrable_comp h

/-- A polynomial differential symbol has an absolutely convergent quantization integral
on every Schwartz input, even without smoothness of its position-dependent coefficients. -/
theorem integrable_quantizeSchwartzValue_integrand_differentialSymbol
    (s : Finset ι) (v : ∀ i, Fin (k i) → E) (b : ι → E → V →L[ℂ] W)
    (u : 𝓢(E, V)) (x : E) :
    Integrable (fun ζ ↦ 𝐞 ⟪ζ, x⟫ • differentialSymbol s v b (x, (2 * π) • ζ) (𝓕 u ζ)) := by
  simp only [differentialSymbol_def, sum_apply, Finset.smul_sum]
  exact integrable_finsetSum _ fun i _ ↦
    integrable_quantizeSchwartzValue_integrand_prod_inner (v i) (b i x) u x

variable [CompleteSpace V] [CompleteSpace W]

/-- The monomial quantization integral is the corresponding derivative followed by
its fixed coefficient map. -/
private theorem integral_smul_apply_fourier_prod_inner {r : ℕ} (v : Fin r → E)
    (B : V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) :
    (∫ ζ, 𝐞 ⟪ζ, x⟫ •
      ((∏ j, (Complex.I * (⟪(2 * π) • ζ, v j⟫ : ℂ))) • B) (𝓕 u ζ)) =
      B (∂^{v} u x) := by
  calc
    _ = quantizeSchwartzValue (fun _ ↦ B) (∂^{v} u) x := by
      simp only [quantizeSchwartzValue_def,
        smul_apply_fourier_eq_apply_fourier_iteratedLineDerivOp]
    _ = _ := quantizeSchwartzValue_comp_fst (fun _ ↦ B) (∂^{v} u) x

/-- **Exact differential-operator comparison.** The left quantization of the polynomial
Fourier symbol of a finite differential expression equals that expression on Schwartz input.
There are no derivatives of the coefficients in left quantization. -/
@[simp]
theorem quantizeSchwartzValue_differentialSymbol (s : Finset ι)
    (v : ∀ i, Fin (k i) → E) (b : ι → E → V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue (differentialSymbol s v b) u x =
      ∑ i ∈ s, b i x (∂^{v i} u x) := by
  simp only [quantizeSchwartzValue_def, differentialSymbol_def,
    sum_apply, Finset.smul_sum]
  rw [integral_finsetSum _ fun i _ ↦
    integrable_quantizeSchwartzValue_integrand_prod_inner (v i) (b i x) u x]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_smul_apply_fourier_prod_inner (v i) (b i x) u x

/-- The same comparison written with native iterated Fréchet derivatives. -/
theorem quantizeSchwartzValue_differentialSymbol_eq_sum_iteratedFDeriv (s : Finset ι)
    (v : ∀ i, Fin (k i) → E) (b : ι → E → V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue (differentialSymbol s v b) u x =
      ∑ i ∈ s, b i x (iteratedFDeriv ℝ (k i) u x (v i)) := by
  simp only [quantizeSchwartzValue_differentialSymbol,
    SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]

/-- Coefficients of class `C^n` give quantized differential expressions of class `C^n`.
No global boundedness of any coefficient or its derivatives is required. -/
theorem contDiff_quantizeSchwartzValue_differentialSymbol {n : ℕ∞} (s : Finset ι)
    (v : ∀ i, Fin (k i) → E) (b : ι → E → V →L[ℂ] W)
    (hb : ∀ i ∈ s, ContDiff ℝ n (b i)) (u : 𝓢(E, V)) :
    ContDiff ℝ n (quantizeSchwartzValue (differentialSymbol s v b) u) := by
  simp only [funext (quantizeSchwartzValue_differentialSymbol s v b u)]
  apply ContDiff.sum
  intro i hi
  -- Restrict coefficient maps to real scalars, since smoothness is over the real base.
  have hbi := (ContinuousLinearMap.restrictScalarsL ℂ V W ℝ ℝ).contDiff.comp (hb i hi)
  simpa only [Function.comp_apply, ContinuousLinearMap.coe_restrict_scalarsL',
    ContinuousLinearMap.coe_restrictScalars'] using hbi.clm_apply ((∂^{v i} u).smooth n)

/-- The quantized differential expression is supported in the topological support
(closure of the support) of the Schwartz input, even for nonsmooth coefficients. -/
theorem support_quantizeSchwartzValue_differentialSymbol_subset (s : Finset ι)
    (v : ∀ i, Fin (k i) → E) (b : ι → E → V →L[ℂ] W) (u : 𝓢(E, V)) :
    Function.support (quantizeSchwartzValue (differentialSymbol s v b) u) ⊆ tsupport u := by
  intro x hx
  by_contra h
  apply hx
  rw [quantizeSchwartzValue_differentialSymbol]
  apply Finset.sum_eq_zero
  intro i _
  have hzero : (∂^{v i} u) x = 0 :=
    image_eq_zero_of_notMem_tsupport fun hx' ↦
      h (SchwartzMap.tsupport_iteratedLineDerivOp_subset (v i) u hx')
  simp [hzero]

/-- The left quantization of the classical symbol of a differential expression is that
expression, on Schwartz input. -/
theorem ClassicalSymbol.quantizeSchwartzValue_ofDifferentialSymbol {n : ℕ} (M : ℕ) (s : Finset ι)
    (v : ∀ i, Fin (k i) → CoordinateSpace n) (b : ι → CoordinateSpace n → V →L[ℂ] W)
    (hb : ∀ i ∈ s, ContDiff ℝ ∞ (b i)) (hk : ∀ i ∈ s, k i ≤ M) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (ClassicalSymbol.ofDifferentialSymbol M s v b hb hk).toSymbol.coefficient
      u x = ∑ i ∈ s, b i x (∂^{v i} u x) := by
  rw [ClassicalSymbol.coefficient_toSymbol_ofDifferentialSymbol,
    quantizeSchwartzValue_differentialSymbol]

open Laplacian in
/-- The left quantization of the classical symbol `ClassicalSymbol.negLaplacian` is the negative
Laplacian `-Δ` on Schwartz input. -/
theorem ClassicalSymbol.quantizeSchwartzValue_negLaplacian {n : ℕ} (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (ClassicalSymbol.negLaplacian V).toSymbol.coefficient u x = -Δ u x := by
  rw [ClassicalSymbol.negLaplacian, ClassicalSymbol.quantizeSchwartzValue_ofDifferentialSymbol,
    SchwartzMap.laplacian_eq_sum (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp [LineDeriv.iteratedLineDerivOp_succ_left, EuclideanSpace.basisFun_apply]

end TauCeti
