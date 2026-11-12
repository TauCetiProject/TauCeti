/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.DifferentialSymbol
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical

/-!
# Classical symbols of differential operators

A differential operator `P u = ∑ i ∈ s, bᵢ(x) (∂^{vᵢ} u)(x)` on `ℝⁿ` with smooth coefficient maps
`bᵢ`, where `∂^{vᵢ}` is a derivative of order `kᵢ ≤ m` along the directions `vᵢ`, has the
polynomial Fourier symbol

`p(x, ξ) = ∑ i ∈ s, (∏ⱼ i ⟪ξ, vᵢⱼ⟫) bᵢ(x)`

(`TauCeti.differentialSymbol`), whose left quantization is `P` on Schwartz functions
(`TauCeti.quantizeSchwartzValue_differentialSymbol`). This file shows that `p` is a classical
symbol of order `m`, whose homogeneous term of degree `m - j` is the part of `p` coming from
the derivatives of order exactly `m - j`. In particular its principal symbol is the top order
part `∑_{kᵢ = m} (∏ⱼ i ⟪ξ, vᵢⱼ⟫) bᵢ(x)`, with the Fourier convention `σ(∂_v)(ξ) = i ⟪ξ, v⟫`,
and `P` is elliptic exactly when this top order part is invertible at every nonzero frequency.
The coefficients only need to be smooth: the symbol estimates of a classical symbol hold on
compact sets of positions, so no bound on the coefficients as `x → ∞` is required. This is what
lets the elliptic symbol calculus (parametrices, elliptic regularity) apply to differential
operators with smooth coefficients.

## Main declarations

* `TauCeti.HomogeneousSymbol.ofDifferentialSymbol`: the symbol of a differential expression all
  of whose derivatives have order `d`, as a homogeneous symbol of degree `d`.
* `TauCeti.ClassicalSymbol.ofDifferentialSymbol`: the polynomial symbol of a differential operator
  of order at most `m` with smooth coefficients, as a classical symbol of order `m`, with
  `TauCeti.ClassicalSymbol.coefficient_toSymbol_ofDifferentialSymbol` (its full symbol is
  `TauCeti.differentialSymbol`), `TauCeti.ClassicalSymbol.coefficient_term_ofDifferentialSymbol`
  (its homogeneous terms) and `TauCeti.ClassicalSymbol.principal_ofDifferentialSymbol`.
* `TauCeti.ClassicalSymbol.quantizeSchwartzValue_ofDifferentialSymbol`: its quantization is the
  differential operator.
* `TauCeti.ClassicalSymbol.isElliptic_ofDifferentialSymbol_iff`: ellipticity is invertibility of
  the top order part.
* `TauCeti.ClassicalSymbol.negLaplacian`: the symbol `‖ξ‖²` of `-Δ = -∑ⱼ ∂ⱼ²`, an elliptic
  classical symbol of order `2` (`TauCeti.ClassicalSymbol.isElliptic_negLaplacian`).

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (1.1)–(1.4) and (1.17).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap LineDeriv

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {ι : Type*} {k : ι → ℕ}

/-! ### Homogeneous parts of differential symbols -/

namespace HomogeneousSymbol

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The symbol `∑ i ∈ s, (∏ⱼ i ⟪ξ, vᵢⱼ⟫) bᵢ(x)` of a differential expression with smooth
coefficients all of whose derivatives have order `d`, as a homogeneous symbol of degree `d`.
It agrees with `TauCeti.differentialSymbol` at every nonzero frequency
(`TauCeti.HomogeneousSymbol.coefficient_ofDifferentialSymbol_of_ne_zero`). -/
def ofDifferentialSymbol (s : Finset ι) (v : ∀ i, Fin (k i) → E) (b : ι → E → V →L[ℂ] W)
    (hb : ∀ i ∈ s, ContDiff ℝ ∞ (b i)) {d : ℕ} (hd : ∀ i ∈ s, k i = d) :
    HomogeneousSymbol E E V W d :=
  mk' (differentialSymbol s v b) (contDiff_differentialSymbol s v b hb).contDiffOn
    fun x ξ _ t _ ↦ by
      rw [differentialSymbol_smul_snd s v b hd, Real.rpow_natCast]

@[simp]
theorem coefficient_ofDifferentialSymbol_of_ne_zero (s : Finset ι) (v : ∀ i, Fin (k i) → E)
    (b : ι → E → V →L[ℂ] W) (hb : ∀ i ∈ s, ContDiff ℝ ∞ (b i)) {d : ℕ}
    (hd : ∀ i ∈ s, k i = d) {x ξ : E} (hξ : ξ ≠ 0) :
    (ofDifferentialSymbol s v b hb hd).coefficient (x, ξ) = differentialSymbol s v b (x, ξ) :=
  coefficient_mk'_of_ne_zero _ _ _ hξ

end HomogeneousSymbol

namespace ClassicalSymbol

/-! ### The classical symbol of a differential operator -/

section Differential

variable (m : ℕ) (s : Finset ι) (v : ∀ i, Fin (k i) → CoordinateSpace n)
  (b : ι → CoordinateSpace n → V →L[ℂ] W) (hb : ∀ i ∈ s, ContDiff ℝ ∞ (b i))

/-- The polynomial Fourier symbol `p(x, ξ) = ∑ i ∈ s, (∏ⱼ i ⟪ξ, vᵢⱼ⟫) bᵢ(x)` of the differential
operator `u ↦ ∑ i ∈ s, bᵢ(x) (∂^{vᵢ} u)(x)` with smooth coefficients, as a classical symbol of
order `m`. Its homogeneous term of degree `m - j` is the part of `p` coming from the derivatives
of order `m - j` (`TauCeti.ClassicalSymbol.coefficient_term_ofDifferentialSymbol`). Summands with
derivatives of order greater than `m` are discarded, so when every `kᵢ ≤ m` its full symbol is
`TauCeti.differentialSymbol s v b`
(`TauCeti.ClassicalSymbol.coefficient_toSymbol_ofDifferentialSymbol`). -/
def ofDifferentialSymbol : ClassicalSymbol n V W m :=
  ∑ d : Fin (m + 1), inclusion (m - d) (by rw [Nat.cast_sub (Nat.lt_succ_iff.1 d.isLt)]; ring)
    (ofHomogeneousOfContDiff
      (HomogeneousSymbol.ofDifferentialSymbol (s.filter fun i ↦ k i = d) v b
        (fun i hi ↦ hb i (Finset.mem_filter.1 hi).1) fun _ hi ↦ (Finset.mem_filter.1 hi).2)
      (contDiff_differentialSymbol _ v b fun i hi ↦ hb i (Finset.mem_filter.1 hi).1)
      fun _ _ hξ ↦
        (HomogeneousSymbol.coefficient_ofDifferentialSymbol_of_ne_zero _ _ _ _ _ hξ).symm)

/-- For an operator of order at most `m`, the full symbol of
`TauCeti.ClassicalSymbol.ofDifferentialSymbol` is the polynomial symbol
`TauCeti.differentialSymbol s v b`. -/
@[simp]
theorem coefficient_toSymbol_ofDifferentialSymbol (hk : ∀ i ∈ s, k i ≤ m) :
    (ofDifferentialSymbol m s v b hb).toSymbol.coefficient = differentialSymbol s v b := by
  funext p
  simp only [ofDifferentialSymbol, toSymbol_sum, Symbol.coefficient_sum, Finset.sum_apply,
    toSymbol_inclusion, Symbol.coefficient_inclusion, coefficient_toSymbol_ofHomogeneousOfContDiff,
    differentialSymbol_def]
  rw [Fin.sum_univ_eq_sum_range (fun d ↦ ∑ i ∈ s with k i = d,
      (∏ j, (Complex.I * (⟪p.2, v i j⟫ : ℂ))) • b i p.1),
    Finset.sum_fiberwise_of_maps_to fun i hi ↦ Finset.mem_range.2 (Nat.lt_succ_of_le (hk i hi))]

/-- **The homogeneous terms of a differential symbol.** The homogeneous term of degree `m - j` of
the classical symbol of a differential operator of order at most `m` is, at nonzero frequencies,
the symbol of the part of the operator of order exactly `m - j`. For `j > m` it vanishes. -/
theorem coefficient_term_ofDifferentialSymbol (j : ℕ) {x ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    ((ofDifferentialSymbol m s v b hb).term j).coefficient (x, ξ) =
      differentialSymbol (s.filter fun i ↦ k i + j = m) v b (x, ξ) := by
  simp only [ofDifferentialSymbol, term_sum, HomogeneousSymbol.coefficient_sum, Finset.sum_apply,
    coefficient_term_inclusion_ofHomogeneousOfContDiff]
  -- The summand of degree `d` contributes its only term exactly when `j = m - d`, namely the
  -- summands of `s` with `k i = d` and `k i + j = m`.
  have hterm : ∀ d : Fin (m + 1),
      (if j = m - d then (HomogeneousSymbol.ofDifferentialSymbol (s.filter fun i ↦ k i = d) v b
          (fun i hi ↦ hb i (Finset.mem_filter.1 hi).1)
          fun _ hi ↦ (Finset.mem_filter.1 hi).2).coefficient else 0) (x, ξ) =
      ∑ i ∈ (s.filter fun i ↦ k i + j = m).filter fun i ↦ k i = d,
        (∏ l, (Complex.I * (⟪ξ, v i l⟫ : ℂ))) • b i x := by
    intro d
    have hd := Nat.lt_succ_iff.1 d.isLt
    rw [Finset.filter_filter]
    by_cases hdj : (d : ℕ) + j = m
    · rw [ite_eq_left (by omega),
        HomogeneousSymbol.coefficient_ofDifferentialSymbol_of_ne_zero _ _ _ _ _ hξ,
        differentialSymbol_def]
      exact Finset.sum_congr (Finset.filter_congr fun i _ ↦ by omega) fun _ _ ↦ rfl
    · rw [ite_eq_right (by omega), Pi.zero_apply]
      refine (Finset.sum_eq_zero fun i hi ↦ ?_).symm
      simp only [Finset.mem_filter] at hi
      omega
  rw [Finset.sum_congr rfl fun d _ ↦ hterm d,
    Fin.sum_univ_eq_sum_range
      (fun d ↦ ∑ i ∈ (s.filter fun i ↦ k i + j = m).filter fun i ↦ k i = d,
        (∏ l, (Complex.I * (⟪ξ, v i l⟫ : ℂ))) • b i x),
    Finset.sum_fiberwise_of_maps_to fun i hi ↦ by
      simp only [Finset.mem_filter] at hi
      simp only [Finset.mem_range]
      omega,
    differentialSymbol_def]

/-- **The principal symbol of a differential operator** of order at most `m` is, at nonzero
frequencies, the symbol `∑_{kᵢ = m} (∏ⱼ i ⟪ξ, vᵢⱼ⟫) bᵢ(x)` of its part of order exactly `m`. -/
theorem principal_ofDifferentialSymbol :
    (ofDifferentialSymbol m s v b hb).principal =
      HomogeneousSymbol.ofDifferentialSymbol (s.filter fun i ↦ k i = m) v b
        (fun i hi ↦ hb i (Finset.mem_filter.1 hi).1) fun _ hi ↦ (Finset.mem_filter.1 hi).2 :=
  HomogeneousSymbol.ext_of_ne_zero fun x ξ hξ ↦ by
    rw [coefficient_principal, coefficient_term_ofDifferentialSymbol _ _ _ _ _ 0 hξ,
      HomogeneousSymbol.coefficient_ofDifferentialSymbol_of_ne_zero _ _ _ _ _ hξ]
    simp

/-- **Ellipticity of a differential operator.** The classical symbol of a differential operator
of order at most `m` is elliptic exactly when the symbol of its part of order exactly `m` is
invertible at every position and every nonzero frequency. -/
theorem isElliptic_ofDifferentialSymbol_iff :
    (ofDifferentialSymbol m s v b hb).IsElliptic ↔ ∀ x ξ, ξ ≠ 0 →
      (differentialSymbol (s.filter fun i ↦ k i = m) v b (x, ξ)).IsInvertible := by
  rw [isElliptic_iff, principal_ofDifferentialSymbol]
  refine forall_congr' fun x ↦ forall_congr' fun ξ ↦ forall_congr' fun hξ ↦ ?_
  rw [HomogeneousSymbol.coefficient_ofDifferentialSymbol_of_ne_zero _ _ _ _ _ hξ]

/-- **Quantization of a differential symbol.** On Schwartz functions, the quantization of the
classical symbol of `u ↦ ∑ i ∈ s, bᵢ(x) (∂^{vᵢ} u)(x)` is this differential operator. -/
theorem quantizeSchwartzValue_ofDifferentialSymbol [CompleteSpace V] [CompleteSpace W]
    (hk : ∀ i ∈ s, k i ≤ m) (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (ofDifferentialSymbol m s v b hb).toSymbol.coefficient u x =
      ∑ i ∈ s, b i x (∂^{v i} u x) := by
  rw [coefficient_toSymbol_ofDifferentialSymbol m s v b hb hk,
    quantizeSchwartzValue_differentialSymbol]

end Differential

/-! ### The Laplacian -/

section Laplacian

variable (n V)

/-- The classical symbol `‖ξ‖²` of the nonnegative Laplacian `-Δ = -∑ⱼ ∂ⱼ²` acting on
`V`-valued functions on `ℝⁿ`: the symbol of each `∂ⱼ` is `i ξⱼ`, so `-∂ⱼ²` has symbol `ξⱼ²`.
It is elliptic (`TauCeti.ClassicalSymbol.isElliptic_negLaplacian`). -/
def negLaplacian : ClassicalSymbol n V V (2 : ℕ) :=
  ofDifferentialSymbol 2 Finset.univ (k := fun _ : Fin n ↦ 2)
    (fun j _ ↦ EuclideanSpace.single j 1) (fun _ _ ↦ -ContinuousLinearMap.id ℂ V)
    fun _ _ ↦ contDiff_const

variable {n V}

/-- The symbol of `-∑ⱼ ∂ⱼ²` is `‖ξ‖²` times the identity. -/
private theorem differentialSymbol_negLaplacian (p : CoordinateSpace n × CoordinateSpace n) :
    differentialSymbol Finset.univ (k := fun _ : Fin n ↦ 2) (fun j _ ↦ EuclideanSpace.single j 1)
      (fun _ _ ↦ -ContinuousLinearMap.id ℂ V) p =
      ((‖p.2‖ ^ 2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V := by
  rw [differentialSymbol_def, EuclideanSpace.real_norm_sq_eq, Complex.ofReal_sum,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [EuclideanSpace.inner_single_right, one_mul, Fin.prod_univ_two, smul_neg,
    ← neg_smul, conj_trivial]
  congr 1
  push_cast
  ring_nf
  simp [Complex.I_sq]

@[simp]
theorem coefficient_toSymbol_negLaplacian (p : CoordinateSpace n × CoordinateSpace n) :
    (negLaplacian n V).toSymbol.coefficient p =
      ((‖p.2‖ ^ 2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V := by
  rw [negLaplacian, coefficient_toSymbol_ofDifferentialSymbol _ _ _ _ _ fun _ _ ↦ le_rfl,
    differentialSymbol_negLaplacian]

/-- The principal symbol of `-Δ` is `‖ξ‖²` times the identity. -/
theorem coefficient_principal_negLaplacian {x ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    (negLaplacian n V).principal.coefficient (x, ξ) =
      ((‖ξ‖ ^ 2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V := by
  rw [negLaplacian, principal_ofDifferentialSymbol,
    HomogeneousSymbol.coefficient_ofDifferentialSymbol_of_ne_zero _ _ _ _ _ hξ,
    Finset.filter_true_of_mem fun _ _ ↦ rfl, differentialSymbol_negLaplacian]

/-- On Schwartz functions the quantization of `TauCeti.ClassicalSymbol.negLaplacian` is
`-∑ⱼ ∂ⱼ²`. -/
theorem quantizeSchwartzValue_negLaplacian [CompleteSpace V] (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (negLaplacian n V).toSymbol.coefficient u x =
      -∑ j : Fin n, ∂^{fun _ : Fin 2 ↦ EuclideanSpace.single j (1 : ℝ)} u x := by
  rw [negLaplacian, quantizeSchwartzValue_ofDifferentialSymbol _ _ _ _ _ fun _ _ ↦ le_rfl,
    ← Finset.sum_neg_distrib]
  simp

/-- `-Δ` is elliptic: its principal symbol `‖ξ‖²` is invertible at every nonzero frequency. -/
theorem isElliptic_negLaplacian : (negLaplacian n V).IsElliptic := by
  rw [isElliptic_iff]
  intro x ξ hξ
  rw [coefficient_principal_negLaplacian hξ,
    ContinuousLinearMap.isInvertible_smul_iff (by simpa using hξ)]
  exact ⟨ContinuousLinearEquiv.refl ℂ V, rfl⟩

end Laplacian

end ClassicalSymbol

end TauCeti
