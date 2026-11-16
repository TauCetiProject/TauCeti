/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.LineDeriv
public import TauCeti.Analysis.Distribution.WaveFrontSet.SingularSupport
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.ProdInner
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod

/-!
# Microlocal elliptic regularity for differential operators

Let `P = ∑ i ∈ s, c i a i ∂^(m i)` be a linear differential operator with smooth real coefficient
functions `a i`, complex constants `c i` and iterated directional derivatives `∂^(m i)` of orders
`k i ≤ M`; complex coefficients are sums of such terms. Its principal symbol of order `M`, in the
geometric convention without factors of `i`, is

`σ_M(P)(x, ξ) = ∑ i ∈ s with k i = M, c i a i(x) ∏ₗ ⟪m i l, ξ⟫`

(`TauCeti.smoothCoeffPrincipalSymbol`), and its *characteristic set*
(`TauCeti.smoothCoeffCharacteristicSet`) consists of the points `(x, ξ)` with `ξ ≠ 0` and
`σ_M(P)(x, ξ) = 0`. This file proves **microlocal elliptic regularity**: at a noncharacteristic
covector, `T` is as regular as `P T`,

`WF(T) ⊆ WF(P T) ∪ Char(P)`

(`Distribution.waveFrontSet_subset_waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_union`).
Together with the reverse microlocality `WF(P T) ⊆ WF(T)` of differential operators
(`Distribution.waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset`), an elliptic
operator, one whose principal symbol vanishes at no `(x, ξ)` with `x ∈ Ω` and `ξ ≠ 0`, satisfies
`WF(P T) = WF(T)`, and hence has the same singular support: `P T` is smooth on an open set exactly
when `T` is. Operators with constant coefficients, with principal symbol
`TauCeti.constCoeffPrincipalSymbol`, are the case `a i = 1`; the Laplacian is the basic example
(`Distribution.waveFrontSet_laplacianCLM`).

## The argument

Write `L(T, ψ)(η) = T (ψ e_η)` for the localized Fourier transform. Multiplication by `a i` moves
onto the cutoff, `L(a T, ψ) = L(T, a ψ)`, and so do the derivatives,
`L(∂_v T, ψ) = 2πi ⟪v, η⟫ L(T, ψ) - L(T, ∂_v ψ)`. With variable coefficients the principal part
`∑ i ∈ s with k i = M, c i ∏ₗ 2πi ⟪m i l, η⟫ L(T, a i θ)(η)` is `(2πi) ^ M L(T, σ_M(P)(·, η) θ)(η)`,
which is `(2πi) ^ M ‖η‖ ^ M L(T, ψ)(η)` for the cutoff `θ = ‖η‖ ^ M ψ / σ_M(P)(·, η)`. This cutoff
depends on the frequency `η` at which the localized Fourier transform is evaluated, so all estimates
are made uniformly over *bounded families* of cutoffs `η ↦ ψ η`, supported in a fixed compact set
and bounded in every `C^n` norm uniformly in `η`. Near a noncharacteristic `(x, ξ)`, the principal
symbol divided by `‖η‖ ^ M` is a smooth nonvanishing function of `x` and of the direction of `η`,
so dividing by it preserves bounded families on a small cone around `ξ`. The localized Fourier
transforms of `T` and of `P T` with the cutoffs of bounded families grow polynomially and decay
where `P T` is microlocally smooth, uniformly over the family
(`Distribution.exists_forall_norm_localFourier_le_of_forall_norm_iteratedFDeriv_le`,
`Distribution.IsMicrolocallySmoothAt.exists_nhds_cone_of_forall_norm_iteratedFDeriv_le`). The
identity then shows that if `L(T, ψ η)(η)` is `O((1 + ‖η‖) ^ (k - j))` for every bounded family,
it is `O((1 + ‖η‖) ^ (k - j - 1))`: the errors from derivatives falling on the cutoff, and the terms
of order less than `M`, have one power of `η` fewer than the principal part. Induction on `j` gives
rapid decay.

## Main definitions

* `TauCeti.smoothCoeffPrincipalSymbol s c a m M`: the principal symbol `σ_M(P)` of order `M` of
  an operator with smooth coefficients.
* `TauCeti.smoothCoeffCharacteristicSet s c a m M`: its characteristic set `Char(P)`.
* `TauCeti.constCoeffPrincipalSymbol s c m M`, `TauCeti.constCoeffCharacteristicSet s c m M`:
  the same for constant coefficients.

## Main results

* `Distribution.IsMicrolocallySmoothAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp`: if `P T` is
  microlocally smooth at `(x, ξ)` and `σ_M(P)(x, ξ) ≠ 0`, then `T` is microlocally smooth there.
* `Distribution.waveFrontSet_subset_waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_union`:
  `WF(T) ⊆ WF(P T) ∪ Char(P)`.
* `Distribution.waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_forall_ne_zero`,
  `Distribution.singularSupport_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_forall_ne_zero`: an
  elliptic operator with smooth coefficients preserves the wave front set and the singular
  support.
* `Distribution.IsMicrolocallySmoothAt.of_sum_smul_iteratedLineDerivOp`,
  `Distribution.waveFrontSet_subset_waveFrontSet_sum_smul_iteratedLineDerivOp_union`,
  `Distribution.waveFrontSet_sum_smul_iteratedLineDerivOp_of_forall_ne_zero`,
  `Distribution.singularSupport_sum_smul_iteratedLineDerivOp_of_forall_ne_zero`: the same for
  constant coefficients.
* `Distribution.waveFrontSet_laplacianCLM`, `Distribution.singularSupport_laplacianCLM`:
  `WF(Δ T) = WF(T)` and `singsupp(Δ T) = singsupp(T)` for the Laplacian
  `Δ = LineDeriv.laplacianCLM ℝ E 𝓓'(Ω, ℂ)`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.3.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, Lecture I, §7.
-/

public section

noncomputable section

open Complex Filter LineDeriv Real Set TopologicalSpace TestFunction
open scoped Distributions Topology RealInnerProductSpace ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The principal symbol and the characteristic set -/

/-- The **principal symbol** of order `M` of the constant-coefficient operator
`P = ∑ i ∈ s, c i ∂^(m i)`, in the geometric convention without factors of `i`:
`σ_M(P)(ξ) = ∑ i ∈ s with k i = M, c i ∏ₗ ⟪m i l, ξ⟫`. Only the terms of order exactly `M`
contribute. -/
def constCoeffPrincipalSymbol {ι : Type*} (s : Finset ι) (c : ι → ℂ) {k : ι → ℕ}
    (m : ∀ i, Fin (k i) → E) (M : ℕ) (ξ : E) : ℂ :=
  ∑ i ∈ s with k i = M, c i * ∏ l, (⟪m i l, ξ⟫ : ℂ)

/-- The **characteristic set** of the constant-coefficient operator `P = ∑ i ∈ s, c i ∂^(m i)`
of order `M`: the points `(x, ξ)` with `ξ ≠ 0` at which the principal symbol
`constCoeffPrincipalSymbol s c m M` vanishes. -/
def constCoeffCharacteristicSet {ι : Type*} (s : Finset ι) (c : ι → ℂ) {k : ι → ℕ}
    (m : ∀ i, Fin (k i) → E) (M : ℕ) : Set (E × E) :=
  {p | p.2 ≠ 0 ∧ constCoeffPrincipalSymbol s c m M p.2 = 0}

theorem constCoeffPrincipalSymbol_def {ι : Type*} (s : Finset ι) (c : ι → ℂ) {k : ι → ℕ}
    (m : ∀ i, Fin (k i) → E) (M : ℕ) (ξ : E) :
    constCoeffPrincipalSymbol s c m M ξ = ∑ i ∈ s with k i = M, c i * ∏ l, (⟪m i l, ξ⟫ : ℂ) :=
  (rfl)

@[fun_prop]
theorem continuous_constCoeffPrincipalSymbol {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) (M : ℕ) :
    Continuous (constCoeffPrincipalSymbol s c m M) := by
  unfold constCoeffPrincipalSymbol
  fun_prop

@[simp]
theorem mem_constCoeffCharacteristicSet_iff {ι : Type*} {s : Finset ι} {c : ι → ℂ} {k : ι → ℕ}
    {m : ∀ i, Fin (k i) → E} {M : ℕ} {p : E × E} :
    p ∈ constCoeffCharacteristicSet s c m M ↔
      p.2 ≠ 0 ∧ constCoeffPrincipalSymbol s c m M p.2 = 0 :=
  Iff.rfl

/-- The characteristic set is empty exactly when the operator is elliptic: its principal symbol
vanishes at no `ξ ≠ 0`. -/
theorem constCoeffCharacteristicSet_eq_empty_iff {ι : Type*} {s : Finset ι}
    {c : ι → ℂ} {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ} :
    constCoeffCharacteristicSet s c m M = ∅ ↔
      ∀ ξ : E, ξ ≠ 0 → constCoeffPrincipalSymbol s c m M ξ ≠ 0 := by
  simp only [eq_empty_iff_forall_notMem, mem_constCoeffCharacteristicSet_iff, Prod.forall,
    not_and, ne_eq]
  exact ⟨fun h ξ ↦ h 0 ξ, fun h _ ξ ↦ h ξ⟩

/-! ### Operators with smooth coefficients -/

/-- The **principal symbol** of order `M` of the operator `P = ∑ i ∈ s, c i a i ∂^(m i)` with smooth
real coefficients `a i` and complex constants `c i`, in the geometric convention without factors of
`i`: `σ_M(P)(x, ξ) = ∑ i ∈ s with k i = M, c i a i(x) ∏ₗ ⟪m i l, ξ⟫`. Only the terms of order
exactly `M` contribute. -/
def smoothCoeffPrincipalSymbol {ι : Type*} (s : Finset ι) (c : ι → ℂ) (a : ι → E → ℝ)
    {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) (M : ℕ) (x ξ : E) : ℂ :=
  ∑ i ∈ s with k i = M, c i * a i x * ∏ l, (⟪m i l, ξ⟫ : ℂ)

/-- The **characteristic set** of the operator `P = ∑ i ∈ s, c i a i ∂^(m i)` of order `M`: the
points `(x, ξ)` with `ξ ≠ 0` at which the principal symbol `smoothCoeffPrincipalSymbol s c a m M`
vanishes. -/
def smoothCoeffCharacteristicSet {ι : Type*} (s : Finset ι) (c : ι → ℂ) (a : ι → E → ℝ)
    {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) (M : ℕ) : Set (E × E) :=
  {p | p.2 ≠ 0 ∧ smoothCoeffPrincipalSymbol s c a m M p.1 p.2 = 0}

section SmoothCoeff

variable {ι : Type*} {s : Finset ι} {c : ι → ℂ} {a : ι → E → ℝ} {k : ι → ℕ}
  {m : ∀ i, Fin (k i) → E} {M : ℕ}

theorem smoothCoeffPrincipalSymbol_def (s : Finset ι) (c : ι → ℂ) (a : ι → E → ℝ)
    (m : ∀ i, Fin (k i) → E) (M : ℕ) (x ξ : E) :
    smoothCoeffPrincipalSymbol s c a m M x ξ =
      ∑ i ∈ s with k i = M, c i * a i x * ∏ l, (⟪m i l, ξ⟫ : ℂ) :=
  (rfl)

@[simp]
theorem mem_smoothCoeffCharacteristicSet_iff {p : E × E} :
    p ∈ smoothCoeffCharacteristicSet s c a m M ↔
      p.2 ≠ 0 ∧ smoothCoeffPrincipalSymbol s c a m M p.1 p.2 = 0 :=
  Iff.rfl

/-- The principal symbol is jointly as smooth as the coefficients: it is polynomial in `ξ`. -/
theorem contDiff_smoothCoeffPrincipalSymbol {n : WithTop ℕ∞} (ha : ∀ i, ContDiff ℝ n (a i)) :
    ContDiff ℝ n fun p : E × E ↦ smoothCoeffPrincipalSymbol s c a m M p.1 p.2 := by
  unfold smoothCoeffPrincipalSymbol
  refine ContDiff.sum fun i _ ↦ ?_
  refine ((contDiff_const.mul (ofRealCLM.contDiff.comp ((ha i).comp contDiff_fst))).mul
    (contDiff_prod fun l _ ↦ ofRealCLM.contDiff.comp ?_))
  exact contDiff_const.inner ℝ contDiff_snd

/-- The principal symbol is homogeneous of degree `M` in `ξ`. -/
theorem smoothCoeffPrincipalSymbol_smul (s : Finset ι) (c : ι → ℂ) (a : ι → E → ℝ)
    (m : ∀ i, Fin (k i) → E) (M : ℕ) (x : E) (t : ℝ) (η : E) :
    smoothCoeffPrincipalSymbol s c a m M x (t • η) =
      (t : ℂ) ^ M * smoothCoeffPrincipalSymbol s c a m M x η := by
  rw [smoothCoeffPrincipalSymbol, smoothCoeffPrincipalSymbol, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hki : k i = M := (Finset.mem_filter.1 hi).2
  have hprod : ∏ l, (⟪m i l, t • η⟫ : ℂ) = (t : ℂ) ^ k i * ∏ l, (⟪m i l, η⟫ : ℂ) := by
    simp only [inner_smul_right, ofReal_mul]
    rw [← Finset.pow_card_mul_prod, Finset.card_univ, Fintype.card_fin]
  have hpow : (t : ℂ) ^ k i = (t : ℂ) ^ M := by rw [hki]
  rw [hprod, hpow]
  ring

/-- The characteristic set is conic in the frequency variable. -/
theorem smul_mem_smoothCoeffCharacteristicSet_iff {x ξ : E} {t : ℝ} (ht : t ≠ 0) :
    (x, t • ξ) ∈ smoothCoeffCharacteristicSet s c a m M ↔
      (x, ξ) ∈ smoothCoeffCharacteristicSet s c a m M := by
  simp [smoothCoeffPrincipalSymbol_smul, ht]

/-- With the constant coefficients `a i = 1`, the principal symbol is that of the
constant-coefficient operator `∑ i ∈ s, c i ∂^(m i)`. -/
@[simp]
theorem smoothCoeffPrincipalSymbol_const_one (s : Finset ι) (c : ι → ℂ)
    (m : ∀ i, Fin (k i) → E) (M : ℕ) (x ξ : E) :
    smoothCoeffPrincipalSymbol s c (fun _ _ ↦ 1) m M x ξ = constCoeffPrincipalSymbol s c m M ξ := by
  simp [smoothCoeffPrincipalSymbol, constCoeffPrincipalSymbol]

/-- With the constant coefficients `a i = 1`, the characteristic set is that of the
constant-coefficient operator `∑ i ∈ s, c i ∂^(m i)`. -/
@[simp]
theorem smoothCoeffCharacteristicSet_const_one (s : Finset ι) (c : ι → ℂ)
    (m : ∀ i, Fin (k i) → E) (M : ℕ) :
    smoothCoeffCharacteristicSet s c (fun _ _ ↦ 1) m M = constCoeffCharacteristicSet s c m M := by
  ext p
  simp

end SmoothCoeff

/-- The principal symbol is homogeneous of degree `M`. -/
theorem constCoeffPrincipalSymbol_smul {ι : Type*} (s : Finset ι) (c : ι → ℂ) {k : ι → ℕ}
    (m : ∀ i, Fin (k i) → E) (M : ℕ) (t : ℝ) (η : E) :
    constCoeffPrincipalSymbol s c m M (t • η) =
      (t : ℂ) ^ M * constCoeffPrincipalSymbol s c m M η := by
  simpa using smoothCoeffPrincipalSymbol_smul s c (fun _ _ ↦ 1) m M 0 t η

/-- The characteristic set is conic in the frequency variable. -/
theorem smul_mem_constCoeffCharacteristicSet_iff {ι : Type*} {s : Finset ι} {c : ι → ℂ}
    {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ} {x ξ : E} {t : ℝ} (ht : t ≠ 0) :
    (x, t • ξ) ∈ constCoeffCharacteristicSet s c m M ↔
      (x, ξ) ∈ constCoeffCharacteristicSet s c m M := by
  simp [constCoeffPrincipalSymbol_smul, ht]

/-- **An elliptic cone.** If the principal symbol does not vanish at `ξ`, then it is bounded
below by `c₀ ‖η‖ ^ M` on an open cone around `ξ`, for some `c₀ > 0`. -/
theorem exists_cone_le_norm_constCoeffPrincipalSymbol {ι : Type*} {s : Finset ι} {c : ι → ℂ}
    {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ} {ξ : E}
    (hξ : constCoeffPrincipalSymbol s c m M ξ ≠ 0) :
    ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ η ∈ Γ, c₀ * ‖η‖ ^ M ≤ ‖constCoeffPrincipalSymbol s c m M η‖ := by
  -- `‖ξ‖ ^ M ≠ 0`: otherwise `ξ = 0` and `M ≠ 0`, and every term of the principal symbol at `ξ`
  -- has a factor `⟪_, 0⟫ = 0`.
  have hξM : 0 < ‖ξ‖ ^ M := by
    rcases eq_or_ne ξ 0 with rfl | hξ0
    · rcases Nat.eq_zero_or_pos M with rfl | hM
      · simp
      · refine absurd (Finset.sum_eq_zero fun i hi ↦ ?_) hξ
        have hki : k i = M := (Finset.mem_filter.1 hi).2
        rw [Finset.prod_eq_zero (i := ⟨0, hki ▸ hM⟩) (Finset.mem_univ _) (by simp), mul_zero]
    · exact pow_pos (norm_pos_iff.2 hξ0) M
  have hσξ := norm_pos_iff.2 hξ
  refine ⟨{η | ‖constCoeffPrincipalSymbol s c m M ξ‖ / (2 * ‖ξ‖ ^ M) * ‖η‖ ^ M <
      ‖constCoeffPrincipalSymbol s c m M η‖}, isOpen_lt (by fun_prop) (by fun_prop),
    ?_, fun t ht η hη ↦ ?_, _, by positivity, fun η hη ↦ hη.le⟩
  · simp only [mem_ofPred_eq]
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hξM.ne']
    linarith
  · simp only [mem_ofPred_eq] at hη ⊢
    rw [constCoeffPrincipalSymbol_smul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg ht.le, norm_smul, Real.norm_of_nonneg ht.le, mul_pow, mul_left_comm]
    exact mul_lt_mul_of_pos_left hη (pow_pos ht M)

end TauCeti

namespace Distribution

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Opens E}

/-! ### Polynomial bounds for the symbol -/

/-- The factor `2πi ⟪v, η⟫` contributed by a derivative `∂_v` is bounded by
`2π ‖v‖ (1 + ‖η‖)`. -/
private theorem norm_two_pi_I_inner_le (v η : E) :
    ‖(2 * π * I * ⟪v, η⟫ : ℂ)‖ ≤ 2 * π * ‖v‖ * (1 + ‖η‖) := by
  calc ‖(2 * π * I * ⟪v, η⟫ : ℂ)‖ = 2 * π * |⟪v, η⟫| := by
        simp [abs_of_pos Real.pi_pos]
    _ ≤ 2 * π * (‖v‖ * (1 + ‖η‖)) := by
        gcongr
        exact (abs_real_inner_le_norm v η).trans
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (norm_nonneg v))
    _ = 2 * π * ‖v‖ * (1 + ‖η‖) := by ring

/-- The symbol of `∂^m` in the frequency variable of the localized Fourier transform is
`(2πi) ^ r` times the product of the inner products. -/
private theorem prod_two_pi_I_inner {r : ℕ} (m : Fin r → E) (η : E) :
    ∏ l, (2 * π * I * ⟪m l, η⟫ : ℂ) = (2 * π * I) ^ r * ∏ l, (⟪m l, η⟫ : ℂ) := by
  rw [← Finset.pow_card_mul_prod, Finset.card_univ, Fintype.card_fin]

/-- The symbol `∏ₗ 2πi ⟪m l, η⟫` of `∂^m` is bounded by `(∏ₗ 2π ‖m l‖) (1 + ‖η‖) ^ r`. -/
private theorem norm_prod_two_pi_I_inner_le {r : ℕ} (m : Fin r → E) (η : E) :
    ‖∏ l, (2 * π * I * ⟪m l, η⟫ : ℂ)‖ ≤ (∏ l, 2 * π * ‖m l‖) * (1 + ‖η‖) ^ r := by
  rw [norm_prod]
  refine (Finset.prod_le_prod₀ (h0 := fun _ _ ↦ norm_nonneg _)
    (h1 := fun l _ ↦ norm_two_pi_I_inner_le (m l) η)).trans (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **A term of lower order.** If `‖X‖` is `O((1 + ‖η‖) ^ k₀ / (1 + ‖η‖) ^ j)`, then
`∏ₗ 2πi ⟪m l, η⟫ X`, for `r < M` directions `m`, is `O((1 + ‖η‖) ^ (k₀ + M) / (1 + ‖η‖) ^ (j + 1))`.
-/
private theorem pow_mul_norm_prod_mul_le {r M j k₀ : ℕ} (hrM : r + 1 ≤ M) (m : Fin r → E) (η : E)
    (c X : ℂ) {C : ℝ} (hX : (1 + ‖η‖) ^ j * ‖X‖ ≤ C * (1 + ‖η‖) ^ k₀) :
    (1 + ‖η‖) ^ (j + 1) * (‖c‖ * ‖∏ l, (2 * π * I * ⟪m l, η⟫ : ℂ)‖ * ‖X‖) ≤
      ‖c‖ * (∏ l, 2 * π * ‖m l‖) * |C| * (1 + ‖η‖) ^ (k₀ + M) := by
  have hw : 1 ≤ 1 + ‖η‖ := le_add_of_nonneg_right (norm_nonneg η)
  calc (1 + ‖η‖) ^ (j + 1) * (‖c‖ * ‖∏ l, (2 * π * I * ⟪m l, η⟫ : ℂ)‖ * ‖X‖)
      ≤ (1 + ‖η‖) ^ (j + 1) * (‖c‖ * ((∏ l, 2 * π * ‖m l‖) * (1 + ‖η‖) ^ r) * ‖X‖) := by
        gcongr
        exact norm_prod_two_pi_I_inner_le m η
    _ = ‖c‖ * (∏ l, 2 * π * ‖m l‖) * (1 + ‖η‖) ^ (r + 1) * ((1 + ‖η‖) ^ j * ‖X‖) := by ring
    _ ≤ ‖c‖ * (∏ l, 2 * π * ‖m l‖) * (1 + ‖η‖) ^ M * (|C| * (1 + ‖η‖) ^ k₀) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity) |>.trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hw hrM)
            (by positivity)) (by positivity))
        exact hX.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    _ = ‖c‖ * (∏ l, 2 * π * ‖m l‖) * |C| * (1 + ‖η‖) ^ (k₀ + M) := by ring

/-! ### Bounded families of cutoffs -/

/-- A family of cutoffs `ψ η` indexed by frequencies, supported in `K` and bounded in every `C^n`
norm uniformly for `η ∈ Γ`. -/
private def IsBddFamily (K Γ : Set E) (ψ : E → 𝓓(Ω, ℂ)) : Prop :=
  (∀ η, tsupport (ψ η) ⊆ K) ∧ ∀ n : ℕ, ∃ B, ∀ η ∈ Γ, ∀ x, ‖iteratedFDeriv ℝ n (ψ η) x‖ ≤ B

/-- A constant family is bounded. -/
private theorem isBddFamily_const {K Γ : Set E} {φ : 𝓓(Ω, ℂ)} (hφ : tsupport φ ⊆ K) :
    IsBddFamily K Γ fun _ ↦ φ := by
  refine ⟨fun _ ↦ hφ, fun n ↦ ?_⟩
  obtain ⟨B, hB⟩ := Continuous.bounded_above_of_compact_support
    (φ.contDiff.continuous_iteratedFDeriv (by simp)) (φ.hasCompactSupport.iteratedFDeriv n)
  exact ⟨B, fun _ _ ↦ hB⟩

/-- Derivatives of a bounded family form a bounded family. -/
private theorem IsBddFamily.lineDerivOp {K Γ : Set E} {ψ : E → 𝓓(Ω, ℂ)}
    (hψ : IsBddFamily K Γ ψ) (v : E) : IsBddFamily K Γ fun η ↦ ∂_{v} (ψ η) := by
  refine ⟨fun η ↦ (tsupport_lineDerivOp_subset _ v).trans (hψ.1 η), fun n ↦ ?_⟩
  obtain ⟨B, hB⟩ := hψ.2 (n + 1)
  refine ⟨‖v‖ * B, fun η hη x ↦ ?_⟩
  have hcoe : ⇑(∂_{v} (ψ η) : 𝓓(Ω, ℂ)) = (ContinuousLinearMap.apply ℝ ℂ v) ∘ fderiv ℝ (ψ η) := by
    ext y
    exact lineDerivOp_apply_eq_fderiv (ψ η) v y
  rw [hcoe]
  refine ((ContinuousLinearMap.apply ℝ ℂ v).norm_iteratedFDeriv_comp_left
    ((ψ η).contDiff.fderiv_right (m := ∞) (by simp)).contDiffAt (by simp)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  have hv : ‖ContinuousLinearMap.apply ℝ ℂ v‖ ≤ ‖v‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun L ↦ by
      simpa [mul_comm] using L.le_opNorm v
  exact mul_le_mul hv (hB η hη x) (norm_nonneg _) (norm_nonneg v)

/-- Multiplying a bounded family by a smooth function gives a bounded family. -/
private theorem IsBddFamily.smulLeftCLM {K Γ : Set E} (hK : IsCompact K) {ψ : E → 𝓓(Ω, ℂ)}
    (hψ : IsBddFamily K Γ ψ) {g : E → ℝ} (hg : ContDiff ℝ ∞ g) :
    IsBddFamily K Γ fun η ↦ TestFunction.smulLeftCLM hg (ψ η) := by
  refine ⟨fun η ↦ (tsupport_smulLeftCLM_subset hg _).trans (inter_subset_right.trans (hψ.1 η)),
    fun n ↦ ?_⟩
  choose B hB using hψ.2
  choose G hG using fun i : ℕ ↦ hK.exists_bound_of_continuousOn
    (hg.continuous_iteratedFDeriv (m := i) (by simp)).continuousOn
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |G i| * |B (n - i)|, fun η hη x ↦ ?_⟩
  by_cases hx : x ∈ K
  · rw [TestFunction.coe_smulLeftCLM]
    refine (norm_iteratedFDeriv_smul_le hg (ψ η).contDiff x (by simp)).trans
      (Finset.sum_le_sum fun i _ ↦ ?_)
    gcongr
    · exact (hG i x hx).trans (le_abs_self _)
    · exact (hB _ η hη x).trans (le_abs_self _)
  · -- Off `K` the product vanishes near `x`, and so do its derivatives.
    rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx ((tsupport_iteratedFDeriv_subset n).trans
      ((tsupport_smulLeftCLM_subset hg _).trans (inter_subset_right.trans (hψ.1 η))) h),
      norm_zero]
    exact Finset.sum_nonneg fun i _ ↦ by positivity

/-- **Each derivative costs one order of decay.** If the localized Fourier transforms of `T` with
cutoffs supported in `U` are `O((1 + ‖η‖) ^ k / (1 + ‖η‖) ^ j)` on `Γ`, those of `∂^m T`, for
`r` directions `m`, are `O((1 + ‖η‖) ^ (k + r) / (1 + ‖η‖) ^ j)`. -/
private theorem exists_localFourier_iteratedLineDerivOp_le {T : 𝓓'(Ω, ℂ)} {K Γ : Set E}
    {j k : ℕ} (hT : ∀ ψ : E → 𝓓(Ω, ℂ), IsBddFamily K Γ ψ →
      ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ j * ‖T.localFourier (ψ η) η‖ ≤ C * (1 + ‖η‖) ^ k)
    {r : ℕ} (m : Fin r → E) (ψ : E → 𝓓(Ω, ℂ)) (hψ : IsBddFamily K Γ ψ) :
    ∃ C, ∀ η ∈ Γ,
      (1 + ‖η‖) ^ j * ‖(∂^{m} T).localFourier (ψ η) η‖ ≤ C * (1 + ‖η‖) ^ (k + r) := by
  induction r generalizing ψ with
  | zero => simpa using hT ψ hψ
  | succ r ih =>
    obtain ⟨C₁, hC₁⟩ := ih (Fin.tail m) ψ hψ
    obtain ⟨C₂, hC₂⟩ := ih (Fin.tail m) (fun η ↦ ∂_{m 0} (ψ η)) (hψ.lineDerivOp _)
    refine ⟨2 * π * ‖m 0‖ * C₁ + |C₂|, fun η hη ↦ ?_⟩
    have hw : 1 ≤ 1 + ‖η‖ := le_add_of_nonneg_right (norm_nonneg η)
    rw [iteratedLineDerivOp_succ_left, localFourier_lineDerivOp]
    calc (1 + ‖η‖) ^ j * ‖2 * π * I * ⟪m 0, η⟫ * (∂^{Fin.tail m} T).localFourier (ψ η) η -
          (∂^{Fin.tail m} T).localFourier (∂_{m 0} (ψ η)) η‖
        ≤ (1 + ‖η‖) ^ j * (‖(2 * π * I * ⟪m 0, η⟫ : ℂ)‖ *
            ‖(∂^{Fin.tail m} T).localFourier (ψ η) η‖ +
              ‖(∂^{Fin.tail m} T).localFourier (∂_{m 0} (ψ η)) η‖) := by
          gcongr
          exact (norm_sub_le _ _).trans_eq (by rw [norm_mul])
      _ ≤ (1 + ‖η‖) ^ j * (2 * π * ‖m 0‖ * (1 + ‖η‖) *
            ‖(∂^{Fin.tail m} T).localFourier (ψ η) η‖ +
              ‖(∂^{Fin.tail m} T).localFourier (∂_{m 0} (ψ η)) η‖) := by
          gcongr
          exact norm_two_pi_I_inner_le _ _
      _ = 2 * π * ‖m 0‖ * (1 + ‖η‖) *
            ((1 + ‖η‖) ^ j * ‖(∂^{Fin.tail m} T).localFourier (ψ η) η‖) +
              (1 + ‖η‖) ^ j * ‖(∂^{Fin.tail m} T).localFourier (∂_{m 0} (ψ η)) η‖ := by ring
      _ ≤ 2 * π * ‖m 0‖ * (1 + ‖η‖) * (C₁ * (1 + ‖η‖) ^ (k + r)) +
            |C₂| * (1 + ‖η‖) ^ (k + r + 1) :=
          add_le_add (mul_le_mul_of_nonneg_left (hC₁ η hη) (by positivity)) <|
            (hC₂ η hη).trans <| mul_le_mul (le_abs_self _)
              (pow_le_pow_right₀ hw (Nat.le_succ _)) (by positivity) (abs_nonneg _)
      _ = (2 * π * ‖m 0‖ * C₁ + |C₂|) * (1 + ‖η‖) ^ (k + (r + 1)) := by ring

/-- **The symbol of an iterated derivative.** Under the hypothesis of
`exists_localFourier_iteratedLineDerivOp_le`, the localized Fourier transform of `∂^m T` is its
symbol `∏ₗ 2πi ⟪m l, η⟫` times that of `T`, up to an error decaying one order faster than the
bound on `∂^m T`. -/
private theorem exists_localFourier_iteratedLineDerivOp_sub_le {T : 𝓓'(Ω, ℂ)} {K Γ : Set E}
    {j k : ℕ} (hT : ∀ ψ : E → 𝓓(Ω, ℂ), IsBddFamily K Γ ψ →
      ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ j * ‖T.localFourier (ψ η) η‖ ≤ C * (1 + ‖η‖) ^ k)
    {r : ℕ} (m : Fin r → E) (ψ : E → 𝓓(Ω, ℂ)) (hψ : IsBddFamily K Γ ψ) :
    ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ (j + 1) * ‖(∂^{m} T).localFourier (ψ η) η -
      (∏ l, (2 * π * I * ⟪m l, η⟫ : ℂ)) * T.localFourier (ψ η) η‖ ≤ C * (1 + ‖η‖) ^ (k + r) := by
  induction r generalizing ψ with
  | zero => exact ⟨0, fun η _ ↦ by simp⟩
  | succ r ih =>
    obtain ⟨C₁, hC₁⟩ := ih (Fin.tail m) ψ hψ
    obtain ⟨C₂, hC₂⟩ := exists_localFourier_iteratedLineDerivOp_le hT (Fin.tail m)
      (fun η ↦ ∂_{m 0} (ψ η)) (hψ.lineDerivOp _)
    refine ⟨2 * π * ‖m 0‖ * C₁ + C₂, fun η hη ↦ ?_⟩
    set a : ℂ := 2 * π * I * ⟪m 0, η⟫
    set D := (∂^{Fin.tail m} T).localFourier (ψ η) η -
      (∏ l, (2 * π * I * ⟪Fin.tail m l, η⟫ : ℂ)) * T.localFourier (ψ η) η
    set B := (∂^{Fin.tail m} T).localFourier (∂_{m 0} (ψ η)) η
    have hid : (∂^{m} T).localFourier (ψ η) η -
        (∏ l, (2 * π * I * ⟪m l, η⟫ : ℂ)) * T.localFourier (ψ η) η = a * D - B := by
      rw [iteratedLineDerivOp_succ_left, localFourier_lineDerivOp, Fin.prod_univ_succ]
      simp only [a, D, B, Fin.tail]
      ring
    rw [hid]
    calc (1 + ‖η‖) ^ (j + 1) * ‖a * D - B‖ ≤ (1 + ‖η‖) ^ (j + 1) * (‖a‖ * ‖D‖ + ‖B‖) := by
          gcongr
          exact (norm_sub_le _ _).trans_eq (by rw [norm_mul])
      _ ≤ (1 + ‖η‖) ^ (j + 1) * (2 * π * ‖m 0‖ * (1 + ‖η‖) * ‖D‖ + ‖B‖) := by
          gcongr
          exact norm_two_pi_I_inner_le _ _
      _ = 2 * π * ‖m 0‖ * (1 + ‖η‖) * ((1 + ‖η‖) ^ (j + 1) * ‖D‖) +
            (1 + ‖η‖) * ((1 + ‖η‖) ^ j * ‖B‖) := by ring
      _ ≤ 2 * π * ‖m 0‖ * (1 + ‖η‖) * (C₁ * (1 + ‖η‖) ^ (k + r)) +
            (1 + ‖η‖) * (C₂ * (1 + ‖η‖) ^ (k + r)) :=
          add_le_add (mul_le_mul_of_nonneg_left (hC₁ η hη) (by positivity))
            (mul_le_mul_of_nonneg_left (hC₂ η hη) (by positivity))
      _ = (2 * π * ‖m 0‖ * C₁ + C₂) * (1 + ‖η‖) ^ (k + (r + 1)) := by ring


/-- **Division by a nonvanishing smooth function of the frequency direction.** Let `σ (x, w)` be
smooth and nonzero for `x ∈ U` and `w ∈ V`, and let `d η` take values in a compact subset of `V`.
Every bounded family `ψ η` supported in a compact subset `K` of `U` is `σ (·, d η)` times a bounded
family `θ η`. -/
private theorem exists_isBddFamily_mul_eq [FiniteDimensional ℝ E] {σ : E → E → ℂ}
    (hσ : ContDiff ℝ ∞ fun p : E × E ↦ σ p.1 p.2) {U V S : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hS : IsCompact S) (hSV : S ⊆ V) (hσ0 : ∀ x ∈ U, ∀ w ∈ V, σ x w ≠ 0) {K Γ : Set E}
    (hK : IsCompact K) (hKU : K ⊆ U) {d : E → E} (hd : ∀ η, d η ∈ S) {ψ : E → 𝓓(Ω, ℂ)}
    (hψ : IsBddFamily K Γ ψ) :
    ∃ θ : E → 𝓓(Ω, ℂ), IsBddFamily K Γ θ ∧ ∀ η x, σ x (d η) * θ η x = ψ η x := by
  obtain ⟨χ, hχ, -, hχ1, hχc, hχU⟩ := hK.exists_contDiff_cutoff hU hKU
  -- `H (x, w) = χ x / σ (x, w)` is smooth on `E × V`: near `x ∉ U` it vanishes identically.
  set H : E × E → ℂ := fun p ↦ (χ p.1 : ℂ) * (σ p.1 p.2)⁻¹
  have hH : ContDiffOn ℝ ∞ H (univ ×ˢ V) := fun p hp ↦ by
    refine ContDiffAt.contDiffWithinAt ?_
    by_cases hp1 : p.1 ∈ U
    · exact (ofRealCLM.contDiff.comp (hχ.comp contDiff_fst)).contDiffAt.mul
        (hσ.contDiffAt.inv (hσ0 _ hp1 _ hp.2))
    · refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
        ((isClosed_tsupport χ).isOpen_compl.mem_nhds fun h ↦ hp1 (hχU h))] with q hq
      simp [H, image_eq_zero_of_notMem_tsupport hq]
  have hHx (w : E) (hw : w ∈ V) : ContDiff ℝ ∞ fun x ↦ H (x, w) :=
    hH.comp_contDiff (contDiff_id.prodMk contDiff_const) fun x ↦ ⟨mem_univ _, hw⟩
  -- The derivatives of `H (·, w)` are bounded uniformly for `w ∈ S`.
  have hG (n : ℕ) : ∃ G, ∀ w ∈ S, ∀ x, ‖iteratedFDeriv ℝ n (fun x ↦ H (x, w)) x‖ ≤ G := by
    obtain ⟨G, hG⟩ := (hχc.isCompact.prod hS).exists_bound_of_continuousOn
      ((hH.continuousOn_iteratedFDeriv_partial (isOpen_univ.prod hV) (k := n) (by simp)).mono
        (prod_mono (subset_univ _) hSV))
    refine ⟨max G 0, fun w hw x ↦ ?_⟩
    by_cases hx : x ∈ tsupport χ
    · exact (hG (x, w) ⟨hx, hw⟩).trans (le_max_left _ _)
    · have hsupp : tsupport (fun x ↦ H (x, w)) ⊆ tsupport χ := by
        refine closure_minimal (fun y hy ↦ subset_tsupport _ ?_) (isClosed_tsupport χ)
        exact fun h ↦ hy (by simp [H, h])
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hsupp (tsupport_iteratedFDeriv_subset n h)),
        norm_zero]
      exact le_max_right _ _
  choose G hG using hG
  choose B hB using hψ.2
  refine ⟨fun η ↦ bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (hHx (d η) (hSV (hd η))) (ψ η),
    ⟨fun η ↦ ?_, fun n ↦ ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |B i| * |G (n - i)|,
      fun η hη x ↦ ?_⟩⟩, fun η x ↦ ?_⟩
  · rw [bilinLeftCLM_apply]
    exact (tsupport_mul_subset_left (f := ψ η)).trans (hψ.1 η)
  · rw [bilinLeftCLM_apply]
    refine (norm_iteratedFDeriv_mul_le (ψ η).contDiff (hHx (d η) (hSV (hd η))) x (by simp)).trans
      (Finset.sum_le_sum fun i _ ↦ ?_)
    gcongr
    · exact (hB i η hη x).trans (le_abs_self _)
    · exact (hG _ (d η) (hd η) x).trans (le_abs_self _)
  · rw [bilinLeftCLM_apply]
    by_cases hψx : ψ η x = 0
    · simp [hψx]
    · have hxK : x ∈ K := hψ.1 η (subset_tsupport _ hψx)
      have hχx : χ x = 1 := interior_subset (hχ1 hxK)
      have hσx := hσ0 x (hKU hxK) (d η) (hSV (hd η))
      simp only [H, hχx, ContinuousLinearMap.mul_apply', ofReal_one, one_mul]
      field_simp

section SmoothCoeff

variable {ι : Type*} {s : Finset ι} {c : ι → ℂ} {a : ι → E → ℝ} (ha : ∀ i, ContDiff ℝ ∞ (a i))
  {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ}

include ha in
/-- **The symbol identity.** If `θ` is `‖η‖ ^ M ψ` divided by the principal symbol `σ_M(P)(·, η)`,
moving the derivatives of `P` onto the cutoff writes `(2πi) ^ M ‖η‖ ^ M L(T, ψ)(η)` as
`L(P T, θ)(η)` minus the errors `D_i` of `exists_localFourier_iteratedLineDerivOp_sub_le` and the
terms of order less than `M`. -/
private theorem localFourier_eq_of_smoothCoeffPrincipalSymbol_mul_eq (T : 𝓓'(Ω, ℂ))
    {θ ψ : 𝓓(Ω, ℂ)} {η : E}
    (h : ∀ x, smoothCoeffPrincipalSymbol s c a m M x η * θ x = (‖η‖ ^ M : ℝ) * ψ x) :
    (2 * π * I) ^ M * (‖η‖ ^ M : ℝ) * T.localFourier ψ η =
      (∑ i ∈ s, c i • smulLeftCLM (ha i) (∂^{m i} T)).localFourier θ η -
        ∑ i ∈ s, c i * ((∂^{m i} T).localFourier (TestFunction.smulLeftCLM (ha i) θ) η -
          (∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) *
            T.localFourier (TestFunction.smulLeftCLM (ha i) θ) η) -
        ∑ i ∈ s with k i ≠ M, c i * (∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) *
          T.localFourier (TestFunction.smulLeftCLM (ha i) θ) η := by
  -- `‖η‖ ^ M ψ` is the sum over the terms of order `M` of `c i ∏ₗ ⟪m i l, η⟫ a i θ`.
  have hcut : ((‖η‖ ^ M : ℝ) : ℂ) • ψ = ∑ i ∈ s with k i = M,
      (c i * ∏ l, (⟪m i l, η⟫ : ℂ)) • TestFunction.smulLeftCLM (ha i) θ := by
    ext x
    have hx := h x
    rw [smoothCoeffPrincipalSymbol, Finset.sum_mul] at hx
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, FunLike.coe_sum, Finset.sum_apply,
      TestFunction.smulLeftCLM_apply, Complex.real_smul, ← hx]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  -- Each term of `L(P T, θ)(η)` is `c i L(∂^(m i) T, a i θ)(η)`.
  have hterm (i : ι) : (c i • smulLeftCLM (ha i) (∂^{m i} T)).localFourier θ η -
      c i * ((∂^{m i} T).localFourier (TestFunction.smulLeftCLM (ha i) θ) η -
        (∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) *
          T.localFourier (TestFunction.smulLeftCLM (ha i) θ) η) =
      c i * (∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) *
        T.localFourier (TestFunction.smulLeftCLM (ha i) θ) η := by
    rw [localFourier_smul, localFourier_smulLeftCLM]
    ring
  rw [mul_assoc, ← localFourier_smul_cutoff, hcut, localFourier_sum_cutoff, Finset.mul_sum,
    localFourier_sum, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun i _ ↦ hterm i,
    ← Finset.sum_filter_add_sum_filter_not s (fun i ↦ k i = M), add_sub_cancel_right]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hpow : (2 * π * I : ℂ) ^ k i = (2 * π * I) ^ M := by rw [(Finset.mem_filter.1 hi).2]
  rw [localFourier_smul_cutoff, prod_two_pi_I_inner, hpow]
  ring

include ha in
/-- The norm form of `localFourier_eq_of_smoothCoeffPrincipalSymbol_mul_eq`, by the triangle
inequality. -/
private theorem norm_localFourier_le_of_smoothCoeffPrincipalSymbol_mul_eq (T : 𝓓'(Ω, ℂ))
    {θ ψ : 𝓓(Ω, ℂ)} {η : E}
    (h : ∀ x, smoothCoeffPrincipalSymbol s c a m M x η * θ x = (‖η‖ ^ M : ℝ) * ψ x) :
    (2 * π) ^ M * ‖η‖ ^ M * ‖T.localFourier ψ η‖ ≤
      ‖(∑ i ∈ s, c i • smulLeftCLM (ha i) (∂^{m i} T)).localFourier θ η‖ +
        ∑ i ∈ s, ‖c i‖ * ‖(∂^{m i} T).localFourier (TestFunction.smulLeftCLM (ha i) θ) η -
          (∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) *
            T.localFourier (TestFunction.smulLeftCLM (ha i) θ) η‖ +
        ∑ i ∈ s with k i ≠ M, ‖c i‖ * ‖∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)‖ *
          ‖T.localFourier (TestFunction.smulLeftCLM (ha i) θ) η‖ := by
  have hid := congrArg norm (localFourier_eq_of_smoothCoeffPrincipalSymbol_mul_eq ha T h)
  have h2π : ‖(2 * π * I : ℂ) ^ M * ((‖η‖ ^ M : ℝ) : ℂ)‖ = (2 * π) ^ M * ‖η‖ ^ M := by
    simp [abs_of_pos pi_pos]
  rw [norm_mul, h2π] at hid
  rw [hid]
  refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
    (add_le_add le_rfl ?_)) ?_)
  · exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
  · exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])

include ha in
/-- **The symbol estimate.** Suppose that the localized Fourier transforms of `T` with the cutoffs
of bounded families are `O((1 + ‖η‖) ^ k₀ / (1 + ‖η‖) ^ j)` on `Γ`, and let `θ` be a bounded family
with `σ_M(P)(·, η) θ η = ‖η‖ ^ M ψ η` for `η ∈ Γ`, such that `L(P T, θ η)(η)` is
`O((1 + ‖η‖) ^ -(j + 1))`. Then `‖η‖ ^ M L(T, ψ η)(η)` is
`O((1 + ‖η‖) ^ (k₀ + M) / (1 + ‖η‖) ^ (j + 1))` on `Γ`. -/
private theorem exists_norm_pow_mul_localFourier_le (hk : ∀ i ∈ s, k i ≤ M) {T : 𝓓'(Ω, ℂ)}
    {K Γ : Set E} (hK : IsCompact K) {j k₀ : ℕ} (hT : ∀ ψ : E → 𝓓(Ω, ℂ), IsBddFamily K Γ ψ →
      ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ j * ‖T.localFourier (ψ η) η‖ ≤ C * (1 + ‖η‖) ^ k₀)
    {θ ψ : E → 𝓓(Ω, ℂ)} (hθ : IsBddFamily K Γ θ)
    (hdiv : ∀ η ∈ Γ, ∀ x, smoothCoeffPrincipalSymbol s c a m M x η * θ η x =
      (‖η‖ ^ M : ℝ) * ψ η x) {Cp : ℝ} (hCp : ∀ η ∈ Γ, (1 + ‖η‖) ^ (j + 1) *
        ‖(∑ i ∈ s, c i • smulLeftCLM (ha i) (∂^{m i} T)).localFourier (θ η) η‖ ≤ Cp) :
    ∃ S, ∀ η ∈ Γ, (1 + ‖η‖) ^ (j + 1) * (‖η‖ ^ M * ‖T.localFourier (ψ η) η‖) ≤
      S * (1 + ‖η‖) ^ (k₀ + M) := by
  have hφ (i : ι) := hθ.smulLeftCLM hK (ha i)
  choose Cd hCd using fun i ↦ exists_localFourier_iteratedLineDerivOp_sub_le hT (m i) _ (hφ i)
  choose Cl hCl using fun i ↦ hT _ (hφ i)
  set A : ℝ := |Cp| + ∑ i ∈ s, ‖c i‖ * |Cd i| +
    ∑ i ∈ s with k i ≠ M, ‖c i‖ * (∏ l, 2 * π * ‖m i l‖) * |Cl i|
  refine ⟨A / (2 * π) ^ M, fun η hη ↦ ?_⟩
  have hw : 1 ≤ 1 + ‖η‖ := le_add_of_nonneg_right (norm_nonneg η)
  have hwM : 1 ≤ (1 + ‖η‖) ^ (k₀ + M) := one_le_pow₀ hw
  -- Each of the three terms is `O((1 + ‖η‖) ^ (k₀ + M) / (1 + ‖η‖) ^ (j + 1))`.
  have h1 : (1 + ‖η‖) ^ (j + 1) *
      ‖(∑ i ∈ s, c i • smulLeftCLM (ha i) (∂^{m i} T)).localFourier (θ η) η‖ ≤
        |Cp| * (1 + ‖η‖) ^ (k₀ + M) :=
    (hCp η hη).trans ((le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hwM))
  have h2 (i : ι) (hi : i ∈ s) : (1 + ‖η‖) ^ (j + 1) * (‖c i‖ *
      ‖(∂^{m i} T).localFourier (TestFunction.smulLeftCLM (ha i) (θ η)) η -
        (∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) *
          T.localFourier (TestFunction.smulLeftCLM (ha i) (θ η)) η‖) ≤
      ‖c i‖ * |Cd i| * (1 + ‖η‖) ^ (k₀ + M) := by
    have hD := (hCd i η hη).trans (mul_le_mul (le_abs_self _)
      (pow_le_pow_right₀ hw (Nat.add_le_add_left (hk i hi) k₀)) (by positivity) (abs_nonneg _))
    calc _ = ‖c i‖ * ((1 + ‖η‖) ^ (j + 1) *
            ‖(∂^{m i} T).localFourier (TestFunction.smulLeftCLM (ha i) (θ η)) η -
              (∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) *
                T.localFourier (TestFunction.smulLeftCLM (ha i) (θ η)) η‖) := by ring
      _ ≤ ‖c i‖ * (|Cd i| * (1 + ‖η‖) ^ (k₀ + M)) := by gcongr
      _ = _ := by ring
  have h3 (i : ι) (hi : i ∈ {i ∈ s | k i ≠ M}) := pow_mul_norm_prod_mul_le (r := k i) (M := M)
    (by have := hk i (Finset.mem_filter.1 hi).1; have := (Finset.mem_filter.1 hi).2; omega)
    (m i) η (c i) _ (hCl i η hη)
  have hmain : (2 * π) ^ M * ((1 + ‖η‖) ^ (j + 1) * (‖η‖ ^ M * ‖T.localFourier (ψ η) η‖)) ≤
      A * (1 + ‖η‖) ^ (k₀ + M) := by
    calc (2 * π) ^ M * ((1 + ‖η‖) ^ (j + 1) * (‖η‖ ^ M * ‖T.localFourier (ψ η) η‖))
        = (1 + ‖η‖) ^ (j + 1) * ((2 * π) ^ M * ‖η‖ ^ M * ‖T.localFourier (ψ η) η‖) := by ring
      _ ≤ (1 + ‖η‖) ^ (j + 1) *
          (‖(∑ i ∈ s, c i • smulLeftCLM (ha i) (∂^{m i} T)).localFourier (θ η) η‖ +
            ∑ i ∈ s, ‖c i‖ *
              ‖(∂^{m i} T).localFourier (TestFunction.smulLeftCLM (ha i) (θ η)) η -
                (∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) *
                  T.localFourier (TestFunction.smulLeftCLM (ha i) (θ η)) η‖ +
            ∑ i ∈ s with k i ≠ M, ‖c i‖ * ‖∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)‖ *
              ‖T.localFourier (TestFunction.smulLeftCLM (ha i) (θ η)) η‖) := by
          gcongr
          exact norm_localFourier_le_of_smoothCoeffPrincipalSymbol_mul_eq ha T (hdiv η hη)
      _ ≤ A * (1 + ‖η‖) ^ (k₀ + M) := by
          rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, add_mul, add_mul, Finset.sum_mul,
            Finset.sum_mul]
          exact add_le_add (add_le_add h1 (Finset.sum_le_sum h2)) (Finset.sum_le_sum h3)
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

include ha in
/-- **One step of the regularity induction.** Suppose that `P T` has rapidly decreasing localized
Fourier transforms on `Γ` with the cutoffs of every bounded family supported in `K`, and that every
such family `ψ` is `σ_M(P)(·, η) / ‖η‖ ^ M` times another one on `Γ`. If the localized Fourier
transforms of `T` with these cutoffs are `O((1 + ‖η‖) ^ k₀ / (1 + ‖η‖) ^ j)` on `Γ`, then they are
`O((1 + ‖η‖) ^ k₀ / (1 + ‖η‖) ^ (j + 1))`. -/
private theorem exists_localFourier_le_succ_of_smoothCoeff (hk : ∀ i ∈ s, k i ≤ M)
    {T : 𝓓'(Ω, ℂ)} {K Γ : Set E} (hK : IsCompact K)
    (hP : ∀ ψ : E → 𝓓(Ω, ℂ), IsBddFamily K Γ ψ → ∀ N : ℕ, ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ N *
      ‖(∑ i ∈ s, c i • smulLeftCLM (ha i) (∂^{m i} T)).localFourier (ψ η) η‖ ≤ C)
    (hdiv : ∀ ψ : E → 𝓓(Ω, ℂ), IsBddFamily K Γ ψ → ∃ θ : E → 𝓓(Ω, ℂ), IsBddFamily K Γ θ ∧
      ∀ η ∈ Γ, ∀ x, smoothCoeffPrincipalSymbol s c a m M x η * θ η x = (‖η‖ ^ M : ℝ) * ψ η x)
    {j k₀ : ℕ} (hT : ∀ ψ : E → 𝓓(Ω, ℂ), IsBddFamily K Γ ψ →
      ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ j * ‖T.localFourier (ψ η) η‖ ≤ C * (1 + ‖η‖) ^ k₀)
    (ψ : E → 𝓓(Ω, ℂ)) (hψ : IsBddFamily K Γ ψ) :
    ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ (j + 1) * ‖T.localFourier (ψ η) η‖ ≤ C * (1 + ‖η‖) ^ k₀ := by
  obtain ⟨θ, hθ, hθψ⟩ := hdiv ψ hψ
  obtain ⟨Cp, hCp⟩ := hP θ hθ (j + 1)
  obtain ⟨S, hS⟩ := exists_norm_pow_mul_localFourier_le ha hk hK hT hθ hθψ hCp
  obtain ⟨C₀, hC₀⟩ := hT ψ hψ
  refine ⟨max (2 * C₀) (2 ^ M * S), fun η hη ↦ ?_⟩
  rcases lt_or_ge ‖η‖ 1 with h1 | h1
  · -- At bounded frequencies the extra factor `1 + ‖η‖` is at most `2`.
    calc (1 + ‖η‖) ^ (j + 1) * ‖T.localFourier (ψ η) η‖
        = (1 + ‖η‖) * ((1 + ‖η‖) ^ j * ‖T.localFourier (ψ η) η‖) := by ring
      _ ≤ 2 * (C₀ * (1 + ‖η‖) ^ k₀) :=
          mul_le_mul (by linarith) (hC₀ η hη) (by positivity) (by norm_num)
      _ ≤ max (2 * C₀) (2 ^ M * S) * (1 + ‖η‖) ^ k₀ := by
          rw [← mul_assoc]
          gcongr
          exact le_max_left _ _
  · -- At large frequencies divide by `‖η‖ ^ M ≥ (1 + ‖η‖) ^ M / 2 ^ M`.
    have hpos : 0 < ‖η‖ ^ M := pow_pos (by linarith) M
    have hle : (1 + ‖η‖) ^ M ≤ 2 ^ M * ‖η‖ ^ M := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) M
    have hSη := hS η hη
    have hS0 : 0 ≤ S := by
      by_contra hneg
      have h0 : 0 ≤ (1 + ‖η‖) ^ (j + 1) * (‖η‖ ^ M * ‖T.localFourier (ψ η) η‖) := by positivity
      nlinarith [pow_pos (by positivity : (0 : ℝ) < 1 + ‖η‖) (k₀ + M)]
    have key : ‖η‖ ^ M * ((1 + ‖η‖) ^ (j + 1) * ‖T.localFourier (ψ η) η‖) ≤
        ‖η‖ ^ M * (2 ^ M * S * (1 + ‖η‖) ^ k₀) := by
      calc _ = (1 + ‖η‖) ^ (j + 1) * (‖η‖ ^ M * ‖T.localFourier (ψ η) η‖) := by ring
        _ ≤ S * (1 + ‖η‖) ^ (k₀ + M) := hSη
        _ = S * (1 + ‖η‖) ^ k₀ * (1 + ‖η‖) ^ M := by ring
        _ ≤ S * (1 + ‖η‖) ^ k₀ * (2 ^ M * ‖η‖ ^ M) := by gcongr
        _ = _ := by ring
    refine (le_of_mul_le_mul_left key hpos).trans ?_
    gcongr
    exact le_max_right _ _

include ha in
/-- The case of order `0` of `exists_nhds_cone_isBddFamily_mul_eq`: the principal symbol does not
depend on the frequency, and the cone is the whole space. -/
private theorem exists_nhds_isBddFamily_mul_eq_of_eq_zero [FiniteDimensional ℝ E] {x ξ : E}
    (hξ : smoothCoeffPrincipalSymbol s c a m 0 x ξ ≠ 0) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∀ K : Set E, IsCompact K → K ⊆ U →
      ∀ Γ' : Set E, ∀ ψ : E → 𝓓(Ω, ℂ), IsBddFamily K Γ' ψ → ∃ θ : E → 𝓓(Ω, ℂ),
        IsBddFamily K Γ' θ ∧ ∀ η ∈ Γ', ∀ y,
          smoothCoeffPrincipalSymbol s c a m 0 y η * θ η y = (‖η‖ ^ 0 : ℝ) * ψ η y := by
  have hσ := contDiff_smoothCoeffPrincipalSymbol (s := s) (c := c) (m := m) (M := 0) ha
  have hσ0 : Continuous fun y ↦ smoothCoeffPrincipalSymbol s c a m 0 y 0 := by
    have hac (i : ι) : Continuous (a i) := (ha i).continuous
    unfold smoothCoeffPrincipalSymbol
    fun_prop
  have hconst (y η : E) :
      smoothCoeffPrincipalSymbol s c a m 0 y η = smoothCoeffPrincipalSymbol s c a m 0 y 0 := by
    simpa using (smoothCoeffPrincipalSymbol_smul s c a m 0 y 0 η).symm
  have hU : IsOpen {y | smoothCoeffPrincipalSymbol s c a m 0 y 0 ≠ 0} :=
    isOpen_ne_fun hσ0 continuous_const
  refine ⟨_, hU, by simpa [← hconst x ξ] using hξ, fun K hK hKU Γ' ψ hψ ↦ ?_⟩
  obtain ⟨θ, hθ, hθψ⟩ := exists_isBddFamily_mul_eq hσ hU isOpen_univ isCompact_singleton
    (subset_univ {0}) (fun y hy w _ ↦ by rwa [hconst]) hK hKU (d := fun _ ↦ 0)
    (fun _ ↦ mem_singleton 0) hψ
  exact ⟨θ, hθ, fun η _ y ↦ by simpa [hconst y η] using hθψ η y⟩

include ha in
/-- **Division by the principal symbol near a noncharacteristic point.** If `σ_M(P)(x, ξ) ≠ 0`,
there are an open neighbourhood `U` of `x` and an open cone `Γ` containing `ξ` such that every
bounded family `ψ` supported in a compact subset of `U` is `σ_M(P)(·, η) / ‖η‖ ^ M` times a
bounded family, on every subset of `Γ`. -/
private theorem exists_nhds_cone_isBddFamily_mul_eq [FiniteDimensional ℝ E] {x ξ : E}
    (hξ : smoothCoeffPrincipalSymbol s c a m M x ξ ≠ 0) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧
      (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧ ∀ K : Set E, IsCompact K → K ⊆ U →
        ∀ Γ' ⊆ Γ, ∀ ψ : E → 𝓓(Ω, ℂ), IsBddFamily K Γ' ψ → ∃ θ : E → 𝓓(Ω, ℂ),
          IsBddFamily K Γ' θ ∧ ∀ η ∈ Γ', ∀ y,
            smoothCoeffPrincipalSymbol s c a m M y η * θ η y = (‖η‖ ^ M : ℝ) * ψ η y := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    obtain ⟨U, hU, hxU, hdiv⟩ := exists_nhds_isBddFamily_mul_eq_of_eq_zero (Ω := Ω) ha hξ
    exact ⟨U, hU, hxU, univ, isOpen_univ, mem_univ ξ, fun _ _ _ _ ↦ mem_univ _,
      fun K hK hKU Γ' _ ↦ hdiv K hK hKU Γ'⟩
  have hσ := contDiff_smoothCoeffPrincipalSymbol (s := s) (c := c) (m := m) (M := M) ha
  -- In positive order `ξ ≠ 0`, and the principal symbol is homogeneous: work with directions.
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    exact hξ (by simpa [hM.ne'] using smoothCoeffPrincipalSymbol_smul s c a m M x 0 0)
  have hσw₀ : smoothCoeffPrincipalSymbol s c a m M x (‖ξ‖⁻¹ • ξ) ≠ 0 := by
    rw [smoothCoeffPrincipalSymbol_smul]
    exact mul_ne_zero (pow_ne_zero _ (by simpa using hξ0)) hξ
  have hO : IsOpen {p : E × E | smoothCoeffPrincipalSymbol s c a m M p.1 p.2 ≠ 0} :=
    isOpen_ne_fun hσ.continuous continuous_const
  obtain ⟨u, v, hu, hv, hxu, hw₀v, huv⟩ := isOpen_prod_iff.1 hO x (‖ξ‖⁻¹ • ξ) hσw₀
  obtain ⟨δ, hδ, hδv⟩ := Metric.isOpen_iff.1 hv _ hw₀v
  -- The cone of the frequencies whose direction lies within `δ / 2` of that of `ξ`.
  set Γ : Set E := {η | η ≠ 0 ∧ ‖η‖⁻¹ • η ∈ Metric.ball (‖ξ‖⁻¹ • ξ) (δ / 2)}
  have hΓ : IsOpen Γ :=
    ((continuous_norm.continuousOn.inv₀ fun η hη ↦ norm_ne_zero_iff.2 hη).smul continuousOn_id
      ).isOpen_inter_preimage isOpen_ne Metric.isOpen_ball
  have hdir {η : E} (hη : η ≠ 0) (y : E) : smoothCoeffPrincipalSymbol s c a m M y η =
      (‖η‖ : ℂ) ^ M * smoothCoeffPrincipalSymbol s c a m M y (‖η‖⁻¹ • η) := by
    rw [← smoothCoeffPrincipalSymbol_smul, smul_inv_smul₀ (norm_ne_zero_iff.2 hη)]
  classical
  refine ⟨u, hu, hxu, Γ, hΓ, ⟨hξ0, Metric.mem_ball_self (half_pos hδ)⟩,
    fun t ht η hη ↦ ⟨smul_ne_zero ht.ne' hη.1, ?_⟩, fun K hK hKU Γ' hΓ' ψ hψ ↦ ?_⟩
  · rw [mem_ofPred_eq, norm_smul, Real.norm_of_nonneg ht.le, smul_smul, mul_inv_rev, mul_assoc,
      inv_mul_cancel₀ ht.ne', mul_one]
    exact hη.2
  obtain ⟨θ, hθ, hθψ⟩ := exists_isBddFamily_mul_eq (σ := smoothCoeffPrincipalSymbol s c a m M)
    hσ hu hv (isCompact_closedBall _ (δ / 2))
    ((Metric.closedBall_subset_ball (half_lt_self hδ)).trans hδv)
    (fun y hy w hw ↦ by simpa using huv (mk_mem_prod hy hw)) hK hKU
    (d := fun η ↦ if η ∈ Γ then ‖η‖⁻¹ • η else ‖ξ‖⁻¹ • ξ) (fun η ↦ by
      split_ifs with h
      · exact Metric.ball_subset_closedBall h.2
      · exact Metric.mem_closedBall_self (half_pos hδ).le) hψ
  refine ⟨θ, hθ, fun η hη y ↦ ?_⟩
  have h := hθψ η y
  simp only [hΓ' hη, ↓reduceIte] at h
  rw [hdir (hΓ' hη).1, mul_assoc, h, ofReal_pow]

variable [FiniteDimensional ℝ E]

/-- **Microlocal elliptic regularity for operators with smooth coefficients** (Hörmander I,
Theorem 8.3.1). Let `P = ∑ i ∈ s, c i a i ∂^(m i)` have smooth coefficients `a i` and orders
`k i ≤ M`, and let `(x, ξ)` be noncharacteristic for `P`: the principal symbol
`smoothCoeffPrincipalSymbol s c a m M` does not vanish at `(x, ξ)`. If `P T` is microlocally smooth
at `(x, ξ)`, then so is `T`. -/
theorem IsMicrolocallySmoothAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp
    (hk : ∀ i ∈ s, k i ≤ M) {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (hP : (∑ i ∈ s, c i • Distribution.smulLeftCLM (ha i) (∂^{m i} T)).IsMicrolocallySmoothAt x ξ)
    (hξ : smoothCoeffPrincipalSymbol s c a m M x ξ ≠ 0) :
    T.IsMicrolocallySmoothAt x ξ := by
  -- `P T` decays on `Γ₁` uniformly over bounded families supported near `x`, and these families
  -- can be divided by the principal symbol on `Γ₂`.
  obtain ⟨U₁, hU₁, hxU₁, hU₁Ω, Γ₁, hΓ₁, hξ₁, hcone₁, hdecay⟩ :=
    hP.exists_nhds_cone_of_forall_norm_iteratedFDeriv_le
  obtain ⟨U₂, hU₂, hxU₂, Γ₂, hΓ₂, hξ₂, hcone₂, hdiv⟩ :=
    exists_nhds_cone_isBddFamily_mul_eq (Ω := Ω) ha hξ
  obtain ⟨K, hKx, hKsub, hKc⟩ := local_compact_nhds ((hU₁.inter hU₂).mem_nhds ⟨hxU₁, hxU₂⟩)
  have hKΩ : K ⊆ Ω := hKsub.trans (inter_subset_left.trans hU₁Ω)
  obtain ⟨k₀, hk₀⟩ := exists_forall_norm_localFourier_le_of_forall_norm_iteratedFDeriv_le T hKc hKΩ
  -- By induction on `j`, every bounded family supported in `K` has localized Fourier transforms
  -- `O((1 + ‖η‖) ^ k₀ / (1 + ‖η‖) ^ j)` on `Γ₁ ∩ Γ₂`.
  have hind (j : ℕ) : ∀ ψ : E → 𝓓(Ω, ℂ), IsBddFamily K (Γ₁ ∩ Γ₂) ψ → ∃ C, ∀ η ∈ Γ₁ ∩ Γ₂,
      (1 + ‖η‖) ^ j * ‖T.localFourier (ψ η) η‖ ≤ C * (1 + ‖η‖) ^ k₀ := by
    induction j with
    | zero =>
      intro ψ hψ
      obtain ⟨C, hC⟩ := hk₀ (Γ₁ ∩ Γ₂) ψ hψ.1 hψ.2
      exact ⟨C, fun η hη ↦ by simpa using hC η hη η⟩
    | succ j ih =>
      refine exists_localFourier_le_succ_of_smoothCoeff ha hk hKc (fun ψ hψ N ↦ ?_)
        (hdiv K hKc (hKsub.trans inter_subset_right) _ inter_subset_right) ih
      obtain ⟨C, hC⟩ := hdecay K hKc (hKsub.trans inter_subset_left) _ ψ hψ.1 hψ.2 N
      exact ⟨C, fun η hη ↦ hC η hη η hη.1⟩
  obtain ⟨φ, hφK, hφx⟩ := exists_tsupport_subset_apply_eq (n := ⊤) hKx hKΩ (1 : ℂ)
  refine isMicrolocallySmoothAt_iff.2 ⟨φ, by simp [hφx], Γ₁ ∩ Γ₂, hΓ₁.inter hΓ₂, ⟨hξ₁, hξ₂⟩,
    fun t ht η hη ↦ ⟨hcone₁ t ht η hη.1, hcone₂ t ht η hη.2⟩, fun N ↦ ?_⟩
  obtain ⟨C, hC⟩ := hind (k₀ + N) _ (isBddFamily_const hφK)
  refine ⟨C, fun η hη ↦ le_of_mul_le_mul_left ?_ (by positivity : 0 < (1 + ‖η‖) ^ k₀)⟩
  calc (1 + ‖η‖) ^ k₀ * ((1 + ‖η‖) ^ N * ‖T.localFourier φ η‖)
      = (1 + ‖η‖) ^ (k₀ + N) * ‖T.localFourier φ η‖ := by ring
    _ ≤ C * (1 + ‖η‖) ^ k₀ := hC η hη
    _ = (1 + ‖η‖) ^ k₀ * C := mul_comm _ _

include ha in
/-- **Microlocal elliptic regularity for operators with smooth coefficients**:
`WF(T) ⊆ WF(P T) ∪ Char(P)` for `P = ∑ i ∈ s, c i a i ∂^(m i)` with smooth coefficients `a i`
and orders `k i ≤ M`, where `Char(P) = smoothCoeffCharacteristicSet s c a m M` is the set of
`(x, ξ)` with `ξ ≠ 0` at which the principal symbol vanishes. -/
theorem waveFrontSet_subset_waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_union
    (hk : ∀ i ∈ s, k i ≤ M) (T : 𝓓'(Ω, ℂ)) :
    T.waveFrontSet ⊆ (∑ i ∈ s, c i • smulLeftCLM (ha i) (∂^{m i} T)).waveFrontSet ∪
      smoothCoeffCharacteristicSet s c a m M := by
  rintro ⟨x, ξ⟩ hp
  obtain ⟨hx, hξ, hT⟩ := mem_waveFrontSet_iff.1 hp
  by_contra h
  rw [mem_union, not_or, mem_waveFrontSet_iff, mem_smoothCoeffCharacteristicSet_iff] at h
  exact hT (IsMicrolocallySmoothAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp ha hk
    (by simpa [hx, hξ] using h.1) fun h0 ↦ h.2 ⟨hξ, h0⟩)

include ha in
/-- **An elliptic operator with smooth coefficients preserves the wave front set.** If the
principal symbol of `P = ∑ i ∈ s, c i a i ∂^(m i)` of order `M` vanishes at no `(x, ξ)` with
`x ∈ Ω` and `ξ ≠ 0`, then `WF(P T) = WF(T)`. -/
theorem waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_forall_ne_zero
    (hk : ∀ i ∈ s, k i ≤ M)
    (hσ : ∀ x ∈ Ω, ∀ ξ : E, ξ ≠ 0 → smoothCoeffPrincipalSymbol s c a m M x ξ ≠ 0)
    (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ s, c i • smulLeftCLM (ha i) (∂^{m i} T)).waveFrontSet = T.waveFrontSet := by
  refine subset_antisymm (waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset s c ha m T)
    fun p hp ↦ ?_
  refine (waveFrontSet_subset_waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_union ha hk T
    hp).resolve_right ?_
  exact fun h ↦ hσ p.1 (mem_waveFrontSet_iff.1 hp).1 p.2 h.1 h.2

include ha in
/-- **Elliptic regularity for operators with smooth coefficients.** If the principal symbol of
`P = ∑ i ∈ s, c i a i ∂^(m i)` of order `M` vanishes at no `(x, ξ)` with `x ∈ Ω` and `ξ ≠ 0`, then
`P T` and `T` have the same singular support: `T` is a smooth function near every point near which
`P T` is. -/
theorem singularSupport_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_forall_ne_zero
    [MeasurableSpace E] [BorelSpace E] (hk : ∀ i ∈ s, k i ≤ M)
    (hσ : ∀ x ∈ Ω, ∀ ξ : E, ξ ≠ 0 → smoothCoeffPrincipalSymbol s c a m M x ξ ≠ 0)
    (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ s, c i • smulLeftCLM (ha i) (∂^{m i} T)).singularSupport = T.singularSupport := by
  rw [← fst_image_waveFrontSet, ← fst_image_waveFrontSet,
    waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_of_forall_ne_zero ha hk hσ]

end SmoothCoeff

/-! ### Constant coefficients -/

variable [FiniteDimensional ℝ E]

/-- **Microlocal elliptic regularity for constant-coefficient operators** (Hörmander I,
Theorem 8.3.1). Let `P = ∑ i ∈ s, c i ∂^(m i)` have orders `k i ≤ M`, and let `ξ` be
noncharacteristic for `P`: the principal symbol `constCoeffPrincipalSymbol s c m M` does not
vanish at `ξ`. If `P T` is microlocally smooth at `(x, ξ)`, then so is `T`. This is the case of
constant coefficients `a i = 1` of
`Distribution.IsMicrolocallySmoothAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp`. -/
theorem IsMicrolocallySmoothAt.of_sum_smul_iteratedLineDerivOp {ι : Type*} {s : Finset ι}
    {c : ι → ℂ} {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ} (hk : ∀ i ∈ s, k i ≤ M)
    {T : 𝓓'(Ω, ℂ)} {x ξ : E} (hP : (∑ i ∈ s, c i • ∂^{m i} T).IsMicrolocallySmoothAt x ξ)
    (hξ : constCoeffPrincipalSymbol s c m M ξ ≠ 0) :
    T.IsMicrolocallySmoothAt x ξ :=
  of_sum_smul_smulLeftCLM_iteratedLineDerivOp (a := fun _ _ ↦ 1) (fun _ ↦ contDiff_const) hk
    (by simpa using hP) (by simpa using hξ)

/-- **Microlocal elliptic regularity for constant-coefficient operators**:
`WF(T) ⊆ WF(P T) ∪ Char(P)` for `P = ∑ i ∈ s, c i ∂^(m i)` with orders `k i ≤ M`, where
`Char(P) = constCoeffCharacteristicSet s c m M` is the set of `(x, ξ)` with `ξ ≠ 0` at which the
principal symbol vanishes. -/
theorem waveFrontSet_subset_waveFrontSet_sum_smul_iteratedLineDerivOp_union {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) {M : ℕ} (hk : ∀ i ∈ s, k i ≤ M)
    (T : 𝓓'(Ω, ℂ)) :
    T.waveFrontSet ⊆ (∑ i ∈ s, c i • ∂^{m i} T).waveFrontSet ∪
      constCoeffCharacteristicSet s c m M := by
  rintro ⟨x, ξ⟩ hp
  obtain ⟨hx, hξ, hT⟩ := mem_waveFrontSet_iff.1 hp
  by_contra h
  rw [mem_union, not_or, mem_waveFrontSet_iff, mem_constCoeffCharacteristicSet_iff] at h
  exact hT (IsMicrolocallySmoothAt.of_sum_smul_iteratedLineDerivOp hk
    (by simpa [hx, hξ] using h.1) fun h0 ↦ h.2 ⟨hξ, h0⟩)

/-- **An elliptic constant-coefficient operator preserves the wave front set.** If the principal
symbol of `P = ∑ i ∈ s, c i ∂^(m i)` of order `M` vanishes at no `ξ ≠ 0`, then
`WF(P T) = WF(T)`. -/
theorem waveFrontSet_sum_smul_iteratedLineDerivOp_of_forall_ne_zero {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) {M : ℕ} (hk : ∀ i ∈ s, k i ≤ M)
    (hσ : ∀ ξ : E, ξ ≠ 0 → constCoeffPrincipalSymbol s c m M ξ ≠ 0)
    (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ s, c i • ∂^{m i} T).waveFrontSet = T.waveFrontSet := by
  refine subset_antisymm (waveFrontSet_sum_smul_iteratedLineDerivOp_subset s c m T)
    fun p hp ↦ ?_
  refine (waveFrontSet_subset_waveFrontSet_sum_smul_iteratedLineDerivOp_union s c m hk T
    hp).resolve_right ?_
  exact fun h ↦ hσ p.2 h.1 h.2

/-- **Elliptic regularity for constant-coefficient operators.** If the principal symbol of
`P = ∑ i ∈ s, c i ∂^(m i)` of order `M` vanishes at no `ξ ≠ 0`, then `P T` and `T` have the same
singular support: `T` is a smooth function near every point near which `P T` is. -/
theorem singularSupport_sum_smul_iteratedLineDerivOp_of_forall_ne_zero [MeasurableSpace E]
    [BorelSpace E] {ι : Type*} (s : Finset ι) (c : ι → ℂ) {k : ι → ℕ} (m : ∀ i, Fin (k i) → E)
    {M : ℕ} (hk : ∀ i ∈ s, k i ≤ M)
    (hσ : ∀ ξ : E, ξ ≠ 0 → constCoeffPrincipalSymbol s c m M ξ ≠ 0)
    (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ s, c i • ∂^{m i} T).singularSupport = T.singularSupport := by
  rw [← fst_image_waveFrontSet, ← fst_image_waveFrontSet,
    waveFrontSet_sum_smul_iteratedLineDerivOp_of_forall_ne_zero s c m hk hσ]

/-- **The Laplacian preserves the wave front set.** The Laplacian
`Δ = LineDeriv.laplacianCLM ℝ E 𝓓'(Ω, ℂ)`, which is `∑ i, ∂_{b i} ∂_{b i}` for any orthonormal
basis `b`, satisfies `WF(Δ T) = WF(T)`: its principal symbol `∑ i, ⟪b i, ξ⟫ ^ 2 = ‖ξ‖ ^ 2`
vanishes only at `ξ = 0`. -/
@[simp]
theorem waveFrontSet_laplacianCLM (T : 𝓓'(Ω, ℂ)) :
    (laplacianCLM ℝ E 𝓓'(Ω, ℂ) T).waveFrontSet = T.waveFrontSet := by
  set b := stdOrthonormalBasis ℝ E
  have h := waveFrontSet_sum_smul_iteratedLineDerivOp_of_forall_ne_zero Finset.univ (fun _ ↦ 1)
    (k := fun _ ↦ 2) (fun i ↦ ![b i, b i]) (M := 2) (fun _ _ ↦ le_rfl) (fun ξ hξ ↦ ?_) T
  · simpa [laplacianCLM_eq_sum b, iteratedLineDerivOp_succ_left, iteratedLineDerivOp_one, Fin.tail]
      using h
  have hsum : ∑ i, ⟪b i, ξ⟫ * ⟪b i, ξ⟫ = ‖ξ‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner ξ ξ]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm]
  have hval : constCoeffPrincipalSymbol Finset.univ (fun _ ↦ 1) (fun i ↦ ![b i, b i]) 2 ξ =
      ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hsum]
    simp [constCoeffPrincipalSymbol, Fin.prod_univ_two]
  rw [hval]
  exact_mod_cast (pow_pos (norm_pos_iff.2 hξ) 2).ne'

/-- **Elliptic regularity for the Laplacian.** `Δ T` and `T` have the same singular support. -/
@[simp]
theorem singularSupport_laplacianCLM [MeasurableSpace E] [BorelSpace E] (T : 𝓓'(Ω, ℂ)) :
    (laplacianCLM ℝ E 𝓓'(Ω, ℂ) T).singularSupport = T.singularSupport := by
  rw [← fst_image_waveFrontSet, ← fst_image_waveFrontSet, waveFrontSet_laplacianCLM]

end Distribution
