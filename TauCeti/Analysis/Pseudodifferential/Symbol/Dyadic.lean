/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.LittlewoodPaley
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic

/-!
# Littlewood–Paley decomposition of symbols

Let `φ` be a smooth bump function on `ℝⁿ` and `ψ₀ = φ, ψ₁, ψ₂, …` the inhomogeneous
Littlewood–Paley partition built from it (`ContDiffBump.inhomogeneousLittlewoodPaley`): `ψ₀` is
supported in a ball, each `ψⱼ` with `j ≥ 1` in the annulus `2^{j-1} φ.rIn ≤ ‖ξ‖ ≤ 2^j φ.rOut`,
and `∑ⱼ ψⱼ = 1`. Cutting a symbol `a(x, ξ)` of order `m` by this partition in the frequency gives
its **Littlewood–Paley pieces** `aⱼ(x, ξ) = ψⱼ(ξ) a(x, ξ)`. This is the frequency decomposition
behind the `L²` boundedness of operators with symbols of order zero (Calderón–Vaillancourt): each
piece is frequency-localized at scale `2^j`, and its estimates are uniform in `j` after rescaling.

The derivatives of the cutoffs satisfy `‖D^k ψⱼ ξ‖ ≤ B 2^{-jk}`, and `⟨ξ⟩ ≤ C 2^j` on the
support of `ψⱼ`, so `‖D^k ψⱼ ξ‖ ⟨ξ⟩ ^ k` is bounded independently of `j`: the cutoffs form a
bounded family of symbols of order zero
(`ContDiffBump.exists_norm_iteratedFDeriv_inhomogeneousLittlewoodPaley_mul_le`). The Leibniz rule
(`TauCeti.norm_mixedDeriv_comp_snd_smul_le`) then gives symbol estimates for the pieces with
constants independent of `j`.

## Main declarations

* `TauCeti.Symbol.littlewoodPaleyPiece φ a j`: the piece `ψⱼ(ξ) a(x, ξ)`, a symbol of order `m`.
* `TauCeti.Symbol.hasSum_coefficient_littlewoodPaleyPiece`: the pieces sum to `a` pointwise, with
  finitely many nonzero terms at each point.
* `TauCeti.Symbol.isSmoothing_littlewoodPaleyPiece`: each piece is smoothing; it vanishes for
  `‖ξ‖ ≥ 2^j φ.rOut` and, for `j ≥ 1`, for `‖ξ‖ ≤ 2^{j-1} φ.rIn`.
* `TauCeti.Symbol.exists_norm_mixedDeriv_littlewoodPaleyPiece_le` and
  `TauCeti.Symbol.IsUniform.exists_norm_mixedDeriv_littlewoodPaleyPiece_le`: the pieces form a
  bounded family of symbols of order `m`, uniform in the position when `a` is.
* `TauCeti.Symbol.IsUniform.exists_norm_mixedDeriv_littlewoodPaleyPiece_le_two_pow`: the dyadic
  estimates `‖∂ₓ^α ∂_ξ^β aⱼ(x, ξ)‖ ≤ C (2^j) ^ (m - |β|)` for a uniform symbol.
* `TauCeti.Symbol.IsUniform.exists_integral_norm_mixedDeriv_littlewoodPaleyPiece_le`: the
  integrated estimates `∫ ‖∂ₓ^α ∂_ξ^β aⱼ(x, ξ)‖ dξ ≤ C (2^j) ^ (m - |β| + n)`. For `m = 0` they
  read `∫ ‖∂_ξ^β aⱼ(x, ξ)‖ dξ ≤ A R ^ |β|` with `A = C 2^{jn}` and `R = 2^{-j}`, the
  scale-invariant form in which they control the kernels of the pieces.

`ContDiffBump.littlewoodPaleyPiece` is the analogous decomposition of a Fourier multiplier
satisfying Mihlin's condition, with the homogeneous partition of `ℝⁿ \ {0}`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §3.
* E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993, Chapter VII, §2.
-/

public noncomputable section

open Set Filter Metric MeasureTheory
open scoped ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ} (φ : ContDiffBump (0 : CoordinateSpace n))

/-! ### The cutoffs -/

/-- `⟨ξ⟩ ^ k ≤ (1 + ‖ξ‖) ^ k`. -/
private theorem rpow_weight_natCast_le (ξ : CoordinateSpace n) (k : ℕ) :
    (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) ≤ (1 + ‖ξ‖) ^ k := by
  rw [div_eq_mul_inv, mul_comm, Real.rpow_mul (by positivity), Real.rpow_natCast]
  gcongr
  rw [← one_div, ← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
  exact ⟨by positivity, by nlinarith [norm_nonneg ξ]⟩

/-- The derivatives of the Littlewood–Paley cutoffs satisfy the order-zero symbol estimates
uniformly in the scale: `‖D^k ψⱼ ξ‖ ⟨ξ⟩ ^ k ≤ B` with `B` independent of `j`. -/
private theorem exists_norm_iteratedFDeriv_mul_rpow_weight_le (k : ℕ) :
    ∃ B, 0 ≤ B ∧ ∀ (j : ℕ) (ξ : CoordinateSpace n),
      ‖iteratedFDeriv ℝ k (φ.inhomogeneousLittlewoodPaley j) ξ‖ *
        (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) ≤ B := by
  obtain ⟨B, hB0, hB⟩ := φ.exists_norm_iteratedFDeriv_inhomogeneousLittlewoodPaley_mul_le k
  exact ⟨B, hB0, fun j ξ => (mul_le_mul_of_nonneg_left (rpow_weight_natCast_le ξ k)
    (norm_nonneg _)).trans (hB j ξ)⟩

/-! ### The Leibniz bound -/

/-- The constant in `norm_mixedDeriv_littlewoodPaley_smul_le`. -/
private def leibnizConst (B : ℕ → ℝ) (D : List (Fin n) → ℝ) (β : List (Fin n)) : ℝ :=
  ∑ i ∈ Finset.range (β.length + 1), (β.length.choose i : ℝ) * B i *
    ∑ w : Fin (β.length - i) → Fin n, D (List.ofFn w)

private theorem leibnizConst_nonneg {B : ℕ → ℝ} (hB : ∀ k, 0 ≤ B k) {D : List (Fin n) → ℝ}
    (hD : ∀ w, 0 ≤ D w) (β : List (Fin n)) : 0 ≤ leibnizConst B D β :=
  Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hB i))
    (Finset.sum_nonneg fun w _ => hD _)

/-- **Symbol estimates for the pieces.** Let `B k` bound `‖D^k ψⱼ ξ‖ ⟨ξ⟩ ^ k` for all scales `j`.
If the mixed derivatives `∂ₓ^α ∂_ξ^w a` at `(x, ξ)` are bounded by `D w ⟨ξ⟩ ^ (m - |w|)`, then
`∂ₓ^α ∂_ξ^β (ψⱼ(ξ) a(x, ξ))` is bounded by `leibnizConst B D β * ⟨ξ⟩ ^ (m - |β|)`, a constant
independent of `j`. -/
private theorem norm_mixedDeriv_littlewoodPaley_smul_le {B : ℕ → ℝ}
    (hB : ∀ k j (ξ : CoordinateSpace n), ‖iteratedFDeriv ℝ k (φ.inhomogeneousLittlewoodPaley j) ξ‖ *
      (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) ≤ B k)
    {a : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W} (ha : ContDiff ℝ ∞ a)
    {α : List (Fin n)} {x ξ : CoordinateSpace n} {D : List (Fin n) → ℝ} (hD0 : ∀ w, 0 ≤ D w)
    (hD : ∀ w, ‖mixedDeriv α w a x ξ‖ ≤ D w * (1 + ‖ξ‖ ^ 2) ^ ((m - w.length) / 2))
    (β : List (Fin n)) (j : ℕ) :
    ‖mixedDeriv α β (fun p => φ.inhomogeneousLittlewoodPaley j p.2 • a p) x ξ‖ ≤
      leibnizConst B D β * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  refine (norm_mixedDeriv_comp_snd_smul_le (φ.contDiff_inhomogeneousLittlewoodPaley j) ha α β x
    ξ).trans ?_
  rw [leibnizConst, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ β.length := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  -- `⟨ξ⟩ ^ (m - (|β| - i)) = ⟨ξ⟩ ^ i * ⟨ξ⟩ ^ (m - |β|)`
  have hw (w : Fin (β.length - i) → Fin n) :
      (1 + ‖ξ‖ ^ 2) ^ ((m - (List.ofFn w).length) / 2) =
        (1 + ‖ξ‖ ^ 2) ^ ((i : ℝ) / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
    rw [← Real.rpow_add (by positivity), List.length_ofFn, Nat.cast_sub hi']
    ring_nf
  have hsum : ∑ w : Fin (β.length - i) → Fin n, ‖mixedDeriv α (List.ofFn w) a x ξ‖ ≤
      (∑ w : Fin (β.length - i) → Fin n, D (List.ofFn w)) *
        ((1 + ‖ξ‖ ^ 2) ^ ((i : ℝ) / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun w _ => (hD _).trans_eq (by rw [hw])
  have hS : 0 ≤ ∑ w : Fin (β.length - i) → Fin n, D (List.ofFn w) :=
    Finset.sum_nonneg fun w _ => hD0 _
  calc (β.length.choose i : ℝ) * ‖iteratedFDeriv ℝ i (φ.inhomogeneousLittlewoodPaley j) ξ‖ *
        ∑ w : Fin (β.length - i) → Fin n, ‖mixedDeriv α (List.ofFn w) a x ξ‖
      ≤ (β.length.choose i : ℝ) * ‖iteratedFDeriv ℝ i (φ.inhomogeneousLittlewoodPaley j) ξ‖ *
        ((∑ w : Fin (β.length - i) → Fin n, D (List.ofFn w)) *
          ((1 + ‖ξ‖ ^ 2) ^ ((i : ℝ) / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2))) := by
        gcongr
    _ = (β.length.choose i : ℝ) * (‖iteratedFDeriv ℝ i (φ.inhomogeneousLittlewoodPaley j) ξ‖ *
          (1 + ‖ξ‖ ^ 2) ^ ((i : ℝ) / 2)) * (∑ w : Fin (β.length - i) → Fin n, D (List.ofFn w)) *
          (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by ring
    _ ≤ (β.length.choose i : ℝ) * B i * (∑ w : Fin (β.length - i) → Fin n, D (List.ofFn w)) *
          (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
        gcongr
        exact hB i j ξ

/-! ### The Littlewood–Paley pieces of a symbol -/

/-- The `j`-th **Littlewood–Paley piece** `ψⱼ(ξ) a(x, ξ)` of a symbol `a`, for the inhomogeneous
Littlewood–Paley partition `ψ₀ = φ, ψ₁, ψ₂, …` built from the bump function `φ`. It is a symbol of
the order of `a`, with estimates uniform in `j`
(`Symbol.exists_norm_mixedDeriv_littlewoodPaleyPiece_le`); it is smoothing
(`Symbol.isSmoothing_littlewoodPaleyPiece`), and the pieces sum to `a`
(`Symbol.hasSum_coefficient_littlewoodPaleyPiece`). -/
def littlewoodPaleyPiece (a : Symbol n V W m) (j : ℕ) : Symbol n V W m where
  coefficient p := φ.inhomogeneousLittlewoodPaley j p.2 • a.coefficient p
  contDiff_coefficient :=
    ((φ.contDiff_inhomogeneousLittlewoodPaley j).comp contDiff_snd).smul a.contDiff_coefficient
  exists_bound K hK α β := by
    choose B hB0 hB using exists_norm_iteratedFDeriv_mul_rpow_weight_le φ
    choose D hD0 hD using fun w => a.exists_bound K hK α w
    exact ⟨leibnizConst B D β, leibnizConst_nonneg hB0 hD0 β, fun x hx ξ =>
      norm_mixedDeriv_littlewoodPaley_smul_le φ hB a.contDiff_coefficient hD0
        (fun w => hD w x hx ξ) β j⟩

@[simp]
theorem coefficient_littlewoodPaleyPiece (a : Symbol n V W m) (j : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (a.littlewoodPaleyPiece φ j).coefficient p =
      φ.inhomogeneousLittlewoodPaley j p.2 • a.coefficient p :=
  (rfl)

/-- **The Littlewood–Paley decomposition of a symbol.** At every point the pieces sum to the
symbol, with only finitely many nonzero terms. -/
theorem hasSum_coefficient_littlewoodPaleyPiece (a : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    HasSum (fun j => (a.littlewoodPaleyPiece φ j).coefficient p) (a.coefficient p) := by
  simpa using (φ.hasSum_inhomogeneousLittlewoodPaley p.2).smul_const (a.coefficient p)

/-- The `j`-th piece vanishes at frequencies of norm at least `2^j φ.rOut`. -/
theorem coefficient_littlewoodPaleyPiece_eq_zero_of_le_norm (a : Symbol n V W m) {j : ℕ}
    (x : CoordinateSpace n) {ξ : CoordinateSpace n} (hξ : 2 ^ j * φ.rOut ≤ ‖ξ‖) :
    (a.littlewoodPaleyPiece φ j).coefficient (x, ξ) = 0 := by
  simp [φ.inhomogeneousLittlewoodPaley_eq_zero_of_le_norm hξ]

/-- The piece of index `j + 1` vanishes at frequencies of norm at most `2^j φ.rIn`. -/
theorem coefficient_littlewoodPaleyPiece_succ_eq_zero_of_norm_le (a : Symbol n V W m) {j : ℕ}
    (x : CoordinateSpace n) {ξ : CoordinateSpace n} (hξ : ‖ξ‖ ≤ 2 ^ j * φ.rIn) :
    (a.littlewoodPaleyPiece φ (j + 1)).coefficient (x, ξ) = 0 := by
  simp [φ.inhomogeneousLittlewoodPaley_succ_eq_zero_of_norm_le hξ]

/-- Each piece is smoothing, since its frequency support is bounded. -/
theorem isSmoothing_littlewoodPaleyPiece (a : Symbol n V W m) (j : ℕ) :
    (a.littlewoodPaleyPiece φ j).IsSmoothing :=
  isSmoothing_iff.2 fun _ => ⟨ofBoundedFrequencySupport _
    (a.littlewoodPaleyPiece φ j).contDiff_coefficient (2 ^ j * φ.rOut)
    fun x _ hξ => a.coefficient_littlewoodPaleyPiece_eq_zero_of_le_norm φ x hξ,
    coefficient_ofBoundedFrequencySupport _ _ _ _⟩

/-- Away from the support of `ψⱼ`, every mixed derivative of the `j`-th piece vanishes. -/
theorem mixedDeriv_littlewoodPaleyPiece_eq_zero_of_notMem_tsupport (a : Symbol n V W m) {j : ℕ}
    (α β : List (Fin n)) (x : CoordinateSpace n) {ξ : CoordinateSpace n}
    (hξ : ξ ∉ tsupport (φ.inhomogeneousLittlewoodPaley j)) :
    mixedDeriv α β (a.littlewoodPaleyPiece φ j).coefficient x ξ = 0 :=
  mixedDeriv_comp_snd_smul_eq_zero_of_notMem_tsupport (φ.contDiff_inhomogeneousLittlewoodPaley j)
    a.contDiff_coefficient α β x hξ

/-- **The pieces form a bounded family of symbols of order `m`.** On a compact set of positions,
the symbol estimates of the pieces hold with constants independent of `j`. -/
theorem exists_norm_mixedDeriv_littlewoodPaleyPiece_le (a : Symbol n V W m)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ (j : ℕ), ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (a.littlewoodPaleyPiece φ j).coefficient x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  choose B hB0 hB using exists_norm_iteratedFDeriv_mul_rpow_weight_le φ
  choose D hD0 hD using fun w => a.exists_bound K hK α w
  exact ⟨leibnizConst B D β, leibnizConst_nonneg hB0 hD0 β, fun j x hx ξ =>
    norm_mixedDeriv_littlewoodPaley_smul_le φ hB a.contDiff_coefficient hD0
      (fun w => hD w x hx ξ) β j⟩

/-- **The pieces of a uniform symbol form a bounded family of uniform symbols.** The symbol
estimates of the pieces hold with constants independent of both the position and `j`. -/
theorem IsUniform.exists_norm_mixedDeriv_littlewoodPaleyPiece_le {a : Symbol n V W m}
    (ha : a.IsUniform) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ (j : ℕ) x ξ,
      ‖mixedDeriv α β (a.littlewoodPaleyPiece φ j).coefficient x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  choose B hB0 hB using exists_norm_iteratedFDeriv_mul_rpow_weight_le φ
  choose D hD0 hD using fun w => isUniform_iff.1 ha α w
  exact ⟨leibnizConst B D β, leibnizConst_nonneg hB0 hD0 β, fun j x ξ =>
    norm_mixedDeriv_littlewoodPaley_smul_le φ hB a.contDiff_coefficient hD0
      (fun w => hD w x ξ) β j⟩

/-- The Littlewood–Paley pieces of a uniform symbol are uniform. -/
theorem IsUniform.littlewoodPaleyPiece {a : Symbol n V W m} (ha : a.IsUniform) (j : ℕ) :
    (a.littlewoodPaleyPiece φ j).IsUniform :=
  isUniform_iff.2 fun α β => by
    obtain ⟨C, hC0, hC⟩ := ha.exists_norm_mixedDeriv_littlewoodPaleyPiece_le φ α β
    exact ⟨C, hC0, hC j⟩

/-! ### Dyadic estimates -/

/-- On the support of `ψⱼ`, the weight `⟨ξ⟩` is comparable to `2^j`, so every power `⟨ξ⟩ ^ t` is
bounded by a constant times `(2^j) ^ t`. -/
private theorem exists_rpow_weight_le_two_pow (t : ℝ) :
    ∃ c, 0 ≤ c ∧ ∀ (j : ℕ) (ξ : CoordinateSpace n),
      ξ ∈ tsupport (φ.inhomogeneousLittlewoodPaley j) →
        (1 + ‖ξ‖ ^ 2) ^ (t / 2) ≤ c * ((2 : ℝ) ^ j) ^ t := by
  set c₁ := min 1 (φ.rIn / 2)
  set c₂ := 1 + φ.rOut
  have hc₁ : 0 < c₁ := lt_min one_pos (half_pos φ.rIn_pos)
  have hc₂ : 0 < c₂ := by linarith [φ.rOut_pos]
  refine ⟨max (c₁ ^ t) (c₂ ^ t), by positivity, fun j ξ hξ => ?_⟩
  set s := Real.sqrt (1 + ‖ξ‖ ^ 2)
  have hs : (1 + ‖ξ‖ ^ 2) ^ (t / 2) = s ^ t := by
    rw [show s = (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) from Real.sqrt_eq_rpow _,
      ← Real.rpow_mul (by positivity)]
    ring_nf
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  -- upper bound `s ≤ c₂ 2^j`
  have hupper : s ≤ c₂ * 2 ^ j := by
    have hξ' : ‖ξ‖ ≤ 2 ^ j * φ.rOut :=
      mem_closedBall_zero_iff.1 (φ.tsupport_inhomogeneousLittlewoodPaley_subset_closedBall j hξ)
    have h1 : s ≤ 1 + ‖ξ‖ := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [norm_nonneg ξ]⟩
    have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
    nlinarith
  -- lower bound `c₁ 2^j ≤ s`
  have hlower : c₁ * 2 ^ j ≤ s := by
    have hnorm : ‖ξ‖ ≤ s := (le_abs_self _).trans (Real.abs_le_sqrt (by linarith))
    have hone : 1 ≤ s := Real.one_le_sqrt.2 (by nlinarith [norm_nonneg ξ])
    rcases j with _ | j
    · simp only [pow_zero, mul_one]
      exact (min_le_left _ _).trans hone
    · have hξ' := (φ.tsupport_inhomogeneousLittlewoodPaley_succ_subset j hξ).1
      calc c₁ * 2 ^ (j + 1) ≤ φ.rIn / 2 * 2 ^ (j + 1) := by gcongr; exact min_le_right _ _
        _ = 2 ^ j * φ.rIn := by ring
        _ ≤ s := hξ'.trans hnorm
  rw [hs]
  rcases le_total 0 t with ht | ht
  · calc s ^ t ≤ (c₂ * 2 ^ j) ^ t := Real.rpow_le_rpow (by positivity) hupper ht
      _ = c₂ ^ t * ((2 : ℝ) ^ j) ^ t := Real.mul_rpow hc₂.le h2.le
      _ ≤ max (c₁ ^ t) (c₂ ^ t) * ((2 : ℝ) ^ j) ^ t := by gcongr; exact le_max_right _ _
  · calc s ^ t ≤ (c₁ * 2 ^ j) ^ t := Real.rpow_le_rpow_of_nonpos (by positivity) hlower ht
      _ = c₁ ^ t * ((2 : ℝ) ^ j) ^ t := Real.mul_rpow hc₁.le h2.le
      _ ≤ max (c₁ ^ t) (c₂ ^ t) * ((2 : ℝ) ^ j) ^ t := by gcongr; exact le_max_left _ _

/-- **Dyadic estimates.** For a uniform symbol of order `m`, the `j`-th piece and its mixed
derivatives satisfy `‖∂ₓ^α ∂_ξ^β aⱼ(x, ξ)‖ ≤ C (2^j) ^ (m - |β|)` uniformly in `x`, `ξ` and `j`:
each frequency derivative gains a factor `2^{-j}`. -/
theorem IsUniform.exists_norm_mixedDeriv_littlewoodPaleyPiece_le_two_pow {a : Symbol n V W m}
    (ha : a.IsUniform) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ (j : ℕ) x ξ,
      ‖mixedDeriv α β (a.littlewoodPaleyPiece φ j).coefficient x ξ‖ ≤
        C * ((2 : ℝ) ^ j) ^ (m - β.length) := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_mixedDeriv_littlewoodPaleyPiece_le φ α β
  obtain ⟨c, hc0, hc⟩ := exists_rpow_weight_le_two_pow φ (n := n) (m - β.length)
  refine ⟨C * c, by positivity, fun j x ξ => ?_⟩
  by_cases hξ : ξ ∈ tsupport (φ.inhomogeneousLittlewoodPaley j)
  · calc ‖mixedDeriv α β (a.littlewoodPaleyPiece φ j).coefficient x ξ‖
        ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := hC j x ξ
      _ ≤ C * (c * ((2 : ℝ) ^ j) ^ (m - β.length)) := by gcongr; exact hc j ξ hξ
      _ = C * c * ((2 : ℝ) ^ j) ^ (m - β.length) := by ring
  · rw [a.mixedDeriv_littlewoodPaleyPiece_eq_zero_of_notMem_tsupport φ α β x hξ, norm_zero]
    positivity

/-- **Integrated dyadic estimates.** For a uniform symbol of order `m` on `ℝⁿ`, the frequency
integrals of the mixed derivatives of the `j`-th piece satisfy
`∫ ‖∂ₓ^α ∂_ξ^β aⱼ(x, ξ)‖ dξ ≤ C (2^j) ^ (m - |β| + n)` uniformly in `x` and `j`: the piece is
supported in a ball of radius `2^j φ.rOut`, of volume proportional to `2^{jn}`. For `m = 0` these
are the bounds `∫ ‖∂_ξ^β aⱼ(x, ξ)‖ dξ ≤ A R ^ |β|` with `A = C 2^{jn}` and `R = 2^{-j}`. -/
theorem IsUniform.exists_integral_norm_mixedDeriv_littlewoodPaleyPiece_le {a : Symbol n V W m}
    (ha : a.IsUniform) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ (j : ℕ) x,
      ∫ ξ, ‖mixedDeriv α β (a.littlewoodPaleyPiece φ j).coefficient x ξ‖ ≤
        C * ((2 : ℝ) ^ j) ^ (m - β.length + n) := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_mixedDeriv_littlewoodPaleyPiece_le_two_pow φ α β
  set v := (volume : Measure (CoordinateSpace n)).real (ball 0 1)
  refine ⟨C * φ.rOut ^ n * v, by have := φ.rOut_pos; positivity, fun j x => ?_⟩
  set R := (2 : ℝ) ^ j * φ.rOut
  have hR : 0 ≤ R := by have := φ.rOut_pos; positivity
  -- the integrand is dominated by a constant on the ball of radius `2^j φ.rOut`
  have hle : ∀ ξ, ‖mixedDeriv α β (a.littlewoodPaleyPiece φ j).coefficient x ξ‖ ≤
      (closedBall (0 : CoordinateSpace n) R).indicator
        (fun _ => C * ((2 : ℝ) ^ j) ^ (m - β.length)) ξ := fun ξ => by
    by_cases hξ : ξ ∈ closedBall (0 : CoordinateSpace n) R
    · rw [indicator_of_mem hξ]
      exact hC j x ξ
    · rw [indicator_of_notMem hξ,
        a.mixedDeriv_littlewoodPaleyPiece_eq_zero_of_notMem_tsupport φ α β x
          fun h => hξ (φ.tsupport_inhomogeneousLittlewoodPaley_subset_closedBall j h), norm_zero]
  have hint : Integrable ((closedBall (0 : CoordinateSpace n) R).indicator
      fun _ => C * ((2 : ℝ) ^ j) ^ (m - β.length)) :=
    (integrableOn_const (measure_closedBall_lt_top (x := (0 : CoordinateSpace n))).ne
      ).integrable_indicator measurableSet_closedBall
  calc ∫ ξ, ‖mixedDeriv α β (a.littlewoodPaleyPiece φ j).coefficient x ξ‖
      ≤ ∫ ξ, (closedBall (0 : CoordinateSpace n) R).indicator
          (fun _ => C * ((2 : ℝ) ^ j) ^ (m - β.length)) ξ :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint
          (Eventually.of_forall hle)
    _ = R ^ n * v * (C * ((2 : ℝ) ^ j) ^ (m - β.length)) := by
        rw [integral_indicator_const _ measurableSet_closedBall,
          Measure.addHaar_real_closedBall _ _ hR, finrank_euclideanSpace_fin, smul_eq_mul]
    _ = C * φ.rOut ^ n * v * ((2 : ℝ) ^ j) ^ (m - β.length + n) := by
        rw [Real.rpow_add (by positivity), Real.rpow_natCast, mul_pow]
        ring

end Symbol

end TauCeti
