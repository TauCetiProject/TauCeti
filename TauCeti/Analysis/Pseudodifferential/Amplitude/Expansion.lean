/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Amplitude.LeftSymbol
public import TauCeti.Analysis.Pseudodifferential.AsymptoticSum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Fourier.Inversion
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# The asymptotic expansion of the left symbol of an amplitude

Let `a(x, y, ξ)` be an amplitude of order `m` with compact support in the input position `y`
(`TauCeti.Amplitude.HasCompactInputSupport`). Its left symbol `c = TauCeti.Amplitude.leftSymbol a`,
whose quantization is the quantization of `a`, has the asymptotic expansion

`c(x, ξ) ∼ ∑_α (1 / α!) ∂_ξ^α D_y^α a(x, y, ξ)|_{y = x}`, with `D_y = -i ∂_y`,

obtained by Taylor expanding `a` in the input position around the output position. This file
proves the expansion with an actual remainder symbol after every number of terms. The values of
`a` lie in `V →L[ℂ] W` with `W` complete, for the Fourier inversion identifying the leading term.

* `TauCeti.Amplitude.spatialDerivFst_comm`, `TauCeti.Amplitude.spatialDerivSnd_frequencyDeriv_comm`
  and their companions: the derivatives `∂_{x_j}`, `∂_{y_j}` and `∂_{ξ_j}` of an amplitude commute.
* `TauCeti.Amplitude.diag a`: the restriction `(x, ξ) ↦ a(x, x, ξ)` of an amplitude to the diagonal,
  a symbol of order `m`, with the derivative rules `TauCeti.Amplitude.spatialDeriv_diag`
  (`∂_{x_j}` of the restriction is the restriction of `∂_{x_j} a + ∂_{y_j} a`) and
  `TauCeti.Amplitude.frequencyDeriv_diag`.
* `TauCeti.Amplitude.leftSymbolTerm a k`: the term
  `((-i)^k / k!) ∑_{|w| = k} (∂_y^w ∂_ξ^w a)(x, x, ξ)` of order `m - k`, the sum running over the
  words `w` of coordinate indices of length `k` (`TauCeti.Amplitude.coefficient_leftSymbolTerm`).
  Grouping the words by the multi-index they determine gives the sum over `|α| = k` above. The
  leading term `leftSymbolTerm a 0` is `diag a`.
* `TauCeti.Amplitude.leftSymbolRemainder a ha N`: the remainder
  `leftSymbol a - ∑_{k < N} leftSymbolTerm a k`, a symbol of order `m - N`.
* `TauCeti.Amplitude.leftSymbol_eq_sum_leftSymbolTerm_add_leftSymbolRemainder`: **the expansion
  of the left symbol**, `leftSymbol a = ∑_{k < N} leftSymbolTerm a k + leftSymbolRemainder a ha N`
  for every `N`. In particular the left symbol is `a(x, x, ξ)` up to a symbol of order `m - 1`
  (`TauCeti.Amplitude.leftSymbol_eq_diag_add_leftSymbolRemainder_one`), and it is an asymptotic sum
  of the terms (`TauCeti.Amplitude.isAsymptoticSum_leftSymbol`), which determines it modulo
  smoothing symbols.

## Proof outline

Write `â(x, θ, ξ)` for the Fourier transform of the input slice `y ↦ a(x, y, ξ)`. For a real
parameter `t` consider

`A_t(x, ξ) = ∫ exp(2πi ⟪θ, x⟫) â(x, θ, ξ + 2πtθ) dθ`,

so that `A_1` is the left symbol by definition and `A_0(x, ξ) = a(x, x, ξ)` by Fourier inversion.
Since `(∂_{y_j} a)^(x, θ, ξ) = 2πi θⱼ â(x, θ, ξ)`, differentiating under the integral sign gives
`d/dt A_t(a) = -i ∑ⱼ A_t(∂_{y_j} ∂_{ξ_j} a)`. The terms satisfy the matching recursion
`leftSymbolTerm a (k + 1) = (-i / (k + 1)) ∑ⱼ leftSymbolTerm (∂_{y_j} ∂_{ξ_j} a) k`, so the
remainder `R_N(t) = A_t(a) - ∑_{k < N} t^k leftSymbolTerm a k` satisfies
`d/dt R_{N+1}(t)(a) = -i ∑ⱼ R_N(t)(∂_{y_j} ∂_{ξ_j} a)` and `R_{N+1}(0) = 0`. The mean value theorem
and induction on `N` bound `R_N(t)` by `C ⟨ξ⟩ ^ (m - N)` for `t ∈ [0, 1]` and output positions in a
compact set, starting from the rapid decay of `â(x, θ, ξ + 2πtθ)` in `θ` and Peetre's inequality.
The position and frequency derivatives of the remainder are the remainders of the derivatives of
`a`, a position derivative `∂_{x_j}` giving the sum of the remainders of `∂_{x_j} a` and
`∂_{y_j} a`, so the symbol estimates of order `m - N` follow by induction on the number of
derivatives. The argument follows the one for the adjoint symbol in
`TauCeti.Analysis.Pseudodifferential.Adjoint.Expansion`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (1.21)–(1.28).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.7.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Finset
open scoped ContDiff RealInnerProductSpace

namespace TauCeti

variable {n : ℕ}

namespace Amplitude

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-! ### Commuting the derivatives of an amplitude -/

section Comm

/-- Two directional derivatives of the coefficient of an amplitude commute. -/
private theorem iteratedFDerivAlong_singleton_comm (a : Amplitude n V W m)
    (d e : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    iteratedFDerivAlong ℝ [d] (iteratedFDerivAlong ℝ [e] a.coefficient) =
      iteratedFDerivAlong ℝ [e] (iteratedFDerivAlong ℝ [d] a.coefficient) := by
  rw [← iteratedFDerivAlong_append, ← iteratedFDerivAlong_append]
  exact iteratedFDerivAlong_swap a.contDiff_coefficient d e [] (by simp)

private theorem coefficient_spatialDerivFst_eq (j : Fin n) (a : Amplitude n V W m) :
    (spatialDerivFst j a).coefficient =
      iteratedFDerivAlong ℝ [(EuclideanSpace.single j 1, 0)] a.coefficient :=
  funext fun p ↦ by simp

private theorem coefficient_spatialDerivSnd_eq (j : Fin n) (a : Amplitude n V W m) :
    (spatialDerivSnd j a).coefficient =
      iteratedFDerivAlong ℝ [(0, EuclideanSpace.single j 1, 0)] a.coefficient :=
  funext fun p ↦ by simp

private theorem coefficient_frequencyDeriv_eq (j : Fin n) (a : Amplitude n V W m) :
    (frequencyDeriv j a).coefficient =
      iteratedFDerivAlong ℝ [(0, 0, EuclideanSpace.single j 1)] a.coefficient :=
  funext fun p ↦ by simp

/-- Two derivatives of an amplitude in the output position commute. -/
theorem spatialDerivFst_comm (j l : Fin n) (a : Amplitude n V W m) :
    spatialDerivFst j (spatialDerivFst l a) = spatialDerivFst l (spatialDerivFst j a) := by
  ext1
  simp only [coefficient_spatialDerivFst_eq]
  exact a.iteratedFDerivAlong_singleton_comm _ _

/-- Two derivatives of an amplitude in the input position commute. -/
theorem spatialDerivSnd_comm (j l : Fin n) (a : Amplitude n V W m) :
    spatialDerivSnd j (spatialDerivSnd l a) = spatialDerivSnd l (spatialDerivSnd j a) := by
  ext1
  simp only [coefficient_spatialDerivSnd_eq]
  exact a.iteratedFDerivAlong_singleton_comm _ _

/-- Two frequency derivatives of an amplitude commute. -/
theorem frequencyDeriv_comm (j l : Fin n) (a : Amplitude n V W m) :
    frequencyDeriv j (frequencyDeriv l a) = frequencyDeriv l (frequencyDeriv j a) := by
  ext1
  simp only [coefficient_frequencyDeriv_eq]
  exact a.iteratedFDerivAlong_singleton_comm _ _

/-- Derivatives of an amplitude in the output and in the input position commute. -/
theorem spatialDerivFst_spatialDerivSnd_comm (j l : Fin n) (a : Amplitude n V W m) :
    spatialDerivFst j (spatialDerivSnd l a) = spatialDerivSnd l (spatialDerivFst j a) := by
  ext1
  simp only [coefficient_spatialDerivFst_eq, coefficient_spatialDerivSnd_eq]
  exact a.iteratedFDerivAlong_singleton_comm _ _

/-- Derivatives of an amplitude in the output position and in the frequency commute. -/
theorem spatialDerivFst_frequencyDeriv_comm (j l : Fin n) (a : Amplitude n V W m) :
    spatialDerivFst j (frequencyDeriv l a) = frequencyDeriv l (spatialDerivFst j a) := by
  ext1
  simp only [coefficient_spatialDerivFst_eq, coefficient_frequencyDeriv_eq]
  exact a.iteratedFDerivAlong_singleton_comm _ _

/-- Derivatives of an amplitude in the input position and in the frequency commute. -/
theorem spatialDerivSnd_frequencyDeriv_comm (j l : Fin n) (a : Amplitude n V W m) :
    spatialDerivSnd j (frequencyDeriv l a) = frequencyDeriv l (spatialDerivSnd j a) := by
  ext1
  simp only [coefficient_spatialDerivSnd_eq, coefficient_frequencyDeriv_eq]
  exact a.iteratedFDerivAlong_singleton_comm _ _

private theorem spatialDerivFst_spatialDerivSnd_frequencyDeriv (l j : Fin n)
    (a : Amplitude n V W m) :
    spatialDerivFst l (spatialDerivSnd j (frequencyDeriv j a)) =
      spatialDerivSnd j (frequencyDeriv j (spatialDerivFst l a)) := by
  rw [spatialDerivFst_spatialDerivSnd_comm, spatialDerivFst_frequencyDeriv_comm]

private theorem spatialDerivSnd_spatialDerivSnd_frequencyDeriv (l j : Fin n)
    (a : Amplitude n V W m) :
    spatialDerivSnd l (spatialDerivSnd j (frequencyDeriv j a)) =
      spatialDerivSnd j (frequencyDeriv j (spatialDerivSnd l a)) := by
  rw [spatialDerivSnd_comm l j, spatialDerivSnd_frequencyDeriv_comm l j]

private theorem frequencyDeriv_spatialDerivSnd_frequencyDeriv (l j : Fin n)
    (a : Amplitude n V W m) :
    frequencyDeriv l (spatialDerivSnd j (frequencyDeriv j a)) =
      spatialDerivSnd j (frequencyDeriv j (frequencyDeriv l a)) := by
  rw [← spatialDerivSnd_frequencyDeriv_comm j l, frequencyDeriv_comm l j]

end Comm

/-! ### The restriction to the diagonal -/

section Diag

/-- The derivative of the restriction `x ↦ a(x, x, ξ)` in the position `x_j` is the restriction of
`∂_{x_j} a + ∂_{y_j} a`. -/
private theorem coordinateDeriv_diag_fst (a : Amplitude n V W m) (j : Fin n)
    (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun x ↦ a.coefficient (x, x, ξ)) x =
      (spatialDerivFst j a).coefficient (x, x, ξ) +
        (spatialDerivSnd j a).coefficient (x, x, ξ) := by
  have hφ : HasFDerivAt (fun x : CoordinateSpace n ↦ (x, x, ξ))
      ((ContinuousLinearMap.id ℝ (CoordinateSpace n)).prod
        ((ContinuousLinearMap.id ℝ (CoordinateSpace n)).prod 0)) x :=
    (hasFDerivAt_id x).prodMk ((hasFDerivAt_id x).prodMk (hasFDerivAt_const ξ x))
  have h := (a.contDiff_coefficient.differentiable (by simp) _).hasFDerivAt.comp x hφ
  simp only [Function.comp_def] at h
  rw [coordinateDeriv_cons, coordinateDeriv_nil, h.fderiv, coefficient_spatialDerivFst,
    coefficient_spatialDerivSnd, ContinuousLinearMap.comp_apply, ← map_add]
  exact congrArg _ (by ext <;> simp)

/-- The derivative of the restriction `ξ ↦ a(x, x, ξ)` in the frequency `ξ_j` is the restriction
of `∂_{ξ_j} a`. -/
private theorem coordinateDeriv_diag_snd (a : Amplitude n V W m) (j : Fin n)
    (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun ξ ↦ a.coefficient (x, x, ξ)) ξ =
      (frequencyDeriv j a).coefficient (x, x, ξ) := by
  have hφ : HasFDerivAt (fun ξ : CoordinateSpace n ↦ (x, x, ξ))
      ((ContinuousLinearMap.inr ℝ (CoordinateSpace n) _).comp
        (ContinuousLinearMap.inr ℝ (CoordinateSpace n) (CoordinateSpace n))) ξ :=
    (hasFDerivAt_prodMk_right x (x, ξ)).comp ξ (hasFDerivAt_prodMk_right x ξ)
  have h := (a.contDiff_coefficient.differentiable (by simp) _).hasFDerivAt.comp ξ hφ
  simp only [Function.comp_def] at h
  rw [coordinateDeriv_cons, coordinateDeriv_nil, h.fderiv, coefficient_frequencyDeriv]
  rfl

/-- Frequency derivatives of the restriction to the diagonal along a word `β` are the restriction
of an amplitude of order `m - |β|`. -/
private theorem exists_coordinateDeriv_diag_snd :
    ∀ (β : List (Fin n)) {m : ℝ} (a : Amplitude n V W m),
      ∃ (m' : ℝ) (b : Amplitude n V W m'), m' = m - β.length ∧
        ∀ x, coordinateDeriv β (fun ξ ↦ a.coefficient (x, x, ξ)) =
          fun ξ ↦ b.coefficient (x, x, ξ)
  | [], m, a => ⟨m, a, by simp, fun _ ↦ coordinateDeriv_nil _⟩
  | j :: js, m, a => by
    obtain ⟨m', b, hm', hab⟩ := exists_coordinateDeriv_diag_snd js a
    refine ⟨m' - 1, frequencyDeriv j b, by rw [hm']; simp; ring, fun x ↦ ?_⟩
    rw [← List.singleton_append, coordinateDeriv_append, hab x]
    funext ξ
    exact b.coordinateDeriv_diag_snd j x ξ

/-- Position derivatives of the restriction to the diagonal grow at most like `⟨ξ⟩ ^ m`,
uniformly for positions in a compact set. -/
private theorem exists_norm_coordinateDeriv_diag_le (α : List (Fin n)) :
    ∀ {m : ℝ} (a : Amplitude n V W m) {K : Set (CoordinateSpace n)}, IsCompact K →
      ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
        ‖coordinateDeriv α (fun x ↦ a.coefficient (x, x, ξ)) x‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  induction α using List.reverseRecOn with
  | nil =>
    intro m a K hK
    obtain ⟨C, hC0, hC⟩ := a.exists_bound ((fun x ↦ (x, x)) '' K) (hK.image (by fun_prop)) [] [] []
    refine ⟨C, hC0, fun x hx ξ ↦ ?_⟩
    simpa [amplitudeDirections_def] using hC x x ⟨x, hx, rfl⟩ ξ
  | append_singleton js j ih =>
    intro m a K hK
    obtain ⟨C₁, hC₁0, hC₁⟩ := ih (spatialDerivFst j a) hK
    obtain ⟨C₂, hC₂0, hC₂⟩ := ih (spatialDerivSnd j a) hK
    refine ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun x hx ξ ↦ ?_⟩
    have hs : ∀ {s : ℝ} (b : Amplitude n V W s),
        ContDiff ℝ js.length fun x ↦ b.coefficient (x, x, ξ) := fun b ↦
      (b.contDiff_coefficient.comp (by fun_prop)).of_le (by exact_mod_cast le_top)
    have hsplit : coordinateDeriv [j] (fun x ↦ a.coefficient (x, x, ξ)) =
        (fun x ↦ (spatialDerivFst j a).coefficient (x, x, ξ)) +
          fun x ↦ (spatialDerivSnd j a).coefficient (x, x, ξ) :=
      funext fun x ↦ a.coordinateDeriv_diag_fst j x ξ
    rw [coordinateDeriv_append, hsplit,
      coordinateDeriv_add js (hs (spatialDerivFst j a)) (hs (spatialDerivSnd j a)),
      Pi.add_apply, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hC₁ x hx ξ) (hC₂ x hx ξ))

/-- The **restriction of an amplitude to the diagonal** `y = x`: the symbol
`(x, ξ) ↦ a(x, x, ξ)` of order `m`. It is the leading term of the left symbol of an amplitude
with compact input support (`TauCeti.Amplitude.leftSymbol_eq_diag_add_leftSymbolRemainder_one`). -/
def diag (a : Amplitude n V W m) : Symbol n V W m where
  coefficient p := a.coefficient (p.1, p.1, p.2)
  contDiff_coefficient := a.contDiff_coefficient.comp (by fun_prop)
  exists_bound K hK α β := by
    obtain ⟨m', b, hm', hab⟩ := exists_coordinateDeriv_diag_snd β a
    obtain ⟨C, hC0, hC⟩ := exists_norm_coordinateDeriv_diag_le α b hK
    refine ⟨C, hC0, fun x hx ξ ↦ ?_⟩
    rw [mixedDeriv_def]
    simp_rw [hab]
    rw [← hm']
    exact hC x hx ξ

@[simp]
theorem coefficient_diag (a : Amplitude n V W m) (x ξ : CoordinateSpace n) :
    a.diag.coefficient (x, ξ) = a.coefficient (x, x, ξ) :=
  (rfl)

/-- Position derivatives of the restriction to the diagonal: `∂_{x_j}` of `a(x, x, ξ)` is the
restriction of `∂_{x_j} a + ∂_{y_j} a`. -/
theorem spatialDeriv_diag (j : Fin n) (a : Amplitude n V W m) :
    Symbol.spatialDeriv j a.diag = (spatialDerivFst j a).diag + (spatialDerivSnd j a).diag := by
  ext1
  funext ⟨x, ξ⟩
  rw [Symbol.coefficient_spatialDeriv, Symbol.coefficient_add, Pi.add_apply]
  exact a.coordinateDeriv_diag_fst j x ξ

/-- Frequency derivatives of the restriction to the diagonal: `∂_{ξ_j}` of `a(x, x, ξ)` is the
restriction of `∂_{ξ_j} a`. -/
theorem frequencyDeriv_diag (j : Fin n) (a : Amplitude n V W m) :
    Symbol.frequencyDeriv j a.diag = (frequencyDeriv j a).diag := by
  ext1
  funext ⟨x, ξ⟩
  rw [Symbol.coefficient_frequencyDeriv]
  exact a.coordinateDeriv_diag_snd j x ξ

end Diag

/-! ### The terms of the expansion -/

section Term

/-- The term of order `m - k` in the asymptotic expansion of the left symbol of an amplitude:
`((-i)^k / k!) ∑_{|w| = k} (∂_y^w ∂_ξ^w a)(x, x, ξ)`, the sum running over the words `w` of
coordinate indices of length `k` (`coefficient_leftSymbolTerm`). It is defined by the recursion
`leftSymbolTerm a (k + 1) = (-i / (k + 1)) ∑ⱼ leftSymbolTerm (∂_{yⱼ} ∂_{ξⱼ} a) k`, starting from
the restriction to the diagonal `leftSymbolTerm a 0 = diag a`. -/
def leftSymbolTerm : {m : ℝ} → Amplitude n V W m → (k : ℕ) → Symbol n V W (m - k)
  | _, a, 0 => Symbol.inclusion (by simp) a.diag
  | _, a, k + 1 => Symbol.inclusion (by push_cast; linarith)
      ((-Complex.I / (k + 1)) • ∑ j, leftSymbolTerm (spatialDerivSnd j (frequencyDeriv j a)) k)

theorem leftSymbolTerm_zero (a : Amplitude n V W m) :
    a.leftSymbolTerm 0 = Symbol.inclusion (by simp) a.diag := by
  rw [leftSymbolTerm]

theorem leftSymbolTerm_succ (a : Amplitude n V W m) (k : ℕ) :
    a.leftSymbolTerm (k + 1) = Symbol.inclusion (by push_cast; linarith)
      ((-Complex.I / (k + 1)) •
        ∑ j, (spatialDerivSnd j (frequencyDeriv j a)).leftSymbolTerm k) := by
  rw [leftSymbolTerm]

@[simp]
theorem coefficient_leftSymbolTerm_zero (a : Amplitude n V W m) (x ξ : CoordinateSpace n) :
    (a.leftSymbolTerm 0).coefficient (x, ξ) = a.coefficient (x, x, ξ) := by
  rw [leftSymbolTerm_zero, Symbol.coefficient_inclusion, coefficient_diag]

theorem coefficient_leftSymbolTerm_succ (a : Amplitude n V W m) (k : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (a.leftSymbolTerm (k + 1)).coefficient p = (-Complex.I / (k + 1)) •
      ∑ j, ((spatialDerivSnd j (frequencyDeriv j a)).leftSymbolTerm k).coefficient p := by
  simp [leftSymbolTerm_succ]

/-- The coefficient of `∂_{y_j} ∂_{ξ_j} a`, differentiated along further directions, is the
coefficient of `a` differentiated along those directions followed by `∂_{y_j}` and `∂_{ξ_j}`. -/
private theorem iteratedFDerivAlong_spatialDerivSnd_frequencyDeriv (a : Amplitude n V W m)
    (j : Fin n) (vs : List (CoordinateSpace n × CoordinateSpace n × CoordinateSpace n)) :
    iteratedFDerivAlong ℝ vs (spatialDerivSnd j (frequencyDeriv j a)).coefficient =
      iteratedFDerivAlong ℝ (vs ++ amplitudeDirections [] [j] [j]) a.coefficient := by
  simp only [coefficient_spatialDerivSnd_eq, coefficient_frequencyDeriv_eq,
    ← iteratedFDerivAlong_append, amplitudeDirections_def, List.map_nil, List.map_cons,
    List.nil_append, List.cons_append]

/-- Appending `∂_{y_j} ∂_{ξ_j}` to `∂_y^γ ∂_ξ^γ` reorders the directions of
`∂_y^{γ j} ∂_ξ^{γ j}`. -/
private theorem perm_amplitudeDirections_append (γ : List (Fin n)) (j : Fin n) :
    (amplitudeDirections [] γ γ ++ amplitudeDirections [] [j] [j]).Perm
      (amplitudeDirections [] (γ ++ [j]) (γ ++ [j])) := by
  simp only [amplitudeDirections_def, List.map_nil, List.nil_append, List.map_append,
    List.map_cons, List.append_assoc, List.singleton_append]
  exact List.Perm.append_left _ List.perm_middle

/-- **The terms of the expansion of the left symbol** are
`((-i)^k / k!) ∑_{|w| = k} (∂_y^w ∂_ξ^w a)(x, x, ξ)`, the sum running over the words `w` of
coordinate indices of length `k`. Grouping the words by the multi-index they determine gives the
familiar form `∑_{|α| = k} (1 / α!) (∂_ξ^α D_y^α a)(x, x, ξ)` with `D_y = -i ∂_y`. -/
theorem coefficient_leftSymbolTerm (a : Amplitude n V W m) (k : ℕ) (x ξ : CoordinateSpace n) :
    (a.leftSymbolTerm k).coefficient (x, ξ) = ((-Complex.I) ^ k / k.factorial) •
      ∑ w : Fin k → Fin n, iteratedFDerivAlong ℝ
        (amplitudeDirections [] (List.ofFn w) (List.ofFn w)) a.coefficient (x, x, ξ) := by
  induction k generalizing m with
  | zero => simp [amplitudeDirections_def]
  | succ k ih =>
    rw [coefficient_leftSymbolTerm_succ, ← (Fin.snocEquiv fun _ ↦ Fin n).sum_comp,
      Fintype.sum_prod_type]
    simp only [ih, Finset.smul_sum, smul_smul, Fin.snocEquiv_apply, List.ofFn_succ',
      Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append,
      iteratedFDerivAlong_spatialDerivSnd_frequencyDeriv]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun w _ ↦ ?_
    rw [(perm_amplitudeDirections_append (List.ofFn w) j).iteratedFDerivAlong_eq
      a.contDiff_coefficient (by simp)]
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- Position derivatives of the terms: `∂_{x_l}` of `leftSymbolTerm a k` is the sum of the terms
of `∂_{x_l} a` and `∂_{y_l} a`. -/
theorem spatialDeriv_leftSymbolTerm (l : Fin n) (a : Amplitude n V W m) (k : ℕ) :
    Symbol.spatialDeriv l (a.leftSymbolTerm k) =
      (spatialDerivFst l a).leftSymbolTerm k + (spatialDerivSnd l a).leftSymbolTerm k := by
  induction k generalizing m with
  | zero => simp [leftSymbolTerm_zero, spatialDeriv_diag]
  | succ k ih =>
    simp only [leftSymbolTerm_succ, Symbol.spatialDeriv_inclusion, map_smul, map_sum, ih,
      ← map_add, ← smul_add, ← Finset.sum_add_distrib,
      spatialDerivFst_spatialDerivSnd_frequencyDeriv,
      spatialDerivSnd_spatialDerivSnd_frequencyDeriv]

/-- Frequency derivatives of the terms: `∂_{ξ_l}` of `leftSymbolTerm a k` is the term of
`∂_{ξ_l} a`. The orders `m - k - 1` and `m - 1 - k` of the two sides differ syntactically, so the
rule is stated for their coefficients. -/
theorem coefficient_frequencyDeriv_leftSymbolTerm (l : Fin n) (a : Amplitude n V W m) (k : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (Symbol.frequencyDeriv l (a.leftSymbolTerm k)).coefficient p =
      ((frequencyDeriv l a).leftSymbolTerm k).coefficient p := by
  induction k generalizing m with
  | zero =>
    simp only [leftSymbolTerm_zero, Symbol.frequencyDeriv_inclusion, Symbol.coefficient_inclusion,
      frequencyDeriv_diag]
  | succ k ih =>
    simp only [leftSymbolTerm_succ, Symbol.frequencyDeriv_inclusion, map_smul, map_sum,
      Symbol.coefficient_inclusion, Symbol.coefficient_smul, Symbol.coefficient_sum,
      Pi.smul_apply, Finset.sum_apply]
    refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
    rw [ih, frequencyDeriv_spatialDerivSnd_frequencyDeriv]

end Term

/-! ### The interpolating family `A_t` -/

section Scaled

variable (a : Amplitude n V W m)

/-- The integrand `exp(2πi ⟪θ, x⟫) â(x, θ, ξ + sθ)` of the interpolating family, with the
frequency shift `2πθ` of the left symbol scaled to `sθ`. -/
private def shiftIntegrand (s : ℝ) (x ξ θ : CoordinateSpace n) : V →L[ℂ] W :=
  (𝐞 ⟪θ, x⟫ : ℂ) • 𝓕 (fun y ↦ a.coefficient (x, y, ξ + s • θ)) θ

variable {a}

private theorem continuous_shiftIntegrand (ha : a.HasCompactInputSupport)
    (s : ℝ) (x ξ : CoordinateSpace n) : Continuous (shiftIntegrand a s x ξ) := by
  have h₁ : Continuous fun θ : CoordinateSpace n ↦ (𝐞 ⟪θ, x⟫ : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have h₂ : Continuous fun θ ↦ 𝓕 (fun y ↦ a.coefficient (x, y, ξ + s • θ)) θ :=
    ha.continuous_fourier_slice.comp (f := fun θ : CoordinateSpace n ↦ (θ, x, ξ + s • θ))
      (by fun_prop)
  exact h₁.smul h₂

/-- Peetre's inequality and the rapid decay of `â` bound the integrand by
`C ⟨θ⟩ ^ (-(n + 1)) ⟨ξ⟩ ^ m`, uniformly for output positions in a compact set and shifts
`|s| ≤ 4π`. -/
private theorem exists_norm_shiftIntegrand_le
    (ha : a.HasCompactInputSupport) {K : Set (CoordinateSpace n)} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℝ, |s| ≤ 4 * π → ∀ x ∈ K, ∀ ξ θ : CoordinateSpace n,
      ‖shiftIntegrand a s x ξ θ‖ ≤
        C * ((1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_fourier_slice_le hK (|m| + (n + 1))
  refine ⟨C * 2 ^ (|m| / 2) * (4 * π) ^ |m|, by positivity, fun s hs x hx ξ θ ↦ ?_⟩
  have h4π : (1 : ℝ) ≤ 4 * π := by linarith [Real.two_le_pi]
  have hpeetre := one_add_norm_add_sq_rpow_le_mul m ξ (s • θ)
  have hscale : (1 + ‖s • θ‖ ^ 2) ^ (|m| / 2) ≤ (4 * π) ^ |m| * (1 + ‖θ‖ ^ 2) ^ (|m| / 2) := by
    refine le_trans ?_ ((one_add_norm_smul_sq_rpow_le h4π |m| θ).trans_eq (by rw [abs_abs]))
    refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
    gcongr
  have hθ : (1 + ‖θ‖ ^ 2) ^ (|m| / 2) * (1 + ‖θ‖ ^ 2) ^ (-(|m| + (n + 1)) / 2) =
      (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
    rw [← Real.rpow_add (by positivity)]
    ring_nf
  rw [shiftIntegrand, norm_smul, Circle.norm_coe, one_mul]
  calc ‖𝓕 (fun y ↦ a.coefficient (x, y, ξ + s • θ)) θ‖
      ≤ C * (1 + ‖ξ + s • θ‖ ^ 2) ^ (m / 2) * (1 + ‖θ‖ ^ 2) ^ (-(|m| + (n + 1)) / 2) :=
        hC x hx θ _
    _ ≤ C * (2 ^ (|m| / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) *
          ((4 * π) ^ |m| * (1 + ‖θ‖ ^ 2) ^ (|m| / 2))) *
          (1 + ‖θ‖ ^ 2) ^ (-(|m| + (n + 1)) / 2) := by
        gcongr
        exact hpeetre.trans (by gcongr)
    _ = C * 2 ^ (|m| / 2) * (4 * π) ^ |m| * (1 + ‖ξ‖ ^ 2) ^ (m / 2) *
          ((1 + ‖θ‖ ^ 2) ^ (|m| / 2) * (1 + ‖θ‖ ^ 2) ^ (-(|m| + (n + 1)) / 2)) := by ring
    _ = _ := by rw [hθ]; ring

private theorem integrable_shiftIntegrand (ha : a.HasCompactInputSupport)
    {s : ℝ} (hs : |s| ≤ 4 * π) (x ξ : CoordinateSpace n) :
    Integrable (shiftIntegrand a s x ξ) := by
  obtain ⟨C, -, hC⟩ := exists_norm_shiftIntegrand_le ha (isCompact_singleton (x := x))
  exact (((integrable_rpow_neg_one_add_norm_sq (r := n + 1) (by simp)).mul_const
    ((1 + ‖ξ‖ ^ 2) ^ (m / 2))).const_mul C).mono'
    (continuous_shiftIntegrand ha s x ξ).aestronglyMeasurable
    (.of_forall fun θ ↦ by simpa using hC s hs x rfl ξ θ)

/-- The frequency shifts `2πtθ` of the family with `|t| ≤ 2` are at most `4π ‖θ‖`. -/
private theorem abs_mul_two_pi_le {t : ℝ} (ht : |t| ≤ 2) : |t * (2 * π)| ≤ 4 * π := by
  rw [abs_mul, abs_of_pos two_pi_pos]
  nlinarith [pi_pos]

/-- **Differentiation in the parameter** of the integrand: since `2π θⱼ â = -i (∂_{yⱼ} a)^`,
`d/dt` of the integrand of `A_t(a)` is `-i ∑ⱼ` the integrand of `A_t(∂_{yⱼ} ∂_{ξⱼ} a)`. -/
private theorem hasDerivAt_shiftIntegrand
    (ha : a.HasCompactInputSupport) (t : ℝ) (x ξ θ : CoordinateSpace n) :
    HasDerivAt (fun t ↦ shiftIntegrand a (t * (2 * π)) x ξ θ)
      (∑ j, (-Complex.I) •
        shiftIntegrand (spatialDerivSnd j (frequencyDeriv j a)) (t * (2 * π)) x ξ θ) t := by
  set ζ := ξ + (t * (2 * π)) • θ
  have hF := ha.hasFDerivAt_fourier_slice θ (x, ζ)
  have hl : HasDerivAt (fun t : ℝ ↦ (x, ξ + (t * (2 * π)) • θ))
      ((0 : CoordinateSpace n), (2 * π) • θ) t := by
    refine HasDerivAt.prodMk (hasDerivAt_const (𝕜 := ℝ) t x) ?_
    simpa using (((hasDerivAt_id t).mul_const (2 * π)).smul_const θ).const_add ξ
  have h := (hF.comp_hasDerivAt t hl).const_smul (𝐞 ⟪θ, x⟫ : ℂ)
  refine h.congr_deriv ?_
  set D := ∫ y, (𝐞 (-⟪y, θ⟫) : ℂ) • fderiv ℝ (fun q : CoordinateSpace n × CoordinateSpace n ↦
    a.coefficient (q.1, y, q.2)) (x, ζ)
  -- On the coordinate vectors of the frequency, `D` is the Fourier transform of the frequency
  -- derivatives.
  have hD (j : Fin n) : D (0, EuclideanSpace.single j 1) =
      𝓕 (fun y ↦ (frequencyDeriv j a).coefficient (x, y, ζ)) θ := by
    rw [ha.fderiv_fourier_slice_apply θ (x, ζ)]
    simp
  have hsum : D (0, (2 * π) • θ) =
      ∑ j, ((2 * π) • θ) j • D (0, EuclideanSpace.single j 1) := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using
      (D.comp (ContinuousLinearMap.inr ℝ (CoordinateSpace n) (CoordinateSpace n))
        ).apply_eq_sum_single ((2 * π) • θ)
  rw [hsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [hD, shiftIntegrand, (ha.frequencyDeriv j).fourier_spatialDerivSnd_slice,
    PiLp.smul_apply, smul_eq_mul, ← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  linear_combination (↑(𝐞 ⟪θ, x⟫) * 2 * ↑π * ↑(θ.ofLp j) : ℂ) * Complex.I_sq

variable (a) in
/-- The family `A_t(x, ξ) = ∫ exp(2πi ⟪θ, x⟫) â(x, θ, ξ + 2πtθ) dθ` interpolating between the
restriction to the diagonal (`t = 0`) and the left symbol (`t = 1`). -/
private def scaledLeft (t : ℝ) (x ξ : CoordinateSpace n) : V →L[ℂ] W :=
  ∫ θ, shiftIntegrand a (t * (2 * π)) x ξ θ

/-- `‖A_t(x, ξ)‖ ≤ C ⟨ξ⟩ ^ m`, uniformly for output positions in a compact set and `|t| ≤ 2`. -/
private theorem exists_norm_scaledLeft_le (ha : a.HasCompactInputSupport)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ 2 → ∀ x ∈ K, ∀ ξ : CoordinateSpace n,
      ‖scaledLeft a t x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_shiftIntegrand_le ha hK
  set I := ∫ θ : CoordinateSpace n, (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  have hI : 0 ≤ I := integral_nonneg fun θ ↦ by positivity
  refine ⟨C * I, mul_nonneg hC0 hI, fun t ht x hx ξ ↦ ?_⟩
  have hint : Integrable fun θ : CoordinateSpace n ↦
      C * ((1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :=
    (((integrable_rpow_neg_one_add_norm_sq (r := n + 1) (by simp)).mul_const
      ((1 + ‖ξ‖ ^ 2) ^ (m / 2))).const_mul C).congr (.of_forall fun θ ↦ by simp)
  refine (norm_integral_le_of_norm_le hint
    (.of_forall fun θ ↦ hC _ (abs_mul_two_pi_le ht) x hx ξ θ)).trans_eq ?_
  rw [integral_const_mul, integral_mul_const]
  ring

/-- At `t = 1` the family is the left symbol. -/
private theorem scaledLeft_one (ha : a.HasCompactInputSupport) (x ξ : CoordinateSpace n) :
    scaledLeft a 1 x ξ = (a.leftSymbol ha).coefficient (x, ξ) := by
  simp only [scaledLeft, shiftIntegrand, one_mul, coefficient_leftSymbol]

/-- At `t = 0` the family is the restriction to the diagonal, by Fourier inversion. -/
private theorem scaledLeft_zero [CompleteSpace W] (ha : a.HasCompactInputSupport)
    (x ξ : CoordinateSpace n) : scaledLeft a 0 x ξ = a.coefficient (x, x, ξ) := by
  set f : CoordinateSpace n → V →L[ℂ] W := fun y ↦ a.coefficient (x, y, ξ)
  have hfc : Continuous f := a.contDiff_coefficient.continuous.comp (by fun_prop)
  have hfi : Integrable f := hfc.integrable_of_hasCompactSupport (ha.hasCompactSupport_slice x ξ)
  have hFi : Integrable (𝓕 f) := by
    obtain ⟨C, -, hC⟩ := ha.exists_norm_fourier_slice_le (isCompact_singleton (x := x)) (n + 1)
    have hFc : Continuous (𝓕 f) :=
      ha.continuous_fourier_slice.comp (f := fun θ : CoordinateSpace n ↦ (θ, x, ξ)) (by fun_prop)
    exact ((integrable_rpow_neg_one_add_norm_sq (r := n + 1) (by simp)).const_mul
      (C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))).mono' hFc.aestronglyMeasurable
      (.of_forall fun θ ↦ hC x rfl θ ξ)
  have hinv : 𝓕⁻ (𝓕 f) = f := hfc.fourierInv_fourier_eq hfi hFi
  calc scaledLeft a 0 x ξ = 𝓕⁻ (𝓕 f) x := by
        simp only [scaledLeft, shiftIntegrand, zero_mul, zero_smul, add_zero, Real.fourierInv_eq,
          Circle.smul_def, f]
    _ = f x := by rw [hinv]

/-- **Differentiation in the parameter** under the integral sign:
`d/dt A_t(a) = -i ∑ⱼ A_t(∂_{yⱼ} ∂_{ξⱼ} a)`. -/
private theorem hasDerivAt_scaledLeft (ha : a.HasCompactInputSupport)
    {t₀ : ℝ} (ht₀ : |t₀| ≤ 1) (x ξ : CoordinateSpace n) :
    HasDerivAt (fun t ↦ scaledLeft a t x ξ)
      ((-Complex.I) • ∑ j, scaledLeft (spatialDerivSnd j (frequencyDeriv j a)) t₀ x ξ) t₀ := by
  have hb (j : Fin n) := (ha.frequencyDeriv j).spatialDerivSnd j
  choose C hC0 hC using fun j ↦ exists_norm_shiftIntegrand_le (hb j) (isCompact_singleton (x := x))
  have hball : ∀ t ∈ Metric.ball t₀ 1, |t * (2 * π)| ≤ 4 * π := fun t ht ↦ by
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have := abs_sub_abs_le_abs_sub t t₀
    exact abs_mul_two_pi_le (by linarith)
  set F' : ℝ → CoordinateSpace n → V →L[ℂ] W := fun t θ ↦
    ∑ j, (-Complex.I) •
      shiftIntegrand (spatialDerivSnd j (frequencyDeriv j a)) (t * (2 * π)) x ξ θ
  set bound : CoordinateSpace n → ℝ := fun θ ↦
    ∑ j, C j * ((1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m - 1) / 2))
  have hint (j : Fin n) : Integrable fun θ ↦ (-Complex.I) •
      shiftIntegrand (spatialDerivSnd j (frequencyDeriv j a)) (t₀ * (2 * π)) x ξ θ :=
    (integrable_shiftIntegrand (hb j) (abs_mul_two_pi_le (by linarith)) x ξ).fun_smul _
  have hbound : ∀ᵐ θ ∂(volume : Measure (CoordinateSpace n)), ∀ t ∈ Metric.ball t₀ 1,
      ‖F' t θ‖ ≤ bound θ := .of_forall fun θ t ht ↦ by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
    exact hC j _ (hball t ht) x rfl ξ θ
  have hbound_int : Integrable bound :=
    integrable_finsetSum _ fun j _ ↦
      ((integrable_rpow_neg_one_add_norm_sq (r := n + 1) (by simp)).mul_const
        ((1 + ‖ξ‖ ^ 2) ^ ((m - 1) / 2))).const_mul (C j)
  obtain ⟨-, h⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t θ ↦ shiftIntegrand a (t * (2 * π)) x ξ θ) (F' := F')
    (Metric.ball_mem_nhds t₀ one_pos)
    (.of_forall fun t ↦ (continuous_shiftIntegrand ha _ x ξ).aestronglyMeasurable)
    (integrable_shiftIntegrand ha (abs_mul_two_pi_le (by linarith)) x ξ)
    (continuous_finsetSum _ fun j _ ↦
      (continuous_shiftIntegrand (hb j) _ x ξ).const_smul (-Complex.I)).aestronglyMeasurable
    hbound hbound_int (.of_forall fun θ t _ ↦ hasDerivAt_shiftIntegrand ha t x ξ θ)
  refine h.congr_deriv ?_
  simp only [F', integral_finsetSum _ fun j _ ↦ hint j, integral_smul, Finset.smul_sum,
    scaledLeft]

end Scaled

/-! ### The remainder along the family -/

section Remainder

variable {a : Amplitude n V W m}

variable (a) in
/-- The remainder `A_t(a) - ∑_{k < N} t^k leftSymbolTerm a k` of the expansion along the
interpolating family. -/
private def remainderAt (N : ℕ) (t : ℝ) (x ξ : CoordinateSpace n) : V →L[ℂ] W :=
  scaledLeft a t x ξ - ∑ k ∈ range N, t ^ k • (a.leftSymbolTerm k).coefficient (x, ξ)

/-- The derivative of the polynomial part `∑_{k < N + 1} t^k leftSymbolTerm a k` is given by the
recursion defining `leftSymbolTerm`. -/
private theorem hasDerivAt_sum_pow_smul_leftSymbolTerm (N : ℕ) (a : Amplitude n V W m)
    (x ξ : CoordinateSpace n) (t : ℝ) :
    HasDerivAt
      (fun t : ℝ ↦ ∑ k ∈ range (N + 1), t ^ k • (a.leftSymbolTerm k).coefficient (x, ξ))
      (∑ k ∈ range N, t ^ k • ((-Complex.I) •
        ∑ j, ((spatialDerivSnd j (frequencyDeriv j a)).leftSymbolTerm k).coefficient (x, ξ)))
      t := by
  have h := HasDerivAt.fun_sum (u := range (N + 1)) fun k _ ↦
    (hasDerivAt_pow k t).smul_const ((a.leftSymbolTerm k).coefficient (x, ξ))
  refine h.congr_deriv ?_
  rw [Finset.sum_range_succ']
  simp only [CharP.cast_eq_zero, zero_mul, zero_smul, add_zero]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [coefficient_leftSymbolTerm_succ, Nat.add_sub_cancel, mul_comm, mul_smul]
  congr 1
  rw [← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  field_simp

/-- The derivative in `t` of the remainder with `N + 1` terms is `-i ∑ⱼ` the remainders with `N`
terms of `∂_{yⱼ} ∂_{ξⱼ} a`. -/
private theorem hasDerivAt_remainderAt (ha : a.HasCompactInputSupport)
    (N : ℕ) {t : ℝ} (ht : |t| ≤ 1) (x ξ : CoordinateSpace n) :
    HasDerivAt (fun t ↦ remainderAt a (N + 1) t x ξ)
      ((-Complex.I) • ∑ j, remainderAt (spatialDerivSnd j (frequencyDeriv j a)) N t x ξ) t := by
  refine ((hasDerivAt_scaledLeft ha ht x ξ).fun_sub
    (hasDerivAt_sum_pow_smul_leftSymbolTerm N a x ξ t)).congr_deriv ?_
  simp only [remainderAt, smul_sub, Finset.smul_sum, Finset.sum_sub_distrib, smul_comm (t ^ _)]
  rw [Finset.sum_comm]

/-- The remainder vanishes at `t = 0`. -/
private theorem remainderAt_zero [CompleteSpace W] (ha : a.HasCompactInputSupport) (N : ℕ)
    (x ξ : CoordinateSpace n) : remainderAt a (N + 1) 0 x ξ = 0 := by
  rw [remainderAt, scaledLeft_zero ha, Finset.sum_range_succ']
  simp

/-- **The remainder estimate.** `‖A_t(a) - ∑_{k < N} t^k leftSymbolTerm a k‖ ≤ C ⟨ξ⟩ ^ (m - N)`,
uniformly for output positions in a compact set and `t ∈ [0, 1]`. -/
private theorem exists_norm_remainderAt_le [CompleteSpace W] (N : ℕ) :
    ∀ {m : ℝ} {a : Amplitude n V W m}, a.HasCompactInputSupport →
      ∀ {K : Set (CoordinateSpace n)}, IsCompact K →
        ∃ C, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ ξ : CoordinateSpace n,
          ‖remainderAt a N t x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - N) / 2) := by
  induction N with
  | zero =>
    intro m a ha K hK
    obtain ⟨C, hC0, hC⟩ := exists_norm_scaledLeft_le ha hK
    refine ⟨C, hC0, fun t ht x hx ξ ↦ ?_⟩
    have ht2 : |t| ≤ 2 := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa [remainderAt] using hC t ht2 x hx ξ
  | succ N ih =>
    intro m a ha K hK
    choose C hC0 hC using fun j ↦ ih ((ha.frequencyDeriv j).spatialDerivSnd j) hK
    refine ⟨∑ j, C j, Finset.sum_nonneg fun j _ ↦ hC0 j, fun t ht x hx ξ ↦ ?_⟩
    have hw : (1 + ‖ξ‖ ^ 2) ^ ((m - 1 - N) / 2) =
        (1 + ‖ξ‖ ^ 2) ^ ((m - ((N + 1 : ℕ) : ℝ)) / 2) := by
      congr 1
      push_cast
      ring
    have hbound : ∀ s ∈ Set.Ico (0 : ℝ) 1,
        ‖(-Complex.I) • ∑ j, remainderAt (spatialDerivSnd j (frequencyDeriv j a)) N s x ξ‖ ≤
          (∑ j, C j) * (1 + ‖ξ‖ ^ 2) ^ ((m - ((N + 1 : ℕ) : ℝ)) / 2) := by
      intro s hs
      rw [norm_smul, norm_neg, Complex.norm_I, one_mul, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
      rw [← hw]
      exact hC j s (Set.Ico_subset_Icc_self hs) x hx ξ
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s hs ↦ (hasDerivAt_remainderAt ha N (abs_le.2 ⟨by linarith [hs.1], hs.2⟩) x
        ξ).hasDerivWithinAt) hbound t ht
    rw [remainderAt_zero ha, sub_zero, sub_zero] at hmv
    have hB : 0 ≤ (∑ j, C j) * (1 + ‖ξ‖ ^ 2) ^ ((m - ((N + 1 : ℕ) : ℝ)) / 2) :=
      mul_nonneg (Finset.sum_nonneg fun j _ ↦ hC0 j) (by positivity)
    exact hmv.trans (mul_le_of_le_one_right hB ht.2)

end Remainder

/-! ### The remainder symbol -/

section RemainderSymbol

variable {a : Amplitude n V W m}

variable (a) in
/-- The remainder `leftSymbol a - ∑_{k < N} leftSymbolTerm a k`, as a symbol of order `m`. -/
private def remainderSymbol (ha : a.HasCompactInputSupport) (N : ℕ) : Symbol n V W m :=
  a.leftSymbol ha -
    ∑ k ∈ range N, Symbol.inclusion (sub_le_self _ (Nat.cast_nonneg k)) (a.leftSymbolTerm k)

private theorem coefficient_remainderSymbol (ha : a.HasCompactInputSupport) (N : ℕ)
    (x ξ : CoordinateSpace n) :
    (remainderSymbol a ha N).coefficient (x, ξ) = remainderAt a N 1 x ξ := by
  simp [remainderSymbol, remainderAt, scaledLeft_one ha]

private theorem spatialDeriv_remainderSymbol (ha : a.HasCompactInputSupport) (N : ℕ)
    (j : Fin n) :
    Symbol.spatialDeriv j (remainderSymbol a ha N) =
      remainderSymbol (spatialDerivFst j a) (ha.spatialDerivFst j) N +
        remainderSymbol (spatialDerivSnd j a) (ha.spatialDerivSnd j) N := by
  simp only [remainderSymbol, map_sub, map_sum, spatialDeriv_leftSymbol,
    Symbol.spatialDeriv_inclusion, spatialDeriv_leftSymbolTerm, map_add, Finset.sum_add_distrib]
  abel

private theorem frequencyDeriv_remainderSymbol (ha : a.HasCompactInputSupport) (N : ℕ)
    (j : Fin n) :
    Symbol.frequencyDeriv j (remainderSymbol a ha N) =
      remainderSymbol (frequencyDeriv j a) (ha.frequencyDeriv j) N := by
  ext1
  funext p
  simp only [remainderSymbol, map_sub, map_sum, Symbol.coefficient_sub, Symbol.coefficient_sum,
    Symbol.frequencyDeriv_inclusion, Symbol.coefficient_inclusion, Pi.sub_apply,
    Finset.sum_apply, frequencyDeriv_leftSymbol, coefficient_frequencyDeriv_leftSymbolTerm]

/-- The symbol estimates of order `m - N` for the remainder: every mixed derivative of the
remainder of `a` is a sum of remainders of derivatives of `a`, and a frequency derivative lowers
the order of `a` by one. -/
private theorem exists_bound_remainderSymbol [CompleteSpace W] (N : ℕ) (α β : List (Fin n)) :
    ∀ {m : ℝ} {a : Amplitude n V W m} (ha : a.HasCompactInputSupport)
      {K : Set (CoordinateSpace n)}, IsCompact K → ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
        ‖mixedDeriv α β (remainderSymbol a ha N).coefficient x ξ‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ ((m - N - β.length) / 2) := by
  obtain ⟨D, hD⟩ : ∃ D, α.length + β.length = D := ⟨_, rfl⟩
  induction D generalizing α β with
  | zero =>
    obtain ⟨rfl, rfl⟩ : α = [] ∧ β = [] := by
      simpa [List.length_eq_zero_iff] using hD
    intro m a ha K hK
    obtain ⟨C, hC0, hC⟩ := exists_norm_remainderAt_le N ha hK
    refine ⟨C, hC0, fun x hx ξ ↦ ?_⟩
    simpa [coefficient_remainderSymbol] using hC 1 ⟨zero_le_one, le_rfl⟩ x hx ξ
  | succ D ih =>
    intro m a ha K hK
    rcases List.eq_nil_or_concat' β with rfl | ⟨β', j, rfl⟩
    · rcases List.eq_nil_or_concat' α with rfl | ⟨α', j, rfl⟩
      · simp at hD
      · have hlen : α'.length + ([] : List (Fin n)).length = D := by simpa using hD
        obtain ⟨C₁, hC₁0, hC₁⟩ := ih α' [] hlen (ha.spatialDerivFst j) hK
        obtain ⟨C₂, hC₂0, hC₂⟩ := ih α' [] hlen (ha.spatialDerivSnd j) hK
        refine ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun x hx ξ ↦ ?_⟩
        rw [← Symbol.mixedDeriv_spatialDeriv, spatialDeriv_remainderSymbol,
          Symbol.coefficient_add, mixedDeriv_add (Symbol.contDiff_coefficient _)
            (Symbol.contDiff_coefficient _), add_mul]
        exact (norm_add_le _ _).trans (add_le_add (hC₁ x hx ξ) (hC₂ x hx ξ))
    · have hlen : α.length + β'.length = D := by
        simp only [List.length_append, List.length_singleton] at hD
        omega
      obtain ⟨C, hC0, hC⟩ := ih α β' hlen (ha.frequencyDeriv j) hK
      refine ⟨C, hC0, fun x hx ξ ↦ ?_⟩
      have e : (m - 1 - N - β'.length) / 2 = (m - N - (β' ++ [j]).length) / 2 := by
        simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
        ring
      rw [← Symbol.mixedDeriv_frequencyDeriv, frequencyDeriv_remainderSymbol, ← e]
      exact hC x hx ξ

variable [CompleteSpace W]

variable (a) in
/-- The remainder `leftSymbol a - ∑_{k < N} leftSymbolTerm a k` of the expansion of the left
symbol after `N` terms, a symbol of order `m - N`
(`leftSymbol_eq_sum_leftSymbolTerm_add_leftSymbolRemainder`). -/
def leftSymbolRemainder (ha : a.HasCompactInputSupport) (N : ℕ) : Symbol n V W (m - N) where
  coefficient := (remainderSymbol a ha N).coefficient
  contDiff_coefficient := (remainderSymbol a ha N).contDiff_coefficient
  exists_bound _ hK α β := exists_bound_remainderSymbol N α β ha hK

@[simp]
theorem coefficient_leftSymbolRemainder (ha : a.HasCompactInputSupport) (N : ℕ) :
    (a.leftSymbolRemainder ha N).coefficient =
      (a.leftSymbol ha).coefficient - ∑ k ∈ range N, (a.leftSymbolTerm k).coefficient := by
  simp [leftSymbolRemainder, remainderSymbol]

/-- **The asymptotic expansion of the left symbol of an amplitude.** For every `N`,
`leftSymbol a = ∑_{k < N} leftSymbolTerm a k + leftSymbolRemainder a ha N`, where
`leftSymbolTerm a k` is the term `((-i)^k / k!) ∑_{|w| = k} (∂_y^w ∂_ξ^w a)(x, x, ξ)` of order
`m - k` and the remainder is a symbol of order `m - N`. -/
theorem leftSymbol_eq_sum_leftSymbolTerm_add_leftSymbolRemainder
    (ha : a.HasCompactInputSupport) (N : ℕ) :
    a.leftSymbol ha =
      ∑ k ∈ range N, Symbol.inclusion (sub_le_self _ (Nat.cast_nonneg k)) (a.leftSymbolTerm k) +
        Symbol.inclusion (sub_le_self _ (Nat.cast_nonneg N)) (a.leftSymbolRemainder ha N) := by
  ext1
  simp

/-- The left symbol of an amplitude is its restriction `a(x, x, ξ)` to the diagonal up to a
symbol of order `m - 1`. -/
theorem leftSymbol_eq_diag_add_leftSymbolRemainder_one (ha : a.HasCompactInputSupport) :
    a.leftSymbol ha = a.diag + Symbol.inclusion (by simp) (a.leftSymbolRemainder ha 1) := by
  ext1
  funext ⟨x, ξ⟩
  simp

/-- The left symbol of an amplitude is an asymptotic sum `leftSymbol a ∼ ∑ₖ leftSymbolTerm a k`
of the terms of the expansion, of orders `m - k`. In particular it is determined by the terms
modulo smoothing symbols (`TauCeti.Symbol.IsAsymptoticSum.isAsymptoticSum_iff_isSmoothing_sub`). -/
theorem isAsymptoticSum_leftSymbol (ha : a.HasCompactInputSupport) :
    Symbol.IsAsymptoticSum (m := fun k : ℕ ↦ m - k)
      (Symbol.inclusion (by simp) (a.leftSymbol ha)) a.leftSymbolTerm :=
  Symbol.isAsymptoticSum_iff.2 fun N ↦ ⟨a.leftSymbolRemainder ha N, by simp⟩

end RemainderSymbol

end Amplitude

end TauCeti
