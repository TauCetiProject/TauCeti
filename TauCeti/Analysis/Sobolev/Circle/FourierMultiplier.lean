/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Theta
public import TauCeti.Analysis.Fredholm.FiniteRank
public import TauCeti.Analysis.Sobolev.Circle.Basic

/-!
# Fourier multipliers on the circle Sobolev spaces and their elliptic theory

A translation-invariant operator on the circle multiplies the `n`-th Fourier coefficient by a
number `p n`. A constant-coefficient differential operator `∑ⱼ cⱼ ∂ʲ` of order `m` on the circle
`AddCircle T` is of this form, with the polynomial symbol `p n = ∑ⱼ cⱼ (2πin/T) ʲ`. This file
develops the elliptic theory of such operators on the Fourier-coefficient Sobolev spaces `H^s` of
`TauCeti/Analysis/Sobolev/Circle/Basic.lean`. It is the model case, on the simplest compact
manifold, of the regularity and Fredholm theory of elliptic operators on compact bases.

A sequence `p : ℤ → ℂ` is a *symbol of order `m`* when `p =O[cofinite] weight m`, that is
`‖p n‖ ≤ C (1 + |n|) ^ m`; it is *elliptic of order `m`* when moreover `weight m =O[cofinite] p`,
that is `p =Θ[cofinite] weight m`. A symbol of order `m` gives a bounded operator
`P : H^t → H^s` for `s + m ≤ t` (`TauCeti.CircleSobolev.fourierMultiplier`). For an elliptic
symbol of order `m` and `s + m = t`:

* `P` has a **two-sided parametrix** `G`, the multiplier with the symbol `n ↦ (p n)⁻¹` of order
  `-m`, with `P G = 1 - Π` and `G P = 1 - Π`, where `Π` is the projection onto the finitely many
  Fourier modes at which `p` vanishes (`TauCeti.CircleSobolev.modeProjection`);
* **elliptic regularity**: if the formal series with coefficients `p n • c n` lies in `H^s`, then
  `c` is the coefficient sequence of an element of `H^(s + m)`, for any sequence `c`; in particular
  every solution of `P a = 0` lies in every `H^u`;
* the **kernel** consists of the elements supported on the zero modes of `p`, and the **range**
  of the elements whose coefficients vanish at those modes: `P a = b` is solvable exactly when these
  finitely many compatibility conditions hold;
* `P` is **Fredholm of index zero** when `E` is finite-dimensional;
* the **elliptic estimate** `‖a‖_{H^t} ≤ C (‖P a‖_{H^s} + ‖a‖_{H^r})` holds for every `r ≤ t`;
  on the orthogonal complement of the kernel the lower-order term can be dropped, and when `P`
  has a nonzero kernel it cannot be dropped on all of `H^t`.

## Main definitions

* `TauCeti.CircleSobolev.fourierMultiplier p hp h`: the multiplier `H^t → H^s` with symbol `p`
  of order `m`, for `s + m ≤ t`.
* `TauCeti.CircleSobolev.fourierMultiplierEquiv`: for an elliptic symbol without zeros, the
  multiplier as an isomorphism `H^t ≃ H^s`, `s + m = t`.
* `TauCeti.CircleSobolev.modeProjection S`: the projection keeping the Fourier modes in `S`.

## Main statements

* `TauCeti.CircleSobolev.fourierMultiplier_fourierMultiplier_inv`,
  `TauCeti.CircleSobolev.fourierMultiplier_inv_fourierMultiplier`: the parametrix identities.
* `TauCeti.CircleSobolev.exists_coeff_eq_of_coeff_eq_smul`: elliptic regularity.
* `TauCeti.CircleSobolev.fourierMultiplier_eq_zero_iff`,
  `TauCeti.CircleSobolev.mem_range_fourierMultiplier_iff`: kernel and range.
* `TauCeti.CircleSobolev.isFredholm_fourierMultiplier`,
  `TauCeti.CircleSobolev.index_fourierMultiplier`: the Fredholm property and the index.
* `TauCeti.CircleSobolev.exists_norm_le_add`: the elliptic estimate with a lower-order term.
* `TauCeti.CircleSobolev.exists_norm_le_of_mem_orthogonal_ker`: the estimate without it on the
  orthogonal complement of the kernel, and `TauCeti.CircleSobolev.not_exists_norm_le_of_eq_zero`:
  its failure on a nonzero kernel.

## References

* M. E. Taylor, *Partial Differential Equations I*, Chapter 3 (Sobolev spaces on the torus via
  Fourier series) and Chapter 5, §1 (elliptic regularity and Fredholm properties).
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.1)–(4.11) (parametrices and elliptic regularity).
-/

public section

noncomputable section

open Asymptotics Filter

namespace TauCeti

namespace CircleSobolev

variable {s t r m m' : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {p q : ℤ → ℂ}

/-! ### Symbols -/

/-- A symbol of order `m` is bounded by a fixed multiple of `(1 + |n|) ^ m` at every frequency. -/
private theorem exists_forall_norm_le_of_isBigO (hp : p =O[cofinite] weight m) :
    ∃ C, 0 ≤ C ∧ ∀ n, ‖p n‖ ≤ C * weight m n := by
  obtain ⟨C, hC⟩ := (isBigO_cofinite_iff fun n hn ↦ absurd hn (weight_pos m n).ne').1 hp
  refine ⟨max C 0, le_max_right _ _, fun n ↦ (hC n).trans ?_⟩
  rw [norm_weight]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (weight_nonneg m n)

/-- An elliptic symbol of order `m` is bounded below by a fixed multiple of `(1 + |n|) ^ m` at
every frequency where it does not vanish. -/
private theorem exists_pos_forall_le_norm_of_isBigO (he : weight m =O[cofinite] p) :
    ∃ c, 0 < c ∧ ∀ n, p n ≠ 0 → c * weight m n ≤ ‖p n‖ := by
  obtain ⟨C, hC, h⟩ := bound_of_isBigO_cofinite he
  refine ⟨C⁻¹, inv_pos.2 hC, fun n hn ↦ ?_⟩
  have h' := h hn
  rw [norm_weight] at h'
  rwa [inv_mul_le_iff₀ hC]

/-- An elliptic symbol vanishes at only finitely many frequencies. -/
theorem finite_setOf_eq_zero (he : weight m =O[cofinite] p) : {n | p n = 0}.Finite := by
  obtain ⟨C, hC⟩ := he.bound
  have h : ∀ᶠ n in cofinite, p n ≠ 0 := hC.mono fun n hn hpn ↦ by
    rw [hpn, norm_zero, mul_zero, norm_weight] at hn
    exact (weight_pos m n).not_ge hn
  simpa using Filter.eventually_cofinite.1 h

/-- The inverse `n ↦ (p n)⁻¹` of an elliptic symbol of order `m`, which is `0` where `p`
vanishes, is a symbol of order `-m`. -/
theorem isBigO_inv (he : weight m =O[cofinite] p) :
    (fun n ↦ (p n)⁻¹) =O[cofinite] weight (-m) := by
  have h := he.inv_rev (Eventually.of_forall fun n hn ↦ absurd hn (weight_pos m n).ne')
  convert h using 1
  exact funext fun n ↦ weight_neg m n

/-- The indicator function of a set of frequencies is a symbol of order `0`. -/
theorem isBigO_indicator_one (S : Set ℤ) : S.indicator (1 : ℤ → ℂ) =O[cofinite] weight 0 :=
  IsBigO.of_bound' (Eventually.of_forall fun n ↦ by
    by_cases hn : n ∈ S <;> simp [hn, weight_zero_left])

/-- A symbol vanishing outside a finite set is a symbol of every order. -/
theorem isBigO_of_forall_notMem_eq_zero {F : Finset ℤ} (hF : ∀ n ∉ F, q n = 0) (m : ℝ) :
    q =O[cofinite] weight m :=
  IsBigO.of_bound 0 (F.finite_toSet.eventually_cofinite_notMem.mono fun n hn ↦ by
    simp [hF n hn])

/-! ### The multiplier -/

private theorem weight_mul_norm_smul_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ n, ‖p n‖ ≤ C * weight m n)
    (h : s + m ≤ t) (n : ℤ) (x : E) :
    weight s n * ‖p n • x‖ ≤ C * (weight t n * ‖x‖) := by
  rw [norm_smul]
  calc weight s n * (‖p n‖ * ‖x‖) ≤ weight s n * (C * weight m n * ‖x‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg x))
          (weight_nonneg s n)
    _ = C * (weight (s + m) n * ‖x‖) := by rw [weight_add]; ring
    _ ≤ C * (weight t n * ‖x‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (weight_le_weight h n) (norm_nonneg x)) hC0

/-- The Fourier multiplier with symbol `p` of order `m`, as a bounded operator `H^t → H^s` for
`s + m ≤ t`: it multiplies the `n`-th Fourier coefficient by `p n`. -/
def fourierMultiplier (p : ℤ → ℂ) (hp : p =O[cofinite] weight m) (h : s + m ≤ t) :
    CircleSobolev t E →L[ℂ] CircleSobolev s E :=
  LinearMap.mkContinuousOfExistsBound
    { toFun a := ⟨fun n ↦ p n • a.coeff n, by
        obtain ⟨C, hC0, hC⟩ := exists_forall_norm_le_of_isBigO hp
        exact memℓp_of_forall_le fun n ↦ weight_mul_norm_smul_le hC0 hC h n (a.coeff n)⟩
      map_add' a b := CircleSobolev.ext (funext fun n ↦ smul_add _ (a.coeff n) (b.coeff n))
      map_smul' c a := CircleSobolev.ext (funext fun n ↦ smul_comm _ c (a.coeff n)) }
    (by
      obtain ⟨C, hC0, hC⟩ := exists_forall_norm_le_of_isBigO hp
      exact ⟨C, fun a ↦
        norm_le_of_forall_le fun n ↦ weight_mul_norm_smul_le hC0 hC h n (a.coeff n)⟩)

@[simp]
theorem coeff_fourierMultiplier (hp : p =O[cofinite] weight m) (h : s + m ≤ t)
    (a : CircleSobolev t E) (n : ℤ) :
    (fourierMultiplier p hp h a).coeff n = p n • a.coeff n :=
  (rfl)

@[simp]
theorem fourierMultiplier_single (hp : p =O[cofinite] weight m) (h : s + m ≤ t) (n : ℤ) (x : E) :
    fourierMultiplier p hp h (single n x) = single n (p n • x) :=
  CircleSobolev.ext (funext fun k ↦ by
    rcases eq_or_ne k n with rfl | hk
    · simp
    · simp [hk])

@[simp]
theorem fourierMultiplier_inclusion {u : ℝ} (hp : p =O[cofinite] weight m) (h : s + m ≤ t)
    (htu : t ≤ u) (a : CircleSobolev u E) :
    fourierMultiplier p hp h (inclusion htu a) = fourierMultiplier p hp (h.trans htu) a :=
  CircleSobolev.ext (funext fun n ↦ by simp)

@[simp]
theorem inclusion_fourierMultiplier (hrs : r ≤ s) (hp : p =O[cofinite] weight m) (h : s + m ≤ t)
    (a : CircleSobolev t E) :
    inclusion hrs (fourierMultiplier p hp h a) = fourierMultiplier p hp (by linarith) a :=
  CircleSobolev.ext (funext fun n ↦ by simp)

/-- Fourier multipliers compose by multiplying their symbols. -/
theorem fourierMultiplier_comp_fourierMultiplier {u m'' : ℝ} (hq : q =O[cofinite] weight m')
    (hp : p =O[cofinite] weight m) (hqp : (fun n ↦ q n * p n) =O[cofinite] weight m'')
    (h₁ : s + m' ≤ t) (h₂ : t + m ≤ u) (h : s + m'' ≤ u) :
    (fourierMultiplier q hq h₁).comp (fourierMultiplier p hp h₂) =
      (fourierMultiplier (fun n ↦ q n * p n) hqp h : CircleSobolev u E →L[ℂ] _) :=
  ContinuousLinearMap.ext fun a ↦ CircleSobolev.ext (funext fun n ↦ by simp [mul_smul])

/-- A multiplier whose symbol vanishes outside a finite set `F` is the finite sum of the rank
`dim E` operators `q n • single n ∘ coeff n`, `n ∈ F`. -/
theorem fourierMultiplier_eq_sum (hq : q =O[cofinite] weight m) (h : s + m ≤ t) {F : Finset ℤ}
    (hF : ∀ n ∉ F, q n = 0) :
    fourierMultiplier q hq h =
      ∑ n ∈ F, q n • (single n).comp (coeffCLM n : CircleSobolev t E →L[ℂ] E) := by
  refine ContinuousLinearMap.ext fun a ↦ CircleSobolev.ext (funext fun k ↦ ?_)
  rw [coeff_fourierMultiplier, _root_.sum_apply, coeff_sum, Finset.sum_apply,
    Finset.sum_eq_single k]
  · simp
  · intro n _ hn
    simp [hn.symm]
  · intro hk
    simp [hF k hk]

/-- A multiplier whose symbol vanishes outside a finite set has finite rank when `E` is
finite-dimensional. -/
theorem hasFiniteRange_fourierMultiplier [FiniteDimensional ℂ E] (hq : q =O[cofinite] weight m)
    (h : s + m ≤ t) {F : Finset ℤ} (hF : ∀ n ∉ F, q n = 0) :
    LinearMap.HasFiniteRange
      (fourierMultiplier q hq h : CircleSobolev t E →L[ℂ] CircleSobolev s E).toLinearMap := by
  rw [fourierMultiplier_eq_sum hq h hF, ContinuousLinearMap.toLinearMap_sum]
  refine Finset.sum_induction _ LinearMap.HasFiniteRange (fun _ _ ha hb ↦ ha.add hb)
    LinearMap.HasFiniteRange.zero fun n _ ↦ ?_
  rw [ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_comp]
  exact (LinearMap.HasFiniteRange.of_finite_dom.comp_right _).smul _

/-- An elliptic symbol of order `m` without zeros gives an isomorphism `H^t ≃ H^s` for
`s + m = t`, whose inverse is the multiplier with the inverse symbol. -/
def fourierMultiplierEquiv (hp : p =Θ[cofinite] weight m) (hz : ∀ n, p n ≠ 0) (h : s + m = t) :
    CircleSobolev t E ≃L[ℂ] CircleSobolev s E :=
  ContinuousLinearEquiv.equivOfInverse (fourierMultiplier p hp.1 h.le)
    (fourierMultiplier (fun n ↦ (p n)⁻¹) (isBigO_inv hp.2) (by linarith))
    (fun a ↦ CircleSobolev.ext (funext fun n ↦ by simp [smul_smul, inv_mul_cancel₀ (hz n)]))
    (fun b ↦ CircleSobolev.ext (funext fun n ↦ by simp [smul_smul, mul_inv_cancel₀ (hz n)]))

@[simp]
theorem coe_fourierMultiplierEquiv (hp : p =Θ[cofinite] weight m) (hz : ∀ n, p n ≠ 0)
    (h : s + m = t) :
    ((fourierMultiplierEquiv hp hz h : CircleSobolev t E ≃L[ℂ] CircleSobolev s E) :
      CircleSobolev t E →L[ℂ] CircleSobolev s E) =
      fourierMultiplier p hp.1 h.le :=
  (rfl)

@[simp]
theorem coe_fourierMultiplierEquiv_symm (hp : p =Θ[cofinite] weight m) (hz : ∀ n, p n ≠ 0)
    (h : s + m = t) :
    ((fourierMultiplierEquiv hp hz h : CircleSobolev t E ≃L[ℂ] CircleSobolev s E).symm :
      CircleSobolev s E →L[ℂ] CircleSobolev t E) =
      fourierMultiplier (fun n ↦ (p n)⁻¹) (isBigO_inv hp.2) (by linarith) :=
  (rfl)

@[simp]
theorem fourierMultiplierEquiv_apply (hp : p =Θ[cofinite] weight m) (hz : ∀ n, p n ≠ 0)
    (h : s + m = t) (a : CircleSobolev t E) :
    fourierMultiplierEquiv hp hz h a = fourierMultiplier p hp.1 h.le a :=
  (rfl)

@[simp]
theorem fourierMultiplierEquiv_symm_apply (hp : p =Θ[cofinite] weight m) (hz : ∀ n, p n ≠ 0)
    (h : s + m = t) (b : CircleSobolev s E) :
    (fourierMultiplierEquiv hp hz h).symm b =
      fourierMultiplier (fun n ↦ (p n)⁻¹) (isBigO_inv hp.2) (show t + -m ≤ s by linarith) b :=
  (rfl)

/-! ### Projections onto Fourier modes -/

/-- The projection of `H^s` onto the Fourier modes in `S`: it keeps the Fourier coefficients
indexed by `S` and replaces the others by `0`. -/
def modeProjection (S : Set ℤ) : CircleSobolev s E →L[ℂ] CircleSobolev s E :=
  fourierMultiplier (S.indicator 1) (isBigO_indicator_one S) (by simp)

@[simp]
theorem coeff_modeProjection (S : Set ℤ) (a : CircleSobolev s E) (n : ℤ) :
    (modeProjection S a).coeff n = S.indicator a.coeff n := by
  by_cases hn : n ∈ S <;> simp [modeProjection, hn]

/-- The projection onto finitely many Fourier modes has finite rank when `E` is
finite-dimensional. -/
theorem hasFiniteRange_modeProjection [FiniteDimensional ℂ E] {S : Set ℤ} (hS : S.Finite) :
    (modeProjection S : CircleSobolev s E →L[ℂ] CircleSobolev s E).toLinearMap.HasFiniteRange :=
  hasFiniteRange_fourierMultiplier _ _ (F := hS.toFinset) fun n hn ↦ by simp_all

/-! ### The parametrix -/

/-- **The parametrix identity** `P G = 1 - Π`. For an elliptic symbol `p` of order `m`, the
multiplier `G` with the inverse symbol `n ↦ (p n)⁻¹` of order `-m` is a right inverse of the
multiplier `P` with symbol `p` up to the projection `Π` onto the finitely many Fourier modes where
`p` vanishes. -/
theorem fourierMultiplier_fourierMultiplier_inv (hp : p =Θ[cofinite] weight m) (h : s + m = t)
    (b : CircleSobolev s E) :
    fourierMultiplier p hp.1 h.le
        (fourierMultiplier (fun n ↦ (p n)⁻¹) (isBigO_inv hp.2) (show t + -m ≤ s by linarith) b) =
      b - modeProjection {n | p n = 0} b :=
  CircleSobolev.ext (funext fun n ↦ by
    by_cases hn : p n = 0
    · simp [hn]
    · simp [hn, smul_smul])

/-- **The parametrix identity** `G P = 1 - Π`: the multiplier with the inverse symbol is a left
inverse of `P` up to the projection onto the modes where `p` vanishes. -/
theorem fourierMultiplier_inv_fourierMultiplier (hp : p =Θ[cofinite] weight m) (h : s + m = t)
    (a : CircleSobolev t E) :
    fourierMultiplier (fun n ↦ (p n)⁻¹) (isBigO_inv hp.2) (show t + -m ≤ s by linarith)
        (fourierMultiplier p hp.1 h.le a) =
      a - modeProjection {n | p n = 0} a :=
  CircleSobolev.ext (funext fun n ↦ by
    by_cases hn : p n = 0
    · simp [hn]
    · simp [hn, smul_smul])

/-! ### Kernel, range and regularity -/

/-- The kernel of a Fourier multiplier consists of the elements whose Fourier coefficients vanish
at every frequency where the symbol does not. -/
theorem fourierMultiplier_eq_zero_iff (hp : p =O[cofinite] weight m) (h : s + m ≤ t)
    (a : CircleSobolev t E) :
    fourierMultiplier p hp h a = 0 ↔ ∀ n, p n ≠ 0 → a.coeff n = 0 := by
  refine ⟨fun ha n hn ↦ ?_, fun ha ↦ CircleSobolev.ext (funext fun n ↦ ?_)⟩
  · have := congr_arg (fun b : CircleSobolev s E ↦ b.coeff n) ha
    simpa [hn] using this
  · by_cases hn : p n = 0
    · simp [hn]
    · simp [ha n hn]

/-- **Solvability.** For an elliptic symbol `p` of order `m` and `s + m = t`, the equation
`P a = b` has a solution `a ∈ H^t` exactly when `b ∈ H^s` satisfies the finitely many
compatibility conditions `b.coeff n = 0` at the frequencies where `p` vanishes. -/
theorem mem_range_fourierMultiplier_iff (hp : p =Θ[cofinite] weight m) (h : s + m = t)
    (b : CircleSobolev s E) :
    b ∈ (fourierMultiplier p hp.1 h.le : CircleSobolev t E →L[ℂ] CircleSobolev s E).range ↔
      ∀ n, p n = 0 → b.coeff n = 0 := by
  refine ⟨?_, fun hb ↦ ⟨_, fourierMultiplier_fourierMultiplier_inv hp h b |>.trans ?_⟩⟩
  · rintro ⟨a, rfl⟩ n hn
    simp [hn]
  · refine CircleSobolev.ext (funext fun n ↦ ?_)
    by_cases hn : p n = 0 <;> simp [hn, hb]

/-- **Elliptic regularity.** Let `p` be elliptic of order `m`. If the formal Fourier series with
coefficients `p n • c n` is an element of `H^s`, then `c` is the coefficient sequence of an
element of `H^t`, `t = s + m`. No regularity of `c` is assumed, so this applies to every
distribution on the circle. -/
theorem exists_coeff_eq_of_coeff_eq_smul (he : weight m =O[cofinite] p) (h : s + m = t)
    {c : ℤ → E} (b : CircleSobolev s E) (hb : ∀ n, b.coeff n = p n • c n) :
    ∃ a : CircleSobolev t E, a.coeff = c := by
  subst h
  obtain ⟨C, hC⟩ := he.bound
  refine (exists_coeff_eq_iff c).2 ((memℓp_weight_smul_iff c).2 ?_)
  refine Summable.of_norm_bounded_eventually
    ((hasSum_sq_weight_mul_norm_coeff b).summable.mul_left (C ^ 2)) (hC.mono fun n hn ↦ ?_)
  have hle : weight (s + m) n * ‖c n‖ ≤ C * (weight s n * ‖b.coeff n‖) := by
    rw [norm_weight] at hn
    rw [hb, norm_smul, weight_add]
    calc weight s n * weight m n * ‖c n‖ ≤ weight s n * (C * ‖p n‖) * ‖c n‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hn (weight_nonneg s n)) (norm_nonneg _)
      _ = C * (weight s n * (‖p n‖ * ‖c n‖)) := by ring
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← mul_pow]
  exact pow_le_pow_left₀ (mul_nonneg (weight_nonneg _ n) (norm_nonneg _)) hle 2

/-- Solutions of an elliptic equation `P a = 0` are smooth: they lie in every `H^u`. -/
theorem exists_coeff_eq_of_fourierMultiplier_eq_zero (hp : p =Θ[cofinite] weight m)
    (h : s + m ≤ t) {a : CircleSobolev t E} (ha : fourierMultiplier p hp.1 h a = 0) (u : ℝ) :
    ∃ b : CircleSobolev u E, b.coeff = a.coeff :=
  exists_coeff_eq_of_coeff_eq_smul hp.2 (show u - m + m = u by ring) 0 fun n ↦ by
    rw [← coeff_fourierMultiplier hp.1 h, ha]
    simp

/-! ### Estimates -/

/-- **The lower bound off the zero modes.** For an elliptic symbol `p` of order `m` and
`s + m = t`, there is `C` with `‖a - Π a‖_{H^t} ≤ C ‖P a‖_{H^s}` for every `a ∈ H^t`, where `Π` is
the projection onto the Fourier modes at which `p` vanishes. -/
theorem exists_norm_sub_modeProjection_le (hp : p =Θ[cofinite] weight m) (h : s + m = t) :
    ∃ C, ∀ a : CircleSobolev t E,
      ‖a - modeProjection {n | p n = 0} a‖ ≤ C * ‖fourierMultiplier p hp.1 h.le a‖ := by
  obtain ⟨c, hc, hle⟩ := exists_pos_forall_le_norm_of_isBigO hp.2
  refine ⟨c⁻¹, fun a ↦ norm_le_of_forall_le fun n ↦ ?_⟩
  by_cases hn : p n = 0
  · simp [hn]
  · rw [coeff_sub, Pi.sub_apply, coeff_modeProjection, Set.indicator_of_notMem hn, sub_zero,
      coeff_fourierMultiplier, norm_smul, show weight t n = weight s n * weight m n by
        rw [← h, weight_add]]
    calc weight s n * weight m n * ‖a.coeff n‖
        = c⁻¹ * (weight s n * (c * weight m n) * ‖a.coeff n‖) := by field_simp
      _ ≤ c⁻¹ * (weight s n * ‖p n‖ * ‖a.coeff n‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hle n hn) (weight_nonneg s n)) (norm_nonneg _))
            (inv_nonneg.2 hc.le)
      _ = c⁻¹ * (weight s n * (‖p n‖ * ‖a.coeff n‖)) := by ring

/-- The projection onto finitely many Fourier modes is bounded from `H^r` to `H^t`. -/
private theorem exists_norm_modeProjection_le {S : Set ℤ} (hS : S.Finite) (hr : r ≤ t) :
    ∃ K, 0 ≤ K ∧ ∀ a : CircleSobolev t E, ‖modeProjection S a‖ ≤ K * ‖inclusion hr a‖ := by
  obtain ⟨K, hK⟩ := (hS.image (weight (t - r))).bddAbove
  refine ⟨max K 0, le_max_right _ _, fun a ↦ norm_le_of_forall_le fun n ↦ ?_⟩
  by_cases hn : n ∈ S
  · rw [coeff_modeProjection, Set.indicator_of_mem hn, coeff_inclusion,
      show weight t n = weight (t - r) n * weight r n by rw [← weight_add, sub_add_cancel],
      mul_assoc]
    exact mul_le_mul_of_nonneg_right ((hK ⟨n, hn, rfl⟩).trans (le_max_left _ _))
      (mul_nonneg (weight_nonneg r n) (norm_nonneg _))
  · rw [coeff_modeProjection, Set.indicator_of_notMem hn, norm_zero, mul_zero]
    exact mul_nonneg (le_max_right _ _) (mul_nonneg (weight_nonneg r n) (norm_nonneg _))

/-- **The elliptic estimate.** For an elliptic symbol `p` of order `m`, `s + m = t` and any
`r ≤ t`, there is `C` with `‖a‖_{H^t} ≤ C (‖P a‖_{H^s} + ‖a‖_{H^r})` for every `a ∈ H^t`. -/
theorem exists_norm_le_add (hp : p =Θ[cofinite] weight m) (h : s + m = t) (hr : r ≤ t) :
    ∃ C, ∀ a : CircleSobolev t E,
      ‖a‖ ≤ C * (‖fourierMultiplier p hp.1 h.le a‖ + ‖inclusion hr a‖) := by
  obtain ⟨C, hC⟩ := exists_norm_sub_modeProjection_le (E := E) hp h
  obtain ⟨K, -, hK⟩ := exists_norm_modeProjection_le (E := E) (finite_setOf_eq_zero hp.2) hr
  refine ⟨max C K, fun a ↦ ?_⟩
  calc ‖a‖ = ‖(a - modeProjection {n | p n = 0} a) + modeProjection {n | p n = 0} a‖ := by
        rw [sub_add_cancel]
    _ ≤ C * ‖fourierMultiplier p hp.1 h.le a‖ + K * ‖inclusion hr a‖ :=
        (norm_add_le _ _).trans (add_le_add (hC a) (hK a))
    _ ≤ max C K * ‖fourierMultiplier p hp.1 h.le a‖ + max C K * ‖inclusion hr a‖ := by
        gcongr
        exacts [le_max_left _ _, le_max_right _ _]
    _ = _ := by ring

/-- Without kernel orthogonality the lower-order term cannot be dropped: if `p` vanishes at some
frequency `n₀`, then no estimate `‖a‖_{H^t} ≤ C ‖P a‖_{H^s}` holds on all of `H^t`, since the
nonzero Fourier monomials at `n₀` lie in the kernel. -/
theorem not_exists_norm_le_of_eq_zero [Nontrivial E] (hp : p =O[cofinite] weight m)
    (h : s + m ≤ t) {n₀ : ℤ} (hn₀ : p n₀ = 0) :
    ¬ ∃ C, ∀ a : CircleSobolev t E, ‖a‖ ≤ C * ‖fourierMultiplier p hp h a‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have h₀ := hC (single n₀ x)
  rw [fourierMultiplier_single, hn₀, zero_smul, map_zero, norm_zero, mul_zero, norm_single] at h₀
  exact (mul_pos (weight_pos t n₀) (norm_pos_iff.2 hx)).not_ge h₀

section Inner

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The inner product of `H^s` with a Fourier monomial picks out one weighted Fourier
coefficient. -/
theorem inner_single_left (n : ℤ) (x : F) (a : CircleSobolev s F) :
    inner ℂ (single n x) a = (weight (2 * s) n : ℂ) * inner ℂ x (a.coeff n) := by
  rw [← (hasSum_inner (single n x) a).tsum_eq, tsum_eq_single n fun k hk ↦ by simp [hk]]
  simp

/-- The orthogonal complement of the kernel of a Fourier multiplier consists of the elements whose
Fourier coefficients vanish at every frequency where the symbol vanishes. -/
theorem mem_orthogonal_ker_fourierMultiplier_iff (hp : p =O[cofinite] weight m) (h : s + m ≤ t)
    (a : CircleSobolev t F) :
    a ∈ (fourierMultiplier p hp h : CircleSobolev t F →L[ℂ] CircleSobolev s F).kerᗮ ↔
      ∀ n, p n = 0 → a.coeff n = 0 := by
  rw [Submodule.mem_orthogonal]
  refine ⟨fun ha n hn ↦ ?_, fun ha b hb ↦ ?_⟩
  · have hmem : single n (a.coeff n) ∈
        (fourierMultiplier p hp h : CircleSobolev t F →L[ℂ] CircleSobolev s F).ker := by
      simp [hn]
    have h₀ := ha _ hmem
    rw [inner_single_left, mul_eq_zero, inner_self_eq_zero] at h₀
    exact h₀.resolve_left (Complex.ofReal_ne_zero.2 (weight_pos _ n).ne')
  · have hb' := (fourierMultiplier_eq_zero_iff hp h b).1 hb
    rw [← (hasSum_inner b a).tsum_eq]
    refine (tsum_congr fun n ↦ ?_).trans tsum_zero
    by_cases hn : p n = 0
    · simp [ha n hn]
    · simp [hb' n hn]

/-- **The estimate on the orthogonal complement of the kernel.** For an elliptic symbol `p` of
order `m` and `s + m = t`, the lower-order term of `exists_norm_le_add` can be dropped on the
orthogonal complement of the kernel of `P`. -/
theorem exists_norm_le_of_mem_orthogonal_ker (hp : p =Θ[cofinite] weight m) (h : s + m = t) :
    ∃ C, ∀ a ∈ (fourierMultiplier p hp.1 h.le : CircleSobolev t F →L[ℂ] CircleSobolev s F).kerᗮ,
      ‖a‖ ≤ C * ‖fourierMultiplier p hp.1 h.le a‖ := by
  obtain ⟨C, hC⟩ := exists_norm_sub_modeProjection_le (E := F) hp h
  refine ⟨C, fun a ha ↦ ?_⟩
  have ha' := (mem_orthogonal_ker_fourierMultiplier_iff hp.1 h.le a).1 ha
  have hproj : modeProjection {n | p n = 0} a = 0 :=
    CircleSobolev.ext (funext fun n ↦ by
      by_cases hn : p n = 0 <;> simp [hn, ha' n])
  simpa [hproj] using hC a

end Inner

/-! ### Fredholm property -/

/-- An elliptic symbol with its finitely many zeros replaced by `1` is still elliptic. -/
private theorem isTheta_add_indicator (hp : p =Θ[cofinite] weight m) :
    (fun n ↦ p n + {n | p n = 0}.indicator 1 n) =Θ[cofinite] weight m := by
  have heq : p =ᶠ[cofinite] fun n ↦ p n + {n | p n = 0}.indicator 1 n :=
    (finite_setOf_eq_zero hp.2).eventually_cofinite_notMem.mono fun n hn ↦ by
      simp [Set.indicator_of_notMem hn]
  exact ⟨hp.1.congr' heq EventuallyEq.rfl, hp.2.congr' EventuallyEq.rfl heq⟩

private theorem add_indicator_ne_zero (n : ℤ) : p n + {n | p n = 0}.indicator 1 n ≠ 0 := by
  by_cases hn : p n = 0 <;> simp [hn]

private theorem isBigO_indicator_setOf_eq_zero (hp : p =Θ[cofinite] weight m) :
    {n | p n = 0}.indicator (1 : ℤ → ℂ) =O[cofinite] weight m :=
  isBigO_of_forall_notMem_eq_zero (F := (finite_setOf_eq_zero hp.2).toFinset)
    (fun n hn ↦ Set.indicator_of_notMem (by simpa using hn) _) m

/-- An elliptic multiplier is an isomorphism minus the finite-rank multiplier with the indicator
function of the zeros of its symbol. -/
private theorem fourierMultiplier_eq_sub (hp : p =Θ[cofinite] weight m) (h : s + m = t) :
    (fourierMultiplier p hp.1 h.le : CircleSobolev t E →L[ℂ] CircleSobolev s E) =
      ((fourierMultiplierEquiv (isTheta_add_indicator hp) add_indicator_ne_zero h :
          CircleSobolev t E ≃L[ℂ] CircleSobolev s E) : CircleSobolev t E →L[ℂ] _) -
        fourierMultiplier _ (isBigO_indicator_setOf_eq_zero hp) h.le :=
  ContinuousLinearMap.ext fun a ↦ CircleSobolev.ext (funext fun n ↦ by simp [add_smul])

private theorem hasFiniteRange_neg_fourierMultiplier_indicator [FiniteDimensional ℂ E]
    (hp : p =Θ[cofinite] weight m) (h : s + m = t) :
    (-fourierMultiplier _ (isBigO_indicator_setOf_eq_zero hp) h.le :
      CircleSobolev t E →L[ℂ] CircleSobolev s E).toLinearMap.HasFiniteRange := by
  rw [ContinuousLinearMap.toLinearMap_neg]
  exact (hasFiniteRange_fourierMultiplier _ _ (F := (finite_setOf_eq_zero hp.2).toFinset)
    fun n hn ↦ Set.indicator_of_notMem (by simpa using hn) _).neg

/-- A Fourier multiplier with an elliptic symbol of order `m` is a Fredholm operator
`H^t → H^s`, `s + m = t`, when `E` is finite-dimensional. -/
theorem isFredholm_fourierMultiplier [FiniteDimensional ℂ E] (hp : p =Θ[cofinite] weight m)
    (h : s + m = t) :
    (fourierMultiplier p hp.1 h.le : CircleSobolev t E →L[ℂ] CircleSobolev s E).IsFredholm := by
  rw [fourierMultiplier_eq_sub hp h, sub_eq_add_neg]
  exact (ContinuousLinearEquiv.isFredholm _).add_hasFiniteRange
    (hasFiniteRange_neg_fourierMultiplier_indicator hp h)

/-- A Fourier multiplier with an elliptic symbol has index zero. -/
theorem index_fourierMultiplier [FiniteDimensional ℂ E] (hp : p =Θ[cofinite] weight m)
    (h : s + m = t) :
    (fourierMultiplier p hp.1 h.le : CircleSobolev t E →L[ℂ] CircleSobolev s E).index = 0 := by
  rw [fourierMultiplier_eq_sub hp h, sub_eq_add_neg,
    ContinuousLinearMap.index_add_of_hasFiniteRange (ContinuousLinearEquiv.isFredholm _)
      (hasFiniteRange_neg_fourierMultiplier_indicator hp h),
    ContinuousLinearEquiv.index_eq_zero]

end CircleSobolev

end TauCeti
