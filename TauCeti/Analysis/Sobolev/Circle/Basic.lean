/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.PSeries

/-!
# Fourier-coefficient Sobolev spaces on the circle

For a real number `s` and a complex normed space `E`, the Sobolev space `H^s` of `E`-valued
functions on a circle is described through Fourier coefficients: it consists of the sequences
`a : ℤ → E` with

`‖a‖² = ∑ₙ (1 + |n|) ^ (2 s) ‖a n‖² < ∞`.

The order `s` is an arbitrary real number, so this covers the fractional and negative orders
needed for boundary traces. These spaces are the boundary function spaces on which the Hardy
decompositions of a cut Riemann surface are carried out (Robbin–Salamon).

The space is `TauCeti.CircleSobolev s E`, an extensional structure recording the coefficient
sequence `coeff`. Multiplication by the weights `(1 + |n|) ^ s` identifies it isometrically with
`ℓ²(ℤ, E)` (`CircleSobolev.toℓ2ₗᵢ`), which supplies its norm, and its completeness and inner
product when `E` has them.

## Main definitions

* `TauCeti.CircleSobolev.weight s n = (1 + |n|) ^ s`, the Sobolev weight of the frequency `n`.
* `TauCeti.CircleSobolev s E`: the Sobolev space of order `s`, with norm
  `‖a‖² = ∑ₙ weight (2 s) n * ‖a.coeff n‖²` (`CircleSobolev.hasSum_norm_sq`).
* `TauCeti.CircleSobolev.single n x`: the Fourier monomial `x e^{inθ}`.
* `TauCeti.CircleSobolev.inclusion`: the continuous inclusion `H^s → H^t` for `t ≤ s`.
* `TauCeti.CircleSobolev.toContinuousMap`: for `s > 1/2`, the continuous function on
  `AddCircle T` given by the uniformly convergent Fourier series.

## Main statements

* `TauCeti.CircleSobolev.weight_add_le`: Peetre's inequality
  `(1 + |m + n|) ^ s ≤ (1 + |m|) ^ |s| (1 + |n|) ^ s`, for every real `s`.
* `TauCeti.CircleSobolev.hasSum_single`: the Fourier series of an element converges to it in
  `H^s`, so trigonometric polynomials are dense (`CircleSobolev.dense_finite_support_coeff`).
  Continuous linear maps out of `H^s` are therefore determined by their values on Fourier
  monomials (`CircleSobolev.continuousLinearMap_ext_single`).
* `TauCeti.CircleSobolev.isCompactOperator_inclusion`: for `t < s` and finite-dimensional `E`,
  the inclusion `H^s → H^t` is compact (Rellich's theorem).
* `TauCeti.CircleSobolev.tsum_norm_coeff_le`: for `s > 1/2`, the Fourier coefficients are
  absolutely summable, with `∑ₙ ‖a.coeff n‖ ≤ (∑ₙ (1 + |n|) ^ (-2 s)) ^ (1/2) ‖a‖`.
* `TauCeti.CircleSobolev.fourierCoeff_toContinuousMap`: for `s > 1/2`, the continuous function
  attached to `a` has Fourier coefficients `a.coeff`; in particular `H^s` embeds continuously
  into the continuous functions on the circle.
* `TauCeti.CircleSobolev.toContinuousMap_equivAddCircle`: the continuous functions attached to `a`
  on circles of different lengths correspond under rescaling.

## References

* M. E. Taylor, *Partial Differential Equations I*, Chapter 3 (Sobolev spaces on the torus via
  Fourier series).
* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699 (boundary Sobolev spaces of Hardy decompositions).
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti

namespace CircleSobolev

/-- The Sobolev weight `(1 + |n|) ^ s` of the frequency `n`. -/
def weight (s : ℝ) (n : ℤ) : ℝ :=
  (1 + |(n : ℝ)|) ^ s

theorem weight_def (s : ℝ) (n : ℤ) : weight s n = (1 + |(n : ℝ)|) ^ s :=
  (rfl)

private theorem one_le_one_add_abs (n : ℤ) : 1 ≤ 1 + |(n : ℝ)| :=
  le_add_of_nonneg_right (abs_nonneg _)

theorem weight_pos (s : ℝ) (n : ℤ) : 0 < weight s n :=
  Real.rpow_pos_of_pos (zero_lt_one.trans_le (one_le_one_add_abs n)) s

theorem weight_nonneg (s : ℝ) (n : ℤ) : 0 ≤ weight s n :=
  (weight_pos s n).le

theorem norm_weight (s : ℝ) (n : ℤ) : ‖weight s n‖ = weight s n :=
  Real.norm_of_nonneg (weight_nonneg s n)

@[simp]
theorem weight_zero_left (n : ℤ) : weight 0 n = 1 :=
  Real.rpow_zero _

theorem weight_add (s t : ℝ) (n : ℤ) : weight (s + t) n = weight s n * weight t n :=
  Real.rpow_add (zero_lt_one.trans_le (one_le_one_add_abs n)) s t

theorem weight_neg (s : ℝ) (n : ℤ) : weight (-s) n = (weight s n)⁻¹ :=
  Real.rpow_neg (zero_le_one.trans (one_le_one_add_abs n)) s

theorem weight_mul_weight_neg (s : ℝ) (n : ℤ) : weight s n * weight (-s) n = 1 := by
  rw [weight_neg, mul_inv_cancel₀ (weight_pos s n).ne']

theorem one_le_weight {s : ℝ} (hs : 0 ≤ s) (n : ℤ) : 1 ≤ weight s n :=
  Real.one_le_rpow (one_le_one_add_abs n) hs

theorem weight_le_weight {s t : ℝ} (h : t ≤ s) (n : ℤ) : weight t n ≤ weight s n :=
  Real.rpow_le_rpow_of_exponent_le (one_le_one_add_abs n) h

@[simp]
theorem weight_neg_right (s : ℝ) (n : ℤ) : weight s (-n) = weight s n := by
  simp [weight_def]

private theorem weight_add_le_of_nonneg {s : ℝ} (hs : 0 ≤ s) (m n : ℤ) :
    weight s (m + n) ≤ weight s m * weight s n := by
  simp only [weight_def]
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  refine Real.rpow_le_rpow (by positivity) ?_ hs
  push_cast
  nlinarith [abs_add_le (m : ℝ) n, abs_nonneg (m : ℝ), abs_nonneg (n : ℝ)]

/-- **Peetre's inequality**: `(1 + |m + n|) ^ s ≤ (1 + |m|) ^ |s| (1 + |n|) ^ s` for every real
`s`. Shifting frequencies by `m` therefore changes the weights of every order `s` by at most the
factor `(1 + |m|) ^ |s|`. -/
theorem weight_add_le (s : ℝ) (m n : ℤ) : weight s (m + n) ≤ weight |s| m * weight s n := by
  rcases le_or_gt 0 s with hs | hs
  · rw [abs_of_nonneg hs]
    exact weight_add_le_of_nonneg hs m n
  · rw [abs_of_neg hs]
    have h := weight_add_le_of_nonneg (neg_nonneg.2 hs.le) (-m) (m + n)
    rw [neg_add_cancel_left, weight_neg_right, weight_neg, weight_neg s (m + n)] at h
    have hmn := weight_pos s (m + n)
    have hn := weight_pos s n
    rw [inv_le_iff_one_le_mul₀ hn] at h
    calc weight s (m + n) ≤ weight (-s) m * (weight s (m + n))⁻¹ * weight s n *
        weight s (m + n) := le_mul_of_one_le_left hmn.le h
      _ = weight (-s) m * weight s n := by field_simp

/-- For `s ≤ 0`, the weight at a frequency `|n| ≥ N` is at most `(1 + N) ^ s`. -/
theorem weight_le_of_le_abs {s : ℝ} (hs : s ≤ 0) {N : ℕ} {n : ℤ} (hn : (N : ℝ) ≤ |(n : ℝ)|) :
    weight s n ≤ (1 + N) ^ s :=
  Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hs

/-- The weights `(1 + |n|) ^ r` are summable over `ℤ` for `r < -1`. -/
theorem summable_weight {r : ℝ} (hr : r < -1) : Summable (weight r) := by
  refine Summable.of_norm_bounded_eventually (Real.summable_abs_int_rpow (b := -r) (by linarith)) ?_
  filter_upwards [eventually_cofinite_ne 0] with n hn
  rw [neg_neg, norm_weight]
  exact Real.rpow_le_rpow_of_nonpos (abs_pos.2 (Int.cast_ne_zero.2 hn))
    (le_add_of_nonneg_left zero_le_one) (by linarith)

/-- Exponential decay beats every polynomial weight: `∑ₙ (1 + |n|) ^ r e^{-a |n|} < ∞` for
`a > 0` and every real `r`. -/
theorem summable_weight_mul_exp_neg (r : ℝ) {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℤ ↦ weight r n * Real.exp (-(a * |(n : ℝ)|)) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, r ≤ N := ⟨⌈r⌉₊, Nat.le_ceil r⟩
  have hF : Summable fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) ^ N * Real.exp (-a * ((k + 1 : ℕ) : ℝ)) :=
    (summable_nat_add_iff 1).2 (Real.summable_pow_mul_exp_neg_nat_mul N ha)
  have hle (n : ℤ) : weight r n * Real.exp (-(a * |(n : ℝ)|)) ≤
      Real.exp a * ((1 + |(n : ℝ)|) ^ N * Real.exp (-a * (1 + |(n : ℝ)|))) := by
    have hw : weight r n ≤ (1 + |(n : ℝ)|) ^ N := by
      rw [← Real.rpow_natCast, ← weight_def]
      exact weight_le_weight hN n
    calc _ ≤ (1 + |(n : ℝ)|) ^ N * Real.exp (-(a * |(n : ℝ)|)) :=
          mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le
      _ = _ := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
  refine Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (weight_nonneg r n) (Real.exp_pos _).le)
    hle ((Summable.of_nat_of_neg
      (f := fun n : ℤ ↦ (1 + |(n : ℝ)|) ^ N * Real.exp (-a * (1 + |(n : ℝ)|))) ?_ ?_).mul_left _)
  · simpa [add_comm] using hF
  · simpa [add_comm] using hF

end CircleSobolev

open CircleSobolev in
/-- The Sobolev space `H^s` of `E`-valued functions on the circle, described by Fourier
coefficients: a sequence `coeff : ℤ → E` with `∑ₙ (1 + |n|) ^ (2 s) ‖coeff n‖² < ∞`. -/
@[ext]
structure CircleSobolev (s : ℝ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] where
  /-- The `n`-th Fourier coefficient. -/
  coeff : ℤ → E
  /-- The weighted coefficients `(1 + |n|) ^ s • coeff n` are square-summable. -/
  memℓp_weight_smul_coeff : Memℓp (fun n ↦ weight s n • coeff n) 2

namespace CircleSobolev

variable {s t : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem coeff_injective : Function.Injective (coeff : CircleSobolev s E → ℤ → E) :=
  fun _ _ ↦ CircleSobolev.ext

/-! ### The vector space structure -/

instance : Zero (CircleSobolev s E) :=
  ⟨⟨0, by simp only [Pi.zero_apply, smul_zero]; exact zero_memℓp⟩⟩

instance : Add (CircleSobolev s E) :=
  ⟨fun a b ↦ ⟨a.coeff + b.coeff, by
    convert a.memℓp_weight_smul_coeff.add b.memℓp_weight_smul_coeff using 1
    ext n
    simp [smul_add]⟩⟩

instance : Neg (CircleSobolev s E) :=
  ⟨fun a ↦ ⟨-a.coeff, by
    convert a.memℓp_weight_smul_coeff.neg using 1
    ext n
    simp⟩⟩

instance : Sub (CircleSobolev s E) :=
  ⟨fun a b ↦ ⟨a.coeff - b.coeff, by
    convert a.memℓp_weight_smul_coeff.sub b.memℓp_weight_smul_coeff using 1
    ext n
    simp [smul_sub]⟩⟩

instance : SMul ℂ (CircleSobolev s E) :=
  ⟨fun c a ↦ ⟨c • a.coeff, by
    convert a.memℓp_weight_smul_coeff.const_smul c using 1
    ext n
    simp [smul_comm _ c]⟩⟩

instance : SMul ℕ (CircleSobolev s E) :=
  ⟨fun k a ↦ (k : ℂ) • a⟩

instance : SMul ℤ (CircleSobolev s E) :=
  ⟨fun k a ↦ (k : ℂ) • a⟩

@[simp] theorem coeff_zero : (0 : CircleSobolev s E).coeff = 0 := (rfl)

@[simp] theorem coeff_add (a b : CircleSobolev s E) : (a + b).coeff = a.coeff + b.coeff := (rfl)

@[simp] theorem coeff_neg (a : CircleSobolev s E) : (-a).coeff = -a.coeff := (rfl)

@[simp] theorem coeff_sub (a b : CircleSobolev s E) : (a - b).coeff = a.coeff - b.coeff := (rfl)

@[simp] theorem coeff_smul (c : ℂ) (a : CircleSobolev s E) : (c • a).coeff = c • a.coeff := (rfl)

instance : AddCommGroup (CircleSobolev s E) :=
  coeff_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ funext fun _ ↦ Nat.cast_smul_eq_nsmul ℂ _ _)
    (fun _ _ ↦ funext fun _ ↦ Int.cast_smul_eq_zsmul ℂ _ _)

@[simp]
theorem coeff_nsmul (k : ℕ) (a : CircleSobolev s E) : (k • a).coeff = k • a.coeff :=
  funext fun _ ↦ Nat.cast_smul_eq_nsmul ℂ _ _

@[simp]
theorem coeff_zsmul (k : ℤ) (a : CircleSobolev s E) : (k • a).coeff = k • a.coeff :=
  funext fun _ ↦ Int.cast_smul_eq_zsmul ℂ _ _

instance : Module ℂ (CircleSobolev s E) :=
  coeff_injective.module ℂ ⟨⟨coeff, rfl⟩, fun _ _ ↦ rfl⟩ fun _ _ ↦ rfl

/-- The Fourier coefficient sequence, as a linear map. -/
def coeffₗ : CircleSobolev s E →ₗ[ℂ] ℤ → E where
  toFun := coeff
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)

@[simp] theorem coeffₗ_apply (a : CircleSobolev s E) : coeffₗ a = a.coeff := (rfl)

@[simp]
theorem coeff_sum {ι : Type*} (S : Finset ι) (a : ι → CircleSobolev s E) :
    (∑ i ∈ S, a i).coeff = ∑ i ∈ S, (a i).coeff :=
  map_sum coeffₗ a S

/-! ### The identification with `ℓ²` -/

/-- An element of `ℓ²(ℤ, E)` divided by the weights `(1 + |n|) ^ s` is a Fourier-coefficient
sequence of order `s`. -/
def ofℓ2 (f : lp (fun _ : ℤ ↦ E) 2) : CircleSobolev s E where
  coeff n := weight (-s) n • f n
  memℓp_weight_smul_coeff := by
    convert lp.memℓp f using 1
    ext n
    simp [smul_smul, weight_mul_weight_neg]

@[simp]
theorem coeff_ofℓ2 (f : lp (fun _ : ℤ ↦ E) 2) (n : ℤ) :
    (ofℓ2 (s := s) f).coeff n = weight (-s) n • f n :=
  (rfl)

/-- Multiplication by the weights `(1 + |n|) ^ s`, an isometric isomorphism onto `ℓ²(ℤ, E)`
(see `CircleSobolev.toℓ2ₗᵢ`). -/
def toℓ2 : CircleSobolev s E ≃ₗ[ℂ] lp (fun _ : ℤ ↦ E) 2 where
  toFun a := ⟨fun n ↦ weight s n • a.coeff n, a.memℓp_weight_smul_coeff⟩
  map_add' a b := by ext n; exact smul_add _ _ _
  map_smul' c a := by ext n; exact smul_comm _ _ _
  invFun := ofℓ2
  left_inv a := by ext n; simp [smul_smul, mul_comm (weight (-s) n), weight_mul_weight_neg]
  right_inv f := by ext n; simp [smul_smul, weight_mul_weight_neg]

@[simp]
theorem toℓ2_apply (a : CircleSobolev s E) (n : ℤ) : toℓ2 a n = weight s n • a.coeff n :=
  (rfl)

@[simp]
theorem toℓ2_symm_apply (f : lp (fun _ : ℤ ↦ E) 2) : toℓ2.symm f = ofℓ2 (s := s) f :=
  (rfl)

/-- A sequence is the coefficient sequence of an element of `H^s` exactly when its weighted
sequence is square-summable. -/
theorem exists_coeff_eq_iff (c : ℤ → E) :
    (∃ a : CircleSobolev s E, a.coeff = c) ↔ Memℓp (fun n ↦ weight s n • c n) 2 :=
  ⟨fun ⟨a, ha⟩ ↦ ha ▸ a.memℓp_weight_smul_coeff, fun h ↦ ⟨⟨c, h⟩, rfl⟩⟩

/-- A sequence lies in `H^s` exactly when its weighted norms are square-summable. -/
theorem memℓp_weight_smul_iff (c : ℤ → E) :
    Memℓp (fun n ↦ weight s n • c n) 2 ↔ Summable fun n ↦ (weight s n * ‖c n‖) ^ 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  simp [norm_smul, abs_of_nonneg (weight_nonneg s _)]

instance : NormedAddCommGroup (CircleSobolev s E) :=
  NormedAddCommGroup.induced _ _ (toℓ2 : CircleSobolev s E ≃ₗ[ℂ] _) toℓ2.injective

instance : NormedSpace ℂ (CircleSobolev s E) :=
  NormedSpace.induced ℂ _ _ (toℓ2 : CircleSobolev s E ≃ₗ[ℂ] _)

@[simp]
theorem norm_toℓ2 (a : CircleSobolev s E) : ‖toℓ2 a‖ = ‖a‖ :=
  (rfl)

/-- The isometric identification of `H^s` with `ℓ²(ℤ, E)` by the weights `(1 + |n|) ^ s`. -/
def toℓ2ₗᵢ : CircleSobolev s E ≃ₗᵢ[ℂ] lp (fun _ : ℤ ↦ E) 2 :=
  { toℓ2 with norm_map' := norm_toℓ2 }

@[simp]
theorem coe_toℓ2ₗᵢ : ⇑(toℓ2ₗᵢ : CircleSobolev s E ≃ₗᵢ[ℂ] _) = toℓ2 :=
  (rfl)

@[simp]
theorem coe_toℓ2ₗᵢ_symm : ⇑(toℓ2ₗᵢ : CircleSobolev s E ≃ₗᵢ[ℂ] _).symm = toℓ2.symm :=
  (rfl)

instance [CompleteSpace E] : CompleteSpace (CircleSobolev s E) :=
  (toℓ2ₗᵢ (s := s) (E := E)).toIsometryEquiv.completeSpace_iff.2 inferInstance

/-- The squared norm of `H^s` is the sum of the squared weighted coefficient norms. -/
theorem hasSum_sq_weight_mul_norm_coeff (a : CircleSobolev s E) :
    HasSum (fun n ↦ (weight s n * ‖a.coeff n‖) ^ 2) (‖a‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (toℓ2 a)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, toℓ2_apply, norm_smul,
    norm_weight, norm_toℓ2] using h

/-- The squared norm of `H^s` is `∑ₙ (1 + |n|) ^ (2 s) ‖a.coeff n‖²`. -/
theorem hasSum_norm_sq (a : CircleSobolev s E) :
    HasSum (fun n ↦ weight (2 * s) n * ‖a.coeff n‖ ^ 2) (‖a‖ ^ 2) := by
  convert hasSum_sq_weight_mul_norm_coeff a using 2 with n
  rw [two_mul, weight_add]
  ring

theorem norm_sq_eq_tsum (a : CircleSobolev s E) :
    ‖a‖ ^ 2 = ∑' n, weight (2 * s) n * ‖a.coeff n‖ ^ 2 :=
  (hasSum_norm_sq a).tsum_eq.symm

/-- A coefficientwise bound of weighted norms gives the corresponding bound on the norms, possibly
between different orders. -/
theorem norm_le_of_forall_le {a : CircleSobolev s E} {b : CircleSobolev t E} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ n, weight t n * ‖b.coeff n‖ ≤ C * (weight s n * ‖a.coeff n‖)) :
    ‖b‖ ≤ C * ‖a‖ := by
  have hle : ‖b‖ ^ 2 ≤ (C * ‖a‖) ^ 2 := by
    rw [mul_pow]
    refine hasSum_le (fun n ↦ ?_) (hasSum_sq_weight_mul_norm_coeff b)
      ((hasSum_sq_weight_mul_norm_coeff a).mul_left (C ^ 2))
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg (weight_nonneg t n) (norm_nonneg _)) (h n) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hle

/-- The `n`-th Fourier coefficient of an element of `H^s` is bounded by `(1 + |n|) ^ (-s)` times
its norm. -/
theorem norm_coeff_le (a : CircleSobolev s E) (n : ℤ) : ‖a.coeff n‖ ≤ weight (-s) n * ‖a‖ := by
  have h := lp.norm_apply_le_norm (by norm_num) (toℓ2 a) n
  rw [toℓ2_apply, norm_smul, norm_weight, norm_toℓ2] at h
  rw [weight_neg, le_inv_mul_iff₀ (weight_pos s n)]
  exact h

/-- The `n`-th Fourier coefficient is a continuous linear functional on `H^s`. -/
def coeffCLM (n : ℤ) : CircleSobolev s E →L[ℂ] E :=
  (LinearMap.proj n ∘ₗ coeffₗ).mkContinuous (weight (-s) n) fun a ↦ norm_coeff_le a n

@[simp]
theorem coeffCLM_apply (n : ℤ) (a : CircleSobolev s E) : coeffCLM n a = a.coeff n :=
  (rfl)

theorem opNorm_coeffCLM_le (n : ℤ) : ‖(coeffCLM n : CircleSobolev s E →L[ℂ] E)‖ ≤ weight (-s) n :=
  ContinuousLinearMap.opNorm_le_bound _ (weight_nonneg (-s) n) fun a ↦ norm_coeff_le a n

/-- A sequence whose weighted norms of order `t` are bounded by a multiple of the weighted norms of
order `s` of an element of `H^s` is the coefficient sequence of an element of `H^t`. -/
theorem memℓp_of_forall_le {a : CircleSobolev s E} {c : ℤ → E} {C : ℝ}
    (h : ∀ n, weight t n * ‖c n‖ ≤ C * (weight s n * ‖a.coeff n‖)) :
    Memℓp (fun n ↦ weight t n • c n) 2 := by
  refine (a.memℓp_weight_smul_coeff.const_smul C).mono' fun n ↦ ?_
  rw [Pi.smul_apply, norm_smul, norm_smul, norm_smul, norm_weight, norm_weight, Real.norm_eq_abs]
  exact (h n).trans
    (mul_le_mul_of_nonneg_right (le_abs_self C) (mul_nonneg (weight_nonneg s n) (norm_nonneg _)))

/-! ### Hilbert structure -/

section Inner

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

instance : InnerProductSpace ℂ (CircleSobolev s F) :=
  InnerProductSpace.induced (toℓ2 : CircleSobolev s F ≃ₗ[ℂ] _)

@[simp]
theorem inner_toℓ2 (a b : CircleSobolev s F) : inner ℂ (toℓ2 a) (toℓ2 b) = inner ℂ a b :=
  (rfl)

/-- The inner product of `H^s` is `∑ₙ (1 + |n|) ^ (2 s) ⟪a.coeff n, b.coeff n⟫`. -/
theorem hasSum_inner (a b : CircleSobolev s F) :
    HasSum (fun n ↦ (weight (2 * s) n : ℂ) * inner ℂ (a.coeff n) (b.coeff n)) (inner ℂ a b) := by
  convert lp.hasSum_inner (toℓ2 a) (toℓ2 b) using 1
  · ext n
    simp only [toℓ2_apply, two_mul, weight_add, ← Complex.coe_smul, inner_smul_left,
      inner_smul_right, Complex.conj_ofReal, Complex.ofReal_mul]
    ring

theorem inner_eq_tsum (a b : CircleSobolev s F) :
    inner ℂ a b = ∑' n, (weight (2 * s) n : ℂ) * inner ℂ (a.coeff n) (b.coeff n) :=
  (hasSum_inner a b).tsum_eq.symm

end Inner

/-! ### Fourier monomials and density of trigonometric polynomials -/

/-- The weighted coefficients of the Fourier monomial `x e^{inθ}` form the `ℓ²` monomial
`(1 + |n|) ^ s • x` at `n`. -/
private theorem weight_smul_piSingle (n m : ℤ) (x : E) :
    weight s m • Pi.single (M := fun _ : ℤ ↦ E) n x m =
      lp.single (E := fun _ : ℤ ↦ E) 2 n (weight s n • x) m := by
  rcases eq_or_ne m n with rfl | hm
  · simp
  · simp [hm]

/-- The Fourier monomial `x e^{inθ}` in `H^s`, as a linear map in `x`. -/
private def singleₗ (n : ℤ) : E →ₗ[ℂ] CircleSobolev s E where
  toFun x := ⟨Pi.single n x, by
    convert lp.memℓp (lp.single (E := fun _ : ℤ ↦ E) 2 n (weight s n • x)) using 1
    exact funext fun m ↦ weight_smul_piSingle n m x⟩
  map_add' x y := CircleSobolev.ext (Pi.single_add (f := fun _ : ℤ ↦ E) n x y)
  map_smul' c x := CircleSobolev.ext (Pi.single_smul' n c x)

private theorem toℓ2_singleₗ (n : ℤ) (x : E) :
    toℓ2 (singleₗ (s := s) n x) = lp.single 2 n (weight s n • x) :=
  lp.ext (funext fun m ↦ weight_smul_piSingle n m x)

private theorem norm_singleₗ (n : ℤ) (x : E) : ‖singleₗ (s := s) n x‖ = weight s n * ‖x‖ := by
  rw [← norm_toℓ2, toℓ2_singleₗ, lp.norm_single (by norm_num), norm_smul, norm_weight]

/-- The Fourier monomial `x e^{inθ}` in `H^s`, as a continuous linear map in `x`. -/
def single (n : ℤ) : E →L[ℂ] CircleSobolev s E :=
  (singleₗ n).mkContinuous (weight s n) fun x ↦ (norm_singleₗ n x).le

@[simp]
theorem coeff_single (n : ℤ) (x : E) : (single (s := s) n x).coeff = Pi.single n x :=
  (rfl)

@[simp]
theorem toℓ2_single (n : ℤ) (x : E) :
    toℓ2 (single (s := s) n x) = lp.single 2 n (weight s n • x) :=
  toℓ2_singleₗ n x

@[simp]
theorem norm_single (n : ℤ) (x : E) : ‖single (s := s) n x‖ = weight s n * ‖x‖ :=
  norm_singleₗ n x

/-- The Fourier series of an element of `H^s` converges to it in `H^s`. -/
theorem hasSum_single (a : CircleSobolev s E) : HasSum (fun n ↦ single n (a.coeff n)) a := by
  have h := (lp.hasSum_single (p := 2) (by norm_num) (toℓ2 a)).mapL
    ((toℓ2ₗᵢ (s := s) (E := E)).symm.toContinuousLinearEquiv : _ →L[ℂ] CircleSobolev s E)
  convert h using 1
  · funext n
    apply toℓ2.injective
    simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      coe_toℓ2ₗᵢ_symm, LinearEquiv.apply_symm_apply, toℓ2_apply, toℓ2_single]
  · simp

/-- Continuous linear maps out of `H^s` are determined by their values on the Fourier monomials. -/
theorem continuousLinearMap_ext_single {F : Type*} [AddCommMonoid F] [Module ℂ F]
    [TopologicalSpace F] [T2Space F] {f g : CircleSobolev s E →L[ℂ] F}
    (h : ∀ n x, f (single n x) = g (single n x)) : f = g :=
  ContinuousLinearMap.ext fun a ↦
    ((hasSum_single a).mapL f).unique (by simpa only [h] using (hasSum_single a).mapL g)

/-- Trigonometric polynomials, the elements of `H^s` with finitely many nonzero Fourier
coefficients, are dense in `H^s`. -/
theorem dense_finite_support_coeff :
    Dense {a : CircleSobolev s E | (Function.support a.coeff).Finite} := by
  refine fun a ↦ mem_closure_of_tendsto (hasSum_single a) (Eventually.of_forall fun S ↦ ?_)
  refine S.finite_toSet.subset fun m hm ↦ ?_
  by_contra hmS
  refine hm ?_
  simp [Finset.sum_apply, Pi.single_apply, Finset.mem_coe.not.1 hmS]

/-! ### Inclusions between the Sobolev spaces -/

private theorem weight_mul_norm_le_of_le (h : t ≤ s) (a : CircleSobolev s E) (n : ℤ) :
    weight t n * ‖a.coeff n‖ ≤ 1 * (weight s n * ‖a.coeff n‖) := by
  rw [one_mul]
  exact mul_le_mul_of_nonneg_right (weight_le_weight h n) (norm_nonneg _)

/-- The continuous inclusion `H^s → H^t` for `t ≤ s`, which keeps the Fourier coefficients. -/
def inclusion (h : t ≤ s) : CircleSobolev s E →L[ℂ] CircleSobolev t E :=
  LinearMap.mkContinuous
    { toFun a := ⟨a.coeff, memℓp_of_forall_le (weight_mul_norm_le_of_le h a)⟩
      map_add' _ _ := (rfl)
      map_smul' _ _ := (rfl) }
    1 fun a ↦ norm_le_of_forall_le zero_le_one (weight_mul_norm_le_of_le h a)

@[simp]
theorem coeff_inclusion (h : t ≤ s) (a : CircleSobolev s E) :
    (inclusion h a).coeff = a.coeff := by
  simp [inclusion]

@[simp]
theorem inclusion_refl (a : CircleSobolev s E) : inclusion le_rfl a = a :=
  CircleSobolev.ext (by simp)

@[simp]
theorem inclusion_inclusion {u : ℝ} (h₁ : u ≤ t) (h₂ : t ≤ s) (a : CircleSobolev s E) :
    inclusion h₁ (inclusion h₂ a) = inclusion (h₁.trans h₂) a :=
  CircleSobolev.ext (by simp)

@[simp]
theorem inclusion_single (h : t ≤ s) (n : ℤ) (x : E) :
    inclusion h (single n x) = single n x :=
  CircleSobolev.ext (by simp)

theorem inclusion_injective (h : t ≤ s) :
    Function.Injective (inclusion (E := E) h) :=
  fun _ _ hab ↦ CircleSobolev.ext (by simpa using congr_arg coeff hab)

theorem norm_inclusion_le (h : t ≤ s) (a : CircleSobolev s E) : ‖inclusion h a‖ ≤ ‖a‖ := by
  simpa using norm_le_of_forall_le (a := a) (b := inclusion h a) zero_le_one
    (by simpa using weight_mul_norm_le_of_le h a)

/-- **Rellich's theorem** on the circle: the inclusion `H^s → H^t` is a compact operator for
`t < s` when `E` is finite-dimensional. -/
theorem isCompactOperator_inclusion [FiniteDimensional ℂ E] (h : t < s) :
    IsCompactOperator (inclusion (E := E) h.le) := by
  have := FiniteDimensional.complete ℂ E
  have := FiniteDimensional.proper ℂ E
  -- The inclusion is the operator-norm limit of the truncations `F N` of the Fourier series to the
  -- frequencies `|n| ≤ N`, which factor through finitely many copies of `E`.
  set F : ℕ → CircleSobolev s E →L[ℂ] CircleSobolev t E :=
    fun N ↦ ∑ n ∈ Finset.Icc (-(N : ℤ)) N, (single n).comp (coeffCLM n) with hF
  refine isCompactOperator_of_tendsto (l := atTop) (F := F) ?_ (Eventually.of_forall fun N ↦ ?_)
  · have hlim : Tendsto (fun N : ℕ ↦ (1 + (N : ℝ)) ^ (t - s)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (tendsto_rpow_neg_atTop (sub_pos.2 h)).comp
        (tendsto_atTop_add_const_left _ 1 tendsto_natCast_atTop_atTop)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun N ↦ ?_) hlim
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a ↦ ?_
    refine norm_le_of_forall_le (by positivity) fun m ↦ ?_
    have hw : 0 ≤ weight s m * ‖a.coeff m‖ := mul_nonneg (weight_nonneg s m) (norm_nonneg _)
    by_cases hm : m ∈ Finset.Icc (-(N : ℤ)) N
    · simp [hF, Finset.sum_apply, Pi.single_apply, hm,
        mul_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + N) (t - s)) hw]
    · have hN : (N : ℝ) ≤ |(m : ℝ)| := by
        rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hm
        rw [← Int.cast_natCast, ← Int.cast_abs, Int.cast_le, le_abs]
        omega
      have hcoeff :
          ((F N - inclusion h.le : CircleSobolev s E →L[ℂ] CircleSobolev t E) a).coeff m =
            -a.coeff m := by
        simp [hF, Finset.sum_apply, Pi.single_apply, hm]
      have hweight : weight t m = weight (t - s) m * weight s m := by
        rw [← weight_add, sub_add_cancel]
      rw [hcoeff, norm_neg, hweight, mul_assoc]
      exact mul_le_mul_of_nonneg_right (weight_le_of_le_abs (by linarith) hN) hw
  · refine Finset.sum_induction _ (fun G : CircleSobolev s E →L[ℂ] CircleSobolev t E ↦
      IsCompactOperator G) (fun G G' hG hG' ↦ ?_) ?_ fun n _ ↦ ?_
    · simpa using hG.add hG'
    · simpa using isCompactOperator_zero
    · rw [ContinuousLinearMap.coe_comp]
      exact (isCompactOperator_of_locallyCompactSpace_dom (coeffCLM n)).clm_comp (single n)

/-! ### Absolute convergence and continuity for `s > 1/2` -/

private theorem summable_norm_coeff_and_tsum_le (hs : 1 / 2 < s) (a : CircleSobolev s E) :
    Summable (fun n ↦ ‖a.coeff n‖) ∧
      ∑' n, ‖a.coeff n‖ ≤ √(∑' n, weight (-(2 * s)) n) * ‖a‖ := by
  have hsq (n : ℤ) : weight (-s) n ^ (2 : ℝ) = weight (-(2 * s)) n := by
    rw [Real.rpow_two, sq, ← weight_add]
    ring_nf
  have hf : Summable fun n ↦ weight (-s) n ^ (2 : ℝ) := by
    simpa only [hsq] using summable_weight (r := -(2 * s)) (by linarith)
  have hg := hasSum_sq_weight_mul_norm_coeff a
  simp only [← Real.rpow_two] at hg
  obtain ⟨h₁, h₂⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two (fun n ↦ weight_nonneg (-s) n)
    (fun n ↦ mul_nonneg (weight_nonneg s n) (norm_nonneg _)) hf hg.summable
  have key (n : ℤ) : weight (-s) n * (weight s n * ‖a.coeff n‖) = ‖a.coeff n‖ := by
    rw [← mul_assoc, mul_comm (weight (-s) n), weight_mul_weight_neg, one_mul]
  simp only [key] at h₁ h₂
  refine ⟨h₁, h₂.trans_eq ?_⟩
  rw [hg.tsum_eq, tsum_congr hsq, ← Real.rpow_mul (norm_nonneg _), Real.sqrt_eq_rpow]
  norm_num

/-- For `s > 1/2` the Fourier coefficients of an element of `H^s` are absolutely summable. -/
theorem summable_norm_coeff (hs : 1 / 2 < s) (a : CircleSobolev s E) :
    Summable fun n ↦ ‖a.coeff n‖ :=
  (summable_norm_coeff_and_tsum_le hs a).1

/-- For `s > 1/2`, the `ℓ¹` norm of the Fourier coefficients is bounded by the `H^s` norm:
`∑ₙ ‖a.coeff n‖ ≤ (∑ₙ (1 + |n|) ^ (-2 s)) ^ (1/2) ‖a‖`. -/
theorem tsum_norm_coeff_le (hs : 1 / 2 < s) (a : CircleSobolev s E) :
    ∑' n, ‖a.coeff n‖ ≤ √(∑' n, weight (-(2 * s)) n) * ‖a‖ :=
  (summable_norm_coeff_and_tsum_le hs a).2

section Continuous

variable (T : ℝ) [Fact (0 < T)]

private theorem summable_norm_fourier_smul_const_and_tsum_le (hs : 1 / 2 < s)
    (a : CircleSobolev s E) :
    Summable (fun n ↦ ‖fourier (T := T) n • ContinuousMap.const (AddCircle T) (a.coeff n)‖) ∧
      ∑' n, ‖fourier (T := T) n • ContinuousMap.const (AddCircle T) (a.coeff n)‖ ≤
        √(∑' n, weight (-(2 * s)) n) * ‖a‖ := by
  simp only [ContinuousMap.norm_smul_const, fourier_norm, one_mul]
  exact summable_norm_coeff_and_tsum_le hs a

private theorem norm_tsum_fourier_smul_const_le (hs : 1 / 2 < s) (a : CircleSobolev s E) :
    ‖∑' n, fourier (T := T) n • ContinuousMap.const (AddCircle T) (a.coeff n)‖ ≤
      √(∑' n, weight (-(2 * s)) n) * ‖a‖ :=
  have h := summable_norm_fourier_smul_const_and_tsum_le T hs a
  (norm_tsum_le_tsum_norm h.1).trans h.2

variable [CompleteSpace E]

private theorem summable_fourier_smul_const (hs : 1 / 2 < s) (a : CircleSobolev s E) :
    Summable fun n ↦ fourier (T := T) n • ContinuousMap.const (AddCircle T) (a.coeff n) :=
  (summable_norm_fourier_smul_const_and_tsum_le T hs a).1.of_norm

/-- For `s > 1/2`, the continuous function on `AddCircle T` attached to an element of `H^s`:
the sum of its uniformly convergent Fourier series `∑ₙ a.coeff n e^{2πinx/T}`. -/
def toContinuousMap (hs : 1 / 2 < s) : CircleSobolev s E →L[ℂ] C(AddCircle T, E) :=
  LinearMap.mkContinuous
    { toFun a := ∑' n, fourier (T := T) n • ContinuousMap.const (AddCircle T) (a.coeff n)
      map_add' a b := by
        rw [← (summable_fourier_smul_const T hs a).tsum_add (summable_fourier_smul_const T hs b)]
        congr 1 with n
        simp [ContinuousMap.smul_apply', smul_add]
      map_smul' c a := by
        rw [RingHom.id_apply, ← (summable_fourier_smul_const T hs a).tsum_const_smul c]
        congr 1 with n
        simp [ContinuousMap.smul_apply', smul_comm c] }
    (√(∑' n, weight (-(2 * s)) n)) (norm_tsum_fourier_smul_const_le T hs)

/-- The Fourier series of an element of `H^s`, `s > 1/2`, converges uniformly to its continuous
function. -/
theorem hasSum_toContinuousMap (hs : 1 / 2 < s) (a : CircleSobolev s E) :
    HasSum (fun n ↦ fourier (T := T) n • ContinuousMap.const (AddCircle T) (a.coeff n))
      (toContinuousMap T hs a) := by
  simpa [toContinuousMap] using (summable_fourier_smul_const T hs a).hasSum

theorem toContinuousMap_apply (hs : 1 / 2 < s) (a : CircleSobolev s E) (x : AddCircle T) :
    toContinuousMap T hs a x = ∑' n, fourier n x • a.coeff n :=
  (((hasSum_toContinuousMap T hs a).mapL (ContinuousMap.evalCLM ℂ x)).tsum_eq).symm

theorem norm_toContinuousMap_le (hs : 1 / 2 < s) (a : CircleSobolev s E) :
    ‖toContinuousMap T hs a‖ ≤ √(∑' n, weight (-(2 * s)) n) * ‖a‖ := by
  rw [← (hasSum_toContinuousMap T hs a).tsum_eq]
  exact norm_tsum_fourier_smul_const_le T hs a

@[simp]
theorem toContinuousMap_single (hs : 1 / 2 < s) (n : ℤ) (x : E) :
    toContinuousMap T hs (single n x) =
      fourier (T := T) n • ContinuousMap.const (AddCircle T) x := by
  rw [← (hasSum_toContinuousMap T hs (single n x)).tsum_eq, tsum_eq_single n fun m hm ↦ by
    simp [hm]]
  simp

/-- For `1/2 < t ≤ s`, the continuous function attached to `a ∈ H^s` does not depend on whether
`a` is regarded as an element of `H^s` or of `H^t`. -/
@[simp]
theorem toContinuousMap_inclusion (ht : 1 / 2 < t) (h : t ≤ s) (a : CircleSobolev s E) :
    toContinuousMap T ht (inclusion h a) = toContinuousMap T (ht.trans_le h) a :=
  (hasSum_toContinuousMap T ht (inclusion h a)).unique
    (by simpa using hasSum_toContinuousMap T (ht.trans_le h) a)

/-- For `s > 1/2`, the continuous function attached to `a ∈ H^s` has Fourier coefficients
`a.coeff`. -/
@[simp]
theorem fourierCoeff_toContinuousMap (hs : 1 / 2 < s) (a : CircleSobolev s E) (n : ℤ) :
    fourierCoeff (toContinuousMap T hs a) n = a.coeff n := by
  have hint (m : ℤ) : MeasureTheory.Integrable
      (fun x ↦ fourier (-n) x • fourier m x • a.coeff m) AddCircle.haarAddCircle :=
    (by fun_prop : Continuous fun x : AddCircle T ↦ fourier (-n) x • fourier m x • a.coeff m)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnorm (m : ℤ) : ∫ x, ‖fourier (T := T) (-n) x • fourier m x • a.coeff m‖
      ∂AddCircle.haarAddCircle = ‖a.coeff m‖ := by
    simp [norm_smul, fourier_apply]
  have hterm (m : ℤ) : ∫ x, fourier (T := T) (-n) x • fourier m x • a.coeff m
      ∂AddCircle.haarAddCircle = (Pi.single (M := fun _ : ℤ ↦ ℂ) m 1 n) • a.coeff m := by
    rw [← fourierCoeff_fourier (T := T) m, fourierCoeff, ← integral_smul_const]
    simp_rw [smul_assoc]
  have hsmul (x : AddCircle T) : fourier (-n) x • toContinuousMap T hs a x =
      ∑' m, fourier (-n) x • fourier m x • a.coeff m := by
    rw [toContinuousMap_apply, Summable.tsum_const_smul]
    exact (summable_norm_coeff hs a).of_norm_bounded fun m ↦ by simp [norm_smul, fourier_apply]
  rw [fourierCoeff, funext hsmul, ← MeasureTheory.integral_tsum_of_summable_integral_norm hint
    (by simpa only [hnorm] using summable_norm_coeff hs a), tsum_congr hterm,
    tsum_eq_single n fun m hm ↦ by simp [Ne.symm hm]]
  simp

theorem toContinuousMap_injective (hs : 1 / 2 < s) :
    Function.Injective (toContinuousMap (E := E) T hs) := fun a b hab ↦
  CircleSobolev.ext <| funext fun n ↦ by
    rw [← fourierCoeff_toContinuousMap T hs a, hab, fourierCoeff_toContinuousMap]

/-- For `s > 1/2`, the continuous representatives of `a ∈ H^s` on circles of different lengths
correspond under the rescaling `AddCircle.equivAddCircle`. -/
@[simp]
theorem toContinuousMap_equivAddCircle (T' : ℝ) [hT' : Fact (0 < T')] (hs : 1 / 2 < s)
    (a : CircleSobolev s E) (x : AddCircle T) :
    toContinuousMap T' hs a
        (AddCircle.equivAddCircle T T' (Fact.out : 0 < T).ne' hT'.out.ne' x) =
      toContinuousMap T hs a x := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hT : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Fact.out : 0 < T).ne'
  have hT'c : (T' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hT'.out.ne'
  rw [AddCircle.equivAddCircle_apply_mk, toContinuousMap_apply,
    toContinuousMap_apply]
  refine tsum_congr fun n ↦ ?_
  rw [fourier_coe_apply, fourier_coe_apply]
  congr 2
  push_cast
  field_simp

/-- For `s > 1/2` and an open set `U`, the elements of `H^s` whose continuous representatives take
values in `U` form an open subset of `H^s`. -/
theorem isOpen_setOf_forall_toContinuousMap_mem (hs : 1 / 2 < s) {U : Set E} (hU : IsOpen U) :
    IsOpen {a : CircleSobolev s E | ∀ x, toContinuousMap T hs a x ∈ U} := by
  simpa [Set.MapsTo] using (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ hU).preimage
    (toContinuousMap T hs).continuous

end Continuous

end CircleSobolev

end TauCeti
