/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.NumberTheory.Padics.AnnularRing.Basic
public import TauCeti.RingTheory.Huber.LocalizationTopology.Away
import Mathlib.NumberTheory.Padics.RingHoms
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The `T`-adic completeness of `ℤ_p⟦T, p/T⟧` and its localization `H[1/T]`

Let `H = TauCeti.AnnularRing p` be the integral annular coefficient ring `ℤ_p⟦T, p/T⟧`.
Multiplication by `T ^ n` shifts the normal form up by `n` degrees, so `x ∈ H` is divisible by
`T ^ n` exactly when its coefficients satisfy `‖x.coeff m‖ ≤ p ^ min 0 (m - n)` for all `m ∈ ℤ`.
From this criterion we deduce that `H` is `(T)`-adically (and hence `(p, T)`-adically, since
`(p, T) = (T)`) separated and complete (`IsAdicComplete (Ideal.span {T}) (AnnularRing p)`).

For any localization `A` of `H` away from `T`, writing `x * T ^ k = a` with `a ∈ H` assigns to
`x ∈ A` a well-defined two-sided coefficient family `localizedCoeff x : ℤ → ℤ_p` given by
`localizedCoeff x m = a.coeff (m + k)`. This identifies `A = H[1/T]` with the two-sided formal
series `∑_{m ∈ ℤ} d_m T ^ m` with `d_m ∈ ℤ_p` satisfying the shifted valuation bound
`v_p(d_m) ≥ max(0, -m - k)` for some `k : ℕ`, stated in norm form as
`‖d_m‖ ≤ p ^ min 0 (m + k)` (`TauCeti.AnnularRing.existsUnique_localizedCoeff_eq_iff`;
`TauCeti.AnnularRing.norm_le_zpow_min_iff_pow_dvd` translates this into divisibility by powers of
`p`). The product in `A` is again given coefficientwise by the `p`-adically convergent convolution
series, and the `T`-adic filtration `T ^ n H` is characterized by
`‖localizedCoeff x m‖ ≤ p ^ min 0 (m - n)`.

## Main definitions

* `TauCeti.AnnularRing.localizedCoeff`: the coefficient family `ℤ → ℤ_p` of an element of any
  localization `A` of `AnnularRing p` away from `T`.

## Main results

* `TauCeti.AnnularRing.T_pow_dvd_iff`: `T ^ n ∣ x ↔ ∀ m, ‖x.coeff m‖ ≤ p ^ min 0 (m - n)`.
* `TauCeti.AnnularRing.T_not_dvd_U_pow`: no power `U ^ j` is divisible by `T` in `H`.
* `TauCeti.AnnularRing.instIsAdicCompleteSpanT`, `TauCeti.AnnularRing.isAdicComplete_span_p_T`:
  `H` is `(T)`-adically and `(p, T)`-adically complete.
* `TauCeti.AnnularRing.localizedCoeff_injective`, `TauCeti.AnnularRing.localizedCoeff_mul`:
  coefficients determine elements of `H[1/T]` and multiply by convolution.
* `TauCeti.AnnularRing.existsUnique_localizedCoeff_eq_iff`: the coefficient criterion
  `‖d m‖ ≤ p ^ min 0 (m + k)` characterizing `H[1/T]`.
* `TauCeti.AnnularRing.T_zpow_neg_mul_mem_range_iff`,
  `TauCeti.AnnularRing.mem_awayNhd_iff_norm_localizedCoeff_le`: coefficient description of the
  `T`-adic filtration `T ^ n H` in `H[1/T]`.

## References

* R. Liu, D. Wan and L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J.
  166 (2017), §§2–3.
-/

public noncomputable section

open Filter Topology

namespace TauCeti.AnnularRing

variable {p : ℕ} [Fact p.Prime]

private theorem one_lt_p : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt

/-! ### Divisibility by powers of `T` and `T`-adic completeness of `H` -/

/-- Multiplication by `T ^ n` shifts the normal form up by `n` degrees. -/
@[simp] theorem coeff_T_pow_mul (n : ℕ) (x : AnnularRing p) (m : ℤ) :
    (T ^ n * x).coeff m = x.coeff (m - n) := by
  rw [coeff_mul_of_coeff_eq_zero (k := (n : ℤ)) fun i hi ↦ by simp [coeff_T_pow, hi]]
  simp [coeff_T_pow]

/-- An element of `AnnularRing p` is divisible by `T ^ n` exactly when its coefficients satisfy
`‖x.coeff m‖ ≤ p ^ min 0 (m - n)` for every `m ∈ ℤ`. -/
theorem T_pow_dvd_iff {n : ℕ} {x : AnnularRing p} :
    (T : AnnularRing p) ^ n ∣ x ↔ ∀ m : ℤ, ‖x.coeff m‖ ≤ (p : ℝ) ^ min 0 (m - n) := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨y, rfl⟩ m
    rw [coeff_T_pow_mul]
    exact y.norm_coeff_le (m - n)
  · refine ⟨⟨fun m ↦ x.coeff (m + n), fun m ↦ ?_⟩, ?_⟩
    · simpa [add_sub_cancel_right] using h (m + n)
    · ext m : 2
      simp [coeff_T_pow_mul]

/-- An element of `AnnularRing p` is divisible by `T` exactly when its coefficients satisfy
`‖x.coeff m‖ ≤ p ^ min 0 (m - 1)` for every `m ∈ ℤ`. -/
theorem T_dvd_iff {x : AnnularRing p} :
    (T : AnnularRing p) ∣ x ↔ ∀ m : ℤ, ‖x.coeff m‖ ≤ (p : ℝ) ^ min 0 (m - 1) := by
  simpa using T_pow_dvd_iff (p := p) (n := 1) (x := x)

/-- No power `U ^ j` is divisible by `T` in `AnnularRing p`: its degree `-j` coefficient is `p ^ j`,
which has norm `p ^ (-j) > p ^ (-j - 1)`. -/
theorem T_not_dvd_U_pow (j : ℕ) : ¬(T : AnnularRing p) ∣ U ^ j := by
  intro h
  have hle := T_dvd_iff.mp h (-(j : ℤ))
  rw [coeff_U_pow, ite_eq_left rfl, PadicInt.norm_p_pow, min_eq_right (by omega)] at hle
  have hlt : (p : ℝ) ^ (-(j : ℤ) - 1) < (p : ℝ) ^ (-(j : ℤ)) :=
    (zpow_lt_zpow_iff_right₀ (one_lt_p (p := p))).2 (by omega)
  exact hlt.not_ge hle

/-- Congruence modulo `(T) ^ n` in `AnnularRing p` is equivalent to the shifted coefficient bound
on the difference. -/
private theorem smodEq_span_T_pow_iff {n : ℕ} {x y : AnnularRing p} :
    x ≡ y [SMOD (Ideal.span {(T : AnnularRing p)} ^ n • ⊤ :
      Submodule (AnnularRing p) (AnnularRing p))] ↔
      ∀ m : ℤ, ‖x.coeff m - y.coeff m‖ ≤ (p : ℝ) ^ min 0 (m - n) := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, T_pow_dvd_iff]
  simp only [coeff_sub]

/-- For fixed `m : ℤ`, `min 0 (m - n)` tends to `-∞` as `n → ∞`. -/
private theorem tendsto_min_zero_sub_nat (m : ℤ) :
    Tendsto (fun n : ℕ ↦ min (0 : ℤ) (m - n)) atTop atBot :=
  tendsto_atBot.2 fun N ↦ eventually_atTop.2 ⟨(m - N).toNat, fun n hn ↦ by omega⟩

/-- `AnnularRing p` is `(T)`-adically separated. -/
instance instIsHausdorffSpanT : IsHausdorff (Ideal.span {(T : AnnularRing p)}) (AnnularRing p) := by
  refine ⟨fun x hx ↦ AnnularRing.ext <| funext fun m ↦ ?_⟩
  have hle (n : ℕ) : ‖x.coeff m‖ ≤ (p : ℝ) ^ min 0 (m - n) := by
    simpa using (smodEq_span_T_pow_iff.mp (hx n)) m
  have ht : Tendsto (fun _ : ℕ ↦ x.coeff m) atTop (𝓝 0) :=
    tendsto_zero_of_norm_le_zpow (one_lt_p (p := p)) hle (tendsto_min_zero_sub_nat m)
  exact tendsto_const_nhds_iff.mp ht

/-- `AnnularRing p` is `(T)`-adically precomplete: a `(T)`-adically Cauchy sequence converges
coefficientwise in `ℤ_p` to an element of `AnnularRing p`. -/
instance instIsPrecompleteSpanT :
    IsPrecomplete (Ideal.span {(T : AnnularRing p)}) (AnnularRing p) := by
  refine ⟨fun f hf ↦ ?_⟩
  have hdiff {i j : ℕ} (hij : i ≤ j) (m : ℤ) :
      ‖(f i).coeff m - (f j).coeff m‖ ≤ (p : ℝ) ^ min 0 (m - i) :=
    smodEq_span_T_pow_iff.mp (hf hij) m
  -- Each coefficient sequence `n ↦ (f n).coeff m` is Cauchy in `ℤ_p`, hence converges.
  have hconv (m : ℤ) : ∃ c : ℤ_[p], Tendsto (fun n ↦ (f n).coeff m) atTop (𝓝 c) := by
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.2 fun ε hε ↦ ?_)
    have hlim : Tendsto (fun n : ℕ ↦ (p : ℝ) ^ min (0 : ℤ) (m - n)) atTop (𝓝 0) :=
      tendsto_zero_of_norm_le_zpow (one_lt_p (p := p))
        (fun n ↦ by rw [Real.norm_of_nonneg (by positivity)]) (tendsto_min_zero_sub_nat m)
    obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [dist_eq_norm, norm_sub_rev]
    exact (hdiff hn m).trans_lt hN
  choose c hc using hconv
  refine ⟨⟨c, fun m ↦ le_of_tendsto (hc m).norm (Eventually.of_forall fun n ↦
    (f n).norm_coeff_le m)⟩, fun i ↦ smodEq_span_T_pow_iff.mpr fun m ↦ ?_⟩
  refine le_of_tendsto ((tendsto_const_nhds.sub (hc m)).norm) ?_
  filter_upwards [eventually_ge_atTop i] with n hn
  exact hdiff hn m

/-- `AnnularRing p` is `(T)`-adically complete. -/
instance instIsAdicCompleteSpanT :
    IsAdicComplete (Ideal.span {(T : AnnularRing p)}) (AnnularRing p) := {}

/-- `AnnularRing p` is `(p, T)`-adically complete, since `(p, T) = (T)`. -/
theorem isAdicComplete_span_p_T :
    IsAdicComplete (Ideal.span {(p : AnnularRing p), T}) (AnnularRing p) := by
  rw [span_p_T_eq_span_T]
  infer_instance

/-! ### Coefficients in the localization `H[1/T]` -/

section Localization

variable {A : Type*} [CommRing A] [Algebra (AnnularRing p) A]
  [IsLocalization.Away (T : AnnularRing p) A]

/-- The canonical map `H → H[1/T]` is injective, because `T` is a non-zero-divisor in `H`. -/
theorem algebraMap_injective : Function.Injective (algebraMap (AnnularRing p) A) :=
  IsLocalization.injective A (Submonoid.powers_le.mpr T_mem_nonZeroDivisors)

/-- The `m`-th coefficient `d_m ∈ ℤ_p` of an element `x ∈ H[1/T]`: if `x * T ^ k = a` with
`a ∈ H`, then `localizedCoeff p x m = a.coeff (m + k)`. This is independent of the choice of
`(a, k)` (`localizedCoeff_eq_of_mul_pow`). -/
def localizedCoeff (p : ℕ) [Fact p.Prime] {A : Type*} [CommRing A] [Algebra (AnnularRing p) A]
    [IsLocalization.Away (T : AnnularRing p) A] (x : A) (m : ℤ) : ℤ_[p] :=
  (IsLocalization.Away.surj (T : AnnularRing p) x).choose_spec.choose.coeff
    (m + (IsLocalization.Away.surj (T : AnnularRing p) x).choose)

/-- If `x * T ^ k = a` in `H[1/T]`, then the `m`-th coefficient of `x` is `a.coeff (m + k)`. -/
theorem localizedCoeff_eq_of_mul_pow {x : A} {a : AnnularRing p} {k : ℕ}
    (h : x * algebraMap (AnnularRing p) A T ^ k = algebraMap (AnnularRing p) A a) (m : ℤ) :
    localizedCoeff p x m = a.coeff (m + k) := by
  set s := IsLocalization.Away.surj (T : AnnularRing p) x
  set k' := s.choose
  set a' := s.choose_spec.choose
  have h' : x * algebraMap (AnnularRing p) A T ^ k' = algebraMap (AnnularRing p) A a' :=
    s.choose_spec.choose_spec
  have heq : (T : AnnularRing p) ^ k * a' = T ^ k' * a := algebraMap_injective (A := A) <| by
    simp only [map_mul, map_pow, ← h, ← h']
    ring
  have hc := congr_arg (coeff · (m + k + k')) heq
  rw [coeff_T_pow_mul, coeff_T_pow_mul] at hc
  have h1 : m + (k : ℤ) + (k' : ℤ) - (k : ℤ) = m + (k' : ℤ) := by omega
  have h2 : m + (k : ℤ) + (k' : ℤ) - (k' : ℤ) = m + (k : ℤ) := by omega
  rw [h1, h2] at hc
  exact hc

/-- The coefficients of the image of `a ∈ H` in `H[1/T]` are the coefficients of `a`. -/
@[simp] theorem localizedCoeff_algebraMap (a : AnnularRing p) (m : ℤ) :
    localizedCoeff p (algebraMap (AnnularRing p) A a) m = a.coeff m := by
  simpa using localizedCoeff_eq_of_mul_pow (x := algebraMap (AnnularRing p) A a) (k := 0)
    (by simp) m

/-- An element of `H[1/T]` is uniquely determined by its coefficients. -/
theorem localizedCoeff_injective : Function.Injective (localizedCoeff p (A := A)) := by
  intro x y hxy
  obtain ⟨k₁, a₁, h₁⟩ := IsLocalization.Away.surj (T : AnnularRing p) x
  obtain ⟨k₂, a₂, h₂⟩ := IsLocalization.Away.surj (T : AnnularRing p) y
  have heq : (T : AnnularRing p) ^ k₂ * a₁ = T ^ k₁ * a₂ := by
    ext m : 2
    rw [coeff_T_pow_mul, coeff_T_pow_mul]
    have hx := localizedCoeff_eq_of_mul_pow h₁ (m - k₁ - k₂)
    have hy := localizedCoeff_eq_of_mul_pow h₂ (m - k₁ - k₂)
    have hm := congr_fun hxy (m - k₁ - k₂)
    rw [hx, hy] at hm
    have h1 : m - (k₁ : ℤ) - (k₂ : ℤ) + (k₁ : ℤ) = m - (k₂ : ℤ) := by omega
    have h2 : m - (k₁ : ℤ) - (k₂ : ℤ) + (k₂ : ℤ) = m - (k₁ : ℤ) := by omega
    rw [h1, h2] at hm
    exact hm
  have hmul : x * algebraMap (AnnularRing p) A T ^ (k₁ + k₂) =
      y * algebraMap (AnnularRing p) A T ^ (k₁ + k₂) := by
    calc x * algebraMap (AnnularRing p) A T ^ (k₁ + k₂)
        = algebraMap (AnnularRing p) A (T ^ k₂ * a₁) := by
          rw [map_mul, map_pow, ← h₁, pow_add]; ring
      _ = algebraMap (AnnularRing p) A (T ^ k₁ * a₂) := by rw [heq]
      _ = y * algebraMap (AnnularRing p) A T ^ (k₁ + k₂) := by
          rw [map_mul, map_pow, ← h₂, pow_add]; ring
  exact ((IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).pow (k₁ + k₂)).mul_right_cancel
    hmul

@[simp] theorem localizedCoeff_zero (m : ℤ) : localizedCoeff p (0 : A) m = 0 := by
  simpa using localizedCoeff_algebraMap (A := A) (0 : AnnularRing p) m

@[simp] theorem localizedCoeff_one (m : ℤ) :
    localizedCoeff p (1 : A) m = if m = 0 then 1 else 0 := by
  simpa using localizedCoeff_algebraMap (A := A) (1 : AnnularRing p) m

@[simp] theorem localizedCoeff_add (x y : A) (m : ℤ) :
    localizedCoeff p (x + y) m = localizedCoeff p x m + localizedCoeff p y m := by
  obtain ⟨k₁, a₁, h₁⟩ := IsLocalization.Away.surj (T : AnnularRing p) x
  obtain ⟨k₂, a₂, h₂⟩ := IsLocalization.Away.surj (T : AnnularRing p) y
  have hsum : (x + y) * algebraMap (AnnularRing p) A T ^ (k₁ + k₂) =
      algebraMap (AnnularRing p) A (T ^ k₂ * a₁ + T ^ k₁ * a₂) := by
    simp only [map_add, map_mul, map_pow, ← h₁, ← h₂, pow_add]
    ring
  rw [localizedCoeff_eq_of_mul_pow hsum, coeff_add, coeff_T_pow_mul, coeff_T_pow_mul,
    localizedCoeff_eq_of_mul_pow h₁, localizedCoeff_eq_of_mul_pow h₂]
  have h1 : m + ((k₁ + k₂ : ℕ) : ℤ) - (k₂ : ℤ) = m + (k₁ : ℤ) := by omega
  have h2 : m + ((k₁ + k₂ : ℕ) : ℤ) - (k₁ : ℤ) = m + (k₂ : ℤ) := by omega
  rw [h1, h2]

@[simp] theorem localizedCoeff_neg (x : A) (m : ℤ) :
    localizedCoeff p (-x) m = -localizedCoeff p x m := by
  obtain ⟨k, a, h⟩ := IsLocalization.Away.surj (T : AnnularRing p) x
  have hneg : (-x) * algebraMap (AnnularRing p) A T ^ k = algebraMap (AnnularRing p) A (-a) := by
    rw [neg_mul, h, map_neg]
  rw [localizedCoeff_eq_of_mul_pow hneg, localizedCoeff_eq_of_mul_pow h, coeff_neg]

@[simp] theorem localizedCoeff_sub (x y : A) (m : ℤ) :
    localizedCoeff p (x - y) m = localizedCoeff p x m - localizedCoeff p y m := by
  rw [sub_eq_add_neg, localizedCoeff_add, localizedCoeff_neg, sub_eq_add_neg]

private theorem localizedCoeff_nsmul (n : ℕ) (x : A) (m : ℤ) :
    localizedCoeff p (n • x) m = n • localizedCoeff p x m := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, localizedCoeff_add, ih]

/-- Every ring homomorphism `ℤ_[p] →+* H[1/T]` equals the canonical structure map through `H`:
any two ring homomorphisms agree modulo `p ^ n` for every `n`, and `H[1/T]` is `p`-adically
separated. -/
theorem ringHom_padicInt_eq (f : ℤ_[p] →+* A) :
    f = (algebraMap (AnnularRing p) A).comp (algebraMap ℤ_[p] (AnnularRing p)) := by
  ext c
  refine localizedCoeff_injective (p := p) (funext fun m ↦ ?_)
  have hle (n : ℕ) :
      ‖localizedCoeff p (f c - algebraMap (AnnularRing p) A (algebraMap ℤ_[p] (AnnularRing p) c))
        m‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec n c)
    have hc : c = (c.appr n : ℤ_[p]) + (p : ℤ_[p]) ^ n * r := eq_add_of_sub_eq' hr
    have hsub : f c - algebraMap (AnnularRing p) A (algebraMap ℤ_[p] (AnnularRing p) c) =
        ((p ^ n : ℕ) : A) * (f r - algebraMap (AnnularRing p) A
          (algebraMap ℤ_[p] (AnnularRing p) r)) := by
      conv_lhs => rw [hc]
      simp only [map_add, map_natCast, map_mul, map_pow, Nat.cast_pow]
      ring
    rw [hsub, ← nsmul_eq_mul, localizedCoeff_nsmul, nsmul_eq_mul, Nat.cast_pow, norm_mul,
      PadicInt.norm_p_pow]
    exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)
  have ht : Tendsto (fun _ : ℕ ↦ localizedCoeff p
      (f c - algebraMap (AnnularRing p) A (algebraMap ℤ_[p] (AnnularRing p) c)) m)
      atTop (𝓝 0) :=
    tendsto_zero_of_norm_le_zpow (one_lt_p (p := p)) hle
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have h0 := tendsto_const_nhds_iff.mp ht
  rw [localizedCoeff_sub, sub_eq_zero] at h0
  exact h0

@[simp] theorem localizedCoeff_smul [Algebra ℤ_[p] A] (c : ℤ_[p]) (x : A) (m : ℤ) :
    localizedCoeff p (c • x) m = c * localizedCoeff p x m := by
  obtain ⟨k, a, h⟩ := IsLocalization.Away.surj (T : AnnularRing p) x
  have hmap : algebraMap ℤ_[p] A c =
      algebraMap (AnnularRing p) A (algebraMap ℤ_[p] (AnnularRing p) c) :=
    DFunLike.congr_fun (ringHom_padicInt_eq (algebraMap ℤ_[p] A)) c
  have hsmul : (c • x) * algebraMap (AnnularRing p) A T ^ k =
      algebraMap (AnnularRing p) A (c • a) := by
    rw [smul_mul_assoc, h, Algebra.smul_def, Algebra.smul_def, map_mul, hmap]
  rw [localizedCoeff_eq_of_mul_pow hsmul, localizedCoeff_eq_of_mul_pow h, coeff_smul]

/-- Multiplication by `T ^ n` in `H[1/T]` shifts the coefficients up by `n` degrees. -/
@[simp] theorem localizedCoeff_T_pow_mul (n : ℕ) (x : A) (m : ℤ) :
    localizedCoeff p (algebraMap (AnnularRing p) A T ^ n * x) m = localizedCoeff p x (m - n) := by
  obtain ⟨k, a, h⟩ := IsLocalization.Away.surj (T : AnnularRing p) x
  have hmul : (algebraMap (AnnularRing p) A T ^ n * x) * algebraMap (AnnularRing p) A T ^ k =
      algebraMap (AnnularRing p) A (T ^ n * a) := by
    rw [mul_assoc, h, map_mul, map_pow]
  rw [localizedCoeff_eq_of_mul_pow hmul, localizedCoeff_eq_of_mul_pow h, coeff_T_pow_mul]
  congr 1
  omega

/-- Multiplication by `T` in `H[1/T]` shifts the coefficients up by one degree. -/
@[simp] theorem localizedCoeff_T_mul (x : A) (m : ℤ) :
    localizedCoeff p (algebraMap (AnnularRing p) A T * x) m = localizedCoeff p x (m - 1) := by
  simpa using localizedCoeff_T_pow_mul 1 x m

/-- Multiplication by an integer power `T ^ k` in `H[1/T]` shifts the coefficients by `k`
degrees. -/
@[simp] theorem localizedCoeff_T_zpow_mul (k : ℤ) (x : A) (m : ℤ) :
    localizedCoeff p (((IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit ^ k : Aˣ) *
      x) m = localizedCoeff p x (m - k) := by
  set u : Aˣ := (IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit
  have hu : (u : A) = algebraMap (AnnularRing p) A T := rfl
  cases k with
  | ofNat n =>
    simp [hu]
  | negSucc n =>
    have hmul : algebraMap (AnnularRing p) A T ^ (n + 1) * (((u ^ (Int.negSucc n) : Aˣ) : A) * x) =
        x := by
      rw [← hu, ← Units.val_pow_eq_pow_val, ← mul_assoc, ← Units.val_mul, zpow_negSucc,
        mul_inv_cancel, Units.val_one, one_mul]
    have := localizedCoeff_T_pow_mul (p := p) (n + 1) (((u ^ (Int.negSucc n) : Aˣ) : A) * x)
      (m + ((n + 1 : ℕ) : ℤ))
    rw [hmul, add_sub_cancel_right] at this
    exact this.symm.trans (congr_arg _ (by omega))

/-- The convolution series of the coefficients of two elements of `H[1/T]` converges in `ℤ_p`. -/
theorem summable_localizedCoeff_mul_localizedCoeff (x y : A) (m : ℤ) :
    Summable fun i : ℤ ↦ localizedCoeff p x i * localizedCoeff p y (m - i) := by
  obtain ⟨k₁, a₁, h₁⟩ := IsLocalization.Away.surj (T : AnnularRing p) x
  obtain ⟨k₂, a₂, h₂⟩ := IsLocalization.Away.surj (T : AnnularRing p) y
  have hs := ((Equiv.addRight (k₁ : ℤ)).summable_iff).mpr
    (summable_coeff_mul_coeff a₁ a₂ (m + k₁ + k₂))
  refine hs.congr fun i ↦ ?_
  rw [Function.comp_apply, Equiv.coe_addRight, localizedCoeff_eq_of_mul_pow h₁,
    localizedCoeff_eq_of_mul_pow h₂]
  dsimp only
  congr 2
  omega

/-- The coefficient of `T ^ m` in a product in `H[1/T]` is the convolution of the coefficients. -/
theorem localizedCoeff_mul (x y : A) (m : ℤ) :
    localizedCoeff p (x * y) m = ∑' i : ℤ, localizedCoeff p x i * localizedCoeff p y (m - i) := by
  obtain ⟨k₁, a₁, h₁⟩ := IsLocalization.Away.surj (T : AnnularRing p) x
  obtain ⟨k₂, a₂, h₂⟩ := IsLocalization.Away.surj (T : AnnularRing p) y
  have hprod : (x * y) * algebraMap (AnnularRing p) A T ^ (k₁ + k₂) =
      algebraMap (AnnularRing p) A (a₁ * a₂) := by
    rw [map_mul, ← h₁, ← h₂, pow_add]
    ring
  rw [localizedCoeff_eq_of_mul_pow hprod, coeff_mul, ← (Equiv.addRight (k₁ : ℤ)).tsum_eq]
  refine tsum_congr fun i ↦ ?_
  rw [Equiv.coe_addRight, localizedCoeff_eq_of_mul_pow h₁, localizedCoeff_eq_of_mul_pow h₂]
  dsimp only
  congr 2
  omega

/-- The convolution series converges to the coefficient of the product in `H[1/T]`. -/
theorem hasSum_localizedCoeff_mul (x y : A) (m : ℤ) :
    HasSum (fun i : ℤ ↦ localizedCoeff p x i * localizedCoeff p y (m - i))
      (localizedCoeff p (x * y) m) := by
  rw [localizedCoeff_mul]
  exact (summable_localizedCoeff_mul_localizedCoeff x y m).hasSum

/-! ### The coefficient criterion and `T`-adic filtration in `H[1/T]` -/

/-- Every element `x ∈ H[1/T]` satisfies the shifted valuation bound `‖d_m‖ ≤ p ^ min 0 (m + k)`
for some `k : ℕ`. -/
theorem exists_norm_localizedCoeff_le (x : A) :
    ∃ k : ℕ, ∀ m : ℤ, ‖localizedCoeff p x m‖ ≤ (p : ℝ) ^ min 0 (m + k) := by
  obtain ⟨k, a, h⟩ := IsLocalization.Away.surj (T : AnnularRing p) x
  exact ⟨k, fun m ↦ (localizedCoeff_eq_of_mul_pow h m).symm ▸ a.norm_coeff_le (m + k)⟩

/-- **Coefficient criterion for `H[1/T]`**: a family `d : ℤ → ℤ_p` is the coefficient family of a
(unique) element of `H[1/T]` exactly when `‖d m‖ ≤ p ^ min 0 (m + k)` for some `k : ℕ`, i.e.
`v_p(d_m) ≥ max(0, -m - k)`. -/
theorem existsUnique_localizedCoeff_eq_iff {d : ℤ → ℤ_[p]} :
    (∃! x : A, localizedCoeff p x = d) ↔ ∃ k : ℕ, ∀ m : ℤ, ‖d m‖ ≤ (p : ℝ) ^ min 0 (m + k) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨x, rfl, -⟩
    exact exists_norm_localizedCoeff_le x
  · rintro ⟨k, hk⟩
    let a : AnnularRing p := ⟨fun m ↦ d (m - k), fun m ↦ by simpa [sub_add_cancel] using hk (m - k)⟩
    let u : Aˣ := (IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit
    refine ⟨((u ^ (-(k : ℤ)) : Aˣ) : A) * algebraMap (AnnularRing p) A a, funext fun m ↦ ?_,
      fun y hy ↦ localizedCoeff_injective <| hy.trans <| (funext fun m ↦ ?_).symm⟩
    · rw [localizedCoeff_T_zpow_mul, localizedCoeff_algebraMap]
      simp [a]
    · rw [localizedCoeff_T_zpow_mul, localizedCoeff_algebraMap]
      simp [a]

/-- An element `x ∈ H[1/T]` lies in `T ^ n H` (with `n : ℤ`) exactly when its coefficients satisfy
`‖localizedCoeff p x m‖ ≤ p ^ min 0 (m - n)` for every `m ∈ ℤ`. -/
theorem T_zpow_neg_mul_mem_range_iff {x : A} {n : ℤ} :
    (((IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit ^ (-n) : Aˣ) : A) * x ∈
        (algebraMap (AnnularRing p) A).range ↔
      ∀ m : ℤ, ‖localizedCoeff p x m‖ ≤ (p : ℝ) ^ min 0 (m - n) := by
  set u : Aˣ := (IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨a, ha⟩ m
    have hx : localizedCoeff p x m = a.coeff (m - n) := by
      have := congr_arg (fun y ↦ localizedCoeff p y (m - n)) ha
      rw [localizedCoeff_algebraMap, localizedCoeff_T_zpow_mul, sub_neg_eq_add, sub_add_cancel]
        at this
      exact this.symm
    rw [hx]
    exact a.norm_coeff_le (m - n)
  · refine ⟨⟨fun m ↦ localizedCoeff p x (m + n), fun m ↦ by
      simpa [add_sub_cancel_right] using h (m + n)⟩,
      localizedCoeff_injective (p := p) <| funext fun m ↦ ?_⟩
    rw [localizedCoeff_algebraMap, localizedCoeff_T_zpow_mul, sub_neg_eq_add]

/-- An element of `H[1/T]` lies in the subring `H` exactly when its coefficients satisfy
`‖localizedCoeff p x m‖ ≤ p ^ min 0 m` for every `m ∈ ℤ`. -/
theorem mem_range_algebraMap_iff_norm_localizedCoeff_le {x : A} :
    x ∈ (algebraMap (AnnularRing p) A).range ↔
      ∀ m : ℤ, ‖localizedCoeff p x m‖ ≤ (p : ℝ) ^ min 0 m := by
  simpa using T_zpow_neg_mul_mem_range_iff (p := p) (A := A) (x := x) (n := 0)

/-- An element of `H[1/T]` lies in the basic `T`-adic neighbourhood `T ^ n H` (`n : ℕ`) exactly
when its coefficients satisfy `‖localizedCoeff p x m‖ ≤ p ^ min 0 (m - n)` for every `m ∈ ℤ`. -/
theorem mem_awayNhd_iff_norm_localizedCoeff_le {n : ℕ} {x : A} :
    x ∈ Huber.awayNhd (T : AnnularRing p) A n ↔
      ∀ m : ℤ, ‖localizedCoeff p x m‖ ≤ (p : ℝ) ^ min 0 (m - n) := by
  rw [← T_zpow_neg_mul_mem_range_iff (p := p), Huber.mem_awayNhd, RingHom.mem_range]
  set u : Aˣ := (IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit
  have hu : ((u ^ (n : ℤ) : Aˣ) : A) = algebraMap (AnnularRing p) A (T ^ n) := by
    simp [u]
  refine ⟨?_, ?_⟩
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    rw [map_mul, ← hu, ← mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
      Units.val_one, one_mul]
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [map_mul, ← hu, ha, ← mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero,
      Units.val_one, one_mul]

end Localization

end TauCeti.AnnularRing
