/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import TauCeti.Analysis.Sobolev.Circle.Basic

/-!
# Laurent subspaces of the circle Sobolev spaces and holomorphic extension to the disc

For a set `S ⊆ ℤ` of frequencies, the elements of `H^s` whose Fourier coefficients vanish outside
`S` form a closed subspace, the image of the frequency projection that discards the coefficients
outside `S`. Taking `S` to be the nonnegative or the negative frequencies gives the Laurent
splitting `H^s = H^s_{≥0} ⊕ H^s_{<0}` of a boundary circle, which is orthogonal in the Hilbert case.
These are the subspaces in which the Hardy decomposition of a cut Riemann surface is carried out:
the nonnegative part consists of boundary values of holomorphic functions on the disc bounded by
the circle (Robbin–Salamon, §§9–12).

The second half of the file makes this precise. The power series `∑_{n ≥ 0} a.coeff n w ^ n`
converges on the open unit disc for every order `s` and defines a holomorphic function there,
the disc function of `a`. For `s > 1/2` it converges on the closed disc and is continuous there,
and when the negative coefficients of `a` vanish its values on the unit circle are the continuous
function `CircleSobolev.toContinuousMap` attached to `a`. For every order `s`, an element of
`H^s_{≥0}` is determined by its holomorphic extension to the open disc, whose Taylor coefficients
at `0` are its nonnegative Fourier coefficients.

## Main definitions

* `TauCeti.CircleSobolev.supported s E S`: the closed subspace of `H^s` of elements with Fourier
  coefficients supported in `S`.
* `TauCeti.CircleSobolev.indicator S`: the frequency projection onto `supported s E S`.
* `TauCeti.CircleSobolev.diskFunction a`: the function `w ↦ ∑_{n ≥ 0} a.coeff n w ^ n`.

## Main statements

* `TauCeti.CircleSobolev.isCompl_supported`: `supported s E S` and `supported s E Sᶜ` are
  complementary; `TauCeti.CircleSobolev.orthogonal_supported` identifies the second as the
  orthogonal complement of the first in the Hilbert case.
* `TauCeti.CircleSobolev.analyticOnNhd_diskFunction`: the disc function is holomorphic on the
  open unit disc.
* `TauCeti.CircleSobolev.continuousOn_diskFunction`: for `s > 1/2` it is continuous on the closed
  unit disc.
* `TauCeti.CircleSobolev.toContinuousMap_apply_eq_diskFunction`: for `s > 1/2` and `a` with
  vanishing negative coefficients, the boundary values of the disc function are the continuous
  function attached to `a`.
* `TauCeti.CircleSobolev.eq_of_eqOn_diskFunction`: elements with vanishing negative coefficients
  are determined by their disc functions on the open disc.

## References

* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699 (Hardy decompositions on boundary Sobolev spaces).
* P. L. Duren, *Theory of Hᵖ Spaces*, chapter 1.
-/

public section

noncomputable section

open Filter Metric Topology

namespace TauCeti

namespace CircleSobolev

variable {s t : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### Subspaces of prescribed frequency support -/

variable (s E) in
/-- The subspace of `H^s` of elements whose Fourier coefficients vanish outside `S`. -/
def supported (S : Set ℤ) : Submodule ℂ (CircleSobolev s E) where
  carrier := {a | Function.support a.coeff ⊆ S}
  add_mem' ha hb := (Function.support_add _ _).trans (Set.union_subset ha hb)
  zero_mem' := by simp
  smul_mem' c a ha := (Function.support_const_smul_subset c a.coeff).trans ha

variable {S S' : Set ℤ} {a : CircleSobolev s E}

theorem mem_supported : a ∈ supported s E S ↔ Function.support a.coeff ⊆ S :=
  Iff.rfl

theorem mem_supported' : a ∈ supported s E S ↔ ∀ n ∉ S, a.coeff n = 0 := by
  simp only [mem_supported, Function.support_subset_iff']

theorem supported_mono (h : S ⊆ S') : supported s E S ≤ supported s E S' :=
  fun _ ha ↦ ha.trans h

@[simp]
theorem supported_univ : supported s E Set.univ = ⊤ :=
  eq_top_iff.2 fun _ _ ↦ Set.subset_univ _

@[simp]
theorem supported_empty : supported s E ∅ = ⊥ :=
  eq_bot_iff.2 fun a ha ↦ (Submodule.mem_bot ℂ).2 <| CircleSobolev.ext <| by
    simpa using Function.support_eq_empty_iff.1 (Set.subset_empty_iff.1 ha)

@[simp]
theorem supported_inter : supported s E (S ∩ S') = supported s E S ⊓ supported s E S' :=
  Submodule.ext fun _ ↦ Set.subset_inter_iff

theorem single_mem_supported {n : ℤ} (hn : n ∈ S) (x : E) : single n x ∈ supported s E S := by
  rw [mem_supported, coeff_single]
  exact Pi.support_single_subset.trans (Set.singleton_subset_iff.2 hn)

@[simp]
theorem inclusion_mem_supported_iff (h : t ≤ s) :
    inclusion h a ∈ supported t E S ↔ a ∈ supported s E S := by
  simp [mem_supported]

/-! ### Frequency projections -/

private theorem weight_mul_norm_indicator_le (S : Set ℤ) (a : CircleSobolev s E) (n : ℤ) :
    weight s n * ‖S.indicator a.coeff n‖ ≤ 1 * (weight s n * ‖a.coeff n‖) := by
  rw [one_mul]
  exact mul_le_mul_of_nonneg_left (norm_indicator_le_norm_self _ _) (weight_nonneg s n)

/-- The frequency projection onto `S`: it keeps the Fourier coefficients indexed by `S` and
replaces the others by zero. Its range is `supported s E S` and its kernel is
`supported s E Sᶜ`. -/
def indicator (S : Set ℤ) : CircleSobolev s E →L[ℂ] CircleSobolev s E :=
  LinearMap.mkContinuous
    { toFun a := ⟨S.indicator a.coeff, memℓp_of_forall_le (weight_mul_norm_indicator_le S a)⟩
      map_add' a b := CircleSobolev.ext (Set.indicator_add' S a.coeff b.coeff)
      map_smul' c a := CircleSobolev.ext (Set.indicator_const_smul S c a.coeff) }
    1 fun a ↦ norm_le_of_forall_le zero_le_one (weight_mul_norm_indicator_le S a)

@[simp]
theorem coeff_indicator (S : Set ℤ) (a : CircleSobolev s E) :
    (indicator S a).coeff = S.indicator a.coeff :=
  (rfl)

theorem norm_indicator_le (S : Set ℤ) (a : CircleSobolev s E) : ‖indicator S a‖ ≤ ‖a‖ := by
  simpa using norm_le_of_forall_le zero_le_one (weight_mul_norm_indicator_le S a)

theorem opNorm_indicator_le (S : Set ℤ) :
    ‖(indicator S : CircleSobolev s E →L[ℂ] CircleSobolev s E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a ↦ by
    simpa using norm_indicator_le S a

theorem indicator_mem_supported (S : Set ℤ) (a : CircleSobolev s E) :
    indicator S a ∈ supported s E S :=
  Set.support_indicator_subset

theorem indicator_eq_self_iff : indicator S a = a ↔ a ∈ supported s E S := by
  rw [mem_supported, ← Set.indicator_eq_self, ← coeff_indicator]
  exact ⟨congr_arg coeff, CircleSobolev.ext⟩

theorem indicator_eq_zero_iff : indicator S a = 0 ↔ a ∈ supported s E Sᶜ := by
  rw [mem_supported', CircleSobolev.ext_iff, coeff_indicator, coeff_zero, funext_iff]
  refine forall_congr' fun n ↦ ?_
  by_cases hn : n ∈ S <;> simp [hn]

@[simp]
theorem indicator_indicator (S S' : Set ℤ) (a : CircleSobolev s E) :
    indicator S (indicator S' a) = indicator (S ∩ S') a :=
  CircleSobolev.ext (Set.indicator_indicator S S' a.coeff)

@[simp]
theorem indicator_univ : (indicator Set.univ : CircleSobolev s E →L[ℂ] CircleSobolev s E) =
    ContinuousLinearMap.id ℂ _ :=
  ContinuousLinearMap.ext fun a ↦ CircleSobolev.ext (Set.indicator_univ a.coeff)

@[simp]
theorem indicator_empty : (indicator ∅ : CircleSobolev s E →L[ℂ] CircleSobolev s E) = 0 :=
  ContinuousLinearMap.ext fun a ↦ CircleSobolev.ext (Set.indicator_empty a.coeff)

@[simp]
theorem indicator_add_indicator_compl (S : Set ℤ) (a : CircleSobolev s E) :
    indicator S a + indicator Sᶜ a = a :=
  CircleSobolev.ext (Set.indicator_self_add_compl S a.coeff)

@[simp]
theorem indicator_single (S : Set ℤ) (n : ℤ) (x : E) [Decidable (n ∈ S)] :
    indicator S (single (s := s) n x) = if n ∈ S then single n x else 0 := by
  split_ifs with hn
  · exact indicator_eq_self_iff.2 (single_mem_supported hn x)
  · exact indicator_eq_zero_iff.2 (single_mem_supported hn x)

@[simp]
theorem inclusion_indicator (h : t ≤ s) (S : Set ℤ) (a : CircleSobolev s E) :
    inclusion h (indicator S a) = indicator S (inclusion h a) :=
  CircleSobolev.ext (by simp)

theorem range_indicator (S : Set ℤ) :
    (indicator S : CircleSobolev s E →L[ℂ] CircleSobolev s E).range = supported s E S :=
  le_antisymm (LinearMap.range_le_iff_comap.2 <| eq_top_iff.2 fun a _ ↦
      indicator_mem_supported S a)
    fun a ha ↦ ⟨a, indicator_eq_self_iff.2 ha⟩

theorem ker_indicator (S : Set ℤ) :
    (indicator S : CircleSobolev s E →L[ℂ] CircleSobolev s E).ker = supported s E Sᶜ :=
  Submodule.ext fun _ ↦ indicator_eq_zero_iff

theorem isClosed_supported (S : Set ℤ) : IsClosed (supported s E S : Set (CircleSobolev s E)) := by
  rw [← compl_compl S, ← ker_indicator]
  exact (indicator Sᶜ).isClosed_ker

instance [CompleteSpace E] (S : Set ℤ) : CompleteSpace (supported s E S) :=
  (isClosed_supported S).completeSpace_coe

/-- The subspaces of `H^s` supported on `S` and on its complement are complementary: this is the
Laurent splitting of `H^s` when `S` is the set of nonnegative frequencies. -/
theorem isCompl_supported (S : Set ℤ) : IsCompl (supported s E S) (supported s E Sᶜ) := by
  refine ⟨Submodule.disjoint_def.2 fun a ha hac ↦ ?_, Submodule.codisjoint_iff_exists_add_eq.2
    fun a ↦ ⟨_, _, indicator_mem_supported S a, indicator_mem_supported Sᶜ a,
      indicator_add_indicator_compl S a⟩⟩
  rw [← indicator_eq_self_iff.2 ha, indicator_eq_zero_iff.2 hac]

section Inner

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- In the Hilbert case, the Laurent splitting is orthogonal: the orthogonal complement of the
subspace supported on `S` is the subspace supported on `Sᶜ`. -/
theorem orthogonal_supported (S : Set ℤ) : (supported s F S)ᗮ = supported s F Sᶜ := by
  refine le_antisymm (fun b hb ↦ mem_supported'.2 fun n hn ↦ ?_) fun b hb ↦
    (Submodule.mem_orthogonal _ _).2 fun a ha ↦ ?_
  · have h := (Submodule.mem_orthogonal _ _).1 hb (single n (b.coeff n))
      (single_mem_supported (not_not.1 hn) _)
    rw [inner_eq_tsum, tsum_eq_single n fun m hm ↦ by simp [hm]] at h
    simpa [(weight_pos (2 * s) n).ne'] using h
  · rw [inner_eq_tsum]
    refine (tsum_congr fun n ↦ ?_).trans tsum_zero
    by_cases hn : n ∈ S
    · simp [mem_supported'.1 hb n (not_not.2 hn)]
    · simp [mem_supported'.1 ha n hn]

end Inner

/-! ### The holomorphic disc function -/

/-- For `0 ≤ r < 1` and every order `s`, the sequence `r ^ n (1 + n) ^ (-s)` is summable. -/
private theorem summable_pow_mul_weight {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < 1) (s : ℝ) :
    Summable fun n : ℕ ↦ r ^ n * weight (-s) n := by
  set k := ⌈-s⌉₊
  refine Summable.of_norm_bounded_eventually_nat
    ((summable_pow_mul_geometric_of_norm_lt_one k (r := r) (by
      rwa [Real.norm_of_nonneg hr₀])).mul_left (2 ^ k)) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hr₀ n) (weight_nonneg _ _)), weight_def,
    Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n), mul_comm (r ^ n), ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr₀ n)
  calc (1 + (n : ℝ)) ^ (-s) ≤ (1 + (n : ℝ)) ^ (k : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil _)
    _ = (1 + (n : ℝ)) ^ k := Real.rpow_natCast _ _
    _ ≤ (2 * n) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
    _ = 2 ^ k * (n : ℝ) ^ k := mul_pow _ _ _

private theorem norm_pow_smul_coeff_le (a : CircleSobolev s E) (w : ℂ) (n : ℕ) :
    ‖w ^ n • a.coeff n‖ ≤ ‖w‖ ^ n * weight (-s) n * ‖a‖ := by
  rw [norm_smul, norm_pow, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_coeff_le a n) (by positivity)

private theorem summable_norm_pow_smul_coeff (a : CircleSobolev s E) {w : ℂ} (hw : ‖w‖ < 1) :
    Summable fun n : ℕ ↦ ‖w ^ n • a.coeff n‖ :=
  ((summable_pow_mul_weight (norm_nonneg w) hw s).mul_right ‖a‖).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (norm_pow_smul_coeff_le a w)

/-- The function `w ↦ ∑_{n ≥ 0} a.coeff n w ^ n` determined by the nonnegative Fourier
coefficients of `a`. It is holomorphic on the open unit disc for every order `s`
(`CircleSobolev.analyticOnNhd_diskFunction`), and for `s > 1/2` it is continuous on the closed disc
with boundary values `CircleSobolev.toContinuousMap` when the negative coefficients of `a` vanish
(`CircleSobolev.toContinuousMap_apply_eq_diskFunction`). Where the series does not converge its
value is a junk value. -/
def diskFunction (a : CircleSobolev s E) (w : ℂ) : E :=
  ∑' n : ℕ, w ^ n • a.coeff n

theorem diskFunction_def (a : CircleSobolev s E) (w : ℂ) :
    diskFunction a w = ∑' n : ℕ, w ^ n • a.coeff n :=
  (rfl)

@[simp]
theorem diskFunction_zero (w : ℂ) : diskFunction (0 : CircleSobolev s E) w = 0 := by
  simp [diskFunction]

/-- The disc function only depends on the nonnegative Fourier coefficients. -/
@[simp]
theorem diskFunction_indicator_Ici (a : CircleSobolev s E) :
    diskFunction (indicator (Set.Ici 0) a) = diskFunction a :=
  funext fun w ↦ tsum_congr fun n ↦ by simp

@[simp]
theorem diskFunction_inclusion (h : t ≤ s) (a : CircleSobolev s E) :
    diskFunction (inclusion h a) = diskFunction a :=
  funext fun w ↦ tsum_congr fun n ↦ by simp

/-- The disc function of the Fourier monomial `x e^{inθ}`, `n ≥ 0`, is the monomial `w ^ n • x`. -/
@[simp]
theorem diskFunction_single_natCast (n : ℕ) (x : E) (w : ℂ) :
    diskFunction (single (s := s) n x) w = w ^ n • x := by
  rw [diskFunction, tsum_eq_single n fun m hm ↦ by simp [hm]]
  simp

/-- The disc function of a Fourier monomial of negative frequency vanishes. -/
@[simp]
theorem diskFunction_single_of_neg {n : ℤ} (hn : n < 0) (x : E) (w : ℂ) :
    diskFunction (single (s := s) n x) w = 0 := by
  rw [diskFunction]
  refine (tsum_congr fun m ↦ ?_).trans tsum_zero
  rw [coeff_single, Pi.single_eq_of_ne (by omega), smul_zero]

/-- The value of the disc function at the centre is the zeroth Fourier coefficient. -/
@[simp]
theorem diskFunction_apply_zero (a : CircleSobolev s E) : diskFunction a 0 = a.coeff 0 := by
  rw [diskFunction, tsum_eq_single 0 fun n hn ↦ by simp [hn]]
  simp

/-- On the open unit disc the disc function is bounded by `∑ₙ ‖w‖ ^ n (1 + n) ^ (-s)` times the
norm. -/
theorem norm_diskFunction_le (a : CircleSobolev s E) {w : ℂ} (hw : ‖w‖ < 1) :
    ‖diskFunction a w‖ ≤ (∑' n : ℕ, ‖w‖ ^ n * weight (-s) n) * ‖a‖ := by
  rw [← tsum_mul_right]
  exact (norm_tsum_le_tsum_norm (summable_norm_pow_smul_coeff a hw)).trans <|
    (summable_norm_pow_smul_coeff a hw).tsum_le_tsum (norm_pow_smul_coeff_le a w)
      ((summable_pow_mul_weight (norm_nonneg w) hw s).mul_right ‖a‖)

private theorem summable_norm_coeff_natCast (hs : 1 / 2 < s) (a : CircleSobolev s E) :
    Summable fun n : ℕ ↦ ‖a.coeff n‖ :=
  (summable_norm_coeff hs a).comp_injective Nat.cast_injective

private theorem norm_pow_smul_coeff_le_of_norm_le_one (a : CircleSobolev s E) {w : ℂ}
    (hw : ‖w‖ ≤ 1) (n : ℕ) : ‖w ^ n • a.coeff n‖ ≤ ‖a.coeff n‖ := by
  rw [norm_smul, norm_pow]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg w) hw)

/-- For `s > 1/2`, the disc function is bounded on the closed unit disc by the bound
`√(∑ₙ (1 + |n|) ^ (-2 s)) ‖a‖` of `CircleSobolev.norm_toContinuousMap_le`. -/
theorem norm_diskFunction_le_of_norm_le_one (hs : 1 / 2 < s) (a : CircleSobolev s E) {w : ℂ}
    (hw : ‖w‖ ≤ 1) : ‖diskFunction a w‖ ≤ √(∑' n, weight (-(2 * s)) n) * ‖a‖ := by
  have hsum := (summable_norm_coeff_natCast hs a).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_pow_smul_coeff_le_of_norm_le_one a hw)
  calc ‖diskFunction a w‖ ≤ ∑' n : ℕ, ‖w ^ n • a.coeff n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n : ℕ, ‖a.coeff n‖ := hsum.tsum_le_tsum (norm_pow_smul_coeff_le_of_norm_le_one a hw)
        (summable_norm_coeff_natCast hs a)
    _ ≤ ∑' n : ℤ, ‖a.coeff n‖ := tsum_comp_le_tsum_of_inj (summable_norm_coeff hs a)
        (fun _ ↦ norm_nonneg _) Nat.cast_injective
    _ ≤ √(∑' n, weight (-(2 * s)) n) * ‖a‖ := tsum_norm_coeff_le hs a

theorem diskFunction_smul (c : ℂ) (a : CircleSobolev s E) (w : ℂ) :
    diskFunction (c • a) w = c • diskFunction a w := by
  simp_rw [diskFunction, coeff_smul, Pi.smul_apply, smul_comm _ c, tsum_const_smul'']

variable [CompleteSpace E]

/-- On the open unit disc the disc function is the sum of its power series. -/
theorem hasSum_diskFunction (a : CircleSobolev s E) {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ ↦ w ^ n • a.coeff n) (diskFunction a w) :=
  (summable_norm_pow_smul_coeff a hw).of_norm.hasSum

theorem diskFunction_add (a b : CircleSobolev s E) {w : ℂ} (hw : ‖w‖ < 1) :
    diskFunction (a + b) w = diskFunction a w + diskFunction b w :=
  (hasSum_diskFunction (a + b) hw).unique <| by
    simpa [smul_add] using (hasSum_diskFunction a hw).add (hasSum_diskFunction b hw)

theorem diskFunction_sub (a b : CircleSobolev s E) {w : ℂ} (hw : ‖w‖ < 1) :
    diskFunction (a - b) w = diskFunction a w - diskFunction b w :=
  (hasSum_diskFunction (a - b) hw).unique <| by
    simpa [smul_sub] using (hasSum_diskFunction a hw).sub (hasSum_diskFunction b hw)

/-- The disc function is holomorphic on the open unit disc. -/
theorem differentiableOn_diskFunction (a : CircleSobolev s E) :
    DifferentiableOn ℂ (diskFunction a) (ball 0 1) := by
  intro w hw
  rw [mem_ball_zero_iff] at hw
  obtain ⟨r, hwr, hr⟩ := exists_between hw
  have h := Complex.differentiableOn_tsum_of_summable_norm (U := ball 0 r)
    ((summable_pow_mul_weight ((norm_nonneg w).trans hwr.le) hr s).mul_right ‖a‖)
    (fun n ↦ ((differentiable_id.pow n).smul_const (a.coeff n)).differentiableOn) isOpen_ball
    fun n z hz ↦ (norm_pow_smul_coeff_le a z n).trans <| by
      rw [mem_ball_zero_iff] at hz
      have := weight_nonneg (-s) n
      gcongr
  exact (h.differentiableAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hwr))).differentiableWithinAt

/-- The disc function is analytic on the open unit disc. -/
theorem analyticOnNhd_diskFunction (a : CircleSobolev s E) :
    AnalyticOnNhd ℂ (diskFunction a) (ball 0 1) :=
  (differentiableOn_diskFunction a).analyticOnNhd isOpen_ball

/-- An element of `H^s` with vanishing negative Fourier coefficients is determined by its disc
function on the open unit disc: its nonnegative coefficients are the Taylor coefficients of the
disc function at `0`. -/
theorem eq_of_eqOn_diskFunction {a b : CircleSobolev s E}
    (ha : a ∈ supported s E (Set.Ici 0)) (hb : b ∈ supported s E (Set.Ici 0))
    (h : Set.EqOn (diskFunction a) (diskFunction b) (ball 0 1)) : a = b := by
  have hp (c : CircleSobolev s E) : HasFPowerSeriesAt (diskFunction c)
      (fun n ↦ ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (c.coeff n) :
        FormalMultilinearSeries ℂ ℂ E) 0 :=
    hasFPowerSeriesAt_iff.2 <| eventually_of_mem (ball_mem_nhds 0 one_pos) fun w hw ↦ by
      simpa [FormalMultilinearSeries.coeff] using hasSum_diskFunction c (mem_ball_zero_iff.1 hw)
  have hpq := (hp a).eq_formalMultilinearSeries <|
    (hp b).congr (h.symm.eventuallyEq_of_mem (ball_mem_nhds 0 one_pos))
  refine CircleSobolev.ext <| funext fun n ↦ ?_
  rcases lt_or_ge n 0 with hn | hn
  · rw [mem_supported'.1 ha n (not_le.2 hn), mem_supported'.1 hb n (not_le.2 hn)]
  · lift n to ℕ using hn
    simpa [FormalMultilinearSeries.coeff] using congr_arg (·.coeff n) hpq

/-! ### The closed disc and the boundary circle for `s > 1/2` -/

/-- For `s > 1/2`, the power series of the disc function converges absolutely on the closed unit
disc. -/
theorem hasSum_diskFunction_of_norm_le_one (hs : 1 / 2 < s) (a : CircleSobolev s E) {w : ℂ}
    (hw : ‖w‖ ≤ 1) : HasSum (fun n : ℕ ↦ w ^ n • a.coeff n) (diskFunction a w) :=
  ((summable_norm_coeff_natCast hs a).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_pow_smul_coeff_le_of_norm_le_one a hw)).of_norm.hasSum

/-- For `s > 1/2`, the disc function is continuous on the closed unit disc. -/
theorem continuousOn_diskFunction (hs : 1 / 2 < s) (a : CircleSobolev s E) :
    ContinuousOn (diskFunction a) (closedBall 0 1) :=
  continuousOn_tsum (fun n ↦ ((continuous_pow n).smul continuous_const).continuousOn)
    (summable_norm_coeff_natCast hs a) fun n _ hw ↦
      norm_pow_smul_coeff_le_of_norm_le_one a (mem_closedBall_zero_iff.1 hw) n

/-- **Boundary values of the disc function.** For `s > 1/2` and `a ∈ H^s` with vanishing
negative Fourier coefficients, the continuous function on `AddCircle T` attached to `a` is the
restriction of the disc function to the unit circle. -/
theorem toContinuousMap_apply_eq_diskFunction (T : ℝ) [Fact (0 < T)] (hs : 1 / 2 < s)
    {a : CircleSobolev s E} (ha : a ∈ supported s E (Set.Ici 0)) (x : AddCircle T) :
    toContinuousMap T hs a x = diskFunction a (fourier 1 x) := by
  have hsupp : Function.support (fun n : ℤ ↦ fourier n x • a.coeff n) ⊆ Set.range Nat.cast :=
    fun n hn ↦ ⟨n.toNat, Int.toNat_of_nonneg <| mem_supported.1 ha <|
      Function.support_smul_subset_right _ _ hn⟩
  rw [toContinuousMap_apply, diskFunction, ← Nat.cast_injective.tsum_eq hsupp]
  refine tsum_congr fun n ↦ ?_
  rw [fourier_one, fourier_apply, natCast_zsmul, AddCircle.toCircle_nsmul, Circle.coe_pow]

end CircleSobolev

end TauCeti
