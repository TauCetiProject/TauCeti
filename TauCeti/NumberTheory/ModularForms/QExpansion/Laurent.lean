/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.NumberTheory.ModularForms.QExpansion.Basic
import Mathlib.Analysis.Complex.TaylorSeries
import TauCeti.Analysis.Complex.UpperHalfPlane.QExpansion.Order
import TauCeti.RingTheory.LaurentSeries.Basic

/-!
# Laurent `q`-expansions of functions meromorphic at `i∞`

Let `h > 0` and let `f` be a function on the upper half-plane whose cusp function
`UpperHalfPlane.cuspFunction h f`, the function of `q = exp (2 π i τ / h)` attached to `f`, is
meromorphic at `q = 0`. This is the condition that `f` is meromorphic at `i∞`; unlike for modular
forms, `f` may have poles in the upper half-plane, and a pole at the cusp. Such an `f` has a
**Laurent `q`-expansion** `TauCeti.UpperHalfPlane.laurentQExpansion h f`, a formal Laurent series
over `ℂ`: if the pole at `q = 0` has order at most `k`, then `𝕢 ^ k * f` has an analytic cusp
function, and the Laurent `q`-expansion is the `q`-expansion of `𝕢 ^ k * f` shifted down by `k`.
The result does not depend on `k` (`TauCeti.UpperHalfPlane.laurentQExpansion_eq`), and it agrees
with Mathlib's `UpperHalfPlane.qExpansion` when the cusp function is analytic at `0`.

The Laurent `q`-expansion is compatible with the field operations: it is additive and
multiplicative, and it commutes with scalars, powers, inverses and quotients. It only depends on
the cusp function on a punctured neighbourhood of `0`. Its order is the order of the cusp function
at `0`, so it vanishes exactly when the cusp function vanishes near `0`, and for a periodic
function it converges to the function sufficiently high in the upper half-plane. This gives the
`q`-expansion principle: two periodic functions meromorphic at `i∞` have the same Laurent
`q`-expansion exactly when they agree near `i∞`.

These are the expansions at `i∞` through which modular functions, and fields of modular
functions with prescribed Fourier coefficients, are described. Compare
`TauCeti.Subgroup.CuspDatum.laurentQExpansion`, which expands functions holomorphic on the whole
upper half-plane at an arbitrary cusp of a Fuchsian group, for a chosen growth exponent.

## Main declarations

* `TauCeti.UpperHalfPlane.laurentQExpansion`: the Laurent `q`-expansion at `i∞`.
* `TauCeti.UpperHalfPlane.laurentQExpansion_eq`: its description through any admissible twisting
  exponent, and `TauCeti.UpperHalfPlane.laurentQExpansion_of_analyticAt` at analytic points.
* `TauCeti.UpperHalfPlane.laurentQExpansion_add`, `TauCeti.UpperHalfPlane.laurentQExpansion_mul`,
  `TauCeti.UpperHalfPlane.laurentQExpansion_inv` and their companions: the field operations.
* `TauCeti.UpperHalfPlane.orderTop_laurentQExpansion`: the order at `i∞`.
* `TauCeti.UpperHalfPlane.laurentQExpansion_eq_zero_iff`: uniqueness of the expansion.
* `TauCeti.UpperHalfPlane.hasSum_laurentQExpansion`: convergence near `i∞`.
* `TauCeti.UpperHalfPlane.laurentQExpansion_eq_laurentQExpansion_iff`: the `q`-expansion
  principle.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §2.1 (functions meromorphic at a cusp and their Laurent expansions in
  the local parameter at the cusp).
* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §1.1 and §2.4.
-/

public noncomputable section

open UpperHalfPlane Filter Topology Function

namespace TauCeti.UpperHalfPlane

variable {h : ℝ} {f g : ℍ → ℂ}

local notation "𝕢" => Function.Periodic.qParam

/-! ### Twisting by powers of the `q`-parameter -/

/-- Off `q = 0` and inside the unit disc, the cusp function of `𝕢 ^ k * f` is `q ^ k` times the
cusp function of `f`. -/
theorem cuspFunction_qParam_pow_mul_eventuallyEq (hh : 0 < h) (k : ℕ) (f : ℍ → ℂ) :
    cuspFunction h (fun τ ↦ 𝕢 h τ ^ k * f τ) =ᶠ[𝓝[≠] 0] fun q ↦ q ^ k * cuspFunction h f q := by
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)] with q hq hqn
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hq
  simp only [cuspFunction, Periodic.cuspFunction_eq_of_nonzero _ _ hq, Function.comp_apply]
  rw [ofComplex_apply_of_im_pos (Periodic.im_invQParam_pos_of_norm_lt_one hh
    (mem_ball_zero_iff.mp hqn) hq)]
  rw [Periodic.qParam_right_inv hh.ne' hq]

/-- Cusp functions which agree off `q = 0` agree near `q = 0`: the value at `0` is the limit
along the punctured neighbourhoods. -/
theorem cuspFunction_eventuallyEq_nhds {f g : ℍ → ℂ}
    (hfg : cuspFunction h f =ᶠ[𝓝[≠] 0] cuspFunction h g) :
    cuspFunction h f =ᶠ[𝓝 0] cuspFunction h g := by
  refine eventuallyEq_nhds_of_eventuallyEq_nhdsNE hfg ?_
  simp only [cuspFunction]
  rw [Periodic.cuspFunction_zero_eq_limUnder_nhds_ne,
    Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
  exact congrArg lim (Filter.map_congr hfg)

/-- A cusp function which agrees off `q = 0` with a function continuous at `0` agrees with it
near `0`. -/
theorem cuspFunction_eventuallyEq_nhds_of_continuousAt {f : ℍ → ℂ} {ψ : ℂ → ℂ}
    (hf : cuspFunction h f =ᶠ[𝓝[≠] 0] ψ) (hψ : ContinuousAt ψ 0) :
    cuspFunction h f =ᶠ[𝓝 0] ψ := by
  refine eventuallyEq_nhds_of_eventuallyEq_nhdsNE hf ?_
  simp only [cuspFunction]
  rw [Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
  exact ((hψ.tendsto.mono_left nhdsWithin_le_nhds).congr' hf.symm).limUnder_eq

/-- The `q`-expansion only depends on the cusp function off `q = 0`. -/
theorem qExpansion_congr {f g : ℍ → ℂ} (hfg : cuspFunction h f =ᶠ[𝓝[≠] 0] cuspFunction h g) :
    qExpansion h f = qExpansion h g := by
  ext n
  rw [qExpansion_coeff, qExpansion_coeff, (cuspFunction_eventuallyEq_nhds hfg).iteratedDeriv_eq]

/-- The order at `0` of `q ^ k` times the cusp function of `f`. -/
private theorem meromorphicOrderAt_qParam_pow_mul {k : ℕ}
    (hf : MeromorphicAt (cuspFunction h f) 0) :
    meromorphicOrderAt (fun q ↦ q ^ k * cuspFunction h f q) 0 =
      k + meromorphicOrderAt (cuspFunction h f) 0 := by
  have hq : MeromorphicAt (fun q : ℂ ↦ q ^ k) 0 := (analyticAt_id.pow k).meromorphicAt
  rw [fun_meromorphicOrderAt_mul hq hf]
  congr 1
  simpa using fun_meromorphicOrderAt_pow_id_sub_const (x := (0 : ℂ)) (n := k)

/-- If the cusp function of `f` is meromorphic at `0` with a pole of order at most `k`, then the
cusp function of `𝕢 ^ k * f` is analytic at `0`. -/
theorem analyticAt_cuspFunction_qParam_pow_mul (hh : 0 < h) {k : ℕ}
    (hf : MeromorphicAt (cuspFunction h f) 0)
    (hk : ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h f) 0) :
    AnalyticAt ℂ (cuspFunction h (fun τ ↦ 𝕢 h τ ^ k * f τ)) 0 := by
  have hψ : MeromorphicAt (fun q ↦ q ^ k * cuspFunction h f q) 0 :=
    (analyticAt_id.pow k).meromorphicAt.mul hf
  have hord : 0 ≤ meromorphicOrderAt (fun q ↦ q ^ k * cuspFunction h f q) 0 := by
    rw [meromorphicOrderAt_qParam_pow_mul hf]
    cases hn : meromorphicOrderAt (cuspFunction h f) 0 using WithTop.recTopCoe with
    | top => simp
    | coe n =>
      rw [hn] at hk
      have : -(k : ℤ) ≤ n := WithTop.coe_le_coe.mp hk
      exact_mod_cast (by omega : (0 : ℤ) ≤ k + n)
  have han := hψ.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp hord
  refine han.congr (cuspFunction_eventuallyEq_nhds_of_continuousAt ?_ han.continuousAt).symm
  exact (cuspFunction_qParam_pow_mul_eventuallyEq hh k f).trans hψ.eq_nhdsNE_toMeromorphicNFAt

/-! ### The Laurent `q`-expansion -/

/-- The pole order of `f` at `i∞`, as a natural number: the order of the pole at `0` of the cusp
function of `f`, and `0` if there is no pole. -/
private def cuspPoleOrder (h : ℝ) (f : ℍ → ℂ) : ℕ :=
  (-(meromorphicOrderAt (cuspFunction h f) 0).untop₀).toNat

/-- The pole order bounds the order of the cusp function from below. -/
private theorem neg_cuspPoleOrder_le (h : ℝ) (f : ℍ → ℂ) :
    ((-(cuspPoleOrder h f : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h f) 0 := by
  cases hn : meromorphicOrderAt (cuspFunction h f) 0 using WithTop.recTopCoe with
  | top => exact le_top
  | coe n =>
    simp only [cuspPoleOrder, hn, WithTop.untop₀_coe]
    exact WithTop.coe_le_coe.mpr (by omega)

/-- The **Laurent `q`-expansion** of a function `f` on the upper half-plane at `i∞`, in the
`q`-parameter `q = exp (2 π i τ / h)`. When the cusp function of `f` is meromorphic at `q = 0`
with a pole of order `k`, then `𝕢 ^ k * f` has an analytic cusp function, and the Laurent
expansion is its `q`-expansion shifted down by `k`. -/
def laurentQExpansion (h : ℝ) (f : ℍ → ℂ) : LaurentSeries ℂ :=
  HahnSeries.single (-(cuspPoleOrder h f : ℤ)) 1 *
    (qExpansion h (fun τ ↦ 𝕢 h τ ^ cuspPoleOrder h f * f τ) : LaurentSeries ℂ)

/-- Multiplying a twisted `q`-expansion by `X ^ m` twists further by `𝕢 ^ m`. -/
private theorem qExpansion_qParam_pow_add_mul (hh : 0 < h) {k : ℕ} (m : ℕ)
    (hk : AnalyticAt ℂ (cuspFunction h (fun τ ↦ 𝕢 h τ ^ k * f τ)) 0) :
    qExpansion h (fun τ ↦ 𝕢 h τ ^ (k + m) * f τ) =
      PowerSeries.X ^ m * qExpansion h (fun τ ↦ 𝕢 h τ ^ k * f τ) := by
  have hfun : (fun τ : ℍ ↦ 𝕢 h τ ^ (k + m) * f τ) =
      (fun τ : ℍ ↦ 𝕢 h τ ^ m) * fun τ : ℍ ↦ 𝕢 h τ ^ k * f τ := by
    funext τ
    simp only [Pi.mul_apply]
    ring
  rw [hfun, qExpansion_mul (analyticAt_cuspFunction_qParam_pow hh m) hk, qExpansion_qParam_pow hh]

/-- **Independence of the twisting exponent.** The Laurent `q`-expansion is the `q`-expansion of
`𝕢 ^ k * f` shifted down by `k`, for every `k` bounding the order of the pole at `i∞`. -/
theorem laurentQExpansion_eq (hh : 0 < h) (hf : MeromorphicAt (cuspFunction h f) 0) {k : ℕ}
    (hk : ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h f) 0) :
    laurentQExpansion h f = HahnSeries.single (-(k : ℤ)) 1 *
      (qExpansion h (fun τ ↦ 𝕢 h τ ^ k * f τ) : LaurentSeries ℂ) := by
  have key : ∀ {k : ℕ}, ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h f) 0 →
      ∀ m : ℕ, HahnSeries.single (-((k + m : ℕ) : ℤ)) 1 *
        (qExpansion h (fun τ ↦ 𝕢 h τ ^ (k + m) * f τ) : LaurentSeries ℂ) =
        HahnSeries.single (-(k : ℤ)) 1 *
          (qExpansion h (fun τ ↦ 𝕢 h τ ^ k * f τ) : LaurentSeries ℂ) := by
    intro k hk m
    rw [qExpansion_qParam_pow_add_mul hh m (analyticAt_cuspFunction_qParam_pow_mul hh hf hk),
      PowerSeries.coe_mul, PowerSeries.coe_pow, PowerSeries.coe_X, HahnSeries.single_pow, ←
      mul_assoc, HahnSeries.single_mul_single, one_pow, one_mul]
    congr 3
    simp only [Nat.cast_add, nsmul_eq_mul, mul_one]
    omega
  rw [laurentQExpansion, ← key (neg_cuspPoleOrder_le h f) k, add_comm, key hk]

/-- The Laurent `q`-expansion only depends on the cusp function off `q = 0`. -/
theorem laurentQExpansion_congr (hh : 0 < h)
    (hfg : cuspFunction h f =ᶠ[𝓝[≠] 0] cuspFunction h g) :
    laurentQExpansion h f = laurentQExpansion h g := by
  have hk : cuspPoleOrder h f = cuspPoleOrder h g := by
    simp only [cuspPoleOrder, meromorphicOrderAt_congr hfg]
  rw [laurentQExpansion, laurentQExpansion, hk, qExpansion_congr]
  refine (cuspFunction_qParam_pow_mul_eventuallyEq hh _ f).trans ?_
  refine EventuallyEq.trans ?_ (cuspFunction_qParam_pow_mul_eventuallyEq hh _ g).symm
  filter_upwards [hfg] with q hq
  rw [hq]

/-- When the cusp function of `f` is analytic at `0`, the Laurent `q`-expansion is the
`q`-expansion. -/
theorem laurentQExpansion_of_analyticAt (hh : 0 < h) (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    laurentQExpansion h f = qExpansion h f := by
  rw [laurentQExpansion_eq hh hf.meromorphicAt (k := 0)
    (by simpa using hf.meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr hf)]
  simp

/-- The coefficients of the Laurent `q`-expansion are those of the `q`-expansion of `𝕢 ^ k * f`,
shifted down by `k`. -/
theorem laurentQExpansion_coeff_natCast_sub (hh : 0 < h)
    (hf : MeromorphicAt (cuspFunction h f) 0) {k : ℕ}
    (hk : ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h f) 0) (n : ℕ) :
    (laurentQExpansion h f).coeff ((n : ℤ) - k) =
      (qExpansion h (fun τ ↦ 𝕢 h τ ^ k * f τ)).coeff n := by
  rw [laurentQExpansion_eq hh hf hk, HahnSeries.coeff_single_mul, one_mul,
    PowerSeries.coeff_coe]
  simp

/-- The coefficients of the Laurent `q`-expansion vanish below the order of the pole. -/
theorem laurentQExpansion_coeff_eq_zero_of_lt_neg (hh : 0 < h)
    (hf : MeromorphicAt (cuspFunction h f) 0) {k : ℕ}
    (hk : ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h f) 0) {n : ℤ}
    (hn : n < -k) :
    (laurentQExpansion h f).coeff n = 0 := by
  rw [laurentQExpansion_eq hh hf hk, HahnSeries.coeff_single_mul, one_mul,
    PowerSeries.coeff_coe]
  split_ifs
  · rfl
  · omega

/-! ### The order at `i∞` -/

/-- **The order at `i∞`.** The order of the Laurent `q`-expansion is the order at `0` of the cusp
function, with value `⊤` exactly for the zero expansion. -/
theorem orderTop_laurentQExpansion (hh : 0 < h) (hf : MeromorphicAt (cuspFunction h f) 0) :
    (laurentQExpansion h f).orderTop = meromorphicOrderAt (cuspFunction h f) 0 := by
  have hk := neg_cuspPoleOrder_le h f
  have han := analyticAt_cuspFunction_qParam_pow_mul hh hf hk
  rw [laurentQExpansion, HahnSeries.orderTop_mul, HahnSeries.orderTop_single one_ne_zero,
    PowerSeries.orderTop_coe, TauCeti.qExpansion_order_eq_analyticOrderAt_cuspFunction han,
    ← han.meromorphicOrderAt_eq,
    meromorphicOrderAt_congr (cuspFunction_qParam_pow_mul_eventuallyEq hh _ f),
    meromorphicOrderAt_qParam_pow_mul hf]
  cases hn : meromorphicOrderAt (cuspFunction h f) 0 using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    norm_cast
    omega

/-- **Uniqueness of the Laurent `q`-expansion.** The Laurent `q`-expansion vanishes exactly when
the cusp function vanishes on a punctured neighbourhood of `0`. -/
theorem laurentQExpansion_eq_zero_iff (hh : 0 < h) (hf : MeromorphicAt (cuspFunction h f) 0) :
    laurentQExpansion h f = 0 ↔ ∀ᶠ q in 𝓝[≠] 0, cuspFunction h f q = 0 := by
  rw [← HahnSeries.orderTop_eq_top, orderTop_laurentQExpansion hh hf, meromorphicOrderAt_eq_top_iff]

/-! ### Field operations -/

/-- Off `q = 0`, the cusp function is evaluated at the logarithm of `q`. -/
private theorem cuspFunction_of_ne_zero {q : ℂ} (hq : q ≠ 0) (f : ℍ → ℂ) :
    cuspFunction h f q = f (ofComplex (Periodic.invQParam h q)) := by
  simp [cuspFunction, Periodic.cuspFunction_eq_of_nonzero _ _ hq]

/-- Off `q = 0`, cusp functions commute with pointwise binary operations. -/
private theorem cuspFunction_map₂_eventuallyEq (op : ℂ → ℂ → ℂ) (f g : ℍ → ℂ) :
    cuspFunction h (fun τ ↦ op (f τ) (g τ)) =ᶠ[𝓝[≠] 0]
      fun q ↦ op (cuspFunction h f q) (cuspFunction h g q) :=
  eventually_nhdsWithin_of_forall fun q hq ↦ by
    simp only [cuspFunction_of_ne_zero (Set.mem_compl_singleton_iff.mp hq)]

/-- Off `q = 0`, cusp functions commute with pointwise operations. -/
private theorem cuspFunction_map_eventuallyEq (op : ℂ → ℂ) (f : ℍ → ℂ) :
    cuspFunction h (fun τ ↦ op (f τ)) =ᶠ[𝓝[≠] 0] fun q ↦ op (cuspFunction h f q) :=
  eventually_nhdsWithin_of_forall fun q hq ↦ by
    simp only [cuspFunction_of_ne_zero (Set.mem_compl_singleton_iff.mp hq)]

/-- The Laurent `q`-expansion of a constant function is the constant Laurent series. -/
@[simp]
theorem laurentQExpansion_const (hh : 0 < h) (c : ℂ) :
    laurentQExpansion h (fun _ ↦ c) = HahnSeries.C c := by
  have hc : (fun _ : ℍ ↦ c) = c • (1 : ℍ → ℂ) := by
    funext
    simp
  have han : AnalyticAt ℂ (cuspFunction h (1 : ℍ → ℂ)) 0 := by
    simpa [Pi.one_def] using analyticAt_cuspFunction_qParam_pow hh 0
  have hcan : AnalyticAt ℂ (cuspFunction h fun _ : ℍ ↦ c) 0 := by
    rw [hc, cuspFunction_smul han.continuousAt]
    exact analyticAt_const.smul han
  rw [laurentQExpansion_of_analyticAt hh hcan, hc, qExpansion_smul han, qExpansion_one,
    PowerSeries.coe_smul, PowerSeries.coe_one, ← HahnSeries.C_mul_eq_smul, mul_one]

/-- The Laurent `q`-expansion of `1` is `1`. -/
@[simp]
theorem laurentQExpansion_one (hh : 0 < h) : laurentQExpansion h (1 : ℍ → ℂ) = 1 := by
  rw [Pi.one_def, laurentQExpansion_const hh, map_one]

/-- The Laurent `q`-expansion of `0` is `0`. -/
@[simp]
theorem laurentQExpansion_zero (hh : 0 < h) : laurentQExpansion h (0 : ℍ → ℂ) = 0 := by
  rw [Pi.zero_def, laurentQExpansion_const hh, map_zero]

/-- The Laurent `q`-expansion is multiplicative. -/
theorem laurentQExpansion_mul (hh : 0 < h) (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) :
    laurentQExpansion h (f * g) = laurentQExpansion h f * laurentQExpansion h g := by
  have heq : cuspFunction h (f * g) =ᶠ[𝓝[≠] 0] cuspFunction h f * cuspFunction h g :=
    cuspFunction_map₂_eventuallyEq (· * ·) f g
  have hfg : MeromorphicAt (cuspFunction h (f * g)) 0 := (hf.mul hg).congr heq.symm
  set k := cuspPoleOrder h f
  set l := cuspPoleOrder h g
  have hk : ((-(k + l : ℕ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h (f * g)) 0 := by
    rw [meromorphicOrderAt_congr heq, meromorphicOrderAt_mul hf hg]
    calc ((-(k + l : ℕ) : ℤ) : WithTop ℤ) = ((-k : ℤ) : WithTop ℤ) + ((-l : ℤ) : WithTop ℤ) := by
          norm_cast
          omega
      _ ≤ _ := add_le_add (neg_cuspPoleOrder_le h f) (neg_cuspPoleOrder_le h g)
  have hfun : (fun τ : ℍ ↦ 𝕢 h τ ^ (k + l) * (f * g) τ) =
      (fun τ : ℍ ↦ 𝕢 h τ ^ k * f τ) * fun τ : ℍ ↦ 𝕢 h τ ^ l * g τ := by
    funext τ
    simp only [Pi.mul_apply]
    ring
  have hs : HahnSeries.single (-((k + l : ℕ) : ℤ)) (1 : ℂ) =
      HahnSeries.single (-(k : ℤ)) 1 * HahnSeries.single (-(l : ℤ)) 1 := by
    rw [HahnSeries.single_mul_single, one_mul]
    congr 2
    push_cast
    ring
  rw [laurentQExpansion_eq hh hfg hk, hfun, qExpansion_mul
    (analyticAt_cuspFunction_qParam_pow_mul hh hf (neg_cuspPoleOrder_le h f))
    (analyticAt_cuspFunction_qParam_pow_mul hh hg (neg_cuspPoleOrder_le h g)),
    PowerSeries.coe_mul, hs, laurentQExpansion, laurentQExpansion]
  ring

/-- The Laurent `q`-expansion is additive. -/
theorem laurentQExpansion_add (hh : 0 < h) (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) :
    laurentQExpansion h (f + g) = laurentQExpansion h f + laurentQExpansion h g := by
  have heq : cuspFunction h (f + g) =ᶠ[𝓝[≠] 0] cuspFunction h f + cuspFunction h g :=
    cuspFunction_map₂_eventuallyEq (· + ·) f g
  have hfg : MeromorphicAt (cuspFunction h (f + g)) 0 := (hf.add hg).congr heq.symm
  set k := max (cuspPoleOrder h f) (cuspPoleOrder h g)
  have hkf : ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h f) 0 :=
    le_trans (WithTop.coe_le_coe.mpr (by omega)) (neg_cuspPoleOrder_le h f)
  have hkg : ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h g) 0 :=
    le_trans (WithTop.coe_le_coe.mpr (by omega)) (neg_cuspPoleOrder_le h g)
  have hk : ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h (f + g)) 0 := by
    rw [meromorphicOrderAt_congr heq]
    exact (le_min hkf hkg).trans (meromorphicOrderAt_add hf hg)
  have hfun : (fun τ : ℍ ↦ 𝕢 h τ ^ k * (f + g) τ) =
      (fun τ : ℍ ↦ 𝕢 h τ ^ k * f τ) + fun τ : ℍ ↦ 𝕢 h τ ^ k * g τ := by
    funext τ
    simp only [Pi.add_apply]
    ring
  rw [laurentQExpansion_eq hh hfg hk, laurentQExpansion_eq hh hf hkf,
    laurentQExpansion_eq hh hg hkg, hfun, qExpansion_add
    (analyticAt_cuspFunction_qParam_pow_mul hh hf hkf)
    (analyticAt_cuspFunction_qParam_pow_mul hh hg hkg), PowerSeries.coe_add, mul_add]

/-- The Laurent `q`-expansion commutes with scalar multiplication. -/
theorem laurentQExpansion_smul (hh : 0 < h) (hf : MeromorphicAt (cuspFunction h f) 0) (c : ℂ) :
    laurentQExpansion h (c • f) = c • laurentQExpansion h f := by
  have hc : c • f = (fun _ ↦ c) * f := by
    funext
    simp
  have hcf : MeromorphicAt (cuspFunction h fun _ : ℍ ↦ c) 0 :=
    (analyticAt_const (v := c)).meromorphicAt.congr
      (cuspFunction_map_eventuallyEq (h := h) (fun _ ↦ c) f).symm
  rw [hc, laurentQExpansion_mul hh hcf hf, laurentQExpansion_const hh, HahnSeries.C_mul_eq_smul]

/-- The Laurent `q`-expansion commutes with negation. -/
@[simp]
theorem laurentQExpansion_neg (hh : 0 < h) (hf : MeromorphicAt (cuspFunction h f) 0) :
    laurentQExpansion h (-f) = -laurentQExpansion h f := by
  rw [show -f = (-1 : ℂ) • f by simp, laurentQExpansion_smul hh hf]
  exact neg_one_smul ℂ (laurentQExpansion h f)

/-- The Laurent `q`-expansion commutes with subtraction. -/
theorem laurentQExpansion_sub (hh : 0 < h) (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) :
    laurentQExpansion h (f - g) = laurentQExpansion h f - laurentQExpansion h g := by
  have hng : MeromorphicAt (cuspFunction h (-g)) 0 :=
    hg.neg.congr (cuspFunction_map_eventuallyEq (h := h) (- ·) g).symm
  rw [sub_eq_add_neg, laurentQExpansion_add hh hf hng, laurentQExpansion_neg hh hg, sub_eq_add_neg]

/-- The Laurent `q`-expansion commutes with powers. -/
theorem laurentQExpansion_pow (hh : 0 < h) (hf : MeromorphicAt (cuspFunction h f) 0) (n : ℕ) :
    laurentQExpansion h (f ^ n) = laurentQExpansion h f ^ n := by
  induction n with
  | zero => simpa using laurentQExpansion_one hh
  | succ n ih =>
    have hfn : MeromorphicAt (cuspFunction h (f ^ n)) 0 :=
      (hf.pow n).congr (cuspFunction_map_eventuallyEq (h := h) (· ^ n) f).symm
    rw [pow_succ, laurentQExpansion_mul hh hfn hf, ih, pow_succ]

/-- The Laurent `q`-expansion commutes with inverses. This includes functions vanishing near
`i∞`, whose expansion and inverse are both `0`. -/
theorem laurentQExpansion_inv (hh : 0 < h) (hf : MeromorphicAt (cuspFunction h f) 0) :
    laurentQExpansion h f⁻¹ = (laurentQExpansion h f)⁻¹ := by
  have heq : cuspFunction h f⁻¹ =ᶠ[𝓝[≠] 0] (cuspFunction h f)⁻¹ :=
    cuspFunction_map_eventuallyEq (·⁻¹) f
  have hfi : MeromorphicAt (cuspFunction h f⁻¹) 0 := hf.inv.congr heq.symm
  by_cases htop : meromorphicOrderAt (cuspFunction h f) 0 = ⊤
  · have hzero := meromorphicOrderAt_eq_top_iff.mp htop
    rw [(laurentQExpansion_eq_zero_iff hh hf).mpr hzero, inv_zero,
      laurentQExpansion_eq_zero_iff hh hfi]
    filter_upwards [heq, hzero] with q h₁ h₂
    rw [h₁, Pi.inv_apply, h₂, inv_zero]
  · have hne := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf).mp htop
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← laurentQExpansion_mul hh hf hfi, ← laurentQExpansion_one hh]
    refine laurentQExpansion_congr hh ?_
    filter_upwards [self_mem_nhdsWithin, hne] with q hq hq'
    rw [cuspFunction_of_ne_zero hq] at hq'
    rw [cuspFunction_of_ne_zero hq, cuspFunction_of_ne_zero hq, Pi.mul_apply, Pi.inv_apply,
      mul_inv_cancel₀ hq', Pi.one_apply]

/-- The Laurent `q`-expansion commutes with quotients. -/
theorem laurentQExpansion_div (hh : 0 < h) (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) :
    laurentQExpansion h (f / g) = laurentQExpansion h f / laurentQExpansion h g := by
  have hgi : MeromorphicAt (cuspFunction h g⁻¹) 0 :=
    hg.inv.congr (cuspFunction_map_eventuallyEq (h := h) (·⁻¹) g).symm
  rw [div_eq_mul_inv, laurentQExpansion_mul hh hf hgi, laurentQExpansion_inv hh hg, div_eq_mul_inv]

/-! ### Convergence and the `q`-expansion principle -/

/-- **Convergence of the Laurent `q`-expansion.** A periodic function whose cusp function is
meromorphic at `0` is the sum of its Laurent `q`-expansion sufficiently high in the upper
half-plane. -/
theorem hasSum_laurentQExpansion (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hf : MeromorphicAt (cuspFunction h f) 0) :
    ∀ᶠ τ : ℍ in atImInfty,
      HasSum (fun n : ℤ ↦ (laurentQExpansion h f).coeff n * 𝕢 h τ ^ n) (f τ) := by
  set k := cuspPoleOrder h f
  have hk := neg_cuspPoleOrder_le h f
  obtain ⟨r, hr, hrF⟩ := (analyticAt_cuspFunction_qParam_pow_mul hh hf hk).exists_ball_analyticOnNhd
  have hFper : Periodic ((fun τ : ℍ ↦ 𝕢 h τ ^ k * f τ) ∘ ofComplex) h := fun z ↦ by
    simpa using congrArg₂ (fun a b ↦ a ^ k * b) (periodic_qParam_comp_ofComplex hh.ne' z) (hfper z)
  filter_upwards [(qParam_tendsto_atImInfty hh).eventually (Metric.ball_mem_nhds 0 hr)] with τ hτ
  have hq : 𝕢 h τ ≠ 0 := Periodic.qParam_ne_zero _
  have hsum := Complex.hasSum_taylorSeries_on_ball hrF.differentiableOn hτ
  rw [eq_cuspFunction τ hh.ne' hFper] at hsum
  have hsum' : HasSum
      (fun n : ℕ ↦ (laurentQExpansion h f).coeff ((n : ℤ) - k) * 𝕢 h τ ^ ((n : ℤ) - k)) (f τ) := by
    convert hsum.mul_left (𝕢 h τ ^ k)⁻¹ using 1
    · funext n
      rw [laurentQExpansion_coeff_natCast_sub hh hf hk, qExpansion_coeff, zpow_sub₀ hq]
      simp only [sub_zero, smul_eq_mul, zpow_natCast]
      field_simp
    · field_simp
  have hinj : Injective fun n : ℕ ↦ (n : ℤ) - k := fun a b hab ↦ by simpa using hab
  refine (hinj.hasSum_iff fun m hm ↦ ?_).mp hsum'
  have hm' : m < -k := by
    by_contra! H
    exact hm ⟨(m + k).toNat, by simp only; omega⟩
  rw [laurentQExpansion_coeff_eq_zero_of_lt_neg hh hf hk hm', zero_mul]

/-- Functions which agree sufficiently high in the upper half-plane have the same Laurent
`q`-expansion. -/
theorem laurentQExpansion_eq_of_eventuallyEq (hh : 0 < h) (hfg : f =ᶠ[atImInfty] g) :
    laurentQExpansion h f = laurentQExpansion h g := by
  refine laurentQExpansion_congr hh ?_
  filter_upwards [self_mem_nhdsWithin,
    (tendsto_comap_im_ofComplex.comp (Periodic.invQParam_tendsto hh)).eventually hfg] with q hq hq'
  rw [cuspFunction_of_ne_zero hq, cuspFunction_of_ne_zero hq]
  exact hq'

/-- **The `q`-expansion principle.** Two periodic functions whose cusp functions are meromorphic
at `0` have the same Laurent `q`-expansion exactly when they agree sufficiently high in the upper
half-plane. -/
theorem laurentQExpansion_eq_laurentQExpansion_iff (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hgper : Periodic (g ∘ ofComplex) h)
    (hf : MeromorphicAt (cuspFunction h f) 0) (hg : MeromorphicAt (cuspFunction h g) 0) :
    laurentQExpansion h f = laurentQExpansion h g ↔ f =ᶠ[atImInfty] g := by
  refine ⟨fun H ↦ ?_, laurentQExpansion_eq_of_eventuallyEq hh⟩
  have hfg : MeromorphicAt (cuspFunction h (f - g)) 0 :=
    (hf.sub hg).congr (cuspFunction_map₂_eventuallyEq (h := h) (· - ·) f g).symm
  have hzero := (laurentQExpansion_eq_zero_iff hh hfg).mp
    (by rw [laurentQExpansion_sub hh hf hg, H, sub_self])
  have hq : Tendsto (fun τ : ℍ ↦ 𝕢 h τ) atImInfty (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨qParam_tendsto_atImInfty hh, .of_forall fun τ ↦ Periodic.qParam_ne_zero _⟩
  have hper : Periodic ((f - g) ∘ ofComplex) h := hfper.sub hgper
  filter_upwards [hq.eventually hzero] with τ hτ
  rw [eq_cuspFunction τ hh.ne' hper, Pi.sub_apply, sub_eq_zero] at hτ
  exact hτ

end TauCeti.UpperHalfPlane
