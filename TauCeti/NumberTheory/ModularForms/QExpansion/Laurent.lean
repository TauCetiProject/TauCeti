/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Laurent
public import TauCeti.NumberTheory.ModularForms.QExpansion.Basic
public import TauCeti.RingTheory.LaurentSeries.Rescale
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.TaylorSeries
import TauCeti.Analysis.Complex.UpperHalfPlane.QExpansion.Order
import TauCeti.NumberTheory.ModularForms.QExpansion.Order
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
with Mathlib's `UpperHalfPlane.qExpansion` when the cusp function is analytic at `0`, in which case
its constant term is the value of the cusp function at `0`.

The Laurent `q`-expansion is compatible with the field operations: it is additive and
multiplicative, and it commutes with scalars, powers, inverses and quotients. It only depends on
the cusp function on a punctured neighbourhood of `0`. Its order is the order of the cusp function
at `0`, so it vanishes exactly when the cusp function vanishes near `0`, and for a periodic
function it converges to the function sufficiently high in the upper half-plane. This gives the
`q`-expansion principle: two periodic functions meromorphic at `i∞` have the same Laurent
`q`-expansion exactly when they agree near `i∞`. Passing from the period `h` to a multiple
`d * h`, or scaling the argument by `d : ℕ+`, substitutes `q ^ d` for `q`; scaling both the period
and the argument by the same positive real leaves the expansion unchanged; and translating the
argument by `s : ℝ` rescales `q` by `exp (2 π i s / h)`.

These are the expansions at `i∞` through which modular functions, and fields of modular
functions with prescribed Fourier coefficients, are described. Compare
`TauCeti.Subgroup.CuspDatum.laurentQExpansion`, which expands functions holomorphic on the whole
upper half-plane at an arbitrary cusp of a Fuchsian group, for a chosen growth exponent; by
`TauCeti.Subgroup.CuspDatum.laurentQExpansion_eq_upperHalfPlane_laurentQExpansion` it is the
expansion here of the function read in the scaling coordinate of the cusp.

## Main declarations

* `TauCeti.UpperHalfPlane.laurentQExpansion`: the Laurent `q`-expansion at `i∞`.
* `TauCeti.UpperHalfPlane.laurentQExpansion_eq`: its description through any admissible twisting
  exponent, `TauCeti.UpperHalfPlane.laurentQExpansion_eq_of_analyticAt_qParam_pow_mul` for any
  exponent making the twisted cusp function analytic, and
  `TauCeti.UpperHalfPlane.laurentQExpansion_of_analyticAt` at analytic points.
* `TauCeti.UpperHalfPlane.laurentQExpansion_add`, `TauCeti.UpperHalfPlane.laurentQExpansion_mul`,
  `TauCeti.UpperHalfPlane.laurentQExpansion_inv` and their companions: the field operations.
* `TauCeti.UpperHalfPlane.orderTop_laurentQExpansion`: the order at `i∞`.
* `TauCeti.UpperHalfPlane.laurentQExpansion_eq_zero_iff`: uniqueness of the expansion.
* `TauCeti.UpperHalfPlane.hasSum_laurentQExpansion`: convergence near `i∞`.
* `TauCeti.UpperHalfPlane.laurentQExpansion_eq_laurentQExpansion_iff`: the `q`-expansion
  principle.
* `TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_pnat_mul_iff` and
  `TauCeti.UpperHalfPlane.laurentQExpansion_pnat_mul`: meromorphy at `0` is preserved and reflected
  between periods `h` and `d * h`, and the expansion at period `d * h` substitutes `q ^ d` for `q`.
* `TauCeti.UpperHalfPlane.laurentQExpansion_posReal_mul` and
  `TauCeti.UpperHalfPlane.laurentQExpansion_pnat_smul`: scaling the argument by positive reals and
  by positive integers.
* `TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_vadd_iff` and
  `TauCeti.UpperHalfPlane.laurentQExpansion_vadd`: translating the argument by `s : ℝ` rescales `q`
  by `exp (2 π i s / h)`.
* `TauCeti.Subgroup.CuspDatum.laurentQExpansion_eq_upperHalfPlane_laurentQExpansion`: agreement
  with the Laurent expansion at a cusp of a Fuchsian group.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §2.1 (functions meromorphic at a cusp and their Laurent expansions in
  the local parameter at the cusp).
* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §1.1 and §2.4.
-/

public noncomputable section

open UpperHalfPlane Filter Topology Function
open scoped Manifold MatrixGroups

namespace TauCeti.UpperHalfPlane

variable {h : ℝ} {f g : ℍ → ℂ}

local notation "𝕢" => Function.Periodic.qParam

/-! ### Twisting by powers of the `q`-parameter -/

/-- The cusp function of `f` has a pole of order at most `k` at `0` exactly when twisting it by
`q ^ k` gives a nonnegative order. -/
private theorem neg_le_meromorphicOrderAt_iff {k : ℕ} (hf : MeromorphicAt (cuspFunction h f) 0) :
    ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h f) 0 ↔
      0 ≤ meromorphicOrderAt (fun q ↦ q ^ k * cuspFunction h f q) 0 := by
  rw [meromorphicOrderAt_pow_mul_cuspFunction hf]
  cases meromorphicOrderAt (cuspFunction h f) 0 using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    rw [WithTop.coe_le_coe, ← WithTop.coe_natCast, ← WithTop.coe_add, ← WithTop.coe_zero,
      WithTop.coe_le_coe]
    omega

/-- If the cusp function of `f` is meromorphic at `0` with a pole of order at most `k`, then the
cusp function of `𝕢 ^ k * f` is analytic at `0`. -/
theorem analyticAt_cuspFunction_qParam_pow_mul {k : ℕ}
    (hf : MeromorphicAt (cuspFunction h f) 0)
    (hk : ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h f) 0) :
    AnalyticAt ℂ (cuspFunction h (fun τ ↦ 𝕢 h τ ^ k * f τ)) 0 := by
  rcases le_or_gt h 0 with hh | hh
  · exact analyticAt_const.congr (cuspFunction_eventuallyEq_const_of_nonpos hh _).symm
  have hψ : MeromorphicAt (fun q ↦ q ^ k * cuspFunction h f q) 0 :=
    (analyticAt_id.pow k).meromorphicAt.mul hf
  have han := hψ.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp
    ((neg_le_meromorphicOrderAt_iff hf).mp hk)
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
  rw [hfun, qExpansion_mul (analyticAt_cuspFunction_qParam_pow h m) hk, qExpansion_qParam_pow hh]

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
    rw [qExpansion_qParam_pow_add_mul hh m (analyticAt_cuspFunction_qParam_pow_mul hf hk)]
    simp [HahnSeries.single_pow, ← mul_assoc, HahnSeries.single_mul_single]
  rw [laurentQExpansion, ← key (neg_cuspPoleOrder_le h f) k, add_comm, key hk]

/-- If the cusp function of `𝕢 ^ k * f` is analytic at `0`, then the cusp function of `f` is
meromorphic at `0`. -/
theorem meromorphicAt_cuspFunction_of_analyticAt_qParam_pow_mul {k : ℕ}
    (hk : AnalyticAt ℂ (cuspFunction h (fun τ ↦ 𝕢 h τ ^ k * f τ)) 0) :
    MeromorphicAt (cuspFunction h f) 0 := by
  rcases le_or_gt h 0 with hh | hh
  · exact (analyticAt_const.congr
      (cuspFunction_eventuallyEq_const_of_nonpos hh f).symm).meromorphicAt
  have heq : cuspFunction h f =ᶠ[𝓝[≠] 0]
      fun q ↦ (q ^ k)⁻¹ * cuspFunction h (fun τ ↦ 𝕢 h τ ^ k * f τ) q := by
    filter_upwards [cuspFunction_qParam_pow_mul_eventuallyEq hh k f,
      self_mem_nhdsWithin] with q h₁ hq
    rw [h₁, inv_mul_cancel_left₀ (pow_ne_zero k hq)]
  exact ((analyticAt_id.pow k).meromorphicAt.inv.mul hk.meromorphicAt).congr heq.symm

/-- If the cusp function of `𝕢 ^ k * f` is analytic at `0`, then the Laurent `q`-expansion of `f`
is the `q`-expansion of `𝕢 ^ k * f` shifted down by `k`. -/
theorem laurentQExpansion_eq_of_analyticAt_qParam_pow_mul (hh : 0 < h) {k : ℕ}
    (hk : AnalyticAt ℂ (cuspFunction h (fun τ ↦ 𝕢 h τ ^ k * f τ)) 0) :
    laurentQExpansion h f = HahnSeries.single (-(k : ℤ)) 1 *
      (qExpansion h (fun τ ↦ 𝕢 h τ ^ k * f τ) : LaurentSeries ℂ) := by
  have hf := meromorphicAt_cuspFunction_of_analyticAt_qParam_pow_mul hk
  refine laurentQExpansion_eq hh hf ((neg_le_meromorphicOrderAt_iff hf).mpr ?_)
  rw [← meromorphicOrderAt_congr (cuspFunction_qParam_pow_mul_eventuallyEq hh k f)]
  exact hk.meromorphicOrderAt_nonneg

/-- The pole order only depends on the cusp function off `q = 0`. -/
private theorem cuspPoleOrder_congr (hfg : cuspFunction h f =ᶠ[𝓝[≠] 0] cuspFunction h g) :
    cuspPoleOrder h f = cuspPoleOrder h g := by
  simp only [cuspPoleOrder, meromorphicOrderAt_congr hfg]

/-- When the cusp function of `f` is analytic at `0`, the Laurent `q`-expansion is the
`q`-expansion. -/
theorem laurentQExpansion_of_analyticAt (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    laurentQExpansion h f = qExpansion h f := by
  have hk : cuspPoleOrder h f = 0 := by simp [cuspPoleOrder, hf.meromorphicOrderAt_nonneg]
  rw [laurentQExpansion, hk]
  simp

/-- The Laurent `q`-expansion of a constant function is the constant Laurent series. -/
@[simp]
theorem laurentQExpansion_const (h : ℝ) (c : ℂ) :
    laurentQExpansion h (fun _ ↦ c) = HahnSeries.C c := by
  have hc : (fun _ : ℍ ↦ c) = c • (1 : ℍ → ℂ) := by
    funext
    simp
  have han : AnalyticAt ℂ (cuspFunction h (1 : ℍ → ℂ)) 0 := by
    rw [cuspFunction_one]
    exact analyticAt_const
  rw [laurentQExpansion_of_analyticAt (by rw [cuspFunction_const]; exact analyticAt_const), hc,
    qExpansion_smul han]
  simpa [qExpansion_one] using (HahnSeries.C_mul_eq_smul (r := c) (x := (1 : LaurentSeries ℂ))).symm

/-- The Laurent `q`-expansion of `1` is `1`. -/
@[simp]
theorem laurentQExpansion_one (h : ℝ) : laurentQExpansion h (1 : ℍ → ℂ) = 1 := by
  rw [Pi.one_def, laurentQExpansion_const, map_one]

/-- The Laurent `q`-expansion of `0` is `0`. -/
@[simp]
theorem laurentQExpansion_zero (h : ℝ) : laurentQExpansion h (0 : ℍ → ℂ) = 0 := by
  rw [Pi.zero_def, laurentQExpansion_const, map_zero]

/-- The Laurent `q`-expansion only depends on the cusp function off `q = 0`. -/
theorem laurentQExpansion_congr (hfg : cuspFunction h f =ᶠ[𝓝[≠] 0] cuspFunction h g) :
    laurentQExpansion h f = laurentQExpansion h g := by
  rcases le_or_gt h 0 with hh | hh
  · rw [laurentQExpansion_of_analyticAt
      (analyticAt_const.congr (cuspFunction_eventuallyEq_const_of_nonpos hh f).symm),
      laurentQExpansion_of_analyticAt
      (analyticAt_const.congr (cuspFunction_eventuallyEq_const_of_nonpos hh g).symm)]
    rw [qExpansion_congr hfg]
  rw [laurentQExpansion, laurentQExpansion, cuspPoleOrder_congr hfg, qExpansion_congr]
  refine (cuspFunction_qParam_pow_mul_eventuallyEq hh _ f).trans ?_
  refine EventuallyEq.trans ?_ (cuspFunction_qParam_pow_mul_eventuallyEq hh _ g).symm
  filter_upwards [hfg] with q hq
  rw [hq]

/-- For `h ≤ 0`, the Laurent `q`-expansion of `f` is the constant series with value
`f (Classical.choice inferInstance)`, the value of `f` at the junk value of `ofComplex`
outside `ℍ`. -/
theorem laurentQExpansion_of_nonpos (hh : h ≤ 0) (f : ℍ → ℂ) :
    laurentQExpansion h f = HahnSeries.C (f (Classical.choice inferInstance)) :=
  (laurentQExpansion_congr (by
    simpa using ((cuspFunction_eventuallyEq_const_of_nonpos hh f).filter_mono
      nhdsWithin_le_nhds : cuspFunction h f =ᶠ[𝓝[≠] 0] _))).trans (laurentQExpansion_const h _)

/-- When the cusp function of `f` is analytic at `0`, the constant term of the Laurent
`q`-expansion is the value of the cusp function at `0`. -/
theorem laurentQExpansion_coeff_zero_of_analyticAt
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    (laurentQExpansion h f).coeff 0 = cuspFunction h f 0 := by
  rw [laurentQExpansion_of_analyticAt hf]
  simpa [UpperHalfPlane.qExpansion_coeff] using
    HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (qExpansion h f) 0

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
theorem laurentQExpansion_coeff_eq_zero_of_lt_neg {k : ℕ}
    (hk : ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h f) 0) {n : ℤ}
    (hn : n < -k) :
    (laurentQExpansion h f).coeff n = 0 := by
  have hp : cuspPoleOrder h f ≤ k := by
    rw [cuspPoleOrder, Int.toNat_le, Int.neg_le_iff, WithTop.untop₀, WithTop.le_untopD_iff]
    exacts [hk, fun _ ↦ by omega]
  rw [laurentQExpansion, HahnSeries.coeff_single_mul, one_mul, PowerSeries.coeff_coe]
  split_ifs
  · rfl
  · omega

/-! ### The order at `i∞` -/

/-- **The order at `i∞`.** The order of the Laurent `q`-expansion is the order at `0` of the cusp
function, with value `⊤` exactly for the zero expansion. -/
theorem orderTop_laurentQExpansion (hf : MeromorphicAt (cuspFunction h f) 0) :
    (laurentQExpansion h f).orderTop = meromorphicOrderAt (cuspFunction h f) 0 := by
  rcases le_or_gt h 0 with hh | hh
  · have hc : cuspFunction h f =ᶠ[𝓝[≠] 0] _ :=
      (cuspFunction_eventuallyEq_const_of_nonpos hh f).filter_mono nhdsWithin_le_nhds
    rw [laurentQExpansion_of_nonpos hh, meromorphicOrderAt_congr hc, meromorphicOrderAt_const]
    by_cases hc0 : f (Classical.choice inferInstance) = 0 <;> simp [hc0]
  have hk := neg_cuspPoleOrder_le h f
  have han := analyticAt_cuspFunction_qParam_pow_mul hf hk
  rw [laurentQExpansion, HahnSeries.orderTop_mul, HahnSeries.orderTop_single one_ne_zero,
    PowerSeries.orderTop_coe, TauCeti.qExpansion_order_eq_analyticOrderAt_cuspFunction han,
    ← han.meromorphicOrderAt_eq,
    meromorphicOrderAt_congr (cuspFunction_qParam_pow_mul_eventuallyEq hh _ f),
    meromorphicOrderAt_pow_mul_cuspFunction hf]
  cases hn : meromorphicOrderAt (cuspFunction h f) 0 using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    norm_cast
    omega

/-- **Uniqueness of the Laurent `q`-expansion.** The Laurent `q`-expansion vanishes exactly when
the cusp function vanishes on a punctured neighbourhood of `0`. -/
theorem laurentQExpansion_eq_zero_iff (hf : MeromorphicAt (cuspFunction h f) 0) :
    laurentQExpansion h f = 0 ↔ ∀ᶠ q in 𝓝[≠] 0, cuspFunction h f q = 0 := by
  rw [← HahnSeries.orderTop_eq_top, orderTop_laurentQExpansion hf, meromorphicOrderAt_eq_top_iff]

/-! ### Field operations -/

/-- The Laurent `q`-expansion is multiplicative. -/
theorem laurentQExpansion_mul (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) :
    laurentQExpansion h (f * g) = laurentQExpansion h f * laurentQExpansion h g := by
  rcases le_or_gt h 0 with hh | hh
  · simp only [laurentQExpansion_of_nonpos hh, Pi.mul_apply, map_mul]
  have heq : cuspFunction h (f * g) =ᶠ[𝓝[≠] 0] cuspFunction h f * cuspFunction h g :=
    cuspFunction_map₂_eventuallyEq (· * ·) f g
  have hfg : MeromorphicAt (cuspFunction h (f * g)) 0 := meromorphicAt_cuspFunction_mul hf hg
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
    (analyticAt_cuspFunction_qParam_pow_mul hf (neg_cuspPoleOrder_le h f))
    (analyticAt_cuspFunction_qParam_pow_mul hg (neg_cuspPoleOrder_le h g)),
    PowerSeries.coe_mul, hs, laurentQExpansion, laurentQExpansion]
  ring

/-- The Laurent `q`-expansion is additive. -/
theorem laurentQExpansion_add (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) :
    laurentQExpansion h (f + g) = laurentQExpansion h f + laurentQExpansion h g := by
  rcases le_or_gt h 0 with hh | hh
  · rw [laurentQExpansion_of_nonpos hh, laurentQExpansion_of_nonpos hh,
      laurentQExpansion_of_nonpos hh, Pi.add_apply, map_add]
  have heq : cuspFunction h (f + g) =ᶠ[𝓝[≠] 0] cuspFunction h f + cuspFunction h g :=
    cuspFunction_map₂_eventuallyEq (· + ·) f g
  have hfg : MeromorphicAt (cuspFunction h (f + g)) 0 := meromorphicAt_cuspFunction_add hf hg
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
    (analyticAt_cuspFunction_qParam_pow_mul hf hkf)
    (analyticAt_cuspFunction_qParam_pow_mul hg hkg), PowerSeries.coe_add, mul_add]

/-- The Laurent `q`-expansion commutes with scalar multiplication. -/
theorem laurentQExpansion_smul (hf : MeromorphicAt (cuspFunction h f) 0) (c : ℂ) :
    laurentQExpansion h (c • f) = c • laurentQExpansion h f := by
  have hc : c • f = (fun _ ↦ c) * f := by
    funext
    simp
  rw [hc, laurentQExpansion_mul (meromorphicAt_cuspFunction_const c) hf,
    laurentQExpansion_const, HahnSeries.C_mul_eq_smul]

/-- The Laurent `q`-expansion commutes with negation. -/
@[simp]
theorem laurentQExpansion_neg (hf : MeromorphicAt (cuspFunction h f) 0) :
    laurentQExpansion h (-f) = -laurentQExpansion h f := by
  rw [show -f = (-1 : ℂ) • f by simp, laurentQExpansion_smul hf]
  exact neg_one_smul ℂ (laurentQExpansion h f)

/-- The Laurent `q`-expansion commutes with subtraction. -/
theorem laurentQExpansion_sub (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) :
    laurentQExpansion h (f - g) = laurentQExpansion h f - laurentQExpansion h g := by
  rw [sub_eq_add_neg, laurentQExpansion_add hf (meromorphicAt_cuspFunction_neg hg),
    laurentQExpansion_neg hg, sub_eq_add_neg]

/-- The Laurent `q`-expansion commutes with powers. -/
theorem laurentQExpansion_pow (hf : MeromorphicAt (cuspFunction h f) 0) (n : ℕ) :
    laurentQExpansion h (f ^ n) = laurentQExpansion h f ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, laurentQExpansion_mul (meromorphicAt_cuspFunction_pow hf n) hf, ih, pow_succ]

/-- The Laurent `q`-expansion commutes with inverses. This includes the case where the cusp
function vanishes near `q = 0`, where both sides are `0`. -/
theorem laurentQExpansion_inv (hf : MeromorphicAt (cuspFunction h f) 0) :
    laurentQExpansion h f⁻¹ = (laurentQExpansion h f)⁻¹ := by
  have heq : cuspFunction h f⁻¹ =ᶠ[𝓝[≠] 0] (cuspFunction h f)⁻¹ :=
    cuspFunction_map_eventuallyEq (·⁻¹) f
  have hfi : MeromorphicAt (cuspFunction h f⁻¹) 0 := meromorphicAt_cuspFunction_inv hf
  by_cases htop : meromorphicOrderAt (cuspFunction h f) 0 = ⊤
  · have hzero := meromorphicOrderAt_eq_top_iff.mp htop
    rw [(laurentQExpansion_eq_zero_iff hf).mpr hzero, inv_zero,
      laurentQExpansion_eq_zero_iff hfi]
    filter_upwards [heq, hzero] with q h₁ h₂
    rw [h₁, Pi.inv_apply, h₂, inv_zero]
  · have hne := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf).mp htop
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← laurentQExpansion_mul hf hfi, ← laurentQExpansion_one h]
    refine laurentQExpansion_congr ?_
    filter_upwards [self_mem_nhdsWithin, hne] with q hq hq'
    rw [cuspFunction_of_ne_zero hq] at hq'
    rw [cuspFunction_of_ne_zero hq, cuspFunction_of_ne_zero hq, Pi.mul_apply, Pi.inv_apply,
      mul_inv_cancel₀ hq', Pi.one_apply]

/-- The Laurent `q`-expansion commutes with quotients. -/
theorem laurentQExpansion_div (hf : MeromorphicAt (cuspFunction h f) 0)
    (hg : MeromorphicAt (cuspFunction h g) 0) :
    laurentQExpansion h (f / g) = laurentQExpansion h f / laurentQExpansion h g := by
  rw [div_eq_mul_inv, laurentQExpansion_mul hf (meromorphicAt_cuspFunction_inv hg),
    laurentQExpansion_inv hg, div_eq_mul_inv]

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
  obtain ⟨r, hr, hrF⟩ := (analyticAt_cuspFunction_qParam_pow_mul hf hk).exists_ball_analyticOnNhd
  have hFper : Periodic ((fun τ : ℍ ↦ 𝕢 h τ ^ k * f τ) ∘ ofComplex) h := fun z ↦ by
    simpa using congrArg₂ (fun a b ↦ a ^ k * b) (periodic_qParam_comp_ofComplex z) (hfper z)
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
  rw [laurentQExpansion_coeff_eq_zero_of_lt_neg hk hm', zero_mul]

/-- Functions which agree sufficiently high in the upper half-plane have the same Laurent
`q`-expansion. -/
theorem laurentQExpansion_eq_of_eventuallyEq (hh : 0 < h) (hfg : f =ᶠ[atImInfty] g) :
    laurentQExpansion h f = laurentQExpansion h g := by
  refine laurentQExpansion_congr ?_
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
  have hzero := (laurentQExpansion_eq_zero_iff (meromorphicAt_cuspFunction_sub hf hg)).mp
    (by rw [laurentQExpansion_sub hf hg, H, sub_self])
  have hq : Tendsto (fun τ : ℍ ↦ 𝕢 h τ) atImInfty (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨qParam_tendsto_atImInfty hh, .of_forall fun τ ↦ Periodic.qParam_ne_zero _⟩
  have hper : Periodic ((f - g) ∘ ofComplex) h := hfper.sub hgper
  filter_upwards [hq.eventually hzero] with τ hτ
  rw [eq_cuspFunction τ hh.ne' hper, Pi.sub_apply, sub_eq_zero] at hτ
  exact hτ

/-! ### Changing the period, scaling, and translation -/

private theorem analyticAt_cuspFunction_of_nat_mul (hh : 0 < h) {d : ℕ} (hd : 0 < d)
    (hgper : Periodic (g ∘ ofComplex) h) (han : AnalyticAt ℂ (cuspFunction (d * h) g) 0) :
    AnalyticAt ℂ (cuspFunction h g) 0 := by
  have hdh : 0 < (d * h : ℝ) := mul_pos (Nat.cast_pos.mpr hd) hh
  have hgper_dh : Periodic (g ∘ ofComplex) ↑(d * h) := by simpa using hgper.nat_mul d
  have hG : g ∘ ofComplex = cuspFunction (d * h) g ∘ 𝕢 (d * h) :=
    funext fun z ↦ (Periodic.eq_cuspFunction hdh.ne' hgper_dh z).symm
  have hq_diff : Differentiable ℂ (𝕢 (d * h)) := by unfold Periodic.qParam; fun_prop
  have hq_tendsto : Tendsto (𝕢 (d * h)) (comap Complex.im atTop) (𝓝 0) :=
    tendsto_nhds_of_tendsto_nhdsWithin (Periodic.qParam_tendsto hdh)
  have h_hol : ∀ᶠ z in comap Complex.im atTop, DifferentiableAt ℂ (g ∘ ofComplex) z := by
    filter_upwards [hq_tendsto.eventually
      (Complex.analyticAt_iff_eventually_differentiableAt.mp han)] with z hz
    rw [hG]
    exact hz.comp z (hq_diff z)
  have h_bd : Filter.BoundedAtFilter (comap Complex.im atTop) (g ∘ ofComplex) := by
    rw [hG]
    exact (han.continuousAt.tendsto.comp hq_tendsto).isBigO_one ℝ
  rw [Complex.analyticAt_iff_eventually_differentiableAt, eventually_nhds_iff]
  obtain ⟨S, hS, hSopen, hS0⟩ := eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp
    (Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero hh hgper h_hol))
  refine ⟨S, fun q hq ↦ ?_, hSopen, hS0⟩
  rcases eq_or_ne q 0 with rfl | hq0
  · exact Periodic.differentiableAt_cuspFunction_zero hh hgper h_hol h_bd
  · exact hS q hq hq0

/-- For an `h`-periodic function, meromorphy of the cusp function at `0` is preserved and reflected
when multiplying the period by a positive integer `d`. -/
theorem meromorphicAt_cuspFunction_pnat_mul_iff (hfper : Periodic (f ∘ ofComplex) h) (d : ℕ+) :
    MeromorphicAt (cuspFunction ((d : ℕ) * h) f) 0 ↔ MeromorphicAt (cuspFunction h f) 0 := by
  rcases le_or_gt h 0 with hh | hh
  · exact iff_of_true
      ((analyticAt_const.congr (cuspFunction_eventuallyEq_const_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hh) f).symm).meromorphicAt)
      ((analyticAt_const.congr (cuspFunction_eventuallyEq_const_of_nonpos hh f).symm).meromorphicAt)
  refine ⟨fun hfm ↦ ?_, fun hf ↦ ?_⟩
  · set k := cuspPoleOrder ((d : ℕ) * h) f
    set g : ℍ → ℂ := fun τ ↦ 𝕢 h τ ^ k * f τ
    have hg : (fun τ : ℍ ↦ 𝕢 ((d : ℕ) * h) τ ^ ((d : ℕ) * k) * f τ) = g := by
      funext τ; rw [pow_mul, TauCeti.Periodic.qParam_nat_mul_pow d.ne_zero]
    have hk : ((-((d : ℕ) * k : ℕ) : ℤ) : WithTop ℤ) ≤
        meromorphicOrderAt (cuspFunction ((d : ℕ) * h) f) 0 :=
      (WithTop.coe_le_coe.mpr (Int.neg_le_neg (Nat.cast_le.mpr
        (Nat.le_mul_of_pos_left k d.pos)))).trans (neg_cuspPoleOrder_le _ f)
    have han : AnalyticAt ℂ (cuspFunction ((d : ℕ) * h) g) 0 :=
      hg ▸ analyticAt_cuspFunction_qParam_pow_mul hfm hk
    have hgper : Periodic (g ∘ ofComplex) h := fun z ↦ by
      simpa [g] using congrArg₂ (fun a b ↦ a ^ k * b) (periodic_qParam_comp_ofComplex z) (hfper z)
    exact meromorphicAt_cuspFunction_of_analyticAt_qParam_pow_mul
      (analyticAt_cuspFunction_of_nat_mul hh d.pos hgper han)
  · set k := cuspPoleOrder h f
    set g : ℍ → ℂ := fun τ ↦ 𝕢 h τ ^ k * f τ
    have han : AnalyticAt ℂ (cuspFunction h g) 0 :=
      analyticAt_cuspFunction_qParam_pow_mul hf (neg_cuspPoleOrder_le h f)
    have hgper : Periodic (g ∘ ofComplex) h := fun z ↦ by
      simpa [g] using congrArg₂ (fun a b ↦ a ^ k * b) (periodic_qParam_comp_ofComplex z) (hfper z)
    have hg : (fun τ : ℍ ↦ 𝕢 ((d : ℕ) * h) τ ^ ((d : ℕ) * k) * f τ) = g := by
      funext τ; rw [pow_mul, TauCeti.Periodic.qParam_nat_mul_pow d.ne_zero]
    exact meromorphicAt_cuspFunction_of_analyticAt_qParam_pow_mul
      (hg.symm ▸ analyticAt_cuspFunction_nat_mul hh.ne' d.pos hgper han)

/-- **The Laurent `q`-expansion at period `d * h`.** For an `h`-periodic function whose cusp
function is meromorphic at `0`, the Laurent `q`-expansion at period `d * h` is the expansion at
period `h` in the variable `q ^ d`: since `𝕢 (d * h) ^ d = 𝕢 h`, the coefficient of `q ^ n` at
period `h` becomes the coefficient of `q ^ (d * n)`. -/
theorem laurentQExpansion_pnat_mul (hfper : Periodic (f ∘ ofComplex) h)
    (hf : MeromorphicAt (cuspFunction h f) 0) (d : ℕ+) :
    laurentQExpansion ((d : ℕ) * h) f = LaurentSeries.expand ℂ d (laurentQExpansion h f) := by
  rcases le_or_gt h 0 with hh | hh
  · rw [laurentQExpansion_of_nonpos hh, laurentQExpansion_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hh), HahnSeries.C_apply,
      LaurentSeries.expand_single]
    simp
  set k := cuspPoleOrder h f
  set g : ℍ → ℂ := fun τ ↦ 𝕢 h τ ^ k * f τ
  have han : AnalyticAt ℂ (cuspFunction h g) 0 :=
    analyticAt_cuspFunction_qParam_pow_mul hf (neg_cuspPoleOrder_le h f)
  have hgper : Periodic (g ∘ ofComplex) h := fun z ↦ by
    simpa [g] using congrArg₂ (fun a b ↦ a ^ k * b) (periodic_qParam_comp_ofComplex z)
      (hfper z)
  -- twisting by `𝕢 (d * h) ^ (d * k) = 𝕢 h ^ k` at period `d * h` gives the same function `g`
  have hg : (fun τ : ℍ ↦ 𝕢 ((d : ℕ) * h) τ ^ ((d : ℕ) * k) * f τ) = g := by
    funext τ
    rw [pow_mul, TauCeti.Periodic.qParam_nat_mul_pow d.ne_zero]
  have han' := analyticAt_cuspFunction_nat_mul hh.ne' d.pos hgper han
  rw [← hg] at han'
  rw [laurentQExpansion_eq_of_analyticAt_qParam_pow_mul (by positivity) han', hg,
    TauCeti.qExpansion_nat_mul hh.ne' d.pos hgper han,
    laurentQExpansion_eq_of_analyticAt_qParam_pow_mul hh han, map_mul, LaurentSeries.expand_single,
    LaurentSeries.expand_coe, mul_neg, Nat.cast_mul]

/-- Off `q = 0` and inside the unit disc, scaling the period by a positive real `x` and the
argument by `x⁻¹` leaves the cusp function unchanged. -/
theorem cuspFunction_posReal_mul_eventuallyEq_nhdsNE (hh : 0 < h) {x : ℝ} (hx : 0 < x)
    (f : ℍ → ℂ) :
    cuspFunction (x * h) (fun τ ↦ f ((⟨x⁻¹, inv_pos.mpr hx⟩ : {y : ℝ // 0 < y}) • τ)) =ᶠ[𝓝[≠] 0]
      cuspFunction h f := by
  have hxh : 0 < x * h := mul_pos hx hh
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)] with q hq hqn
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hq
  have him := Periodic.im_invQParam_pos_of_norm_lt_one hh (mem_ball_zero_iff.mp hqn) hq
  have him' := Periodic.im_invQParam_pos_of_norm_lt_one hxh (mem_ball_zero_iff.mp hqn) hq
  rw [cuspFunction_of_ne_zero hq, cuspFunction_of_ne_zero hq]
  congr 1
  ext
  rw [coe_pos_real_smul, ofComplex_apply_of_im_pos him, ofComplex_apply_of_im_pos him']
  simp only [Complex.real_smul, Periodic.invQParam, Complex.ofReal_mul, Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr hx.ne']

/-- Scaling the period by a positive real `x` and the argument by `x⁻¹` preserves and reflects
meromorphy of the cusp function at `0`. -/
theorem meromorphicAt_cuspFunction_posReal_mul_iff {x : ℝ} (hx : 0 < x) (f : ℍ → ℂ) :
    MeromorphicAt
      (cuspFunction (x * h) (fun τ ↦ f ((⟨x⁻¹, inv_pos.mpr hx⟩ : {y : ℝ // 0 < y}) • τ))) 0 ↔
      MeromorphicAt (cuspFunction h f) 0 := by
  rcases le_or_gt h 0 with hh | hh
  · exact iff_of_true
      ((analyticAt_const.congr (cuspFunction_eventuallyEq_const_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos hx.le hh) _).symm).meromorphicAt)
      ((analyticAt_const.congr (cuspFunction_eventuallyEq_const_of_nonpos hh f).symm).meromorphicAt)
  · have heq := cuspFunction_posReal_mul_eventuallyEq_nhdsNE hh hx f
    exact ⟨fun H ↦ H.congr heq, fun H ↦ H.congr heq.symm⟩

/-- Scaling the period by a positive real `x` and the argument by `x⁻¹` leaves the Laurent
`q`-expansion unchanged. -/
theorem laurentQExpansion_posReal_mul (hh : 0 < h) {x : ℝ} (hx : 0 < x) (f : ℍ → ℂ) :
    laurentQExpansion (x * h) (fun τ ↦ f ((⟨x⁻¹, inv_pos.mpr hx⟩ : {y : ℝ // 0 < y}) • τ)) =
      laurentQExpansion h f := by
  let g : ℍ → ℂ := fun τ ↦ f ((⟨x⁻¹, inv_pos.mpr hx⟩ : {y : ℝ // 0 < y}) • τ)
  have hfg : cuspFunction (x * h) g =ᶠ[𝓝[≠] 0] cuspFunction h f :=
    cuspFunction_posReal_mul_eventuallyEq_nhdsNE hh hx f
  have hk : cuspPoleOrder (x * h) g = cuspPoleOrder h f := by
    simp only [cuspPoleOrder, meromorphicOrderAt_congr hfg]
  have hfg_k :
      cuspFunction (x * h) (fun τ ↦ 𝕢 (x * h) τ ^ cuspPoleOrder h f * g τ) =ᶠ[𝓝[≠] 0]
        cuspFunction h (fun τ ↦ 𝕢 h τ ^ cuspPoleOrder h f * f τ) :=
    (cuspFunction_qParam_pow_mul_eventuallyEq (mul_pos hx hh) _ g).trans <|
      EventuallyEq.trans (hfg.mono fun q hq ↦ by dsimp only; rw [hq])
        (cuspFunction_qParam_pow_mul_eventuallyEq hh _ f).symm
  have hfg_nhds :
      cuspFunction (x * h) (fun τ ↦ 𝕢 (x * h) τ ^ cuspPoleOrder h f * g τ) =ᶠ[𝓝 0]
        cuspFunction h (fun τ ↦ 𝕢 h τ ^ cuspPoleOrder h f * f τ) := by
    refine eventuallyEq_nhds_of_eventuallyEq_nhdsNE hfg_k ?_
    simp only [cuspFunction]
    rw [Periodic.cuspFunction_zero_eq_limUnder_nhds_ne,
      Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
    exact congrArg lim (Filter.map_congr hfg_k)
  rw [show (fun τ ↦ f ((⟨x⁻¹, inv_pos.mpr hx⟩ : {y : ℝ // 0 < y}) • τ)) = g from rfl,
    laurentQExpansion, laurentQExpansion, hk]
  congr 2
  ext n
  rw [_root_.UpperHalfPlane.qExpansion_coeff, _root_.UpperHalfPlane.qExpansion_coeff,
    hfg_nhds.iteratedDeriv_eq]

private theorem periodic_pnat_smul_div_of_periodic (hfper : Periodic (f ∘ ofComplex) h)
    (d : ℕ+) :
    Periodic
      ((fun τ : ℍ ↦ f ((⟨(d : ℝ), Nat.cast_pos.mpr d.pos⟩ : {y : ℝ // 0 < y}) • τ)) ∘
        ofComplex) ↑(h / (d : ℝ)) := by
  let x : {y : ℝ // 0 < y} := ⟨(d : ℝ), Nat.cast_pos.mpr d.pos⟩
  refine UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ ?_
  have hEq : x • ((h / (d : ℝ)) +ᵥ τ) = h +ᵥ (x • τ) := by
    ext
    simp only [coe_pos_real_smul, coe_vadd, Complex.real_smul, x]
    push_cast
    field_simp [Nat.cast_ne_zero.mpr d.ne_zero]
  have hw := hfper ↑(x • τ)
  rw [Function.comp_apply, Function.comp_apply, add_comm (↑(x • τ) : ℂ) h, ← coe_vadd,
    ofComplex_apply, ofComplex_apply] at hw
  simpa only [x, hEq] using hw

/-- For an `h`-periodic function, scaling the argument by a positive integer `d` preserves and
reflects meromorphy of the cusp function at `0`. -/
theorem meromorphicAt_cuspFunction_pnat_smul_iff (hfper : Periodic (f ∘ ofComplex) h) (d : ℕ+) :
    MeromorphicAt
      (cuspFunction h (fun τ ↦ f ((⟨(d : ℝ), Nat.cast_pos.mpr d.pos⟩ : {y : ℝ // 0 < y}) • τ))) 0 ↔
      MeromorphicAt (cuspFunction h f) 0 := by
  rcases le_or_gt h 0 with hh | _
  · exact iff_of_true
      ((analyticAt_const.congr (cuspFunction_eventuallyEq_const_of_nonpos hh _).symm).meromorphicAt)
      ((analyticAt_const.congr (cuspFunction_eventuallyEq_const_of_nonpos hh f).symm).meromorphicAt)
  have hd_pos : 0 < ((d : ℕ) : ℝ) := Nat.cast_pos.mpr d.pos
  let x : {y : ℝ // 0 < y} := ⟨(d : ℝ), hd_pos⟩
  let x_inv : {y : ℝ // 0 < y} := ⟨((d : ℝ))⁻¹, inv_pos.mpr hd_pos⟩
  let g : ℍ → ℂ := fun τ ↦ f (x • τ)
  have hmul : ((d : ℕ) : ℝ) * (h / (d : ℝ)) = h := mul_div_cancel₀ h hd_pos.ne'
  have hxmul : x * x_inv = 1 := Subtype.ext (mul_inv_cancel₀ hd_pos.ne')
  have hgx : (fun τ : ℍ ↦ g (x_inv • τ)) = f := funext fun τ ↦ by simp [g, ← mul_smul, hxmul]
  conv_lhs => rw [← hmul]
  rw [meromorphicAt_cuspFunction_pnat_mul_iff (periodic_pnat_smul_div_of_periodic hfper d) d]
  have hiff := (meromorphicAt_cuspFunction_posReal_mul_iff (h := h / (d : ℝ)) hd_pos g).symm
  rwa [hmul, hgx] at hiff

/-- **The Laurent `q`-expansion of `τ ↦ f (d • τ)`.** For an `h`-periodic function with `0 < h`
whose cusp function is meromorphic at `0`, scaling the argument by `d : ℕ+` substitutes `q ^ d` for
`q`. -/
theorem laurentQExpansion_pnat_smul (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hf : MeromorphicAt (cuspFunction h f) 0) (d : ℕ+) :
    laurentQExpansion h (fun τ ↦ f ((⟨(d : ℝ), Nat.cast_pos.mpr d.pos⟩ : {y : ℝ // 0 < y}) • τ)) =
      LaurentSeries.expand ℂ d (laurentQExpansion h f) := by
  have hd_pos : 0 < ((d : ℕ) : ℝ) := Nat.cast_pos.mpr d.pos
  let x : {y : ℝ // 0 < y} := ⟨(d : ℝ), hd_pos⟩
  let x_inv : {y : ℝ // 0 < y} := ⟨((d : ℝ))⁻¹, inv_pos.mpr hd_pos⟩
  let g : ℍ → ℂ := fun τ ↦ f (x • τ)
  have hmul : ((d : ℕ) : ℝ) * (h / (d : ℝ)) = h := mul_div_cancel₀ h hd_pos.ne'
  have hxmul : x * x_inv = 1 := Subtype.ext (mul_inv_cancel₀ hd_pos.ne')
  have hgx : (fun τ : ℍ ↦ g (x_inv • τ)) = f := funext fun τ ↦ by simp [g, ← mul_smul, hxmul]
  have hgm : MeromorphicAt (cuspFunction (h / (d : ℝ)) g) 0 := by
    have hiff := meromorphicAt_cuspFunction_posReal_mul_iff (h := h / (d : ℝ)) hd_pos g
    rw [hmul, hgx] at hiff
    exact hiff.mp hf
  have hgeq : laurentQExpansion (h / (d : ℝ)) g = laurentQExpansion h f := by
    have heq := (laurentQExpansion_posReal_mul (div_pos hh hd_pos) hd_pos g).symm
    rwa [hmul, hgx] at heq
  conv_lhs => rw [← hmul]
  rw [laurentQExpansion_pnat_mul (periodic_pnat_smul_div_of_periodic hfper d) hgm d, hgeq]

/-- Off `q = 0`, translating the argument of an `h`-periodic function by `s : ℝ` multiplies the
argument of its cusp function by `exp (2 π i s / h)`. -/
theorem cuspFunction_vadd_eventuallyEq_nhdsNE (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (s : ℝ) :
    cuspFunction h (fun τ ↦ f (s +ᵥ τ)) =ᶠ[𝓝[≠] 0]
      fun q ↦ cuspFunction h f (Complex.exp (2 * Real.pi * Complex.I * s / h) * q) := by
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)] with q hq hqn
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hq
  have him := Periodic.im_invQParam_pos_of_norm_lt_one hh (mem_ball_zero_iff.mp hqn) hq
  let τ : ℍ := ⟨Periodic.invQParam h q, him⟩
  have hqτ : 𝕢 h (s +ᵥ τ) = Complex.exp (2 * Real.pi * Complex.I * s / h) * q := by
    rw [← Periodic.qParam_right_inv hh.ne' hq]
    simp only [Periodic.qParam, coe_vadd, τ]
    rw [mul_add, add_div, Complex.exp_add]
  rw [cuspFunction_of_ne_zero hq, ofComplex_apply_of_im_pos him,
    ← eq_cuspFunction (s +ᵥ τ) hh.ne' hfper, hqτ]

private theorem analyticAt_cuspFunction_vadd (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) (s : ℝ) :
    AnalyticAt ℂ (cuspFunction h (fun τ ↦ f (s +ᵥ τ))) 0 := by
  let u : ℂ := Complex.exp (2 * Real.pi * Complex.I * s / h)
  have hcomp : AnalyticAt ℂ (fun q ↦ cuspFunction h f (u * q)) 0 :=
    hf.comp_of_eq (analyticAt_const.mul analyticAt_id) (mul_zero u)
  exact hcomp.congr (cuspFunction_eventuallyEq_nhds_of_continuousAt
    (cuspFunction_vadd_eventuallyEq_nhdsNE hh hfper s) hcomp.continuousAt).symm

private theorem analyticAt_cuspFunction_qParam_pow_mul_vadd (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hf : MeromorphicAt (cuspFunction h f) 0) (s : ℝ) :
    AnalyticAt ℂ (cuspFunction h (fun τ ↦ 𝕢 h τ ^ cuspPoleOrder h f * f (s +ᵥ τ))) 0 := by
  let u : ℂ := Complex.exp (2 * Real.pi * Complex.I * s / h)
  have hu : u ≠ 0 := Complex.exp_ne_zero _
  set k := cuspPoleOrder h f
  set g : ℍ → ℂ := fun τ ↦ 𝕢 h τ ^ k * f τ
  have han : AnalyticAt ℂ (cuspFunction h g) 0 :=
    analyticAt_cuspFunction_qParam_pow_mul hf (neg_cuspPoleOrder_le h f)
  have hgper : Periodic (g ∘ ofComplex) h := fun z ↦ by
    simpa [g] using congrArg₂ (fun a b ↦ a ^ k * b) (periodic_qParam_comp_ofComplex z) (hfper z)
  have hgvadd : (fun τ : ℍ ↦ 𝕢 h τ ^ k * f (s +ᵥ τ)) = fun τ ↦ (u ^ k)⁻¹ * g (s +ᵥ τ) := by
    funext τ
    have hq : 𝕢 h (s +ᵥ τ) = u * 𝕢 h τ := by
      simp only [Periodic.qParam, coe_vadd, u]; rw [mul_add, add_div, Complex.exp_add]
    simp only [g, hq, mul_pow]
    field_simp [hu]
  rw [hgvadd]
  have hcomp := analyticAt_const (v := (u ^ k)⁻¹).mul
    (analyticAt_cuspFunction_vadd hh hgper han s)
  exact hcomp.congr (cuspFunction_eventuallyEq_nhds_of_continuousAt
    (cuspFunction_map_eventuallyEq ((u ^ k)⁻¹ * ·) _) hcomp.continuousAt).symm

/-- Translating the argument of an `h`-periodic function by `s : ℝ` preserves and reflects
meromorphy of its cusp function at `0`. -/
theorem meromorphicAt_cuspFunction_vadd_iff (hfper : Periodic (f ∘ ofComplex) h) (s : ℝ) :
    MeromorphicAt (cuspFunction h (fun τ ↦ f (s +ᵥ τ))) 0 ↔ MeromorphicAt (cuspFunction h f) 0 := by
  rcases le_or_gt h 0 with hh | hh
  · exact iff_of_true
      ((analyticAt_const.congr (cuspFunction_eventuallyEq_const_of_nonpos hh _).symm).meromorphicAt)
      ((analyticAt_const.congr (cuspFunction_eventuallyEq_const_of_nonpos hh f).symm).meromorphicAt)
  refine ⟨fun hm ↦ ?_, fun hf ↦ meromorphicAt_cuspFunction_of_analyticAt_qParam_pow_mul
    (analyticAt_cuspFunction_qParam_pow_mul_vadd hh hfper hf s)⟩
  have hper' : Periodic ((fun τ ↦ f (s +ᵥ τ)) ∘ ofComplex) h := by
    refine UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ ?_
    have hw := hfper ↑(s +ᵥ τ)
    rw [Function.comp_apply, Function.comp_apply, add_comm (↑(s +ᵥ τ) : ℂ) h, ← coe_vadd,
      ofComplex_apply, ofComplex_apply] at hw
    simpa [vadd_vadd, add_comm] using hw
  simpa [vadd_vadd] using meromorphicAt_cuspFunction_of_analyticAt_qParam_pow_mul
    (analyticAt_cuspFunction_qParam_pow_mul_vadd hh hper' hm (-s))

private theorem iteratedDeriv_comp_mul_left (m : ℕ) (u : ℂ) (G : ℂ → ℂ) :
    iteratedDeriv m (fun q ↦ G (u * q)) = fun q ↦ u ^ m * iteratedDeriv m G (u * q) := by
  induction m with
  | zero => simp
  | succ m ih =>
    funext q
    rw [iteratedDeriv_succ, ih, deriv_const_mul_field, deriv_comp_mul_left, iteratedDeriv_succ]
    simp only [smul_eq_mul, pow_succ]
    ring

private theorem cuspFunction_vadd_eventuallyEq_nhds (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (s : ℝ) :
    cuspFunction h (fun τ ↦ f (s +ᵥ τ)) =ᶠ[𝓝 0]
      fun q ↦ cuspFunction h f (Complex.exp (2 * Real.pi * Complex.I * s / h) * q) := by
  let u : ℂ := Complex.exp (2 * Real.pi * Complex.I * s / h)
  have hu : u ≠ 0 := Complex.exp_ne_zero _
  have hne := cuspFunction_vadd_eventuallyEq_nhdsNE hh hfper s
  have h0 : cuspFunction h (fun τ ↦ f (s +ᵥ τ)) 0 = cuspFunction h f (u * 0) := by
    simp only [mul_zero, _root_.UpperHalfPlane.cuspFunction, Periodic.cuspFunction,
      Function.update_self, limUnder]
    refine congrArg lim ?_
    have hcongr : (((fun τ ↦ f (s +ᵥ τ)) ∘ ofComplex) ∘ Periodic.invQParam h) =ᶠ[𝓝[≠] 0]
        (((f ∘ ofComplex) ∘ Periodic.invQParam h) ∘ Homeomorph.mulLeft₀ u hu) := by
      filter_upwards [hne, self_mem_nhdsWithin] with q hq hq0
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hq0
      have huq0 : u * q ≠ 0 := mul_ne_zero hu hq0
      simpa [cuspFunction_of_ne_zero hq0, cuspFunction_of_ne_zero huq0, u] using hq
    rw [Filter.map_congr hcongr, ← Filter.map_map,
      (Homeomorph.mulLeft₀ u hu).map_punctured_nhds_eq 0]
    simp
  rw [Filter.EventuallyEq, eventually_nhds_iff]
  obtain ⟨S, hS, hSopen, hS0⟩ := eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hne)
  refine ⟨S, fun q hq ↦ ?_, hSopen, hS0⟩
  rcases eq_or_ne q 0 with rfl | hq0
  · exact h0
  · exact hS q hq hq0

/-- **The `q`-expansion under translation of the argument.** For an `h`-periodic function with
`0 < h`, translating the argument by `s : ℝ` rescales the `q`-expansion by `exp (2 π i s / h)`. -/
private theorem qExpansion_vadd (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h) (s : ℝ) :
    qExpansion h (fun τ ↦ f (s +ᵥ τ)) =
      PowerSeries.rescale (Complex.exp (2 * Real.pi * Complex.I * s / h)) (qExpansion h f) := by
  ext n
  rw [_root_.UpperHalfPlane.qExpansion_coeff,
    (cuspFunction_vadd_eventuallyEq_nhds hh hfper s).iteratedDeriv_eq,
    iteratedDeriv_comp_mul_left, PowerSeries.coeff_rescale,
    _root_.UpperHalfPlane.qExpansion_coeff]
  simp only [mul_zero]
  ring

/-- **The Laurent `q`-expansion under translation of the argument.** For an `h`-periodic function
with `0 < h`, translating the argument by `s : ℝ` rescales the variable `q` by
`exp (2 π i s / h)`. -/
theorem laurentQExpansion_vadd (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h) (s : ℝ) :
    laurentQExpansion h (fun τ ↦ f (s +ᵥ τ)) =
      TauCeti.LaurentSeries.rescale
        (Units.mk0 (Complex.exp (2 * Real.pi * Complex.I * s / h)) (Complex.exp_ne_zero _))
        (laurentQExpansion h f) := by
  by_cases hf : MeromorphicAt (cuspFunction h f) 0
  · let u : ℂ := Complex.exp (2 * Real.pi * Complex.I * s / h)
    have hu_def : Complex.exp (2 * ↑Real.pi * Complex.I * ↑s / ↑h) = u := rfl
    have hu : u ≠ 0 := Complex.exp_ne_zero _
    set k := cuspPoleOrder h f
    set g : ℍ → ℂ := fun τ ↦ 𝕢 h τ ^ k * f τ
    have han : AnalyticAt ℂ (cuspFunction h g) 0 :=
      analyticAt_cuspFunction_qParam_pow_mul hf (neg_cuspPoleOrder_le h f)
    have hgper : Periodic (g ∘ ofComplex) h := fun z ↦ by
      simpa [g] using congrArg₂ (fun a b ↦ a ^ k * b) (periodic_qParam_comp_ofComplex z) (hfper z)
    have hgvadd : (fun τ : ℍ ↦ 𝕢 h τ ^ k * f (s +ᵥ τ)) = (u ^ k)⁻¹ • fun τ ↦ g (s +ᵥ τ) := by
      funext τ
      have hq : 𝕢 h (s +ᵥ τ) = u * 𝕢 h τ := by
        simp only [Periodic.qParam, coe_vadd, u]; rw [mul_add, add_div, Complex.exp_add]
      simp only [Pi.smul_apply, smul_eq_mul, g, hq, mul_pow]
      field_simp [hu]
    rw [laurentQExpansion_eq_of_analyticAt_qParam_pow_mul hh
        (analyticAt_cuspFunction_qParam_pow_mul_vadd hh hfper hf s),
      laurentQExpansion_eq_of_analyticAt_qParam_pow_mul hh han, hgvadd,
      qExpansion_smul (analyticAt_cuspFunction_vadd hh hgper han s),
      qExpansion_vadd hh hgper s, map_mul,
      TauCeti.LaurentSeries.rescale_single, TauCeti.LaurentSeries.rescale_coe]
    ext n
    simp only [HahnSeries.coeff_single_mul, PowerSeries.coeff_coe, sub_neg_eq_add]
    split_ifs with hn
    · simp
    · simp only [PowerSeries.coeff_smul, PowerSeries.coeff_rescale, smul_eq_mul, zpow_neg,
        zpow_natCast, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_mk0, hu_def,
        mul_one, one_mul, ← mul_assoc, k, g]
  · have hf' : ¬ MeromorphicAt (cuspFunction h (fun τ ↦ f (s +ᵥ τ))) 0 :=
      mt (meromorphicAt_cuspFunction_vadd_iff hfper s).mp hf
    have hk : cuspPoleOrder h f = 0 := by
      simp [cuspPoleOrder, meromorphicOrderAt_of_not_meromorphicAt hf]
    have hk' : cuspPoleOrder h (fun τ ↦ f (s +ᵥ τ)) = 0 := by
      simp [cuspPoleOrder, meromorphicOrderAt_of_not_meromorphicAt hf']
    simp only [laurentQExpansion, hk, hk', pow_zero, one_mul, CharP.cast_eq_zero, neg_zero,
      HahnSeries.single_zero_one]
    rw [qExpansion_vadd hh hfper s, TauCeti.LaurentSeries.rescale_coe]
    rfl

end TauCeti.UpperHalfPlane

/-! ### Comparison with the Laurent expansion at a Fuchsian cusp -/

namespace TauCeti.Subgroup.CuspDatum

variable {Γ : Subgroup PSL(2, ℝ)}

/-- The Laurent expansion `laurentQExpansion D k f` at the cusp of `D`, built from a growth bound
`k`, is the Laurent `q`-expansion at `i∞`, in width `D.width`, of `f` read in the scaling
coordinate. -/
theorem laurentQExpansion_eq_upperHalfPlane_laurentQExpansion (D : Γ.CuspDatum) (k : ℤ)
    (f : ℍ → ℂ) (hf : ∀ (g : MulAction.stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width)) :
    laurentQExpansion D k f =
      UpperHalfPlane.laurentQExpansion D.width fun z ↦ f (D.scaling⁻¹ • z) := by
  have hk : k ≤ (k.toNat : ℤ) := Int.self_le_toNat k
  have han := analyticAt_twistedExtension_zero D k.toNat f hf (.of_forall fun z ↦ hhol _)
    (TauCeti.UpperHalfPlane.isBigO_exp_of_le D.width_pos.le (by exact_mod_cast hk) hbound)
  simp only [twistedExtension_def, cuspExtension_def, cuspTwist_inv_smul, zpow_natCast] at han
  rw [laurentQExpansion_eq_of_le D f hk hf hhol hbound,
    UpperHalfPlane.laurentQExpansion_eq_of_analyticAt_qParam_pow_mul D.width_pos han,
    laurentQExpansion_def, twistedQExpansion_def]
  simp only [cuspTwist_inv_smul, zpow_natCast]

end TauCeti.Subgroup.CuspDatum
