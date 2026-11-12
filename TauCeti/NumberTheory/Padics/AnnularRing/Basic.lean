/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import TauCeti.Topology.Algebra.InfiniteSum.DiscreteConvolution
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The annular coefficient ring `ℤ_p⟦T, p/T⟧`

This file constructs the integral coefficient ring

`H = {∑_{m ∈ ℤ} d_m T ^ m : d_m ∈ ℤ_p, v_p(d_m) ≥ max(0, -m)}`

of two-sided formal series. The condition says exactly that `|d_m| r ^ m ≤ 1` for every radius
`p⁻¹ < r < 1`, so these are the integral series bounded by one on the open annulus
`p⁻¹ < |T| < 1`. Rings of this kind are the coefficient rings of Liu–Wan–Xiao's study of the
eigencurve over the boundary of weight space. An element is stored by its normal form, the
coefficient family `d : ℤ → ℤ_p`, and the valuation condition is stated in norm form
`‖d_m‖ ≤ p ^ min 0 m`; `TauCeti.AnnularRing.norm_le_zpow_min_iff_pow_dvd` translates it into the
divisibility `p ^ (-m) ∣ d_m` for `m < 0`.

The product is the convolution `(d e)_m = ∑_{i ∈ ℤ} d_i e_{m - i}`, Mathlib's
`DiscreteConvolution.addRingConvolution` of the coefficient families. Each such coefficient is an
infinite `p`-adically convergent sum: the term `d_i e_{m - i}` has norm at most
`p ^ (min 0 i + min 0 (m - i))`, and this exponent tends to `-∞` in both directions. Associativity
follows from `DiscreteConvolution.addRingConvolution_assoc`, since the double series of three
coefficient families converges in the same way.

The ring contains `T` and `U = p / T`, with `T U = p`. The maps `f ↦ f(T)` and `g ↦ g(U)` are
ring homomorphisms from `ℤ_p⟦X⟧`, and every element has a unique normal form `f(T) + U g(U)`
(`TauCeti.AnnularRing.normalForm`). The coefficients of `g` are arbitrary `p`-adic integers, so `H`
is larger than the `p`-adic completion of `ℤ_p⟦T⟧[p/T]`, in which they tend to zero. For instance
`1 - U` is a unit whose inverse is the formal geometric series `∑_{j ≥ 0} U ^ j`.

## Main definitions

* `TauCeti.AnnularRing p`: the ring `H`, with its `ℤ_p`-algebra structure.
* `TauCeti.AnnularRing.T`, `TauCeti.AnnularRing.U`: the elements `T` and `U = p / T`.
* `TauCeti.AnnularRing.ofPowerSeriesT`, `TauCeti.AnnularRing.ofPowerSeriesU`: substitution of `T`,
  respectively `U`, into integral power series.
* `TauCeti.AnnularRing.normalForm`: the `ℤ_p`-linear equivalence `(f, g) ↦ f(T) + U g(U)` from
  `ℤ_p⟦X⟧ × ℤ_p⟦X⟧`.

## Main results

* `TauCeti.AnnularRing.hasSum_coeff_mul`: the convolution series of a product converges to the
  coefficient of the product.
* `TauCeti.AnnularRing.T_mul_U`: `T U = p`; hence `TauCeti.AnnularRing.span_p_T_eq_span_T` gives
  `(p, T) = (T)`.
* `TauCeti.AnnularRing.coeff_T_pow`, `TauCeti.AnnularRing.coeff_U_pow`: the normal forms of
  `T ^ n` and `U ^ n = p ^ n T ^ (-n)`.
* `TauCeti.AnnularRing.coeff_normalForm_natCast`, `TauCeti.AnnularRing.coeff_normalForm_neg_succ`:
  the coefficients of `f(T) + U g(U)`, which determine it.
* `TauCeti.AnnularRing.one_sub_U_mul_ofPowerSeriesU_mk_one`: `(1 - U) ∑_{j ≥ 0} U ^ j = 1`.

## References

* R. Liu, D. Wan and L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J.
  166 (2017), §§2–3.
-/

public noncomputable section

open Filter Topology PowerSeries
open scoped DiscreteConvolution

namespace TauCeti

variable (p : ℕ) [Fact p.Prime]

/-- The annular coefficient ring `H = ℤ_p⟦T, p/T⟧`: two-sided formal series `∑_{m ∈ ℤ} d_m T ^ m`
with `d_m ∈ ℤ_p` and `v_p(d_m) ≥ max(0, -m)`, stored by their coefficients. The valuation
condition is stated as `‖d_m‖ ≤ p ^ min 0 m`. -/
@[ext]
structure AnnularRing where
  /-- The coefficient `d_m` of `T ^ m`. -/
  coeff : ℤ → ℤ_[p]
  /-- The valuation condition `v_p(d_m) ≥ max(0, -m)`, in norm form. -/
  norm_coeff_le : ∀ m, ‖coeff m‖ ≤ (p : ℝ) ^ min 0 m

namespace AnnularRing

variable {p}

private theorem one_lt_p : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt

/-- The norm condition defining `AnnularRing` is the divisibility `p ^ (-m) ∣ d_m`, read as
`p ^ 0 ∣ d_m` for `m ≥ 0`. -/
theorem norm_le_zpow_min_iff_pow_dvd {d : ℤ_[p]} {m : ℤ} :
    ‖d‖ ≤ (p : ℝ) ^ min 0 m ↔ (p : ℤ_[p]) ^ (-m).toNat ∣ d := by
  have h : min 0 m = -(((-m).toNat : ℕ) : ℤ) := by omega
  rw [h, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]

/-- The coefficient of `T ^ (-n)` is divisible by `p ^ n`. -/
theorem pow_dvd_coeff_neg (x : AnnularRing p) (n : ℕ) : (p : ℤ_[p]) ^ n ∣ x.coeff (-n) := by
  simpa using norm_le_zpow_min_iff_pow_dvd.1 (x.norm_coeff_le (-n))

/-- An element is determined by its normal form. -/
theorem coeff_injective : Function.Injective (coeff : AnnularRing p → ℤ → ℤ_[p]) :=
  fun _ _ h ↦ AnnularRing.ext h

/-! ### Convergence of the convolution series -/

/-- The product of the coefficients of `T ^ i` and `T ^ j` in two elements has norm at most
`p ^ (min 0 i + min 0 j)`. -/
theorem norm_coeff_mul_coeff_le (x y : AnnularRing p) (i j : ℤ) :
    ‖x.coeff i * y.coeff j‖ ≤ (p : ℝ) ^ (min 0 i + min 0 j) := by
  rw [zpow_add₀ (zero_lt_one.trans one_lt_p).ne']
  exact norm_mul_le_of_le (x.norm_coeff_le i) (y.norm_coeff_le j)

/-- The exponent bounding the terms of a convolution coefficient tends to `-∞`. -/
private theorem tendsto_min_add_min (m : ℤ) :
    Tendsto (fun i : ℤ ↦ min 0 i + min 0 (m - i)) cofinite atBot := by
  refine tendsto_atBot.2 fun N ↦ eventually_cofinite.2 <|
    (Set.finite_Icc N (m - N)).subset fun i hi ↦ ?_
  simp only [Set.mem_ofPred_eq, not_le] at hi
  constructor <;> omega

/-- The exponent bounding the terms of a double convolution tends to `-∞`. -/
private theorem tendsto_min_add_min_add_min (m : ℤ) :
    Tendsto (fun ij : ℤ × ℤ ↦ min 0 ij.1 + min 0 ij.2 + min 0 (m - ij.1 - ij.2)) cofinite
      atBot := by
  refine tendsto_atBot.2 fun N ↦ eventually_cofinite.2 <|
    ((Set.finite_Icc N (m - N)).prod (Set.finite_Icc N (m - N))).subset fun ij hij ↦ ?_
  simp only [Set.mem_ofPred_eq, not_le] at hij
  simp only [Set.mem_prod, Set.mem_Icc]
  omega

/-- The convolution series defining the coefficient of `T ^ m` in a product converges. -/
theorem summable_coeff_mul_coeff (x y : AnnularRing p) (m : ℤ) :
    Summable fun i ↦ x.coeff i * y.coeff (m - i) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <|
    tendsto_zero_of_norm_le_zpow (one_lt_p (p := p)) (fun i ↦ norm_coeff_mul_coeff_le x y i (m - i))
      (tendsto_min_add_min m)

/-- The double convolution series `∑_{i, j} d_i e_j f_{m - i - j}` of three elements converges. -/
theorem summable_coeff_mul_coeff_mul_coeff (x y z : AnnularRing p) (m : ℤ) :
    Summable fun ij : ℤ × ℤ ↦ x.coeff ij.1 * y.coeff ij.2 * z.coeff (m - ij.1 - ij.2) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <|
    tendsto_zero_of_norm_le_zpow (one_lt_p (p := p))
      (fun ij ↦ by
        rw [zpow_add₀ (zero_lt_one.trans one_lt_p).ne']
        exact norm_mul_le_of_le (norm_coeff_mul_coeff_le x y ij.1 ij.2)
          (z.norm_coeff_le (m - ij.1 - ij.2)))
      (tendsto_min_add_min_add_min m)

/-- The convolution series defining the coefficient of `T ^ m` in a product satisfies the
valuation condition in degree `m`. -/
theorem norm_tsum_coeff_mul_coeff_le (x y : AnnularRing p) (m : ℤ) :
    ‖∑' i, x.coeff i * y.coeff (m - i)‖ ≤ (p : ℝ) ^ min 0 m :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun i ↦
    (norm_coeff_mul_coeff_le x y i (m - i)).trans
      (zpow_le_zpow_right₀ one_lt_p.le (by omega))

/-! ### The additive structure and the `ℤ_p`-action -/

instance : Zero (AnnularRing p) where
  zero := ⟨0, fun _ ↦ by simp only [Pi.zero_apply, norm_zero]; positivity⟩

instance : Add (AnnularRing p) where
  add x y := ⟨x.coeff + y.coeff, fun m ↦ (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (x.norm_coeff_le m) (y.norm_coeff_le m))⟩

instance : Neg (AnnularRing p) where
  neg x := ⟨-x.coeff, fun m ↦ by simpa using x.norm_coeff_le m⟩

instance : Sub (AnnularRing p) where
  sub x y := ⟨x.coeff - y.coeff, fun m ↦ by
    rw [Pi.sub_apply, sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (x.norm_coeff_le m) (by simpa using y.norm_coeff_le m))⟩

instance : SMul ℤ_[p] (AnnularRing p) where
  smul c x := ⟨c • x.coeff, fun m ↦ by
    simpa [Pi.smul_apply, smul_eq_mul, norm_mul] using
      mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one c) |>.trans (x.norm_coeff_le m)⟩

instance : SMul ℕ (AnnularRing p) where
  smul n x := ⟨n • x.coeff, fun m ↦ by
    simpa [Pi.smul_apply, nsmul_eq_mul, norm_mul] using
      mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one n) |>.trans (x.norm_coeff_le m)⟩

instance : SMul ℤ (AnnularRing p) where
  smul n x := ⟨n • x.coeff, fun m ↦ by
    simpa [Pi.smul_apply, zsmul_eq_mul, norm_mul] using
      mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one n) |>.trans (x.norm_coeff_le m)⟩

@[simp] theorem coeff_zero (m : ℤ) : (0 : AnnularRing p).coeff m = 0 := (rfl)

@[simp] theorem coeff_add (x y : AnnularRing p) (m : ℤ) :
    (x + y).coeff m = x.coeff m + y.coeff m := (rfl)

@[simp] theorem coeff_neg (x : AnnularRing p) (m : ℤ) : (-x).coeff m = -x.coeff m := (rfl)

@[simp] theorem coeff_sub (x y : AnnularRing p) (m : ℤ) :
    (x - y).coeff m = x.coeff m - y.coeff m := (rfl)

@[simp] theorem coeff_smul (c : ℤ_[p]) (x : AnnularRing p) (m : ℤ) :
    (c • x).coeff m = c * x.coeff m := (rfl)

theorem coeff_nsmul (n : ℕ) (x : AnnularRing p) (m : ℤ) :
    (n • x).coeff m = n • x.coeff m := (rfl)

theorem coeff_zsmul (n : ℤ) (x : AnnularRing p) (m : ℤ) :
    (n • x).coeff m = n • x.coeff m := (rfl)

instance : AddCommGroup (AnnularRing p) :=
  coeff_injective.addCommGroup _ (funext coeff_zero) (fun _ _ ↦ (rfl)) (fun _ ↦ (rfl))
    (fun _ _ ↦ (rfl)) (fun _ _ ↦ (rfl)) (fun _ _ ↦ (rfl))

instance : Module ℤ_[p] (AnnularRing p) :=
  coeff_injective.module ℤ_[p] ⟨⟨coeff, funext coeff_zero⟩, fun _ _ ↦ (rfl)⟩ fun _ _ ↦ (rfl)

/-! ### The convolution product -/

instance : One (AnnularRing p) where
  one := ⟨Pi.single 0 1, fun m ↦ by
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · simp only [Pi.single_eq_of_ne hm, norm_zero]; positivity⟩

instance : NatCast (AnnularRing p) where
  natCast n := (n : ℤ_[p]) • 1

instance : IntCast (AnnularRing p) where
  intCast n := (n : ℤ_[p]) • 1

instance : Mul (AnnularRing p) where
  mul x y := ⟨x.coeff ⋆ᵣ₊ y.coeff, fun m ↦ by
    rw [DiscreteConvolution.addRingConvolution_eq_tsum_neg_add]
    simpa only [neg_add_eq_sub] using norm_tsum_coeff_mul_coeff_le x y m⟩

@[simp] theorem coeff_one (m : ℤ) : (1 : AnnularRing p).coeff m = if m = 0 then 1 else 0 :=
  Pi.single_apply 0 1 m

theorem coeff_one_zero : (1 : AnnularRing p).coeff 0 = 1 :=
  (coeff_one 0).trans (ite_eq_left rfl)

theorem natCast_def (n : ℕ) : (n : AnnularRing p) = (n : ℤ_[p]) • 1 := (rfl)

theorem intCast_def (n : ℤ) : (n : AnnularRing p) = (n : ℤ_[p]) • 1 := (rfl)

/-- The coefficient family of a product is the additive ring convolution of the coefficient
families. -/
theorem coeff_mul_eq_addRingConvolution (x y : AnnularRing p) :
    (x * y).coeff = x.coeff ⋆ᵣ₊ y.coeff := (rfl)

/-- The coefficient of `T ^ m` in a product is the convolution `∑_{i ∈ ℤ} d_i e_{m - i}`. -/
theorem coeff_mul (x y : AnnularRing p) (m : ℤ) :
    (x * y).coeff m = ∑' i, x.coeff i * y.coeff (m - i) := by
  rw [coeff_mul_eq_addRingConvolution, DiscreteConvolution.addRingConvolution_eq_tsum_neg_add]
  simp only [neg_add_eq_sub]

/-- Every coefficient of the additive ring convolution of two coefficient families converges. -/
theorem addConvolutionExists_coeff (x y : AnnularRing p) :
    DiscreteConvolution.AddConvolutionExists (.mul ℕ ℤ_[p]) x.coeff y.coeff := fun m ↦
  (DiscreteConvolution.addFiberEquivSub m).summable_iff.1 <|
    (summable_coeff_mul_coeff y x m).congr fun i ↦ by simp [mul_comm]

/-- The double convolution series of three coefficient families converges when indexed, as in
`DiscreteConvolution.addRingConvolution_assoc`, by pairs `((k, c), (a, b))` with `k + c = n` and
`a + b = k`. -/
private theorem summable_sigma_addFiber_coeff_mul_coeff_mul_coeff (x y z : AnnularRing p) (n : ℤ) :
    Summable fun σ : Σ q : DiscreteConvolution.addFiber n, DiscreteConvolution.addFiber q.1.1 ↦
      x.coeff σ.2.1.1 * y.coeff σ.2.1.2 * z.coeff σ.1.1.2 := by
  -- Such a pair is determined by `(a, b)`, since `c = n - a - b`.
  have hj : Function.Injective fun σ : Σ q : DiscreteConvolution.addFiber n,
      DiscreteConvolution.addFiber q.1.1 ↦ σ.2.1 := fun _ _ _ ↦ by grind
  refine ((summable_coeff_mul_coeff_mul_coeff x y z n).comp_injective hj).congr fun σ ↦ ?_
  obtain ⟨⟨⟨k, c⟩, hkc⟩, ⟨⟨a, b⟩, hab⟩⟩ := σ
  simp only [DiscreteConvolution.mem_addFiber] at hkc hab
  simp only [Function.comp_apply]
  congr 2
  omega

/-- The convolution series converges to the coefficient of the product. -/
theorem hasSum_coeff_mul (x y : AnnularRing p) (m : ℤ) :
    HasSum (fun i ↦ x.coeff i * y.coeff (m - i)) ((x * y).coeff m) := by
  rw [coeff_mul]
  exact (summable_coeff_mul_coeff x y m).hasSum

/-- Multiplication by a series concentrated in degree `k` shifts the coefficients by `k`. -/
theorem coeff_mul_of_coeff_eq_zero {x : AnnularRing p} {k : ℤ} (hx : ∀ i ≠ k, x.coeff i = 0)
    (y : AnnularRing p) (m : ℤ) : (x * y).coeff m = x.coeff k * y.coeff (m - k) := by
  rw [coeff_mul, tsum_eq_single k fun i hi ↦ by rw [hx i hi, zero_mul]]

instance : CommRing (AnnularRing p) where
  __ := (inferInstance : AddCommGroup (AnnularRing p))
  mul := (· * ·)
  one := 1
  natCast := Nat.cast
  intCast := Int.cast
  -- The tactic block keeps the private summability lemma out of the exposed instance body.
  mul_assoc x y z := by
    exact AnnularRing.ext <| DiscreteConvolution.addRingConvolution_assoc
      (addConvolutionExists_coeff x y) (addConvolutionExists_coeff y z)
      (summable_sigma_addFiber_coeff_mul_coeff_mul_coeff x y z)
  one_mul x := AnnularRing.ext <| DiscreteConvolution.single_addRingConvolution x.coeff
  mul_one x := AnnularRing.ext <| DiscreteConvolution.addRingConvolution_single x.coeff
  zero_mul x := AnnularRing.ext <| DiscreteConvolution.zero_addRingConvolution x.coeff
  mul_zero x := AnnularRing.ext <| DiscreteConvolution.addRingConvolution_zero x.coeff
  left_distrib x y z := AnnularRing.ext <| DiscreteConvolution.addRingConvolution_add _ _ _
    (addConvolutionExists_coeff x y) (addConvolutionExists_coeff x z)
  right_distrib x y z := AnnularRing.ext <| DiscreteConvolution.add_addRingConvolution _ _ _
    (addConvolutionExists_coeff x z) (addConvolutionExists_coeff y z)
  mul_comm x y := AnnularRing.ext <| DiscreteConvolution.addRingConvolution_comm _ _
  natCast_zero := by simp [natCast_def]
  natCast_succ n := by simp [natCast_def, add_smul]
  intCast_ofNat n := by simp [natCast_def, intCast_def]
  intCast_negSucc n := by simp [natCast_def, intCast_def, Int.cast_negSucc, add_smul]

instance : Algebra ℤ_[p] (AnnularRing p) :=
  Algebra.ofModule
    (fun c x y ↦ AnnularRing.ext <|
      DiscreteConvolution.smul_addRingConvolution c _ _ (addConvolutionExists_coeff x y))
    (fun c x y ↦ AnnularRing.ext <|
      DiscreteConvolution.addRingConvolution_smul c _ _ (addConvolutionExists_coeff x y))

@[simp] theorem coeff_algebraMap (c : ℤ_[p]) (m : ℤ) :
    (algebraMap ℤ_[p] (AnnularRing p) c).coeff m = if m = 0 then c else 0 := by
  simp [Algebra.algebraMap_eq_smul_one, coeff_one]

@[simp] theorem coeff_natCast (n : ℕ) (m : ℤ) :
    (n : AnnularRing p).coeff m = if m = 0 then (n : ℤ_[p]) else 0 := by
  simp [natCast_def, coeff_one]

@[simp] theorem coeff_intCast (n : ℤ) (m : ℤ) :
    (n : AnnularRing p).coeff m = if m = 0 then (n : ℤ_[p]) else 0 := by
  simp [intCast_def, coeff_one]

@[simp] theorem coeff_ofNat (n : ℕ) [n.AtLeastTwo] (m : ℤ) :
    (ofNat(n) : AnnularRing p).coeff m = if m = 0 then ofNat(n) else 0 :=
  coeff_natCast n m

instance : Nontrivial (AnnularRing p) :=
  ⟨⟨0, 1, fun h ↦ by simpa using congr_arg (coeff · 0) h⟩⟩

/-! ### The elements `T` and `U = p / T` -/

/-- The variable `T`, of normal form `T ^ 1`. -/
def T : AnnularRing p :=
  ⟨fun m ↦ if m = 1 then 1 else 0, fun m ↦ by
    split_ifs with hm
    · simp [hm]
    · simp only [norm_zero]; positivity⟩

/-- The element `U = p / T`, of normal form `p T ^ (-1)`. -/
def U : AnnularRing p :=
  ⟨fun m ↦ if m = -1 then (p : ℤ_[p]) else 0, fun m ↦ by
    split_ifs with hm
    · simp [hm, PadicInt.norm_p]
    · simp only [norm_zero]; positivity⟩

theorem coeff_T (m : ℤ) : (T : AnnularRing p).coeff m = if m = 1 then 1 else 0 := (rfl)

theorem coeff_U (m : ℤ) : (U : AnnularRing p).coeff m = if m = -1 then (p : ℤ_[p]) else 0 :=
  (rfl)

/-- Multiplication by `T` shifts the normal form up by one degree. -/
@[simp] theorem coeff_T_mul (x : AnnularRing p) (m : ℤ) : (T * x).coeff m = x.coeff (m - 1) := by
  rw [coeff_mul_of_coeff_eq_zero (k := 1) fun i hi ↦ by simp [coeff_T, hi]]
  simp [coeff_T]

/-- Multiplication by `U` shifts the normal form down by one degree and multiplies it by `p`. -/
@[simp] theorem coeff_U_mul (x : AnnularRing p) (m : ℤ) :
    (U * x).coeff m = p * x.coeff (m + 1) := by
  rw [coeff_mul_of_coeff_eq_zero (k := -1) fun i hi ↦ by simp [coeff_U, hi]]
  simp [coeff_U]

theorem coeff_T_pow (n : ℕ) (m : ℤ) :
    ((T : AnnularRing p) ^ n).coeff m = if m = n then 1 else 0 := by
  induction n generalizing m with
  | zero => simp [coeff_one]
  | succ n ih =>
    rw [pow_succ', coeff_T_mul, ih]
    congr 1
    simp only [Nat.cast_succ, sub_eq_iff_eq_add]

theorem coeff_U_pow (n : ℕ) (m : ℤ) :
    ((U : AnnularRing p) ^ n).coeff m = if m = -n then (p : ℤ_[p]) ^ n else 0 := by
  induction n generalizing m with
  | zero => simp [coeff_one]
  | succ n ih =>
    rw [pow_succ', coeff_U_mul, ih]
    by_cases hm : m = -(n + 1 : ℕ)
    · simp [hm, pow_succ']
    · rw [ite_eq_right (show ¬m + 1 = -(n : ℤ) by omega), ite_eq_right hm, mul_zero]

/-- The defining relation `T U = p` of the annular coefficient ring. -/
@[simp] theorem T_mul_U : (T : AnnularRing p) * U = (p : AnnularRing p) := by
  ext m : 2
  rw [coeff_T_mul, coeff_U, coeff_natCast]
  congr 1
  simp only [sub_eq_neg_self]

/-- The defining relation in the form `U T = p`. -/
@[simp] theorem U_mul_T : (U : AnnularRing p) * T = (p : AnnularRing p) := by
  rw [mul_comm, T_mul_U]

/-- In the annular coefficient ring, `p = T U`, so the ideal `(p, T)` equals `(T)`. -/
theorem span_p_T_eq_span_T : Ideal.span {(p : AnnularRing p), T} = Ideal.span {T} := by
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono (by simp))
  rintro x (rfl | rfl)
  · exact Ideal.mem_span_singleton'.2 ⟨U, by rw [mul_comm, T_mul_U]⟩
  · exact Ideal.subset_span rfl

/-- `T` is a non-zero-divisor. -/
theorem T_mem_nonZeroDivisors : (T : AnnularRing p) ∈ nonZeroDivisors (AnnularRing p) := by
  have h (x : AnnularRing p) (hx : T * x = 0) : x = 0 := by
    ext m : 2
    simpa using congr_arg (coeff · (m + 1)) hx
  exact mem_nonZeroDivisors_iff.2 ⟨h, fun x hx ↦ h x (by rwa [mul_comm])⟩

/-! ### Substituting `T` and `U` into integral power series -/

/-- The normal form `∑_{n ≥ 0} a_n T ^ n` of a power series in `T`. -/
private def seriesT (f : ℤ_[p]⟦X⟧) : AnnularRing p :=
  ⟨fun m ↦ if 0 ≤ m then PowerSeries.coeff m.toNat f else 0, fun m ↦ by
    split_ifs with hm
    · rw [min_eq_left hm, zpow_zero]
      exact PadicInt.norm_le_one _
    · simp only [norm_zero]; positivity⟩

/-- The normal form `∑_{n ≥ 0} p ^ n b_n T ^ (-n)` of a power series in `U`. -/
private def seriesU (g : ℤ_[p]⟦X⟧) : AnnularRing p :=
  ⟨fun m ↦ if m ≤ 0 then (p : ℤ_[p]) ^ (-m).toNat * PowerSeries.coeff (-m).toNat g else 0,
    fun m ↦ by
      split_ifs with hm
      · rw [norm_mul]
        refine (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)).trans_eq ?_
        rw [PadicInt.norm_p_pow]
        congr 1
        omega
      · simp only [norm_zero]; positivity⟩

private theorem coeff_seriesT (f : ℤ_[p]⟦X⟧) (m : ℤ) :
    (seriesT f).coeff m = if 0 ≤ m then PowerSeries.coeff m.toNat f else 0 := (rfl)

private theorem coeff_seriesU (g : ℤ_[p]⟦X⟧) (m : ℤ) :
    (seriesU g).coeff m =
      if m ≤ 0 then (p : ℤ_[p]) ^ (-m).toNat * PowerSeries.coeff (-m).toNat g else 0 :=
  (rfl)

private theorem seriesT_mul (f g : ℤ_[p]⟦X⟧) : seriesT (f * g) = seriesT f * seriesT g := by
  have h (h : ℤ_[p]⟦X⟧) : ∀ i < 0, (seriesT h).coeff i = 0 := fun i hi ↦ by
    simp [coeff_seriesT, not_le.2 hi]
  ext m : 2
  rw [coeff_mul]
  rcases lt_or_ge m 0 with hm | hm
  · rw [DiscreteConvolution.tsum_mul_sub_eq_zero_of_neg (h f) (h g) hm, coeff_seriesT,
      ite_eq_right (not_le.2 hm)]
  · lift m to ℕ using hm
    rw [DiscreteConvolution.tsum_mul_sub_eq_sum_antidiagonal (h f) (h g), coeff_seriesT,
      ite_eq_left (Nat.cast_nonneg _), Int.toNat_natCast, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun ij _ ↦ ?_
    simp [coeff_seriesT]

private theorem seriesU_mul (f g : ℤ_[p]⟦X⟧) : seriesU (f * g) = seriesU f * seriesU g := by
  -- Reflecting the degrees turns both factors into families supported in nonnegative degrees.
  have h (h : ℤ_[p]⟦X⟧) : ∀ i < 0, (seriesU h).coeff (-i) = 0 := fun i hi ↦ by
    simp [coeff_seriesU, not_le.2 hi]
  ext m : 2
  rw [coeff_mul, ← (Equiv.neg ℤ).tsum_eq]
  simp only [Equiv.neg_apply, sub_neg_eq_add]
  have hc (i : ℤ) : m + i = -(-m - i) := by ring
  simp only [hc]
  rcases lt_or_ge (-m) 0 with hm | hm
  · rw [DiscreteConvolution.tsum_mul_sub_eq_zero_of_neg (h f) (h g) hm, coeff_seriesU,
      ite_eq_right (by omega)]
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hm
    rw [hn, DiscreteConvolution.tsum_mul_sub_eq_sum_antidiagonal (h f) (h g), coeff_seriesU,
      ite_eq_left (by omega), show (-m).toNat = n by omega, PowerSeries.coeff_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ij hij ↦ ?_
    rw [← Finset.mem_antidiagonal.1 hij]
    simp only [coeff_seriesU, neg_nonpos, Nat.cast_nonneg, ite_true, neg_neg, Int.toNat_natCast]
    ring

/-- Substitution of `T` into integral power series, `f ↦ f(T) = ∑_{n ≥ 0} a_n T ^ n`. -/
def ofPowerSeriesT : ℤ_[p]⟦X⟧ →ₐ[ℤ_[p]] AnnularRing p where
  toFun := seriesT
  map_one' := by
    ext m : 2
    by_cases hm : m = 0 <;> simp [coeff_seriesT, coeff_one, PowerSeries.coeff_one, hm]
    omega
  map_mul' := seriesT_mul
  map_zero' := by ext m : 2; simp [coeff_seriesT]
  map_add' f g := by ext m : 2; by_cases hm : 0 ≤ m <;> simp [coeff_seriesT, hm]
  commutes' c := by
    ext m : 2
    by_cases hm : m = 0 <;> simp [coeff_seriesT, PowerSeries.coeff_C, hm]
    omega

/-- Substitution of `U` into integral power series, `g ↦ g(U) = ∑_{n ≥ 0} p ^ n b_n T ^ (-n)`.
The coefficients `b_n` are arbitrary, so `g(U)` may have a formal tail in `U`. -/
def ofPowerSeriesU : ℤ_[p]⟦X⟧ →ₐ[ℤ_[p]] AnnularRing p where
  toFun := seriesU
  map_one' := by
    ext m : 2
    by_cases hm : m = 0 <;> simp [coeff_seriesU, coeff_one, PowerSeries.coeff_one, hm]
    omega
  map_mul' := seriesU_mul
  map_zero' := by ext m : 2; simp [coeff_seriesU]
  map_add' f g := by ext m : 2; by_cases hm : m ≤ 0 <;> simp [coeff_seriesU, hm, mul_add]
  commutes' c := by
    ext m : 2
    by_cases hm : m = 0 <;> simp [coeff_seriesU, PowerSeries.coeff_C, hm]
    omega

@[simp] theorem coeff_ofPowerSeriesT_natCast (f : ℤ_[p]⟦X⟧) (n : ℕ) :
    (ofPowerSeriesT f).coeff n = PowerSeries.coeff n f := by
  simp [ofPowerSeriesT, coeff_seriesT]

theorem coeff_ofPowerSeriesT_of_neg (f : ℤ_[p]⟦X⟧) {m : ℤ} (hm : m < 0) :
    (ofPowerSeriesT f).coeff m = 0 := by
  simp [ofPowerSeriesT, coeff_seriesT, not_le.2 hm]

@[simp] theorem coeff_ofPowerSeriesU_neg_natCast (g : ℤ_[p]⟦X⟧) (n : ℕ) :
    (ofPowerSeriesU g).coeff (-n) = (p : ℤ_[p]) ^ n * PowerSeries.coeff n g := by
  simp [ofPowerSeriesU, coeff_seriesU]

theorem coeff_ofPowerSeriesU_of_pos (g : ℤ_[p]⟦X⟧) {m : ℤ} (hm : 0 < m) :
    (ofPowerSeriesU g).coeff m = 0 := by
  simp [ofPowerSeriesU, coeff_seriesU, not_le.2 hm]

@[simp] theorem ofPowerSeriesT_X : ofPowerSeriesT (X : ℤ_[p]⟦X⟧) = T := by
  ext m : 2
  rcases lt_or_ge m 0 with hm | hm
  · rw [coeff_ofPowerSeriesT_of_neg _ hm, coeff_T, ite_eq_right (by omega)]
  · lift m to ℕ using hm
    rw [coeff_ofPowerSeriesT_natCast, PowerSeries.coeff_X, coeff_T]
    simp

@[simp] theorem ofPowerSeriesU_X : ofPowerSeriesU (X : ℤ_[p]⟦X⟧) = U := by
  ext m : 2
  rcases lt_or_ge 0 m with hm | hm
  · rw [coeff_ofPowerSeriesU_of_pos _ hm, coeff_U, ite_eq_right (by omega)]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = -n := ⟨(-m).toNat, by omega⟩
    rw [coeff_ofPowerSeriesU_neg_natCast, PowerSeries.coeff_X, coeff_U]
    by_cases hn : n = 1 <;> simp [hn]

/-- The element `1 - U` is a unit: its inverse is the formal geometric series
`∑_{j ≥ 0} U ^ j = ∑_{j ≥ 0} p ^ j T ^ (-j)`. -/
theorem one_sub_U_mul_ofPowerSeriesU_mk_one :
    (1 - U) * ofPowerSeriesU (PowerSeries.mk 1 : ℤ_[p]⟦X⟧) = 1 := by
  rw [← ofPowerSeriesU_X, ← map_one ofPowerSeriesU, ← map_sub, ← map_mul, mul_comm,
    mk_one_mul_one_sub_eq_one, map_one]

theorem isUnit_one_sub_U : IsUnit (1 - U : AnnularRing p) :=
  IsUnit.of_mul_eq_one _ one_sub_U_mul_ofPowerSeriesU_mk_one

/-! ### Normal forms -/

private theorem coeff_U_mul_ofPowerSeriesU_of_nonneg (g : ℤ_[p]⟦X⟧) {m : ℤ} (hm : 0 ≤ m) :
    (U * ofPowerSeriesU g).coeff m = 0 := by
  rw [coeff_U_mul, coeff_ofPowerSeriesU_of_pos _ (by omega), mul_zero]

private theorem coeff_U_mul_ofPowerSeriesU_neg_succ (g : ℤ_[p]⟦X⟧) (n : ℕ) :
    (U * ofPowerSeriesU g).coeff (-(n + 1)) = (p : ℤ_[p]) ^ (n + 1) * PowerSeries.coeff n g := by
  rw [coeff_U_mul, show -((n : ℤ) + 1) + 1 = -n by ring, coeff_ofPowerSeriesU_neg_natCast,
    pow_succ', mul_assoc]

/-- The map `(f, g) ↦ f(T) + U g(U)`. -/
private def normalFormLinearMap : (ℤ_[p]⟦X⟧ × ℤ_[p]⟦X⟧) →ₗ[ℤ_[p]] AnnularRing p :=
  ofPowerSeriesT.toLinearMap.coprod
    ((LinearMap.mulLeft ℤ_[p] (U : AnnularRing p)) ∘ₗ ofPowerSeriesU.toLinearMap)

private theorem normalFormLinearMap_apply (fg : ℤ_[p]⟦X⟧ × ℤ_[p]⟦X⟧) :
    normalFormLinearMap fg = ofPowerSeriesT fg.1 + U * ofPowerSeriesU fg.2 := (rfl)

private theorem coeff_normalFormLinearMap_natCast (fg : ℤ_[p]⟦X⟧ × ℤ_[p]⟦X⟧) (n : ℕ) :
    (normalFormLinearMap fg).coeff n = PowerSeries.coeff n fg.1 := by
  rw [normalFormLinearMap_apply, coeff_add, coeff_ofPowerSeriesT_natCast,
    coeff_U_mul_ofPowerSeriesU_of_nonneg _ (Nat.cast_nonneg _), add_zero]

private theorem coeff_normalFormLinearMap_neg_succ (fg : ℤ_[p]⟦X⟧ × ℤ_[p]⟦X⟧) (n : ℕ) :
    (normalFormLinearMap fg).coeff (-(n + 1)) =
      (p : ℤ_[p]) ^ (n + 1) * PowerSeries.coeff n fg.2 := by
  rw [normalFormLinearMap_apply, coeff_add, coeff_ofPowerSeriesT_of_neg _ (by omega), zero_add,
    coeff_U_mul_ofPowerSeriesU_neg_succ]

private theorem bijective_normalFormLinearMap :
    Function.Bijective (normalFormLinearMap (p := p)) := by
  have hp : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  refine ⟨(injective_iff_map_eq_zero _).2 fun fg h ↦ Prod.ext (PowerSeries.ext fun n ↦ ?_)
    (PowerSeries.ext fun n ↦ ?_), fun x ↦ ?_⟩
  · simpa [coeff_normalFormLinearMap_natCast] using congr_arg (coeff · (n : ℤ)) h
  · have := congr_arg (coeff · (-((n : ℤ) + 1))) h
    simp only [coeff_normalFormLinearMap_neg_succ, coeff_zero, mul_eq_zero, pow_eq_zero_iff',
      hp, false_and, false_or] at this
    simpa using this
  · -- The coefficient of `T ^ (-(n + 1))` is divisible by `p ^ (n + 1)`.
    choose c hc using fun n : ℕ ↦ x.pow_dvd_coeff_neg (n + 1)
    refine ⟨(PowerSeries.mk fun n ↦ x.coeff n, PowerSeries.mk c),
      AnnularRing.ext (funext fun m ↦ ?_)⟩
    cases m with
    | ofNat n => simp [coeff_normalFormLinearMap_natCast]
    | negSucc n =>
      rw [Int.negSucc_eq, coeff_normalFormLinearMap_neg_succ, PowerSeries.coeff_mk, ← hc]
      push_cast
      rfl

/-- **Normal forms in the annular coefficient ring.** Every element is uniquely of the form
`f(T) + U g(U)` with `f, g ∈ ℤ_p⟦X⟧`: its coefficients are `a_n` at `T ^ n`, `n ≥ 0`, and
`p ^ (n + 1) b_n` at `T ^ (-(n + 1))`, where `f = ∑ a_n X ^ n` and `g = ∑ b_n X ^ n`. -/
def normalForm : (ℤ_[p]⟦X⟧ × ℤ_[p]⟦X⟧) ≃ₗ[ℤ_[p]] AnnularRing p :=
  LinearEquiv.ofBijective normalFormLinearMap bijective_normalFormLinearMap

theorem normalForm_apply (f g : ℤ_[p]⟦X⟧) :
    normalForm (f, g) = ofPowerSeriesT f + U * ofPowerSeriesU g := (rfl)

@[simp] theorem coeff_normalForm_natCast (f g : ℤ_[p]⟦X⟧) (n : ℕ) :
    (normalForm (f, g)).coeff n = PowerSeries.coeff n f :=
  coeff_normalFormLinearMap_natCast (f, g) n

theorem coeff_normalForm_neg_succ (f g : ℤ_[p]⟦X⟧) (n : ℕ) :
    (normalForm (f, g)).coeff (-(n + 1)) = (p : ℤ_[p]) ^ (n + 1) * PowerSeries.coeff n g :=
  coeff_normalFormLinearMap_neg_succ (f, g) n

@[simp] theorem coeff_normalForm_symm_fst (x : AnnularRing p) (n : ℕ) :
    PowerSeries.coeff n (normalForm.symm x).1 = x.coeff n := by
  simpa using (coeff_normalForm_natCast (normalForm.symm x).1 (normalForm.symm x).2 n).symm

theorem pow_mul_coeff_normalForm_symm_snd (x : AnnularRing p) (n : ℕ) :
    (p : ℤ_[p]) ^ (n + 1) * PowerSeries.coeff n (normalForm.symm x).2 = x.coeff (-(n + 1)) := by
  simpa using (coeff_normalForm_neg_succ (normalForm.symm x).1 (normalForm.symm x).2 n).symm

end AnnularRing

end TauCeti
