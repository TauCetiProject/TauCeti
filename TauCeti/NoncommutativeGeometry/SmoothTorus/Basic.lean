/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PSeries
public import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# The smooth noncommutative two-torus

For a real parameter `θ`, the smooth noncommutative torus `𝒜_θ` is the algebra of rapidly
decreasing Fourier series `∑ a_(m,n) U₁ ^ m U₂ ^ n` in two unitaries subject to
`U₂ U₁ = exp(2πiθ) U₁ U₂`. We model it by its coefficient functions `a : ℤ × ℤ → ℂ`, rapidly
decreasing in the sense that `‖a (m, n)‖ ((1 + |m|) (1 + |n|)) ^ k` is bounded for every `k`. Since
`1 + |m| + |n| ≤ (1 + |m|) (1 + |n|) ≤ (1 + |m| + |n|) ^ 2`, this is the usual rapid decay on
the lattice `ℤ²`.

The relation gives `U₁ ^ m U₂ ^ n U₁ ^ m' U₂ ^ n' = exp(2πiθ n m') U₁ ^ (m + m') U₂ ^ (n + n')`,
so the product is the twisted convolution

`(a * b) x = ∑' y, a y * b (x - y) * exp(2πiθ y₂ (x - y)₁)`,

and reversing the word `U₁ ^ m U₂ ^ n` gives the involution
`(star a) x = conj (a (-x)) * exp(2πiθ x₁ x₂)`. The phase `(y, z) ↦ exp(2πiθ y₂ z₁)` is the
exponential of a biadditive form, hence a normalized two-cocycle on `ℤ²`; this is what makes the
product associative. The rapid-decay weights are submultiplicative, so the twisted convolution of
two rapidly decreasing functions is again rapidly decreasing.

On finitely supported coefficients this is the twisted group algebra of `ℤ²` for the factor set
`(y, z) ↦ exp(2πiθ y₂ z₁)`, as in `TauCeti.twistedMonoidAlgebra`; rapidly decreasing coefficients
give infinite sums, so the product here is a convergent series rather than a finite one.

The coefficient at the origin is the canonical trace `τ`. It is tracial, and
`τ (star a * a) = ∑' x, ‖a x‖ ^ 2`, so it is faithful.

## Main definitions

* `TauCeti.SmoothNoncommutativeTorus θ`: the smooth noncommutative torus `𝒜_θ`, a `ℂ`-algebra
  with a star structure, implemented by rapidly decreasing coefficient functions on `ℤ × ℤ`.
* `TauCeti.SmoothNoncommutativeTorus.single x c`: the monomial `c U₁ ^ x₁ U₂ ^ x₂`.
* `TauCeti.SmoothNoncommutativeTorus.U₁`, `TauCeti.SmoothNoncommutativeTorus.U₂`: the two unitary
  generators.
* `TauCeti.SmoothNoncommutativeTorus.trace`: the canonical trace `τ a = a (0, 0)`.

## Main statements

* `TauCeti.SmoothNoncommutativeTorus.single_mul_single`: the multiplication rule for monomials,
  with multiplier `exp(2πiθ n m')`.
* `TauCeti.SmoothNoncommutativeTorus.U₂_mul_U₁`: the defining relation
  `U₂ U₁ = exp(2πiθ) U₁ U₂`.
* `TauCeti.SmoothNoncommutativeTorus.U₁_zpow_mul_U₂_zpow`: `U₁ ^ m U₂ ^ n` is the monomial with
  coefficient `1` at `(m, n)`.
* `TauCeti.SmoothNoncommutativeTorus.trace_mul_comm`: `τ (a * b) = τ (b * a)`.
* `TauCeti.SmoothNoncommutativeTorus.trace_star_mul_self_eq_zero_iff`: `τ` is faithful.

## References

* A. Connes, *Noncommutative Geometry*, Academic Press, 1994, Chapter IV, §6.
* M. A. Rieffel, *C*-algebras associated with irrational rotations*, Pacific J. Math. 93 (1981).
-/

public section

open Complex Filter
open scoped ComplexConjugate FourierTransform

noncomputable section

namespace TauCeti

namespace SmoothNoncommutativeTorus

/-! ### Rapid decay on the lattice -/

/-- The weight `(1 + |m|) (1 + |n|)` on the lattice `ℤ × ℤ`. -/
def weight (x : ℤ × ℤ) : ℝ :=
  (1 + |(x.1 : ℝ)|) * (1 + |(x.2 : ℝ)|)

/-- The product formula for the rapid-decay weight. -/
theorem weight_def (x : ℤ × ℤ) :
    weight x = (1 + |(x.1 : ℝ)|) * (1 + |(x.2 : ℝ)|) := (rfl)

theorem one_le_weight (x : ℤ × ℤ) : 1 ≤ weight x :=
  one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (abs_nonneg _))
    (le_add_of_nonneg_right (abs_nonneg _))

/-- The absolute value of the first coordinate is bounded by the rapid-decay weight. -/
theorem abs_fst_le_weight (x : ℤ × ℤ) : |(x.1 : ℝ)| ≤ weight x := by
  rw [weight_def]
  nlinarith [abs_nonneg (x.1 : ℝ), abs_nonneg (x.2 : ℝ)]

/-- The absolute value of the second coordinate is bounded by the rapid-decay weight. -/
theorem abs_snd_le_weight (x : ℤ × ℤ) : |(x.2 : ℝ)| ≤ weight x := by
  rw [weight_def]
  nlinarith [abs_nonneg (x.1 : ℝ), abs_nonneg (x.2 : ℝ)]

theorem weight_pos (x : ℤ × ℤ) : 0 < weight x :=
  zero_lt_one.trans_le (one_le_weight x)

@[simp]
theorem weight_zero : weight 0 = 1 := by
  simp [weight]

@[simp]
theorem weight_neg (x : ℤ × ℤ) : weight (-x) = weight x := by
  simp [weight]

/-- The weight is submultiplicative. -/
theorem weight_add_le (x y : ℤ × ℤ) : weight (x + y) ≤ weight x * weight y := by
  simp only [weight, Prod.fst_add, Prod.snd_add, Int.cast_add]
  calc (1 + |(x.1 : ℝ) + y.1|) * (1 + |(x.2 : ℝ) + y.2|)
      ≤ ((1 + |(x.1 : ℝ)|) * (1 + |(y.1 : ℝ)|)) * ((1 + |(x.2 : ℝ)|) * (1 + |(y.2 : ℝ)|)) :=
        mul_le_mul (by simpa only [Real.norm_eq_abs] using one_add_norm_add_le (x.1 : ℝ) y.1)
          (by simpa only [Real.norm_eq_abs] using one_add_norm_add_le (x.2 : ℝ) y.2)
          (by positivity) (by positivity)
    _ = (1 + |(x.1 : ℝ)|) * (1 + |(x.2 : ℝ)|) * ((1 + |(y.1 : ℝ)|) * (1 + |(y.2 : ℝ)|)) := by
        ring

/-- The inverse square of the weight is summable over `ℤ × ℤ`. -/
theorem summable_inv_weight_sq : Summable fun x : ℤ × ℤ ↦ (weight x ^ 2)⁻¹ := by
  have h := summable_one_add_abs_int_rpow (r := -2) (by norm_num)
  convert h.mul_of_nonneg h (fun _ ↦ by positivity) (fun _ ↦ by positivity) using 2 with x
  rw [weight, mul_pow, mul_inv, Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
  norm_cast

/-- A function on `ℤ × ℤ` is **rapidly decreasing** if `‖a x‖ * weight x ^ k` is bounded for
every `k`. -/
def IsRapidDecay (a : ℤ × ℤ → ℂ) : Prop :=
  ∀ k : ℕ, ∃ C, ∀ x, ‖a x‖ * weight x ^ k ≤ C

/-- Rapid decay is boundedness of every weighted coefficient function. -/
theorem isRapidDecay_iff (a : ℤ × ℤ → ℂ) :
    IsRapidDecay a ↔ ∀ k : ℕ, ∃ C, ∀ x, ‖a x‖ * weight x ^ k ≤ C := Iff.rfl

namespace IsRapidDecay

variable {a b : ℤ × ℤ → ℂ}

theorem zero : IsRapidDecay 0 :=
  fun _ ↦ ⟨0, fun _ ↦ by simp⟩

theorem add (ha : IsRapidDecay a) (hb : IsRapidDecay b) : IsRapidDecay (a + b) := by
  intro k
  obtain ⟨C, hC⟩ := ha k
  obtain ⟨D, hD⟩ := hb k
  refine ⟨C + D, fun x ↦ ?_⟩
  have hw := pow_nonneg (weight_pos x).le k
  calc ‖(a + b) x‖ * weight x ^ k ≤ (‖a x‖ + ‖b x‖) * weight x ^ k :=
        mul_le_mul_of_nonneg_right (norm_add_le _ _) hw
    _ ≤ C + D := by rw [add_mul]; exact add_le_add (hC x) (hD x)

theorem const_smul (ha : IsRapidDecay a) (c : ℂ) : IsRapidDecay (c • a) := by
  intro k
  obtain ⟨C, hC⟩ := ha k
  refine ⟨‖c‖ * C, fun x ↦ ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)

theorem neg (ha : IsRapidDecay a) : IsRapidDecay (-a) := by
  simpa using ha.const_smul (-1)

theorem single (x₀ : ℤ × ℤ) (c : ℂ) : IsRapidDecay (Pi.single x₀ c) := by
  intro k
  refine ⟨‖c‖ * weight x₀ ^ k, fun x ↦ ?_⟩
  rcases eq_or_ne x x₀ with rfl | hx
  · simp
  · simp only [ne_eq, hx, not_false_eq_true, Pi.single_eq_of_ne, norm_zero, zero_mul]
    exact mul_nonneg (norm_nonneg _) (pow_nonneg (weight_pos _).le _)

/-- A rapidly decreasing function remains summable after multiplication by any power of the
weight. -/
theorem summable_norm_mul_weight_pow (ha : IsRapidDecay a) (k : ℕ) :
    Summable fun x ↦ ‖a x‖ * weight x ^ k := by
  obtain ⟨C, hC⟩ := ha (k + 2)
  refine (summable_inv_weight_sq.mul_left C).of_nonneg_of_le
    (fun x ↦ mul_nonneg (norm_nonneg _) (pow_nonneg (weight_pos x).le k)) fun x ↦ ?_
  have hw : 0 < weight x ^ 2 := pow_pos (weight_pos x) 2
  rw [← div_eq_mul_inv, le_div_iff₀ hw, mul_assoc, ← pow_add]
  exact hC x

theorem summable_norm (ha : IsRapidDecay a) : Summable fun x ↦ ‖a x‖ := by
  simpa using ha.summable_norm_mul_weight_pow 0

theorem bddAbove_norm (ha : IsRapidDecay a) : ∃ C, ∀ x, ‖a x‖ ≤ C := by
  simpa using ha 0

end IsRapidDecay

/-! ### The twisting phase -/

/-- The phase `exp(2πiθ y₂ z₁)` of the product `U₁ ^ y₁ U₂ ^ y₂ U₁ ^ z₁ U₂ ^ z₂`. -/
def twist (θ : ℝ) (y z : ℤ × ℤ) : Circle :=
  𝐞 (θ * (y.2 * z.1 : ℤ))

variable {θ : ℝ}

theorem twist_apply (y z : ℤ × ℤ) : twist θ y z = 𝐞 (θ * (y.2 * z.1 : ℤ)) :=
  (rfl)

@[simp]
theorem twist_zero_left (z : ℤ × ℤ) : twist θ 0 z = 1 := by
  simp [twist_apply]

@[simp]
theorem twist_zero_right (y : ℤ × ℤ) : twist θ y 0 = 1 := by
  simp [twist_apply]

/-- The twisting phase is a two-cocycle. -/
theorem twist_mul_twist_add (x y z : ℤ × ℤ) :
    twist θ x y * twist θ (x + y) z = twist θ y z * twist θ x (y + z) := by
  simp only [twist_apply, ← AddChar.map_add_eq_mul, Prod.fst_add, Prod.snd_add]
  congr 1
  push_cast
  ring

@[simp]
theorem twist_neg_neg (y z : ℤ × ℤ) : twist θ (-y) (-z) = twist θ y z := by
  simp [twist_apply]

/-- Negating the first argument inverts the twisting phase. -/
theorem twist_neg_left (y z : ℤ × ℤ) : twist θ (-y) z = (twist θ y z)⁻¹ := by
  rw [twist_apply, twist_apply, ← AddChar.map_neg_eq_inv]
  congr 1
  push_cast [Prod.snd_neg]
  ring

/-- Negating the second argument inverts the twisting phase. -/
theorem twist_neg_right (y z : ℤ × ℤ) : twist θ y (-z) = (twist θ y z)⁻¹ := by
  rw [twist_apply, twist_apply, ← AddChar.map_neg_eq_inv]
  congr 1
  push_cast [Prod.fst_neg]
  ring

/-! ### The algebra -/

end SmoothNoncommutativeTorus

open SmoothNoncommutativeTorus in
/-- The **smooth noncommutative torus** `𝒜_θ`, the algebra of rapidly decreasing Fourier series
`∑ a_(m,n) U₁ ^ m U₂ ^ n` with `U₂ U₁ = exp(2πiθ) U₁ U₂`, represented by its coefficients. -/
@[ext]
structure SmoothNoncommutativeTorus (θ : ℝ) where
  /-- The coefficient of the monomial `U₁ ^ m U₂ ^ n` at `(m, n)`. -/
  coeff : ℤ × ℤ → ℂ
  isRapidDecay_coeff : IsRapidDecay coeff

namespace SmoothNoncommutativeTorus

variable {θ : ℝ}

theorem coeff_injective : Function.Injective (coeff (θ := θ)) :=
  fun _ _ ↦ SmoothNoncommutativeTorus.ext

instance : Zero (SmoothNoncommutativeTorus θ) :=
  ⟨⟨0, .zero⟩⟩

instance : Add (SmoothNoncommutativeTorus θ) :=
  ⟨fun a b ↦ ⟨a.coeff + b.coeff, a.isRapidDecay_coeff.add b.isRapidDecay_coeff⟩⟩

instance : Neg (SmoothNoncommutativeTorus θ) :=
  ⟨fun a ↦ ⟨-a.coeff, a.isRapidDecay_coeff.neg⟩⟩

instance : Sub (SmoothNoncommutativeTorus θ) :=
  ⟨fun a b ↦ ⟨a.coeff - b.coeff, by
    simpa [sub_eq_add_neg] using a.isRapidDecay_coeff.add b.isRapidDecay_coeff.neg⟩⟩

instance {S : Type*} [SMul S ℂ] [IsScalarTower S ℂ ℂ] : SMul S (SmoothNoncommutativeTorus θ) :=
  ⟨fun c a ↦ ⟨c • a.coeff, by
    simpa only [smul_one_smul] using a.isRapidDecay_coeff.const_smul (c • (1 : ℂ))⟩⟩

@[simp]
theorem coeff_zero : (0 : SmoothNoncommutativeTorus θ).coeff = 0 :=
  (rfl)

@[simp]
theorem coeff_add (a b : SmoothNoncommutativeTorus θ) : (a + b).coeff = a.coeff + b.coeff :=
  (rfl)

@[simp]
theorem coeff_neg (a : SmoothNoncommutativeTorus θ) : (-a).coeff = -a.coeff :=
  (rfl)

@[simp]
theorem coeff_sub (a b : SmoothNoncommutativeTorus θ) : (a - b).coeff = a.coeff - b.coeff :=
  (rfl)

@[simp]
theorem coeff_smul {S : Type*} [SMul S ℂ] [IsScalarTower S ℂ ℂ] (c : S)
    (a : SmoothNoncommutativeTorus θ) : (c • a).coeff = c • a.coeff :=
  (rfl)

instance : AddCommGroup (SmoothNoncommutativeTorus θ) :=
  coeff_injective.addCommGroup _ coeff_zero coeff_add coeff_neg coeff_sub (fun _ _ ↦ rfl)
    fun _ _ ↦ rfl

instance : Module ℂ (SmoothNoncommutativeTorus θ) :=
  coeff_injective.module ℂ ⟨⟨coeff, coeff_zero⟩, coeff_add⟩ coeff_smul

/-- The monomial `c U₁ ^ x₁ U₂ ^ x₂`. -/
def single (x : ℤ × ℤ) (c : ℂ) : SmoothNoncommutativeTorus θ :=
  ⟨Pi.single x c, .single x c⟩

@[simp]
theorem coeff_single (x : ℤ × ℤ) (c : ℂ) :
    (single x c : SmoothNoncommutativeTorus θ).coeff = Pi.single x c :=
  (rfl)

@[simp]
theorem smul_single (x : ℤ × ℤ) (c d : ℂ) :
    c • (single x d : SmoothNoncommutativeTorus θ) = single x (c * d) := by
  ext y
  simp [Pi.single_apply]

/-! ### The twisted product -/

private theorem summable_norm_mul_coeff (a b : SmoothNoncommutativeTorus θ) (x : ℤ × ℤ) :
    Summable fun y ↦ ‖a.coeff y * b.coeff (x - y) * twist θ y (x - y)‖ := by
  obtain ⟨C, hC⟩ := b.isRapidDecay_coeff.bddAbove_norm
  refine (a.isRapidDecay_coeff.summable_norm.mul_right C).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun y ↦ ?_
  simp only [norm_mul, Circle.norm_coe, mul_one]
  exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)

/-- The terms of the twisted convolution are summable. -/
theorem summable_mul_coeff (a b : SmoothNoncommutativeTorus θ) (x : ℤ × ℤ) :
    Summable fun y ↦ a.coeff y * b.coeff (x - y) * twist θ y (x - y) :=
  (summable_norm_mul_coeff a b x).of_norm

/-- The twisted convolution of two rapidly decreasing functions is rapidly decreasing. -/
theorem isRapidDecay_mul (a b : SmoothNoncommutativeTorus θ) :
    IsRapidDecay fun x ↦ ∑' y, a.coeff y * b.coeff (x - y) * twist θ y (x - y) := by
  intro k
  obtain ⟨C, hC⟩ := b.isRapidDecay_coeff k
  have hs := a.isRapidDecay_coeff.summable_norm_mul_weight_pow k
  refine ⟨(∑' y, ‖a.coeff y‖ * weight y ^ k) * C, fun x ↦ ?_⟩
  have hw := pow_nonneg (weight_pos x).le k
  have hbound : ∀ y, ‖a.coeff y * b.coeff (x - y) * twist θ y (x - y)‖ * weight x ^ k ≤
      ‖a.coeff y‖ * weight y ^ k * C := fun y ↦ by
    rw [norm_mul, Circle.norm_coe, mul_one, norm_mul]
    calc ‖a.coeff y‖ * ‖b.coeff (x - y)‖ * weight x ^ k
        ≤ ‖a.coeff y‖ * ‖b.coeff (x - y)‖ * (weight y ^ k * weight (x - y) ^ k) := by
          gcongr
          rw [← mul_pow]
          gcongr
          · exact (weight_pos _).le
          · simpa using weight_add_le y (x - y)
      _ = ‖a.coeff y‖ * weight y ^ k * (‖b.coeff (x - y)‖ * weight (x - y) ^ k) := by ring
      _ ≤ ‖a.coeff y‖ * weight y ^ k * C :=
          mul_le_mul_of_nonneg_left (hC _)
            (mul_nonneg (norm_nonneg _) (pow_nonneg (weight_pos y).le k))
  calc ‖∑' y, a.coeff y * b.coeff (x - y) * twist θ y (x - y)‖ * weight x ^ k
      ≤ (∑' y, ‖a.coeff y * b.coeff (x - y) * twist θ y (x - y)‖) * weight x ^ k :=
        mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm (summable_norm_mul_coeff a b x)) hw
    _ = ∑' y, ‖a.coeff y * b.coeff (x - y) * twist θ y (x - y)‖ * weight x ^ k :=
        (tsum_mul_right).symm
    _ ≤ ∑' y, ‖a.coeff y‖ * weight y ^ k * C :=
        Summable.tsum_le_tsum hbound ((summable_norm_mul_coeff a b x).mul_right _)
          (hs.mul_right C)
    _ = (∑' y, ‖a.coeff y‖ * weight y ^ k) * C := tsum_mul_right

instance : Mul (SmoothNoncommutativeTorus θ) :=
  ⟨fun a b ↦ ⟨_, isRapidDecay_mul a b⟩⟩

theorem coeff_mul (a b : SmoothNoncommutativeTorus θ) (x : ℤ × ℤ) :
    (a * b).coeff x = ∑' y, a.coeff y * b.coeff (x - y) * twist θ y (x - y) :=
  (rfl)

theorem hasSum_coeff_mul (a b : SmoothNoncommutativeTorus θ) (x : ℤ × ℤ) :
    HasSum (fun y ↦ a.coeff y * b.coeff (x - y) * twist θ y (x - y)) ((a * b).coeff x) :=
  (summable_mul_coeff a b x).hasSum

instance : One (SmoothNoncommutativeTorus θ) :=
  ⟨single 0 1⟩

theorem one_def : (1 : SmoothNoncommutativeTorus θ) = single 0 1 :=
  (rfl)

@[simp]
theorem coeff_one : (1 : SmoothNoncommutativeTorus θ).coeff = Pi.single 0 1 :=
  (rfl)

/-- The multiplication rule for monomials:
`U₁ ^ y₁ U₂ ^ y₂ U₁ ^ z₁ U₂ ^ z₂ = exp(2πiθ y₂ z₁) U₁ ^ (y₁ + z₁) U₂ ^ (y₂ + z₂)`. -/
theorem single_mul_single (y z : ℤ × ℤ) (c d : ℂ) :
    (single y c * single z d : SmoothNoncommutativeTorus θ) =
      single (y + z) (c * d * twist θ y z) := by
  ext x
  rw [coeff_mul, tsum_eq_single y fun w hw ↦ by simp [Pi.single_apply, hw]]
  rcases eq_or_ne x (y + z) with rfl | hx
  · simp
  · have : x - y ≠ z := fun h ↦ hx (by rw [← h, add_sub_cancel])
    simp [this, hx]

private theorem one_mul' (a : SmoothNoncommutativeTorus θ) : 1 * a = a := by
  ext x
  rw [coeff_mul, tsum_eq_single 0 fun y hy ↦ by simp [hy]]
  simp

private theorem mul_one' (a : SmoothNoncommutativeTorus θ) : a * 1 = a := by
  ext x
  rw [coeff_mul, tsum_eq_single x fun y hy ↦ by simp [sub_eq_zero, Ne.symm hy]]
  simp

private theorem mul_add' (a b c : SmoothNoncommutativeTorus θ) : a * (b + c) = a * b + a * c := by
  ext x
  simp only [coeff_mul, coeff_add, Pi.add_apply, mul_add, add_mul]
  exact (summable_mul_coeff a b x).tsum_add (summable_mul_coeff a c x)

private theorem add_mul' (a b c : SmoothNoncommutativeTorus θ) : (a + b) * c = a * c + b * c := by
  ext x
  simp only [coeff_mul, coeff_add, Pi.add_apply, add_mul]
  exact (summable_mul_coeff a c x).tsum_add (summable_mul_coeff b c x)

private theorem smul_mul' (r : ℂ) (a b : SmoothNoncommutativeTorus θ) :
    r • a * b = r • (a * b) := by
  ext x
  simp only [coeff_mul, coeff_smul, Pi.smul_apply, smul_eq_mul, ← tsum_mul_left]
  exact tsum_congr fun _ ↦ by ring

private theorem mul_smul' (r : ℂ) (a b : SmoothNoncommutativeTorus θ) :
    a * r • b = r • (a * b) := by
  ext x
  simp only [coeff_mul, coeff_smul, Pi.smul_apply, smul_eq_mul, ← tsum_mul_left]
  exact tsum_congr fun _ ↦ by ring

private theorem mul_assoc' (a b c : SmoothNoncommutativeTorus θ) : a * b * c = a * (b * c) := by
  ext x
  -- Both sides are sums of `F (y, v)` over pairs, with `y + v + w = x`.
  set F : (ℤ × ℤ) × (ℤ × ℤ) → ℂ := fun p ↦ a.coeff p.1 * b.coeff p.2 * c.coeff (x - p.1 - p.2) *
    (twist θ p.1 p.2 * twist θ (p.1 + p.2) (x - p.1 - p.2) : Circle) with hF_def
  obtain ⟨C, hC⟩ := c.isRapidDecay_coeff.bddAbove_norm
  have hF : Summable F := by
    refine ((a.isRapidDecay_coeff.summable_norm.mul_of_nonneg
      b.isRapidDecay_coeff.summable_norm (fun _ ↦ norm_nonneg _)
        (fun _ ↦ norm_nonneg _)).mul_right C).of_norm_bounded fun p ↦ ?_
    simp only [hF_def, norm_mul, Circle.norm_coe, mul_one]
    exact mul_le_mul_of_nonneg_left (hC _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  -- the reindexing `(u, y) ↦ (y, u - y)` regroups the double sums
  let e : (ℤ × ℤ) × (ℤ × ℤ) ≃ (ℤ × ℤ) × (ℤ × ℤ) :=
    (Equiv.prodComm _ _).trans (Equiv.prodCongrRight fun y ↦ Equiv.subRight y)
  have hG : Summable (F ∘ e) := e.summable_iff.2 hF
  calc (a * b * c).coeff x
      = ∑' u, ∑' y, (F ∘ e) (u, y) := by
        rw [coeff_mul]
        refine tsum_congr fun u ↦ ?_
        rw [coeff_mul, ← tsum_mul_right, ← tsum_mul_right]
        refine tsum_congr fun y ↦ ?_
        simp only [hF_def, e, Function.comp_apply, Equiv.trans_apply, Equiv.prodComm_apply,
          Prod.swap_prod_mk, Equiv.prodCongrRight_apply, Equiv.subRight_apply, add_sub_cancel,
          sub_sub_sub_cancel_right, Circle.coe_mul]
        ring
    _ = ∑' p, F p := by rw [← hG.tsum_prod]; exact e.tsum_eq F
    _ = ∑' y, ∑' v, F (y, v) := hF.tsum_prod
    _ = (a * (b * c)).coeff x := by
        rw [coeff_mul]
        refine tsum_congr fun y ↦ ?_
        rw [coeff_mul, ← tsum_mul_left, ← tsum_mul_right]
        refine tsum_congr fun v ↦ ?_
        have h := congrArg ((↑) : Circle → ℂ) (twist_mul_twist_add (θ := θ) y v (x - y - v))
        simp only [Circle.coe_mul, add_sub_cancel] at h
        simp only [hF_def, Circle.coe_mul]
        rw [h]
        ring

instance : Ring (SmoothNoncommutativeTorus θ) where
  mul_assoc a b c := by exact mul_assoc' a b c
  one_mul a := by exact one_mul' a
  mul_one a := by exact mul_one' a
  left_distrib a b c := by exact mul_add' a b c
  right_distrib a b c := by exact add_mul' a b c
  zero_mul a := by ext x; simp [coeff_mul]
  mul_zero a := by ext x; simp [coeff_mul]
  __ := (inferInstance : AddCommGroup (SmoothNoncommutativeTorus θ))

instance : Algebra ℂ (SmoothNoncommutativeTorus θ) :=
  Algebra.ofModule (fun r a b ↦ by exact smul_mul' r a b) fun r a b ↦ by exact mul_smul' r a b

theorem algebraMap_eq_single (c : ℂ) :
    algebraMap ℂ (SmoothNoncommutativeTorus θ) c = single 0 c := by
  rw [Algebra.algebraMap_eq_smul_one, one_def, smul_single, mul_one]

/-! ### The involution -/

/-- The coefficients of the adjoint: reversing `U₁ ^ m U₂ ^ n` gives
`U₂ ^ (-n) U₁ ^ (-m) = exp(2πiθ m n) U₁ ^ (-m) U₂ ^ (-n)`. -/
theorem isRapidDecay_star (a : SmoothNoncommutativeTorus θ) :
    IsRapidDecay fun x ↦ conj (a.coeff (-x)) * twist θ x x := by
  intro k
  obtain ⟨C, hC⟩ := a.isRapidDecay_coeff k
  exact ⟨C, fun x ↦ by simpa using hC (-x)⟩

instance : Star (SmoothNoncommutativeTorus θ) :=
  ⟨fun a ↦ ⟨_, isRapidDecay_star a⟩⟩

@[simp]
theorem coeff_star (a : SmoothNoncommutativeTorus θ) (x : ℤ × ℤ) :
    (star a).coeff x = conj (a.coeff (-x)) * twist θ x x :=
  (rfl)

private theorem conj_twist (y z : ℤ × ℤ) : conj (twist θ y z : ℂ) = twist θ (-y) z := by
  rw [← Circle.coe_inv_eq_conj, twist_neg_left]

private theorem star_star' (a : SmoothNoncommutativeTorus θ) : star (star a) = a := by
  ext x
  rw [coeff_star, coeff_star, map_mul, conj_conj, conj_twist, mul_assoc, ← Circle.coe_mul,
    twist_neg_neg, neg_neg, twist_neg_left]
  simp

private theorem star_mul' (a b : SmoothNoncommutativeTorus θ) : star (a * b) = star b * star a := by
  ext x
  rw [coeff_star, coeff_mul, conj_tsum, ← tsum_mul_right, coeff_mul]
  -- reindex the right-hand sum by `z = x + y`
  conv_rhs => rw [← (Equiv.addLeft x).tsum_eq]
  refine tsum_congr fun y ↦ ?_
  simp only [Equiv.coe_addLeft, coeff_star, map_mul, conj_twist, sub_add_cancel_left, neg_neg,
    neg_add']
  -- both sides carry the phase `exp(2πiθ (x₁x₂ + x₁y₂ + y₁y₂))`
  have h : (twist θ (-y) (-x - y) : ℂ) * twist θ x x =
      twist θ (x + y) (x + y) * twist θ (-y) (-y) * twist θ (x + y) (-y) := by
    simp only [← Circle.coe_mul, twist_apply, ← AddChar.map_add_eq_mul]
    congr 2
    push_cast [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, Prod.fst_sub, Prod.snd_sub]
    ring
  linear_combination (conj (a.coeff y) * conj (b.coeff (-x - y))) * h

instance : StarRing (SmoothNoncommutativeTorus θ) where
  star_involutive a := by exact star_star' a
  star_mul a b := by exact star_mul' a b
  star_add a b := by ext x; simp [add_mul]

instance : StarModule ℂ (SmoothNoncommutativeTorus θ) where
  star_smul c a := by ext x; simp [mul_assoc]

@[simp]
theorem star_single (x : ℤ × ℤ) (c : ℂ) :
    star (single x c : SmoothNoncommutativeTorus θ) = single (-x) (conj c * twist θ x x) := by
  ext y
  rw [coeff_star]
  rcases eq_or_ne y (-x) with rfl | hy
  · simp
  · have : -y ≠ x := fun h ↦ hy (by rw [← h, neg_neg])
    simp [this, hy]

/-! ### The unitary generators -/

private theorem single_mem_unitary {x : ℤ × ℤ} (hx : twist θ x x = 1)
    (h₁ : twist θ (-x) x = 1) (h₂ : twist θ x (-x) = 1) :
    (single x 1 : SmoothNoncommutativeTorus θ) ∈ unitary (SmoothNoncommutativeTorus θ) := by
  rw [Unitary.mem_iff, star_single, single_mul_single, single_mul_single]
  simp [hx, h₁, h₂, one_def]

variable (θ) in
/-- The unitary generator `U₁`, the monomial at `(1, 0)`. -/
def U₁ : unitary (SmoothNoncommutativeTorus θ) :=
  ⟨single (1, 0) 1, single_mem_unitary (by simp [twist_apply]) (by simp [twist_apply])
    (by simp [twist_apply])⟩

variable (θ) in
/-- The unitary generator `U₂`, the monomial at `(0, 1)`. -/
def U₂ : unitary (SmoothNoncommutativeTorus θ) :=
  ⟨single (0, 1) 1, single_mem_unitary (by simp [twist_apply]) (by simp [twist_apply])
    (by simp [twist_apply])⟩

@[simp]
theorem coe_U₁ : (U₁ θ : SmoothNoncommutativeTorus θ) = single (1, 0) 1 :=
  (rfl)

@[simp]
theorem coe_U₂ : (U₂ θ : SmoothNoncommutativeTorus θ) = single (0, 1) 1 :=
  (rfl)

/-- The defining relation of the noncommutative torus: `U₂ U₁ = exp(2πiθ) U₁ U₂`. -/
theorem U₂_mul_U₁ :
    (U₂ θ * U₁ θ : SmoothNoncommutativeTorus θ) = (𝐞 θ : ℂ) • (U₁ θ * U₂ θ) := by
  simp [single_mul_single, twist_apply]

@[simp]
theorem coe_U₁_zpow (m : ℤ) : ((U₁ θ ^ m : unitary _) : SmoothNoncommutativeTorus θ) =
    single (m, 0) 1 := by
  induction m using Int.induction_on with
  | zero => simp [one_def, Prod.zero_eq_mk]
  | succ m ih =>
    rw [zpow_add_one, Submonoid.coe_mul, ih, coe_U₁, single_mul_single]
    simp [twist_apply]
  | pred m ih =>
    rw [zpow_sub_one, Submonoid.coe_mul, ih, ← Unitary.star_eq_inv, Unitary.coe_star, coe_U₁,
      star_single, single_mul_single]
    simp [twist_apply, sub_eq_add_neg]

@[simp]
theorem coe_U₂_zpow (n : ℤ) : ((U₂ θ ^ n : unitary _) : SmoothNoncommutativeTorus θ) =
    single (0, n) 1 := by
  induction n using Int.induction_on with
  | zero => simp [one_def, Prod.zero_eq_mk]
  | succ n ih =>
    rw [zpow_add_one, Submonoid.coe_mul, ih, coe_U₂, single_mul_single]
    simp [twist_apply]
  | pred n ih =>
    rw [zpow_sub_one, Submonoid.coe_mul, ih, ← Unitary.star_eq_inv, Unitary.coe_star, coe_U₂,
      star_single, single_mul_single]
    simp [twist_apply, sub_eq_add_neg]

/-- The ordered monomial `U₁ ^ m U₂ ^ n` is the function with value `1` at `(m, n)`. -/
theorem U₁_zpow_mul_U₂_zpow (m n : ℤ) :
    ((U₁ θ ^ m : unitary _) * (U₂ θ ^ n : unitary _) : SmoothNoncommutativeTorus θ) =
      single (m, n) 1 := by
  rw [coe_U₁_zpow, coe_U₂_zpow, single_mul_single]
  simp [twist_apply]

/-! ### The canonical trace -/

variable (θ) in
/-- The **canonical trace** `τ a = a (0, 0)`, the coefficient of the identity monomial. -/
def trace : SmoothNoncommutativeTorus θ →ₗ[ℂ] ℂ where
  toFun a := a.coeff 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem trace_apply (a : SmoothNoncommutativeTorus θ) : trace θ a = a.coeff 0 :=
  (rfl)

theorem trace_one : trace θ 1 = 1 := by
  simp

theorem trace_single (x : ℤ × ℤ) (c : ℂ) :
    trace θ (single x c) = if x = 0 then c else 0 := by
  simp [Pi.single_apply, eq_comm]

theorem trace_star (a : SmoothNoncommutativeTorus θ) : trace θ (star a) = conj (trace θ a) := by
  simp

/-- The canonical trace is tracial. -/
theorem trace_mul_comm (a b : SmoothNoncommutativeTorus θ) :
    trace θ (a * b) = trace θ (b * a) := by
  rw [trace_apply, trace_apply, coeff_mul, coeff_mul, ← (Equiv.neg (ℤ × ℤ)).tsum_eq]
  refine tsum_congr fun y ↦ ?_
  simp only [Equiv.neg_apply, zero_sub, neg_neg]
  rw [mul_comm (a.coeff (-y)) (b.coeff y), twist_neg_left, twist_neg_right]

/-- `τ (star a * a)` is the sum of the squared moduli of the coefficients of `a`. -/
theorem trace_star_mul_self (a : SmoothNoncommutativeTorus θ) :
    trace θ (star a * a) = ((∑' x, ‖a.coeff x‖ ^ 2 : ℝ) : ℂ) := by
  rw [trace_apply, coeff_mul, ofReal_tsum, ← (Equiv.neg (ℤ × ℤ)).tsum_eq]
  refine tsum_congr fun y ↦ ?_
  simp only [Equiv.neg_apply, coeff_star, neg_neg, zero_sub, ofReal_pow]
  have h : (twist θ (-y) (-y) : ℂ) * twist θ (-y) y = 1 := by
    rw [← Circle.coe_mul, twist_neg_neg, twist_neg_left, mul_inv_cancel, Circle.coe_one]
  rw [← mul_conj']
  linear_combination (conj (a.coeff y) * a.coeff y) * h

theorem summable_norm_sq_coeff (a : SmoothNoncommutativeTorus θ) :
    Summable fun x ↦ ‖a.coeff x‖ ^ 2 := by
  obtain ⟨C, hC⟩ := a.isRapidDecay_coeff.bddAbove_norm
  refine (a.isRapidDecay_coeff.summable_norm.mul_left C).of_nonneg_of_le
    (fun _ ↦ by positivity) fun x ↦ ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

/-- The canonical trace is faithful. -/
theorem trace_star_mul_self_eq_zero_iff (a : SmoothNoncommutativeTorus θ) :
    trace θ (star a * a) = 0 ↔ a = 0 := by
  rw [trace_star_mul_self, ofReal_eq_zero, ← (summable_norm_sq_coeff a).hasSum_iff,
    hasSum_zero_iff_of_nonneg fun _ ↦ by positivity]
  constructor
  · intro h
    ext x
    simpa using congrFun h x
  · rintro rfl
    ext
    simp

end SmoothNoncommutativeTorus

end TauCeti
