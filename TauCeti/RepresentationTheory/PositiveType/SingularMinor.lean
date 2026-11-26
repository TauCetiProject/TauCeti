/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import TauCeti.InformationTheory.Coding.CharacterSum
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.LegendreSymbol.Complex

/-!
# Functions of positive type and singular minors

A function `Θ` on a group `G` has *positive type* if `Θ (a⁻¹ * b) = ⟪u a, u b⟫` for vectors `u a`
of a complex inner product space. This file bounds the `Θ`-mass of the group elements at which a
bilinear minor `det (A₁ᵀ π(s) A₀)` vanishes, for a representation `π` of a finite group by
matrices over a finite field.

Let `π : G →* GL_d(𝔽_q)` and let `A₀, A₁` be `d × e` matrices. Suppose `Θ ≥ 0` has positive type
and that, for every nonzero `v ∈ 𝔽_q^e`, the `Θ`-mass of the stabiliser of the column `A₀ v` under
`π` and that of the row `(A₁ v)ᵀ` under right multiplication by `π` are at most `Y ≥ 0`. Then
`q · Θ {s | det (A₁ᵀ π(s) A₀) = 0} ≤ 2 Θ(G) + q^e q^(d/2) Y`
(`card_mul_sum_det_eq_zero_le`).

The proof counts the left kernel of `Z = A₁ᵀ π(s) A₀`, which has at least `q` elements when
`det Z = 0`, by orthogonality of a primitive additive character `ψ`: it is
`q^(-e) ∑_y ∑_v ψ (yᵀ Z v)`. Summing against `Θ` first, the terms with `y = 0` or `v = 0` give
`Θ(G)` each. For `y, v ≠ 0` the sum `∑_s ψ ((A₁ y)ᵀ π(s) (A₀ v)) Θ(s)` is, up to `q^(d/2) / #G`,
an inner product of two vectors of `ℂ^(𝔽_q^d) ⊗ H` whose squared norms are `#G` times the
`Θ`-masses of the two stabilisers, so it is at most `q^(d/2) Y`.

## Main results

* `inner_sum_sum_eq_card_mul_sum`: Gram sums over a group, `⟪∑ v a, ∑ w b⟫ = #G ∑ f s` when
  `⟪v a, w b⟫ = f (a⁻¹ * b)`.
* `card_mul_sum_det_eq_zero_le`: the bound on the mass of the singular minors.

## Stabilisers under the contragredient

The roadmap states the second stabiliser through the contragredient `π′(s) = (π(s)ᵀ)⁻¹` acting on
columns: `π′(s) x = x`. This holds exactly when `xᵀ π(s) = xᵀ`, the form used here
(`x ᵥ* π s = x`), which needs no inverse transpose on `GL_d`.

## References

These results are adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0,
Copyright 2026 Anthropic PBC), file `src/New/Spanning/SecondMoment/PositiveType.lean`
(`New.inner_sum_sum_eq_card_mul`, `New.norm_sq_sum_tmul_eq_card_mul_sum`,
`New.orthonormal_addChar_div_sqrt`, `New.re_sum_addChar_dotProduct_mul_le`,
`New.card_le_card_filter_vecMul_eq_zero`, `New.card_mul_sum_det_eq_zero_le`).
-/

public section

open Finset Matrix

open scoped InnerProductSpace TensorProduct

variable {G : Type*} [Group G] [Fintype G]

/-- **Gram sums over a group.** If `⟪v a, w b⟫ = f (a⁻¹ * b)` for all `a, b` in a finite group
`G`, then `⟪∑ a, v a, ∑ b, w b⟫ = #G · ∑ s, f s`. -/
theorem inner_sum_sum_eq_card_mul_sum {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {v w : G → E} (f : G → 𝕜) (h : ∀ a b, ⟪v a, w b⟫_𝕜 = f (a⁻¹ * b)) :
    ⟪∑ a, v a, ∑ b, w b⟫_𝕜 = Fintype.card G * ∑ s, f s := by
  -- For each `a` the map `b ↦ a⁻¹ * b` is a bijection of `G`.
  have h_row (a : G) : ⟪v a, ∑ b, w b⟫_𝕜 = ∑ s, f s := by
    simpa [inner_sum, h] using (Group.mulLeft_bijective a⁻¹).sum_comp f
  simp [sum_inner, h_row]

namespace PositiveType

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Let `Θ` have positive type, `Θ (a⁻¹ * b) = ⟪u a, u b⟫`, let `c` be an orthonormal family and
`y : G → X` a family of indices with `y a = y b` exactly when `P (a⁻¹ * b)`. Then the squared norm
of `∑ a, c (y a) ⊗ u a` is `#G` times the `Θ`-mass of `P`. -/
private theorem norm_sq_sum_tmul_eq {X E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {c : X → E} (hc : Orthonormal ℂ c) (y : G → X) (P : G → Prop) [DecidablePred P]
    (hy : ∀ a b, y a = y b ↔ P (a⁻¹ * b)) {Θ : G → ℝ} {u : G → H}
    (hu : ∀ a b, ⟪u a, u b⟫_ℂ = Θ (a⁻¹ * b)) :
    ‖∑ a, c (y a) ⊗ₜ[ℂ] u a‖ ^ 2 = Fintype.card G * ∑ s with P s, Θ s := by
  classical
  have h_inner (a b : G) : ⟪c (y a) ⊗ₜ[ℂ] u a, c (y b) ⊗ₜ[ℂ] u b⟫_ℂ =
      ((if P (a⁻¹ * b) then Θ (a⁻¹ * b) else 0 : ℝ) : ℂ) := by
    rw [TensorProduct.inner_tmul, orthonormal_iff_ite.1 hc, hu]
    by_cases h : P (a⁻¹ * b)
    · simp [(hy a b).2 h, h]
    · simp [mt (hy a b).1 h, h]
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_sum_sum_eq_card_mul_sum
    (fun s ↦ ((if P s then Θ s else 0 : ℝ) : ℂ)) h_inner, sum_filter]
  simp [← Complex.ofReal_natCast, ← Complex.ofReal_sum, ← Complex.ofReal_mul]

variable {k n : Type*} [Field k] [Fintype k] [DecidableEq k] [Fintype n] [DecidableEq n]

omit [DecidableEq k] in
/-- For a primitive additive character `ψ` of a finite field with `q` elements, the functions
`ζ ↦ ψ (-(x ⬝ᵥ ζ)) / √(q ^ |n|)`, one for each `x : kⁿ`, are orthonormal: they are the Fourier
transforms of the point masses. -/
private theorem orthonormal_addChar_dotProduct {ψ : AddChar k ℂ} (hψ : ψ.IsPrimitive) :
    Orthonormal ℂ fun x : n → k ↦ (WithLp.toLp 2 fun ζ : n → k ↦
      ψ (-(x ⬝ᵥ ζ)) / √((Fintype.card k : ℝ) ^ Fintype.card n) : EuclideanSpace ℂ (n → k)) := by
  classical
  rw [orthonormal_iff_ite]
  intro x y
  have h_mul (ζ : n → k) :
      ψ (-(y ⬝ᵥ ζ)) * starRingEnd ℂ (ψ (-(x ⬝ᵥ ζ))) = ψ ((x - y) ⬝ᵥ ζ) := by
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, sub_dotProduct, neg_neg,
      neg_add_eq_sub]
  -- The character sum is `q ^ |n|` for `x = y` and `0` otherwise.
  have h_sum : ∑ ζ : n → k, ψ (-(y ⬝ᵥ ζ)) * starRingEnd ℂ (ψ (-(x ⬝ᵥ ζ))) =
      if x = y then (Fintype.card k : ℂ) ^ Fintype.card n else 0 := by
    simp only [h_mul, AddChar.sum_apply_dotProduct hψ, sub_eq_zero]
  have hq : (0 : ℝ) < (Fintype.card k : ℝ) ^ Fintype.card n := by positivity
  simp only [PiLp.inner_apply, RCLike.inner_apply, map_div₀, Complex.conj_ofReal,
    div_mul_div_comm, ← sum_div, h_sum]
  split_ifs
  · rw [← Complex.ofReal_mul, Real.mul_self_sqrt hq.le, Complex.ofReal_pow,
      Complex.ofReal_natCast, div_self (by exact_mod_cast hq.ne')]
  · simp

/-- The Fourier vector of `x` paired with the point mass at `w` is `ψ (x ⬝ᵥ w) / √(q ^ |n|)`. -/
private theorem inner_addChar_single {ψ : AddChar k ℂ} (r : ℝ) (x w : n → k) :
    ⟪(WithLp.toLp 2 fun ζ : n → k ↦ ψ (-(x ⬝ᵥ ζ)) / r : EuclideanSpace ℂ (n → k)),
      EuclideanSpace.single w (1 : ℂ)⟫_ℂ = ψ (x ⬝ᵥ w) / r := by
  simp [EuclideanSpace.inner_single_right, ← AddChar.map_neg_eq_conj]

omit [Fintype G] [Fintype k] [DecidableEq k] in
/-- The translates `x π(a)⁻¹` of a row agree exactly when `π(a⁻¹ b)` fixes the row. -/
private theorem vecMul_inv_eq_vecMul_inv_iff (π : G →* GL n k) (x : n → k) (a b : G) :
    x ᵥ* (π a⁻¹ : Matrix n n k) = x ᵥ* (π b⁻¹ : Matrix n n k) ↔
      x ᵥ* (π (a⁻¹ * b) : Matrix n n k) = x := by
  have hvm (v : n → k) (g h : G) :
      v ᵥ* (π g : Matrix n n k) ᵥ* (π h : Matrix n n k) = v ᵥ* (π (g * h) : Matrix n n k) := by
    rw [vecMul_vecMul, map_mul, Units.val_mul]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [hvm] using congrArg (· ᵥ* (π b : Matrix n n k)) h
  · simpa [hvm, h] using congrArg (· ᵥ* (π b⁻¹ : Matrix n n k)) h

omit [Fintype G] [Fintype k] [DecidableEq k] in
/-- The translates `π(a) z` of a column agree exactly when `π(a⁻¹ b)` fixes the column. -/
private theorem mulVec_eq_mulVec_iff (π : G →* GL n k) (z : n → k) (a b : G) :
    (π a : Matrix n n k) *ᵥ z = (π b : Matrix n n k) *ᵥ z ↔
      (π (a⁻¹ * b) : Matrix n n k) *ᵥ z = z := by
  have hmv (v : n → k) (g h : G) :
      (π g : Matrix n n k) *ᵥ (π h : Matrix n n k) *ᵥ v = (π (g * h) : Matrix n n k) *ᵥ v := by
    rw [mulVec_mulVec, map_mul, Units.val_mul]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [hmv] using (congrArg ((π a⁻¹ : Matrix n n k) *ᵥ ·) h).symm
  · simpa [hmv, h] using (congrArg ((π a : Matrix n n k) *ᵥ ·) h).symm

/-- **The off-axis character sum.** Let `Θ` have positive type and `ψ` be a primitive additive
character of a finite field with `q` elements. If the `Θ`-mass of the row stabiliser
`{s | x ᵥ* π s = x}` and that of the column stabiliser `{s | π s *ᵥ z = z}` are at most `Y`, then
`Re ∑_s ψ (x ⬝ᵥ π(s) z) Θ(s) ≤ q^(|n|/2) Y`. -/
private theorem re_sum_addChar_mul_le {ψ : AddChar k ℂ} (hψ : ψ.IsPrimitive) (π : G →* GL n k)
    {Θ : G → ℝ} {u : G → H} (hu : ∀ a b, ⟪u a, u b⟫_ℂ = Θ (a⁻¹ * b)) {x z : n → k} {Y : ℝ}
    (hx : ∑ s with x ᵥ* (π s : Matrix n n k) = x, Θ s ≤ Y)
    (hz : ∑ s with (π s : Matrix n n k) *ᵥ z = z, Θ s ≤ Y) :
    (∑ s, ψ (x ⬝ᵥ (π s : Matrix n n k) *ᵥ z) * Θ s).re ≤
      √((Fintype.card k : ℝ) ^ Fintype.card n) * Y := by
  set r : ℝ := √((Fintype.card k : ℝ) ^ Fintype.card n)
  have hr : 0 < r := by positivity
  let c (v : n → k) : EuclideanSpace ℂ (n → k) := WithLp.toLp 2 fun ζ ↦ ψ (-(v ⬝ᵥ ζ)) / r
  let e (v : n → k) : EuclideanSpace ℂ (n → k) := EuclideanSpace.single v 1
  -- The row `x` translated by `a` is `x π(a)⁻¹`; the column `z` translated by `b` is `π(b) z`.
  let X₁ := ∑ a, c (x ᵥ* (π a⁻¹ : Matrix n n k)) ⊗ₜ[ℂ] u a
  let X₀ := ∑ a, e ((π a : Matrix n n k) *ᵥ z) ⊗ₜ[ℂ] u a
  have h_mat (a b : G) : ((π a⁻¹ : GL n k) : Matrix n n k) * (π b : Matrix n n k) =
      (π (a⁻¹ * b) : Matrix n n k) := by
    rw [map_mul, Units.val_mul]
  have h_inner (a b : G) : ⟪c (x ᵥ* (π a⁻¹ : Matrix n n k)) ⊗ₜ[ℂ] u a,
      e ((π b : Matrix n n k) *ᵥ z) ⊗ₜ[ℂ] u b⟫_ℂ =
        ψ (x ⬝ᵥ (π (a⁻¹ * b) : Matrix n n k) *ᵥ z) * Θ (a⁻¹ * b) / r := by
    rw [TensorProduct.inner_tmul, inner_addChar_single, hu, ← dotProduct_mulVec, mulVec_mulVec,
      h_mat, div_mul_eq_mul_div]
  have h_X : ⟪X₁, X₀⟫_ℂ = Fintype.card G * ∑ s, ψ (x ⬝ᵥ (π s : Matrix n n k) *ᵥ z) * Θ s / r :=
    inner_sum_sum_eq_card_mul_sum _ h_inner
  have hG₀ : (0 : ℝ) ≤ Fintype.card G := Nat.cast_nonneg _
  have hX₁ : ‖X₁‖ ^ 2 ≤ Fintype.card G * Y :=
    (norm_sq_sum_tmul_eq (orthonormal_addChar_dotProduct hψ) _ _
      (vecMul_inv_eq_vecMul_inv_iff π x) hu).trans_le (mul_le_mul_of_nonneg_left hx hG₀)
  have hX₀ : ‖X₀‖ ^ 2 ≤ Fintype.card G * Y :=
    (norm_sq_sum_tmul_eq EuclideanSpace.orthonormal_single _ _
      (mulVec_eq_mulVec_iff π z) hu).trans_le (mul_le_mul_of_nonneg_left hz hG₀)
  have h_cs : 2 * (⟪X₁, X₀⟫_ℂ).re ≤ ‖X₁‖ ^ 2 + ‖X₀‖ ^ 2 := by
    have h_re : (⟪X₁, X₀⟫_ℂ).re ≤ ‖X₁‖ * ‖X₀‖ := re_inner_le_norm (𝕜 := ℂ) X₁ X₀
    linarith [two_mul_le_add_sq ‖X₁‖ ‖X₀‖]
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have h_eq : (∑ s, ψ (x ⬝ᵥ (π s : Matrix n n k) *ᵥ z) * Θ s).re =
      r * (⟪X₁, X₀⟫_ℂ).re / Fintype.card G := by
    rw [h_X, ← sum_div, ← Complex.ofReal_natCast, Complex.re_ofReal_mul,
      Complex.div_ofReal_re]
    field_simp
  have h_le : (⟪X₁, X₀⟫_ℂ).re ≤ Fintype.card G * Y := by linarith
  rw [h_eq, div_le_iff₀ hG]
  nlinarith [mul_le_mul_of_nonneg_left h_le hr.le]

/-- A singular square matrix over a field with `q` elements has at least `q` vectors in its left
kernel. -/
private theorem card_le_card_filter_vecMul_eq_zero {m : Type*} [Fintype m] [DecidableEq m]
    {Z : Matrix m m k} (hZ : Z.det = 0) : Fintype.card k ≤ #{y : m → k | y ᵥ* Z = 0} := by
  -- The left kernel holds the `q` multiples of some `y ≠ 0`.
  obtain ⟨y, hy, hyZ⟩ : ∃ y : m → k, y ≠ 0 ∧ y ᵥ* Z = 0 := exists_vecMul_eq_zero_iff.2 hZ
  exact card_le_card_of_injOn (fun t : k ↦ t • y) (by simp [smul_vecMul, hyZ])
    (smul_left_injective k hy).injOn

omit [Group G] in
/-- Counting left kernels: `q` times the `Θ`-mass of the `s` with `det Z(s) = 0` is at most the
sum over `y` of the `Θ`-mass of the `s` with `y ᵥ* Z(s) = 0`. -/
private theorem card_mul_sum_det_eq_zero_le_sum_sum {m : Type*} [Fintype m] [DecidableEq m]
    (Z : G → Matrix m m k) {Θ : G → ℝ} (hΘ : ∀ s, 0 ≤ Θ s) :
    (Fintype.card k : ℝ) * ∑ s with (Z s).det = 0, Θ s ≤
      ∑ y : m → k, ∑ s with y ᵥ* Z s = 0, Θ s := by
  calc (Fintype.card k : ℝ) * ∑ s with (Z s).det = 0, Θ s
      ≤ ∑ s, (#{y : m → k | y ᵥ* Z s = 0} : ℝ) * Θ s := by
        rw [mul_sum, sum_filter]
        gcongr with s
        split_ifs with hs
        · exact mul_le_mul_of_nonneg_right
            (Nat.cast_le.2 (card_le_card_filter_vecMul_eq_zero hs)) (hΘ s)
        · exact mul_nonneg (Nat.cast_nonneg _) (hΘ s)
    _ = ∑ y : m → k, ∑ s with y ᵥ* Z s = 0, Θ s := by
        simp only [sum_filter, natCast_card_filter, sum_mul, boole_mul]
        exact sum_comm

/-- **Functions of positive type and singular minors.** Let `π` be a representation of a finite
group `G` by `n × n` matrices over a field with `q` elements, let `A₀, A₁` be `n × m` matrices, and
let `Θ ≥ 0` have positive type, `Θ (a⁻¹ * b) = ⟪u a, u b⟫`. Suppose that for every nonzero
`v : kᵐ` the `Θ`-mass of the `s` with `π(s) (A₀ v) = A₀ v` and that of the `s` with
`(A₁ v)ᵀ π(s) = (A₁ v)ᵀ` are at most `Y ≥ 0`. Then
`q · Θ {s | det (A₁ᵀ π(s) A₀) = 0} ≤ 2 Θ(G) + q ^ |m| · q ^ (|n| / 2) · Y`.

The second stabiliser is the stabiliser of `A₁ v` under the contragredient `s ↦ (π(s)ᵀ)⁻¹`. -/
theorem card_mul_sum_det_eq_zero_le {m : Type*} [Fintype m] [DecidableEq m] (π : G →* GL n k)
    (A₀ A₁ : Matrix n m k) {Θ : G → ℝ} (hΘ : ∀ s, 0 ≤ Θ s) {u : G → H}
    (hu : ∀ a b, ⟪u a, u b⟫_ℂ = Θ (a⁻¹ * b)) {Y : ℝ} (hY : 0 ≤ Y)
    (h_fix₀ : ∀ v : m → k, v ≠ 0 →
      ∑ s with (π s : Matrix n n k) *ᵥ (A₀ *ᵥ v) = A₀ *ᵥ v, Θ s ≤ Y)
    (h_fix₁ : ∀ v : m → k, v ≠ 0 →
      ∑ s with (A₁ *ᵥ v) ᵥ* (π s : Matrix n n k) = A₁ *ᵥ v, Θ s ≤ Y) :
    Fintype.card k * ∑ s with (A₁ᵀ * (π s : Matrix n n k) * A₀).det = 0, Θ s ≤
      2 * ∑ s, Θ s +
        Fintype.card k ^ Fintype.card m * √((Fintype.card k : ℝ) ^ Fintype.card n) * Y := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AddChar k ℂ, ψ.IsPrimitive :=
    ⟨_, AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive k⟩
  set q : ℝ := (Fintype.card k : ℝ)
  set r : ℝ := √(q ^ Fintype.card n)
  set Q : ℝ := q ^ Fintype.card m
  have hQ : 0 < Q := by positivity
  set Z : G → Matrix m m k := fun s ↦ A₁ᵀ * (π s : Matrix n n k) * A₀
  let W (y v : m → k) (s : G) : ℂ := ψ (y ᵥ* Z s ⬝ᵥ v) * Θ s
  set mass : ℝ := ∑ s, Θ s
  have h_mass : 0 ≤ mass := sum_nonneg fun s _ ↦ hΘ s
  -- Off the axes `y = 0` and `v = 0`, the sum of `W y v` is bounded through the stabilisers.
  have off_axes (y v : m → k) (hy : y ≠ 0) (hv : v ≠ 0) : (∑ s, W y v s).re ≤ r * Y := by
    have h_dot (s : G) : y ᵥ* Z s ⬝ᵥ v = (A₁ *ᵥ y) ⬝ᵥ (π s : Matrix n n k) *ᵥ (A₀ *ᵥ v) := by
      simp [Z, dotProduct_mulVec, ← vecMul_vecMul, vecMul_transpose]
    simp only [W, h_dot]
    exact re_sum_addChar_mul_le hψ π hu (h_fix₁ y hy) (h_fix₀ v hv)
  have term_le (y v : m → k) : (∑ s, W y v s).re ≤
      (if y = 0 then mass else 0) + (if v = 0 then mass else 0) + r * Y := by
    have h_rY : 0 ≤ r * Y := by positivity
    -- On the axes `y = 0` and `v = 0` the character is `1`, so the sum is `Θ(G)`.
    have h_axis (h : y = 0 ∨ v = 0) : (∑ s, W y v s).re = mass := by
      rcases h with rfl | rfl <;> simp [W, mass]
    by_cases hy : y = 0
    · rw [h_axis (.inl hy), ite_eq_left hy]
      split_ifs <;> linarith
    by_cases hv : v = 0
    · rw [h_axis (.inr hv), ite_eq_right hy, ite_eq_left hv]
      linarith
    simpa [hy, hv] using off_axes y v hy hv
  -- By orthogonality of characters, summing over `v` gives `Q` times the mass of the `s` with
  -- `y` in the left kernel of `Z s`.
  have sum_eq (y : m → k) : ∑ v : m → k, (∑ s, W y v s).re = Q * ∑ s with y ᵥ* Z s = 0, Θ s := by
    rw [← Complex.re_sum, sum_comm]
    simp only [W, ← sum_mul, AddChar.sum_apply_dotProduct hψ, sum_filter, mul_sum]
    have hre : ((Fintype.card k : ℂ) ^ Fintype.card m).re = Q := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.ofReal_re]
    simp [apply_ite Complex.re]
    simp only [hre]
  have h_kernel := card_mul_sum_det_eq_zero_le_sum_sum Z hΘ
  have h_total : Q * ∑ y : m → k, ∑ s with y ᵥ* Z s = 0, Θ s ≤ Q * (2 * mass + Q * r * Y) := by
    calc Q * ∑ y : m → k, ∑ s with y ᵥ* Z s = 0, Θ s
        = ∑ y : m → k, ∑ v : m → k, (∑ s, W y v s).re := by simp only [mul_sum, sum_eq]
      _ ≤ ∑ y : m → k, ∑ v : m → k,
          ((if y = 0 then mass else 0) + (if v = 0 then mass else 0) + r * Y) :=
        sum_le_sum fun y _ ↦ sum_le_sum fun v _ ↦ term_le y v
      _ = Q * (2 * mass + Q * r * Y) := by
        simp [sum_add_distrib, Q, q]
        ring
  have := le_of_mul_le_mul_left h_total hQ
  linarith

end PositiveType
