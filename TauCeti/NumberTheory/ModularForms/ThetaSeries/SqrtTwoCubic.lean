/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Asymptotics
import Mathlib.Tactic.NormNum.LegendreSymbol
import TauCeti.NumberTheory.ModularForms.JacobiTheta.OneVariable
import TauCeti.NumberTheory.ModularForms.ThetaSeries.Cubic
import TauCeti.NumberTheory.ModularForms.ThetaSeries.Reciprocity

/-!
# Gauss sums and theta series of the lattice `√2 ℤⁿ`

Let `b` be an orthonormal basis of a real inner product space `E` of dimension `n ≥ 1`, and let
`L = √2 ℤ b` be the cubic lattice `ℤ b = span ℤ (range b)` scaled by `√2`, a copy of `√2 ℤⁿ`. It is
an even lattice of level `4` and determinant `2ⁿ`, with dual `L^∨ = (1/√2) ℤ b`, and it is the
smallest lattice on which several hypotheses of the general theory of Gauss sums and theta series
of an even lattice can be seen to be necessary, and on which the reciprocity law for Gauss sums
reduces to a classical identity. This file records these tests.

**The asymptotic at a cusp is additive.** As `t → 0⁺`,
`t^k Θ_L(a/c + i t) → G_L(a, c) / (c^{2k} covol L)` for `L` of rank `2k`
(`ZLattice.IsEven.tendsto_pow_mul_thetaSeries_nhdsGT`). On `L = √2 ℤ b`, the Gauss sum
`G_L(a, c) = ∑_{y ∈ L / cL} e(a ‖y‖² / (2c))` is the `n`-th power of the classical quadratic Gauss
sum `∑_{u mod c} e(a u² / c)`, which vanishes for odd `a` and `c ≡ 2 (mod 4)`; for instance
`G_L(1, 2) = (1 - 1)ⁿ = 0`. Yet `Θ_L(1/2 + i t) = θ(1 + 2 i t)ⁿ` is a positive real number, where
`θ` is Jacobi's theta function: by its functional equation,
`θ(1 + 2 i t) = (2 t)^{-1/2} ∑_{s ∈ ℤ} e^{-π (s - 1/2)² / (2t)} > 0`
(`TauCeti.jacobiTheta_one_add_I_mul_pos`). So the leading term of `Θ_L` at the cusp `1/2`
vanishes although `Θ_L` does not, and the asymptotic is a limit of `t^k Θ_L`, not a statement
`Θ_L ~ G_L(a, c) · (…)`.

**The odd-modulus evaluation needs coprimality.** For an even lattice of rank `2k` and level `N`,
an odd `a` and a multiple `t` of `N` prime to `a`,
`∑_{y ∈ L^∨ / aL} e(t ‖y‖² / (2a)) = det L · (D_L / a) · a^k` with `D_L = (-1)^k det L`
(`ZLattice.IsEven.dualGaussSum_eq_jacobiSym`). On `L = √2 ℤ b` every summand is `1` as soon as
`4a ∣ t`, so the sum is the number `(2a)ⁿ` of classes of `L^∨ / aL`. In rank `2`, with `a = 3` and
`t = -12`, this is `36`, while `det L · (D_L / a) · a^k = 4 · (-4 / 3) · 3 = -12`. The hypothesis
that fails is that `t` is prime to `a`.

**Reciprocity on `√2 ℤ²` is the squared Landsberg–Schaar identity.** In the coordinates of `b`,
`L / cL` is `(ℤ / c)ⁿ` and, since `aL = 2a L^∨`, `L^∨ / aL` is `(ℤ / 2a)ⁿ`; both Gauss sums
factor over the coordinates: `G_L(a, c) = (∑_{u < c} e(a u² / c))ⁿ` and
`∑_{y ∈ L^∨ / aL} e(t ‖y‖² / (2a)) = (∑_{u < 2a} e(t u² / (4a)))ⁿ`. In rank `2`, where
`covol L = 2`, the reciprocity law `ZLattice.IsEven.gaussSum_eq_mul_dualGaussSum` therefore reads
`(∑_{u < c} e(a u² / c))² = (c / (2a)) · i · (∑_{u < 2a} e(-c u² / (4a)))²`
for all positive integers `a` and `c`, the square of the Landsberg–Schaar identity.

## Main statements

* `ZLattice.isEven_sqrt_two_smul_span_orthonormalBasis`: `√2 ℤ b` is even.
* `ZLattice.gaussSum_sqrt_two_smul_span_orthonormalBasis_eq_zero`: `G_{√2 ℤ b}(a, c) = 0` for
  odd `a` and `c ≡ 2 (mod 4)`.
* `ZLattice.thetaSeries_sqrt_two_smul_span_orthonormalBasis_pos`: `Θ_{√2 ℤ b}(τ) > 0` on the
  line `re τ = 1/2`.
* `ZLattice.tendsto_pow_mul_thetaSeries_sqrt_two_smul_span_orthonormalBasis_nhdsGT`:
  `t^k Θ_{√2 ℤ b}(1/2 + i t) → 0` as `t → 0⁺`.
* `ZLattice.dualGaussSum_sqrt_two_smul_span_orthonormalBasis`: the Gauss sum over `L^∨ / aL` is
  `(2a)ⁿ` when `4a ∣ t`.
* `ZLattice.dualGaussSum_sqrt_two_smul_span_orthonormalBasis_ne_jacobiSym`: in rank `2` the
  Gauss sum at `a = 3`, `t = -12` differs from the odd-modulus closed form.
* `ZLattice.gaussSum_sqrt_two_smul_span_orthonormalBasis_eq_pow`,
  `ZLattice.dualGaussSum_sqrt_two_smul_span_orthonormalBasis_eq_pow`: the two Gauss sums of
  `√2 ℤ b` as powers of one-variable quadratic Gauss sums.
* `TauCeti.sq_sum_range_cexp_two_pi_I_mul_sq_div`: the squared Landsberg–Schaar identity.

## References

* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Springer, 1973, Appendix 4.
* B. Schoeneberg, *Elliptic Modular Functions*, Springer, 1974, Chapter IX.
* H. Rademacher, *Topics in Analytic Number Theory*, Springer, 1973, Chapter 9 (the
  Landsberg–Schaar relation).
-/

public section

open Complex Filter Module Submodule
open UpperHalfPlane (ofComplex)
open scoped ComplexOrder Pointwise Real RealInnerProductSpace Topology UpperHalfPlane

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*} [Fintype ι]
  (b : OrthonormalBasis ι ℝ E)

/-- The lattice instances of `√2 ℤ b` need the scalar `√2` to be nonzero. -/
local instance : NeZero √(2 : ℝ) := ⟨Real.sqrt_ne_zero'.mpr two_pos⟩

/-- The lattice `√2 ℤ b` is even: `ℤ b` is integral and `2` is even. -/
theorem isEven_sqrt_two_smul_span_orthonormalBasis : IsEven (√2 • span ℤ (Set.range b)) := by
  simpa using (isUnimodular_span_orthonormalBasis b).isIntegral.isEven_sqrt_smul even_two

/-- **Vanishing Gauss sums of `√2 ℤ b`.** For an orthonormal basis `b` of a nonzero space, an odd
`a` and `c ≡ 2 (mod 4)`, the Gauss sum `G_L(a, c) = ∑_{y ∈ L / cL} e(a ‖y‖² / (2c))` of the even
lattice `L = √2 ℤ b` vanishes: translating `y` by `(c/2) √2 b i` multiplies every summand by
`e(a c / 4) = -1`. -/
theorem gaussSum_sqrt_two_smul_span_orthonormalBasis_eq_zero [Nonempty ι] {a : ℤ} (ha : Odd a)
    {c : ℕ} (hc : c ≡ 2 [MOD 4])
    [Fintype ((√2 • span ℤ (Set.range b) : Submodule ℤ E) ⧸
      ((c : ℝ) • (√2 • span ℤ (Set.range b))).submoduleOf (√2 • span ℤ (Set.range b)))] :
    gaussSum (√2 • span ℤ (Set.range b)) (isEven_sqrt_two_smul_span_orthonormalBasis b) a c =
      0 := by
  set hL := isEven_sqrt_two_smul_span_orthonormalBasis b
  -- Write `c = 2 c'` with `c' = 2 q + 1` odd, and shift by `w = √2 c' b i`.
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, c = 2 * (2 * q + 1) :=
    ⟨c / 4, by unfold Nat.ModEq at hc; omega⟩
  obtain ⟨p, rfl⟩ := ha
  set i := Classical.arbitrary ι
  set r : ℝ := ((2 * q + 1 : ℕ) : ℝ)
  have hbi : b i ∈ span ℤ (Set.range b) := subset_span ⟨i, rfl⟩
  have hrb : r • b i ∈ span ℤ (Set.range b) := by
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hbi _
  let w : (√2 • span ℤ (Set.range b) : Submodule ℤ E) :=
    ⟨√2 • (r • b i), smul_mem_pointwise_smul _ _ _ hrb⟩
  have hsq (x : E) : ‖√2 • x‖ ^ 2 = 2 * ‖x‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt zero_le_two]
  -- The shift negates every summand.
  have hterm (y : (√2 • span ℤ (Set.range b) : Submodule ℤ E) ⧸
      ((((2 * (2 * q + 1) : ℕ)) : ℝ) • (√2 • span ℤ (Set.range b))).submoduleOf
        (√2 • span ℤ (Set.range b))) :
      gaussTerm _ hL (2 * p + 1) (2 * (2 * q + 1)) 0 (y + Submodule.Quotient.mk w) =
        -gaussTerm _ hL (2 * p + 1) (2 * (2 * q + 1)) 0 y := by
    induction y using Submodule.Quotient.induction_on with | H v
    obtain ⟨u, hu, hv⟩ := mem_smul_pointwise_iff_exists _ _ _ |>.mp v.2
    obtain ⟨m, hm⟩ := isIntegral_iff.mp (isUnimodular_span_orthonormalBasis b).isIntegral u hu _ hbi
    -- `‖u + c' b i‖² = ‖u‖² + 2 c' ⟪u, b i⟫ + c'²`, so the argument of `e` moves by
    -- `a ⟪u, b i⟫ + a c' / 2 ∈ ℤ + 1/2`.
    have hnorm : ‖u + r • b i‖ ^ 2 = ‖u‖ ^ 2 + 2 * r * m + r ^ 2 := by
      rw [norm_add_sq_real, inner_smul_right, hm, norm_smul, b.orthonormal.1 i, mul_one,
        Real.norm_eq_abs, sq_abs]
      ring
    have hvw : ((v + w : (√2 • span ℤ (Set.range b) : Submodule ℤ E)) : E) =
        √2 • (u + r • b i) := by
      rw [Submodule.coe_add, ← hv, smul_add]
    have harg : (((2 * p + 1 : ℤ) : ℝ) * ‖((v + w : (√2 • span ℤ (Set.range b) : Submodule ℤ E))
        : E)‖ ^ 2 / 2) / ((2 * (2 * q + 1) : ℕ) : ℝ) =
        (((2 * p + 1 : ℤ) : ℝ) * ‖(v : E)‖ ^ 2 / 2) / ((2 * (2 * q + 1) : ℕ) : ℝ) +
          (((2 * p + 1) * m + 2 * p * q + p + q : ℤ) : ℝ) + 1 / 2 := by
      rw [hvw, hsq, hnorm, ← hv, hsq]
      simp only [r]
      push_cast
      field_simp
      ring
    rw [← Submodule.Quotient.mk_add, gaussTerm_mk, gaussTerm_mk]
    simp only [ZeroMemClass.coe_zero, inner_zero_right, add_zero]
    have hint (K : ℤ) : cexp (2 * π * I * ((K : ℝ) : ℂ)) = 1 := by
      rw [ofReal_intCast, mul_comm, exp_int_mul_two_pi_mul_I]
    rw [harg, ofReal_add, ofReal_add, mul_add, mul_add, Complex.exp_add, Complex.exp_add, hint,
      show 2 * π * I * ((1 / 2 : ℝ) : ℂ) = π * I by push_cast; ring, exp_pi_mul_I]
    ring
  have h := Fintype.sum_equiv (Equiv.addRight (Submodule.Quotient.mk w))
    (fun y ↦ gaussTerm _ hL (2 * p + 1) (2 * (2 * q + 1)) 0 (y + Submodule.Quotient.mk w))
    (gaussTerm _ hL (2 * p + 1) (2 * (2 * q + 1)) 0) fun y ↦ rfl
  rw [Fintype.sum_congr _ _ hterm, Finset.sum_neg_distrib, ← gaussSum_def] at h
  exact self_eq_neg.mp h.symm

/-- **`Θ_{√2 ℤ b}` is positive on the line `re τ = 1/2`.** For an orthonormal basis `b`, the theta
series of `√2 ℤ b` is `θ(2τ)ⁿ`, and `θ(1 + iy)` is a positive real number for `y > 0`
(`TauCeti.jacobiTheta_one_add_I_mul_pos`). -/
theorem thetaSeries_sqrt_two_smul_span_orthonormalBasis_pos {τ : ℍ} (hτ : τ.re = 1 / 2) :
    0 < thetaSeries (√2 • span ℤ (Set.range b)) τ := by
  rw [thetaSeries_smul_span_orthonormalBasis b (Real.sqrt_ne_zero'.mpr two_pos),
    Real.sq_sqrt zero_le_two]
  have h2τ : ((2 : ℝ) : ℂ) * τ = 1 + I * ((2 * τ.im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hτ]
  rw [h2τ]
  exact pow_pos (TauCeti.jacobiTheta_one_add_I_mul_pos (by positivity)) _

/-- **The leading term of `Θ_{√2 ℤ b}` at the cusp `1/2` vanishes.** For an orthonormal basis `b`
of a space of dimension `2k ≥ 2`, `t^k Θ_{√2 ℤ b}(1/2 + i t) → 0` as `t → 0⁺`, since the limit is
`G_L(1, 2) / (2^{2k} covol L)` and `G_L(1, 2) = 0`; yet `Θ_{√2 ℤ b}(1/2 + i t) > 0`
(`ZLattice.thetaSeries_sqrt_two_smul_span_orthonormalBasis_pos`). -/
theorem tendsto_pow_mul_thetaSeries_sqrt_two_smul_span_orthonormalBasis_nhdsGT [Nonempty ι]
    {k : ℕ} (hk : Fintype.card ι = 2 * k) :
    Tendsto (fun t : ℝ ↦ (t : ℂ) ^ k *
      thetaSeries (√2 • span ℤ (Set.range b)) (ofComplex (1 / 2 + I * t))) (𝓝[>] 0) (𝓝 0) := by
  have := b.toBasis.finiteDimensional_of_finite
  borelize E
  have h := (isEven_sqrt_two_smul_span_orthonormalBasis b).tendsto_pow_mul_thetaSeries_nhdsGT
    ((finrank_eq_card_basis b.toBasis).trans hk) 1 2
  rw [gaussSum_sqrt_two_smul_span_orthonormalBasis_eq_zero b odd_one rfl, zero_div] at h
  simpa using h

/-- **The trivial Gauss sums over `L^∨ / aL` for `L = √2 ℤ b`.** For an orthonormal basis `b` of
a space of dimension `n` and `4a ∣ t`, every summand `e(t ‖y‖² / (2a))` is `1`, and
`∑_{y ∈ L^∨ / aL} e(t ‖y‖² / (2a)) = (2a)ⁿ`. -/
theorem dualGaussSum_sqrt_two_smul_span_orthonormalBasis {t : ℤ} {a : ℕ}
    [Fintype (dual (√2 • span ℤ (Set.range b)) ⧸
      ((a : ℝ) • (√2 • span ℤ (Set.range b))).submoduleOf (dual (√2 • span ℤ (Set.range b))))]
    (h : (4 * a : ℤ) ∣ t) :
    dualGaussSum (√2 • span ℤ (Set.range b)) (isEven_sqrt_two_smul_span_orthonormalBasis b) t a =
      (2 * a) ^ Fintype.card ι := by
  have := b.toBasis.finiteDimensional_of_finite
  -- The level of `√2 ℤ b` divides `4`: it is `4` in positive rank, and `1` in rank `0`.
  have hlevel : level (√2 • span ℤ (Set.range b)) ∣ 4 := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact level_dvd_iff.mpr fun x _ ↦ ⟨0, by rw [← b.sum_repr x]; simp⟩
    · exact dvd_of_eq (by simpa using level_sqrt_smul_span_orthonormalBasis b (m := 2) two_ne_zero)
  have hdvd : (a * level (√2 • span ℤ (Set.range b)) : ℤ) ∣ t :=
    (mul_dvd_mul_left (a : ℤ) (Int.natCast_dvd_natCast.mpr hlevel)).trans (by rwa [mul_comm])
  have hcard : Nat.card (DiscriminantGroup (√2 • span ℤ (Set.range b))) = 2 ^ finrank ℝ E := by
    simpa using natCard_discriminantGroup_sqrt_smul_span_orthonormalBasis b (m := 2) two_ne_zero
  rw [dualGaussSum_eq_pow_mul_card_of_dvd _ hdvd, hcard, finrank_eq_card_basis b.toBasis]
  push_cast
  ring

/-- **The odd-modulus evaluation fails without coprimality.** For `L = √2 ℤ b` of rank `2`, with
`det L = 4` and `D_L = -4`, the Gauss sum `∑_{y ∈ L^∨ / 3L} e(-12 ‖y‖² / 6)` is `36`, while the
closed form `det L · (D_L / 3) · 3` of `ZLattice.IsEven.dualGaussSum_eq_jacobiSym` would be
`-12`. That theorem applies to odd `a` and multiples `t` of the level `4` prime to `a`; here
`a = 3` and `t = -12` are not coprime. -/
theorem dualGaussSum_sqrt_two_smul_span_orthonormalBasis_ne_jacobiSym (hι : Fintype.card ι = 2)
    [Fintype (dual (√2 • span ℤ (Set.range b)) ⧸
      (((3 : ℕ) : ℝ) • (√2 • span ℤ (Set.range b))).submoduleOf
        (dual (√2 • span ℤ (Set.range b))))] :
    dualGaussSum (√2 • span ℤ (Set.range b)) (isEven_sqrt_two_smul_span_orthonormalBasis b)
        (-12) 3 ≠
      Nat.card (DiscriminantGroup (√2 • span ℤ (Set.range b))) *
        jacobiSym (-Nat.card (DiscriminantGroup (√2 • span ℤ (Set.range b)))) 3 * 3 := by
  have hcard : Nat.card (DiscriminantGroup (√2 • span ℤ (Set.range b))) = 2 ^ finrank ℝ E := by
    simpa using natCard_discriminantGroup_sqrt_smul_span_orthonormalBasis b (m := 2) two_ne_zero
  rw [dualGaussSum_sqrt_two_smul_span_orthonormalBasis b (by norm_num), hcard,
    finrank_eq_card_basis b.toBasis, hι]
  norm_num

/-! ### The Gauss sums of `√2 ℤ b` and the squared Landsberg–Schaar identity -/

/-- Let `M` be a lattice with a `ℤ`-basis `r b`. A function `f` on `M / mM` given by
`e(s ‖v‖²)` on the class of each `v ∈ M` sums to the `n`-th power of the one-variable sum
`∑_{u < m} e(s r² u²)`, where `n` is the rank: in the coordinates of `(ℤ / m)ⁿ`, `e(s ‖v‖²)` is
a product of one factor per coordinate. -/
private theorem sum_quotient_eq_pow {M : Submodule ℤ E} (B : Basis ι ℤ M) {r : ℝ}
    (hB : ∀ i, (B i : E) = r • b i) (m : ℕ) [NeZero m] {P : Submodule ℤ M}
    (hP : P = ((m : ℝ) • M).submoduleOf M) [Fintype (M ⧸ P)] (s : ℝ) (f : M ⧸ P → ℂ)
    (hf : ∀ v : M, f (Submodule.Quotient.mk v) =
      cexp (2 * π * I * ((s * ‖(v : E)‖ ^ 2 : ℝ) : ℂ))) :
    ∑ y, f y = (∑ u ∈ Finset.range m,
      cexp (2 * π * I * ((s * r ^ 2 * (u : ℝ) ^ 2 : ℝ) : ℂ))) ^ Fintype.card ι := by
  classical
  subst hP
  rw [← (B.quotientSmulEquivPiZMod m).toEquiv.symm.sum_comp]
  have hterm (x : ι → ZMod m) : f ((B.quotientSmulEquivPiZMod m).toEquiv.symm x) =
      ∏ i, cexp (2 * π * I * ((s * r ^ 2 * ((x i).val : ℝ) ^ 2 : ℝ) : ℂ)) := by
    rw [LinearEquiv.coe_toEquiv_symm, EquivLike.coe_coe, B.quotientSmulEquivPiZMod_symm_apply,
      hf, ← Complex.exp_sum]
    congr 1
    rw [Submodule.coe_sum]
    simp_rw [Submodule.coe_smul, hB, ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
    have hn := b.orthonormal.orthogonalFamily.norm_sum (fun i ↦ (((x i).val : ℤ) : ℝ) * r) .univ
    simp only [LinearIsometry.toSpanSingleton_apply] at hn
    rw [hn]
    simp_rw [Real.norm_eq_abs, sq_abs, Int.cast_natCast]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [Fintype.sum_congr _ _ hterm, ← Fintype.prod_sum (fun (_ : ι) (u : ZMod m) ↦
    cexp (2 * π * I * ((s * r ^ 2 * (u.val : ℝ) ^ 2 : ℝ) : ℂ))), Finset.prod_const,
    Finset.card_univ]
  -- Index the residues modulo `m` by their least natural representatives.
  congr 1
  refine Finset.sum_nbij' (fun u ↦ u.val) (fun n ↦ (n : ZMod m)) (fun u _ ↦ ?_)
    (fun _ _ ↦ Finset.mem_univ _) (fun u _ ↦ ZMod.natCast_zmod_val u) (fun n hn ↦ ?_)
    (fun _ _ ↦ rfl)
  · exact Finset.mem_range.mpr (ZMod.val_lt u)
  · exact ZMod.val_cast_of_lt (Finset.mem_range.mp hn)

/-- **The Gauss sums of `√2 ℤ b`.** For an orthonormal basis `b` of a space of dimension `n`, the
Gauss sum `G_L(a, c) = ∑_{y ∈ L / cL} e(a ‖y‖² / (2c))` of `L = √2 ℤ b` is the `n`-th power of
the classical quadratic Gauss sum: `G_L(a, c) = (∑_{u < c} e(a u² / c))ⁿ`. -/
theorem gaussSum_sqrt_two_smul_span_orthonormalBasis_eq_pow (a : ℤ) (c : ℕ) [NeZero c]
    [Fintype ((√2 • span ℤ (Set.range b) : Submodule ℤ E) ⧸
      ((c : ℝ) • (√2 • span ℤ (Set.range b))).submoduleOf (√2 • span ℤ (Set.range b)))] :
    gaussSum (√2 • span ℤ (Set.range b)) (isEven_sqrt_two_smul_span_orthonormalBasis b) a c =
      (∑ u ∈ Finset.range c, cexp (2 * π * I * a * u ^ 2 / c)) ^ Fintype.card ι := by
  have hc : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne c)
  rw [gaussSum_def, sum_quotient_eq_pow b
    (basisSmul (basisSpanOrthonormalBasis b) (NeZero.ne √(2 : ℝ)))
    (fun i ↦ by rw [coe_basisSmul_apply, coe_basisSpanOrthonormalBasis_apply]) c rfl
    (a / (2 * c)) _ fun v ↦ ?_,
    Real.sq_sqrt zero_le_two]
  · refine congrArg (· ^ _) (Finset.sum_congr rfl fun u _ ↦ congrArg cexp ?_)
    push_cast
    field_simp
  · rw [gaussTerm_mk, ZeroMemClass.coe_zero, inner_zero_right, add_zero]
    exact congrArg (fun x : ℝ ↦ cexp (2 * π * I * x)) (by ring)

/-- **The Gauss sums over `L^∨ / aL` for `L = √2 ℤ b`.** For an orthonormal basis `b` of a space
of dimension `n`, the dual lattice is `L^∨ = (1/√2) ℤ b` and `aL = 2a L^∨`, so
`∑_{y ∈ L^∨ / aL} e(t ‖y‖² / (2a)) = (∑_{u < 2a} e(t u² / (4a)))ⁿ`. -/
theorem dualGaussSum_sqrt_two_smul_span_orthonormalBasis_eq_pow (t : ℤ) (a : ℕ) [NeZero a]
    [Fintype (dual (√2 • span ℤ (Set.range b)) ⧸
      ((a : ℝ) • (√2 • span ℤ (Set.range b))).submoduleOf (dual (√2 • span ℤ (Set.range b))))] :
    dualGaussSum (√2 • span ℤ (Set.range b)) (isEven_sqrt_two_smul_span_orthonormalBasis b) t a =
      (∑ u ∈ Finset.range (2 * a), cexp (2 * π * I * t * u ^ 2 / (4 * a))) ^ Fintype.card ι := by
  have ha : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne a)
  have h2 : √(2 : ℝ) ≠ 0 := NeZero.ne _
  have hdual : dual (√2 • span ℤ (Set.range b)) = (√(2 : ℝ))⁻¹ • span ℤ (Set.range b) := by
    rw [dual_smul _ h2, dual_span_orthonormalBasis]
  have hsmul : (a : ℝ) • (√2 • span ℤ (Set.range b)) =
      ((2 * a : ℕ) : ℝ) • dual (√2 • span ℤ (Set.range b)) := by
    rw [hdual, smul_smul, smul_smul]
    congr 1
    have := Real.mul_self_sqrt (zero_le_two (α := ℝ))
    field_simp
    push_cast
    linear_combination (a : ℝ) * this
  let B := (basisSmul (basisSpanOrthonormalBasis b) (inv_ne_zero h2)).map
    (LinearEquiv.ofEq _ _ hdual.symm)
  have hB (i : ι) : (B i : E) = (√(2 : ℝ))⁻¹ • b i := by
    simp [B]
  rw [dualGaussSum_def, sum_quotient_eq_pow b B hB (2 * a) (by rw [hsmul]) (t / (2 * a)) _
    fun v ↦ ?_, inv_pow, Real.sq_sqrt zero_le_two]
  · refine congrArg (· ^ _) (Finset.sum_congr rfl fun u _ ↦ congrArg cexp ?_)
    push_cast
    field_simp
    ring
  · rw [dualGaussTerm_mk]
    exact congrArg (fun x : ℝ ↦ cexp (2 * π * I * x)) (by ring)

end ZLattice

namespace TauCeti

open ZLattice

/-- **The squared Landsberg–Schaar identity.** For a positive integer `a` and a natural number `c`,
`(∑_{u < c} e(a u² / c))² = (c / (2a)) · i · (∑_{u < 2a} e(-c u² / (4a)))²`.
This is the reciprocity law `ZLattice.IsEven.gaussSum_eq_mul_dualGaussSum` for the lattice
`L = √2 ℤ²` of rank `2`, with covolume `2`, whose two Gauss sums are the squares of the
one-variable sums. The Landsberg–Schaar identity itself,
`∑_{u < c} e(a u² / c) = √(c / (2a)) e(1/8) ∑_{u < 2a} e(-c u² / (4a))`, is the case of rank one,
which is not covered by the reciprocity law of even rank. -/
theorem sq_sum_range_cexp_two_pi_I_mul_sq_div (a c : ℕ) [NeZero a] :
    (∑ u ∈ Finset.range c, cexp (2 * π * I * a * u ^ 2 / c)) ^ 2 =
      c / (2 * a) * I *
        (∑ u ∈ Finset.range (2 * a), cexp (-(2 * π * I * c * u ^ 2 / (4 * a)))) ^ 2 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have : NeZero c := ⟨hc⟩
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have hL := isEven_sqrt_two_smul_span_orthonormalBasis b
  have hne : NeZero √(2 : ℝ) := ⟨Real.sqrt_ne_zero'.mpr two_pos⟩
  -- The quotient `L^∨ / aL` is finite, of order `a² |L^∨ / L|`.
  have : Finite (DiscriminantGroup (√2 • span ℤ (Set.range b))) :=
    hL.isIntegral.finite_discriminantGroup
  have : Finite (dual (√2 • span ℤ (Set.range b)) ⧸
      ((a : ℝ) • (√2 • span ℤ (Set.range b))).submoduleOf (dual (√2 • span ℤ (Set.range b)))) :=
    Nat.finite_of_card_ne_zero <| by
      rw [hL.isIntegral.card_quotient_smul_submoduleOf_dual]
      exact mul_ne_zero (pow_ne_zero _ (NeZero.ne a)) Nat.card_pos.ne'
  have := Fintype.ofFinite (dual (√2 • span ℤ (Set.range b)) ⧸
      ((a : ℝ) • (√2 • span ℤ (Set.range b))).submoduleOf (dual (√2 • span ℤ (Set.range b))))
  have hcov : covolume (√2 • span ℤ (Set.range b)) = 2 := by
    rw [covolume_smul _ (NeZero.ne _) MeasureTheory.volume,
      (isUnimodular_span_orthonormalBasis b).covolume_eq_one, finrank_euclideanSpace_fin,
      abs_of_pos (Real.sqrt_pos.mpr two_pos), Real.sq_sqrt zero_le_two, mul_one]
  have h := hL.gaussSum_eq_mul_dualGaussSum (k := 1) (by simp) a c
  rw [gaussSum_sqrt_two_smul_span_orthonormalBasis_eq_pow,
    dualGaussSum_sqrt_two_smul_span_orthonormalBasis_eq_pow, hcov, Fintype.card_fin] at h
  push_cast at h
  rw [h]
  have ha : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne a)
  field_simp

end TauCeti
