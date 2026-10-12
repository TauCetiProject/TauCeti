/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import TauCeti.NumberTheory.ModularForms.LFunction.EulerProduct
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
import TauCeti.NumberTheory.ModularForms.Newforms.PeterssonAdjoint

/-!
# Satake parameters and Satake angles of a newform

Let `f` be a newform of level `N`, weight `k` and nebentypus `χ`, with `χ` extended by zero to
the integers not coprime to `N` (`HeckeRing.GL2.Newform.dirichletLift`). Its Euler factor at a
prime `p` is `1 - a_p p^{-s} + χ(p) p^{k-1-2s}`. The **Satake parameters** of `f` at `p` are the
two roots `α_p`, `β_p`, counted with multiplicity, of `X² - a_p X + χ(p) p^{k-1}`; equivalently
they are characterised by

`α_p + β_p = a_p`   and   `α_p β_p = χ(p) p^{k-1}`,

and they factor the Euler factor as `(1 - α_p p^{-s}) (1 - β_p p^{-s})`. They form an unordered
pair, recorded as a multiset of cardinality two, and are defined at every `p` with no
hypotheses: at a prime dividing the level they are `a_p` and `0`, the Euler factor being linear
there, and at a prime not dividing it both are nonzero.

A single **Satake angle** is canonical only when the normalized coefficient is real. At a prime
`p` with `χ(p) = 1` — for instance any prime not dividing the level when the nebentypus is
trivial — the coefficient `a_p` is real, because the Petersson adjoint of `T_p` is
`χ(p)⁻¹ T_p` (`HeckeRing.GL2.Newform.qExpansion_coeff_eq_dirichletLift_mul_conj`). More generally,
the angle API takes the reality of `a_p` as an explicit hypothesis. Under the Ramanujan–Deligne
bound `|a_p| ≤ 2 p^{(k-1)/2}`, also explicit since it is not proved here, there is then a unique
`θ_p ∈ [0, π]` with `a_p = 2 p^{(k-1)/2} cos θ_p`. When moreover `χ(p) = 1`, the Satake parameters
are `p^{(k-1)/2} e^{± i θ_p}`. The angle equals
`arccos (Re a_p / (2 p^{(k-1)/2}))`.

The parameters are taken in the arithmetic normalisation of the coefficients `a_p`, rather than
in the unitary normalisation `a_p / p^{(k-1)/2}`: at a prime with `χ(p) = 1` (so not dividing the
level) and under the Ramanujan–Deligne bound, both have absolute value `p^{(k-1)/2}`
(`HeckeRing.GL2.Newform.satakeParameters_eq_exp_satakeAngle`).

## Main definitions

* `HeckeRing.GL2.Newform.satakeParameters`: the Satake parameters of a newform at `p`.
* `HeckeRing.GL2.Newform.satakeAngle`: the Satake angle of a newform at a prime `p` where `a_p`
  is real, under the Ramanujan–Deligne bound.

## Main results

* `HeckeRing.GL2.Newform.satakeParameters_eq_pair_iff`: `{α, β}` are the Satake parameters at
  `p` exactly when `α + β = a_p` and `α β = χ(p) p^{k-1}`.
* `HeckeRing.GL2.Newform.mem_satakeParameters_iff`: the Satake parameters are the roots of
  `X² - a_p X + χ(p) p^{k-1}`.
* `HeckeRing.GL2.Newform.prod_map_one_sub_mul_satakeParameters`: they factor the Euler factor
  at `p`, and `HeckeRing.GL2.Newform.LSeries_eulerProduct_hasProd_satakeParameters` writes the
  Euler product of `L(s, f)` through them.
* `HeckeRing.GL2.Newform.qExpansion_coeff_eq_dirichletLift_mul_conj`: `a_p = χ(p) · conj a_p`
  at a prime not dividing the level.
* `HeckeRing.GL2.Newform.qExpansion_coeff_eq_two_mul_rpow_mul_cos_satakeAngle`: when `a_p` is real
  and satisfies the Ramanujan–Deligne bound, `a_p = 2 p^{(k-1)/2} cos θ_p`, and
  `HeckeRing.GL2.Newform.satakeAngle_eq_of_qExpansion_coeff_eq` says that `θ_p` is the only
  angle in `[0, π]` with this property; `HeckeRing.GL2.Newform.satakeAngle_eq_arccos` computes
  it as `arccos (Re a_p / (2 p^{(k-1)/2}))`.
* `HeckeRing.GL2.Newform.satakeParameters_eq_exp_satakeAngle`: when moreover `χ(p) = 1`, the
  Satake parameters are `p^{(k-1)/2} e^{± i θ_p}`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.9.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, §5.1.
-/

public section

noncomputable section

open Polynomial UpperHalfPlane ComplexConjugate

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The **Satake parameters** of a newform `f` at a prime `p`: the roots, counted with
multiplicity, of `X² - a_p X + χ(p) p^{k-1}`, where `a_p` is the `p`-th Fourier coefficient of `f`
and the nebentypus `χ` is extended by zero to the integers not coprime to the level. This is a
multiset of cardinality two (`card_satakeParameters`). The definition is stated for every natural
number `p`, but carries arithmetic meaning only for primes. -/
def satakeParameters (f : Newform N k) (p : ℕ) : Multiset ℂ :=
  (X ^ 2 - C ((qExpansion 1 f.toCuspForm).coeff p) * X +
    C (f.dirichletLift p * (p : ℂ) ^ (k - 1))).roots

/-- The definition of the Satake parameters as the roots of `X² - a_p X + χ(p) p^{k-1}`. -/
theorem satakeParameters_def (f : Newform N k) (p : ℕ) :
    f.satakeParameters p = (X ^ 2 - C ((qExpansion 1 f.toCuspForm).coeff p) * X +
      C (f.dirichletLift p * (p : ℂ) ^ (k - 1))).roots := (rfl)

/-- The monic quadratic `X² - a X + c` in the shape `C a * X ^ 2 + C b * X + C c` of Mathlib's
quadratic Vieta formulas. -/
private theorem X_sq_sub_C_mul_X_add_C (a c : ℂ) :
    X ^ 2 - C a * X + C c = C 1 * X ^ 2 + C (-a) * X + C c := by
  simp [sub_eq_add_neg]

/-- **The Satake parameters are characterised by their sum and product**: `{α, β}` are the
Satake parameters of `f` at `p` exactly when `α + β = a_p` and `α β = χ(p) p^{k-1}`. -/
theorem satakeParameters_eq_pair_iff (f : Newform N k) (p : ℕ) {α β : ℂ} :
    f.satakeParameters p = {α, β} ↔
      α + β = (qExpansion 1 f.toCuspForm).coeff p ∧
        α * β = f.dirichletLift p * (p : ℂ) ^ (k - 1) := by
  rw [satakeParameters_def, X_sq_sub_C_mul_X_add_C,
    roots_quadratic_eq_pair_iff_of_ne_zero one_ne_zero]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨by linear_combination h₁, by linear_combination -h₂⟩

/-- The Satake parameters at `p` form an unordered pair. -/
theorem exists_satakeParameters_eq_pair (f : Newform N k) (p : ℕ) :
    ∃ α β : ℂ, f.satakeParameters p = {α, β} := by
  apply Multiset.card_eq_two.mp
  rw [satakeParameters_def, IsAlgClosed.card_roots_eq_natDegree, X_sq_sub_C_mul_X_add_C,
    natDegree_quadratic one_ne_zero]

/-- There are two Satake parameters at `p`, counted with multiplicity. -/
@[simp]
theorem card_satakeParameters (f : Newform N k) (p : ℕ) :
    Multiset.card (f.satakeParameters p) = 2 := by
  obtain ⟨α, β, h⟩ := f.exists_satakeParameters_eq_pair p
  rw [h, Multiset.card_pair]

/-- The Satake parameters at `p` are the roots of `X² - a_p X + χ(p) p^{k-1}`. -/
@[simp]
theorem mem_satakeParameters_iff (f : Newform N k) (p : ℕ) (z : ℂ) :
    z ∈ f.satakeParameters p ↔
      z ^ 2 - (qExpansion 1 f.toCuspForm).coeff p * z +
        f.dirichletLift p * (p : ℂ) ^ (k - 1) = 0 := by
  rw [satakeParameters_def, mem_roots', X_sq_sub_C_mul_X_add_C]
  simp only [IsRoot.def, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  constructor
  · rintro ⟨-, h⟩
    linear_combination h
  · refine fun h ↦ ⟨fun h0 ↦ by simpa using congrArg (coeff · 2) h0, by linear_combination h⟩

/-- The Satake parameters at `p` sum to the Fourier coefficient `a_p`. -/
@[simp]
theorem sum_satakeParameters (f : Newform N k) (p : ℕ) :
    (f.satakeParameters p).sum = (qExpansion 1 f.toCuspForm).coeff p := by
  obtain ⟨α, β, h⟩ := f.exists_satakeParameters_eq_pair p
  rw [h, Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton,
    ((f.satakeParameters_eq_pair_iff p).mp h).1]

/-- The product of the Satake parameters at `p` is `χ(p) p^{k-1}`. -/
@[simp]
theorem prod_satakeParameters (f : Newform N k) (p : ℕ) :
    (f.satakeParameters p).prod = f.dirichletLift p * (p : ℂ) ^ (k - 1) := by
  obtain ⟨α, β, h⟩ := f.exists_satakeParameters_eq_pair p
  rw [h, Multiset.insert_eq_cons, Multiset.prod_cons, Multiset.prod_singleton,
    ((f.satakeParameters_eq_pair_iff p).mp h).2]

/-- **The Satake parameters factor the Euler factor**:
`(1 - α_p x) (1 - β_p x) = 1 - a_p x + χ(p) p^{k-1} x²`. -/
theorem prod_map_one_sub_mul_satakeParameters (f : Newform N k) (p : ℕ) (x : ℂ) :
    ((f.satakeParameters p).map fun α ↦ 1 - α * x).prod =
      1 - (qExpansion 1 f.toCuspForm).coeff p * x +
        f.dirichletLift p * (p : ℂ) ^ (k - 1) * x ^ 2 := by
  obtain ⟨α, β, h⟩ := f.exists_satakeParameters_eq_pair p
  obtain ⟨hsum, hprod⟩ := (f.satakeParameters_eq_pair_iff p).mp h
  rw [h, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton, ← hsum, ← hprod]
  ring

/-- At a prime dividing the level, where the extended nebentypus vanishes, the Satake parameters
are `a_p` and `0`. -/
theorem satakeParameters_of_not_coprime (f : Newform N k) {p : ℕ} (hpN : ¬ p.Coprime N) :
    f.satakeParameters p = {(qExpansion 1 f.toCuspForm).coeff p, 0} := by
  rw [satakeParameters_eq_pair_iff, f.dirichletLift_apply_eq_zero p hpN]
  simp

/-- At a nonzero `p` coprime to the level, the Satake parameters are nonzero. -/
theorem zero_notMem_satakeParameters (f : Newform N k) {p : ℕ} (hp : p ≠ 0)
    (hpN : p.Coprime N) : 0 ∉ f.satakeParameters p := by
  intro h0
  have hχ : f.dirichletLift p ≠ 0 := by
    rw [f.dirichletLift_apply_of_coprime hpN]
    exact Units.ne_zero _
  have hprod := Multiset.prod_eq_zero h0
  rw [prod_satakeParameters] at hprod
  exact mul_ne_zero hχ (zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp)) hprod

/-- **The Euler product through the Satake parameters**: for `Re s > k/2 + 1`,
`L(s, f) = ∏_p ((1 - α_p p^{-s}) (1 - β_p p^{-s}))⁻¹`. -/
theorem LSeries_eulerProduct_hasProd_satakeParameters (f : Newform N k) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦
        ((f.satakeParameters p).map fun α ↦ 1 - α * (p.val : ℂ) ^ (-s)).prod⁻¹)
      (LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s) := by
  convert f.LSeries_eulerProduct_hasProd hs using 2 with p
  have hs_neg : -2 * s = 2 * -s := by ring
  rw [prod_map_one_sub_mul_satakeParameters, hs_neg, Complex.cpow_ofNat_mul]

/-! ### The Satake angle -/

/-- **The coefficients of a newform are real up to the nebentypus**: at a prime `p ∤ N`,
`a_p = χ(p) · conj a_p`. In particular `a_p` is real when `χ(p) = 1`. -/
theorem qExpansion_coeff_eq_dirichletLift_mul_conj (f : Newform N k) {p : ℕ} (hp : p.Prime)
    (hpN : p.Coprime N) :
    (qExpansion 1 f.toCuspForm).coeff p =
      f.dirichletLift p * conj ((qExpansion 1 f.toCuspForm).coeff p) := by
  have hcoeff := f.toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue f.isNorm
    ⟨p, hp.pos⟩ hpN
  rw [PNat.mk_coe] at hcoeff
  rw [hcoeff, f.dirichletLift_apply_of_coprime hpN]
  exact f.toEigenformAwayFromLevel.eigenvalue_eq_mul_conj hp hpN

/-- At a prime with `χ(p) = 1`, the `p`-th coefficient of a newform is real. -/
theorem conj_qExpansion_coeff_eq_self_of_dirichletLift_eq_one (f : Newform N k) {p : ℕ}
    (hp : p.Prime) (hχ : f.dirichletLift p = 1) :
    conj ((qExpansion 1 f.toCuspForm).coeff p) = (qExpansion 1 f.toCuspForm).coeff p := by
  have hpN : p.Coprime N := by
    by_contra h
    rw [f.dirichletLift_apply_eq_zero p h] at hχ
    exact zero_ne_one hχ
  simpa [hχ] using (f.qExpansion_coeff_eq_dirichletLift_mul_conj hp hpN).symm

/-- `(p^{(k-1)/2})² = p^{k-1}`. -/
private theorem sq_ofReal_rpow (p : ℕ) (k : ℤ) :
    (((p : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) ^ 2 = (p : ℂ) ^ (k - 1) := by
  have hk : ((k : ℝ) - 1) / 2 * ((2 : ℕ) : ℝ) = ((k - 1 : ℤ) : ℝ) := by
    push_cast
    ring
  rw [← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p), hk,
    Real.rpow_intCast, Complex.ofReal_zpow, Complex.ofReal_natCast]

/-- When `a_p` is real and satisfies the Ramanujan–Deligne bound
`|a_p| ≤ 2 p^{(k-1)/2}`, it is `2 p^{(k-1)/2} cos θ` for
`θ = arccos (Re a_p / (2 p^{(k-1)/2}))`. -/
private theorem qExpansion_coeff_eq_two_mul_rpow_mul_cos_arccos (f : Newform N k) {p : ℕ}
    (hp : p.Prime)
    (hreal : conj ((qExpansion 1 f.toCuspForm).coeff p) =
      (qExpansion 1 f.toCuspForm).coeff p)
    (hR : ‖(qExpansion 1 f.toCuspForm).coeff p‖ ≤ 2 * (p : ℝ) ^ (((k : ℝ) - 1) / 2)) :
    (qExpansion 1 f.toCuspForm).coeff p =
      ((2 * (p : ℝ) ^ (((k : ℝ) - 1) / 2) * Real.cos (Real.arccos
        (((qExpansion 1 f.toCuspForm).coeff p).re / (2 * (p : ℝ) ^ (((k : ℝ) - 1) / 2)))) :
        ℝ) : ℂ) := by
  set a := (qExpansion 1 f.toCuspForm).coeff p
  set r := (p : ℝ) ^ (((k : ℝ) - 1) / 2)
  have hreal' : (a.re : ℂ) = a := by
    rw [Complex.conj_eq_iff_re] at hreal
    exact hreal
  have hr : 0 < 2 * r := mul_pos two_pos (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.pos) _)
  have habs : |a.re| ≤ 2 * r := (Complex.abs_re_le_norm a).trans hR
  rw [Real.cos_arccos ((le_div_iff₀ hr).mpr (by linarith [neg_abs_le a.re]))
    ((div_le_one hr).mpr (le_of_abs_le habs)), mul_div_cancel₀ _ hr.ne', hreal']

/-- When `a_p` is real and satisfies the Ramanujan–Deligne bound `|a_p| ≤ 2 p^{(k-1)/2}`,
there is an angle `θ ∈ [0, π]` with `a_p = 2 p^{(k-1)/2} cos θ`. -/
theorem exists_qExpansion_coeff_eq_two_mul_rpow_mul_cos (f : Newform N k) {p : ℕ}
    (hp : p.Prime)
    (hreal : conj ((qExpansion 1 f.toCuspForm).coeff p) =
      (qExpansion 1 f.toCuspForm).coeff p)
    (hR : ‖(qExpansion 1 f.toCuspForm).coeff p‖ ≤ 2 * (p : ℝ) ^ (((k : ℝ) - 1) / 2)) :
    ∃ θ ∈ Set.Icc 0 Real.pi, (qExpansion 1 f.toCuspForm).coeff p =
      ((2 * (p : ℝ) ^ (((k : ℝ) - 1) / 2) * Real.cos θ : ℝ) : ℂ) :=
  ⟨_, ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩,
    f.qExpansion_coeff_eq_two_mul_rpow_mul_cos_arccos hp hreal hR⟩

/-- The **Satake angle** of a newform `f` at a prime `p` where `a_p` is real, under the
Ramanujan–Deligne bound `|a_p| ≤ 2 p^{(k-1)/2}`: the unique `θ_p ∈ [0, π]` with
`a_p = 2 p^{(k-1)/2} cos θ_p` (`qExpansion_coeff_eq_two_mul_rpow_mul_cos_satakeAngle`,
`satakeAngle_eq_of_qExpansion_coeff_eq`). It is `arccos (Re a_p / (2 p^{(k-1)/2}))`
(`satakeAngle_eq_arccos`). -/
def satakeAngle (f : Newform N k) {p : ℕ} (_hp : p.Prime)
    (_hreal : conj ((qExpansion 1 f.toCuspForm).coeff p) =
      (qExpansion 1 f.toCuspForm).coeff p)
    (_hR : ‖(qExpansion 1 f.toCuspForm).coeff p‖ ≤ 2 * (p : ℝ) ^ (((k : ℝ) - 1) / 2)) : ℝ :=
  Real.arccos (((qExpansion 1 f.toCuspForm).coeff p).re /
    (2 * (p : ℝ) ^ (((k : ℝ) - 1) / 2)))

variable (f : Newform N k) {p : ℕ} (hp : p.Prime)
  (hreal : conj ((qExpansion 1 f.toCuspForm).coeff p) =
    (qExpansion 1 f.toCuspForm).coeff p)
  (hR : ‖(qExpansion 1 f.toCuspForm).coeff p‖ ≤ 2 * (p : ℝ) ^ (((k : ℝ) - 1) / 2))

/-- The Satake angle is nonnegative. -/
theorem satakeAngle_nonneg : 0 ≤ f.satakeAngle hp hreal hR :=
  Real.arccos_nonneg _

/-- The Satake angle is at most `π`. -/
theorem satakeAngle_le_pi : f.satakeAngle hp hreal hR ≤ Real.pi :=
  Real.arccos_le_pi _

/-- **The Satake angle for a real coefficient**: under the Ramanujan–Deligne bound
`|a_p| ≤ 2 p^{(k-1)/2}`, the coefficient is `a_p = 2 p^{(k-1)/2} cos θ_p`. -/
theorem qExpansion_coeff_eq_two_mul_rpow_mul_cos_satakeAngle :
    (qExpansion 1 f.toCuspForm).coeff p =
      ((2 * (p : ℝ) ^ (((k : ℝ) - 1) / 2) * Real.cos (f.satakeAngle hp hreal hR) : ℝ) :
        ℂ) := by
  simpa [satakeAngle] using
    f.qExpansion_coeff_eq_two_mul_rpow_mul_cos_arccos hp hreal hR

/-- **The Satake angle is the only angle in `[0, π]` with `a_p = 2 p^{(k-1)/2} cos θ`.** -/
theorem satakeAngle_eq_of_qExpansion_coeff_eq {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (h : (qExpansion 1 f.toCuspForm).coeff p =
      ((2 * (p : ℝ) ^ (((k : ℝ) - 1) / 2) * Real.cos θ : ℝ) : ℂ)) :
    f.satakeAngle hp hreal hR = θ := by
  have hr : 0 < 2 * (p : ℝ) ^ (((k : ℝ) - 1) / 2) :=
    mul_pos two_pos (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.pos) _)
  have hcos := (f.qExpansion_coeff_eq_two_mul_rpow_mul_cos_satakeAngle hp hreal hR).symm.trans h
  rw [Complex.ofReal_inj, mul_right_inj' hr.ne'] at hcos
  exact Real.injOn_cos ⟨f.satakeAngle_nonneg hp hreal hR, f.satakeAngle_le_pi hp hreal hR⟩
    ⟨hθ₀, hθπ⟩ hcos

/-- The Satake angle is `arccos (Re a_p / (2 p^{(k-1)/2}))`. -/
@[simp]
theorem satakeAngle_eq_arccos :
    f.satakeAngle hp hreal hR = Real.arccos (((qExpansion 1 f.toCuspForm).coeff p).re /
      (2 * (p : ℝ) ^ (((k : ℝ) - 1) / 2))) := by
  rw [satakeAngle]

/-- **The Satake parameters at a prime with `χ(p) = 1`**: under the Ramanujan–Deligne bound they
are the complex conjugates `p^{(k-1)/2} e^{± i θ_p}`. Here `a_p` is real by
`conj_qExpansion_coeff_eq_self_of_dirichletLift_eq_one`. -/
theorem satakeParameters_eq_exp_satakeAngle (hχ : f.dirichletLift p = 1) :
    f.satakeParameters p =
      {((p : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) * Complex.exp (f.satakeAngle hp
          (f.conj_qExpansion_coeff_eq_self_of_dirichletLift_eq_one hp hχ) hR * Complex.I),
        ((p : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) * Complex.exp (-f.satakeAngle hp
          (f.conj_qExpansion_coeff_eq_self_of_dirichletLift_eq_one hp hχ) hR * Complex.I)} := by
  rw [satakeParameters_eq_pair_iff, hχ, one_mul, ← sq_ofReal_rpow,
    f.qExpansion_coeff_eq_two_mul_rpow_mul_cos_satakeAngle hp
      (f.conj_qExpansion_coeff_eq_self_of_dirichletLift_eq_one hp hχ) hR]
  constructor
  · rw [← mul_add, ← Complex.two_cos]
    push_cast
    ring
  · rw [mul_mul_mul_comm, ← Complex.exp_add, neg_mul, add_neg_cancel, Complex.exp_zero, mul_one,
      sq]

end HeckeRing.GL2.Newform
