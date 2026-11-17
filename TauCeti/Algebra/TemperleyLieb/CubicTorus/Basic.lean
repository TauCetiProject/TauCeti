/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Data.ZMod.Basic
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic
public import TauCeti.Algebra.TemperleyLieb.Star
public import TauCeti.Analysis.StarAlgebra.GNS.Basic
-- Private: trigonometric special values for `ω = exp (2πi/3)`, matrix trace calculations, and
-- involution dimension formulas are used only inside proofs.
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import TauCeti.LinearAlgebra.Trace.Idempotent

/-!
# The cubic quantum torus representation of the Temperley–Lieb algebra at `δ = √3`

At the loop parameter `δ = √3 = 2 cos (π / 6)` — corresponding to Jones index `δ² = 3` — the
Temperley–Lieb algebra `TemperleyLieb ℂ (√3 : ℂ) m` surjects onto the inversion-fixed subalgebra
`cubicFixed (m - 1)` of the cubic quantum torus `CubicTorus (m - 1)` via a `ℂ`-star-algebra
homomorphism `F_m = cubicFixedHom m`.

Concretely, let `ω = exp (2πi / 3)` (`cubeRootOfUnity`) and let `chainForm N` be the alternating
biadditive form
`B(a, b) = ∑_{j + 1 = k} (a_j b_k - b_j a_k)` on `Fin N → ZMod 3`.
The factor set `cubicFactor N a b = ω ^ (2 * B(a, b))` defines the `3 ^ N`-dimensional twisted
group algebra `CubicTorus N` with Weyl basis `W(a) = weyl N a`, multiplication
`W(a) * W(b) = α(a, b) • W(a * b)`, commutation law `W(a) * W(b) = ω ^ (B(a, b)) • (W(b) * W(a))`,
and analytic adjoint `star (W(a)) = W(a⁻¹)`.

* **Scalar trace and Parseval positivity**: `cubicScalarCoefficient N` extracts the `1`-coordinate
  in the Weyl basis. It is a star-preserving tracial functional with
  `s_N (star x * x) = ∑_a |x_a|² ≥ 0`, vanishing only at `x = 0`, and therefore defines a faithful
  `StarPositiveFunctional` `cubicScalarFunctional N`.
* **Inversion-fixed subalgebra**: `cubicInversion N` (`θ_N : W(a) ↦ W(a⁻¹)`) is a star-algebra
  involution of `CubicTorus N` with trace `1`, so its fixed subalgebra `cubicFixed N` has complex
  dimension `(3 ^ N + 1) / 2`.
* **Temperley–Lieb projections and homomorphism**: the site unitaries `U_j = cubicSite N j` satisfy
  `U_j ^ 3 = 1`, `U_j * U_{j + 1} = ω • (U_{j + 1} * U_j)`, and commute at distance `≥ 2`. The
  self-adjoint idempotents `p_j = 3⁻¹ • (1 + U_j + U_j ^ 2)` lie in `cubicFixed N`, satisfy
  `p_j * p_k * p_j = 3⁻¹ • p_j` for `|j - k| = 1`, and commute for `|j - k| ≥ 2`. Rescaling by
  `√3` defines `cubicFixedHom m : TemperleyLieb ℂ (√3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1)`.

Surjectivity of `cubicFixedHom`, tower inclusions, the conditional expectation, the Markov trace
identity, positivity, and the identification of the trace-radical Jones quotient with
`cubicFixed (m - 1)` are established in `TauCeti.Algebra.TemperleyLieb.CubicTorus.Quotient`. The
Gaussian braid representation and its finiteness are established in
`TauCeti.Algebra.TemperleyLieb.CubicTorus.Braid`.

## Main definitions

* `TauCeti.TemperleyLieb.cubeRootOfUnity` and `TauCeti.TemperleyLieb.cubeRootPow`:
  `ω = exp (2πi / 3)` as a unit of `ℂ` and the additive power map `ZMod 3 → ℂˣ`.
* `TauCeti.TemperleyLieb.chainForm` and `TauCeti.TemperleyLieb.cubicFactor`: the alternating
  nearest-neighbor form on `Fin N → ZMod 3` and the normalized factor set `α(a, b) = ω^(2 B(a, b))`.
* `TauCeti.TemperleyLieb.CubicTorus`, `TauCeti.TemperleyLieb.cubicTorusEquiv`,
  `TauCeti.TemperleyLieb.weyl`, and `TauCeti.TemperleyLieb.cubicBasis`: the cubic quantum torus
  `G_N` realized as `twistedMonoidAlgebra ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)`,
  its canonical algebra equivalence, and its Weyl basis `W(a)`.
* `TauCeti.TemperleyLieb.cubicScalarCoefficient` and `TauCeti.TemperleyLieb.cubicScalarFunctional`:
  the normalized scalar-part trace `s_N` and its bundled faithful positive functional.
* `TauCeti.TemperleyLieb.cubicInversion` and `TauCeti.TemperleyLieb.cubicFixed`: the inversion
  involution `θ_N : W(a) ↦ W(a⁻¹)` and its fixed star-subalgebra `C_N`.
* `TauCeti.TemperleyLieb.cubicSite`, `TauCeti.TemperleyLieb.cubicProjection`, and
  `TauCeti.TemperleyLieb.cubicFixedHom`: the site unitaries `U_j`, Temperley–Lieb projections
  `p_j`, and star-algebra homomorphism `F_m : TemperleyLieb ℂ (√3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1)`.

## Main results

* `TauCeti.TemperleyLieb.finrank_cubicTorus` and `TauCeti.TemperleyLieb.finrank_cubicFixed`:
  `finrank ℂ (CubicTorus N) = 3 ^ N` and `finrank ℂ (cubicFixed N) = (3 ^ N + 1) / 2`.
* `TauCeti.TemperleyLieb.cubicScalarCoefficient_star_mul`,
  `TauCeti.TemperleyLieb.cubicScalarCoefficient_star_mul_self_nonneg`, and
  `TauCeti.TemperleyLieb.nullSubmodule_cubicScalarFunctional`: Parseval identity, positivity, and
  faithfulness of the scalar trace.
* `TauCeti.TemperleyLieb.cubicProjection_mul_cubicProjection_mul_of_adj` and
  `TauCeti.TemperleyLieb.coe_cubicFixedHom_e`: the Temperley–Lieb relations and the star-algebra
  representation `cubicFixedHom m`.

## Implementation notes

`CubicTorus N` is defined as an opaque type alias (`def`) for
`twistedMonoidAlgebra ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)` with a single `Ring`
and `Algebra ℂ` hierarchy transported from `twistedMonoidAlgebra` (exhibited via
`cubicTorusEquiv`). Keeping `CubicTorus N` opaque prevents typeclass synthesis from seeing both
`Subalgebra.toSemiring` and `Subalgebra.toRing` on `Subalgebra ℂ (Module.End ℂ (_ →₀ ℂ))`
simultaneously, where `Finsupp.instAddCommMonoid` and `Finsupp.instAddCommGroup.toAddCommMonoid`
do not unify at reducible transparency, and also gives `CubicTorus N` a clean `StarRing` and
`StarModule ℂ` hierarchy without competing with any generic `Subalgebra` instances.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111.
* C. Galindo and E. C. Rowell, *Braid representations from unitary braided vector spaces*,
  J. Math. Phys. 55 (2014), 061702, Proposition 3.6.
* E. C. Rowell and H. Wenzl, `SO(N)_2` *braid group representations are Gaussian*, Quantum Topol.
  8 (2017), no. 1, 1–33.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4.
-/

public section

open scoped ComplexConjugate ComplexOrder

namespace TauCeti.TemperleyLieb

/-! ### Arithmetic for `√3` and the primitive cube root of unity `ω = exp (2πi / 3)` -/

/-- Registers `IsSelfAdjoint (Real.sqrt 3 : ℂ)` as a `Fact` so that
`TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m` carries the analytic adjoint instances
`TemperleyLieb.instStarRing` and `TemperleyLieb.instStarModule`. -/
instance : Fact (IsSelfAdjoint (Real.sqrt 3 : ℂ)) :=
  ⟨Complex.conj_ofReal _⟩

private theorem sqrt_three_coe_mul_self :
    (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
  exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)

/-- The primitive cube root of unity `ω = exp (2πi / 3)`, as a unit of `ℂ`. -/
noncomputable def cubeRootOfUnity : ℂˣ :=
  Units.mk0 (Complex.exp (2 * Real.pi / 3 * Complex.I)) (Complex.exp_ne_zero _)

/-- Unfolding the underlying complex value of `cubeRootOfUnity`. -/
theorem cubeRootOfUnity_val :
    (cubeRootOfUnity : ℂ) = Complex.exp (2 * Real.pi / 3 * Complex.I) :=
  (rfl)

/-- Rectangular form of `ω = exp (2πi / 3) = -1/2 + (√3 / 2) i`. -/
theorem cubeRootOfUnity_val_eq :
    (cubeRootOfUnity : ℂ) = -(2 : ℂ)⁻¹ + ((Real.sqrt 3 : ℂ) / 2) * Complex.I := by
  have harg : (2 * (Real.pi : ℂ) / 3 * Complex.I) = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
    push_cast
    rfl
  have h2pi3 : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
  rw [cubeRootOfUnity_val, harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    h2pi3, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  ring

/-- `ω ^ 3 = 1` in `ℂˣ`. -/
@[simp]
theorem cubeRootOfUnity_pow_three : cubeRootOfUnity ^ 3 = 1 := by
  ext
  simp only [Units.val_pow_eq_pow_val, cubeRootOfUnity_val, Units.val_one]
  rw [← Complex.exp_nat_mul]
  convert Complex.exp_two_pi_mul_I using 2
  push_cast
  ring

/-- `ω ^ 3 = 1` in `ℂ`. -/
@[simp]
theorem cubeRootOfUnity_val_pow_three : (cubeRootOfUnity : ℂ) ^ 3 = 1 := by
  rw [← Units.val_pow_eq_pow_val, cubeRootOfUnity_pow_three, Units.val_one]

/-- The primitive cube root of unity is not `1`. -/
theorem cubeRootOfUnity_ne_one : cubeRootOfUnity ≠ 1 := by
  intro h
  have him := congrArg Complex.im (congrArg Units.val h)
  rw [cubeRootOfUnity_val_eq, Units.val_one] at him
  simp [Complex.div_ofNat] at him

/-- Cyclotomic relation `1 + ω + ω² = 0`. -/
theorem one_add_cubeRootOfUnity_add_sq :
    (1 : ℂ) + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2 = 0 := by
  have hne : (cubeRootOfUnity : ℂ) - 1 ≠ 0 :=
    sub_ne_zero.mpr (Units.ext_iff.not.mp cubeRootOfUnity_ne_one)
  have hmul :
      ((cubeRootOfUnity : ℂ) - 1) *
        (1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2) = 0 := by
    calc
      ((cubeRootOfUnity : ℂ) - 1) *
          (1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2) =
          (cubeRootOfUnity : ℂ) ^ 3 - 1 := by ring
      _ = 0 := by rw [cubeRootOfUnity_val_pow_three, sub_self]
  exact (mul_eq_zero.mp hmul).resolve_left hne

/-- The inverse of `ω` is `ω²`. -/
theorem cubeRootOfUnity_inv_eq_sq : cubeRootOfUnity⁻¹ = cubeRootOfUnity ^ 2 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ', cubeRootOfUnity_pow_three]

/-- `ω ≠ ω⁻¹`. -/
theorem cubeRootOfUnity_ne_inv : cubeRootOfUnity ≠ cubeRootOfUnity⁻¹ := by
  intro h
  have hsq : cubeRootOfUnity ^ 2 = 1 := by
    rw [sq, ← inv_eq_iff_mul_eq_one]
    exact h.symm
  have h1 : cubeRootOfUnity = 1 := by
    have := cubeRootOfUnity_pow_three
    rw [pow_succ, hsq, one_mul] at this
    exact this
  exact cubeRootOfUnity_ne_one h1

/-- Complex conjugation sends `ω` to `ω⁻¹`. -/
@[simp]
theorem star_cubeRootOfUnity_val :
    star (cubeRootOfUnity : ℂ) = ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ) := by
  have hinv : ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ) = (cubeRootOfUnity : ℂ)⁻¹ := rfl
  rw [hinv, cubeRootOfUnity_val, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [map_div₀, map_ofNat]

/-- The additive-to-multiplicative character `x ↦ ω ^ x.val` from `ZMod 3` into `ℂˣ`. -/
noncomputable def cubeRootPow (x : ZMod 3) : ℂˣ :=
  cubeRootOfUnity ^ x.val

/-- Unfolding `cubeRootPow` as `cubeRootOfUnity ^ x.val`. -/
theorem cubeRootPow_def (x : ZMod 3) : cubeRootPow x = cubeRootOfUnity ^ x.val :=
  (rfl)

/-- `cubeRootPow 0 = 1`. -/
@[simp]
theorem cubeRootPow_zero : cubeRootPow 0 = 1 := by
  simp [cubeRootPow_def]

/-- `cubeRootPow 1 = ω`. -/
@[simp]
theorem cubeRootPow_one : cubeRootPow 1 = cubeRootOfUnity := by
  change cubeRootOfUnity ^ 1 = cubeRootOfUnity
  simp

/-- `cubeRootPow` converts addition in `ZMod 3` to multiplication in `ℂˣ`. -/
@[simp]
theorem cubeRootPow_add (x y : ZMod 3) :
    cubeRootPow (x + y) = cubeRootPow x * cubeRootPow y := by
  simp only [cubeRootPow_def, ZMod.val_add]
  rw [← pow_add, ← pow_eq_pow_mod _ cubeRootOfUnity_pow_three]

/-- `cubeRootPow` converts negation in `ZMod 3` to inversion in `ℂˣ`. -/
@[simp]
theorem cubeRootPow_neg (x : ZMod 3) :
    cubeRootPow (-x) = (cubeRootPow x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← cubeRootPow_add, neg_add_cancel, cubeRootPow_zero]

/-- `cubeRootPow` converts subtraction in `ZMod 3` to division in `ℂˣ`. -/
theorem cubeRootPow_sub (x y : ZMod 3) :
    cubeRootPow (x - y) = cubeRootPow x * (cubeRootPow y)⁻¹ := by
  rw [sub_eq_add_neg, cubeRootPow_add, cubeRootPow_neg]

/-- Every value of `cubeRootPow` has cube `1`. -/
@[simp]
theorem cubeRootPow_pow_three (x : ZMod 3) : cubeRootPow x ^ 3 = 1 := by
  rw [cubeRootPow_def, ← pow_mul, mul_comm, pow_mul, cubeRootOfUnity_pow_three, one_pow]

/-- Complex conjugation negates the `ZMod 3` exponent of `cubeRootPow`. -/
@[simp]
theorem star_cubeRootPow_val (x : ZMod 3) :
    star (cubeRootPow x : ℂ) = (cubeRootPow (-x) : ℂ) := by
  rw [cubeRootPow_neg, cubeRootPow_def, Units.val_pow_eq_pow_val, star_pow,
    star_cubeRootOfUnity_val, ← Units.val_pow_eq_pow_val, inv_pow]

/-- `ω ^ x = 1` if and only if `x = 0` in `ZMod 3`. -/
@[simp]
theorem cubeRootPow_eq_one_iff {x : ZMod 3} : cubeRootPow x = 1 ↔ x = 0 := by
  constructor
  · intro h
    have hlt := ZMod.val_lt x
    have hcases : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by omega
    rcases hcases with hv | hv | hv
    · exact (ZMod.val_eq_zero x).mp hv
    · rw [cubeRootPow_def, hv, pow_one] at h
      exact absurd h cubeRootOfUnity_ne_one
    · rw [cubeRootPow_def, hv, ← cubeRootOfUnity_inv_eq_sq, inv_eq_one] at h
      exact absurd h cubeRootOfUnity_ne_one
  · rintro rfl
    exact cubeRootPow_zero

/-- `cubeRootPow : ZMod 3 → ℂˣ` is injective. -/
theorem cubeRootPow_injective : Function.Injective cubeRootPow := by
  intro x y hxy
  have h : cubeRootPow (x - y) = 1 := by
    rw [cubeRootPow_sub, hxy, mul_inv_cancel]
  exact sub_eq_zero.mp (cubeRootPow_eq_one_iff.mp h)

/-! ### The chain form and cubic factor set -/

/-- The alternating nearest-neighbor bilinear form
`B(a, b) = ∑_{i + 1 = j} (a_i b_j - b_i a_j)` on `Fin N → ZMod 3`. -/
def chainForm (N : ℕ) (a b : Fin N → ZMod 3) : ZMod 3 :=
  ∑ i : Fin N, ∑ j : Fin N, if (i : ℕ) + 1 = j then a i * b j - b i * a j else 0

/-- Unfolding `chainForm` as its explicit double sum. -/
theorem chainForm_def (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N a b =
      ∑ i : Fin N, ∑ j : Fin N, if (i : ℕ) + 1 = j then a i * b j - b i * a j else 0 :=
  (rfl)

/-- `chainForm` is alternating: `B(a, a) = 0`. -/
@[simp]
theorem chainForm_self (N : ℕ) (a : Fin N → ZMod 3) : chainForm N a a = 0 := by
  simp [chainForm_def]

/-- `chainForm` is skew-symmetric: `B(b, a) = -B(a, b)`. -/
theorem chainForm_swap (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N b a = -chainForm N a b := by
  rw [chainForm_def, chainForm_def, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> ring

/-- `chainForm` is additive in its first argument. -/
theorem chainForm_add_left (N : ℕ) (a b c : Fin N → ZMod 3) :
    chainForm N (a + b) c = chainForm N a c + chainForm N b c := by
  rw [chainForm_def, chainForm_def, chainForm_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Pi.add_apply]
  split_ifs <;> ring

/-- `chainForm` is additive in its second argument. -/
theorem chainForm_add_right (N : ℕ) (a b c : Fin N → ZMod 3) :
    chainForm N a (b + c) = chainForm N a b + chainForm N a c := by
  rw [chainForm_swap, chainForm_add_left, chainForm_swap N b a, chainForm_swap N c a]
  ring

/-- `chainForm` vanishes when its first argument is `0`. -/
@[simp]
theorem chainForm_zero_left (N : ℕ) (b : Fin N → ZMod 3) : chainForm N 0 b = 0 := by
  simp [chainForm_def]

/-- `chainForm` vanishes when its second argument is `0`. -/
@[simp]
theorem chainForm_zero_right (N : ℕ) (a : Fin N → ZMod 3) : chainForm N a 0 = 0 := by
  simp [chainForm_def]

/-- `chainForm` is homogeneous with respect to negation in its first argument. -/
@[simp]
theorem chainForm_neg_left (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N (-a) b = -chainForm N a b := by
  have h := chainForm_add_left N (-a) a b
  rw [neg_add_cancel, chainForm_zero_left] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- `chainForm` is homogeneous with respect to negation in its second argument. -/
@[simp]
theorem chainForm_neg_right (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N a (-b) = -chainForm N a b := by
  rw [chainForm_swap, chainForm_neg_left, chainForm_swap, neg_neg]

/-- `chainForm` is invariant under simultaneous negation of both arguments. -/
theorem chainForm_neg_neg (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N (-a) (-b) = chainForm N a b := by
  simp

/-- Pairing `a` with the `k`-th standard basis vector `Pi.single k 1` picks out `a_{k-1} - a_{k+1}`
(with out-of-range coordinates read as `0`). -/
theorem chainForm_single_right (N : ℕ) (a : Fin N → ZMod 3) (k : Fin N) :
    chainForm N a (Pi.single k 1) =
      (if h : 0 < (k : ℕ) then a ⟨(k : ℕ) - 1, by omega⟩ else 0) -
        (if h : (k : ℕ) + 1 < N then a ⟨(k : ℕ) + 1, h⟩ else 0) := by
  let e : Fin N → ZMod 3 := Pi.single k 1
  have he : ∀ i : Fin N, e i = if i = k then 1 else 0 := fun i ↦ Pi.single_apply k 1 i
  rw [chainForm_def]
  have hsplit :
      (∑ i : Fin N, ∑ j : Fin N,
          if (i : ℕ) + 1 = j then a i * e j - e i * a j else 0) =
        (∑ i : Fin N, ∑ j : Fin N, if (i : ℕ) + 1 = j then a i * e j else 0) -
          (∑ i : Fin N, ∑ j : Fin N, if (i : ℕ) + 1 = j then e i * a j else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs <;> ring
  change (∑ i : Fin N, ∑ j : Fin N,
    if (i : ℕ) + 1 = j then a i * e j - e i * a j else 0) = _
  rw [hsplit]
  congr 1
  · calc
      (∑ i : Fin N, ∑ j : Fin N, if (i : ℕ) + 1 = j then a i * e j else 0) =
          ∑ i : Fin N, if (i : ℕ) + 1 = k then a i else 0 := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_eq_single k]
        · simp [he]
        · intro j _ hjk
          simp [he, hjk]
        · intro hk
          exact absurd (Finset.mem_univ k) hk
      _ = if h : 0 < (k : ℕ) then a ⟨(k : ℕ) - 1, by omega⟩ else 0 := by
        split_ifs with hk
        · rw [Finset.sum_eq_single (⟨(k : ℕ) - 1, by omega⟩ : Fin N)]
          · have hstep : (k : ℕ) - 1 + 1 = (k : ℕ) := by omega
            simp [hstep]
          · intro i _ hi
            have hne : (i : ℕ) + 1 ≠ (k : ℕ) := fun heq ↦ hi (Fin.ext (by dsimp; omega))
            simp [hne]
          · intro hmem
            exact absurd (Finset.mem_univ _) hmem
        · refine Finset.sum_eq_zero fun i _ ↦ ?_
          have hne : (i : ℕ) + 1 ≠ (k : ℕ) := by omega
          simp [hne]
  · calc
      (∑ i : Fin N, ∑ j : Fin N, if (i : ℕ) + 1 = j then e i * a j else 0) =
          ∑ j : Fin N, if (k : ℕ) + 1 = j then a j else 0 := by
        rw [Finset.sum_eq_single k]
        · refine Finset.sum_congr rfl fun j _ ↦ ?_
          simp [he]
        · intro i _ hik
          exact Finset.sum_eq_zero fun j _ ↦ by simp [he, hik]
        · intro hk
          exact absurd (Finset.mem_univ k) hk
      _ = if h : (k : ℕ) + 1 < N then a ⟨(k : ℕ) + 1, h⟩ else 0 := by
        split_ifs with hk
        · rw [Finset.sum_eq_single (⟨(k : ℕ) + 1, hk⟩ : Fin N)]
          · simp
          · intro j _ hj
            have hne : (k : ℕ) + 1 ≠ (j : ℕ) := fun heq ↦ hj (Fin.ext heq.symm)
            simp [hne]
          · intro hmem
            exact absurd (Finset.mem_univ _) hmem
        · refine Finset.sum_eq_zero fun j _ ↦ ?_
          have hne : (k : ℕ) + 1 ≠ (j : ℕ) := by omega
          simp [hne]

/-- Adjacent standard basis vectors satisfy `B(e_j, e_{j + 1}) = 1`. -/
theorem chainForm_single_single_succ {N : ℕ} {j k : Fin N} (h : (j : ℕ) + 1 = k) :
    chainForm N (Pi.single j 1) (Pi.single k 1) = 1 := by
  rw [chainForm_single_right]
  have hk0 : 0 < (k : ℕ) := by omega
  have hprev : (⟨(k : ℕ) - 1, by omega⟩ : Fin N) = j := Fin.ext (by dsimp; omega)
  simp only [hk0, ↓reduceDIte, hprev, Pi.single_eq_same]
  split_ifs with hk1
  · have hne : (⟨(k : ℕ) + 1, hk1⟩ : Fin N) ≠ j := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp at hval
      omega
    simp [Pi.single_eq_of_ne hne]
  · simp

/-- Standard basis vectors at distance at least two are orthogonal for `chainForm`. -/
theorem chainForm_single_single_of_dist_ge_two {N : ℕ} {j k : Fin N}
    (h : (j : ℕ) + 2 ≤ k ∨ (k : ℕ) + 2 ≤ j) :
    chainForm N (Pi.single j 1) (Pi.single k 1) = 0 := by
  rw [chainForm_single_right]
  have h1 :
      (if h0 : 0 < (k : ℕ) then
          (Pi.single j (1 : ZMod 3) : Fin N → ZMod 3) ⟨(k : ℕ) - 1, by omega⟩
        else 0) = 0 := by
    split_ifs with h0
    · refine Pi.single_eq_of_ne (fun heq ↦ ?_) _
      have hval := congrArg Fin.val heq
      dsimp at hval
      omega
    · rfl
  have h2 :
      (if h1 : (k : ℕ) + 1 < N then
          (Pi.single j (1 : ZMod 3) : Fin N → ZMod 3) ⟨(k : ℕ) + 1, h1⟩
        else 0) = 0 := by
    split_ifs with hk1
    · refine Pi.single_eq_of_ne (fun heq ↦ ?_) _
      have hval := congrArg Fin.val heq
      dsimp at hval
      omega
    · rfl
  rw [h1, h2, sub_self]

/-- The factor set `α(a, b) = ω ^ (2 * B(a, b))` defining the cubic quantum torus `CubicTorus N`.
Since `2 - (-2) = 1` in `ZMod 3`, it satisfies `α(a, b) / α(b, a) = ω ^ (B(a, b))`. -/
noncomputable def cubicFactor (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) : ℂˣ :=
  cubeRootPow (2 * chainForm N a.toAdd b.toAdd)

/-- Unfolding `cubicFactor` as `cubeRootPow (2 * chainForm N a.toAdd b.toAdd)`. -/
theorem cubicFactor_def (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a b = cubeRootPow (2 * chainForm N a.toAdd b.toAdd) :=
  (rfl)

/-- `cubicFactor N` is a normalized factor set on `Multiplicative (Fin N → ZMod 3)`. -/
instance instIsFactorSetCubicFactor (N : ℕ) : IsFactorSet (cubicFactor N) where
  cocycle g h j := by
    simp only [cubicFactor_def, toAdd_mul, ← cubeRootPow_add]
    congr 1
    rw [chainForm_add_left, chainForm_add_right]
    ring
  one_left g := by
    simp [cubicFactor_def]

/-- `α(a, a) = 1`. -/
@[simp]
theorem cubicFactor_self (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a a = 1 := by
  simp [cubicFactor_def]

/-- `α(a, a⁻¹) = 1`. -/
@[simp]
theorem cubicFactor_inv_right (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a a⁻¹ = 1 := by
  simp [cubicFactor_def]

/-- `α(a⁻¹, a) = 1`. -/
@[simp]
theorem cubicFactor_inv_left (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a⁻¹ a = 1 := by
  simp [cubicFactor_def]

/-- Swapping arguments inverts `cubicFactor`: `α(b, a) = α(a, b)⁻¹`. -/
theorem cubicFactor_swap (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N b a = (cubicFactor N a b)⁻¹ := by
  rw [cubicFactor_def, cubicFactor_def, chainForm_swap, mul_neg, cubeRootPow_neg]

/-- `cubicFactor` is invariant under inverting both arguments: `α(a⁻¹, b⁻¹) = α(a, b)`. -/
theorem cubicFactor_inv_inv (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a⁻¹ b⁻¹ = cubicFactor N a b := by
  simp [cubicFactor_def]

/-- Inverting the first argument inverts `cubicFactor`: `α(a⁻¹, b) = α(a, b)⁻¹`. -/
@[simp]
theorem cubicFactor_inv_fst (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a⁻¹ b = (cubicFactor N a b)⁻¹ := by
  rw [cubicFactor_def, cubicFactor_def, toAdd_inv, chainForm_neg_left, mul_neg, cubeRootPow_neg]

/-- Inverting the second argument inverts `cubicFactor`: `α(a, b⁻¹) = α(a, b)⁻¹`. -/
@[simp]
theorem cubicFactor_inv_snd (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a b⁻¹ = (cubicFactor N a b)⁻¹ := by
  rw [cubicFactor_def, cubicFactor_def, toAdd_inv, chainForm_neg_right, mul_neg, cubeRootPow_neg]

/-- The commutator ratio of `cubicFactor` is `α(a, b) * α(b, a)⁻¹ = ω ^ (B(a, b))`. -/
theorem cubicFactor_mul_swap_inv (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a b * (cubicFactor N b a)⁻¹ =
      cubeRootPow (chainForm N a.toAdd b.toAdd) := by
  rw [cubicFactor_swap N a b, inv_inv, cubicFactor_def, ← cubeRootPow_add]
  congr 1
  have h4 : (2 : ZMod 3) + 2 = 1 := by decide
  rw [← add_mul, h4, one_mul]

/-- Complex conjugation reverses and inverts the arguments of `cubicFactor`. -/
@[simp]
theorem star_cubicFactor_val (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    star (cubicFactor N a b : ℂ) = (cubicFactor N b⁻¹ a⁻¹ : ℂ) := by
  rw [cubicFactor_inv_inv, cubicFactor_swap N a b, cubicFactor_def, star_cubeRootPow_val,
    cubeRootPow_neg]

/-! ### The cubic quantum torus, Weyl basis, and analytic adjoint -/

/-- The **cubic quantum torus** `G_N`, realized as the twisted monoid algebra
`twistedMonoidAlgebra ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)`. It has complex
dimension `3 ^ N` (`finrank_cubicTorus`). -/
def CubicTorus (N : ℕ) : Type :=
  twistedMonoidAlgebra ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)

/-- Ring structure on `CubicTorus N`, inherited from `twistedMonoidAlgebra`. -/
@[no_expose]
noncomputable instance instRingCubicTorus (N : ℕ) : Ring (CubicTorus N) :=
  inferInstanceAs
    (Ring (twistedMonoidAlgebra ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)))

/-- Complex algebra structure on `CubicTorus N`, inherited from `twistedMonoidAlgebra`. -/
@[no_expose]
noncomputable instance instAlgebraCubicTorus (N : ℕ) : Algebra ℂ (CubicTorus N) :=
  inferInstanceAs
    (Algebra ℂ (twistedMonoidAlgebra ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)))

/-- The canonical algebra equivalence identifying `CubicTorus N` with
`twistedMonoidAlgebra ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)`. -/
noncomputable def cubicTorusEquiv (N : ℕ) :
    CubicTorus N ≃ₐ[ℂ] twistedMonoidAlgebra ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N) :=
  AlgEquiv.refl

/-- The Weyl basis element `W(a)` of `CubicTorus N`, corresponding to
`TwistedMonoidAlgebra.of a`. -/
noncomputable def weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) : CubicTorus N :=
  (cubicTorusEquiv N).symm (TwistedMonoidAlgebra.of a)

/-- `cubicTorusEquiv` sends each Weyl element `W(a)` to `TwistedMonoidAlgebra.of a`. -/
@[simp]
theorem cubicTorusEquiv_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicTorusEquiv N (weyl N a) = TwistedMonoidAlgebra.of a :=
  (cubicTorusEquiv N).apply_symm_apply _

/-- The Weyl basis `{W(a)}` of `CubicTorus N` indexed by `Multiplicative (Fin N → ZMod 3)`. -/
noncomputable def cubicBasis (N : ℕ) :
    Module.Basis (Multiplicative (Fin N → ZMod 3)) ℂ (CubicTorus N) :=
  (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)).map
    (cubicTorusEquiv N).symm.toLinearEquiv

/-- Evaluating `cubicBasis N` at `a` gives `weyl N a`. -/
@[simp]
theorem cubicBasis_apply (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicBasis N a = weyl N a := by
  simp [cubicBasis, weyl]

/-- `CubicTorus N` is finite-dimensional over `ℂ`. -/
instance instFiniteDimensionalCubicTorus (N : ℕ) : Module.Finite ℂ (CubicTorus N) :=
  Module.Finite.of_basis (cubicBasis N)

/-- `CubicTorus N` is a free `ℂ`-module. -/
instance instFreeCubicTorus (N : ℕ) : Module.Free ℂ (CubicTorus N) :=
  Module.Free.of_basis (cubicBasis N)

/-- The identity Weyl basis element is `1`. -/
@[simp]
theorem weyl_one (N : ℕ) : weyl N 1 = 1 :=
  (cubicTorusEquiv N).injective (by simp)

/-- Multiplication table of the Weyl basis: `W(a) * W(b) = α(a, b) • W(a * b)`. -/
theorem weyl_mul (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    weyl N a * weyl N b = (cubicFactor N a b : ℂ) • weyl N (a * b) :=
  (cubicTorusEquiv N).injective (by simp)

/-- Universal property of `CubicTorus N`: a projective representation of
`Multiplicative (Fin N → ZMod 3)` with factor set `cubicFactor N` in a `ℂ`-algebra `A` extends to
a `ℂ`-algebra homomorphism `CubicTorus N →ₐ[ℂ] A`. -/
noncomputable def cubicTorusLift {N : ℕ} {A : Type*} [Semiring A] [Algebra ℂ A]
    (u : Multiplicative (Fin N → ZMod 3) → A) (hu₁ : u 1 = 1)
    (hu : ∀ g h, u g * u h = (cubicFactor N g h : ℂ) • u (g * h)) :
    CubicTorus N →ₐ[ℂ] A :=
  (TwistedMonoidAlgebra.lift u hu₁ hu).comp (cubicTorusEquiv N).toAlgHom

/-- Evaluating `cubicTorusLift` on a Weyl basis element `W(a)` returns `u a`. -/
@[simp]
theorem cubicTorusLift_weyl {N : ℕ} {A : Type*} [Semiring A] [Algebra ℂ A]
    (u : Multiplicative (Fin N → ZMod 3) → A) (hu₁ : u 1 = 1)
    (hu : ∀ g h, u g * u h = (cubicFactor N g h : ℂ) • u (g * h))
    (a : Multiplicative (Fin N → ZMod 3)) :
    cubicTorusLift u hu₁ hu (weyl N a) = u a := by
  simp [cubicTorusLift]

/-- Two `ℂ`-algebra homomorphisms out of `CubicTorus N` agree if they agree on every `weyl N a`.
-/
theorem cubicTorus_algHom_ext {N : ℕ} {A : Type*} [Semiring A] [Algebra ℂ A]
    {f g : CubicTorus N →ₐ[ℂ] A} (h : ∀ a, f (weyl N a) = g (weyl N a)) : f = g :=
  AlgHom.toLinearMap_injective <| (cubicBasis N).ext fun a ↦ by simpa using h a

/-- Weyl commutation law: `W(a) * W(b) = ω ^ (B(a, b)) • (W(b) * W(a))`. -/
theorem weyl_mul_comm (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    weyl N a * weyl N b =
      (cubeRootPow (chainForm N a.toAdd b.toAdd) : ℂ) • (weyl N b * weyl N a) := by
  rw [weyl_mul, weyl_mul, smul_smul, ← Units.val_mul, ← cubicFactor_mul_swap_inv, mul_assoc,
    inv_mul_cancel, mul_one, mul_comm a b]

/-- Each Weyl basis element has right inverse `W(a⁻¹)`. -/
@[simp]
theorem weyl_mul_inv (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a * weyl N a⁻¹ = 1 := by
  simp [weyl_mul]

/-- Each Weyl basis element has left inverse `W(a⁻¹)`. -/
@[simp]
theorem weyl_inv_mul (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a⁻¹ * weyl N a = 1 := by
  simp [weyl_mul]

/-- In `CubicTorus N`, squaring a Weyl basis element equals inverting its index: `W(a)² = W(a⁻¹)`.
-/
theorem weyl_sq (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a ^ 2 = weyl N a⁻¹ := by
  have ha : a * a = a⁻¹ := by
    apply Multiplicative.toAdd.injective
    ext i
    simp only [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply]
    have h3 : (3 : ZMod 3) = 0 := rfl
    have hsum : a.toAdd i + a.toAdd i + a.toAdd i = 0 := by
      calc
        a.toAdd i + a.toAdd i + a.toAdd i = (3 : ZMod 3) * a.toAdd i := by ring
        _ = 0 := by rw [h3, zero_mul]
    exact eq_neg_of_add_eq_zero_left hsum
  rw [sq, weyl_mul, cubicFactor_self, Units.val_one, one_smul, ha]

/-- Every Weyl basis element satisfies `W(a) ^ 3 = 1`. -/
@[simp]
theorem weyl_pow_three (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a ^ 3 = 1 := by
  rw [pow_succ, weyl_sq, weyl_inv_mul]

/-- The cubic quantum torus `CubicTorus N` has complex dimension `3 ^ N`. -/
@[simp]
theorem finrank_cubicTorus (N : ℕ) : Module.finrank ℂ (CubicTorus N) = 3 ^ N := by
  rw [(cubicTorusEquiv N).toLinearEquiv.finrank_eq, TwistedMonoidAlgebra.finrank_eq_natCard,
    Nat.card_eq_fintype_card]
  simp

section Star

open MulOpposite

/-- The conjugate-linear antimultiplicative involution `W(a) ↦ W(a⁻¹)` on `CubicTorus N`, bundled
as a ring homomorphism into `(CubicTorus N)ᵐᵒᵖ`. -/
private noncomputable def cubicStarHom (N : ℕ) : CubicTorus N →+* (CubicTorus N)ᵐᵒᵖ :=
  letI : Algebra ℂ (CubicTorus N)ᵐᵒᵖ := Algebra.compHom _ (starRingEnd ℂ)
  (cubicTorusLift (fun a ↦ op (weyl N a⁻¹)) (by simp) fun a b ↦
    unop_injective <| by
      simp only [unop_mul, unop_op, Algebra.smul_def, Algebra.compHom_algebraMap_apply,
        starRingEnd_apply, MulOpposite.algebraMap_apply, weyl_mul, mul_inv_rev,
        star_cubicFactor_val]
      rw [Algebra.commutes]).toRingHom

private theorem cubicStarHom_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicStarHom N (weyl N a) = op (weyl N a⁻¹) := by
  simp [cubicStarHom]

private theorem cubicStarHom_algebraMap (N : ℕ) (z : ℂ) :
    cubicStarHom N (algebraMap ℂ (CubicTorus N) z) =
      op (algebraMap ℂ (CubicTorus N) (star z)) := by
  unfold cubicStarHom
  exact @AlgHom.commutes _ _ _ _ _ _ _ (Algebra.compHom _ (starRingEnd ℂ)) _ z

private theorem cubicStarHom_involutive (N : ℕ) (x : CubicTorus N) :
    unop (cubicStarHom N (unop (cubicStarHom N x))) = x := by
  rw [← (cubicBasis N).sum_repr x]
  simp only [map_sum, Finset.unop_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [cubicBasis_apply, Algebra.smul_def, map_mul, cubicStarHom_algebraMap, cubicStarHom_weyl,
    unop_mul, unop_op, unop_op, map_mul, cubicStarHom_algebraMap, cubicStarHom_weyl, unop_mul,
    unop_op, unop_op, star_star, inv_inv, Algebra.commutes]

/-- The analytic adjoint on `CubicTorus N`: the conjugate-linear, product-reversing involution
sending each Weyl basis element `W(a)` to `W(a⁻¹)`. -/
@[no_expose]
noncomputable instance instStarRingCubicTorus (N : ℕ) : StarRing (CubicTorus N) where
  star x := unop (cubicStarHom N x)
  star_involutive := cubicStarHom_involutive N
  star_mul x y := by simp [map_mul]
  star_add x y := by simp [map_add]

/-- The analytic adjoint sends each Weyl basis element `W(a)` to `W(a⁻¹)`. -/
@[simp]
theorem star_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    star (weyl N a) = weyl N a⁻¹ :=
  congrArg unop (cubicStarHom_weyl N a)

private theorem star_algebraMap_cubicTorus (N : ℕ) (z : ℂ) :
    star (algebraMap ℂ (CubicTorus N) z) = algebraMap ℂ (CubicTorus N) (star z) :=
  congrArg unop (cubicStarHom_algebraMap N z)

/-- The analytic adjoint on `CubicTorus N` is conjugate-linear. -/
noncomputable instance instStarModuleCubicTorus (N : ℕ) : StarModule ℂ (CubicTorus N) where
  star_smul z x := by
    simp [Algebra.smul_def, star_mul, star_algebraMap_cubicTorus, Algebra.commutes]

end Star

/-! ### The scalar trace, Parseval positivity, and faithfulness -/

/-- The normalized scalar trace `s_N : CubicTorus N →ₗ[ℂ] ℂ`, extracting the `1`-coordinate in
the Weyl basis `cubicBasis N`. -/
noncomputable def cubicScalarCoefficient (N : ℕ) : CubicTorus N →ₗ[ℂ] ℂ :=
  (Finsupp.lapply (1 : Multiplicative (Fin N → ZMod 3))).comp (cubicBasis N).repr.toLinearMap

/-- Evaluation of `cubicScalarCoefficient N` as the `1`-coordinate in `cubicBasis N`. -/
theorem cubicScalarCoefficient_apply (N : ℕ) (x : CubicTorus N) :
    cubicScalarCoefficient N x = (cubicBasis N).repr x 1 :=
  (rfl)

/-- On a Weyl basis element `W(a)`, `s_N(W(a))` is `1` if `a = 1` and `0` otherwise. -/
@[simp]
theorem cubicScalarCoefficient_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicScalarCoefficient N (weyl N a) = if a = 1 then 1 else 0 := by
  rw [cubicScalarCoefficient_apply, ← cubicBasis_apply, Module.Basis.repr_self,
    Finsupp.single_apply]

/-- `cubicScalarCoefficient N` is normalized: `s_N(1) = 1`. -/
@[simp]
theorem cubicScalarCoefficient_one (N : ℕ) : cubicScalarCoefficient N 1 = 1 := by
  simp [← weyl_one]

/-- On a product of Weyl basis elements, `s_N(W(a) * W(b))` is `1` when `a * b = 1` and `0`
otherwise. -/
theorem cubicScalarCoefficient_weyl_mul (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicScalarCoefficient N (weyl N a * weyl N b) = if a * b = 1 then 1 else 0 := by
  rw [weyl_mul, map_smul, cubicScalarCoefficient_weyl, smul_eq_mul]
  split_ifs with h
  · have hb : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    subst hb
    simp
  · simp

/-- `cubicScalarCoefficient N` is tracial: `s_N(x * y) = s_N(y * x)`. -/
theorem cubicScalarCoefficient_mul_comm (N : ℕ) (x y : CubicTorus N) :
    cubicScalarCoefficient N (x * y) = cubicScalarCoefficient N (y * x) := by
  have hbilin :
      (LinearMap.mul ℂ (CubicTorus N)).compr₂ (cubicScalarCoefficient N) =
        ((LinearMap.mul ℂ (CubicTorus N)).compr₂ (cubicScalarCoefficient N)).flip := by
    refine (cubicBasis N).ext fun g ↦ (cubicBasis N).ext fun h ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.flip_apply,
      cubicBasis_apply, cubicScalarCoefficient_weyl_mul, mul_comm g h]
  exact LinearMap.congr_fun₂ hbilin x y

/-- `cubicScalarCoefficient N` preserves `star`. -/
@[simp]
theorem cubicScalarCoefficient_star (N : ℕ) (x : CubicTorus N) :
    cubicScalarCoefficient N (star x) = star (cubicScalarCoefficient N x) := by
  conv_lhs => rw [← (cubicBasis N).sum_repr x]
  conv_rhs => rw [← (cubicBasis N).sum_repr x]
  simp only [star_sum, map_sum, star_smul, map_smul, smul_eq_mul, cubicBasis_apply, star_weyl,
    cubicScalarCoefficient_weyl, inv_eq_one]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  split_ifs <;> simp

/-- **Sesquilinear Parseval identity** for `cubicScalarCoefficient N`:
`s_N (star x * y) = ∑_a conj (x_a) * y_a`. -/
theorem cubicScalarCoefficient_star_mul (N : ℕ) (x y : CubicTorus N) :
    cubicScalarCoefficient N (star x * y) =
      ∑ a : Multiplicative (Fin N → ZMod 3),
        star ((cubicBasis N).repr x a) * (cubicBasis N).repr y a := by
  conv_lhs => rw [← (cubicBasis N).sum_repr x, ← (cubicBasis N).sum_repr y]
  rw [star_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.mul_sum, map_sum, Finset.sum_eq_single a]
  · rw [cubicBasis_apply, star_smul, star_weyl, smul_mul_smul_comm, map_smul,
      weyl_inv_mul, cubicScalarCoefficient_one, smul_eq_mul, mul_one]
  · intro c _ hca
    have hne : a⁻¹ * c ≠ 1 := fun h ↦ hca (by simpa [mul_assoc] using congrArg (a * ·) h)
    rw [cubicBasis_apply, cubicBasis_apply, star_smul, star_weyl, smul_mul_smul_comm, map_smul,
      cubicScalarCoefficient_weyl_mul, ite_eq_right_iff.mpr fun h ↦ absurd h hne, smul_zero]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

/-- **Quadratic Parseval identity** for `cubicScalarCoefficient N`:
`s_N (star x * x) = ∑_a |x_a|²`. -/
theorem cubicScalarCoefficient_star_mul_self (N : ℕ) (x : CubicTorus N) :
    cubicScalarCoefficient N (star x * x) =
      ((∑ a : Multiplicative (Fin N → ZMod 3),
          Complex.normSq ((cubicBasis N).repr x a) : ℝ) : ℂ) := by
  rw [cubicScalarCoefficient_star_mul, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]

/-- Positivity of the scalar trace on `CubicTorus N`: `0 ≤ s_N (star x * x)`. -/
theorem cubicScalarCoefficient_star_mul_self_nonneg (N : ℕ) (x : CubicTorus N) :
    0 ≤ cubicScalarCoefficient N (star x * x) := by
  rw [cubicScalarCoefficient_star_mul_self, Complex.zero_le_real]
  exact Finset.sum_nonneg fun a _ ↦ Complex.normSq_nonneg _

/-- Faithfulness of the scalar trace on `CubicTorus N`: `s_N (star x * x) = 0 ↔ x = 0`. -/
@[simp]
theorem cubicScalarCoefficient_star_mul_self_eq_zero_iff (N : ℕ) {x : CubicTorus N} :
    cubicScalarCoefficient N (star x * x) = 0 ↔ x = 0 := by
  rw [cubicScalarCoefficient_star_mul_self, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun a _ ↦ Complex.normSq_nonneg _]
  constructor
  · intro h
    rw [← (cubicBasis N).sum_repr x]
    exact Finset.sum_eq_zero fun a _ ↦ by
      rw [Complex.normSq_eq_zero.mp (h a (Finset.mem_univ a)), zero_smul]
  · rintro rfl a _
    simp

/-- The scalar trace `cubicScalarCoefficient N` bundled as a `StarPositiveFunctional`. -/
noncomputable def cubicScalarFunctional (N : ℕ) : StarPositiveFunctional (CubicTorus N) where
  toLinearMap := cubicScalarCoefficient N
  square_nonneg := cubicScalarCoefficient_star_mul_self_nonneg N

/-- Evaluation of `cubicScalarFunctional N` is `cubicScalarCoefficient N`. -/
@[simp]
theorem cubicScalarFunctional_apply (N : ℕ) (x : CubicTorus N) :
    cubicScalarFunctional N x = cubicScalarCoefficient N x :=
  (rfl)

/-- The GNS null space of `cubicScalarFunctional N` is trivial. -/
theorem nullSubmodule_cubicScalarFunctional (N : ℕ) :
    (cubicScalarFunctional N).nullSubmodule = ⊥ := by
  ext x
  simp [StarPositiveFunctional.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero]

/-! ### The inversion involution and its fixed subalgebra `cubicFixed N` -/

private noncomputable def cubicInversionAlgHom (N : ℕ) : CubicTorus N →ₐ[ℂ] CubicTorus N :=
  cubicTorusLift (fun a ↦ weyl N a⁻¹) (by simp) fun g h ↦ by
    rw [weyl_mul, cubicFactor_inv_inv, mul_inv]

/-- The **inversion automorphism** `θ_N : W(a) ↦ W(a⁻¹)` of `CubicTorus N`, as a star-algebra
endomorphism. -/
noncomputable def cubicInversion (N : ℕ) : CubicTorus N →⋆ₐ[ℂ] CubicTorus N :=
  { cubicInversionAlgHom N with
    map_star' := fun x ↦ by
      rw [← (cubicBasis N).sum_repr x]
      simp [cubicInversionAlgHom] }

/-- `cubicInversion N` acts on Weyl basis elements by inverting the index: `θ_N(W(a)) = W(a⁻¹)`.
-/
@[simp]
theorem cubicInversion_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicInversion N (weyl N a) = weyl N a⁻¹ := by
  simp [cubicInversion, cubicInversionAlgHom]

/-- `cubicInversion N` is an involution: `θ_N (θ_N x) = x`. -/
@[simp]
theorem cubicInversion_involutive (N : ℕ) (x : CubicTorus N) :
    cubicInversion N (cubicInversion N x) = x := by
  have hcomp :
      (cubicInversion N).toAlgHom.comp (cubicInversion N).toAlgHom =
        AlgHom.id ℂ (CubicTorus N) :=
    cubicTorus_algHom_ext fun a ↦ by simp
  exact AlgHom.congr_fun hcomp x

/-- `cubicInversion N` preserves the scalar trace `cubicScalarCoefficient N`. -/
@[simp]
theorem cubicScalarCoefficient_cubicInversion (N : ℕ) (x : CubicTorus N) :
    cubicScalarCoefficient N (cubicInversion N x) = cubicScalarCoefficient N x := by
  conv_lhs => rw [← (cubicBasis N).sum_repr x]
  conv_rhs => rw [← (cubicBasis N).sum_repr x]
  simp only [map_sum, map_smul, smul_eq_mul, cubicBasis_apply, cubicInversion_weyl,
    cubicScalarCoefficient_weyl, inv_eq_one]

/-- The **inversion-fixed star-subalgebra** `C_N = {x ∈ G_N : θ_N x = x}` of `CubicTorus N`. -/
noncomputable def cubicFixed (N : ℕ) : StarSubalgebra ℂ (CubicTorus N) :=
  StarAlgHom.equalizer (cubicInversion N) (StarAlgHom.id ℂ (CubicTorus N))

/-- Membership in `cubicFixed N` is characterized by `θ_N x = x`. -/
@[simp]
theorem mem_cubicFixed (N : ℕ) {x : CubicTorus N} :
    x ∈ cubicFixed N ↔ cubicInversion N x = x :=
  Iff.rfl

private theorem eq_zero_of_two_mul_eq_zero_zmod3 {x : ZMod 3} (h : (2 : ZMod 3) * x = 0) :
    x = 0 := by
  revert x h
  decide

/-- The trace of the inversion operator `θ_N` on `CubicTorus N` is `1`, because `1` is the unique
element of `Multiplicative (Fin N → ZMod 3)` equal to its own inverse. -/
theorem trace_cubicInversion (N : ℕ) :
    _root_.LinearMap.trace ℂ (CubicTorus N) (cubicInversion N).toAlgHom.toLinearMap = 1 := by
  rw [_root_.LinearMap.trace_eq_matrix_trace ℂ (cubicBasis N), Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply,
    StarAlgHom.coe_toAlgHom, cubicBasis_apply, cubicInversion_weyl]
  rw [Finset.sum_eq_single (1 : Multiplicative (Fin N → ZMod 3))]
  · rw [inv_one, ← cubicBasis_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  · intro a _ ha
    have hne : a⁻¹ ≠ a := by
      intro heq
      apply ha
      apply Multiplicative.toAdd.injective
      ext i
      have hi : -(a.toAdd i) = a.toAdd i := by
        simpa [toAdd_inv] using congrFun (congrArg Multiplicative.toAdd heq) i
      apply eq_zero_of_two_mul_eq_zero_zmod3
      calc
        (2 : ZMod 3) * a.toAdd i = a.toAdd i + a.toAdd i := by ring
        _ = -a.toAdd i + a.toAdd i := by rw [hi]
        _ = 0 := neg_add_cancel _
    rw [← cubicBasis_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne hne.symm]
  · intro h1
    exact absurd (Finset.mem_univ _) h1

/-- The complex dimension of the inversion-fixed subalgebra `cubicFixed N` is `(3 ^ N + 1) / 2`. -/
@[simp]
theorem finrank_cubicFixed (N : ℕ) :
    Module.finrank ℂ (cubicFixed N) = (3 ^ N + 1) / 2 := by
  let θ : Module.End ℂ (CubicTorus N) := (cubicInversion N).toAlgHom.toLinearMap
  have hsq : (-θ) ^ 2 = 1 := by
    ext x
    simp [θ, sq]
  have hker :
      _root_.LinearMap.ker (1 + (-θ)) = (cubicFixed N).toSubalgebra.toSubmodule := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.add_apply, one_apply_eq_self, LinearMap.neg_apply,
      Subalgebra.mem_toSubmodule, StarSubalgebra.mem_toSubalgebra, mem_cubicFixed, θ,
      AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom]
    rw [← sub_eq_add_neg, sub_eq_zero, eq_comm]
  have hdim := TauCeti.LinearMap.two_mul_finrank_ker_one_add_of_sq_eq_one hsq
  rw [hker, map_neg, sub_neg_eq_add, trace_cubicInversion, finrank_cubicTorus] at hdim
  have hfin :
      Module.finrank ℂ (cubicFixed N).toSubalgebra.toSubmodule =
        Module.finrank ℂ (cubicFixed N) :=
    rfl
  rw [hfin] at hdim
  have hnat : 2 * Module.finrank ℂ (cubicFixed N) = 3 ^ N + 1 := by
    have hcast :
        ((2 * Module.finrank ℂ (cubicFixed N) : ℕ) : ℂ) = ((3 ^ N + 1 : ℕ) : ℂ) := by
      push_cast
      simpa using hdim
    exact Nat.cast_injective hcast
  omega

/-! ### Site unitaries, Temperley–Lieb projections, and the homomorphism `cubicFixedHom` -/

/-- The `j`-th site unitary `U_j = W(e_j)` of `CubicTorus N`. -/
noncomputable def cubicSite (N : ℕ) (j : Fin N) : CubicTorus N :=
  weyl N (Multiplicative.ofAdd (Pi.single j 1))

/-- Unfolding `cubicSite` as `weyl N (Multiplicative.ofAdd (Pi.single j 1))`. -/
theorem cubicSite_def (N : ℕ) (j : Fin N) :
    cubicSite N j = weyl N (Multiplicative.ofAdd (Pi.single j 1)) :=
  (rfl)

/-- Every site unitary has order dividing `3`: `U_j ^ 3 = 1`. -/
@[simp]
theorem cubicSite_pow_three (N : ℕ) (j : Fin N) : cubicSite N j ^ 3 = 1 :=
  weyl_pow_three N _

/-- The adjoint of a site unitary is its square: `star U_j = U_j ^ 2`. -/
@[simp]
theorem star_cubicSite (N : ℕ) (j : Fin N) : star (cubicSite N j) = cubicSite N j ^ 2 := by
  rw [cubicSite_def, star_weyl, ← weyl_sq]

/-- Inversion sends each site unitary to its square: `θ_N(U_j) = U_j ^ 2`. -/
@[simp]
theorem cubicInversion_cubicSite (N : ℕ) (j : Fin N) :
    cubicInversion N (cubicSite N j) = cubicSite N j ^ 2 := by
  rw [cubicSite_def, cubicInversion_weyl, ← weyl_sq]

/-- Adjacent site unitaries satisfy `U_j * U_{j + 1} = ω • (U_{j + 1} * U_j)`. -/
theorem cubicSite_mul_comm_succ {N : ℕ} {j k : Fin N} (h : (j : ℕ) + 1 = k) :
    cubicSite N j * cubicSite N k = (cubeRootOfUnity : ℂ) • (cubicSite N k * cubicSite N j) := by
  rw [cubicSite_def, cubicSite_def, weyl_mul_comm, toAdd_ofAdd, toAdd_ofAdd,
    chainForm_single_single_succ h, cubeRootPow_one]

/-- Adjacent site unitaries in reverse order satisfy `U_{k + 1} * U_k = ω⁻¹ • (U_k * U_{k + 1})`.
-/
theorem cubicSite_mul_comm_pred {N : ℕ} {j k : Fin N} (h : (k : ℕ) + 1 = j) :
    cubicSite N j * cubicSite N k =
      ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ) • (cubicSite N k * cubicSite N j) := by
  rw [cubicSite_def, cubicSite_def, weyl_mul_comm, toAdd_ofAdd, toAdd_ofAdd, chainForm_swap,
    chainForm_single_single_succ h, cubeRootPow_neg, cubeRootPow_one]

/-- Site unitaries at distance at least two commute. -/
theorem commute_cubicSite_of_dist_ge_two {N : ℕ} {j k : Fin N}
    (h : (j : ℕ) + 2 ≤ k ∨ (k : ℕ) + 2 ≤ j) :
    Commute (cubicSite N j) (cubicSite N k) := by
  rw [Commute, SemiconjBy, cubicSite_def, cubicSite_def, weyl_mul_comm, toAdd_ofAdd, toAdd_ofAdd,
    chainForm_single_single_of_dist_ge_two h, cubeRootPow_zero, Units.val_one, one_smul]

/-- The `j`-th Temperley–Lieb projection `p_j = 3⁻¹ • (1 + U_j + U_j ^ 2)` in `CubicTorus N`. -/
noncomputable def cubicProjection (N : ℕ) (j : Fin N) : CubicTorus N :=
  (3 : ℂ)⁻¹ • (1 + cubicSite N j + cubicSite N j ^ 2)

/-- Unfolding `cubicProjection` as `3⁻¹ • (1 + U_j + U_j ^ 2)`. -/
theorem cubicProjection_def (N : ℕ) (j : Fin N) :
    cubicProjection N j = (3 : ℂ)⁻¹ • (1 + cubicSite N j + cubicSite N j ^ 2) :=
  (rfl)

/-- Every `cubicProjection N j` is self-adjoint. -/
@[simp]
theorem star_cubicProjection (N : ℕ) (j : Fin N) :
    star (cubicProjection N j) = cubicProjection N j := by
  rw [cubicProjection_def, star_smul, star_add, star_add, star_one, star_pow, star_cubicSite]
  have hpow : (cubicSite N j ^ 2) ^ 2 = cubicSite N j := by
    calc
      (cubicSite N j ^ 2) ^ 2 = cubicSite N j ^ 3 * cubicSite N j := by noncomm_ring
      _ = cubicSite N j := by rw [cubicSite_pow_three, one_mul]
  rw [hpow, show star ((3 : ℂ)⁻¹) = (3 : ℂ)⁻¹ by simp]
  congr 1
  abel

/-- Every `cubicProjection N j` lies in the inversion-fixed subalgebra `cubicFixed N`. -/
theorem cubicProjection_mem_cubicFixed (N : ℕ) (j : Fin N) :
    cubicProjection N j ∈ cubicFixed N := by
  rw [mem_cubicFixed, cubicProjection_def, map_smul, map_add, map_add, map_one, map_pow,
    cubicInversion_cubicSite]
  have hpow : (cubicSite N j ^ 2) ^ 2 = cubicSite N j := by
    calc
      (cubicSite N j ^ 2) ^ 2 = cubicSite N j ^ 3 * cubicSite N j := by noncomm_ring
      _ = cubicSite N j := by rw [cubicSite_pow_three, one_mul]
  rw [hpow]
  congr 1
  abel

/-- Right multiplication by `U_j` fixes `p_j`. -/
@[simp]
theorem cubicProjection_mul_cubicSite (N : ℕ) (j : Fin N) :
    cubicProjection N j * cubicSite N j = cubicProjection N j := by
  rw [cubicProjection_def, smul_mul_assoc]
  congr 1
  have h3 := cubicSite_pow_three N j
  linear_combination (norm := noncomm_ring) h3

/-- Left multiplication by `U_j` fixes `p_j`. -/
@[simp]
theorem cubicSite_mul_cubicProjection (N : ℕ) (j : Fin N) :
    cubicSite N j * cubicProjection N j = cubicProjection N j := by
  rw [cubicProjection_def, mul_smul_comm]
  congr 1
  have h3 := cubicSite_pow_three N j
  linear_combination (norm := noncomm_ring) h3

/-- Every `cubicProjection N j` is idempotent: `p_j * p_j = p_j`. -/
@[simp]
theorem cubicProjection_mul_self (N : ℕ) (j : Fin N) :
    cubicProjection N j * cubicProjection N j = cubicProjection N j := by
  calc
    cubicProjection N j * cubicProjection N j =
        (3 : ℂ)⁻¹ •
          (cubicProjection N j * 1 + cubicProjection N j * cubicSite N j +
            cubicProjection N j * cubicSite N j * cubicSite N j) := by
      nth_rw 2 [cubicProjection_def]
      rw [mul_smul_comm, mul_add, mul_add, sq, mul_assoc]
    _ = (3 : ℂ)⁻¹ • ((3 : ℂ) • cubicProjection N j) := by
      simp only [mul_one, cubicProjection_mul_cubicSite]
      congr 1
      module
    _ = cubicProjection N j := by
      rw [smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]

/-- For adjacent sites `j` and `k`, `p_j * U_k * p_j = 0`. -/
private theorem cubicProjection_mul_cubicSite_mul_cubicProjection_of_adj {N : ℕ} {j k : Fin N}
    (h : (j : ℕ) + 1 = k ∨ (k : ℕ) + 1 = j) :
    cubicProjection N j * cubicSite N k * cubicProjection N j = 0 := by
  -- Commuting `U_j` past `U_k` multiplies by a primitive cube root `ζ ∈ {ω, ω⁻¹}`,
  -- whose cyclotomic sum `1 + ζ + ζ²` vanishes.
  have hcomm :
      ∃ ζ : ℂ, (1 + ζ + ζ ^ 2 = 0) ∧
        cubicSite N k * cubicSite N j = ζ • (cubicSite N j * cubicSite N k) := by
    rcases h with hjk | hkj
    · refine ⟨((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ), ?_, cubicSite_mul_comm_pred hjk⟩
      rw [cubeRootOfUnity_inv_eq_sq, Units.val_pow_eq_pow_val]
      linear_combination (cubeRootOfUnity : ℂ) * cubeRootOfUnity_val_pow_three +
        one_add_cubeRootOfUnity_add_sq
    · exact ⟨(cubeRootOfUnity : ℂ), one_add_cubeRootOfUnity_add_sq,
        cubicSite_mul_comm_succ hkj⟩
  obtain ⟨ζ, hζ, hUkUj⟩ := hcomm
  have hUkUj2 :
      cubicSite N k * cubicSite N j ^ 2 =
        (ζ ^ 2) • (cubicSite N j ^ 2 * cubicSite N k) := by
    calc
      cubicSite N k * cubicSite N j ^ 2 = (cubicSite N k * cubicSite N j) * cubicSite N j := by
        rw [sq, ← mul_assoc]
      _ = ζ • (cubicSite N j * (cubicSite N k * cubicSite N j)) := by
        nth_rw 1 [hUkUj]
        rw [smul_mul_assoc, mul_assoc]
      _ = (ζ ^ 2) • (cubicSite N j ^ 2 * cubicSite N k) := by
        rw [hUkUj, mul_smul_comm, smul_smul, ← sq, ← mul_assoc, ← sq]
  have hstep :
      cubicProjection N j * cubicSite N k * (1 + cubicSite N j + cubicSite N j ^ 2) =
        (1 + ζ + ζ ^ 2) • (cubicProjection N j * cubicSite N k) := by
    have h1 :
        cubicProjection N j * (cubicSite N k * cubicSite N j) =
          ζ • (cubicProjection N j * cubicSite N k) := by
      rw [hUkUj, mul_smul_comm, ← mul_assoc, cubicProjection_mul_cubicSite]
    have h2 :
        cubicProjection N j * (cubicSite N k * cubicSite N j ^ 2) =
          (ζ ^ 2) • (cubicProjection N j * cubicSite N k) := by
      rw [hUkUj2, mul_smul_comm, ← mul_assoc, sq (cubicSite N j), ← mul_assoc,
        cubicProjection_mul_cubicSite, cubicProjection_mul_cubicSite]
    rw [mul_add, mul_add, mul_one, mul_assoc, mul_assoc, h1, h2]
    module
  calc
    cubicProjection N j * cubicSite N k * cubicProjection N j =
        (3 : ℂ)⁻¹ •
          (cubicProjection N j * cubicSite N k * (1 + cubicSite N j + cubicSite N j ^ 2)) := by
      nth_rw 2 [cubicProjection_def]
      rw [mul_smul_comm]
    _ = 0 := by rw [hstep, hζ, zero_smul, smul_zero]

/-- For adjacent sites `j` and `k`, `p_j * U_k ^ 2 * p_j = 0`. -/
private theorem cubicProjection_mul_cubicSite_sq_mul_cubicProjection_of_adj {N : ℕ} {j k : Fin N}
    (h : (j : ℕ) + 1 = k ∨ (k : ℕ) + 1 = j) :
    cubicProjection N j * cubicSite N k ^ 2 * cubicProjection N j = 0 := by
  have hstar := congrArg star (cubicProjection_mul_cubicSite_mul_cubicProjection_of_adj h)
  simpa [star_mul, mul_assoc] using hstar

/-- **Temperley–Lieb Jones relation at `δ² = 3`**: for adjacent sites `|j - k| = 1`,
`p_j * p_k * p_j = 3⁻¹ • p_j`. -/
theorem cubicProjection_mul_cubicProjection_mul_of_adj {N : ℕ} {j k : Fin N}
    (h : (j : ℕ) + 1 = k ∨ (k : ℕ) + 1 = j) :
    cubicProjection N j * cubicProjection N k * cubicProjection N j =
      (3 : ℂ)⁻¹ • cubicProjection N j := by
  rw [cubicProjection_def N k, mul_smul_comm, smul_mul_assoc, mul_add, mul_add, add_mul, add_mul,
    mul_one, cubicProjection_mul_self,
    cubicProjection_mul_cubicSite_mul_cubicProjection_of_adj h,
    cubicProjection_mul_cubicSite_sq_mul_cubicProjection_of_adj h, add_zero, add_zero]

/-- Projections at distance at least two commute. -/
theorem commute_cubicProjection_of_dist_ge_two {N : ℕ} {j k : Fin N}
    (h : (j : ℕ) + 2 ≤ k ∨ (k : ℕ) + 2 ≤ j) :
    Commute (cubicProjection N j) (cubicProjection N k) := by
  have hU := commute_cubicSite_of_dist_ge_two h
  rw [Commute, SemiconjBy, cubicProjection_def, cubicProjection_def, smul_mul_smul_comm,
    smul_mul_smul_comm]
  congr 1
  have h1 : cubicSite N j * cubicSite N k = cubicSite N k * cubicSite N j := hU.eq
  have h2 : cubicSite N j * cubicSite N k ^ 2 = cubicSite N k ^ 2 * cubicSite N j :=
    (hU.pow_right 2).eq
  have h3 : cubicSite N j ^ 2 * cubicSite N k = cubicSite N k * cubicSite N j ^ 2 :=
    (hU.pow_left 2).eq
  have h4 : cubicSite N j ^ 2 * cubicSite N k ^ 2 = cubicSite N k ^ 2 * cubicSite N j ^ 2 :=
    ((hU.pow_left 2).pow_right 2).eq
  linear_combination (norm := noncomm_ring) h1 + h2 + h3 + h4

private noncomputable def cubicFixedAlgHom (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1) :=
  TemperleyLieb.lift
    (fun j ↦
      ⟨(Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j,
        (cubicFixed (m - 1)).smul_mem (cubicProjection_mem_cubicFixed (m - 1) j) _⟩)
    (fun j ↦ Subtype.ext <| by
      simp only [MulMemClass.coe_mul, SetLike.val_smul, smul_mul_smul_comm,
        cubicProjection_mul_self, smul_smul])
    (fun {i j} hij ↦ Subtype.ext <| by
      simp only [MulMemClass.coe_mul, mul_smul_comm, smul_mul_assoc,
        cubicProjection_mul_cubicProjection_mul_of_adj hij, smul_smul]
      congr 1
      rw [sqrt_three_coe_mul_self]
      norm_num)
    (fun {i j} hij ↦ Subtype.ext <| by
      simp only [MulMemClass.coe_mul, smul_mul_smul_comm]
      rw [(commute_cubicProjection_of_dist_ge_two hij).eq])

/-- The star-algebra homomorphism
`F_m : TemperleyLieb ℂ (√3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1)` sending each generator `e j` to
`(√3 : ℂ) • cubicProjection (m - 1) j`. -/
noncomputable def cubicFixedHom (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1) :=
  { cubicFixedAlgHom m with
    map_star' :=
      TemperleyLieb.map_star_iff.mpr fun j ↦ by
        rw [IsSelfAdjoint]
        apply Subtype.ext
        simp [cubicFixedAlgHom] }

/-- Coercing `cubicFixedHom m (e j)` to `CubicTorus (m - 1)` gives `(√3 : ℂ) • p_j`. -/
@[simp]
theorem coe_cubicFixedHom_e (m : ℕ) (j : Fin (m - 1)) :
    (cubicFixedHom m (e (Real.sqrt 3 : ℂ) j) : CubicTorus (m - 1)) =
      (Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j := by
  simp [cubicFixedHom, cubicFixedAlgHom]

end TauCeti.TemperleyLieb
