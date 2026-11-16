/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Data.ZMod.Defs
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic
-- Private: `ZMod` cardinality and `Finrank` transport on finite function spaces are used only
-- inside proofs.
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The cubic quantum torus and its inversion-fixed subalgebra

For each `N : ℕ`, let `chainForm N` be the alternating biadditive form
`B(a, b) = ∑_{j < N - 1} (a j * b (j + 1) - b j * a (j + 1))` on `Fin N → ZMod 3`, let
`ω = cubeRootOfUnity = exp (2 * π / 3 * I)`, and form the normalized factor set
`cubicFactor N a b = ω ^ (2 * B(a, b))` on `Multiplicative (Fin N → ZMod 3)`. The **cubic quantum
torus** `CubicTorus N` is the twisted monoid algebra `twistedMonoidAlgebra ℂ _ (cubicFactor N)` of
complex dimension `3 ^ N`, with Weyl basis `weyl N a` satisfying
`weyl N a * weyl N b = cubicFactor N a b • weyl N (a * b)`.

* **Scalar trace and analytic adjoint**: `cubicScalarCoefficient N` extracts the coefficient of
  `weyl N 1 = 1` in the Weyl basis and defines a normalized trace. The conjugate-linear map
  `cubicAdjoint N` sends `∑ z_a W(a)` to `∑ conj z_a W(a⁻¹)`; it is an anti-multiplicative
  involution satisfying the Parseval identity
  `cubicScalarCoefficient N (cubicAdjoint N x * x) = ∑_a ‖x_a‖² ≥ 0`, vanishing only at `x = 0`.
* **Inversion-fixed subalgebra**: exponent negation defines an involutive `ℂ`-algebra automorphism
  `cubicInversion N` commuting with `cubicAdjoint N`, whose fixed subalgebra
  `cubicFixed N = AlgHom.equalizer (cubicInversion N) (AlgHom.id ℂ _)` has complex dimension
  `(3 ^ N + 1) / 2` and nondegenerate trace pairing.

The comparison homomorphism `TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)` is constructed in
`TauCeti.Algebra.TemperleyLieb.CubicTorus.Hom`, and the Markov-trace and Jones-quotient
identifications at `δ = √3` are established in
`TauCeti.Algebra.TemperleyLieb.CubicTorus.Quotient`.

## Main definitions

* `TauCeti.TemperleyLieb.cubeRootOfUnity`, `TauCeti.TemperleyLieb.cubeRootPow`: the primitive cube
  root of unity `ω = exp (2 * π / 3 * I)` and its `ZMod 3`-indexed powers.
* `TauCeti.TemperleyLieb.chainForm`, `TauCeti.TemperleyLieb.cubicFactor`: the alternating chain
  form on `Fin N → ZMod 3` and the associated normalized factor set.
* `TauCeti.TemperleyLieb.CubicTorus`, `TauCeti.TemperleyLieb.weyl`: the cubic quantum torus and
  its Weyl basis elements.
* `TauCeti.TemperleyLieb.cubicScalarCoefficient`: the normalized scalar-part trace.
* `TauCeti.TemperleyLieb.cubicAdjoint`, `TauCeti.TemperleyLieb.cubicFixedAdjoint`: the
  conjugate-linear analytic adjoint on `CubicTorus N` and its restriction to `cubicFixed N`.
* `TauCeti.TemperleyLieb.cubicInversion`, `TauCeti.TemperleyLieb.cubicFixed`: the exponent
  inversion automorphism and its fixed subalgebra.

## Main results

* `TauCeti.TemperleyLieb.cubicFactor_isFactorSet`: `cubicFactor N` is a normalized factor set.
* `TauCeti.TemperleyLieb.finrank_cubicTorus`, `TauCeti.TemperleyLieb.finrank_cubicFixed`:
  `finrank ℂ (CubicTorus N) = 3 ^ N` and `finrank ℂ (cubicFixed N) = (3 ^ N + 1) / 2`.
* `TauCeti.TemperleyLieb.cubicScalarCoefficient_cubicAdjoint_mul`,
  `TauCeti.TemperleyLieb.cubicScalarCoefficient_cubicAdjoint_mul_self_nonneg`,
  `TauCeti.TemperleyLieb.cubicScalarCoefficient_cubicAdjoint_mul_self_eq_zero_iff`, and
  `TauCeti.TemperleyLieb.forall_cubicFixed_scalarCoefficient_mul_eq_zero_iff`: Parseval identity,
  positivity, faithfulness, and trace-pairing nondegeneracy on `cubicFixed N`.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111, p. 107.
* C. Galindo and E. C. Rowell, *Braid representations from unitary braided vector spaces*,
  J. Math. Phys. 55 (2014), 061702.
* E. C. Rowell and H. Wenzl, *SO(N)_2 braid group representations are Gaussian*, Quantum Topology
  8 (2017), 1–33.
-/

public section

open scoped ComplexConjugate ComplexOrder

namespace TauCeti.TemperleyLieb

/-! ### Arithmetic helpers for `ω = exp (2 * π / 3 * I)` -/

/-- The primitive cube root of unity `ω = exp (2 * π / 3 * I)` as a unit of `ℂ`. -/
noncomputable def cubeRootOfUnity : ℂˣ :=
  Units.mk0 (Complex.exp (2 * Real.pi / 3 * Complex.I)) (Complex.exp_ne_zero _)

/-- Coercing `cubeRootOfUnity` to `ℂ` gives `exp (2 * π / 3 * I)`. -/
theorem coe_cubeRootOfUnity :
    (cubeRootOfUnity : ℂ) = Complex.exp (2 * Real.pi / 3 * Complex.I) :=
  (rfl)

/-- `cubeRootOfUnity` is a primitive `3`-rd root of unity in `ℂ`. -/
theorem isPrimitiveRoot_cubeRootOfUnity : IsPrimitiveRoot (cubeRootOfUnity : ℂ) 3 := by
  have h : (2 * Real.pi / 3 * Complex.I : ℂ) = 2 * Real.pi * Complex.I / (3 : ℕ) := by
    push_cast; ring
  rw [coe_cubeRootOfUnity, h]
  exact Complex.isPrimitiveRoot_exp 3 (by norm_num)

/-- `ω ^ 3 = 1` in `ℂˣ`. -/
@[simp]
theorem cubeRootOfUnity_pow_three : cubeRootOfUnity ^ 3 = 1 :=
  Units.ext (by simpa using isPrimitiveRoot_cubeRootOfUnity.pow_eq_one)

/-- `ω ^ 3 = 1` in `ℂ`. -/
@[simp]
theorem coe_cubeRootOfUnity_pow_three : (cubeRootOfUnity : ℂ) ^ 3 = 1 :=
  isPrimitiveRoot_cubeRootOfUnity.pow_eq_one

/-- `ω ≠ 1` in `ℂ`. -/
theorem cubeRootOfUnity_ne_one : (cubeRootOfUnity : ℂ) ≠ 1 :=
  isPrimitiveRoot_cubeRootOfUnity.ne_one (by norm_num)

/-- `1 + ω + ω² = 0`. -/
@[simp]
theorem one_add_cubeRootOfUnity_add_sq :
    1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2 = 0 := by
  have h := isPrimitiveRoot_cubeRootOfUnity.geom_sum_eq_zero (by norm_num)
  simpa [Finset.sum_range_succ, add_assoc] using h

/-- Complex conjugation sends `ω` to `ω⁻¹`. -/
@[simp]
theorem star_cubeRootOfUnity :
    star (cubeRootOfUnity : ℂ) = ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ) := by
  rw [coe_cubeRootOfUnity, Units.val_inv_eq_inv_val, coe_cubeRootOfUnity, Complex.star_def,
    ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [Complex.conj_ofReal, map_div₀, map_ofNat]

/-- The `ZMod 3`-indexed power `ω ^ x`, read through `ZMod.val`. -/
noncomputable def cubeRootPow (x : ZMod 3) : ℂˣ :=
  cubeRootOfUnity ^ x.val

/-- Unfolding `cubeRootPow`. -/
theorem cubeRootPow_def (x : ZMod 3) : cubeRootPow x = cubeRootOfUnity ^ x.val :=
  (rfl)

/-- `cubeRootPow 0 = 1`. -/
@[simp]
theorem cubeRootPow_zero : cubeRootPow 0 = 1 := by simp [cubeRootPow_def]

/-- `cubeRootPow 1 = cubeRootOfUnity`. -/
@[simp]
theorem cubeRootPow_one : cubeRootPow 1 = cubeRootOfUnity := by
  have h1 : (1 : ZMod 3).val = 1 := rfl
  simp [cubeRootPow_def, h1]

/-- `cubeRootPow` converts addition in `ZMod 3` to multiplication in `ℂˣ`. -/
@[simp]
theorem cubeRootPow_add (x y : ZMod 3) :
    cubeRootPow (x + y) = cubeRootPow x * cubeRootPow y := by
  simp only [cubeRootPow_def, ZMod.val_add]
  rw [← pow_add, ← pow_eq_pow_mod _ cubeRootOfUnity_pow_three]

/-- `cubeRootPow` converts negation in `ZMod 3` to inversion in `ℂˣ`. -/
@[simp]
theorem cubeRootPow_neg (x : ZMod 3) : cubeRootPow (-x) = (cubeRootPow x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← cubeRootPow_add, neg_add_cancel, cubeRootPow_zero])

/-- Complex conjugation sends `cubeRootPow x` to `cubeRootPow (-x)`. -/
@[simp]
theorem star_cubeRootPow (x : ZMod 3) :
    star (cubeRootPow x : ℂ) = ((cubeRootPow (-x) : ℂˣ) : ℂ) := by
  rw [cubeRootPow_def, Units.val_pow_eq_pow_val, star_pow, star_cubeRootOfUnity,
    cubeRootPow_neg, cubeRootPow_def, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val, inv_pow]

/-- `cubeRootPow x = 1` if and only if `x = 0`. -/
@[simp]
theorem cubeRootPow_eq_one_iff {x : ZMod 3} : cubeRootPow x = 1 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; exact cubeRootPow_zero⟩
  have hval : (cubeRootOfUnity : ℂ) ^ x.val = 1 := by
    simpa [cubeRootPow_def] using congrArg Units.val h
  exact (ZMod.val_eq_zero x).mp
    (Nat.eq_zero_of_dvd_of_lt ((isPrimitiveRoot_cubeRootOfUnity.pow_eq_one_iff_dvd x.val).mp hval)
      x.val_lt)

/-! ### The alternating chain form and factor set -/

/-- The alternating biadditive **chain form**
`B(a, b) = ∑_{j < N - 1} (a j * b (j + 1) - b j * a (j + 1))` on `Fin N → ZMod 3`. -/
def chainForm (N : ℕ) (a b : Fin N → ZMod 3) : ZMod 3 :=
  ∑ i : Fin N, ∑ j : Fin N, if (i : ℕ) + 1 = j then a i * b j - b i * a j else 0

/-- Unfolding `chainForm`. -/
theorem chainForm_def (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N a b =
      ∑ i : Fin N, ∑ j : Fin N, if (i : ℕ) + 1 = j then a i * b j - b i * a j else 0 :=
  (rfl)

/-- `chainForm` is additive in its first argument. -/
theorem chainForm_add_left (N : ℕ) (a b c : Fin N → ZMod 3) :
    chainForm N (a + b) c = chainForm N a c + chainForm N b c := by
  simp only [chainForm_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Pi.add_apply]; split_ifs <;> ring

/-- `chainForm` is additive in its second argument. -/
theorem chainForm_add_right (N : ℕ) (a b c : Fin N → ZMod 3) :
    chainForm N a (b + c) = chainForm N a b + chainForm N a c := by
  simp only [chainForm_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Pi.add_apply]; split_ifs <;> ring

/-- `chainForm` vanishes when its first argument is zero. -/
@[simp]
theorem chainForm_zero_left (N : ℕ) (b : Fin N → ZMod 3) : chainForm N 0 b = 0 := by
  simp [chainForm_def]

/-- `chainForm` vanishes when its second argument is zero. -/
@[simp]
theorem chainForm_zero_right (N : ℕ) (a : Fin N → ZMod 3) : chainForm N a 0 = 0 := by
  simp [chainForm_def]

/-- `chainForm` is alternating. -/
@[simp]
theorem chainForm_self (N : ℕ) (a : Fin N → ZMod 3) : chainForm N a a = 0 := by
  simp [chainForm_def]

/-- `chainForm` is skew-symmetric: `B(b, a) = -B(a, b)`. -/
theorem chainForm_swap (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N b a = -chainForm N a b := by
  simp only [chainForm_def, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> ring

/-- `chainForm` negates in its first argument. -/
@[simp]
theorem chainForm_neg_left (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N (-a) b = -chainForm N a b :=
  eq_neg_of_add_eq_zero_left (by rw [← chainForm_add_left, neg_add_cancel, chainForm_zero_left])

/-- `chainForm` negates in its second argument. -/
@[simp]
theorem chainForm_neg_right (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N a (-b) = -chainForm N a b :=
  eq_neg_of_add_eq_zero_left (by rw [← chainForm_add_right, neg_add_cancel, chainForm_zero_right])

/-- `chainForm` is invariant under simultaneous negation. -/
theorem chainForm_neg_neg (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N (-a) (-b) = chainForm N a b := by
  simp

/-- `chainForm` is subtractive in its first argument. -/
theorem chainForm_sub_left (N : ℕ) (a b c : Fin N → ZMod 3) :
    chainForm N (a - b) c = chainForm N a c - chainForm N b c := by
  rw [sub_eq_add_neg, chainForm_add_left, chainForm_neg_left, ← sub_eq_add_neg]

/-- `chainForm` is subtractive in its second argument. -/
theorem chainForm_sub_right (N : ℕ) (a b c : Fin N → ZMod 3) :
    chainForm N a (b - c) = chainForm N a b - chainForm N a c := by
  rw [sub_eq_add_neg, chainForm_add_right, chainForm_neg_right, ← sub_eq_add_neg]

/-- On adjacent standard basis vectors `e_i, e_{i+1}`, `chainForm` evaluates to `1`. -/
theorem chainForm_single_single_of_succ {N : ℕ} {i j : Fin N} (h : (i : ℕ) + 1 = j) :
    chainForm N (Pi.single i 1) (Pi.single j 1) = 1 := by
  rw [chainForm_def, Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · have hij : i ≠ j := fun hij ↦ by subst hij; omega
      simp [h, hij]
    · intro k _ hkj
      split_ifs with hik
      · exact absurd (Fin.ext (by omega)) hkj
      · rfl
    · simp
  · intro k _ hki
    refine Finset.sum_eq_zero fun l _ ↦ ?_
    split_ifs with hkl
    · simp only [Pi.single_apply, hki, ↓reduceIte, zero_mul, zero_sub, neg_eq_zero]
      split_ifs <;> simp_all
      omega
    · rfl
  · simp

/-- On standard basis vectors at distance at least two, `chainForm` vanishes. -/
theorem chainForm_single_single_of_distant {N : ℕ} {i j : Fin N}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    chainForm N (Pi.single i 1) (Pi.single j 1) = 0 := by
  rw [chainForm_def]
  refine Finset.sum_eq_zero fun k _ ↦ Finset.sum_eq_zero fun l _ ↦ ?_
  split_ifs with hkl
  · simp only [Pi.single_apply]
    split_ifs <;> simp_all <;> omega
  · rfl

/-- The **cubic quantum torus factor set** `α(a, b) = ω ^ (2 * B(a, b))` on
`Multiplicative (Fin N → ZMod 3)`. Since `2 = -1` in `ZMod 3`, we have
`α(a, b) / α(b, a) = ω ^ B(a, b)`, so adjacent site generators satisfy
`U_j * U_{j + 1} = ω • (U_{j + 1} * U_j)`. -/
noncomputable def cubicFactor (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) : ℂˣ :=
  cubeRootPow (2 * chainForm N a.toAdd b.toAdd)

/-- Unfolding `cubicFactor`. -/
theorem cubicFactor_def (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a b = cubeRootPow (2 * chainForm N a.toAdd b.toAdd) :=
  (rfl)

/-- `cubicFactor N` is a normalized factor set on `Multiplicative (Fin N → ZMod 3)`. -/
instance cubicFactor_isFactorSet (N : ℕ) : IsFactorSet (cubicFactor N) where
  one_left b := by simp [cubicFactor_def]
  cocycle a b c := by
    simp only [cubicFactor_def, toAdd_mul, ← cubeRootPow_add]
    congr 1
    rw [chainForm_add_left, chainForm_add_right]
    ring

/-- Diagonal values of `cubicFactor` are `1`. -/
@[simp]
theorem cubicFactor_self (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a a = 1 := by
  simp [cubicFactor_def]

/-- Swapping the arguments of `cubicFactor` inverts the value. -/
theorem cubicFactor_swap (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N b a = (cubicFactor N a b)⁻¹ := by
  rw [cubicFactor_def, cubicFactor_def, chainForm_swap, mul_neg, cubeRootPow_neg]

/-- Inverting the second argument of `cubicFactor` inverts the value. -/
@[simp]
theorem cubicFactor_inv_right (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a b⁻¹ = (cubicFactor N a b)⁻¹ := by
  simp [cubicFactor_def]

/-- Inverting the first argument of `cubicFactor` inverts the value. -/
@[simp]
theorem cubicFactor_inv_left (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a⁻¹ b = (cubicFactor N a b)⁻¹ := by
  simp [cubicFactor_def]

/-- Simultaneously inverting both arguments leaves `cubicFactor` unchanged. -/
theorem cubicFactor_inv_inv (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a⁻¹ b⁻¹ = cubicFactor N a b := by
  simp

/-- Complex conjugation swaps the arguments of `cubicFactor`. -/
@[simp]
theorem star_cubicFactor (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    star (cubicFactor N a b : ℂ) = (cubicFactor N b a : ℂ) := by
  rw [cubicFactor_def, star_cubeRootPow, cubicFactor_def, chainForm_swap, mul_neg, neg_neg]

/-! ### The cubic quantum torus, Weyl basis, scalar trace, and analytic adjoint -/

/-- The **cubic quantum torus** `G_N`: the twisted monoid algebra of
`Multiplicative (Fin N → ZMod 3)` for the factor set `cubicFactor N`, of complex dimension
`3 ^ N`. -/
noncomputable abbrev CubicTorus (N : ℕ) :=
  twistedMonoidAlgebra ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)

/-- The Weyl basis element `W(a) = TwistedMonoidAlgebra.of a` of `CubicTorus N`. -/
noncomputable def weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) : CubicTorus N :=
  TwistedMonoidAlgebra.of a

/-- Unfolding `weyl`. -/
theorem weyl_def (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a = TwistedMonoidAlgebra.of a :=
  (rfl)

/-- `weyl N 1 = 1`. -/
@[simp]
theorem weyl_one (N : ℕ) : weyl N 1 = 1 :=
  TwistedMonoidAlgebra.of_one

/-- Multiplication table of the Weyl basis: `W(a) * W(b) = cubicFactor N a b • W(a * b)`. -/
@[simp]
theorem weyl_mul (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    weyl N a * weyl N b = (cubicFactor N a b : ℂ) • weyl N (a * b) :=
  TwistedMonoidAlgebra.of_mul_of a b

/-- `W(a) * W(a⁻¹) = 1`. -/
theorem weyl_mul_inv (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a * weyl N a⁻¹ = 1 := by
  simp

/-- `W(a⁻¹) * W(a) = 1`. -/
theorem weyl_inv_mul (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a⁻¹ * weyl N a = 1 := by
  simp

/-- Natural powers of a Weyl basis element satisfy `W(a) ^ k = W(a ^ k)`. -/
theorem weyl_pow (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) (k : ℕ) :
    weyl N a ^ k = weyl N (a ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, weyl_mul, pow_succ]
    have hform : chainForm N (a ^ k).toAdd a.toAdd = 0 := by
      clear ih
      induction k with
      | zero => simp
      | succ k ihk => rw [pow_succ, toAdd_mul, chainForm_add_left, ihk, chainForm_self, add_zero]
    rw [cubicFactor_def, hform]
    simp

/-- Every Weyl basis element has cube equal to `1`. -/
@[simp]
theorem weyl_pow_three (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a ^ 3 = 1 := by
  rw [weyl_pow]
  have ha : a ^ 3 = 1 := Multiplicative.toAdd.injective <| funext fun i ↦ by
    have h3 : (3 : ZMod 3) = 0 := rfl
    simp [h3]
  rw [ha, weyl_one]

/-- The complex dimension of `CubicTorus N` is `3 ^ N`. -/
@[simp]
theorem finrank_cubicTorus (N : ℕ) : Module.finrank ℂ (CubicTorus N) = 3 ^ N := by
  rw [Module.finrank_eq_card_basis
    (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N))]
  simp [ZMod.card]

private theorem basis_repr_sum_weyl (N : ℕ) (f : Multiplicative (Fin N → ZMod 3) → ℂ)
    (a : Multiplicative (Fin N → ZMod 3)) :
    (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3))
      (cubicFactor N)).repr (∑ g, f g • weyl N g) a = f a := by
  set b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  have hsum : ∑ g, f g • weyl N g = ∑ g, f g • b g :=
    Finset.sum_congr rfl fun g _ ↦ by simp [b, weyl_def]
  rw [hsum, ← Module.Basis.coord_apply, map_sum, Finset.sum_eq_single a]
  · simp [Module.Basis.coord_apply]
  · intro g _ hga; simp [Module.Basis.coord_apply, hga]
  · simp

/-- The normalized **scalar-part trace** `s_N : CubicTorus N →ₗ[ℂ] ℂ`, extracting the coefficient
of `weyl N 1 = 1` in the Weyl basis. -/
noncomputable def cubicScalarCoefficient (N : ℕ) : CubicTorus N →ₗ[ℂ] ℂ :=
  (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)).coord 1

/-- Unfolding `cubicScalarCoefficient` as the `1`-coordinate in the Weyl basis. -/
theorem cubicScalarCoefficient_apply (N : ℕ) (x : CubicTorus N) :
    cubicScalarCoefficient N x =
      (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3))
        (cubicFactor N)).repr x 1 :=
  (rfl)

/-- On Weyl basis elements, `cubicScalarCoefficient` is the indicator of `1`. -/
@[simp]
theorem cubicScalarCoefficient_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicScalarCoefficient N (weyl N a) = if a = 1 then 1 else 0 := by
  rw [cubicScalarCoefficient_apply, weyl_def, ← TwistedMonoidAlgebra.basis_apply,
    Module.Basis.repr_self, Finsupp.single_apply]

/-- `cubicScalarCoefficient` is normalized: `s_N(1) = 1`. -/
@[simp]
theorem cubicScalarCoefficient_one (N : ℕ) : cubicScalarCoefficient N 1 = 1 := by
  rw [← weyl_one N, cubicScalarCoefficient_weyl]
  simp

/-- On a product of two Weyl basis elements, `s_N(W(a) * W(b)) = 1` if `a * b = 1` and `0`
otherwise. -/
theorem cubicScalarCoefficient_weyl_mul_weyl (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicScalarCoefficient N (weyl N a * weyl N b) = if a * b = 1 then 1 else 0 := by
  rw [weyl_mul, map_smul, cubicScalarCoefficient_weyl, smul_eq_mul]
  split_ifs with h
  · have hb : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    subst hb; simp
  · simp

/-- `cubicScalarCoefficient` is a trace: `s_N(x * y) = s_N(y * x)`. -/
theorem cubicScalarCoefficient_mul_comm (N : ℕ) (x y : CubicTorus N) :
    cubicScalarCoefficient N (x * y) = cubicScalarCoefficient N (y * x) := by
  let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  have hbil : (LinearMap.mul ℂ (CubicTorus N)).compr₂ (cubicScalarCoefficient N) =
      (LinearMap.mul ℂ (CubicTorus N)).flip.compr₂ (cubicScalarCoefficient N) := by
    refine b.ext fun g ↦ b.ext fun h ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.flip_apply, b,
      TwistedMonoidAlgebra.basis_apply, ← weyl_def, cubicScalarCoefficient_weyl_mul_weyl,
      mul_comm g h]
  exact LinearMap.congr_fun₂ hbil x y

/-- The **analytic adjoint** `x ↦ x†` on `CubicTorus N`: the conjugate-linear, product-reversing
involution sending `weyl N a` to `weyl N a⁻¹`. -/
noncomputable def cubicAdjoint (N : ℕ) : CubicTorus N →ₗ⋆[ℂ] CubicTorus N where
  toFun x :=
    ∑ a : Multiplicative (Fin N → ZMod 3),
      conj ((TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3))
        (cubicFactor N)).repr x a) • weyl N a⁻¹
  map_add' x y := by simp [Finset.sum_add_distrib, add_smul]
  map_smul' z x := by simp [Finset.smul_sum, smul_smul]

/-- Unfolding `cubicAdjoint` as a sum over the Weyl basis. -/
theorem cubicAdjoint_apply (N : ℕ) (x : CubicTorus N) :
    cubicAdjoint N x =
      ∑ a : Multiplicative (Fin N → ZMod 3),
        conj ((TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3))
          (cubicFactor N)).repr x a) • weyl N a⁻¹ :=
  (rfl)

/-- `cubicAdjoint` sends each Weyl basis element `W(a)` to `W(a⁻¹)`. -/
@[simp]
theorem cubicAdjoint_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicAdjoint N (weyl N a) = weyl N a⁻¹ := by
  rw [cubicAdjoint_apply, Finset.sum_eq_single a]
  · simp [weyl_def, ← TwistedMonoidAlgebra.basis_apply]
  · intro g _ hga; simp [weyl_def, ← TwistedMonoidAlgebra.basis_apply, hga.symm]
  · simp

/-- `cubicAdjoint` fixes `1`. -/
@[simp]
theorem cubicAdjoint_one (N : ℕ) : cubicAdjoint N 1 = 1 := by
  rw [← weyl_one N, cubicAdjoint_weyl, inv_one, weyl_one]

/-- `cubicAdjoint` acts on scalars by complex conjugation. -/
@[simp]
theorem cubicAdjoint_algebraMap (N : ℕ) (z : ℂ) :
    cubicAdjoint N (algebraMap ℂ (CubicTorus N) z) = algebraMap ℂ (CubicTorus N) (conj z) := by
  rw [Algebra.algebraMap_eq_smul_one, map_smulₛₗ, cubicAdjoint_one,
    ← Algebra.algebraMap_eq_smul_one]

/-- `cubicAdjoint` reverses products. -/
@[simp]
theorem cubicAdjoint_mul (N : ℕ) (x y : CubicTorus N) :
    cubicAdjoint N (x * y) = cubicAdjoint N y * cubicAdjoint N x := by
  let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  rw [(b.sum_repr x).symm, (b.sum_repr y).symm, Finset.sum_mul, map_sum, map_sum, map_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [Finset.mul_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  simp only [b, TwistedMonoidAlgebra.basis_apply, ← weyl_def, smul_mul_smul_comm, weyl_mul,
    smul_smul, map_smulₛₗ, starRingEnd_apply, cubicAdjoint_weyl, star_mul', star_cubicFactor,
    mul_inv, cubicFactor_inv_inv]
  rw [mul_comm (star (b.repr y h)), mul_comm g⁻¹ h⁻¹]

/-- `cubicAdjoint` is involutive. -/
@[simp]
theorem cubicAdjoint_cubicAdjoint (N : ℕ) (x : CubicTorus N) :
    cubicAdjoint N (cubicAdjoint N x) = x := by
  let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  have hx := (b.sum_repr x).symm
  conv_lhs => rw [hx, map_sum, map_sum]
  conv_rhs => rw [hx]
  exact Finset.sum_congr rfl fun g _ ↦ by simp [b, ← weyl_def]

/-- `cubicScalarCoefficient` intertwines `cubicAdjoint` with complex conjugation. -/
@[simp]
theorem cubicScalarCoefficient_cubicAdjoint (N : ℕ) (x : CubicTorus N) :
    cubicScalarCoefficient N (cubicAdjoint N x) = conj (cubicScalarCoefficient N x) := by
  let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  have hx := (b.sum_repr x).symm
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  simp [b, ← weyl_def, map_sum, Finset.sum_ite_eq']

/-- **Sesquilinear Parseval identity** for `cubicScalarCoefficient`: in the Weyl basis,
`s_N(x† * y) = ∑_a conj (x_a) * y_a`. -/
theorem cubicScalarCoefficient_cubicAdjoint_mul (N : ℕ) (x y : CubicTorus N) :
    cubicScalarCoefficient N (cubicAdjoint N x * y) =
      ∑ a : Multiplicative (Fin N → ZMod 3),
        conj ((TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3))
          (cubicFactor N)).repr x a) *
          (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3))
            (cubicFactor N)).repr y a := by
  let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  conv_lhs => rw [(b.sum_repr x).symm, (b.sum_repr y).symm]
  rw [map_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.mul_sum, map_sum]
  have hinner : ∀ g : Multiplicative (Fin N → ZMod 3),
      cubicScalarCoefficient N
          (cubicAdjoint N (b.repr x a • b a) * (b.repr y g • b g)) =
        if g = a then conj (b.repr x a) * b.repr y g else 0 := by
    intro g
    simp only [b, TwistedMonoidAlgebra.basis_apply, ← weyl_def, map_smulₛₗ, RingHom.id_apply,
      starRingEnd_apply, cubicAdjoint_weyl, smul_mul_smul_comm,
      cubicScalarCoefficient_weyl_mul_weyl, smul_eq_mul, inv_mul_eq_one, eq_comm (a := a)]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun g _ ↦ hinner g]
  simp [b]

/-- **Parseval identity** for `cubicScalarCoefficient`: in the Weyl basis,
`s_N(x† * x)` is the sum of squared moduli of the coordinates of `x`. -/
theorem cubicScalarCoefficient_cubicAdjoint_mul_self (N : ℕ) (x : CubicTorus N) :
    cubicScalarCoefficient N (cubicAdjoint N x * x) =
      ((∑ a : Multiplicative (Fin N → ZMod 3),
        Complex.normSq ((TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3))
          (cubicFactor N)).repr x a) : ℝ) : ℂ) := by
  rw [cubicScalarCoefficient_cubicAdjoint_mul, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun a _ ↦ by rw [mul_comm, Complex.mul_conj]

/-- **Positivity** of `cubicScalarCoefficient` for `cubicAdjoint`. -/
theorem cubicScalarCoefficient_cubicAdjoint_mul_self_nonneg (N : ℕ) (x : CubicTorus N) :
    0 ≤ cubicScalarCoefficient N (cubicAdjoint N x * x) := by
  rw [cubicScalarCoefficient_cubicAdjoint_mul_self, Complex.zero_le_real]
  exact Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _

/-- **Faithfulness** of `cubicScalarCoefficient` for `cubicAdjoint`:
`s_N(x† * x) = 0` if and only if `x = 0`. -/
@[simp]
theorem cubicScalarCoefficient_cubicAdjoint_mul_self_eq_zero_iff (N : ℕ) {x : CubicTorus N} :
    cubicScalarCoefficient N (cubicAdjoint N x * x) = 0 ↔ x = 0 := by
  let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  rw [cubicScalarCoefficient_cubicAdjoint_mul_self, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ Complex.normSq_nonneg _)]
  simp only [Finset.mem_univ, forall_const, Complex.normSq_eq_zero]
  exact ⟨fun h ↦ b.repr.injective (by ext a; rw [b.repr.map_zero]; exact h a),
    fun h a ↦ by rw [h, b.repr.map_zero]; rfl⟩

/-! ### The inversion automorphism and the inversion-fixed subalgebra -/

/-- The **exponent inversion** `θ_N : W(a) ↦ W(a⁻¹)`, an involutive `ℂ`-algebra automorphism of
`CubicTorus N`. -/
noncomputable def cubicInversion (N : ℕ) : CubicTorus N →ₐ[ℂ] CubicTorus N :=
  TwistedMonoidAlgebra.lift (fun a ↦ weyl N a⁻¹) (by simp) (fun _ _ ↦ by simp [mul_comm])

/-- `cubicInversion` sends `W(a)` to `W(a⁻¹)`. -/
@[simp]
theorem cubicInversion_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicInversion N (weyl N a) = weyl N a⁻¹ :=
  TwistedMonoidAlgebra.lift_of _ _ _ a

/-- `cubicInversion` is involutive. -/
@[simp]
theorem cubicInversion_cubicInversion (N : ℕ) (x : CubicTorus N) :
    cubicInversion N (cubicInversion N x) = x := by
  have hcomp : (cubicInversion N).comp (cubicInversion N) = AlgHom.id ℂ (CubicTorus N) :=
    TwistedMonoidAlgebra.algHom_ext fun _ ↦ by simp [← weyl_def]
  exact AlgHom.congr_fun hcomp x

/-- `cubicInversion` commutes with `cubicAdjoint`. -/
@[simp]
theorem cubicInversion_cubicAdjoint (N : ℕ) (x : CubicTorus N) :
    cubicInversion N (cubicAdjoint N x) = cubicAdjoint N (cubicInversion N x) := by
  let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  have hx := (b.sum_repr x).symm
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  simp [b, ← weyl_def, map_sum]

/-- `cubicInversion` preserves `cubicScalarCoefficient`. -/
@[simp]
theorem cubicScalarCoefficient_cubicInversion (N : ℕ) (x : CubicTorus N) :
    cubicScalarCoefficient N (cubicInversion N x) = cubicScalarCoefficient N x := by
  let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  have hx := (b.sum_repr x).symm
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  simp [b, ← weyl_def, map_sum]

/-- The **inversion-fixed subalgebra** `C_N = {x ∈ CubicTorus N : cubicInversion N x = x}`, of
complex dimension `(3 ^ N + 1) / 2`. -/
noncomputable def cubicFixed (N : ℕ) : Subalgebra ℂ (CubicTorus N) :=
  AlgHom.equalizer (cubicInversion N) (AlgHom.id ℂ (CubicTorus N))

/-- Membership in `cubicFixed N` is being fixed by `cubicInversion N`. -/
@[simp]
theorem mem_cubicFixed_iff {N : ℕ} {x : CubicTorus N} :
    x ∈ cubicFixed N ↔ cubicInversion N x = x :=
  AlgHom.mem_equalizer (cubicInversion N) (AlgHom.id ℂ (CubicTorus N)) x

/-- `cubicFixed N` is stable under `cubicAdjoint N`. -/
theorem cubicAdjoint_mem_cubicFixed (N : ℕ) {x : CubicTorus N} (hx : x ∈ cubicFixed N) :
    cubicAdjoint N x ∈ cubicFixed N := by
  rw [mem_cubicFixed_iff, cubicInversion_cubicAdjoint, mem_cubicFixed_iff.mp hx]

/-- `cubicAdjoint N x` lies in `cubicFixed N` if and only if `x` does. -/
theorem cubicAdjoint_mem_cubicFixed_iff (N : ℕ) {x : CubicTorus N} :
    cubicAdjoint N x ∈ cubicFixed N ↔ x ∈ cubicFixed N :=
  ⟨fun h ↦ cubicAdjoint_cubicAdjoint N x ▸ cubicAdjoint_mem_cubicFixed N h,
    cubicAdjoint_mem_cubicFixed N⟩

/-- Restriction of `cubicAdjoint N` to `cubicFixed N`. -/
noncomputable def cubicFixedAdjoint (N : ℕ) : cubicFixed N →ₗ⋆[ℂ] cubicFixed N where
  toFun x := ⟨cubicAdjoint N x, cubicAdjoint_mem_cubicFixed N x.2⟩
  map_add' _ _ := Subtype.ext (by simp)
  map_smul' _ _ := Subtype.ext (by simp)

/-- Coercing `cubicFixedAdjoint N x` to `CubicTorus N` gives `cubicAdjoint N x`. -/
@[simp]
theorem coe_cubicFixedAdjoint (N : ℕ) (x : cubicFixed N) :
    (cubicFixedAdjoint N x : CubicTorus N) = cubicAdjoint N x :=
  (rfl)

/-- `cubicFixedAdjoint` fixes `1`. -/
@[simp]
theorem cubicFixedAdjoint_one (N : ℕ) : cubicFixedAdjoint N 1 = 1 :=
  Subtype.ext (cubicAdjoint_one N)

/-- `cubicFixedAdjoint` acts on scalars by complex conjugation. -/
@[simp]
theorem cubicFixedAdjoint_algebraMap (N : ℕ) (z : ℂ) :
    cubicFixedAdjoint N (algebraMap ℂ (cubicFixed N) z) =
      algebraMap ℂ (cubicFixed N) (conj z) :=
  Subtype.ext (cubicAdjoint_algebraMap N z)

/-- `cubicFixedAdjoint` reverses products. -/
@[simp]
theorem cubicFixedAdjoint_mul (N : ℕ) (x y : cubicFixed N) :
    cubicFixedAdjoint N (x * y) = cubicFixedAdjoint N y * cubicFixedAdjoint N x :=
  Subtype.ext (cubicAdjoint_mul N x y)

/-- `cubicFixedAdjoint` is involutive. -/
@[simp]
theorem cubicFixedAdjoint_cubicFixedAdjoint (N : ℕ) (x : cubicFixed N) :
    cubicFixedAdjoint N (cubicFixedAdjoint N x) = x :=
  Subtype.ext (cubicAdjoint_cubicAdjoint N x)

/-- The bilinear trace pairing `(x, y) ↦ s_N(x * y)` is nondegenerate on `cubicFixed N`. -/
theorem forall_cubicFixed_scalarCoefficient_mul_eq_zero_iff {N : ℕ} {x : cubicFixed N} :
    (∀ y : cubicFixed N, cubicScalarCoefficient N ((x : CubicTorus N) * y) = 0) ↔ x = 0 := by
  refine ⟨fun h ↦ Subtype.ext ?_, fun hx y ↦ by simp [hx]⟩
  apply (cubicScalarCoefficient_cubicAdjoint_mul_self_eq_zero_iff N).mp
  rw [cubicScalarCoefficient_mul_comm]
  exact h (cubicFixedAdjoint N x)

/-! ### Dimension of `cubicFixed N` -/

private theorem basis_repr_cubicInversion (N : ℕ) (x : CubicTorus N)
    (a : Multiplicative (Fin N → ZMod 3)) :
    (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3))
        (cubicFactor N)).repr (cubicInversion N x) a =
      (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3))
        (cubicFactor N)).repr x a⁻¹ := by
  let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  have hinv : cubicInversion N x = ∑ g, b.repr x g⁻¹ • weyl N g := by
    conv_lhs => rw [(b.sum_repr x).symm, map_sum]
    rw [← Equiv.sum_comp (Equiv.inv (Multiplicative (Fin N → ZMod 3)))]
    exact Finset.sum_congr rfl fun g _ ↦ by simp [b, ← weyl_def]
  rw [hinv]
  exact basis_repr_sum_weyl N (fun g ↦ b.repr x g⁻¹) a

/-- Linear equivalence identifying `cubicFixed N` with functions on a chosen set `S` of orbit
representatives for negation on `Fin N → ZMod 3`. -/
private noncomputable def cubicFixedEquivFun (N : ℕ) (S : Finset (Fin N → ZMod 3))
    (hcover : ∀ a : Fin N → ZMod 3, a ∈ S ∨ -a ∈ S) (huniq : ∀ a ∈ S, -a ∈ S → a = 0) :
    cubicFixed N ≃ₗ[ℂ] (S → ℂ) :=
  let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  { toFun := fun x a ↦ b.repr x (Multiplicative.ofAdd a.1)
    map_add' := fun x y ↦ by
      ext a; simp only [Subalgebra.coe_add, b.repr.map_add, Finsupp.add_apply, Pi.add_apply]
    map_smul' := fun z x ↦ by
      ext a
      simp only [SetLike.val_smul, b.repr.map_smul, Finsupp.smul_apply, RingHom.id_apply,
        Pi.smul_apply]
    invFun := fun f ↦
      ⟨∑ g : Multiplicative (Fin N → ZMod 3),
          (if hg : g.toAdd ∈ S then f ⟨g.toAdd, hg⟩
            else f ⟨-g.toAdd, (hcover g.toAdd).resolve_left hg⟩) • weyl N g, by
        rw [mem_cubicFixed_iff, map_sum]
        have hneg : ∀ g : Multiplicative (Fin N → ZMod 3),
            cubicInversion N
                ((if hg : g.toAdd ∈ S then f ⟨g.toAdd, hg⟩
                  else f ⟨-g.toAdd, (hcover g.toAdd).resolve_left hg⟩) • weyl N g) =
              (if hg : g⁻¹.toAdd ∈ S then f ⟨g⁻¹.toAdd, hg⟩
                else f ⟨-g⁻¹.toAdd, (hcover g⁻¹.toAdd).resolve_left hg⟩) • weyl N g⁻¹ := by
          intro g
          simp only [map_smul, cubicInversion_weyl]
          congr 1
          by_cases hg : g.toAdd ∈ S
          · by_cases hgn : -g.toAdd ∈ S
            · simp [huniq g.toAdd hg hgn]
            · simp [hg, hgn]
          · simp [hg, (hcover g.toAdd).resolve_left hg]
        rw [Finset.sum_congr rfl fun g _ ↦ hneg g]
        exact Fintype.sum_equiv (Equiv.inv (Multiplicative (Fin N → ZMod 3))) _ _ fun _ ↦ by
          simp only [Equiv.inv_apply]⟩
    left_inv := fun x ↦ by
      apply Subtype.ext; apply b.repr.injective; ext g
      rw [basis_repr_sum_weyl]
      by_cases hg : g.toAdd ∈ S
      · simp [hg]
      · have hrepr := basis_repr_cubicInversion N x g
        rw [mem_cubicFixed_iff.mp x.2] at hrepr
        simpa [hg] using hrepr.symm
    right_inv := fun f ↦ by
      ext a; dsimp only; rw [basis_repr_sum_weyl]; simp [a.2] }

/-- The complex dimension of the inversion-fixed subalgebra `cubicFixed N` is `(3 ^ N + 1) / 2`. -/
@[simp]
theorem finrank_cubicFixed (N : ℕ) : Module.finrank ℂ (cubicFixed N) = (3 ^ N + 1) / 2 := by
  let e : (Fin N → ZMod 3) ≃ Fin (Fintype.card (Fin N → ZMod 3)) := Fintype.equivFin _
  let S : Finset (Fin N → ZMod 3) := Finset.univ.filter fun a ↦ e a ≤ e (-a)
  have hneg_eq : ∀ a : Fin N → ZMod 3, -a = a → a = 0 := fun a ha ↦ funext fun i ↦ by
    have hai : -a i = a i := congrFun ha i
    have h2 : (2 : ZMod 3) * a i = 0 := by
      calc (2 : ZMod 3) * a i = a i + a i := two_mul _
        _ = -a i + a i := by rw [hai]
        _ = 0 := neg_add_cancel _
    have h4 := congrArg (2 * ·) h2
    have h22 : (2 * 2 : ZMod 3) = 1 := rfl
    rwa [← mul_assoc, h22, one_mul, mul_zero] at h4
  have hcover : ∀ a : Fin N → ZMod 3, a ∈ S ∨ -a ∈ S := fun a ↦ by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, neg_neg]
    exact le_total (e a) (e (-a))
  have huniq : ∀ a ∈ S, -a ∈ S → a = 0 := fun a ha hna ↦ by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, neg_neg] at ha hna
    exact hneg_eq a (e.injective (le_antisymm hna ha))
  rw [(cubicFixedEquivFun N S hcover huniq).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe]
  have hzero : (0 : Fin N → ZMod 3) ∈ S := by simp [S]
  have hunion : S ∪ (S.erase 0).image (-·) = Finset.univ := by
    ext a
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, iff_true]
    rcases hcover a with ha | hna
    · exact Or.inl ha
    · by_cases ha0 : a = 0
      · exact Or.inl (ha0 ▸ hzero)
      · exact Or.inr ⟨-a, ⟨neg_ne_zero.mpr ha0, hna⟩, neg_neg a⟩
  have hdisj : Disjoint S ((S.erase 0).image (-·)) := by
    rw [Finset.disjoint_left]
    intro a ha himg
    rcases Finset.mem_image.mp himg with ⟨b, hb, rfl⟩
    exact (Finset.mem_erase.mp hb).1 (huniq b (Finset.mem_erase.mp hb).2 (by simpa using ha))
  have hcard : Fintype.card (Fin N → ZMod 3) = S.card + (S.card - 1) := by
    rw [← Finset.card_univ, ← hunion, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ neg_injective, Finset.card_erase_of_mem hzero]
  have h3 : Fintype.card (Fin N → ZMod 3) = 3 ^ N := by simp [ZMod.card]
  have hpos : 1 ≤ S.card := Finset.one_le_card.mpr ⟨0, hzero⟩
  omega

end TauCeti.TemperleyLieb
