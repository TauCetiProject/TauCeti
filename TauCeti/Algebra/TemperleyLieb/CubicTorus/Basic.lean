/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.Trace
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
-- Private: field structure on `ZMod 3`, primitive root orthogonality, permutation trace,
-- essential-idempotent trace are proof-only.
import TauCeti.LinearAlgebra.Trace.Idempotent
import TauCeti.RingTheory.RootsOfUnity.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The cubic quantum torus and its inversion-fixed subalgebra

For `N : ℕ`, `V_N = Fin N → ZMod 3` carries the alternating chain form
`chainForm N a b = ∑_{i + 1 = j} (a_i b_j - b_i a_j)` and factor set
`cubicFactor N a b = ω ^ (2 * chainForm N a b)` for `ω = exp (2 π i / 3)`. Its twisted group
algebra `CubicTorus N` has dimension `3 ^ N` with Weyl basis `weyl N a` and site generators
`cubicSite N j = weyl N (ofAdd (Pi.single j 1))` satisfying `U_j ^ 3 = 1`,
`U_i * U_{i+1} = ω • (U_{i+1} * U_i)`, and commutativity at distance `≥ 2` (`liftSite`,
`adjoin_range_cubicSite`). Group inversion induces `cubicInversion N : W(a) ↦ W(a⁻¹)`, whose
fixed subalgebra `cubicFixed N` has dimension `(3 ^ N + 1) / 2` (`finrank_cubicFixed`) and
inherits the conjugate-linear reversal `cubicFixedAdjoint N`.

## Main definitions and results

* `chainForm`, `cubeRootOfUnity`, `cubicFactor`, `CubicTorus`, `weyl`.
* `cubicSite`, `liftSite`, `adjoin_range_cubicSite`, `algHom_ext_cubicSite`.
* `cubicScalarCoefficient`, `cubicAdjoint`, `cubicInversion`, `cubicFixed`, `cubicFixedAdjoint`.
* `finrank_cubicTorus`, `finrank_cubicFixed`.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111, p. 107.
* G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985), Ch. 3.
-/

public section

namespace TauCeti.TemperleyLieb

open Multiplicative

private theorem zmod3_cases (x : ZMod 3) : x = 0 ∨ x = 1 ∨ x = 2 := by revert x; decide

/-! ### The alternating chain form on `Fin N → ZMod 3` -/

/-- Upper-triangular half `∑_{i + 1 = j} a_i b_j` of `chainForm`. -/
private def halfChainForm (N : ℕ) (a b : Fin N → ZMod 3) : ZMod 3 :=
  ∑ i : Fin N, ∑ j : Fin N, if (i : ℕ) + 1 = j then a i * b j else 0

/-- **The chain form** `B(a, b) = ∑_{i + 1 = j} (a_i b_j - b_i a_j)` on `Fin N → ZMod 3`. -/
def chainForm (N : ℕ) (a b : Fin N → ZMod 3) : ZMod 3 :=
  ∑ i : Fin N, ∑ j : Fin N, if (i : ℕ) + 1 = j then a i * b j - b i * a j else 0

theorem chainForm_def (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N a b =
      ∑ i : Fin N, ∑ j : Fin N, if (i : ℕ) + 1 = j then a i * b j - b i * a j else 0 := (rfl)

/-- Extending two vectors by `0` in the last coordinate preserves `chainForm`. -/
@[simp] theorem chainForm_snoc_zero (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm (N + 1) (Fin.snoc a 0) (Fin.snoc b 0) = chainForm N a b := by
  unfold chainForm
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_last, zero_mul, sub_self, ite_self, Finset.sum_const_zero, add_zero]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [Fin.sum_univ_castSucc]; simp

private theorem chainForm_eq_sub (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N a b = halfChainForm N a b - halfChainForm N b a := by
  simp only [chainForm, halfChainForm, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> ring

private theorem halfChainForm_add_left (N : ℕ) (a₁ a₂ b : Fin N → ZMod 3) :
    halfChainForm N (a₁ + a₂) b = halfChainForm N a₁ b + halfChainForm N a₂ b := by
  simp only [halfChainForm, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> ring

private theorem halfChainForm_add_right (N : ℕ) (a b₁ b₂ : Fin N → ZMod 3) :
    halfChainForm N a (b₁ + b₂) = halfChainForm N a b₁ + halfChainForm N a b₂ := by
  simp only [halfChainForm, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> ring

private theorem halfChainForm_single_single (N : ℕ) (i j : Fin N) (c d : ZMod 3) :
    halfChainForm N (Pi.single i c) (Pi.single j d) =
      if (i : ℕ) + 1 = j then c * d else 0 := by
  rw [halfChainForm, Fintype.sum_eq_single i (fun x hx ↦ by simp [Pi.single_eq_of_ne hx]),
    Fintype.sum_eq_single j (fun y hy ↦ by simp [Pi.single_eq_of_ne hy])]
  simp

/-- `chainForm` is additive in its first argument. -/
theorem chainForm_add_left (N : ℕ) (a₁ a₂ b : Fin N → ZMod 3) :
    chainForm N (a₁ + a₂) b = chainForm N a₁ b + chainForm N a₂ b := by
  simp only [chainForm_eq_sub, halfChainForm_add_left, halfChainForm_add_right]; ring

/-- `chainForm` is additive in its second argument. -/
theorem chainForm_add_right (N : ℕ) (a b₁ b₂ : Fin N → ZMod 3) :
    chainForm N a (b₁ + b₂) = chainForm N a b₁ + chainForm N a b₂ := by
  simp only [chainForm_eq_sub, halfChainForm_add_left, halfChainForm_add_right]; ring

@[simp] theorem chainForm_zero_left (N : ℕ) (b : Fin N → ZMod 3) :
    chainForm N 0 b = 0 := by simp [chainForm]

@[simp] theorem chainForm_zero_right (N : ℕ) (a : Fin N → ZMod 3) :
    chainForm N a 0 = 0 := by simp [chainForm]

@[simp] theorem chainForm_self (N : ℕ) (a : Fin N → ZMod 3) :
    chainForm N a a = 0 := by simp [chainForm]

theorem chainForm_swap (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N b a = -chainForm N a b := by simp only [chainForm_eq_sub]; ring

@[simp] theorem chainForm_neg_left (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N (-a) b = -chainForm N a b :=
  eq_neg_of_add_eq_zero_left <| by rw [← chainForm_add_left, neg_add_cancel, chainForm_zero_left]

@[simp] theorem chainForm_neg_right (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N a (-b) = -chainForm N a b :=
  eq_neg_of_add_eq_zero_left <| by rw [← chainForm_add_right, neg_add_cancel, chainForm_zero_right]

theorem chainForm_neg_neg (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N (-a) (-b) = chainForm N a b := by simp

theorem chainForm_single_single (N : ℕ) (i j : Fin N) (c d : ZMod 3) :
    chainForm N (Pi.single i c) (Pi.single j d) =
      (if (i : ℕ) + 1 = j then c * d else 0) - (if (j : ℕ) + 1 = i then d * c else 0) := by
  rw [chainForm_eq_sub, halfChainForm_single_single, halfChainForm_single_single]

/-! ### Cube roots of unity and the cubic factor set -/

/-- The primitive third root of unity `ω = exp (2 π i / 3)`, bundled as a unit of `ℂ`. -/
noncomputable def cubeRootOfUnity : ℂˣ :=
  Units.mk0 (Complex.exp (2 * Real.pi / 3 * Complex.I)) (Complex.exp_ne_zero _)

/-- The complex value of `cubeRootOfUnity` is `exp (2 π i / 3)`. -/
theorem coe_cubeRootOfUnity :
    (cubeRootOfUnity : ℂ) = Complex.exp (2 * Real.pi / 3 * Complex.I) := (rfl)

private theorem isPrimitiveRoot_coe_cubeRootOfUnity :
    IsPrimitiveRoot (cubeRootOfUnity : ℂ) 3 := by
  rw [coe_cubeRootOfUnity]
  convert Complex.isPrimitiveRoot_exp 3 (by decide) using 2
  push_cast; ring

@[simp] theorem coe_cubeRootOfUnity_pow_three : (cubeRootOfUnity : ℂ) ^ 3 = 1 :=
  isPrimitiveRoot_coe_cubeRootOfUnity.pow_eq_one

@[simp] theorem cubeRootOfUnity_pow_three : cubeRootOfUnity ^ 3 = 1 :=
  Units.ext coe_cubeRootOfUnity_pow_three

/-- `cubeRootOfUnity` is nontrivial: `exp (2 π i / 3) ≠ 1`. -/
theorem coe_cubeRootOfUnity_ne_one : (cubeRootOfUnity : ℂ) ≠ 1 :=
  isPrimitiveRoot_coe_cubeRootOfUnity.ne_one (by decide)

/-- Cyclotomic vanishing `1 + ω + ω² = 0`. -/
theorem one_add_cubeRootOfUnity_add_sq :
    1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2 = 0 := by
  have h := isPrimitiveRoot_coe_cubeRootOfUnity.sum_pow_pow_eq 1
  simp only [pow_one, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero,
    Nat.dvd_one, OfNat.ofNat_ne_one, ↓reduceIte] at h
  exact h

@[simp] theorem star_coe_cubeRootOfUnity :
    star (cubeRootOfUnity : ℂ) = ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ) := by
  simpa [Complex.star_def] using
    Complex.conj_rootsOfUnity ((mem_rootsOfUnity 3 cubeRootOfUnity).mpr cubeRootOfUnity_pow_three)

@[simp] theorem zmodChar_cubeRootOfUnity_eq_one_iff {x : ZMod 3} :
    AddChar.zmodChar 3 cubeRootOfUnity_pow_three x = 1 ↔ x = 0 := by
  refine ⟨fun h ↦ by_contra fun hx ↦ ?_, fun h ↦ by simp [h]⟩
  have hval : (cubeRootOfUnity : ℂ) ^ x.val = 1 := by
    simpa [AddChar.zmodChar_apply] using congrArg Units.val h
  exact isPrimitiveRoot_coe_cubeRootOfUnity.pow_ne_one_of_pos_of_lt
    (ZMod.val_pos.mpr hx).ne' (ZMod.val_lt x) hval

@[simp] theorem star_coe_zmodChar_cubeRootOfUnity (x : ZMod 3) :
    star ((AddChar.zmodChar 3 cubeRootOfUnity_pow_three x : ℂˣ) : ℂ) =
      ((AddChar.zmodChar 3 cubeRootOfUnity_pow_three (-x) : ℂˣ) : ℂ) := by
  have hmem : AddChar.zmodChar 3 cubeRootOfUnity_pow_three x ∈ rootsOfUnity 3 ℂ := by
    rw [mem_rootsOfUnity, AddChar.zmodChar_apply, ← pow_mul, mul_comm, pow_mul,
      cubeRootOfUnity_pow_three, one_pow]
  simpa [Complex.star_def, AddChar.map_neg_eq_inv] using Complex.conj_rootsOfUnity hmem

/-- For every nonzero `c : ZMod 3`, `1 + ω^c + ω^(2c) = 0`. -/
theorem one_add_zmodChar_cubeRootOfUnity_add_two_mul {c : ZMod 3} (hc : c ≠ 0) :
    1 + ((AddChar.zmodChar 3 cubeRootOfUnity_pow_three c : ℂˣ) : ℂ) +
      ((AddChar.zmodChar 3 cubeRootOfUnity_pow_three (2 * c) : ℂˣ) : ℂ) = 0 := by
  have h := isPrimitiveRoot_coe_cubeRootOfUnity.sum_pow_pow_eq c.val
  have hndvd : ¬ 3 ∣ c.val := Nat.not_dvd_of_pos_of_lt (ZMod.val_pos.mpr hc) (ZMod.val_lt c)
  simp only [hndvd, ↓reduceIte, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one] at h
  have hc1 : (cubeRootOfUnity : ℂ) ^ c.val =
      ((AddChar.zmodChar 3 cubeRootOfUnity_pow_three c : ℂˣ) : ℂ) := by
    simp [AddChar.zmodChar_apply]
  have hc2 : ((cubeRootOfUnity : ℂ) ^ c.val) ^ 2 =
      ((AddChar.zmodChar 3 cubeRootOfUnity_pow_three (2 * c) : ℂˣ) : ℂ) := by
    rw [hc1, ← Units.val_pow_eq_pow_val, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul,
      Nat.cast_ofNat]
  rwa [← hc1, ← hc2]

/-- **The factor set of the cubic quantum torus**: `α(a, b) = ω ^ (2 * B(a, b))`. -/
noncomputable def cubicFactor (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) : ℂˣ :=
  AddChar.zmodChar 3 cubeRootOfUnity_pow_three (2 * chainForm N a.toAdd b.toAdd)

theorem cubicFactor_def (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a b =
      AddChar.zmodChar 3 cubeRootOfUnity_pow_three (2 * chainForm N a.toAdd b.toAdd) := (rfl)

/-- `cubicFactor N` is a normalized factor set on `Multiplicative (Fin N → ZMod 3)`. -/
instance cubicFactor_isFactorSet (N : ℕ) : IsFactorSet (cubicFactor N) where
  cocycle g h j := by
    simp only [cubicFactor, toAdd_mul, ← AddChar.map_add_eq_mul]
    congr 1; rw [chainForm_add_left, chainForm_add_right]; ring
  one_left g := by simp [cubicFactor]

@[simp] theorem cubicFactor_self (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a a = 1 := by simp [cubicFactor]

@[simp] theorem cubicFactor_inv_self (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a⁻¹ a = 1 := by simp [cubicFactor]

@[simp] theorem cubicFactor_self_inv (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a a⁻¹ = 1 := by simp [cubicFactor]

theorem cubicFactor_inv_inv (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a⁻¹ b⁻¹ = cubicFactor N a b := by simp [cubicFactor]

@[simp] theorem cubicFactor_inv_right (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a b⁻¹ = (cubicFactor N a b)⁻¹ := by
  simp [cubicFactor, AddChar.map_neg_eq_inv]

@[simp] theorem cubicFactor_inv_left (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a⁻¹ b = (cubicFactor N a b)⁻¹ := by
  simp [cubicFactor, AddChar.map_neg_eq_inv]

theorem cubicFactor_swap (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N b a = (cubicFactor N a b)⁻¹ := by
  rw [cubicFactor, chainForm_swap, mul_neg, AddChar.map_neg_eq_inv, ← cubicFactor]

theorem star_coe_cubicFactor (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    star (cubicFactor N a b : ℂ) = (cubicFactor N b⁻¹ a⁻¹ : ℂ) := by
  rw [cubicFactor, star_coe_zmodChar_cubeRootOfUnity, cubicFactor_inv_inv, cubicFactor,
    chainForm_swap, mul_neg, neg_neg]

/-! ### The cubic quantum torus `G_N`, Weyl basis, trace, and adjoint -/

/-- **The cubic quantum torus** `G_N`: the complex twisted group algebra of `(ZMod 3)^N` with
factor set `cubicFactor N`. -/
noncomputable abbrev CubicTorus (N : ℕ) :=
  twistedMonoidAlgebra ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)

/-- The Weyl basis element `W(a)` of `CubicTorus N`. -/
noncomputable def weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) : CubicTorus N :=
  TwistedMonoidAlgebra.of a

theorem weyl_def (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a = TwistedMonoidAlgebra.of a := (rfl)

@[simp] theorem weyl_one (N : ℕ) : weyl N 1 = 1 := TwistedMonoidAlgebra.of_one

@[simp] theorem weyl_mul_weyl (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    weyl N a * weyl N b = (cubicFactor N a b : ℂ) • weyl N (a * b) :=
  TwistedMonoidAlgebra.of_mul_of a b

theorem weyl_mul_weyl_inv (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a * weyl N a⁻¹ = 1 := by
  rw [weyl_mul_weyl, cubicFactor_self_inv, Units.val_one, one_smul, mul_inv_cancel, weyl_one]

theorem weyl_inv_mul_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a⁻¹ * weyl N a = 1 := by
  rw [weyl_mul_weyl, cubicFactor_inv_self, Units.val_one, one_smul, inv_mul_cancel, weyl_one]

/-- Commutation law for Weyl basis elements: `W(a) W(b) = ω ^ B(a, b) • (W(b) W(a))`. -/
theorem weyl_mul_comm (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    weyl N a * weyl N b =
      ((AddChar.zmodChar 3 cubeRootOfUnity_pow_three (chainForm N a.toAdd b.toAdd) : ℂˣ) : ℂ) •
        (weyl N b * weyl N a) := by
  rw [weyl_mul_weyl, weyl_mul_weyl, mul_comm b a, smul_smul, ← Units.val_mul, cubicFactor,
    cubicFactor, chainForm_swap N a.toAdd b.toAdd, ← AddChar.map_add_eq_mul]
  refine congrArg
    (fun z ↦ ((AddChar.zmodChar 3 cubeRootOfUnity_pow_three z : ℂˣ) : ℂ) • weyl N (a * b)) ?_
  calc
    2 * chainForm N a.toAdd b.toAdd
        = 2 * chainForm N a.toAdd b.toAdd + (3 : ZMod 3) * (-chainForm N a.toAdd b.toAdd) := by
          rw [show (3 : ZMod 3) = 0 by decide, zero_mul, add_zero]
    _ = chainForm N a.toAdd b.toAdd + 2 * -chainForm N a.toAdd b.toAdd := by ring

/-- The dimension of `CubicTorus N` over `ℂ` is `3 ^ N`. -/
@[simp] theorem finrank_cubicTorus (N : ℕ) : Module.finrank ℂ (CubicTorus N) = 3 ^ N := by
  rw [TwistedMonoidAlgebra.finrank_eq_natCard]; simp

/-- **The normalized scalar trace** `s_N` on `CubicTorus N`, reading off the `W(0)`-coefficient. -/
noncomputable abbrev cubicScalarCoefficient (N : ℕ) : CubicTorus N →ₗ[ℂ] ℂ :=
  TwistedMonoidAlgebra.scalarTrace ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)

/-- **The conjugate-linear adjoint** `†` on `CubicTorus N`, sending `∑ z_a • W(a)` to
`∑ star z_a • W(a⁻¹)`. -/
noncomputable abbrev cubicAdjoint (N : ℕ) : CubicTorus N →ₗ⋆[ℂ] CubicTorus N :=
  TwistedMonoidAlgebra.conjReverse ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)

@[simp] theorem cubicAdjoint_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicAdjoint N (weyl N a) = weyl N a⁻¹ :=
  TwistedMonoidAlgebra.conjReverse_of a

theorem cubicAdjoint_mul (N : ℕ) (x y : CubicTorus N) :
    cubicAdjoint N (x * y) = cubicAdjoint N y * cubicAdjoint N x :=
  TwistedMonoidAlgebra.conjReverse_mul (star_coe_cubicFactor N) x y

/-! ### Site unitaries and the universal presentation of `CubicTorus N` -/

/-- The site unitary `U_j = W(e_j)` at site `j : Fin N`. -/
noncomputable def cubicSite (N : ℕ) (j : Fin N) : CubicTorus N :=
  weyl N (ofAdd (Pi.single j 1))

theorem cubicSite_def (N : ℕ) (j : Fin N) :
    cubicSite N j = weyl N (ofAdd (Pi.single j 1)) := (rfl)

theorem cubicSite_sq (N : ℕ) (j : Fin N) :
    cubicSite N j ^ 2 = weyl N (ofAdd (Pi.single j 2)) := by
  rw [sq, cubicSite_def, weyl_mul_weyl, cubicFactor_self, Units.val_one, one_smul, ← ofAdd_add,
    ← Pi.single_add]; rfl

/-- Each site unitary has order dividing `3`: `U_j ^ 3 = 1`. -/
@[simp] theorem cubicSite_pow_three (N : ℕ) (j : Fin N) : cubicSite N j ^ 3 = 1 := by
  rw [pow_succ, cubicSite_sq, cubicSite_def, weyl_mul_weyl, cubicFactor, toAdd_ofAdd, toAdd_ofAdd,
    chainForm_single_single]
  simp only [Nat.add_one_ne_self, ↓reduceIte, sub_self, mul_zero, AddChar.map_zero_eq_one,
    Units.val_one, one_smul, ← ofAdd_add, ← Pi.single_add, show (2 : ZMod 3) + 1 = 0 by decide,
    Pi.single_zero, ofAdd_zero, weyl_one]

@[simp] theorem cubicAdjoint_cubicSite (N : ℕ) (j : Fin N) :
    cubicAdjoint N (cubicSite N j) = cubicSite N j ^ 2 := by
  nth_rw 1 [cubicSite_def]
  rw [cubicAdjoint_weyl, ← ofAdd_neg, ← Pi.single_neg, show (-1 : ZMod 3) = 2 by decide,
    ← cubicSite_sq]

/-- Adjacent site unitaries satisfy `U_i * U_j = ω • (U_j * U_i)` when `i + 1 = j`. -/
theorem cubicSite_mul_cubicSite_of_succ {N : ℕ} {i j : Fin N} (h : (i : ℕ) + 1 = j) :
    cubicSite N i * cubicSite N j = (cubeRootOfUnity : ℂ) • (cubicSite N j * cubicSite N i) := by
  have hne : ¬ (j : ℕ) + 1 = i := by omega
  rw [cubicSite_def, cubicSite_def, weyl_mul_comm, toAdd_ofAdd, toAdd_ofAdd,
    chainForm_single_single]
  simp [h, hne, AddChar.zmodChar_apply, ZMod.val_one]

/-- Site unitaries at distance at least two commute. -/
theorem commute_cubicSite {N : ℕ} {i j : Fin N} (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (cubicSite N i) (cubicSite N j) := by
  have hij : ¬ (i : ℕ) + 1 = j := by omega
  have hji : ¬ (j : ℕ) + 1 = i := by omega
  rw [commute_iff_eq, cubicSite_def, cubicSite_def, weyl_mul_comm, toAdd_ofAdd, toAdd_ofAdd,
    chainForm_single_single]
  simp [hij, hji]

section UniversalProperty

private theorem partialProd_one {A : Type*} [Monoid A] (N : ℕ) :
    Fin.partialProd (fun _ : Fin N ↦ (1 : A)) (Fin.last N) = 1 := by
  induction N with
  | zero => exact Fin.partialProd_zero _
  | succ N ih =>
    rw [← Fin.succ_last, Fin.partialProd_succ, ← Fin.partialProd_init]
    simpa [Fin.init_def] using ih

private theorem partialProd_pow_single {A : Type*} [Monoid A] :
    ∀ {N : ℕ} (u : Fin N → A) (j : Fin N),
      Fin.partialProd (fun i ↦ u i ^ ((Pi.single j (1 : ZMod 3) : Fin N → ZMod 3) i).val)
        (Fin.last N) = u j
  | 0, _, j => Fin.elim0 j
  | N + 1, u, j => by
    rw [← Fin.succ_last, Fin.partialProd_succ, ← Fin.partialProd_init]
    induction j using Fin.lastCases with
    | last =>
      have hinit : Fin.init (fun i : Fin (N + 1) ↦
          u i ^ ((Pi.single (Fin.last N) (1 : ZMod 3) : Fin (N + 1) → ZMod 3) i).val) =
          fun _ ↦ 1 := by
        ext i; simp [Fin.init_def]
      rw [hinit, partialProd_one, one_mul, Pi.single_eq_same, ZMod.val_one, pow_one]
    | cast i =>
      have hinit : Fin.init (fun k : Fin (N + 1) ↦
          u k ^ ((Pi.single i.castSucc (1 : ZMod 3) : Fin (N + 1) → ZMod 3) k).val) =
          fun k ↦ (u ∘ Fin.castSucc) k ^
            ((Pi.single i (1 : ZMod 3) : Fin N → ZMod 3) k).val := by
        ext k; simp [Fin.init_def, Pi.single_apply, Fin.castSucc_inj]
      rw [hinit, partialProd_pow_single (u ∘ Fin.castSucc) i,
        Pi.single_eq_of_ne (M := fun _ : Fin (N + 1) ↦ ZMod 3) (Fin.castSucc_ne_last i).symm 1,
        ZMod.val_zero, pow_zero, mul_one]
      rfl

variable {A : Type*} [Semiring A] [Algebra ℂ A]

private theorem mul_partialProd_of_qcomm :
    ∀ {N : ℕ} {u : Fin N → A} {v : A} {φ : Fin N → ZMod 3},
      (∀ i : Fin N, v * u i =
        ((AddChar.zmodChar 3 cubeRootOfUnity_pow_three (2 * φ i) : ℂˣ) : ℂ) • (u i * v)) →
      ∀ b : Fin N → ZMod 3,
        v * Fin.partialProd (fun i ↦ u i ^ (b i).val) (Fin.last N) =
          ((AddChar.zmodChar 3 cubeRootOfUnity_pow_three (2 * ∑ i : Fin N, φ i * b i) : ℂˣ) : ℂ) •
            (Fin.partialProd (fun i ↦ u i ^ (b i).val) (Fin.last N) * v)
  | 0, _, _, _, _, _ => by simp
  | N + 1, u, v, φ, hφ, b => by
    have ih := mul_partialProd_of_qcomm (u := u ∘ Fin.castSucc) (φ := φ ∘ Fin.castSucc)
      (fun i ↦ hφ i.castSucc) (Fin.init b)
    have hsemi : SemiconjBy v (u (Fin.last N))
        (((AddChar.zmodChar 3 cubeRootOfUnity_pow_three (2 * φ (Fin.last N)) : ℂˣ) : ℂ) •
          u (Fin.last N)) := by
      simpa [SemiconjBy, smul_mul_assoc] using hφ (Fin.last N)
    have hlast : v * u (Fin.last N) ^ (b (Fin.last N)).val =
        ((AddChar.zmodChar 3 cubeRootOfUnity_pow_three
          (2 * φ (Fin.last N) * b (Fin.last N)) : ℂˣ) : ℂ) •
          (u (Fin.last N) ^ (b (Fin.last N)).val * v) := by
      have hp := (hsemi.pow_right (b (Fin.last N)).val).eq
      rw [smul_pow, smul_mul_assoc, ← Units.val_pow_eq_pow_val, ← AddChar.map_nsmul_eq_pow,
        nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm (b (Fin.last N))] at hp
      exact hp
    have hinit_fn : Fin.init (fun i ↦ u i ^ (b i).val) =
        fun i ↦ (u ∘ Fin.castSucc) i ^ (Fin.init b i).val := rfl
    rw [← Fin.succ_last, Fin.partialProd_succ, ← Fin.partialProd_init, hinit_fn, ← mul_assoc, ih,
      smul_mul_assoc, mul_assoc, hlast, mul_smul_comm, smul_smul, ← Units.val_mul,
      ← AddChar.map_add_eq_mul, ← mul_assoc]
    congr 3; rw [Fin.sum_univ_castSucc]; simp [Fin.init, mul_add]; ring

private theorem halfChainForm_succ (N : ℕ) (b a : Fin (N + 1) → ZMod 3) :
    halfChainForm (N + 1) b a =
      halfChainForm N (Fin.init b) (Fin.init a) +
        a (Fin.last N) *
          ∑ i : Fin N, (if (i : ℕ) + 1 = N then (1 : ZMod 3) else 0) * b i.castSucc := by
  unfold halfChainForm
  rw [Fin.sum_univ_castSucc,
    show (∑ j : Fin (N + 1),
        if (Fin.last N : ℕ) + 1 = (j : ℕ) then b (Fin.last N) * a j else 0) = 0 from
      Finset.sum_eq_zero fun j _ ↦ by simp [Fin.val_last, show ¬ N + 1 = (j : ℕ) by omega],
    add_zero]
  simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last, Finset.sum_add_distrib,
    Fin.init, Finset.mul_sum]
  congr 1; exact Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> ring

private theorem partialProd_mul_partialProd :
    ∀ {N : ℕ} (u : Fin N → A), (∀ j, u j ^ 3 = 1) →
      (∀ {i j : Fin N}, (i : ℕ) + 1 = j → u i * u j = (cubeRootOfUnity : ℂ) • (u j * u i)) →
      (∀ {i j : Fin N}, (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i → u i * u j = u j * u i) →
      ∀ a b : Fin N → ZMod 3,
      Fin.partialProd (fun i ↦ u i ^ (a i).val) (Fin.last N) *
          Fin.partialProd (fun i ↦ u i ^ (b i).val) (Fin.last N) =
        ((AddChar.zmodChar 3 cubeRootOfUnity_pow_three (2 * halfChainForm N b a) : ℂˣ) : ℂ) •
          Fin.partialProd (fun i ↦ u i ^ ((a + b) i).val) (Fin.last N)
  | 0, _, _, _, _, _, _ => by simp [halfChainForm]
  | N + 1, u, hcube, hadj, hdist, a, b => by
    have hqcomm : ∀ i : Fin N, u (Fin.last N) * u i.castSucc =
        ((AddChar.zmodChar 3 cubeRootOfUnity_pow_three
          (2 * if (i : ℕ) + 1 = N then (1 : ZMod 3) else 0) : ℂˣ) : ℂ) •
          (u i.castSucc * u (Fin.last N)) := fun i ↦ by
      split_ifs with hi
      · have h := congrArg
          (((AddChar.zmodChar 3 cubeRootOfUnity_pow_three 2 : ℂˣ) : ℂ) • ·)
          (hadj (i := i.castSucc) (j := Fin.last N) hi)
        have h21 : (cubeRootOfUnity : ℂ) ^ 2 * (cubeRootOfUnity : ℂ) = 1 := by
          rw [← pow_succ, coe_cubeRootOfUnity_pow_three]
        simpa [AddChar.zmodChar_apply, show (2 : ZMod 3).val = 2 by decide, smul_smul, h21]
          using h.symm
      · have hd : (i.castSucc : ℕ) + 2 ≤ (Fin.last N : ℕ) := by
          have := i.isLt; simp at hi ⊢; omega
        simp [hdist (Or.inr hd)]
    have hmulb := mul_partialProd_of_qcomm (u := u ∘ Fin.castSucc) hqcomm (Fin.init b)
    have hsemi : SemiconjBy
        (Fin.partialProd (fun i ↦ (u ∘ Fin.castSucc) i ^ (Fin.init b i).val) (Fin.last N))
        (((AddChar.zmodChar 3 cubeRootOfUnity_pow_three
          (2 * ∑ i : Fin N,
            (if (i : ℕ) + 1 = N then (1 : ZMod 3) else 0) * Fin.init b i) : ℂˣ) : ℂ) •
          u (Fin.last N))
        (u (Fin.last N)) := by
      simpa [SemiconjBy, smul_mul_assoc] using hmulb.symm
    have hcomm : u (Fin.last N) ^ (a (Fin.last N)).val *
          Fin.partialProd (fun i ↦ (u ∘ Fin.castSucc) i ^ (Fin.init b i).val) (Fin.last N) =
        ((AddChar.zmodChar 3 cubeRootOfUnity_pow_three
          (2 * (a (Fin.last N) * ∑ i : Fin N,
            (if (i : ℕ) + 1 = N then (1 : ZMod 3) else 0) * Fin.init b i)) : ℂˣ) : ℂ) •
          (Fin.partialProd (fun i ↦ (u ∘ Fin.castSucc) i ^ (Fin.init b i).val) (Fin.last N) *
            u (Fin.last N) ^ (a (Fin.last N)).val) := by
      have hp := (hsemi.pow_right (a (Fin.last N)).val).eq.symm
      rwa [smul_pow, mul_smul_comm, ← Units.val_pow_eq_pow_val, ← AddChar.map_nsmul_eq_pow,
        nsmul_eq_mul, ZMod.natCast_zmod_val, mul_left_comm] at hp
    have ih := partialProd_mul_partialProd (u ∘ Fin.castSucc) (fun j ↦ hcube j.castSucc)
      (fun h ↦ hadj h) (fun h ↦ hdist h) (Fin.init a) (Fin.init b)
    have hpow : u (Fin.last N) ^ (a (Fin.last N)).val * u (Fin.last N) ^ (b (Fin.last N)).val =
        u (Fin.last N) ^ ((a + b) (Fin.last N)).val := by
      rw [← pow_add, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hcube (Fin.last N))]
    have hinit : Fin.init (a + b) = Fin.init a + Fin.init b := by ext i; simp [Fin.init_def]
    have hinit_fn (x : Fin (N + 1) → ZMod 3) :
        Fin.init (fun i ↦ u i ^ (x i).val) = fun i ↦ (u ∘ Fin.castSucc) i ^ (Fin.init x i).val :=
      rfl
    simp only [← Fin.succ_last, Fin.partialProd_succ, ← Fin.partialProd_init, hinit_fn]
    rw [mul_assoc (Fin.partialProd _ _) (u (Fin.last N) ^ _),
      ← mul_assoc (u (Fin.last N) ^ _), hcomm, smul_mul_assoc, mul_smul_comm,
      mul_assoc (Fin.partialProd _ _), ← mul_assoc (Fin.partialProd _ _), ih, smul_mul_assoc,
      hpow, smul_smul, ← Units.val_mul, ← AddChar.map_add_eq_mul, halfChainForm_succ, hinit]
    refine congrArg
      (fun z ↦ ((AddChar.zmodChar 3 cubeRootOfUnity_pow_three z : ℂˣ) : ℂ) • _) ?_
    simp only [Fin.init]; ring

/-- **Universal property of `CubicTorus N` on site generators.** Any `N` elements `u : Fin N → A` of
a `ℂ`-algebra satisfying `u j ^ 3 = 1`, `u i * u_{i+1} = ω • (u_{i+1} * u i)`, and commuting at
distance `≥ 2` determine a `ℂ`-algebra homomorphism `CubicTorus N →ₐ[ℂ] A` sending `cubicSite N j`
to `u j`. -/
noncomputable def liftSite {N : ℕ} (u : Fin N → A)
    (hcube : ∀ j, u j ^ 3 = 1)
    (hadj : ∀ {i j : Fin N}, (i : ℕ) + 1 = j → u i * u j = (cubeRootOfUnity : ℂ) • (u j * u i))
    (hdist : ∀ {i j : Fin N}, (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i → u i * u j = u j * u i) :
    CubicTorus N →ₐ[ℂ] A :=
  TwistedMonoidAlgebra.lift
    (fun a ↦
      ((AddChar.zmodChar 3 cubeRootOfUnity_pow_three
        (halfChainForm N a.toAdd a.toAdd) : ℂˣ) : ℂ) •
        Fin.partialProd (fun i ↦ u i ^ (a.toAdd i).val) (Fin.last N))
    (by simp [partialProd_one, halfChainForm])
    (fun a b ↦ by
      rw [smul_mul_smul_comm, partialProd_mul_partialProd u hcube hadj hdist, smul_smul,
        smul_smul, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, cubicFactor,
        ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul,
        chainForm_eq_sub, toAdd_mul, halfChainForm_add_left, halfChainForm_add_right,
        halfChainForm_add_right]
      congr 3; apply sub_eq_zero.mp
      calc _ = (3 : ZMod 3) * (halfChainForm N b.toAdd a.toAdd -
              halfChainForm N a.toAdd b.toAdd) := by ring
        _ = 0 := by rw [show (3 : ZMod 3) = 0 by decide, zero_mul])

/-- `liftSite` sends each site unitary `cubicSite N j` to `u j`. -/
@[simp] theorem liftSite_cubicSite {N : ℕ} (u : Fin N → A) (hcube) (hadj) (hdist) (j : Fin N) :
    liftSite u hcube hadj hdist (cubicSite N j) = u j := by
  rw [liftSite, cubicSite_def, weyl_def, TwistedMonoidAlgebra.lift_of, toAdd_ofAdd,
    halfChainForm_single_single]
  simp only [Nat.add_one_ne_self, ↓reduceIte, AddChar.map_zero_eq_one, Units.val_one, one_smul]
  exact partialProd_pow_single u j

end UniversalProperty

/-- The site unitaries `cubicSite N` generate `CubicTorus N` as a `ℂ`-algebra. -/
theorem adjoin_range_cubicSite (N : ℕ) :
    Algebra.adjoin ℂ (Set.range (cubicSite N)) = ⊤ := by
  let S : Subalgebra ℂ (CubicTorus N) := Algebra.adjoin ℂ (Set.range (cubicSite N))
  have hsingle (j : Fin N) (r : ZMod 3) : weyl N (ofAdd (Pi.single j r)) ∈ S := by
    have hj : cubicSite N j ∈ S := Algebra.subset_adjoin (Set.mem_range_self j)
    rcases zmod3_cases r with rfl | rfl | rfl
    · rw [Pi.single_zero, ofAdd_zero, weyl_one]; exact S.one_mem
    · exact hj
    · rw [← cubicSite_sq]; exact S.pow_mem hj 2
  have hweyl (a : Multiplicative (Fin N → ZMod 3)) : weyl N a ∈ S := by
    have hsum : a.toAdd = ∑ j : Fin N, Pi.single j (a.toAdd j) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    rw [← ofAdd_toAdd a, hsum]
    induction (Finset.univ : Finset (Fin N)) using Finset.cons_induction with
    | empty => simp [S.one_mem]
    | cons j s _ ih =>
      rw [Finset.sum_cons, ofAdd_add]
      set u : Multiplicative (Fin N → ZMod 3) := ofAdd (Pi.single j (a.toAdd j))
      set v : Multiplicative (Fin N → ZMod 3) := ofAdd (∑ i ∈ s, Pi.single i (a.toAdd i))
      have hmul := S.smul_mem (S.mul_mem (hsingle j (a.toAdd j)) ih)
        (((cubicFactor N u v)⁻¹ : ℂˣ) : ℂ)
      rwa [weyl_mul_weyl, smul_smul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, one_smul] at hmul
  suffices ∀ x : CubicTorus N, x ∈ S from eq_top_iff.mpr fun x _ ↦ this x
  intro x
  induction (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3))
      (cubicFactor N)).mem_span x using Submodule.span_induction with
  | mem _ hy =>
    obtain ⟨a, rfl⟩ := hy
    rw [TwistedMonoidAlgebra.basis_apply, ← weyl_def]; exact hweyl a
  | zero => exact S.zero_mem
  | add _ _ _ _ hx hy => exact S.add_mem hx hy
  | smul _ _ _ hx => exact S.smul_mem hx _

/-- Two `ℂ`-algebra homomorphisms out of `CubicTorus N` agreeing on `cubicSite N` are equal. -/
theorem algHom_ext_cubicSite {N : ℕ} {A : Type*} [Semiring A] [Algebra ℂ A]
    {F G : CubicTorus N →ₐ[ℂ] A} (h : ∀ j : Fin N, F (cubicSite N j) = G (cubicSite N j)) :
    F = G :=
  AlgHom.ext_of_adjoin_eq_top (adjoin_range_cubicSite N) (by rintro _ ⟨j, rfl⟩; exact h j)

/-! ### Group inversion, the fixed subalgebra `C_N`, and its dimension `(3 ^ N + 1) / 2` -/

/-- **The inversion automorphism** `θ_N : W(a) ↦ W(a⁻¹)` of `CubicTorus N`. -/
noncomputable def cubicInversion (N : ℕ) : CubicTorus N →ₐ[ℂ] CubicTorus N :=
  TwistedMonoidAlgebra.mapDomain invMonoidHom (cubicFactor_inv_inv N)

theorem cubicInversion_def (N : ℕ) :
    cubicInversion N = TwistedMonoidAlgebra.mapDomain invMonoidHom (cubicFactor_inv_inv N) := (rfl)

@[simp] theorem cubicInversion_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicInversion N (weyl N a) = weyl N a⁻¹ :=
  TwistedMonoidAlgebra.mapDomain_of ..

@[simp] theorem cubicInversion_cubicInversion (N : ℕ) (x : CubicTorus N) :
    cubicInversion N (cubicInversion N x) = x :=
  AlgHom.congr_fun
    (TwistedMonoidAlgebra.algHom_ext (f := (cubicInversion N).comp (cubicInversion N))
      (g := AlgHom.id ℂ (CubicTorus N)) fun g ↦ by
        rw [AlgHom.comp_apply, AlgHom.id_apply, ← weyl_def, cubicInversion_weyl,
          cubicInversion_weyl, inv_inv]) x

theorem cubicAdjoint_cubicInversion (N : ℕ) (x : CubicTorus N) :
    cubicAdjoint N (cubicInversion N x) = cubicInversion N (cubicAdjoint N x) :=
  TwistedMonoidAlgebra.conjReverse_mapDomain invMonoidHom (cubicFactor_inv_inv N) x

@[simp] theorem cubicScalarCoefficient_cubicInversion (N : ℕ) (x : CubicTorus N) :
    cubicScalarCoefficient N (cubicInversion N x) = cubicScalarCoefficient N x :=
  TwistedMonoidAlgebra.scalarTrace_mapDomain_of_injective (cubicFactor_inv_inv N) inv_injective x

@[simp] theorem cubicInversion_cubicSite (N : ℕ) (j : Fin N) :
    cubicInversion N (cubicSite N j) = cubicSite N j ^ 2 := by
  nth_rw 1 [cubicSite_def]
  rw [cubicInversion_weyl, ← ofAdd_neg, ← Pi.single_neg, show (-1 : ZMod 3) = 2 by decide,
    ← cubicSite_sq]

/-- **The inversion-fixed subalgebra** `C_N = {x ∈ CubicTorus N | cubicInversion N x = x}`. -/
noncomputable def cubicFixed (N : ℕ) : Subalgebra ℂ (CubicTorus N) :=
  AlgHom.equalizer (cubicInversion N) (AlgHom.id ℂ (CubicTorus N))

@[simp] theorem mem_cubicFixed_iff {N : ℕ} {x : CubicTorus N} :
    x ∈ cubicFixed N ↔ cubicInversion N x = x := Iff.rfl

theorem cubicAdjoint_mem_cubicFixed {N : ℕ} {x : CubicTorus N} (hx : x ∈ cubicFixed N) :
    cubicAdjoint N x ∈ cubicFixed N := by
  rw [mem_cubicFixed_iff, ← cubicAdjoint_cubicInversion, mem_cubicFixed_iff.mp hx]

/-- Restriction of `cubicAdjoint N` to the inversion-fixed subalgebra `cubicFixed N`. -/
noncomputable def cubicFixedAdjoint (N : ℕ) : cubicFixed N →ₗ⋆[ℂ] cubicFixed N where
  toFun x := ⟨cubicAdjoint N x.val, cubicAdjoint_mem_cubicFixed x.property⟩
  map_add' x y := Subtype.ext (map_add (cubicAdjoint N) x.val y.val)
  map_smul' c x := Subtype.ext (map_smulₛₗ (cubicAdjoint N) c x.val)

@[simp] theorem coe_cubicFixedAdjoint (N : ℕ) (x : cubicFixed N) :
    (cubicFixedAdjoint N x : CubicTorus N) = cubicAdjoint N x := (rfl)

@[simp] theorem cubicFixedAdjoint_cubicFixedAdjoint (N : ℕ) (x : cubicFixed N) :
    cubicFixedAdjoint N (cubicFixedAdjoint N x) = x :=
  Subtype.ext (TwistedMonoidAlgebra.conjReverse_conjReverse x.val)

theorem cubicFixedAdjoint_mul (N : ℕ) (x y : cubicFixed N) :
    cubicFixedAdjoint N (x * y) = cubicFixedAdjoint N y * cubicFixedAdjoint N x :=
  Subtype.ext (cubicAdjoint_mul N x.val y.val)

/-- **Dimension of the inversion-fixed subalgebra**: `dim_ℂ (cubicFixed N) = (3 ^ N + 1) / 2`. -/
@[simp] theorem finrank_cubicFixed (N : ℕ) : Module.finrank ℂ (cubicFixed N) = (3 ^ N + 1) / 2 := by
  classical
  let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  let θ : Module.End ℂ (CubicTorus N) := (cubicInversion N).toLinearMap
  let f : Module.End ℂ (CubicTorus N) := 1 + θ
  have hsq : f * f = (2 : ℂ) • f := by
    ext x
    simp only [f, θ, mul_apply_eq_comp, _root_.LinearMap.add_apply, one_apply_eq_self,
      AlgHom.toLinearMap_apply, map_add, cubicInversion_cubicInversion, two_smul]
    abel_nf
  have hrange : _root_.LinearMap.range f = (cubicFixed N).toSubmodule := by
    ext x
    simp only [_root_.LinearMap.mem_range, Subalgebra.mem_toSubmodule, mem_cubicFixed_iff]
    exact ⟨fun ⟨y, hy⟩ ↦ by subst hy; simp [f, θ, add_comm],
      fun hx ↦ ⟨(2 : ℂ)⁻¹ • x, by simp [f, θ, hx, ← two_smul ℂ x]⟩⟩
  let σ : Equiv.Perm (Multiplicative (Fin N → ZMod 3)) := inv_involutive.toPerm Inv.inv
  have : Module.Finite ℂ (CubicTorus N) := Module.Finite.of_basis b
  have : Module.Free ℂ (CubicTorus N) := Module.Free.of_basis b
  have hmat : _root_.LinearMap.toMatrix b b θ = σ.permMatrix ℂ := by
    ext i j
    rw [_root_.LinearMap.toMatrix_apply, TwistedMonoidAlgebra.basis_apply]
    dsimp only [θ, σ, Equiv.Perm.permMatrix]
    rw [AlgHom.toLinearMap_apply, ← weyl_def, cubicInversion_weyl, weyl_def,
      TwistedMonoidAlgebra.repr_of, Finsupp.single_apply, PEquiv.toMatrix_apply]
    simp [Equiv.toPEquiv_apply, inv_eq_iff_eq_inv, eq_comm (a := i)]
  have hfix : Function.fixedPoints σ = {1} := by
    ext a
    simp only [Function.mem_fixedPoints_iff, σ, Set.mem_singleton_iff]
    refine ⟨fun h ↦ toAdd.injective (funext fun i ↦ ?_), fun h ↦ by simp [h]⟩
    have hi : -a.toAdd i = a.toAdd i := congrFun (congrArg toAdd h) i
    rw [ZMod.neg_eq_self_iff] at hi
    exact hi.resolve_right (by omega)
  have htrθ : _root_.LinearMap.trace ℂ (CubicTorus N) θ = 1 := by
    rw [_root_.LinearMap.trace_eq_matrix_trace ℂ b θ, hmat, Matrix.trace_permutation, hfix,
      Set.ncard_singleton, Nat.cast_one]
  have htr1 : _root_.LinearMap.trace ℂ (CubicTorus N) (1 : Module.End ℂ (CubicTorus N)) =
      (3 ^ N : ℂ) :=
    (_root_.LinearMap.trace_one (R := ℂ) (M := CubicTorus N)).trans
      (by rw [finrank_cubicTorus, Nat.cast_pow, Nat.cast_ofNat])
  have htr := TauCeti.LinearMap.trace_eq_mul_finrank_range (K := ℂ) (M := CubicTorus N) hsq
  rw [hrange] at htr
  dsimp only [f] at htr
  rw [map_add, htr1, htrθ] at htr
  have hnat : 3 ^ N + 1 = 2 * Module.finrank ℂ (cubicFixed N) := by exact_mod_cast htr
  omega

end TauCeti.TemperleyLieb
