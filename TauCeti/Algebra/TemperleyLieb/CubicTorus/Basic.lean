/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.LinearAlgebra.BilinearMap
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic
public import TauCeti.Algebra.TemperleyLieb.Basic
-- Private: these are used only inside proofs.
import TauCeti.Algebra.Ring.Idempotent.Basic
import TauCeti.Analysis.Complex.Sqrt

/-!
# The cubic quantum torus and the Temperley–Lieb algebra at `δ = √3`

At the loop parameter `δ = √3 = 2 cos (π / 6)`, Jones's parameter `t = exp (π i / 3)`, the
Temperley–Lieb algebras are related to a "cubic Clifford algebra" (Jones 1985, p. 107). This file
builds that algebra and the comparison map from the Temperley–Lieb algebra into it.

Let `ω = exp (2 π i / 3)` and let `B` be the alternating *chain form*
`B(a, b) = Σ_(j + 1 < N) (a_j b_(j+1) - a_(j+1) b_j)` on `V_N = Fin N → ZMod 3`. The factor set
`α(a, b) = ω ^ (2 B(a, b))` defines the twisted group algebra `G_N = CubicTorus N` of `V_N`, a cubic
quantum torus of complex dimension `3 ^ N`, with basis `W(a) = weyl N a` and multiplication
`W(a) W(b) = α(a, b) W(a + b)`. Its site unitaries `U_j = W(e_j)` satisfy `U_j ^ 3 = 1`,
`U_j U_(j+1) = ω U_(j+1) U_j`, and commute at distance at least two. The coefficient of `W(0) = 1`
is a trace `s_N` (`cubicScalarCoefficient`).

The elements `p_j = 3⁻¹ (1 + U_j + U_j ^ 2)` are idempotents with `p_i p_j p_i = 3⁻¹ p_i` for
adjacent `i, j`, and commute at distance at least two. Hence `e_j ↦ √3 p_j` defines an algebra map
`F_m = cubicHom m` from `TemperleyLieb ℂ √3 m` to `G_(m-1)`. The negation `a ↦ -a` induces an
involutive automorphism `θ_N = cubicInversion N` of `G_N` fixing every `p_j`, so `F_m` lands in the
fixed subalgebra `C_(m-1) = cubicFixed (m - 1)`, the inversion-fixed cubic quantum torus.

The strand inclusions and the identification of the Markov trace with `(√3) ^ m s_(m-1) ∘ F_m` are
in `TauCeti.Algebra.TemperleyLieb.CubicTorus.Trace`.

## Main definitions

* `TauCeti.TemperleyLieb.chainForm`: the alternating chain form on `Fin N → R`.
* `TauCeti.TemperleyLieb.cubeRootPow`: the character `x ↦ ω ^ x` of `ZMod 3` in `ℂˣ`.
* `TauCeti.TemperleyLieb.cubicFactor`, `TauCeti.TemperleyLieb.CubicTorus` and
  `TauCeti.TemperleyLieb.weyl`: the factor set `ω ^ (2 B)`, the cubic quantum torus `G_N` and its
  basis elements `W(a)`.
* `TauCeti.TemperleyLieb.cubicScalarCoefficient`: the coefficient of `1`, a trace on `G_N`.
* `TauCeti.TemperleyLieb.cubicSite` and `TauCeti.TemperleyLieb.cubicProjection`: the site unitaries
  `U_j` and the projections `p_j = 3⁻¹ (1 + U_j + U_j ^ 2)`.
* `TauCeti.TemperleyLieb.cubicInversion` and `TauCeti.TemperleyLieb.cubicFixed`: the inversion
  `W(a) ↦ W(-a)` and its fixed subalgebra `C_N`.
* `TauCeti.TemperleyLieb.cubicHom`: the comparison map
  `TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)`, `e j ↦ √3 p_j`.

## Main results

* `TauCeti.TemperleyLieb.finrank_cubicTorus`: `G_N` has dimension `3 ^ N`.
* `TauCeti.TemperleyLieb.weyl_mul_weyl_comm`: `W(a) W(b) = ω ^ B(a, b) W(b) W(a)`.
* `TauCeti.TemperleyLieb.cubicSite_pow_three`,
  `TauCeti.TemperleyLieb.cubicSite_mul_cubicSite_comm` and
  `TauCeti.TemperleyLieb.commute_cubicSite`: the relations of the site unitaries.
* `TauCeti.TemperleyLieb.cubicScalarCoefficient_mul_comm`: `s_N` is a trace.
* `TauCeti.TemperleyLieb.cubicProjection_mul_self`,
  `TauCeti.TemperleyLieb.cubicProjection_mul_cubicProjection_mul_cubicProjection` and
  `TauCeti.TemperleyLieb.commute_cubicProjection`: the Temperley–Lieb relations of the `p_j`
  at `δ = √3` after rescaling by `√3`.
* `TauCeti.TemperleyLieb.cubicInversion_cubicInversion` and
  `TauCeti.TemperleyLieb.cubicInversion_cubicProjection`: `θ_N` is an involution fixing every `p_j`.

## Implementation notes

The exponent of `ω` lives in `ZMod 3`, and `ω ^ x` is Mathlib's additive character
`ZMod.toCircle` of `ZMod 3`, read in `ℂˣ`; so `cubeRootPow` is additive by construction. The
factor `2` in `α = ω ^ (2 B)` (that is, `ω ^ (B / 2)` with `1 / 2 = 2` in `ZMod 3`) makes the
commutator `α(a, b) / α(b, a)` equal to `ω ^ B(a, b)`, so `U_j U_(j+1) = ω U_(j+1) U_j`; the
symmetric choice `ω ^ B` would give the relation for `ω⁻¹`.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111, p. 107.
* E. C. Rowell and H. Wenzl, *SO(N)_2 braid group representations are Gaussian*, Quantum Topol. 8
  (2017), §4 (quantum tori and the Temperley–Lieb algebras at `δ = √3`).
-/

public section

namespace TauCeti.TemperleyLieb

open TwistedMonoidAlgebra

/-! ### The chain form -/

section ChainForm

variable (R : Type*) [CommRing R] (N : ℕ)

/-- The **chain form** `B(a, b) = Σ_(j + 1 < N) (a_j b_(j+1) - a_(j+1) b_j)` on `Fin N → R`, the
alternating bilinear form pairing each coordinate with its successor. -/
noncomputable def chainForm : LinearMap.BilinForm R (Fin N → R) :=
  LinearMap.mk₂ R
    (fun a b ↦ ∑ i : Fin N, ∑ j : Fin N, if (i : ℕ) + 1 = j then a i * b j - a j * b i else 0)
    (fun a a' b ↦ by
      simp only [Pi.add_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      split_ifs <;> ring)
    (fun r a b ↦ by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      split_ifs <;> ring)
    (fun a b b' ↦ by
      simp only [Pi.add_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      split_ifs <;> ring)
    (fun r a b ↦ by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      split_ifs <;> ring)

variable {R N}

/-- Unfolding `chainForm` as a double sum over adjacent pairs of coordinates. -/
theorem chainForm_apply (a b : Fin N → R) :
    chainForm R N a b =
      ∑ i : Fin N, ∑ j : Fin N, if (i : ℕ) + 1 = j then a i * b j - a j * b i else 0 :=
  (rfl)

/-- The chain form is alternating. -/
@[simp]
theorem chainForm_self (a : Fin N → R) : chainForm R N a a = 0 := by
  simp [chainForm_apply, mul_comm]

/-- The chain form is antisymmetric. -/
theorem chainForm_swap (a b : Fin N → R) : chainForm R N b a = -chainForm R N a b := by
  simp only [chainForm_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> ring

/-- The chain form on coordinate vectors: `B(r e_i, s e_j)` is `r s` when `j = i + 1`, `-(r s)`
when `i = j + 1`, and `0` otherwise. -/
theorem chainForm_single_single (i j : Fin N) (r s : R) :
    chainForm R N (Pi.single i r) (Pi.single j s) =
      if (i : ℕ) + 1 = j then r * s else if (j : ℕ) + 1 = i then -(r * s) else 0 := by
  have hsplit (p : Prop) [Decidable p] (x y : R) :
      (if p then x - y else 0) = (if p then x else 0) - (if p then y else 0) := by
    split_ifs <;> simp
  simp only [chainForm_apply, hsplit, Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i (fun i' _ hi' ↦ by simp [hi']) (by simp),
    Finset.sum_eq_single j (fun j' _ hj' ↦ by simp [hj']) (by simp),
    Finset.sum_eq_single j (fun i' _ hi' ↦ by simp [hi']) (by simp),
    Finset.sum_eq_single i (fun j' _ hj' ↦ by simp [hj']) (by simp)]
  simp only [Pi.single_eq_same]
  split_ifs <;> first | (exfalso; omega) | ring

/-- Extending both vectors by a zero last coordinate does not change the chain form. -/
@[simp]
theorem chainForm_snoc_zero (a b : Fin N → R) :
    chainForm R (N + 1) (Fin.snoc a 0) (Fin.snoc b 0) = chainForm R N a b := by
  simp [chainForm_apply, Fin.sum_univ_castSucc]

end ChainForm

/-! ### Cube roots of unity -/

/-- The character `x ↦ ω ^ x` of `ZMod 3` with values in `ℂˣ`, where `ω = exp (2 π i / 3)`:
Mathlib's additive character `ZMod.toCircle` of `ZMod 3`, read in the units of `ℂ`. -/
noncomputable def cubeRootPow : AddChar (ZMod 3) ℂˣ :=
  Circle.toUnits.compAddChar ZMod.toCircle

/-- The values of `cubeRootPow` in `ℂ` are those of Mathlib's standard additive character. -/
theorem coe_cubeRootPow (x : ZMod 3) : (cubeRootPow x : ℂ) = ZMod.stdAddChar x := by
  simp [cubeRootPow, ZMod.stdAddChar_apply]

/-- For `x ≠ 0` in `ZMod 3`, `ω ^ x` is a primitive cube root of unity:
`1 + ω ^ x + (ω ^ x) ^ 2 = 0`. -/
theorem one_add_cubeRootPow_add_sq {x : ZMod 3} (hx : x ≠ 0) :
    1 + (cubeRootPow x : ℂ) + (cubeRootPow x : ℂ) ^ 2 = 0 := by
  have h := AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar 3 hx)
  have h3 : ∀ f : ZMod 3 → ℂ, ∑ a, f a = f 0 + f 1 + f 2 := fun f ↦ Fin.sum_univ_three f
  rw [h3] at h
  simp only [coe_cubeRootPow]
  convert h using 2
  · simp
  · rw [AddChar.mulShift_apply, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, Nat.cast_ofNat,
      mul_comm]

/-! ### The cubic quantum torus -/

section CubicTorus

variable (N : ℕ)

/-- The factor set `α(a, b) = ω ^ (2 B(a, b))` of the cubic quantum torus, for the chain form `B`
on `Fin N → ZMod 3`. -/
noncomputable def cubicFactor (a b : Multiplicative (Fin N → ZMod 3)) : ℂˣ :=
  cubeRootPow (2 * chainForm (ZMod 3) N a.toAdd b.toAdd)

/-- `cubicFactor N` is a normalized factor set: the cocycle identity is the biadditivity of the
chain form, and the normalization is `B(0, b) = 0`. -/
instance : IsFactorSet (cubicFactor N) where
  cocycle g h j := by
    simp only [cubicFactor, toAdd_mul, map_add, LinearMap.add_apply, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  one_left g := by simp [cubicFactor]

/-- **The cubic quantum torus** `G_N`: the twisted group algebra of `Fin N → ZMod 3` for the factor
set `cubicFactor N`. -/
noncomputable abbrev CubicTorus :=
  twistedMonoidAlgebra ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)

/-- The basis element `W(a)` of the cubic quantum torus at `a : Fin N → ZMod 3`. -/
noncomputable def weyl (a : Fin N → ZMod 3) : CubicTorus N :=
  of (Multiplicative.ofAdd a)

/-- The cubic quantum torus `G_N` has dimension `3 ^ N`. -/
@[simp]
theorem finrank_cubicTorus : Module.finrank ℂ (CubicTorus N) = 3 ^ N := by
  rw [finrank_eq_natCard, Nat.card_eq_fintype_card]
  simp

variable {N}

theorem cubicFactor_apply (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a b = cubeRootPow (2 * chainForm (ZMod 3) N a.toAdd b.toAdd) :=
  (rfl)

theorem weyl_def (a : Fin N → ZMod 3) : weyl N a = of (Multiplicative.ofAdd a) :=
  (rfl)

/-- The basis elements of the twisted group algebra `CubicTorus N` are the `weyl N a`. -/
theorem of_eq_weyl (g : Multiplicative (Fin N → ZMod 3)) :
    (of g : CubicTorus N) = weyl N g.toAdd :=
  (rfl)

@[simp]
theorem weyl_zero : weyl N 0 = 1 := by
  simp [weyl]

/-- The multiplication table of the cubic quantum torus: `W(a) W(b) = ω ^ (2 B(a, b)) W(a + b)`. -/
@[simp]
theorem weyl_mul_weyl (a b : Fin N → ZMod 3) :
    weyl N a * weyl N b = (cubeRootPow (2 * chainForm (ZMod 3) N a b) : ℂ) • weyl N (a + b) := by
  simp [weyl, cubicFactor]

/-- The basis elements commute up to the phase `ω ^ B(a, b)`:
`W(a) W(b) = ω ^ B(a, b) W(b) W(a)`. -/
theorem weyl_mul_weyl_comm (a b : Fin N → ZMod 3) :
    weyl N a * weyl N b =
      (cubeRootPow (chainForm (ZMod 3) N a b) : ℂ) • (weyl N b * weyl N a) := by
  rw [weyl_mul_weyl, weyl_mul_weyl, smul_smul, ← Units.val_mul, ← AddChar.map_add_eq_mul,
    chainForm_swap a b, add_comm b]
  congr 3
  have h3 : (3 : ZMod 3) = 0 := rfl
  linear_combination chainForm (ZMod 3) N a b * h3

/-- Powers of a basis element: `W(a) ^ n = W(n • a)`, since the chain form is alternating. -/
@[simp]
theorem weyl_pow (a : Fin N → ZMod 3) (n : ℕ) : weyl N a ^ n = weyl N (n • a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [pow_succ, ih, succ_nsmul, -nsmul_eq_mul]

/-! ### The scalar coefficient -/

variable (N) in
/-- The **scalar coefficient** `s_N`: the coefficient of the basis element `W(0) = 1` of `G_N`.
It is a trace (`cubicScalarCoefficient_mul_comm`). -/
noncomputable def cubicScalarCoefficient : CubicTorus N →ₗ[ℂ] ℂ :=
  (basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)).coord 1

theorem cubicScalarCoefficient_apply (x : CubicTorus N) :
    cubicScalarCoefficient N x =
      (basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)).repr x 1 :=
  (rfl)

@[simp]
theorem cubicScalarCoefficient_weyl (a : Fin N → ZMod 3) :
    cubicScalarCoefficient N (weyl N a) = if a = 0 then 1 else 0 := by
  classical
  simp [cubicScalarCoefficient, weyl, Finsupp.single_apply]

@[simp]
theorem cubicScalarCoefficient_one : cubicScalarCoefficient N 1 = 1 := by
  simpa using cubicScalarCoefficient_weyl (N := N) 0

/-- The scalar coefficient is a trace. -/
theorem cubicScalarCoefficient_mul_comm (x y : CubicTorus N) :
    cubicScalarCoefficient N (x * y) = cubicScalarCoefficient N (y * x) :=
  repr_mul_apply_one_comm x y

/-- The scalar coefficient of a product of two basis elements: `s(W(a) W(b))` is `1` when
`a + b = 0` and `0` otherwise. -/
theorem cubicScalarCoefficient_weyl_mul_weyl (a b : Fin N → ZMod 3) :
    cubicScalarCoefficient N (weyl N a * weyl N b) = if a + b = 0 then 1 else 0 := by
  rw [weyl_mul_weyl, map_smul, cubicScalarCoefficient_weyl, smul_eq_mul]
  split_ifs with h
  · simp [eq_neg_of_add_eq_zero_right h]
  · rw [mul_zero]

/-! ### Site unitaries and projections -/

variable (N) in
/-- The **site unitary** `U_j = W(e_j)` of the cubic quantum torus. -/
noncomputable def cubicSite (j : Fin N) : CubicTorus N :=
  weyl N (Pi.single j 1)

theorem cubicSite_def (j : Fin N) : cubicSite N j = weyl N (Pi.single j 1) :=
  (rfl)

theorem cubicSite_pow (j : Fin N) (n : ℕ) :
    cubicSite N j ^ n = weyl N (Pi.single j (n : ZMod 3)) := by
  rw [cubicSite, weyl_pow, ← Pi.single_smul, nsmul_eq_mul, mul_one]

@[simp]
theorem cubicSite_pow_three (j : Fin N) : cubicSite N j ^ 3 = 1 := by
  rw [cubicSite_pow, show ((3 : ℕ) : ZMod 3) = 0 from rfl, Pi.single_zero, weyl_zero]

/-- The commutation relation of the site unitaries: `U_i U_j = ω U_j U_i` when `j = i + 1`,
`U_i U_j = ω⁻¹ U_j U_i` when `i = j + 1`, and `U_i` and `U_j` commute otherwise. -/
theorem cubicSite_mul_cubicSite_comm (i j : Fin N) :
    cubicSite N i * cubicSite N j =
      (cubeRootPow (if (i : ℕ) + 1 = j then 1 else if (j : ℕ) + 1 = i then -1 else 0) : ℂ) •
        (cubicSite N j * cubicSite N i) := by
  rw [cubicSite, cubicSite, weyl_mul_weyl_comm, chainForm_single_single, mul_one]

/-- Site unitaries at distance at least two commute. -/
theorem commute_cubicSite {i j : Fin N} (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (cubicSite N i) (cubicSite N j) := by
  have h₁ : ¬(i : ℕ) + 1 = j := by omega
  have h₂ : ¬(j : ℕ) + 1 = i := by omega
  rw [Commute, SemiconjBy, cubicSite_mul_cubicSite_comm]
  simp [h₁, h₂]

variable (N) in
/-- The **cubic projection** `p_j = 3⁻¹ (1 + U_j + U_j ^ 2)`, the spectral projection of `U_j` for
the eigenvalue `1`. -/
noncomputable def cubicProjection (j : Fin N) : CubicTorus N :=
  (3 : ℂ)⁻¹ • (1 + cubicSite N j + cubicSite N j ^ 2)

theorem cubicProjection_def (j : Fin N) :
    cubicProjection N j = (3 : ℂ)⁻¹ • (1 + cubicSite N j + cubicSite N j ^ 2) :=
  (rfl)

@[simp]
theorem cubicScalarCoefficient_cubicProjection (j : Fin N) :
    cubicScalarCoefficient N (cubicProjection N j) = (3 : ℂ)⁻¹ := by
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  rw [cubicProjection_def, cubicSite_pow, cubicSite]
  simp [Pi.single_eq_zero_iff, h2]

/-- The cubic projections are idempotents. -/
@[simp]
theorem cubicProjection_mul_self (j : Fin N) :
    cubicProjection N j * cubicProjection N j = cubicProjection N j := by
  rw [cubicProjection_def, smul_mul_smul_comm,
    TauCeti.one_add_add_sq_mul_self_of_pow_three_eq_one (cubicSite_pow_three j),
    ← map_ofNat (algebraMap ℂ (CubicTorus N)) 3, ← Algebra.smul_def, smul_smul]
  norm_num

/-- Adjacent cubic projections satisfy `p_i p_j p_i = 3⁻¹ p_i`. -/
theorem cubicProjection_mul_cubicProjection_mul_cubicProjection {i j : Fin N}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    cubicProjection N i * cubicProjection N j * cubicProjection N i =
      (3 : ℂ)⁻¹ • cubicProjection N i := by
  -- `U_j U_i = ω ^ x U_i U_j` with `x = ±1`, and `ω ^ x` is a primitive cube root of unity.
  set x : ZMod 3 := if (j : ℕ) + 1 = i then 1 else if (i : ℕ) + 1 = j then -1 else 0 with hx
  have hx0 : x ≠ 0 := by
    rcases h with h | h
    · have h' : ¬(j : ℕ) + 1 = i := by omega
      simp [hx, h, h']
    · simp [hx, h]
  have hji : cubicSite N j * cubicSite N i =
      (cubeRootPow x : ℂ) • (cubicSite N i * cubicSite N j) :=
    cubicSite_mul_cubicSite_comm j i
  rw [cubicProjection_def, cubicProjection_def, smul_mul_smul_comm, smul_mul_smul_comm,
    TauCeti.one_add_add_sq_mul_one_add_add_sq_mul_one_add_add_sq_of_pow_three_eq_one
      (one_add_cubeRootPow_add_sq hx0) (cubicSite_pow_three i) hji,
    ← map_ofNat (algebraMap ℂ (CubicTorus N)) 3, ← Algebra.smul_def, smul_smul, smul_smul]
  norm_num

/-- Cubic projections at distance at least two commute. -/
theorem commute_cubicProjection {i j : Fin N} (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (cubicProjection N i) (cubicProjection N j) := by
  have hc := commute_cubicSite (N := N) h
  have h₁ : Commute (1 + cubicSite N i + cubicSite N i ^ 2) (cubicSite N j) :=
    ((Commute.one_left _).add_left hc).add_left (hc.pow_left 2)
  have h₂ : Commute (1 + cubicSite N i + cubicSite N i ^ 2)
      (1 + cubicSite N j + cubicSite N j ^ 2) :=
    ((Commute.one_right _).add_right h₁).add_right (h₁.pow_right 2)
  rw [cubicProjection_def, cubicProjection_def]
  exact (h₂.smul_left _).smul_right _

/-! ### The inversion and its fixed subalgebra -/

variable (N) in
/-- The **inversion** `θ_N : W(a) ↦ W(-a)` of the cubic quantum torus, an algebra map since the
chain form satisfies `B(-a, -b) = B(a, b)`. It is an involution
(`cubicInversion_cubicInversion`). -/
noncomputable def cubicInversion : CubicTorus N →ₐ[ℂ] CubicTorus N :=
  TwistedMonoidAlgebra.lift (fun g ↦ weyl N (-g.toAdd)) (by simp) fun g h ↦ by
    rw [weyl_mul_weyl, LinearMap.map_neg₂, map_neg, neg_neg, toAdd_mul, neg_add,
      cubicFactor_apply]

@[simp]
theorem cubicInversion_weyl (a : Fin N → ZMod 3) : cubicInversion N (weyl N a) = weyl N (-a) :=
  TwistedMonoidAlgebra.lift_of _ _ _ _

/-- The inversion is an involution. -/
@[simp]
theorem cubicInversion_cubicInversion (x : CubicTorus N) :
    cubicInversion N (cubicInversion N x) = x := by
  have h : (cubicInversion N).comp (cubicInversion N) = AlgHom.id ℂ (CubicTorus N) :=
    algHom_ext fun g ↦ by simp [of_eq_weyl]
  exact AlgHom.congr_fun h x

/-- The inversion sends `U_j` to `U_j ^ 2 = U_j⁻¹`. -/
@[simp]
theorem cubicInversion_cubicSite (j : Fin N) :
    cubicInversion N (cubicSite N j) = cubicSite N j ^ 2 := by
  rw [cubicSite_pow, cubicSite, cubicInversion_weyl, ← Pi.single_neg,
    show (-1 : ZMod 3) = ((2 : ℕ) : ZMod 3) by decide]

/-- The inversion fixes every cubic projection. -/
@[simp]
theorem cubicInversion_cubicProjection (j : Fin N) :
    cubicInversion N (cubicProjection N j) = cubicProjection N j := by
  have h4 : cubicSite N j ^ 4 = cubicSite N j := by
    rw [pow_succ, cubicSite_pow_three, one_mul]
  simp [cubicProjection_def, ← pow_mul, h4, add_right_comm]

variable (N) in
/-- **The inversion-fixed cubic quantum torus** `C_N`, the subalgebra of `G_N` fixed by
`cubicInversion N`. -/
noncomputable def cubicFixed : Subalgebra ℂ (CubicTorus N) :=
  AlgHom.equalizer (cubicInversion N) (AlgHom.id ℂ (CubicTorus N))

@[simp]
theorem mem_cubicFixed {x : CubicTorus N} : x ∈ cubicFixed N ↔ cubicInversion N x = x :=
  AlgHom.mem_equalizer _ _ x

theorem cubicProjection_mem_cubicFixed (j : Fin N) : cubicProjection N j ∈ cubicFixed N :=
  mem_cubicFixed.2 (cubicInversion_cubicProjection j)

end CubicTorus

/-! ### The comparison map at `δ = √3` -/

section ComparisonMap

/-- The `j`-th Temperley–Lieb generator `√3 p_j`, bundled as an element of `cubicFixed (m - 1)`. -/
private noncomputable def cubicGenerator (m : ℕ) (j : Fin (m - 1)) : cubicFixed (m - 1) :=
  ⟨(Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j,
    Subalgebra.smul_mem _ (cubicProjection_mem_cubicFixed j) _⟩

/-- The **cubic comparison map** `F_m : TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)`,
sending the generator `e j` to `√3 p_j`. -/
noncomputable def cubicHom (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1) :=
  lift (cubicGenerator m)
    (fun i ↦ Subtype.ext <| by
      simp only [Subalgebra.coe_mul, SetLike.val_smul, cubicGenerator, smul_mul_smul_comm,
        cubicProjection_mul_self, smul_smul])
    (fun {i j} h ↦ Subtype.ext <| by
      simp only [Subalgebra.coe_mul, cubicGenerator, smul_mul_assoc, mul_smul_comm,
        cubicProjection_mul_cubicProjection_mul_cubicProjection h, smul_smul]
      congr 1
      linear_combination (norm := skip)
        ((Real.sqrt 3 : ℂ) / 3) * Complex.mul_self_ofReal_sqrt zero_le_three
      push_cast
      ring)
    (fun {i j} h ↦ Subtype.ext <| by
      simp only [Subalgebra.coe_mul, cubicGenerator]
      exact ((commute_cubicProjection h).smul_left _ |>.smul_right _).eq)

/-- The cubic comparison map on the generators, in the ambient cubic quantum torus. -/
@[simp]
theorem coe_cubicHom_e (m : ℕ) (j : Fin (m - 1)) :
    (cubicHom m (e (Real.sqrt 3 : ℂ) j) : CubicTorus (m - 1)) =
      (Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j := by
  simp [cubicHom, cubicGenerator]

end ComparisonMap

end TauCeti.TemperleyLieb
