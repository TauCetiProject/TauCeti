/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.ZMod.Basic
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Star
public import TauCeti.Algebra.TemperleyLieb.Star
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.FinCases

/-!
# The cubic quantum torus representation of the Temperley–Lieb algebra at `δ = √3`

At the loop parameter `δ = √3 = 2 cos (π / 6)` — corresponding to Jones index `δ² = 3` — the
Temperley–Lieb algebra `TemperleyLieb ℂ (√3 : ℂ) m` surjects via a `⋆`-algebra homomorphism
`F_m = cubicFixedHom m` onto the inversion-fixed subalgebra `cubicFixed (m - 1)` of the cubic
quantum torus `CubicTorus (m - 1)` of dimension `3 ^ (m - 1)`.

Concretely, let `chainForm N` be the alternating biadditive form
`B(a, b) = ∑_{j < N - 1} (a_j b_{j + 1} - b_j a_{j + 1})` on `Fin N → ZMod 3`, let
`ω = cubeRootOfUnity = exp (2 π i / 3)`, and let `cubicFactor N` be the unitary normalized
factor set `α(a, b) = ω ^ (2 B(a, b))` on `Multiplicative (Fin N → ZMod 3)`. The twisted group
algebra `CubicTorus N = twistedMonoidAlgebra ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)`
has basis `W(a) = weyl N a`, complex dimension `3 ^ N`, canonical star structure `star (W(a)) =
W(-a)`, and inversion automorphism `θ_N = cubicInversion N` sending `W(a) ↦ W(-a)`. Its fixed-point
star subalgebra `cubicFixed N` has complex dimension `(3 ^ N + 1) / 2`.

The site unitaries `U_j = cubicSite N j = W(e_j)` satisfy `U_j ^ 3 = 1`,
`U_j * U_{j + 1} = ω • (U_{j + 1} * U_j)`, and commute at distance at least two. The projections

  `cubicProjection N j = 3⁻¹ • (1 + U_j + U_j ^ 2)`

lie in `cubicFixed N`, are self-adjoint idempotents, satisfy `p_i * p_j * p_i = 3⁻¹ • p_i` for
`|i - j| = 1`, and commute for `|i - j| ≥ 2`. Rescaling by `√3` therefore defines the `⋆`-algebra
homomorphism `cubicFixedHom m : TemperleyLieb ℂ (√3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1)` sending
`e (√3 : ℂ) j ↦ (√3 : ℂ) • p_j`.

* **Surjectivity**: the symmetric combinations `C(a) = W(a) + W(-a)` span `cubicFixed N` and satisfy
  `C(u) * C(v) = α(u, v) • C(u + v) + α(u, v)⁻¹ • C(u - v)`. Whenever `B(u, v) ≠ 0`, the two
  products `C(u) * C(v)` and `C(v) * C(u)` form an invertible `2 × 2` system recovering both
  `C(u + v)` and `C(u - v)`. Induction on the support length of `a` then shows that the elements
  `C(e_j) = 3 • p_j - 1` generate `cubicFixed N`, so `cubicFixedHom m` is surjective for every `m`.

Coordinate inclusions, the Markov trace identity, the identification of the Jones quotient at
`δ = √3` with `cubicFixed (m - 1)`, and vanishing of `jonesWenzl (√3 : ℂ) 5` are established in
`TauCeti.Algebra.TemperleyLieb.CubicTorus.Quotient`. The Gaussian braid representation and its
finiteness are established in `TauCeti.Algebra.TemperleyLieb.CubicTorus.GaussianBraid`.

## Main definitions

* `TauCeti.TemperleyLieb.chainForm`: the alternating chain form `B` on `Fin N → ZMod 3`.
* `TauCeti.TemperleyLieb.cubeRootOfUnity` and `TauCeti.TemperleyLieb.cubeRootPow`: `ω = exp(2πi/3)`
  and `x ↦ ω ^ x.val` on `ZMod 3`.
* `TauCeti.TemperleyLieb.cubicFactor` and `TauCeti.TemperleyLieb.CubicTorus`: the unitary factor
  set `α(a, b) = ω ^ (2 B(a, b))` and the cubic quantum torus `G_N`.
* `TauCeti.TemperleyLieb.weyl`, `TauCeti.TemperleyLieb.cubicInversion`, and
  `TauCeti.TemperleyLieb.cubicFixed`: the Weyl basis `W(a)`, inversion `θ_N`, and inversion-fixed
  star subalgebra `C_N`.
* `TauCeti.TemperleyLieb.cubicSite` and `TauCeti.TemperleyLieb.cubicProjection`: the site
  unitaries `U_j` and Temperley–Lieb projections `p_j`.
* `TauCeti.TemperleyLieb.cubicFixedHom`: the surjective `⋆`-algebra comparison map
  `TemperleyLieb ℂ (√3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1)`.

## Main results

* `TauCeti.TemperleyLieb.finrank_cubicTorus` and `TauCeti.TemperleyLieb.finrank_cubicFixed`:
  `finrank ℂ (CubicTorus N) = 3 ^ N` and `finrank ℂ (cubicFixed N) = (3 ^ N + 1) / 2`.
* `TauCeti.TemperleyLieb.cubicProjection_mul_self`,
  `TauCeti.TemperleyLieb.cubicProjection_mul_cubicProjection_mul_cubicProjection`, and
  `TauCeti.TemperleyLieb.cubicProjection_mul_cubicProjection_comm`: the Jones projection relations.
* `TauCeti.TemperleyLieb.cubicFixedHom_surjective`: surjectivity of `cubicFixedHom m` for every
  `m : ℕ`.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111, p. 107.
* C. Galindo and E. C. Rowell, *Braid representations from unitary braided vector spaces*,
  J. Math. Phys. 55 (2014), 061702.
* E. C. Rowell and H. Wenzl, *SO(N)_2 braid group representations are Gaussian*, Quantum Topol. 8
  (2017), no. 1, 1–33.
-/

public section

namespace TauCeti.TemperleyLieb

/-! ### Arithmetic helpers for `√3` and `ω = exp (2 π i / 3)` -/

/-- Registers `IsSelfAdjoint (Real.sqrt 3 : ℂ)` as a `Fact` so that
`TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m` carries the analytic adjoint instances
`TemperleyLieb.instStarRing` and `TemperleyLieb.instStarModule`. -/
instance : Fact (IsSelfAdjoint (Real.sqrt 3 : ℂ)) :=
  ⟨Complex.conj_ofReal _⟩

private theorem sqrt_three_coe_mul_self :
    (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
  exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)

/-- The alternating chain form `B(a, b) = ∑_{j < N - 1} (a_j b_{j + 1} - b_j a_{j + 1})` on
`Fin N → ZMod 3`. -/
def chainForm (N : ℕ) (a b : Fin N → ZMod 3) : ZMod 3 :=
  ∑ i : Fin N, ∑ j : Fin N, if (i : ℕ) + 1 = j then a i * b j - b i * a j else 0

/-- Unfolding `chainForm`. -/
theorem chainForm_def (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N a b =
      ∑ i : Fin N, ∑ j : Fin N, if (i : ℕ) + 1 = j then a i * b j - b i * a j else 0 := (rfl)

/-- `chainForm N` is additive in its first argument. -/
theorem chainForm_add_left (N : ℕ) (a b c : Fin N → ZMod 3) :
    chainForm N (a + b) c = chainForm N a c + chainForm N b c := by
  simp only [chainForm_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Pi.add_apply]
  split_ifs <;> ring

/-- `chainForm N` is additive in its second argument. -/
theorem chainForm_add_right (N : ℕ) (a b c : Fin N → ZMod 3) :
    chainForm N a (b + c) = chainForm N a b + chainForm N a c := by
  simp only [chainForm_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Pi.add_apply]
  split_ifs <;> ring

/-- `chainForm N` is homogeneous in its first argument. -/
theorem chainForm_smul_left (N : ℕ) (r : ZMod 3) (a b : Fin N → ZMod 3) :
    chainForm N (r • a) b = r * chainForm N a b := by
  simp only [chainForm_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- `chainForm N` is homogeneous in its second argument. -/
theorem chainForm_smul_right (N : ℕ) (r : ZMod 3) (a b : Fin N → ZMod 3) :
    chainForm N a (r • b) = r * chainForm N a b := by
  simp only [chainForm_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- `chainForm N` vanishes when its first argument is zero. -/
@[simp]
theorem chainForm_zero_left (N : ℕ) (b : Fin N → ZMod 3) :
    chainForm N 0 b = 0 := by
  simp [chainForm_def]

/-- `chainForm N` vanishes when its second argument is zero. -/
@[simp]
theorem chainForm_zero_right (N : ℕ) (a : Fin N → ZMod 3) :
    chainForm N a 0 = 0 := by
  simp [chainForm_def]

/-- `chainForm N` is alternating. -/
@[simp]
theorem chainForm_self (N : ℕ) (a : Fin N → ZMod 3) :
    chainForm N a a = 0 := by
  simp only [chainForm_def]
  refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ ?_
  split_ifs <;> ring

/-- `chainForm N` is skew-symmetric. -/
theorem chainForm_swap (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N b a = -chainForm N a b := by
  simp only [chainForm_def, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> ring

/-- Negating the first argument negates `chainForm N`. -/
@[simp]
theorem chainForm_neg_left (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N (-a) b = -chainForm N a b := by
  simpa using chainForm_smul_left N (-1) a b

/-- Negating the second argument negates `chainForm N`. -/
@[simp]
theorem chainForm_neg_right (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N a (-b) = -chainForm N a b := by
  simpa using chainForm_smul_right N (-1) a b

/-- Negating both arguments preserves `chainForm N`. -/
theorem chainForm_neg_neg (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N (-a) (-b) = chainForm N a b := by
  simp

/-- `chainForm N` evaluated against the `k`-th standard basis vector `Pi.single k 1` is the
difference of the preceding and succeeding coordinates of `a`. -/
theorem chainForm_single_right {N : ℕ} (a : Fin N → ZMod 3) (k : Fin N) :
    chainForm N a (Pi.single k 1) =
      (if h : 0 < k.val then a ⟨k.val - 1, by omega⟩ else 0) -
        (if h : k.val + 1 < N then a ⟨k.val + 1, h⟩ else 0) := by
  have h1 :
      (∑ i : Fin N, ∑ j : Fin N,
          if (i : ℕ) + 1 = j then a i * (Pi.single k (1 : ZMod 3) : Fin N → ZMod 3) j else 0) =
        if h : 0 < k.val then a ⟨k.val - 1, by omega⟩ else 0 := by
    rw [Finset.sum_comm]
    calc
      ∑ j : Fin N, ∑ i : Fin N,
          (if (i : ℕ) + 1 = j then a i * (Pi.single k (1 : ZMod 3) : Fin N → ZMod 3) j else 0)
        = ∑ i : Fin N, (if (i : ℕ) + 1 = k then a i * 1 else 0) := by
            rw [Finset.sum_eq_single k]
            · simp
            · intro j _ hj
              refine Finset.sum_eq_zero fun i _ ↦ ?_
              simp [Pi.single_eq_of_ne hj]
            · intro hk; exact absurd (Finset.mem_univ k) hk
      _ = if h : 0 < k.val then a ⟨k.val - 1, by omega⟩ else 0 := by
            split_ifs with hk
            · rw [Finset.sum_eq_single ⟨k.val - 1, by omega⟩]
              · simp [Nat.sub_add_cancel hk]
              · intro i _ hi
                have hne : (i : ℕ) + 1 ≠ k.val := by
                  intro h
                  apply hi
                  ext
                  dsimp
                  omega
                simp [hne]
              · intro h; exact absurd (Finset.mem_univ _) h
            · refine Finset.sum_eq_zero fun i _ ↦ ?_
              have hne : (i : ℕ) + 1 ≠ k.val := by omega
              simp [hne]
  have h2 :
      (∑ i : Fin N, ∑ j : Fin N,
          if (i : ℕ) + 1 = j then (Pi.single k (1 : ZMod 3) : Fin N → ZMod 3) i * a j else 0) =
        if h : k.val + 1 < N then a ⟨k.val + 1, h⟩ else 0 := by
    calc
      ∑ i : Fin N, ∑ j : Fin N,
          (if (i : ℕ) + 1 = j then (Pi.single k (1 : ZMod 3) : Fin N → ZMod 3) i * a j else 0)
        = ∑ j : Fin N, (if (k : ℕ) + 1 = j then 1 * a j else 0) := by
            rw [Finset.sum_eq_single k]
            · simp
            · intro i _ hi
              refine Finset.sum_eq_zero fun j _ ↦ ?_
              simp [Pi.single_eq_of_ne hi]
            · intro hk; exact absurd (Finset.mem_univ k) hk
      _ = if h : k.val + 1 < N then a ⟨k.val + 1, h⟩ else 0 := by
            split_ifs with hk
            · rw [Finset.sum_eq_single ⟨k.val + 1, hk⟩]
              · simp
              · intro j _ hj
                have hne : (k : ℕ) + 1 ≠ j.val := by
                  intro h
                  apply hj
                  ext
                  dsimp
                  omega
                simp [hne]
              · intro h; exact absurd (Finset.mem_univ _) h
            · refine Finset.sum_eq_zero fun j _ ↦ ?_
              have hne : (k : ℕ) + 1 ≠ j.val := by omega
              simp [hne]
  rw [chainForm_def, ← h1, ← h2]
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> ring

/-- On adjacent standard basis vectors `i + 1 = j`, `chainForm N (e_i) (e_j) = 1`. -/
theorem chainForm_single_single_succ {N : ℕ} {i j : Fin N} (hij : (i : ℕ) + 1 = j) :
    chainForm N (Pi.single i 1) (Pi.single j 1) = 1 := by
  rw [chainForm_single_right]
  have hj0 : 0 < j.val := by omega
  have hi : (⟨j.val - 1, by omega⟩ : Fin N) = i := Fin.ext (by dsimp; omega)
  simp only [hj0, ↓reduceDIte]
  split_ifs with hlt
  · have hne : (⟨j.val + 1, hlt⟩ : Fin N) ≠ i := by
      intro h
      have hval := congrArg Fin.val h
      dsimp at hval
      omega
    simp [hi, Pi.single_eq_of_ne hne]
  · simp [hi]

/-- On distant standard basis vectors `|i - j| ≥ 2`, `chainForm N (e_i) (e_j) = 0`. -/
theorem chainForm_single_single_of_dist_ge_two {N : ℕ} {i j : Fin N}
    (hij : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    chainForm N (Pi.single i 1) (Pi.single j 1) = 0 := by
  rw [chainForm_single_right]
  split_ifs with h1 h2 h3
  · have hne1 : (⟨j.val - 1, by omega⟩ : Fin N) ≠ i := fun h ↦ by
      have hval := congrArg Fin.val h; dsimp at hval; omega
    have hne2 : (⟨j.val + 1, h2⟩ : Fin N) ≠ i := fun h ↦ by
      have hval := congrArg Fin.val h; dsimp at hval; omega
    simp [Pi.single_eq_of_ne hne1, Pi.single_eq_of_ne hne2]
  · have hne1 : (⟨j.val - 1, by omega⟩ : Fin N) ≠ i := fun h ↦ by
      have hval := congrArg Fin.val h; dsimp at hval; omega
    simp [Pi.single_eq_of_ne hne1]
  · have hne2 : (⟨j.val + 1, h3⟩ : Fin N) ≠ i := fun h ↦ by
      have hval := congrArg Fin.val h; dsimp at hval; omega
    simp [Pi.single_eq_of_ne hne2]
  · simp

/-- The primitive cube root of unity `ω = exp (2 π i / 3)`, as a unit of `ℂ`. -/
noncomputable def cubeRootOfUnity : ℂˣ :=
  Units.mk0 (Complex.exp (2 * Real.pi / 3 * Complex.I)) (Complex.exp_ne_zero _)

/-- Unfolding the complex value of `cubeRootOfUnity`. -/
theorem cubeRootOfUnity_val :
    (cubeRootOfUnity : ℂ) = Complex.exp (2 * Real.pi / 3 * Complex.I) := (rfl)

/-- Explicit rectangular form `ω = (-1 + √3 i) / 2`. -/
theorem cubeRootOfUnity_val_eq :
    (cubeRootOfUnity : ℂ) = (-1 + Real.sqrt 3 * Complex.I) / 2 := by
  rw [cubeRootOfUnity_val]
  have harg : (2 * Real.pi / 3 * Complex.I : ℂ) = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg, Complex.exp_mul_I]
  have hcos : Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
    have h : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
    rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
  have hsin : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    have h : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
    rw [h, Real.sin_pi_sub, Real.sin_pi_div_three]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, hcos, hsin]
  push_cast
  ring

/-- `cubeRootOfUnity ^ 3 = 1` in `ℂˣ`. -/
@[simp]
theorem cubeRootOfUnity_pow_three : cubeRootOfUnity ^ 3 = 1 := by
  ext
  simp only [Units.val_pow_eq_pow_val, cubeRootOfUnity_val, Units.val_one]
  rw [← Complex.exp_nat_mul]
  convert Complex.exp_two_pi_mul_I using 2
  push_cast
  ring

/-- `(cubeRootOfUnity : ℂ) ^ 3 = 1`. -/
@[simp]
theorem cubeRootOfUnity_val_pow_three : (cubeRootOfUnity : ℂ) ^ 3 = 1 := by
  rw [← Units.val_pow_eq_pow_val, cubeRootOfUnity_pow_three, Units.val_one]

/-- `cubeRootOfUnity ≠ 1`. -/
theorem cubeRootOfUnity_ne_one : cubeRootOfUnity ≠ 1 := by
  intro h
  have hval : (cubeRootOfUnity : ℂ) = 1 := congrArg Units.val h
  rw [cubeRootOfUnity_val_eq] at hval
  have hre := congrArg Complex.re hval
  simp at hre
  linarith

/-- `(cubeRootOfUnity : ℂ) ≠ 1`. -/
theorem cubeRootOfUnity_val_ne_one : (cubeRootOfUnity : ℂ) ≠ 1 :=
  fun h ↦ cubeRootOfUnity_ne_one (Units.ext h)

/-- The cyclotomic identity `1 + ω + ω ^ 2 = 0`. -/
theorem one_add_cubeRootOfUnity_add_sq :
    1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2 = 0 := by
  have h : ((cubeRootOfUnity : ℂ) - 1) *
      (1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2) = 0 := by
    linear_combination cubeRootOfUnity_val_pow_three
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr cubeRootOfUnity_val_ne_one)

/-- `cubeRootOfUnity` is unitary: `star (ω : ℂ) = (ω⁻¹ : ℂˣ)`. -/
@[simp]
theorem star_cubeRootOfUnity_val :
    star (cubeRootOfUnity : ℂ) = ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ) := by
  have hmul : star (cubeRootOfUnity : ℂ) * (cubeRootOfUnity : ℂ) = 1 := by
    rw [cubeRootOfUnity_val, Complex.star_def, ← Complex.exp_conj]
    have hconj : (starRingEnd ℂ) (2 * Real.pi / 3 * Complex.I) =
        -(2 * Real.pi / 3 * Complex.I) := by
      simp [map_div₀, map_mul, map_ofNat]
    rw [hconj, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have h := congrArg (· * ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ)) hmul
  simpa [mul_assoc] using h

/-- The character `x ↦ ω ^ x.val` on `ZMod 3`. -/
noncomputable def cubeRootPow (x : ZMod 3) : ℂˣ :=
  cubeRootOfUnity ^ x.val

/-- `cubeRootPow 0 = 1`. -/
@[simp]
theorem cubeRootPow_zero : cubeRootPow 0 = 1 := by
  simp [cubeRootPow]

/-- `cubeRootPow 1 = cubeRootOfUnity`. -/
@[simp]
theorem cubeRootPow_one : cubeRootPow 1 = cubeRootOfUnity := by
  rw [cubeRootPow, show (1 : ZMod 3).val = 1 from rfl, pow_one]

/-- `cubeRootPow 2 = cubeRootOfUnity ^ 2`. -/
@[simp]
theorem cubeRootPow_two : cubeRootPow 2 = cubeRootOfUnity ^ 2 := by
  rw [cubeRootPow, show (2 : ZMod 3).val = 2 from rfl]

/-- `cubeRootPow` is a homomorphism from additive `ZMod 3` to `ℂˣ`. -/
theorem cubeRootPow_add (x y : ZMod 3) :
    cubeRootPow (x + y) = cubeRootPow x * cubeRootPow y := by
  simp only [cubeRootPow, ZMod.val_add]
  rw [← pow_add, ← pow_eq_pow_mod _ cubeRootOfUnity_pow_three]

/-- `cubeRootPow (-x) = (cubeRootPow x)⁻¹`. -/
@[simp]
theorem cubeRootPow_neg (x : ZMod 3) :
    cubeRootPow (-x) = (cubeRootPow x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← cubeRootPow_add, neg_add_cancel, cubeRootPow_zero]

/-- `cubeRootPow x = 1` if and only if `x = 0`. -/
@[simp]
theorem cubeRootPow_eq_one_iff {x : ZMod 3} :
    cubeRootPow x = 1 ↔ x = 0 := by
  have hlt : x.val < 3 := x.val_lt
  interval_cases hval : x.val
  · have hx : x = 0 := by simpa [hval] using (ZMod.natCast_zmod_val x).symm
    subst hx
    simp
  · have hx : x = 1 := by simpa [hval] using (ZMod.natCast_zmod_val x).symm
    subst hx
    simp [cubeRootOfUnity_ne_one]
  · have hx : x = 2 := by simpa [hval] using (ZMod.natCast_zmod_val x).symm
    subst hx
    refine ⟨fun h ↦ ?_, fun h ↦ absurd h (by decide)⟩
    exfalso
    apply cubeRootOfUnity_ne_one
    rw [cubeRootPow_two] at h
    calc
      cubeRootOfUnity = cubeRootOfUnity ^ 2 * cubeRootOfUnity := by rw [h, one_mul]
      _ = cubeRootOfUnity ^ 3 := (pow_succ cubeRootOfUnity 2).symm
      _ = 1 := cubeRootOfUnity_pow_three

/-- Every value of `cubeRootPow` is unitary. -/
@[simp]
theorem star_cubeRootPow_val (x : ZMod 3) :
    star (cubeRootPow x : ℂ) = ((cubeRootPow x)⁻¹ : ℂˣ) := by
  rw [cubeRootPow, Units.val_pow_eq_pow_val, star_pow, star_cubeRootOfUnity_val,
    ← Units.val_pow_eq_pow_val, inv_pow]

/-! ### The cubic factor set and cubic quantum torus -/

/-- The factor set `α(a, b) = ω ^ (2 * B(a, b))` of the cubic quantum torus on
`Multiplicative (Fin N → ZMod 3)`. -/
noncomputable def cubicFactor (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) : ℂˣ :=
  cubeRootPow (2 * chainForm N a.toAdd b.toAdd)

/-- Unfolding `cubicFactor`. -/
theorem cubicFactor_def (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a b = cubeRootPow (2 * chainForm N a.toAdd b.toAdd) := (rfl)

/-- `cubicFactor N` is a normalized factor set. -/
instance cubicFactor_isFactorSet (N : ℕ) : IsFactorSet (cubicFactor N) where
  cocycle g h j := by
    simp only [cubicFactor_def, toAdd_mul, ← cubeRootPow_add]
    congr 1
    rw [chainForm_add_left, chainForm_add_right]
    ring
  one_left g := by
    simp [cubicFactor_def]

/-- `cubicFactor N` is unitary, equipping `CubicTorus N` with the canonical star structure
from `TwistedMonoidAlgebra.instStarRing`. -/
instance cubicFactor_unitary (N : ℕ) :
    Fact (∀ g h : Multiplicative (Fin N → ZMod 3),
      star (cubicFactor N g h : ℂ) = ((cubicFactor N g h)⁻¹ : ℂˣ)) :=
  ⟨fun _ _ ↦ star_cubeRootPow_val _⟩

/-- `cubicFactor N g g = 1`. -/
@[simp]
theorem cubicFactor_self (N : ℕ) (g : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N g g = 1 := by
  simp [cubicFactor_def]

/-- `cubicFactor N g g⁻¹ = 1`. -/
@[simp]
theorem cubicFactor_inv_self (N : ℕ) (g : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N g g⁻¹ = 1 := by
  simp [cubicFactor_def]

/-- `cubicFactor N g⁻¹ g = 1`. -/
@[simp]
theorem cubicFactor_inv_self_left (N : ℕ) (g : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N g⁻¹ g = 1 := by
  simp [cubicFactor_def]

/-- `cubicFactor N g⁻¹ h⁻¹ = cubicFactor N g h`. -/
@[simp]
theorem cubicFactor_inv_inv (N : ℕ) (g h : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N g⁻¹ h⁻¹ = cubicFactor N g h := by
  simp [cubicFactor_def]

/-- `cubicFactor N h g = (cubicFactor N g h)⁻¹`. -/
theorem cubicFactor_swap (N : ℕ) (g h : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N h g = (cubicFactor N g h)⁻¹ := by
  rw [cubicFactor_def, cubicFactor_def, chainForm_swap, mul_neg, cubeRootPow_neg]

/-- `cubicFactor N g h * (cubicFactor N h g)⁻¹ = cubeRootPow (chainForm N g.toAdd h.toAdd)`. -/
theorem cubicFactor_mul_inv_swap (N : ℕ) (g h : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N g h * (cubicFactor N h g)⁻¹ = cubeRootPow (chainForm N g.toAdd h.toAdd) := by
  rw [cubicFactor_swap N g h, inv_inv, cubicFactor_def, ← cubeRootPow_add]
  congr 1
  have h4 : (2 : ZMod 3) + 2 = 1 := by decide
  calc
    2 * chainForm N g.toAdd h.toAdd + 2 * chainForm N g.toAdd h.toAdd
      = (2 + 2) * chainForm N g.toAdd h.toAdd := by ring
    _ = chainForm N g.toAdd h.toAdd := by rw [h4, one_mul]

/-- **The cubic quantum torus** `G_N`: the twisted group algebra of `(ZMod 3)^N` for the factor
set `cubicFactor N`, of complex dimension `3 ^ N`. -/
noncomputable abbrev CubicTorus (N : ℕ) :=
  twistedMonoidAlgebra ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)

/-- The Weyl basis element `W(a) = TwistedMonoidAlgebra.of a` of `CubicTorus N`. -/
noncomputable def weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) : CubicTorus N :=
  TwistedMonoidAlgebra.of a

/-- Unfolding `weyl` as `TwistedMonoidAlgebra.of`. -/
theorem weyl_def (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a = TwistedMonoidAlgebra.of a := (rfl)

/-- `weyl N 1 = 1`. -/
@[simp]
theorem weyl_one (N : ℕ) : weyl N 1 = 1 :=
  TwistedMonoidAlgebra.of_one

/-- Product rule for Weyl basis elements: `W(a) * W(b) = α(a, b) • W(a * b)`. -/
@[simp]
theorem weyl_mul (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    weyl N a * weyl N b = (cubicFactor N a b : ℂ) • weyl N (a * b) :=
  TwistedMonoidAlgebra.of_mul_of a b

/-- The star adjoint of `W(a)` is `W(a⁻¹)`. -/
@[simp]
theorem star_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    star (weyl N a) = weyl N a⁻¹ := by
  rw [weyl_def, TwistedMonoidAlgebra.star_of_of_apply_inv_eq_one (cubicFactor_inv_self N a),
    ← weyl_def]

/-- `W(a) * W(a⁻¹) = 1`. -/
theorem weyl_mul_weyl_inv (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a * weyl N a⁻¹ = 1 := by
  simp

/-- `W(a⁻¹) * W(a) = 1`. -/
theorem weyl_inv_mul_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a⁻¹ * weyl N a = 1 := by
  simp

/-- `W(a) ^ 2 = W(a⁻¹)`. -/
@[simp]
theorem weyl_sq (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a ^ 2 = weyl N a⁻¹ := by
  rw [sq, weyl_mul, cubicFactor_self, Units.val_one, one_smul]
  congr 1
  apply Multiplicative.toAdd.injective
  ext i
  simp only [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply]
  have hx (z : ZMod 3) : z + z = -z := by fin_cases z <;> decide
  exact hx (a.toAdd i)

/-- Every Weyl basis element has cube `1`: `W(a) ^ 3 = 1`. -/
@[simp]
theorem weyl_pow_three (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a ^ 3 = 1 := by
  rw [pow_succ, weyl_sq, weyl_inv_mul_weyl]

/-- Commutation relation of Weyl basis elements:
`W(a) * W(b) = ω ^ B(a, b) • (W(b) * W(a))`. -/
theorem weyl_mul_comm_factor (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    weyl N a * weyl N b =
      (cubeRootPow (chainForm N a.toAdd b.toAdd) : ℂ) • (weyl N b * weyl N a) := by
  rw [weyl_mul, weyl_mul, smul_smul, mul_comm b a, ← Units.val_mul,
    ← cubicFactor_mul_inv_swap N a b, mul_assoc, inv_mul_cancel, mul_one]

/-- The cubic quantum torus `CubicTorus N` has complex dimension `3 ^ N`. -/
@[simp]
theorem finrank_cubicTorus (N : ℕ) : Module.finrank ℂ (CubicTorus N) = 3 ^ N := by
  rw [TwistedMonoidAlgebra.finrank_eq_natCard, Nat.card_eq_fintype_card,
    Fintype.card_congr Multiplicative.toAdd, Fintype.card_pi]
  simp [ZMod.card]

/-! ### The inversion automorphism and fixed-point star subalgebra -/

/-- The inversion `⋆`-automorphism `θ_N : CubicTorus N →⋆ₐ[ℂ] CubicTorus N` sending
`W(a) ↦ W(a⁻¹)`. -/
noncomputable def cubicInversion (N : ℕ) : CubicTorus N →⋆ₐ[ℂ] CubicTorus N :=
  TwistedMonoidAlgebra.mapStarAlgHom (MulEquiv.inv (Multiplicative (Fin N → ZMod 3))).toMonoidHom
    (fun g h ↦ cubicFactor_inv_inv N g h)

/-- `cubicInversion N` sends `W(a)` to `W(a⁻¹)`. -/
@[simp]
theorem cubicInversion_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicInversion N (weyl N a) = weyl N a⁻¹ :=
  TwistedMonoidAlgebra.mapStarAlgHom_of _ _ a

/-- `cubicInversion N` is an involution. -/
@[simp]
theorem cubicInversion_involutive (N : ℕ) (x : CubicTorus N) :
    cubicInversion N (cubicInversion N x) = x := by
  have h : (cubicInversion N).toAlgHom.comp (cubicInversion N).toAlgHom =
      AlgHom.id ℂ (CubicTorus N) := by
    apply TwistedMonoidAlgebra.algHom_ext
    intro g
    simp [← weyl_def]
  exact AlgHom.congr_fun h x

/-- `cubicInversion N` preserves the scalar trace. -/
@[simp]
theorem scalarTrace_cubicInversion (N : ℕ) (x : CubicTorus N) :
    TwistedMonoidAlgebra.scalarTrace (cubicFactor N) (cubicInversion N x) =
      TwistedMonoidAlgebra.scalarTrace (cubicFactor N) x := by
  have h : (TwistedMonoidAlgebra.scalarTrace (cubicFactor N)).comp
      (cubicInversion N).toAlgHom.toLinearMap =
      TwistedMonoidAlgebra.scalarTrace (cubicFactor N) := by
    refine (TwistedMonoidAlgebra.basis ℂ _ (cubicFactor N)).ext fun g ↦ ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom,
      TwistedMonoidAlgebra.basis_apply]
    rw [← weyl_def, cubicInversion_weyl]
    classical
    simp [weyl_def, TwistedMonoidAlgebra.scalarTrace_of]
  exact LinearMap.congr_fun h x

/-- **The inversion-fixed star subalgebra** `C_N = {x ∈ G_N : θ_N x = x}` of complex dimension
`(3 ^ N + 1) / 2`. -/
noncomputable def cubicFixed (N : ℕ) : StarSubalgebra ℂ (CubicTorus N) :=
  StarAlgHom.equalizer (cubicInversion N) (StarAlgHom.id ℂ (CubicTorus N))

/-- Membership in `cubicFixed N` is invariance under `cubicInversion N`. -/
@[simp]
theorem mem_cubicFixed {N : ℕ} {x : CubicTorus N} :
    x ∈ cubicFixed N ↔ cubicInversion N x = x := Iff.rfl

/-- The inversion-fixed subalgebra `cubicFixed N` has complex dimension `(3 ^ N + 1) / 2`. -/
@[simp]
theorem finrank_cubicFixed (N : ℕ) :
    Module.finrank ℂ (cubicFixed N) = (3 ^ N + 1) / 2 := by
  let G := Multiplicative (Fin N → ZMod 3)
  let b := TwistedMonoidAlgebra.basis ℂ G (cubicFactor N)
  let P : Module.End ℂ (CubicTorus N) :=
    (2 : ℂ)⁻¹ • (LinearMap.id + (cubicInversion N).toAlgHom.toLinearMap)
  have hP_apply (x : CubicTorus N) : P x = (2 : ℂ)⁻¹ • (x + cubicInversion N x) := (rfl)
  have hP_idem (x : CubicTorus N) : P (P x) = P x := by
    simp only [hP_apply, map_smul, map_add, cubicInversion_involutive]
    rw [add_comm (cubicInversion N x) x, ← two_smul ℂ, smul_smul, smul_smul]
    norm_num
  have hrange : LinearMap.range P = (cubicFixed N).toSubalgebra.toSubmodule := by
    ext x
    simp only [LinearMap.mem_range, Subalgebra.mem_toSubmodule, StarSubalgebra.mem_toSubalgebra,
      mem_cubicFixed]
    refine ⟨?_, fun hx ↦ ⟨x, ?_⟩⟩
    · rintro ⟨y, rfl⟩
      simp [hP_apply, add_comm]
    · rw [hP_apply, hx, ← two_smul ℂ, smul_smul]
      norm_num
  let eV : CubicTorus N ≃ₗ[ℂ] (G → ℂ) := b.equivFun
  let Q : Module.End ℂ (G → ℂ) := eV.conj P
  have hQ_idem (v : G → ℂ) : Q (Q v) = Q v := by
    simp only [Q, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, hP_idem]
  have hcompl : IsCompl (LinearMap.range Q) (LinearMap.ker Q) := by
    constructor
    · rw [Submodule.disjoint_def]
      rintro v ⟨w, rfl⟩ hv
      rw [LinearMap.mem_ker, hQ_idem] at hv
      exact hv
    · rw [codisjoint_iff_le_sup]
      intro v _
      have hdecomp : v = Q v + (v - Q v) := (add_sub_cancel (Q v) v).symm
      rw [hdecomp]
      refine Submodule.add_mem_sup ⟨v, rfl⟩ ?_
      rw [LinearMap.mem_ker, map_sub, hQ_idem, sub_self]
  let e := Submodule.prodEquivOfIsCompl (LinearMap.range Q) (LinearMap.ker Q) hcompl
  have hconj : e.symm.conj Q = LinearMap.prodMap LinearMap.id 0 := by
    apply LinearMap.ext
    rintro ⟨v, w⟩
    apply e.injective
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_symm, LinearMap.prodMap_apply,
      LinearMap.id_apply, LinearMap.zero_apply, e, Submodule.coe_prodEquivOfIsCompl',
      map_add, Submodule.coe_zero, add_zero]
    obtain ⟨y, hy⟩ := v.2
    rw [← hy, hQ_idem, LinearMap.mem_ker.mp w.2, add_zero]
  have hrangeQ : (LinearMap.range P).map eV.toLinearMap = LinearMap.range Q := by
    ext v
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe, Q,
      LinearEquiv.conj_apply, LinearMap.comp_apply]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨eV x, by simp⟩
    · rintro ⟨w, rfl⟩
      exact ⟨P (eV.symm w), ⟨eV.symm w, rfl⟩, rfl⟩
  have hfinrankQ : Module.finrank ℂ (LinearMap.range Q) = Module.finrank ℂ (cubicFixed N) := by
    rw [← hrangeQ, ← (Submodule.equivMapOfInjective eV.toLinearMap eV.injective
      (LinearMap.range P)).finrank_eq, hrange]
    rfl
  have htrQ1 : LinearMap.trace ℂ (G → ℂ) Q = (Module.finrank ℂ (cubicFixed N) : ℂ) := by
    have htr1 := LinearMap.trace_conj' Q e.symm
    rw [hconj, LinearMap.trace_prodMap', LinearMap.trace_id, map_zero, add_zero] at htr1
    rw [← htr1, hfinrankQ]
  have heV_b (g : G) : eV (b g) = Pi.basisFun ℂ G g := by
    ext h
    simp [eV, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  have heV_symm (g : G) : eV.symm (Pi.basisFun ℂ G g) = b g := by
    rw [← heV_b, LinearEquiv.symm_apply_apply]
  have hQ_basis (g : G) :
      Q (Pi.basisFun ℂ G g) = (2 : ℂ)⁻¹ • (Pi.basisFun ℂ G g + Pi.basisFun ℂ G g⁻¹) := by
    simp only [Q, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, heV_symm,
      hP_apply, map_smul, map_add, heV_b]
    congr 2
    rw [show b g = weyl N g from TwistedMonoidAlgebra.basis_apply ℂ G (cubicFactor N) g,
      cubicInversion_weyl, weyl_def, ← TwistedMonoidAlgebra.basis_apply ℂ G (cubicFactor N), heV_b]
  have hcardG : (Fintype.card G : ℂ) = (3 ^ N : ℂ) := by
    have hcard : Fintype.card G = 3 ^ N := by
      rw [Fintype.card_congr Multiplicative.toAdd, Fintype.card_pi]
      simp [ZMod.card]
    exact_mod_cast hcard
  have htrQ2 : LinearMap.trace ℂ (G → ℂ) Q = (2 : ℂ)⁻¹ * ((3 ^ N : ℂ) + 1) := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ G), Matrix.trace]
    have hdiag (g : G) :
        LinearMap.toMatrix (Pi.basisFun ℂ G) (Pi.basisFun ℂ G) Q g g =
          (2 : ℂ)⁻¹ * (1 + if g = 1 then 1 else 0) := by
      rw [LinearMap.toMatrix_apply, hQ_basis, map_smul, map_add, Module.Basis.repr_self,
        Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.single_apply, smul_eq_mul]
      have hinv : g⁻¹ = g ↔ g = 1 := by
        constructor
        · intro h
          apply Multiplicative.toAdd.injective
          ext i
          have hi : -g.toAdd i = g.toAdd i := by
            simpa [G, toAdd_inv] using congrFun (congrArg Multiplicative.toAdd h) i
          have hx : ∀ z : ZMod 3, -z = z → z = 0 := by decide
          exact hx (g.toAdd i) hi
        · intro h; simp [h]
      simp [hinv]
    simp only [Matrix.diag_apply, hdiag, ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, hcardG]
  have hEq : ((2 * Module.finrank ℂ (cubicFixed N) : ℕ) : ℂ) = ((3 ^ N + 1 : ℕ) : ℂ) := by
    push_cast
    have h := htrQ1.symm.trans htrQ2
    linear_combination 2 * h
  have hNat : 2 * Module.finrank ℂ (cubicFixed N) = 3 ^ N + 1 := Nat.cast_injective hEq
  omega

/-! ### Site unitaries and Jones projections -/

/-- The site unitary `U_j = W(e_j)` at site `j : Fin N`. -/
noncomputable def cubicSite (N : ℕ) (j : Fin N) : CubicTorus N :=
  weyl N (Multiplicative.ofAdd (Pi.single j 1))

/-- Unfolding `cubicSite`. -/
theorem cubicSite_def (N : ℕ) (j : Fin N) :
    cubicSite N j = weyl N (Multiplicative.ofAdd (Pi.single j 1)) := (rfl)

/-- Each site unitary has cube `1`: `U_j ^ 3 = 1`. -/
@[simp]
theorem cubicSite_pow_three (N : ℕ) (j : Fin N) :
    cubicSite N j ^ 3 = 1 :=
  weyl_pow_three N _

/-- `star U_j = U_j ^ 2`. -/
@[simp]
theorem star_cubicSite (N : ℕ) (j : Fin N) :
    star (cubicSite N j) = cubicSite N j ^ 2 := by
  rw [cubicSite_def, star_weyl, weyl_sq]

/-- `cubicInversion N U_j = U_j ^ 2`. -/
@[simp]
theorem cubicInversion_cubicSite (N : ℕ) (j : Fin N) :
    cubicInversion N (cubicSite N j) = cubicSite N j ^ 2 := by
  rw [cubicSite_def, cubicInversion_weyl, weyl_sq]

/-- Adjacent site unitaries satisfy `U_i * U_j = ω • (U_j * U_i)` when `i + 1 = j`. -/
theorem cubicSite_mul_cubicSite_succ {N : ℕ} {i j : Fin N} (hij : (i : ℕ) + 1 = j) :
    cubicSite N i * cubicSite N j = (cubeRootOfUnity : ℂ) • (cubicSite N j * cubicSite N i) := by
  rw [cubicSite_def, cubicSite_def, weyl_mul_comm_factor]
  simp [chainForm_single_single_succ hij]

/-- Adjacent site unitaries satisfy `U_j * U_i = ω ^ 2 • (U_i * U_j)` when `i + 1 = j`. -/
theorem cubicSite_mul_cubicSite_pred {N : ℕ} {i j : Fin N} (hij : (i : ℕ) + 1 = j) :
    cubicSite N j * cubicSite N i =
      ((cubeRootOfUnity : ℂ) ^ 2) • (cubicSite N i * cubicSite N j) := by
  rw [cubicSite_mul_cubicSite_succ hij, smul_smul, ← pow_succ, cubeRootOfUnity_val_pow_three,
    one_smul]

/-- Distant site unitaries commute when `|i - j| ≥ 2`. -/
theorem cubicSite_mul_cubicSite_comm {N : ℕ} {i j : Fin N}
    (hij : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    cubicSite N i * cubicSite N j = cubicSite N j * cubicSite N i := by
  rw [cubicSite_def, cubicSite_def, weyl_mul_comm_factor]
  simp [chainForm_single_single_of_dist_ge_two hij]

/-- The Jones projection `p_j = 3⁻¹ • (1 + U_j + U_j ^ 2)` at site `j : Fin N`. -/
noncomputable def cubicProjection (N : ℕ) (j : Fin N) : CubicTorus N :=
  (3 : ℂ)⁻¹ • (1 + cubicSite N j + cubicSite N j ^ 2)

/-- Unfolding `cubicProjection`. -/
theorem cubicProjection_def (N : ℕ) (j : Fin N) :
    cubicProjection N j = (3 : ℂ)⁻¹ • (1 + cubicSite N j + cubicSite N j ^ 2) := (rfl)

/-- Every `cubicProjection N j` lies in the inversion-fixed subalgebra `cubicFixed N`. -/
theorem cubicProjection_mem_cubicFixed (N : ℕ) (j : Fin N) :
    cubicProjection N j ∈ cubicFixed N := by
  rw [mem_cubicFixed, cubicProjection_def, map_smul, map_add, map_add, map_one, map_pow,
    cubicInversion_cubicSite]
  have h4 : cubicSite N j ^ 4 = cubicSite N j := by
    rw [pow_succ, cubicSite_pow_three, one_mul]
  rw [← pow_mul, h4]
  abel_nf

/-- Every `cubicProjection N j` is self-adjoint. -/
@[simp]
theorem star_cubicProjection (N : ℕ) (j : Fin N) :
    star (cubicProjection N j) = cubicProjection N j := by
  rw [cubicProjection_def, star_smul, star_add, star_add, star_one, star_pow, star_cubicSite]
  have h4 : cubicSite N j ^ 4 = cubicSite N j := by
    rw [pow_succ, cubicSite_pow_three, one_mul]
  have h3 : star ((3 : ℂ)⁻¹) = (3 : ℂ)⁻¹ := by simp
  rw [h3, ← pow_mul, h4]
  abel_nf

/-- Every `cubicProjection N j` is self-adjoint, stated with `IsSelfAdjoint`. -/
theorem isSelfAdjoint_cubicProjection (N : ℕ) (j : Fin N) :
    IsSelfAdjoint (cubicProjection N j) :=
  star_cubicProjection N j

/-- `U_j` absorbs into `p_j` on the left: `U_j * p_j = p_j`. -/
@[simp]
theorem cubicSite_mul_cubicProjection (N : ℕ) (j : Fin N) :
    cubicSite N j * cubicProjection N j = cubicProjection N j := by
  rw [cubicProjection_def, mul_smul_comm]
  congr 1
  have h3 : cubicSite N j * cubicSite N j ^ 2 = 1 := by
    rw [← pow_succ', cubicSite_pow_three]
  rw [mul_add, mul_add, mul_one, ← sq, h3]
  abel

/-- `U_j ^ 2` absorbs into `p_j` on the left: `U_j ^ 2 * p_j = p_j`. -/
@[simp]
theorem cubicSite_sq_mul_cubicProjection (N : ℕ) (j : Fin N) :
    cubicSite N j ^ 2 * cubicProjection N j = cubicProjection N j := by
  rw [sq, mul_assoc, cubicSite_mul_cubicProjection, cubicSite_mul_cubicProjection]

/-- Each `cubicProjection N j` is idempotent: `p_j * p_j = p_j`. -/
@[simp]
theorem cubicProjection_mul_self (N : ℕ) (j : Fin N) :
    cubicProjection N j * cubicProjection N j = cubicProjection N j := by
  conv_lhs => arg 1; rw [cubicProjection_def]
  rw [smul_mul_assoc, add_mul, add_mul, one_mul, cubicSite_mul_cubicProjection,
    cubicSite_sq_mul_cubicProjection]
  have h3 : cubicProjection N j + cubicProjection N j + cubicProjection N j =
      (3 : ℂ) • cubicProjection N j := by
    module
  rw [h3, smul_smul]
  norm_num

/-- Helper: if `U_i * x = ζ • (x * U_i)` with `1 + ζ + ζ ^ 2 = 0`, then `p_i * x * p_i = 0`. -/
private theorem cubicProjection_mul_mul_cubicProjection_eq_zero {N : ℕ} (i : Fin N)
    {x : CubicTorus N} {ζ : ℂ} (hcomm : cubicSite N i * x = ζ • (x * cubicSite N i))
    (hsum : 1 + ζ + ζ ^ 2 = 0) :
    cubicProjection N i * x * cubicProjection N i = 0 := by
  have hcomm2 : cubicSite N i ^ 2 * x = (ζ ^ 2) • (x * cubicSite N i ^ 2) := by
    calc
      cubicSite N i ^ 2 * x = cubicSite N i * (cubicSite N i * x) := by rw [sq, mul_assoc]
      _ = ζ • ((cubicSite N i * x) * cubicSite N i) := by
            conv_lhs => rw [hcomm]
            rw [mul_smul_comm, mul_assoc]
      _ = (ζ ^ 2) • (x * cubicSite N i ^ 2) := by
            rw [hcomm, smul_mul_assoc, smul_smul, ← sq, mul_assoc, ← sq]
  calc
    cubicProjection N i * x * cubicProjection N i
      = (3 : ℂ)⁻¹ • ((1 + cubicSite N i + cubicSite N i ^ 2) * x * cubicProjection N i) := by
          rw [cubicProjection_def, smul_mul_assoc, smul_mul_assoc]
    _ = (3 : ℂ)⁻¹ • (x * cubicProjection N i +
          ζ • (x * (cubicSite N i * cubicProjection N i)) +
          (ζ ^ 2) • (x * (cubicSite N i ^ 2 * cubicProjection N i))) := by
          simp only [add_mul, one_mul, hcomm, hcomm2, smul_mul_assoc, mul_assoc]
    _ = (3 : ℂ)⁻¹ • ((1 + ζ + ζ ^ 2) • (x * cubicProjection N i)) := by
          rw [cubicSite_mul_cubicProjection, cubicSite_sq_mul_cubicProjection,
            add_smul, add_smul, one_smul]
    _ = 0 := by rw [hsum, zero_smul, smul_zero]

/-- Adjacent Jones projections satisfy `p_i * p_j * p_i = 3⁻¹ • p_i`. -/
theorem cubicProjection_mul_cubicProjection_mul_cubicProjection {N : ℕ} {i j : Fin N}
    (hij : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    cubicProjection N i * cubicProjection N j * cubicProjection N i =
      (3 : ℂ)⁻¹ • cubicProjection N i := by
  have hsum1 : 1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2 = 0 :=
    one_add_cubeRootOfUnity_add_sq
  have hsum2 : 1 + (cubeRootOfUnity : ℂ) ^ 2 + ((cubeRootOfUnity : ℂ) ^ 2) ^ 2 = 0 := by
    have h4 : ((cubeRootOfUnity : ℂ) ^ 2) ^ 2 = (cubeRootOfUnity : ℂ) := by
      calc
        ((cubeRootOfUnity : ℂ) ^ 2) ^ 2 = (cubeRootOfUnity : ℂ) ^ 3 * (cubeRootOfUnity : ℂ) := by
          ring
        _ = (cubeRootOfUnity : ℂ) := by rw [cubeRootOfUnity_val_pow_three, one_mul]
    rw [h4]
    linear_combination hsum1
  have hU : cubicProjection N i * cubicSite N j * cubicProjection N i = 0 := by
    rcases hij with h | h
    · exact cubicProjection_mul_mul_cubicProjection_eq_zero i
        (cubicSite_mul_cubicSite_succ h) hsum1
    · exact cubicProjection_mul_mul_cubicProjection_eq_zero i
        (cubicSite_mul_cubicSite_pred h) hsum2
  have hU2 : cubicProjection N i * cubicSite N j ^ 2 * cubicProjection N i = 0 := by
    rcases hij with h | h
    · refine cubicProjection_mul_mul_cubicProjection_eq_zero i ?_ hsum2
      calc
        cubicSite N i * cubicSite N j ^ 2
          = (cubicSite N i * cubicSite N j) * cubicSite N j := by rw [sq, mul_assoc]
        _ = (cubeRootOfUnity : ℂ) • (cubicSite N j * (cubicSite N i * cubicSite N j)) := by
              conv_lhs => rw [cubicSite_mul_cubicSite_succ h]
              rw [smul_mul_assoc, mul_assoc]
        _ = ((cubeRootOfUnity : ℂ) ^ 2) • (cubicSite N j ^ 2 * cubicSite N i) := by
              rw [cubicSite_mul_cubicSite_succ h, mul_smul_comm, smul_smul, ← sq, ← mul_assoc, ← sq]
    · refine cubicProjection_mul_mul_cubicProjection_eq_zero i ?_ hsum1
      calc
        cubicSite N i * cubicSite N j ^ 2
          = (cubicSite N i * cubicSite N j) * cubicSite N j := by rw [sq, mul_assoc]
        _ = ((cubeRootOfUnity : ℂ) ^ 2) • (cubicSite N j * (cubicSite N i * cubicSite N j)) := by
              conv_lhs => rw [cubicSite_mul_cubicSite_pred h]
              rw [smul_mul_assoc, mul_assoc]
        _ = (cubeRootOfUnity : ℂ) • (cubicSite N j ^ 2 * cubicSite N i) := by
              rw [cubicSite_mul_cubicSite_pred h, mul_smul_comm, smul_smul, ← mul_assoc]
              have h4 : (cubeRootOfUnity : ℂ) ^ 2 * (cubeRootOfUnity : ℂ) ^ 2 =
                  (cubeRootOfUnity : ℂ) := by
                calc
                  (cubeRootOfUnity : ℂ) ^ 2 * (cubeRootOfUnity : ℂ) ^ 2
                    = (cubeRootOfUnity : ℂ) ^ 3 * (cubeRootOfUnity : ℂ) := by ring
                  _ = (cubeRootOfUnity : ℂ) := by rw [cubeRootOfUnity_val_pow_three, one_mul]
              rw [h4, ← sq]
  calc
    cubicProjection N i * cubicProjection N j * cubicProjection N i
      = (3 : ℂ)⁻¹ • (cubicProjection N i * (1 + cubicSite N j + cubicSite N j ^ 2) *
          cubicProjection N i) := by
          rw [cubicProjection_def N j, mul_smul_comm, smul_mul_assoc]
    _ = (3 : ℂ)⁻¹ • (cubicProjection N i * cubicProjection N i +
          cubicProjection N i * cubicSite N j * cubicProjection N i +
          cubicProjection N i * cubicSite N j ^ 2 * cubicProjection N i) := by
          simp only [mul_add, mul_one, add_mul]
    _ = (3 : ℂ)⁻¹ • cubicProjection N i := by
          rw [cubicProjection_mul_self, hU, hU2, add_zero, add_zero]

/-- Distant Jones projections commute when `|i - j| ≥ 2`. -/
theorem cubicProjection_mul_cubicProjection_comm {N : ℕ} {i j : Fin N}
    (hij : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    cubicProjection N i * cubicProjection N j = cubicProjection N j * cubicProjection N i := by
  have hcomm : Commute (cubicSite N i) (cubicSite N j) := cubicSite_mul_cubicSite_comm hij
  simp only [cubicProjection_def, smul_mul_assoc, mul_smul_comm]
  congr 1
  have h12 : cubicSite N i * cubicSite N j ^ 2 = cubicSite N j ^ 2 * cubicSite N i :=
    (hcomm.pow_right 2).eq
  have h21 : cubicSite N i ^ 2 * cubicSite N j = cubicSite N j * cubicSite N i ^ 2 :=
    (hcomm.pow_left 2).eq
  have h22 : cubicSite N i ^ 2 * cubicSite N j ^ 2 = cubicSite N j ^ 2 * cubicSite N i ^ 2 :=
    ((hcomm.pow_left 2).pow_right 2).eq
  simp only [add_mul, mul_add, one_mul, mul_one, hcomm.eq, h12, h21, h22]
  abel_nf

/-- The scalar trace of every Jones projection is `3⁻¹`. -/
@[simp]
theorem scalarTrace_cubicProjection (N : ℕ) (j : Fin N) :
    TwistedMonoidAlgebra.scalarTrace (cubicFactor N) (cubicProjection N j) = (3 : ℂ)⁻¹ := by
  have h1 : Multiplicative.ofAdd (Pi.single j (1 : ZMod 3) : Fin N → ZMod 3) ≠ 1 := by
    intro h
    have h0 := congrFun (congrArg Multiplicative.toAdd h) j
    simp at h0
  have h2 : (Multiplicative.ofAdd (Pi.single j (1 : ZMod 3) : Fin N → ZMod 3))⁻¹ ≠ 1 :=
    inv_ne_one.mpr h1
  rw [cubicProjection_def, map_smul, map_add, map_add, TwistedMonoidAlgebra.scalarTrace_one,
    cubicSite_def, weyl_sq, weyl_def, weyl_def,
    TwistedMonoidAlgebra.scalarTrace_of_ne_one _ h1,
    TwistedMonoidAlgebra.scalarTrace_of_ne_one _ h2]
  simp

/-! ### The Temperley–Lieb comparison homomorphism and its surjectivity -/

/-- The `⋆`-algebra comparison homomorphism
`F_m : TemperleyLieb ℂ (√3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1)` sending `e (√3 : ℂ) j` to
`(√3 : ℂ) • cubicProjection (m - 1) j`. -/
noncomputable def cubicFixedHom (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1) :=
  let f : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1) :=
    TemperleyLieb.lift
      (fun j ↦ ⟨(Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j,
        StarSubalgebra.smul_mem _ (cubicProjection_mem_cubicFixed (m - 1) j) _⟩)
      (fun j ↦ Subtype.ext <| by
        simp only [MulMemClass.coe_mul, SetLike.val_smul, smul_mul_smul_comm,
          cubicProjection_mul_self, sqrt_three_coe_mul_self, smul_smul])
      (fun {i j} hij ↦ Subtype.ext <| by
        simp only [MulMemClass.coe_mul, smul_mul_smul_comm,
          cubicProjection_mul_cubicProjection_mul_cubicProjection hij, smul_smul]
        congr 1
        calc
          (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) * (3 : ℂ)⁻¹
            = ((Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)) * (3 : ℂ)⁻¹ * (Real.sqrt 3 : ℂ) := by ring
          _ = (Real.sqrt 3 : ℂ) := by rw [sqrt_three_coe_mul_self]; norm_num)
      (fun {i j} hij ↦ Subtype.ext <| by
        simp only [MulMemClass.coe_mul, smul_mul_smul_comm,
          cubicProjection_mul_cubicProjection_comm hij])
  { f with
    map_star' := TemperleyLieb.map_star_iff.mpr fun j ↦ by
      apply Subtype.ext
      simp only [f, TemperleyLieb.lift_e, StarMemClass.coe_star, star_smul,
        Complex.star_def, Complex.conj_ofReal, star_cubicProjection] }

/-- Coercing `cubicFixedHom m (e (√3 : ℂ) j)` to `CubicTorus (m - 1)` gives
`(√3 : ℂ) • cubicProjection (m - 1) j`. -/
@[simp]
theorem coe_cubicFixedHom_e (m : ℕ) (j : Fin (m - 1)) :
    (cubicFixedHom m (e (Real.sqrt 3 : ℂ) j) : CubicTorus (m - 1)) =
      (Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j := by
  simp [cubicFixedHom]

/-- `cubicFixedHom` preserves the analytic adjoint. -/
@[simp]
theorem cubicFixedHom_star {m : ℕ} (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    cubicFixedHom m (star x) = star (cubicFixedHom m x) :=
  map_star (cubicFixedHom m) x

/-! #### Surjectivity of `cubicFixedHom m` -/

/-- The inversion-symmetric Weyl combination `W(a) + W(-a)` in `CubicTorus N`. -/
private noncomputable def symWeyl (N : ℕ) (a : Fin N → ZMod 3) : CubicTorus N :=
  weyl N (Multiplicative.ofAdd a) + weyl N (Multiplicative.ofAdd (-a))

private theorem symWeyl_zero (N : ℕ) : symWeyl N 0 = (2 : ℂ) • (1 : CubicTorus N) := by
  simp [symWeyl, two_smul]

private theorem symWeyl_neg (N : ℕ) (a : Fin N → ZMod 3) : symWeyl N (-a) = symWeyl N a := by
  simp [symWeyl, add_comm]

private theorem symWeyl_single (N : ℕ) (j : Fin N) :
    symWeyl N (Pi.single j 1) = (3 : ℂ) • cubicProjection N j - 1 := by
  have hneg : Multiplicative.ofAdd (-(Pi.single j (1 : ZMod 3) : Fin N → ZMod 3)) =
      (Multiplicative.ofAdd (Pi.single j (1 : ZMod 3) : Fin N → ZMod 3))⁻¹ := ofAdd_neg _
  rw [cubicProjection_def, smul_smul]
  norm_num
  rw [symWeyl, hneg, ← weyl_sq, ← cubicSite_def]
  abel

private theorem symWeyl_mul_symWeyl (N : ℕ) (u v : Fin N → ZMod 3) :
    symWeyl N u * symWeyl N v =
      (cubicFactor N (Multiplicative.ofAdd u) (Multiplicative.ofAdd v) : ℂ) • symWeyl N (u + v) +
        (((cubicFactor N (Multiplicative.ofAdd u) (Multiplicative.ofAdd v))⁻¹ : ℂˣ) : ℂ) •
          symWeyl N (u - v) := by
  have h1 : cubicFactor N (Multiplicative.ofAdd (-u)) (Multiplicative.ofAdd (-v)) =
      cubicFactor N (Multiplicative.ofAdd u) (Multiplicative.ofAdd v) := by
    simp [cubicFactor_def]
  have h2 : cubicFactor N (Multiplicative.ofAdd u) (Multiplicative.ofAdd (-v)) =
      (cubicFactor N (Multiplicative.ofAdd u) (Multiplicative.ofAdd v))⁻¹ := by
    rw [cubicFactor_def, cubicFactor_def]
    simp [mul_neg]
  have h3 : cubicFactor N (Multiplicative.ofAdd (-u)) (Multiplicative.ofAdd v) =
      (cubicFactor N (Multiplicative.ofAdd u) (Multiplicative.ofAdd v))⁻¹ := by
    rw [cubicFactor_def, cubicFactor_def]
    simp [mul_neg]
  simp only [symWeyl, add_mul, mul_add, weyl_mul, h1, h2, h3, ← ofAdd_add]
  have hneg_add : -u + -v = -(u + v) := by abel
  have hsub1 : u + -v = u - v := sub_eq_add_neg u v |>.symm
  have hsub2 : -u + v = -(u - v) := by abel
  rw [hneg_add, hsub1, hsub2, smul_add, smul_add]
  abel

/-- If `C(u)` and `C(v)` lie in a subalgebra `S` and `B(u, v) ≠ 0`, then both `C(u + v)` and
`C(u - v)` lie in `S`. -/
private theorem symWeyl_add_and_sub_mem {N : ℕ} {S : Subalgebra ℂ (CubicTorus N)}
    {u v : Fin N → ZMod 3} (hu : symWeyl N u ∈ S) (hv : symWeyl N v ∈ S)
    (hB : chainForm N u v ≠ 0) :
    symWeyl N (u + v) ∈ S ∧ symWeyl N (u - v) ∈ S := by
  set β : ℂˣ := cubicFactor N (Multiplicative.ofAdd u) (Multiplicative.ofAdd v)
  have hvu : cubicFactor N (Multiplicative.ofAdd v) (Multiplicative.ofAdd u) = β⁻¹ :=
    cubicFactor_swap N (Multiplicative.ofAdd u) (Multiplicative.ofAdd v)
  have hmul1 : symWeyl N u * symWeyl N v =
      (β : ℂ) • symWeyl N (u + v) + ((β⁻¹ : ℂˣ) : ℂ) • symWeyl N (u - v) :=
    symWeyl_mul_symWeyl N u v
  have hmul2 : symWeyl N v * symWeyl N u =
      ((β⁻¹ : ℂˣ) : ℂ) • symWeyl N (u + v) + (β : ℂ) • symWeyl N (u - v) := by
    rw [symWeyl_mul_symWeyl N v u, hvu, inv_inv, add_comm v u]
    have hsub : v - u = -(u - v) := by abel
    rw [hsub, symWeyl_neg]
  have hβ_ne_one : (β : ℂ) ≠ 1 := by
    intro h
    have h1 : β = 1 := Units.ext h
    have h2 : 2 * chainForm N u v = 0 := cubeRootPow_eq_one_iff.mp h1
    apply hB
    have h2' : (2 : ZMod 3) * (2 * chainForm N u v) = 0 := by rw [h2, mul_zero]
    have h4 : (2 : ZMod 3) * 2 = 1 := by decide
    simpa [← mul_assoc, h4] using h2'
  have hβ3 : (β : ℂ) ^ 3 = 1 := by
    have h : cubeRootPow (2 * chainForm N u v) ^ 3 = 1 := by
      rw [cubeRootPow, ← pow_mul, mul_comm, pow_mul, cubeRootOfUnity_pow_three, one_pow]
    exact congrArg Units.val h
  have hdet : (β : ℂ) ^ 2 - ((β⁻¹ : ℂˣ) : ℂ) ^ 2 ≠ 0 := by
    intro h0
    have hsq : (β : ℂ) ^ 2 = ((β⁻¹ : ℂˣ) : ℂ) ^ 2 := sub_eq_zero.mp h0
    have h4 : (β : ℂ) ^ 4 = 1 := by
      calc
        (β : ℂ) ^ 4 = (β : ℂ) ^ 2 * (β : ℂ) ^ 2 := by ring
        _ = (β : ℂ) ^ 2 * ((β⁻¹ : ℂˣ) : ℂ) ^ 2 := by rw [hsq]
        _ = ((β : ℂ) * ((β⁻¹ : ℂˣ) : ℂ)) ^ 2 := by ring
        _ = 1 := by simp
    have h1 : (β : ℂ) = 1 := by
      calc
        (β : ℂ) = (β : ℂ) ^ 3 * (β : ℂ) := by rw [hβ3, one_mul]
        _ = (β : ℂ) ^ 4 := by ring
        _ = 1 := h4
    exact hβ_ne_one h1
  have hcomb1 : ((β : ℂ) ^ 2 - ((β⁻¹ : ℂˣ) : ℂ) ^ 2) • symWeyl N (u + v) =
      (β : ℂ) • (symWeyl N u * symWeyl N v) -
        ((β⁻¹ : ℂˣ) : ℂ) • (symWeyl N v * symWeyl N u) := by
    rw [hmul1, hmul2]
    module
  have hcomb2 : ((β : ℂ) ^ 2 - ((β⁻¹ : ℂˣ) : ℂ) ^ 2) • symWeyl N (u - v) =
      (β : ℂ) • (symWeyl N v * symWeyl N u) -
        ((β⁻¹ : ℂˣ) : ℂ) • (symWeyl N u * symWeyl N v) := by
    rw [hmul1, hmul2]
    module
  constructor
  · have hmem : ((β : ℂ) ^ 2 - ((β⁻¹ : ℂˣ) : ℂ) ^ 2) • symWeyl N (u + v) ∈ S := by
      rw [hcomb1]
      exact sub_mem (S.smul_mem (S.mul_mem hu hv) _) (S.smul_mem (S.mul_mem hv hu) _)
    have hsmul := S.smul_mem hmem ((β : ℂ) ^ 2 - ((β⁻¹ : ℂˣ) : ℂ) ^ 2)⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hdet, one_smul] at hsmul
  · have hmem : ((β : ℂ) ^ 2 - ((β⁻¹ : ℂˣ) : ℂ) ^ 2) • symWeyl N (u - v) ∈ S := by
      rw [hcomb2]
      exact sub_mem (S.smul_mem (S.mul_mem hv hu) _) (S.smul_mem (S.mul_mem hu hv) _)
    have hsmul := S.smul_mem hmem ((β : ℂ) ^ 2 - ((β⁻¹ : ℂˣ) : ℂ) ^ 2)⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hdet, one_smul] at hsmul

/-- **Surjectivity of `cubicFixedHom m`** for every `m : ℕ`. -/
theorem cubicFixedHom_surjective (m : ℕ) :
    Function.Surjective (cubicFixedHom m) := by
  set N := m - 1
  set S : Subalgebra ℂ (CubicTorus N) :=
    ((cubicFixed N).val.comp (cubicFixedHom m).toAlgHom).range
  have hproj (j : Fin N) : cubicProjection N j ∈ S := by
    have hsqrt : (Real.sqrt 3 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
    have hmem : (Real.sqrt 3 : ℂ) • cubicProjection N j ∈ S :=
      ⟨e (Real.sqrt 3 : ℂ) j, coe_cubicFixedHom_e m j⟩
    have hsmul := S.smul_mem hmem (Real.sqrt 3 : ℂ)⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hsqrt, one_smul] at hsmul
  have hsingle (j : Fin N) : symWeyl N (Pi.single j 1) ∈ S := by
    rw [symWeyl_single]
    exact sub_mem (S.smul_mem (hproj j) _) S.one_mem
  have hsingle_smul (j : Fin N) (c : ZMod 3) (hc : c ≠ 0) :
      symWeyl N (c • Pi.single j 1) ∈ S := by
    have hlt : c.val < 3 := c.val_lt
    interval_cases hval : c.val
    · have hc0 : c = 0 := by simpa [hval] using (ZMod.natCast_zmod_val c).symm
      exact absurd hc0 hc
    · have hc1 : c = 1 := by simpa [hval] using (ZMod.natCast_zmod_val c).symm
      rw [hc1, one_smul]
      exact hsingle j
    · have hc2 : c = -1 := by
        have h2 : c = 2 := by simpa [hval] using (ZMod.natCast_zmod_val c).symm
        rw [h2]; decide
      rw [hc2, neg_one_smul, symWeyl_neg]
      exact hsingle j
  have hchain_lt {k : ℕ} (hk : k + 1 < N) {a' : Fin N → ZMod 3}
      (ha' : ∀ i : Fin N, k + 1 ≤ i.val → a' i = 0) :
      chainForm N a' (Pi.single ⟨k + 1, hk⟩ 1) = a' ⟨k, by omega⟩ := by
    rw [chainForm_single_right]
    simp only [Nat.succ_pos', ↓reduceDIte, Nat.add_sub_cancel]
    split_ifs with hlt
    · rw [ha' ⟨k + 2, hlt⟩ (by dsimp; omega), sub_zero]
    · simp
  have hmul_ne_zero : ∀ x y : ZMod 3, x ≠ 0 → y ≠ 0 → x * y ≠ 0 := by decide
  have hadd_self_ne_zero : ∀ x : ZMod 3, x ≠ 0 → x + x ≠ 0 := by decide
  have hind : ∀ k : ℕ, k ≤ N → ∀ a : Fin N → ZMod 3,
      (∀ i : Fin N, k ≤ i.val → a i = 0) → symWeyl N a ∈ S := by
    intro k
    induction k with
    | zero =>
      intro _ a ha
      have ha0 : a = 0 := funext fun i ↦ ha i (Nat.zero_le _)
      rw [ha0, symWeyl_zero]
      exact S.smul_mem S.one_mem _
    | succ k ih =>
      intro hk a ha
      have hkN : k < N := by omega
      set ek : Fin N → ZMod 3 := Pi.single ⟨k, hkN⟩ 1
      set c : ZMod 3 := a ⟨k, hkN⟩
      set a' : Fin N → ZMod 3 := a - c • ek
      have ha'supp : ∀ i : Fin N, k ≤ i.val → a' i = 0 := by
        intro i hi
        by_cases hik : i.val = k
        · have hEq : i = ⟨k, hkN⟩ := Fin.ext hik
          subst hEq
          simp [a', ek, c]
        · have hne : i ≠ ⟨k, hkN⟩ := fun h ↦ hik (congrArg Fin.val h)
          have hgt : k + 1 ≤ i.val := by omega
          simp [a', ek, Pi.single_eq_of_ne hne, ha i hgt]
      have ha'mem : symWeyl N a' ∈ S := ih (by omega) a' ha'supp
      have ha_eq : a = a' + c • ek := by simp [a']
      by_cases hc : c = 0
      · rwa [ha_eq, hc, zero_smul, add_zero]
      · have hcek : symWeyl N (c • ek) ∈ S := hsingle_smul ⟨k, hkN⟩ c hc
        cases k with
        | zero =>
          have ha'0 : a' = 0 := funext fun i ↦ ha'supp i (Nat.zero_le _)
          rwa [ha_eq, ha'0, zero_add]
        | succ p =>
          set ep : Fin N → ZMod 3 := Pi.single ⟨p, by omega⟩ 1
          have hB_a' : chainForm N a' ek = a' ⟨p, by omega⟩ :=
            hchain_lt hkN ha'supp
          by_cases hap : a' ⟨p, by omega⟩ ≠ 0
          · have hB : chainForm N a' (c • ek) ≠ 0 := by
              rw [chainForm_smul_right, hB_a']
              exact hmul_ne_zero c _ hc hap
            rw [ha_eq]
            exact (symWeyl_add_and_sub_mem ha'mem hcek hB).1
          · push Not at hap
            set v : Fin N → ZMod 3 := a' + ep
            have hvsupp : ∀ i : Fin N, p + 1 ≤ i.val → v i = 0 := by
              intro i hi
              have hne : i ≠ ⟨p, by omega⟩ := fun h ↦ by
                have hval := congrArg Fin.val h; dsimp at hval; omega
              simp [v, ep, Pi.single_eq_of_ne hne, ha'supp i hi]
            have hvmem : symWeyl N v ∈ S := ih (by omega) v hvsupp
            have hv_p : v ⟨p, by omega⟩ = 1 := by simp [v, ep, hap]
            have hB_v : chainForm N v ek = 1 := by
              rw [hchain_lt hkN hvsupp, hv_p]
            have hstep : ∀ d : ZMod 3, d ≠ 0 → symWeyl N (v + d • ek) ∈ S := fun d hd ↦ by
              have hB : chainForm N v (d • ek) ≠ 0 := by
                rw [chainForm_smul_right, hB_v, mul_one]
                exact hd
              exact (symWeyl_add_and_sub_mem hvmem (hsingle_smul ⟨p + 1, hkN⟩ d hd) hB).1
            have hB_ek_ep : chainForm N ek ep = -1 := by
              rw [chainForm_swap, chainForm_single_single_succ (by simp : p + 1 = p + 1)]
            have hB_step (d : ZMod 3) :
                chainForm N (v + d • ek) ep = chainForm N a' ep - d := by
              rw [chainForm_add_left, chainForm_add_left, chainForm_self, add_zero,
                chainForm_smul_left, hB_ek_ep]
              ring
            by_cases hcase : chainForm N a' ep ≠ c
            · have hB : chainForm N (v + c • ek) ep ≠ 0 := by
                rw [hB_step]
                exact sub_ne_zero.mpr hcase
              have hsub : v + c • ek - ep = a := by
                rw [ha_eq]
                simp only [v]
                abel
              rw [← hsub]
              exact (symWeyl_add_and_sub_mem (hstep c hc) (hsingle ⟨p, by omega⟩) hB).2
            · push Not at hcase
              have hnegc : -c ≠ 0 := neg_ne_zero.mpr hc
              have hB : chainForm N (v + (-c) • ek) ep ≠ 0 := by
                rw [hB_step, hcase, sub_neg_eq_add]
                exact hadd_self_ne_zero c hc
              have hsub : v + (-c) • ek - ep = a' - c • ek := by
                simp only [v, neg_smul]
                abel
              have hminus : symWeyl N (a' - c • ek) ∈ S := by
                rw [← hsub]
                exact (symWeyl_add_and_sub_mem (hstep (-c) hnegc) (hsingle ⟨p, by omega⟩) hB).2
              have hB0 : chainForm N a' (c • ek) = 0 := by
                rw [chainForm_smul_right, hB_a', hap, mul_zero]
              have hprod : symWeyl N a' * symWeyl N (c • ek) =
                  symWeyl N (a' + c • ek) + symWeyl N (a' - c • ek) := by
                rw [symWeyl_mul_symWeyl]
                simp [cubicFactor_def, hB0]
              have hsum : symWeyl N a =
                  symWeyl N a' * symWeyl N (c • ek) - symWeyl N (a' - c • ek) := by
                rw [ha_eq, hprod]
                abel
              rw [hsum]
              exact sub_mem (S.mul_mem ha'mem hcek) hminus
  have hall (a : Fin N → ZMod 3) : symWeyl N a ∈ S :=
    hind N le_rfl a fun i hi ↦ absurd i.2 (not_lt.mpr hi)
  intro y
  have hy_mem : (y : CubicTorus N) ∈ S := by
    let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
    have hfix : cubicInversion N (y : CubicTorus N) = y := y.2
    have hdecomp : (y : CubicTorus N) =
        (2 : ℂ)⁻¹ • ((y : CubicTorus N) + cubicInversion N (y : CubicTorus N)) := by
      rw [hfix, ← two_smul ℂ, smul_smul]
      norm_num
    rw [hdecomp]
    refine S.smul_mem ?_ _
    have hsum : (y : CubicTorus N) + cubicInversion N (y : CubicTorus N) =
        (b.repr (y : CubicTorus N)).sum fun g z ↦ z • symWeyl N g.toAdd := by
      conv_lhs => rw [← b.linearCombination_repr (y : CubicTorus N)]
      rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, map_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      simp only [b, TwistedMonoidAlgebra.basis_apply, ← weyl_def, map_smul, cubicInversion_weyl,
        symWeyl, ← smul_add]
      rfl
    rw [hsum, Finsupp.sum]
    exact S.sum_mem fun g _ ↦ S.smul_mem (hall g.toAdd) _
  obtain ⟨x, hx⟩ := hy_mem
  exact ⟨x, Subtype.ext hx⟩

end TauCeti.TemperleyLieb
