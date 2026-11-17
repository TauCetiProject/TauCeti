/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic
public import TauCeti.KnotTheory.TemperleyLieb
-- Private: trigonometric special values for `u = exp (πi / 6)`, finite-index / determinant /
-- roots-of-unity tools, and algebraic normalization tactics are used only inside proofs.
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
# The cubic Gaussian braid representation at `δ = √3` and its finiteness

At the loop parameter `δ = √3 = 2 cos (π / 6)`, let `u = exp (πi / 6)` (`twelfthRootOfUnity`) so
that `u + u⁻¹ = √3`, `u ^ 3 = i`, `u ^ 4 = ω = exp (2πi / 3)`, and `u ^ 12 = 1`. In the cubic
quantum torus `CubicTorus N`, the **Gaussian braid generators**

`g_j = u • ((1 + u ^ 2) • p_j - 1) = -(√3)⁻¹ • (1 + ω ^ 2 • (U_j + U_j ^ 2))`

belong to the inversion-fixed star-subalgebra `cubicFixed N`, are unitary (`star g_j * g_j = 1`),
have cube `g_j ^ 3 = (-i) • 1` (hence order dividing `12`), satisfy the braid relations, and match
the image of the Temperley–Lieb Jones braid units `jonesUnit a j` under `cubicFixedHom` up to the
scalar factor `-a / u` whenever `a ^ 2 = -u⁻¹`.

* **Metaplectic action on the Weyl basis and Heisenberg group**: conjugating any Weyl basis element
  `W(a)` by `g_j` yields the exact symplectic transvection
  `g_j * W(a) * star g_j = W(a + B(a, e_j) • e_j)` with trivial phase factor, because the factor set
  `α(a, b) = ω ^ (2 * B(a, b))` is strictly invariant under symplectic transformations of `B`. In
  particular, every `g_j` normalizes the finite Heisenberg subgroup `cubicHeisenbergSubgroup N` of
  order `3 ^ (N + 1)`, and the generated braid subgroup `G = Subgroup.closure (range (g_j))` acts by
  conjugation on the finite Weyl index set `Multiplicative (Fin N → ZMod 3)`.
* **Radical of `chainForm`, center of `CubicTorus N`, and finiteness**: an element of `G` acting
  trivially on the Weyl basis lies in the center of `CubicTorus N`, whose Weyl support is contained
  in the radical of `chainForm N`: `{0}` when `N` is even, and the 1-dimensional span of the
  alternating vector `altVec N = (1, 0, 1, 0, …)` when `N` is odd. Taking determinants of left
  multiplication on `CubicTorus N` (for `Even N`) or on the three central-idempotent eigenspaces
  `V_r = range (mulLeft e_r)` (for `Odd N`), and using `g_j ^ 12 = 1`, forces every central element
  of `G` to act by roots of unity of bounded order. Thus the kernel of the permutation action is
  finite, and hence `G` and the image of `gaussianBraidRep N` are finite
  (`finite_gaussianBraid_closure`, `finite_range_gaussianBraidRep`).

## Main definitions

* `TauCeti.TemperleyLieb.twelfthRootOfUnity`: the primitive 12th root of unity `u = exp (πi / 6)`
  in `ℂˣ`.
* `TauCeti.TemperleyLieb.gaussianBraidGenerator`, `TauCeti.TemperleyLieb.gaussianBraidUnit`,
  `TauCeti.TemperleyLieb.gaussianBraidFixedUnit`, and `TauCeti.TemperleyLieb.gaussianBraidRep`:
  the Gaussian braid generators `g_j` in `CubicTorus N`, their unit versions in `(CubicTorus N)ˣ`
  and `(cubicFixed N)ˣ`, and the induced braid group representation
  `BraidGroup (N + 1) →* (cubicFixed N)ˣ`.
* `TauCeti.TemperleyLieb.weylUnit` and `TauCeti.TemperleyLieb.cubicHeisenbergSubgroup`: the Weyl
  units `W(a)` and the finite Heisenberg subgroup `{(ω ^ c) • W(a)}` of `(CubicTorus N)ˣ`.

## Main results

* `TauCeti.TemperleyLieb.gaussianBraidGenerator_eq_weyl`,
  `TauCeti.TemperleyLieb.star_gaussianBraidGenerator_mul_self`,
  `TauCeti.TemperleyLieb.gaussianBraidGenerator_pow_three`,
  `TauCeti.TemperleyLieb.gaussianBraidGenerator_braid`, and
  `TauCeti.TemperleyLieb.cubicFixedHom_crossing_eq_gaussianBraidGenerator`: Weyl form, unitarity,
  order 12, braid relations, and comparison with the Jones representation.
* `TauCeti.TemperleyLieb.gaussianBraidGenerator_conj_weyl` and
  `TauCeti.TemperleyLieb.gaussianBraidClosure_conj_mem_cubicHeisenbergSubgroup`: symplectic
  transvection formula on Weyl elements and normalization of the finite Heisenberg subgroup.
* `TauCeti.TemperleyLieb.finite_gaussianBraid_closure` and
  `TauCeti.TemperleyLieb.finite_range_gaussianBraidRep`: finiteness of the Gaussian braid group
  image in `(CubicTorus N)ˣ` and `(cubicFixed N)ˣ` for every `N : ℕ`.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111.
* C. Galindo and E. C. Rowell, *Braid representations from unitary braided vector spaces*,
  J. Math. Phys. 55 (2014), 061702, Proposition 3.6.
* E. C. Rowell and H. Wenzl, `SO(N)_2` *braid group representations are Gaussian*, Quantum Topol.
  8 (2017), no. 1, 1–33.
-/

public section

namespace TauCeti.TemperleyLieb

/-! ### Arithmetic for the primitive 12th root of unity `u = exp (πi / 6)` -/

private theorem sqrt_three_mul_self : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
  exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)

private theorem sqrt_three_ne_zero : (Real.sqrt 3 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))

/-- The primitive 12th root of unity `u = exp (πi / 6)`, as a unit of `ℂ`. -/
noncomputable def twelfthRootOfUnity : ℂˣ :=
  Units.mk0 (Complex.exp ((Real.pi / 6 : ℝ) * Complex.I)) (Complex.exp_ne_zero _)

/-- Unfolding the underlying complex value of `twelfthRootOfUnity`. -/
theorem twelfthRootOfUnity_val :
    (twelfthRootOfUnity : ℂ) = Complex.exp ((Real.pi / 6 : ℝ) * Complex.I) :=
  (rfl)

/-- Rectangular form of `u = exp (πi / 6) = √3 / 2 + (1 / 2) * I`. -/
theorem twelfthRootOfUnity_val_eq :
    (twelfthRootOfUnity : ℂ) = (Real.sqrt 3 : ℂ) / 2 + (2 : ℂ)⁻¹ * Complex.I := by
  rw [twelfthRootOfUnity_val, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_six, Real.sin_pi_div_six]
  push_cast
  ring

/-- `u ^ 3 = I` in `ℂ`. -/
@[simp]
theorem twelfthRootOfUnity_val_pow_three : (twelfthRootOfUnity : ℂ) ^ 3 = Complex.I := by
  rw [twelfthRootOfUnity_val, ← Complex.exp_nat_mul]
  convert Complex.exp_pi_div_two_mul_I using 2
  push_cast
  ring

/-- `u ^ 4 = ω` in `ℂˣ`. -/
@[simp]
theorem twelfthRootOfUnity_pow_four : twelfthRootOfUnity ^ 4 = cubeRootOfUnity := by
  ext
  simp only [Units.val_pow_eq_pow_val, twelfthRootOfUnity_val, cubeRootOfUnity_val]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `u ^ 6 = -1` in `ℂ`. -/
@[simp]
theorem twelfthRootOfUnity_val_pow_six : (twelfthRootOfUnity : ℂ) ^ 6 = -1 := by
  calc
    (twelfthRootOfUnity : ℂ) ^ 6 = ((twelfthRootOfUnity : ℂ) ^ 3) ^ 2 := by ring
    _ = Complex.I ^ 2 := by rw [twelfthRootOfUnity_val_pow_three]
    _ = -1 := Complex.I_sq

/-- `u ^ 12 = 1` in `ℂˣ`. -/
@[simp]
theorem twelfthRootOfUnity_pow_twelve : twelfthRootOfUnity ^ 12 = 1 := by
  ext
  simp only [Units.val_pow_eq_pow_val, Units.val_one]
  calc
    (twelfthRootOfUnity : ℂ) ^ 12 = ((twelfthRootOfUnity : ℂ) ^ 6) ^ 2 := by ring
    _ = (-1 : ℂ) ^ 2 := by rw [twelfthRootOfUnity_val_pow_six]
    _ = 1 := by norm_num

/-- Complex conjugation sends `u` to `u⁻¹`. -/
@[simp]
theorem star_twelfthRootOfUnity_val :
    star (twelfthRootOfUnity : ℂ) = ((twelfthRootOfUnity⁻¹ : ℂˣ) : ℂ) := by
  have hinv : ((twelfthRootOfUnity⁻¹ : ℂˣ) : ℂ) = (twelfthRootOfUnity : ℂ)⁻¹ := rfl
  rw [hinv, twelfthRootOfUnity_val, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- Rectangular form of `u⁻¹ = √3 / 2 - (1 / 2) * I`. -/
theorem twelfthRootOfUnity_inv_val_eq :
    ((twelfthRootOfUnity⁻¹ : ℂˣ) : ℂ) = (Real.sqrt 3 : ℂ) / 2 - (2 : ℂ)⁻¹ * Complex.I := by
  rw [← star_twelfthRootOfUnity_val, twelfthRootOfUnity_val_eq]
  simp [sub_eq_add_neg]

/-- `u + u⁻¹ = √3`. -/
theorem twelfthRootOfUnity_add_inv :
    (twelfthRootOfUnity : ℂ) + ((twelfthRootOfUnity⁻¹ : ℂˣ) : ℂ) = (Real.sqrt 3 : ℂ) := by
  rw [twelfthRootOfUnity_val_eq, twelfthRootOfUnity_inv_val_eq]
  ring

/-- `1 + u ^ 2 = √3 * u`. -/
theorem one_add_twelfthRootOfUnity_sq :
    (1 : ℂ) + (twelfthRootOfUnity : ℂ) ^ 2 = (Real.sqrt 3 : ℂ) * (twelfthRootOfUnity : ℂ) := by
  rw [← twelfthRootOfUnity_add_inv]
  linear_combination -(twelfthRootOfUnity.inv_mul)

/-- `u ^ 2 = -ω ^ 2` in `ℂ`. -/
theorem twelfthRootOfUnity_sq_eq_neg_cubeRootOfUnity_sq :
    (twelfthRootOfUnity : ℂ) ^ 2 = -((cubeRootOfUnity : ℂ) ^ 2) := by
  have hw : (cubeRootOfUnity : ℂ) = (twelfthRootOfUnity : ℂ) ^ 4 := by
    rw [← twelfthRootOfUnity_pow_four, Units.val_pow_eq_pow_val]
  rw [hw]
  calc
    (twelfthRootOfUnity : ℂ) ^ 2 =
        -(twelfthRootOfUnity : ℂ) ^ 6 * (twelfthRootOfUnity : ℂ) ^ 2 := by
      rw [twelfthRootOfUnity_val_pow_six]
      ring
    _ = -((twelfthRootOfUnity : ℂ) ^ 4) ^ 2 := by ring

/-! ### The Gaussian braid generators `g_j` and their relations -/

/-- The `j`-th Gaussian braid generator `g_j = u • ((1 + u ^ 2) • p_j - 1)` in `CubicTorus N`. -/
noncomputable def gaussianBraidGenerator (N : ℕ) (j : Fin N) : CubicTorus N :=
  (twelfthRootOfUnity : ℂ) • ((1 + (twelfthRootOfUnity : ℂ) ^ 2) • cubicProjection N j - 1)

/-- Unfolding `gaussianBraidGenerator`. -/
theorem gaussianBraidGenerator_def (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j =
      (twelfthRootOfUnity : ℂ) • ((1 + (twelfthRootOfUnity : ℂ) ^ 2) • cubicProjection N j - 1) :=
  (rfl)

/-- Spectral decomposition of `g_j`: `g_j = I • p_j + (-u) • (1 - p_j)`. -/
theorem gaussianBraidGenerator_eq_spectral (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j =
      Complex.I • cubicProjection N j +
        (-(twelfthRootOfUnity : ℂ)) • (1 - cubicProjection N j) := by
  rw [gaussianBraidGenerator_def, ← twelfthRootOfUnity_val_pow_three]
  module

/-- Weyl-basis form of `g_j`: `g_j = -(√3)⁻¹ • (1 + ω ^ 2 • (U_j + U_j ^ 2))`. -/
theorem gaussianBraidGenerator_eq_weyl (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j =
      -(Real.sqrt 3 : ℂ)⁻¹ •
        (1 + ((cubeRootOfUnity : ℂ) ^ 2) • (cubicSite N j + cubicSite N j ^ 2)) := by
  have hc_sq :
      (Real.sqrt 3 : ℂ) *
          ((twelfthRootOfUnity : ℂ) * (1 + (twelfthRootOfUnity : ℂ) ^ 2) * (3 : ℂ)⁻¹) =
        (twelfthRootOfUnity : ℂ) ^ 2 := by
    rw [one_add_twelfthRootOfUnity_sq]
    calc
      (Real.sqrt 3 : ℂ) * ((twelfthRootOfUnity : ℂ) *
          ((Real.sqrt 3 : ℂ) * (twelfthRootOfUnity : ℂ)) * (3 : ℂ)⁻¹) =
          (((Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)) * (3 : ℂ)⁻¹) *
            (twelfthRootOfUnity : ℂ) ^ 2 := by ring
      _ = (twelfthRootOfUnity : ℂ) ^ 2 := by rw [sqrt_three_mul_self]; norm_num
  have hcoeff1 :
      (twelfthRootOfUnity : ℂ) * (1 + (twelfthRootOfUnity : ℂ) ^ 2) * (3 : ℂ)⁻¹ -
          (twelfthRootOfUnity : ℂ) = -(Real.sqrt 3 : ℂ)⁻¹ := by
    apply mul_left_cancel₀ sqrt_three_ne_zero
    rw [mul_sub, hc_sq, mul_neg, mul_inv_cancel₀ sqrt_three_ne_zero,
      ← one_add_twelfthRootOfUnity_sq]
    ring
  have hcoeff2 :
      (twelfthRootOfUnity : ℂ) * (1 + (twelfthRootOfUnity : ℂ) ^ 2) * (3 : ℂ)⁻¹ =
        -(Real.sqrt 3 : ℂ)⁻¹ * (cubeRootOfUnity : ℂ) ^ 2 := by
    apply mul_left_cancel₀ sqrt_three_ne_zero
    rw [hc_sq, ← mul_assoc, mul_neg, mul_inv_cancel₀ sqrt_three_ne_zero, neg_one_mul,
      ← twelfthRootOfUnity_sq_eq_neg_cubeRootOfUnity_sq]
  calc
    gaussianBraidGenerator N j =
        ((twelfthRootOfUnity : ℂ) * (1 + (twelfthRootOfUnity : ℂ) ^ 2) * (3 : ℂ)⁻¹ -
          (twelfthRootOfUnity : ℂ)) • (1 : CubicTorus N) +
        ((twelfthRootOfUnity : ℂ) * (1 + (twelfthRootOfUnity : ℂ) ^ 2) * (3 : ℂ)⁻¹) •
          (cubicSite N j + cubicSite N j ^ 2) := by
      rw [gaussianBraidGenerator_def, cubicProjection_def]
      module
    _ = -(Real.sqrt 3 : ℂ)⁻¹ •
          (1 + ((cubeRootOfUnity : ℂ) ^ 2) • (cubicSite N j + cubicSite N j ^ 2)) := by
      rw [hcoeff1, hcoeff2]
      module

/-- Weyl-basis form of the adjoint `star g_j`:
`star g_j = -(√3)⁻¹ • (1 + ω • (U_j + U_j ^ 2))`. -/
theorem star_gaussianBraidGenerator_eq_weyl (N : ℕ) (j : Fin N) :
    star (gaussianBraidGenerator N j) =
      -(Real.sqrt 3 : ℂ)⁻¹ • (1 + (cubeRootOfUnity : ℂ) • (cubicSite N j + cubicSite N j ^ 2)) := by
  have hstar_w2 : (star (cubeRootOfUnity : ℂ)) ^ 2 = (cubeRootOfUnity : ℂ) := by
    rw [star_cubeRootOfUnity_val, cubeRootOfUnity_inv_eq_sq, Units.val_pow_eq_pow_val]
    linear_combination (cubeRootOfUnity : ℂ) * cubeRootOfUnity_val_pow_three
  have hpow : (cubicSite N j ^ 2) ^ 2 = cubicSite N j := by
    calc
      (cubicSite N j ^ 2) ^ 2 = cubicSite N j ^ 3 * cubicSite N j := by noncomm_ring
      _ = cubicSite N j := by rw [cubicSite_pow_three, one_mul]
  rw [gaussianBraidGenerator_eq_weyl, star_smul, star_add, star_one, star_smul, star_add,
    star_pow, star_pow, star_cubicSite, hpow, hstar_w2,
    show star (-(Real.sqrt 3 : ℂ)⁻¹) = -(Real.sqrt 3 : ℂ)⁻¹ by simp]
  rw [add_comm (cubicSite N j ^ 2)]

/-- Every Gaussian braid generator lies in the inversion-fixed star-subalgebra `cubicFixed N`. -/
theorem gaussianBraidGenerator_mem_cubicFixed (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j ∈ cubicFixed N := by
  rw [gaussianBraidGenerator_def]
  exact (cubicFixed N).smul_mem
    ((cubicFixed N).sub_mem
      ((cubicFixed N).smul_mem (cubicProjection_mem_cubicFixed N j) _) (cubicFixed N).one_mem) _

/-- Spectral multiplication helper for linear combinations of an idempotent `p` and `1 - p`. -/
private theorem spectral_mul {A : Type*} [Ring A] [Algebra ℂ A] {p : A} (hp : p * p = p)
    (a₁ b₁ a₂ b₂ : ℂ) :
    (a₁ • p + b₁ • (1 - p)) * (a₂ • p + b₂ • (1 - p)) =
      (a₁ * a₂) • p + (b₁ * b₂) • (1 - p) := by
  have h1 : p * (1 - p) = 0 := by rw [mul_sub, mul_one, hp, sub_self]
  have h2 : (1 - p) * p = 0 := by rw [sub_mul, one_mul, hp, sub_self]
  have h3 : (1 - p) * (1 - p) = 1 - p := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hp]
    abel
  simp only [add_mul, mul_add, smul_mul_smul_comm, hp, h1, h2, h3, smul_zero, add_zero, zero_add]

/-- Every Gaussian braid generator is unitary: `star g_j * g_j = 1`. -/
@[simp]
theorem star_gaussianBraidGenerator_mul_self (N : ℕ) (j : Fin N) :
    star (gaussianBraidGenerator N j) * gaussianBraidGenerator N j = 1 := by
  rw [gaussianBraidGenerator_eq_spectral, star_add, star_smul, star_smul, star_cubicProjection,
    star_sub, star_one, star_cubicProjection, star_neg, star_twelfthRootOfUnity_val,
    Complex.star_def, Complex.conj_I,
    spectral_mul (cubicProjection_mul_self N j)]
  have hI : (-Complex.I) * Complex.I = 1 := by simp
  have hu : (-((twelfthRootOfUnity⁻¹ : ℂˣ) : ℂ)) * (-(twelfthRootOfUnity : ℂ)) = 1 := by
    rw [neg_mul_neg]
    exact twelfthRootOfUnity.inv_mul
  rw [hI, hu, one_smul, one_smul, add_sub_cancel]

/-- Every Gaussian braid generator is unitary: `g_j * star g_j = 1`. -/
@[simp]
theorem gaussianBraidGenerator_mul_star_self (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j * star (gaussianBraidGenerator N j) = 1 := by
  rw [gaussianBraidGenerator_eq_spectral, star_add, star_smul, star_smul, star_cubicProjection,
    star_sub, star_one, star_cubicProjection, star_neg, star_twelfthRootOfUnity_val,
    Complex.star_def, Complex.conj_I,
    spectral_mul (cubicProjection_mul_self N j)]
  have hI : Complex.I * (-Complex.I) = 1 := by simp
  have hu : (-(twelfthRootOfUnity : ℂ)) * (-((twelfthRootOfUnity⁻¹ : ℂˣ) : ℂ)) = 1 := by
    rw [neg_mul_neg]
    exact twelfthRootOfUnity.mul_inv
  rw [hI, hu, one_smul, one_smul, add_sub_cancel]

/-- Every Gaussian braid generator satisfies `g_j ^ 3 = (-I) • 1`. -/
@[simp]
theorem gaussianBraidGenerator_pow_three (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j ^ 3 = (-Complex.I) • 1 := by
  rw [gaussianBraidGenerator_eq_spectral, pow_succ, sq,
    spectral_mul (cubicProjection_mul_self N j), spectral_mul (cubicProjection_mul_self N j)]
  have hI3 : Complex.I * Complex.I * Complex.I = -Complex.I := by
    rw [Complex.I_mul_I, neg_one_mul]
  have hu3 :
      (-(twelfthRootOfUnity : ℂ)) * (-(twelfthRootOfUnity : ℂ)) * (-(twelfthRootOfUnity : ℂ)) =
        -Complex.I := by
    calc
      (-(twelfthRootOfUnity : ℂ)) * (-(twelfthRootOfUnity : ℂ)) * (-(twelfthRootOfUnity : ℂ)) =
          -((twelfthRootOfUnity : ℂ) ^ 3) := by ring
      _ = -Complex.I := by rw [twelfthRootOfUnity_val_pow_three]
  rw [hI3, hu3, ← smul_add, add_sub_cancel]

/-- Every Gaussian braid generator has order dividing `12`: `g_j ^ 12 = 1`. -/
@[simp]
theorem gaussianBraidGenerator_pow_twelve (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j ^ 12 = 1 := by
  calc
    gaussianBraidGenerator N j ^ 12 = (gaussianBraidGenerator N j ^ 3) ^ 4 := by
      rw [← pow_mul]
    _ = ((-Complex.I) • (1 : CubicTorus N)) ^ 4 := by rw [gaussianBraidGenerator_pow_three]
    _ = ((-Complex.I) ^ 4) • (1 : CubicTorus N) := by rw [smul_pow, one_pow]
    _ = 1 := by
      have h4 : (-Complex.I) ^ 4 = 1 := by
        calc
          (-Complex.I) ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
          _ = (-1 : ℂ) ^ 2 := by rw [Complex.I_sq]
          _ = 1 := by norm_num
      rw [h4, one_smul]

/-- Gaussian braid generators at distance at least two commute. -/
theorem gaussianBraidGenerator_mul_comm_of_dist_ge_two {N : ℕ} {j k : Fin N}
    (h : (j : ℕ) + 2 ≤ k ∨ (k : ℕ) + 2 ≤ j) :
    gaussianBraidGenerator N j * gaussianBraidGenerator N k =
      gaussianBraidGenerator N k * gaussianBraidGenerator N j := by
  have hp := (commute_cubicProjection_of_dist_ge_two h).eq
  simp only [gaussianBraidGenerator_def, smul_mul_smul_comm, mul_sub, sub_mul, mul_one, one_mul]
  congr 1
  rw [hp]
  abel

/-- **Braid relation** for adjacent Gaussian braid generators: `g_j * g_k * g_j = g_k * g_j * g_k`.
-/
theorem gaussianBraidGenerator_braid {N : ℕ} {j k : Fin N}
    (h : (j : ℕ) + 1 = k ∨ (k : ℕ) + 1 = j) :
    gaussianBraidGenerator N j * gaussianBraidGenerator N k * gaussianBraidGenerator N j =
      gaussianBraidGenerator N k * gaussianBraidGenerator N j * gaussianBraidGenerator N k := by
  set c : ℂ := -(1 + (twelfthRootOfUnity : ℂ) ^ 2)
  have hc : c + c ^ 2 + (3 : ℂ)⁻¹ * c ^ 3 = 0 := by
    have hsq : c ^ 2 = 3 * (twelfthRootOfUnity : ℂ) ^ 2 := by
      dsimp only [c]
      rw [one_add_twelfthRootOfUnity_sq]
      calc
        (-((Real.sqrt 3 : ℂ) * (twelfthRootOfUnity : ℂ))) ^ 2 =
            ((Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)) * (twelfthRootOfUnity : ℂ) ^ 2 := by ring
        _ = 3 * (twelfthRootOfUnity : ℂ) ^ 2 := by rw [sqrt_three_mul_self]
    have hpoly : c ^ 2 + 3 * c + 3 = 0 := by
      rw [hsq]
      dsimp only [c]
      ring
    linear_combination (3 : ℂ)⁻¹ * c * hpoly
  have hform : ∀ i : Fin N,
      gaussianBraidGenerator N i = (-(twelfthRootOfUnity : ℂ)) • (1 + c • cubicProjection N i) := by
    intro i
    rw [gaussianBraidGenerator_def]
    dsimp only [c]
    module
  have hexpand : ∀ a b : Fin N, ((a : ℕ) + 1 = b ∨ (b : ℕ) + 1 = a) →
      (1 + c • cubicProjection N a) * (1 + c • cubicProjection N b) *
          (1 + c • cubicProjection N a) =
        1 + c • cubicProjection N a + c • cubicProjection N b +
          c ^ 2 • (cubicProjection N a * cubicProjection N b +
            cubicProjection N b * cubicProjection N a) := by
    intro a b hab
    have haa : cubicProjection N a * cubicProjection N a = cubicProjection N a :=
      cubicProjection_mul_self N a
    have haba :
        cubicProjection N a * cubicProjection N b * cubicProjection N a =
          (3 : ℂ)⁻¹ • cubicProjection N a :=
      cubicProjection_mul_cubicProjection_mul_of_adj hab
    calc
      (1 + c • cubicProjection N a) * (1 + c • cubicProjection N b) *
          (1 + c • cubicProjection N a) =
          1 + (2 * c) • cubicProjection N a + c • cubicProjection N b +
            (c ^ 2) • (cubicProjection N a * cubicProjection N a) +
            (c ^ 2) • (cubicProjection N a * cubicProjection N b +
              cubicProjection N b * cubicProjection N a) +
            (c ^ 3) • (cubicProjection N a * cubicProjection N b * cubicProjection N a) := by
        simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, pow_succ]
        module
      _ = 1 + c • cubicProjection N a + c • cubicProjection N b +
            (c ^ 2) • (cubicProjection N a * cubicProjection N b +
              cubicProjection N b * cubicProjection N a) +
            (c + c ^ 2 + (3 : ℂ)⁻¹ * c ^ 3) • cubicProjection N a := by
        rw [haa, haba, smul_smul]
        module
      _ = 1 + c • cubicProjection N a + c • cubicProjection N b +
            c ^ 2 • (cubicProjection N a * cubicProjection N b +
              cubicProjection N b * cubicProjection N a) := by
        rw [hc, zero_smul, add_zero]
  rw [hform j, hform k, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm,
    smul_mul_smul_comm, hexpand j k h, hexpand k j h.symm]
  congr 1
  module

/-! ### Units, the Gaussian braid group representation, and comparison with `TemperleyLieb.jones` -/

/-- The `j`-th Gaussian braid generator as a unit of `CubicTorus N`. -/
noncomputable def gaussianBraidUnit (N : ℕ) (j : Fin N) : (CubicTorus N)ˣ where
  val := gaussianBraidGenerator N j
  inv := star (gaussianBraidGenerator N j)
  val_inv := gaussianBraidGenerator_mul_star_self N j
  inv_val := star_gaussianBraidGenerator_mul_self N j

/-- The underlying element of `gaussianBraidUnit N j` is `gaussianBraidGenerator N j`. -/
@[simp]
theorem gaussianBraidUnit_val (N : ℕ) (j : Fin N) :
    (gaussianBraidUnit N j : CubicTorus N) = gaussianBraidGenerator N j :=
  (rfl)

/-- The inverse of `gaussianBraidUnit N j` is `star (gaussianBraidGenerator N j)`. -/
@[simp]
theorem gaussianBraidUnit_inv_val (N : ℕ) (j : Fin N) :
    ((gaussianBraidUnit N j)⁻¹ : (CubicTorus N)ˣ).val = star (gaussianBraidGenerator N j) :=
  (rfl)

/-- Every `gaussianBraidUnit N j` has order dividing `12`. -/
@[simp]
theorem gaussianBraidUnit_pow_twelve (N : ℕ) (j : Fin N) :
    gaussianBraidUnit N j ^ 12 = 1 :=
  Units.ext (by simp)

/-- The `j`-th Gaussian braid generator as a unit of `cubicFixed N`. -/
noncomputable def gaussianBraidFixedUnit (N : ℕ) (j : Fin N) : (cubicFixed N)ˣ where
  val := ⟨gaussianBraidGenerator N j, gaussianBraidGenerator_mem_cubicFixed N j⟩
  inv :=
    ⟨star (gaussianBraidGenerator N j),
      star_mem (gaussianBraidGenerator_mem_cubicFixed N j)⟩
  val_inv := Subtype.ext (gaussianBraidGenerator_mul_star_self N j)
  inv_val := Subtype.ext (star_gaussianBraidGenerator_mul_self N j)

/-- Coercing `gaussianBraidFixedUnit N j` to `CubicTorus N` gives `gaussianBraidGenerator N j`. -/
@[simp]
theorem coe_gaussianBraidFixedUnit_val (N : ℕ) (j : Fin N) :
    (((gaussianBraidFixedUnit N j : (cubicFixed N)ˣ) : cubicFixed N) : CubicTorus N) =
      gaussianBraidGenerator N j :=
  (rfl)

/-- Every `gaussianBraidFixedUnit N j` has order dividing `12`. -/
@[simp]
theorem gaussianBraidFixedUnit_pow_twelve (N : ℕ) (j : Fin N) :
    gaussianBraidFixedUnit N j ^ 12 = 1 :=
  Units.ext <| Subtype.ext <| by
    simp only [Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow, coe_gaussianBraidFixedUnit_val,
      Units.val_one, OneMemClass.coe_one, gaussianBraidGenerator_pow_twelve]

/-- The Gaussian braid group representation `BraidGroup (N + 1) →* (cubicFixed N)ˣ`, sending each
Artin generator `σ_j` to `gaussianBraidFixedUnit N j`. -/
noncomputable def gaussianBraidRep (N : ℕ) : BraidGroup (N + 1) →* (cubicFixed N)ˣ :=
  BraidGroup.lift (fun j ↦ gaussianBraidFixedUnit N j)
    (fun h ↦ Units.ext <| Subtype.ext <| gaussianBraidGenerator_mul_comm_of_dist_ge_two h)
    (fun h ↦ Units.ext <| Subtype.ext <| gaussianBraidGenerator_braid h)

/-- `gaussianBraidRep N` sends each elementary braid `BraidGroup.sigma j` to
`gaussianBraidFixedUnit N j`. -/
@[simp]
theorem gaussianBraidRep_sigma (N : ℕ) (j : Fin N) :
    gaussianBraidRep N (BraidGroup.sigma j) = gaussianBraidFixedUnit N j :=
  BraidGroup.lift_sigma (n := N + 1) _ _ _ j

/-- For any unit `a : ℂˣ` with `a ^ 2 = -u⁻¹`, the Jones loop value `jonesDelta a` equals `√3`. -/
theorem jonesDelta_eq_sqrt_three {a : ℂˣ}
    (ha : (a : ℂ) ^ 2 = -((twelfthRootOfUnity⁻¹ : ℂˣ) : ℂ)) :
    jonesDelta a = (Real.sqrt 3 : ℂ) := by
  have hinv : ((a⁻¹ : ℂˣ) : ℂ) ^ 2 = -(twelfthRootOfUnity : ℂ) := by
    have hmul : (a : ℂ) ^ 2 * ((a⁻¹ : ℂˣ) : ℂ) ^ 2 = 1 := by
      rw [← mul_pow, a.mul_inv, one_pow]
    have hmul' : (a : ℂ) ^ 2 * (-(twelfthRootOfUnity : ℂ)) = 1 := by
      rw [ha, neg_mul_neg]
      exact twelfthRootOfUnity.inv_mul
    exact mul_left_cancel₀ (pow_ne_zero 2 a.ne_zero) (hmul.trans hmul'.symm)
  rw [jonesDelta_def, ha, hinv, ← neg_add, neg_neg, add_comm, twelfthRootOfUnity_add_inv]

/-- Explicit existence of a Jones parameter `a = exp (5πi / 12)` satisfying `a ^ 2 = -u⁻¹` (and
hence `jonesDelta a = √3`). -/
theorem exists_jonesParam_sqrt_three :
    ∃ a : ℂˣ, (a : ℂ) ^ 2 = -((twelfthRootOfUnity⁻¹ : ℂˣ) : ℂ) ∧
      jonesDelta a = (Real.sqrt 3 : ℂ) := by
  let a : ℂˣ := Units.mk0 (Complex.exp ((5 * Real.pi / 12 : ℝ) * Complex.I)) (Complex.exp_ne_zero _)
  have ha : (a : ℂ) ^ 2 = -((twelfthRootOfUnity⁻¹ : ℂˣ) : ℂ) := by
    have hinv :
        ((twelfthRootOfUnity⁻¹ : ℂˣ) : ℂ) = Complex.exp (-(Real.pi / 6 : ℝ) * Complex.I) := by
      change (twelfthRootOfUnity : ℂ)⁻¹ = _
      rw [twelfthRootOfUnity_val, ← Complex.exp_neg]
      congr 1
      ring
    rw [hinv]
    change Complex.exp ((5 * Real.pi / 12 : ℝ) * Complex.I) ^ 2 = _
    rw [← Complex.exp_nat_mul]
    have hexp :
        (2 : ℕ) * (((5 * Real.pi / 12 : ℝ) : ℂ) * Complex.I) =
          (Real.pi : ℂ) * Complex.I + (-((Real.pi / 6 : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [hexp, Complex.exp_add, Complex.exp_pi_mul_I, neg_one_mul]
  exact ⟨a, ha, jonesDelta_eq_sqrt_three ha⟩

/-- Under `cubicFixedHom m`, the Kauffman-bracket crossing `a • 1 + a⁻¹ • e j` at loop value `√3`
maps to `(-a / u) • g_j` whenever `a ^ 2 = -u⁻¹`. -/
theorem cubicFixedHom_crossing_eq_gaussianBraidGenerator (m : ℕ) (j : Fin (m - 1))
    {a : ℂˣ} (ha : (a : ℂ) ^ 2 = -((twelfthRootOfUnity⁻¹ : ℂˣ) : ℂ)) :
    (cubicFixedHom m (crossing (Real.sqrt 3 : ℂ) (a : ℂ) ((a⁻¹ : ℂˣ) : ℂ) j) :
        CubicTorus (m - 1)) =
      (-(a : ℂ) / (twelfthRootOfUnity : ℂ)) • gaussianBraidGenerator (m - 1) j := by
  have hau : -(a : ℂ) * (twelfthRootOfUnity : ℂ) = ((a⁻¹ : ℂˣ) : ℂ) := by
    apply mul_left_cancel₀ a.ne_zero
    calc
      (a : ℂ) * (-(a : ℂ) * (twelfthRootOfUnity : ℂ)) =
          -((a : ℂ) ^ 2 * (twelfthRootOfUnity : ℂ)) := by ring
      _ = -(-((twelfthRootOfUnity⁻¹ : ℂˣ) : ℂ) * (twelfthRootOfUnity : ℂ)) := by rw [ha]
      _ = 1 := by rw [neg_mul, neg_neg]; exact twelfthRootOfUnity.inv_mul
      _ = (a : ℂ) * ((a⁻¹ : ℂˣ) : ℂ) := a.mul_inv.symm
  rw [crossing_def, map_add, map_smul, map_smul, map_one, AddMemClass.coe_add,
    SetLike.val_smul, SetLike.val_smul, OneMemClass.coe_one, coe_cubicFixedHom_e,
    gaussianBraidGenerator_def, smul_smul, smul_smul, div_mul_cancel₀ _ twelfthRootOfUnity.ne_zero,
    smul_sub, smul_smul, one_add_twelfthRootOfUnity_sq,
    show -(a : ℂ) * ((Real.sqrt 3 : ℂ) * (twelfthRootOfUnity : ℂ)) =
      ((a⁻¹ : ℂˣ) : ℂ) * (Real.sqrt 3 : ℂ) by rw [← hau]; ring]
  module

/-- Under `cubicFixedHom m`, the Jones braid unit `jonesUnit a j` (transported across
`jonesDelta a = √3`) maps to `(-a / u) • g_j` whenever `a ^ 2 = -u⁻¹`. -/
theorem cubicFixedHom_jonesUnit (m : ℕ) (j : Fin (m - 1))
    {a : ℂˣ} (ha : (a : ℂ) ^ 2 = -((twelfthRootOfUnity⁻¹ : ℂˣ) : ℂ)) :
    (cubicFixedHom m
        (jonesDelta_eq_sqrt_three ha ▸
          (jonesUnit a j : TemperleyLieb ℂ (jonesDelta a) m)) : CubicTorus (m - 1)) =
      (-(a : ℂ) / (twelfthRootOfUnity : ℂ)) • gaussianBraidGenerator (m - 1) j := by
  have hcast : ∀ {δ₁ δ₂ : ℂ} (hδ : δ₁ = δ₂),
      (hδ ▸ crossing δ₁ (a : ℂ) ((a⁻¹ : ℂˣ) : ℂ) j : TemperleyLieb ℂ δ₂ m) =
        crossing δ₂ (a : ℂ) ((a⁻¹ : ℂˣ) : ℂ) j := by
    rintro δ₁ _ rfl
    rfl
  rw [jonesUnit_val, hcast]
  exact cubicFixedHom_crossing_eq_gaussianBraidGenerator m j ha

/-! ### Symplectic transvection on Weyl elements and the finite Heisenberg subgroup -/

/-- Each Weyl basis element `W(a)` as a unit of `CubicTorus N`, with inverse `W(a⁻¹)`. -/
noncomputable def weylUnit (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) : (CubicTorus N)ˣ where
  val := weyl N a
  inv := weyl N a⁻¹
  val_inv := weyl_mul_inv N a
  inv_val := weyl_inv_mul N a

/-- Unfolding the value of `weylUnit N a`. -/
@[simp]
theorem weylUnit_val (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    (weylUnit N a : CubicTorus N) = weyl N a :=
  (rfl)

/-- The finite **cubic Heisenberg subgroup** `H_N ≤ (CubicTorus N)ˣ`, consisting of all phase-scaled
Weyl units `(ω ^ c) • W(a)` for `c : ZMod 3` and `a : Multiplicative (Fin N → ZMod 3)`. -/
noncomputable def cubicHeisenbergSubgroup (N : ℕ) : Subgroup (CubicTorus N)ˣ where
  carrier :=
    {u | ∃ (c : ZMod 3) (a : Multiplicative (Fin N → ZMod 3)),
      (u : CubicTorus N) = (cubeRootPow c : ℂ) • weyl N a}
  one_mem' := ⟨0, 1, by simp⟩
  mul_mem' := by
    rintro u v ⟨c₁, a, ha⟩ ⟨c₂, b, hb⟩
    refine ⟨c₁ + c₂ + 2 * chainForm N a.toAdd b.toAdd, a * b, ?_⟩
    rw [Units.val_mul, ha, hb, smul_mul_smul_comm, weyl_mul, smul_smul, cubicFactor_def]
    simp only [cubeRootPow_add, Units.val_mul]
  inv_mem' := by
    rintro u ⟨c, a, ha⟩
    refine ⟨-c, a⁻¹, ?_⟩
    have hinv : (u : CubicTorus N) * ((cubeRootPow (-c) : ℂ) • weyl N a⁻¹) = 1 := by
      rw [ha, smul_mul_smul_comm, weyl_mul_inv, cubeRootPow_neg, Units.mul_inv, one_smul]
    calc
      ((u⁻¹ : (CubicTorus N)ˣ) : CubicTorus N) =
          ((u⁻¹ : (CubicTorus N)ˣ) : CubicTorus N) *
            ((u : CubicTorus N) * ((cubeRootPow (-c) : ℂ) • weyl N a⁻¹)) := by
        rw [hinv, mul_one]
      _ = (((u⁻¹ : (CubicTorus N)ˣ) : CubicTorus N) * (u : CubicTorus N)) *
            ((cubeRootPow (-c) : ℂ) • weyl N a⁻¹) := by
        rw [mul_assoc]
      _ = (cubeRootPow (-c) : ℂ) • weyl N a⁻¹ := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

/-- The cubic Heisenberg subgroup `cubicHeisenbergSubgroup N` is finite. -/
instance finite_cubicHeisenbergSubgroup (N : ℕ) : Finite (cubicHeisenbergSubgroup N) := by
  refine Finite.of_surjective
    (f := fun p : ZMod 3 × Multiplicative (Fin N → ZMod 3) ↦
      (⟨⟨(cubeRootPow p.1 : ℂ) • weyl N p.2,
          (cubeRootPow (-p.1) : ℂ) • weyl N p.2⁻¹,
          by rw [smul_mul_smul_comm, weyl_mul_inv, cubeRootPow_neg, Units.mul_inv, one_smul],
          by rw [smul_mul_smul_comm, weyl_inv_mul, cubeRootPow_neg, Units.inv_mul, one_smul]⟩,
        ⟨p.1, p.2, rfl⟩⟩ : cubicHeisenbergSubgroup N)) ?_
  rintro ⟨u, c, a, ha⟩
  exact ⟨(c, a), Subtype.ext (Units.ext ha.symm)⟩

/-- **Metaplectic symplectic transvection**: conjugating any Weyl basis element `W(a)` by the
Gaussian braid generator `g_j` produces `W(a + B(a, e_j) • e_j)` with trivial phase factor. -/
theorem gaussianBraidGenerator_conj_weyl (N : ℕ) (j : Fin N)
    (a : Multiplicative (Fin N → ZMod 3)) :
    gaussianBraidGenerator N j * weyl N a * star (gaussianBraidGenerator N j) =
      weyl N
        (Multiplicative.ofAdd (a.toAdd + chainForm N a.toAdd (Pi.single j 1) • Pi.single j 1)) := by
  have hUcomm :
      cubicSite N j * weyl N a =
        (cubeRootPow (-chainForm N a.toAdd (Pi.single j 1)) : ℂ) • (weyl N a * cubicSite N j) := by
    rw [cubicSite_def, weyl_mul_comm, toAdd_ofAdd, chainForm_swap]
  have hval :
      chainForm N a.toAdd (Pi.single j 1) = 0 ∨
        chainForm N a.toAdd (Pi.single j 1) = 1 ∨
        chainForm N a.toAdd (Pi.single j 1) = 2 := by
    have : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
    exact this _
  have hsqrt_inv : (-(Real.sqrt 3 : ℂ)⁻¹) * (-(Real.sqrt 3 : ℂ)⁻¹) = (3 : ℂ)⁻¹ := by
    rw [neg_mul_neg, ← mul_inv, sqrt_three_mul_self]
  have hw3 : (cubeRootOfUnity : ℂ) ^ 3 = 1 := cubeRootOfUnity_val_pow_three
  have hw4 : (cubeRootOfUnity : ℂ) ^ 2 * (cubeRootOfUnity : ℂ) ^ 2 = (cubeRootOfUnity : ℂ) := by
    linear_combination (cubeRootOfUnity : ℂ) * hw3
  have hw3' : (cubeRootOfUnity : ℂ) ^ 2 * (cubeRootOfUnity : ℂ) = 1 := by
    linear_combination hw3
  have hcyc : (1 : ℂ) + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2 = 0 :=
    one_add_cubeRootOfUnity_add_sq
  have hcw : (cubeRootOfUnity : ℂ) * (cubeRootPow 2 : ℂ) = 1 := by
    have h2' : (2 : ZMod 3) = -1 := by decide
    rw [h2', cubeRootPow_neg, cubeRootPow_one]
    exact cubeRootOfUnity.mul_inv
  have hU3 : cubicSite N j ^ 3 = 1 := cubicSite_pow_three N j
  have hU4 : cubicSite N j ^ 2 * cubicSite N j ^ 2 = cubicSite N j := by
    calc
      cubicSite N j ^ 2 * cubicSite N j ^ 2 = cubicSite N j ^ 3 * cubicSite N j := by noncomm_ring
      _ = cubicSite N j := by rw [hU3, one_mul]
  have hU21 : cubicSite N j ^ 2 * cubicSite N j = 1 := by
    calc
      cubicSite N j ^ 2 * cubicSite N j = cubicSite N j ^ 3 := by noncomm_ring
      _ = 1 := hU3
  have hU12 : cubicSite N j * cubicSite N j ^ 2 = 1 := by
    calc
      cubicSite N j * cubicSite N j ^ 2 = cubicSite N j ^ 3 := by noncomm_ring
      _ = 1 := hU3
  rcases hval with hB | hB | hB
  · -- Case `B(a, e_j) = 0`: `U_j` commutes with `W(a)`, so `g_j` commutes with `W(a)`.
    rw [hB, zero_smul, add_zero, ofAdd_toAdd]
    have hcomm : cubicSite N j * weyl N a = weyl N a * cubicSite N j := by
      simpa [hB] using hUcomm
    have hcomm2 : cubicSite N j ^ 2 * weyl N a = weyl N a * cubicSite N j ^ 2 := by
      rw [sq, mul_assoc, hcomm, ← mul_assoc, hcomm, mul_assoc, ← sq]
    have hgcomm :
        gaussianBraidGenerator N j * weyl N a = weyl N a * gaussianBraidGenerator N j := by
      rw [gaussianBraidGenerator_eq_weyl]
      simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, one_mul, mul_one, hcomm, hcomm2]
    rw [hgcomm, mul_assoc, gaussianBraidGenerator_mul_star_self, mul_one]
  · -- Case `B(a, e_j) = 1`: `U_j W(a) = ω² W(a) U_j` and `g_j W(a) g_j* = W(a + e_j)`.
    have hU1 : cubicSite N j * weyl N a =
        ((cubeRootOfUnity : ℂ) ^ 2) • (weyl N a * cubicSite N j) := by
      simpa [hB, cubeRootPow_neg, cubeRootPow_one, cubeRootOfUnity_inv_eq_sq] using hUcomm
    have hU2 : cubicSite N j ^ 2 * weyl N a =
        (cubeRootOfUnity : ℂ) • (weyl N a * cubicSite N j ^ 2) := by
      rw [sq, mul_assoc, hU1, mul_smul_comm, ← mul_assoc, hU1, smul_mul_assoc, smul_smul, hw4,
        mul_assoc, ← sq]
    have hleft :
        (1 + ((cubeRootOfUnity : ℂ) ^ 2) • (cubicSite N j + cubicSite N j ^ 2)) * weyl N a =
          weyl N a * (1 + (cubeRootOfUnity : ℂ) • cubicSite N j + cubicSite N j ^ 2) := by
      rw [add_mul, one_mul, smul_mul_assoc, add_mul, hU1, hU2, smul_add, smul_smul, smul_smul,
        mul_add, mul_add, mul_one, mul_smul_comm, hw4, hw3', one_smul, add_assoc]
    have hprod :
        (1 + (cubeRootOfUnity : ℂ) • cubicSite N j + cubicSite N j ^ 2) *
            (1 + (cubeRootOfUnity : ℂ) • (cubicSite N j + cubicSite N j ^ 2)) =
          (3 * (cubeRootOfUnity : ℂ)) • cubicSite N j := by
      calc
        (1 + (cubeRootOfUnity : ℂ) • cubicSite N j + cubicSite N j ^ 2) *
            (1 + (cubeRootOfUnity : ℂ) • (cubicSite N j + cubicSite N j ^ 2)) =
            (1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2) • (1 : CubicTorus N) +
              (3 * (cubeRootOfUnity : ℂ)) • cubicSite N j +
              (1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2) • cubicSite N j ^ 2 := by
          simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
            hU4, hU21, hU12, ← sq]
          module
        _ = (3 * (cubeRootOfUnity : ℂ)) • cubicSite N j := by
          rw [hcyc, zero_smul, zero_smul, zero_add, add_zero]
    have hconj :
        gaussianBraidGenerator N j * weyl N a * star (gaussianBraidGenerator N j) =
          (cubeRootOfUnity : ℂ) • (weyl N a * cubicSite N j) := by
      rw [star_gaussianBraidGenerator_eq_weyl, gaussianBraidGenerator_eq_weyl, smul_mul_assoc,
        smul_mul_smul_comm, hsqrt_inv, hleft, mul_assoc, hprod, mul_smul_comm, smul_smul]
      congr 1
      ring
    rw [hconj, cubicSite_def, weyl_mul, smul_smul, cubicFactor_def, toAdd_ofAdd, hB, one_smul]
    have h2 : (2 : ZMod 3) * 1 = 2 := by decide
    rw [h2, hcw, one_smul, ← ofAdd_toAdd a, ← ofAdd_add, ofAdd_toAdd]
  · -- Case `B(a, e_j) = 2`: `U_j W(a) = ω W(a) U_j` and `g_j W(a) g_j* = W(a + 2 e_j)`.
    have hneg2 : -(2 : ZMod 3) = 1 := by decide
    have hU1 : cubicSite N j * weyl N a =
        (cubeRootOfUnity : ℂ) • (weyl N a * cubicSite N j) := by
      simpa [hB, hneg2, cubeRootPow_one] using hUcomm
    have hU2 : cubicSite N j ^ 2 * weyl N a =
        ((cubeRootOfUnity : ℂ) ^ 2) • (weyl N a * cubicSite N j ^ 2) := by
      rw [sq, mul_assoc, hU1, mul_smul_comm, ← mul_assoc, hU1, smul_mul_assoc, smul_smul,
        ← sq (cubeRootOfUnity : ℂ), mul_assoc, ← sq (cubicSite N j)]
    have hleft :
        (1 + ((cubeRootOfUnity : ℂ) ^ 2) • (cubicSite N j + cubicSite N j ^ 2)) * weyl N a =
          weyl N a * (1 + cubicSite N j + (cubeRootOfUnity : ℂ) • cubicSite N j ^ 2) := by
      rw [add_mul, one_mul, smul_mul_assoc, add_mul, hU1, hU2, smul_add, smul_smul, smul_smul,
        mul_add, mul_add, mul_one, mul_smul_comm, hw4, hw3', one_smul, add_assoc]
    have hprod :
        (1 + cubicSite N j + (cubeRootOfUnity : ℂ) • cubicSite N j ^ 2) *
            (1 + (cubeRootOfUnity : ℂ) • (cubicSite N j + cubicSite N j ^ 2)) =
          (3 * (cubeRootOfUnity : ℂ)) • cubicSite N j ^ 2 := by
      calc
        (1 + cubicSite N j + (cubeRootOfUnity : ℂ) • cubicSite N j ^ 2) *
            (1 + (cubeRootOfUnity : ℂ) • (cubicSite N j + cubicSite N j ^ 2)) =
            (1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2) • (1 : CubicTorus N) +
              (1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2) • cubicSite N j +
              (3 * (cubeRootOfUnity : ℂ)) • cubicSite N j ^ 2 := by
          simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
            hU4, hU21, hU12, ← sq]
          module
        _ = (3 * (cubeRootOfUnity : ℂ)) • cubicSite N j ^ 2 := by
          rw [hcyc, zero_smul, zero_smul, zero_add, zero_add]
    have hconj :
        gaussianBraidGenerator N j * weyl N a * star (gaussianBraidGenerator N j) =
          (cubeRootOfUnity : ℂ) • (weyl N a * cubicSite N j ^ 2) := by
      rw [star_gaussianBraidGenerator_eq_weyl, gaussianBraidGenerator_eq_weyl, smul_mul_assoc,
        smul_mul_smul_comm, hsqrt_inv, hleft, mul_assoc, hprod, mul_smul_comm, smul_smul]
      congr 1
      ring
    rw [hconj, cubicSite_def, weyl_sq, weyl_mul, smul_smul, cubicFactor_def, toAdd_inv, toAdd_ofAdd,
      chainForm_neg_right, hB]
    have h2 : (2 : ZMod 3) * -(2 : ZMod 3) = 2 := by decide
    rw [h2, hcw, one_smul]
    congr 1
    apply Multiplicative.toAdd.injective
    ext i
    simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
      smul_eq_mul]
    have h2neg : (2 : ZMod 3) = -1 := by decide
    rw [h2neg]
    ring

/-- Every Gaussian braid generator normalizes `cubicHeisenbergSubgroup N`. -/
theorem gaussianBraidUnit_conj_mem_cubicHeisenbergSubgroup (N : ℕ) (j : Fin N)
    {h : (CubicTorus N)ˣ} (hh : h ∈ cubicHeisenbergSubgroup N) :
    gaussianBraidUnit N j * h * (gaussianBraidUnit N j)⁻¹ ∈ cubicHeisenbergSubgroup N := by
  rcases hh with ⟨c, a, ha⟩
  refine ⟨c,
    Multiplicative.ofAdd (a.toAdd + chainForm N a.toAdd (Pi.single j 1) • Pi.single j 1), ?_⟩
  simp only [Units.val_mul, gaussianBraidUnit_val, gaussianBraidUnit_inv_val, ha, mul_smul_comm,
    smul_mul_assoc, gaussianBraidGenerator_conj_weyl]

/-- Every element of `Subgroup.closure (Set.range (gaussianBraidUnit N))` normalizes
`cubicHeisenbergSubgroup N`. -/
theorem gaussianBraidClosure_conj_mem_cubicHeisenbergSubgroup (N : ℕ)
    {g : (CubicTorus N)ˣ} (hg : g ∈ Subgroup.closure (Set.range (gaussianBraidUnit N)))
    {h : (CubicTorus N)ˣ} (hh : h ∈ cubicHeisenbergSubgroup N) :
    g * h * g⁻¹ ∈ cubicHeisenbergSubgroup N := by
  let S : Subgroup (CubicTorus N)ˣ :=
    { carrier := {u | ∀ x ∈ cubicHeisenbergSubgroup N, u * x * u⁻¹ ∈ cubicHeisenbergSubgroup N ∧
        u⁻¹ * x * u ∈ cubicHeisenbergSubgroup N}
      one_mem' := fun x hx ↦ by simpa using hx
      mul_mem' := fun {u v} hu hv x hx ↦ by
        refine ⟨?_, ?_⟩
        · have h1 := (hv x hx).1
          have h2 := (hu _ h1).1
          simpa [mul_assoc] using h2
        · have h1 := (hu x hx).2
          have h2 := (hv _ h1).2
          simpa [mul_assoc] using h2
      inv_mem' := fun {u} hu x hx ↦ by
        simpa using (hu x hx).symm }
  have hle : Subgroup.closure (Set.range (gaussianBraidUnit N)) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩ x hx
    refine ⟨gaussianBraidUnit_conj_mem_cubicHeisenbergSubgroup N j hx, ?_⟩
    have hinv_eq : (gaussianBraidUnit N j)⁻¹ = gaussianBraidUnit N j ^ 11 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', gaussianBraidUnit_pow_twelve]
    rw [hinv_eq]
    have hpow : ∀ k : ℕ, ∀ y ∈ cubicHeisenbergSubgroup N,
        gaussianBraidUnit N j ^ k * y * (gaussianBraidUnit N j ^ k)⁻¹ ∈
          cubicHeisenbergSubgroup N := by
      intro k
      induction k with
      | zero => intro y hy; simpa using hy
      | succ k ih =>
        intro y hy
        have hstep := gaussianBraidUnit_conj_mem_cubicHeisenbergSubgroup N j (ih y hy)
        simpa [pow_succ', mul_assoc] using hstep
    simpa [← hinv_eq] using hpow 11 x hx
  exact (hle hg h hh).1

/-! ### Radical of `chainForm N`, center of `CubicTorus N`, and finiteness of the braid group -/

/-- The alternating vector `altVec N : Fin N → ZMod 3` with `1` in even positions and `0` in odd
positions; for odd `N`, it spans the radical of `chainForm N`. -/
private def altVec (N : ℕ) : Fin N → ZMod 3 :=
  fun i ↦ if Even (i : ℕ) then 1 else 0

private theorem chainForm_altVec_single {N : ℕ} (hodd : Odd N) (k : Fin N) :
    chainForm N (altVec N) (Pi.single k 1) = 0 := by
  rw [chainForm_single_right]
  by_cases hk : Even (k : ℕ)
  · have h1 :
        (if h : 0 < (k : ℕ) then altVec N ⟨(k : ℕ) - 1, by omega⟩ else 0) = 0 := by
      split_ifs with hpos
      · have hnot : ¬ Even ((k : ℕ) - 1) := by
          obtain ⟨r, hr⟩ := hk
          intro ⟨s, hs⟩
          omega
        simp [altVec, hnot]
      · rfl
    have h2 :
        (if h : (k : ℕ) + 1 < N then altVec N ⟨(k : ℕ) + 1, h⟩ else 0) = 0 := by
      split_ifs with hlt
      · have hnot : ¬ Even ((k : ℕ) + 1) := by
          obtain ⟨r, hr⟩ := hk
          intro ⟨s, hs⟩
          omega
        simp [altVec, hnot]
      · rfl
    rw [h1, h2, sub_self]
  · obtain ⟨m, hm⟩ := hodd
    have hpos : 0 < (k : ℕ) := by
      by_contra h0
      exact hk ⟨0, by omega⟩
    have hlt : (k : ℕ) + 1 < N := by
      have := k.isLt
      by_contra hge
      exact hk ⟨m, by omega⟩
    have hev1 : Even ((k : ℕ) - 1) := by
      rcases Nat.even_or_odd (k : ℕ) with hev | ⟨r, hr⟩
      · exact absurd hev hk
      · exact ⟨r, by omega⟩
    have hev2 : Even ((k : ℕ) + 1) := by
      rcases Nat.even_or_odd (k : ℕ) with hev | ⟨r, hr⟩
      · exact absurd hev hk
      · exact ⟨r + 1, by omega⟩
    simp [hpos, hlt, altVec, hev1, hev2]

private theorem chainForm_altVec_left {N : ℕ} (hodd : Odd N) (b : Fin N → ZMod 3) :
    chainForm N (altVec N) b = 0 := by
  have hb : b = ∑ k : Fin N, b k • Pi.single k 1 := by
    ext i
    simp [Pi.single_apply]
  rw [hb]
  have hsum : ∀ (s : Finset (Fin N)),
      chainForm N (altVec N) (∑ k ∈ s, b k • Pi.single k 1) = 0 := by
    intro s
    induction s using Finset.cons_induction with
    | empty => simp
    | cons k s hks ih =>
      rw [Finset.sum_cons, chainForm_add_right, ih, add_zero]
      have hval : b k = 0 ∨ b k = 1 ∨ b k = 2 := by
        have : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
        exact this (b k)
      rcases hval with hc | hc | hc
      · simp [hc]
      · simp [hc, chainForm_altVec_single hodd k]
      · have h2 : (2 : ZMod 3) • (Pi.single k (1 : ZMod 3) : Fin N → ZMod 3) =
            -(Pi.single k 1) := by
          ext i
          simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
          have h2neg : (2 : ZMod 3) = -1 := by decide
          rw [h2neg]
          ring
        rw [hc, h2, chainForm_neg_right, chainForm_altVec_single hodd k, neg_zero]
  exact hsum Finset.univ

private theorem radical_odd_and_even_coords {N : ℕ} {a : Fin N → ZMod 3}
    (ha : ∀ k : Fin N, chainForm N a (Pi.single k 1) = 0) :
    (∀ i : Fin N, Odd (i : ℕ) → a i = 0) ∧
      (∀ (hN : 0 < N) (i : Fin N), Even (i : ℕ) → a i = a ⟨0, hN⟩) := by
  have hstep : ∀ k : Fin N,
      (if h : 0 < (k : ℕ) then a ⟨(k : ℕ) - 1, by omega⟩ else 0) =
        (if h : (k : ℕ) + 1 < N then a ⟨(k : ℕ) + 1, h⟩ else 0) := fun k ↦
    sub_eq_zero.mp (by rw [← chainForm_single_right]; exact ha k)
  constructor
  · suffices h : ∀ n : ℕ, ∀ hn : n < N, Odd n → a ⟨n, hn⟩ = 0 by
      intro i hi; exact h i.val i.isLt hi
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro hn ⟨r, hr⟩
      cases r with
      | zero =>
        have hk := hstep ⟨0, by omega⟩
        simp only [lt_self_iff_false, ↓reduceDIte, zero_add, show 1 < N by omega] at hk
        simpa [hr] using hk.symm
      | succ r' =>
        have hk := hstep ⟨2 * r' + 2, by omega⟩
        have hpos : 0 < 2 * r' + 2 := by omega
        have hlt : 2 * r' + 2 + 1 < N := by omega
        simp only [hpos, hlt, ↓reduceDIte] at hk
        have hprev : a ⟨2 * r' + 1, by omega⟩ = 0 :=
          ih (2 * r' + 1) (by omega) (by omega) ⟨r', by omega⟩
        have hidx1 : (⟨2 * r' + 2 - 1, by omega⟩ : Fin N) = ⟨2 * r' + 1, by omega⟩ :=
          Fin.ext rfl
        have hidx2 : (⟨2 * r' + 2 + 1, hlt⟩ : Fin N) = ⟨n, hn⟩ := Fin.ext (by dsimp; omega)
        rw [hidx1, hidx2, hprev] at hk
        exact hk.symm
  · intro hN
    suffices h : ∀ n : ℕ, ∀ hn : n < N, Even n → a ⟨n, hn⟩ = a ⟨0, hN⟩ by
      intro i hi; exact h i.val i.isLt hi
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro hn ⟨r, hr⟩
      cases r with
      | zero =>
        have h0 : (⟨n, hn⟩ : Fin N) = ⟨0, hN⟩ := Fin.ext (by dsimp; omega)
        rw [h0]
      | succ r' =>
        have hk := hstep ⟨2 * r' + 1, by omega⟩
        have hpos : 0 < 2 * r' + 1 := by omega
        have hlt : 2 * r' + 1 + 1 < N := by omega
        simp only [hpos, hlt, ↓reduceDIte] at hk
        have hprev : a ⟨2 * r', by omega⟩ = a ⟨0, hN⟩ :=
          ih (2 * r') (by omega) (by omega) ⟨r', by omega⟩
        have hidx1 : (⟨2 * r' + 1 - 1, by omega⟩ : Fin N) = ⟨2 * r', by omega⟩ :=
          Fin.ext rfl
        have hidx2 : (⟨2 * r' + 1 + 1, hlt⟩ : Fin N) = ⟨n, hn⟩ := Fin.ext (by dsimp; omega)
        rw [hidx1, hidx2, hprev] at hk
        exact hk.symm

private theorem chainForm_eq_zero_of_even {N : ℕ} (heven : Even N) {a : Fin N → ZMod 3}
    (ha : ∀ k : Fin N, chainForm N a (Pi.single k 1) = 0) : a = 0 := by
  obtain ⟨m, hm⟩ := heven
  cases m with
  | zero =>
    ext i
    exact absurd i.isLt (by omega)
  | succ m' =>
    have hN : 0 < N := by omega
    obtain ⟨hodd_coord, heven_coord⟩ := radical_odd_and_even_coords ha
    have hlast := ha ⟨2 * m' + 1, by omega⟩
    rw [chainForm_single_right] at hlast
    have hpos : 0 < 2 * m' + 1 := by omega
    have hnotlt : ¬ (2 * m' + 1 + 1 < N) := by omega
    simp only [hpos, hnotlt, ↓reduceDIte, sub_zero] at hlast
    have hzero0 : a ⟨0, hN⟩ = 0 := by
      have hev : Even (2 * m' + 1 - 1) := ⟨m', by omega⟩
      rw [heven_coord hN ⟨2 * m' + 1 - 1, by omega⟩ hev] at hlast
      exact hlast
    ext i
    rcases Nat.even_or_odd (i : ℕ) with hi | hi
    · rw [heven_coord hN i hi, hzero0]; rfl
    · rw [hodd_coord i hi]; rfl

private theorem chainForm_eq_zero_of_odd {N : ℕ} (hodd : Odd N) {a : Fin N → ZMod 3}
    (ha : ∀ k : Fin N, chainForm N a (Pi.single k 1) = 0) :
    ∃ c : ZMod 3, a = c • altVec N := by
  obtain ⟨m, hm⟩ := hodd
  have hN : 0 < N := by omega
  obtain ⟨hodd_coord, heven_coord⟩ := radical_odd_and_even_coords ha
  refine ⟨a ⟨0, hN⟩, ?_⟩
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, altVec]
  rcases Nat.even_or_odd (i : ℕ) with hi | hi
  · simp [hi, heven_coord hN i hi]
  · have hnot : ¬ Even (i : ℕ) := Nat.not_even_iff_odd.mpr hi
    simp [hnot, hodd_coord i hi]

private theorem repr_eq_zero_of_commute_weyl_of_chainForm_ne_zero {N : ℕ} {z : CubicTorus N}
    (hz : ∀ b : Multiplicative (Fin N → ZMod 3), z * weyl N b = weyl N b * z)
    {a : Multiplicative (Fin N → ZMod 3)} (hcoord : (cubicBasis N).repr z a ≠ 0) :
    ∀ k : Fin N, chainForm N a.toAdd (Pi.single k 1) = 0 := by
  intro k
  let b : Multiplicative (Fin N → ZMod 3) := Multiplicative.ofAdd (Pi.single k 1)
  have hcomm := hz b
  have hlhs :
      (cubicBasis N).repr (z * weyl N b) (a * b) =
        (cubicBasis N).repr z a * (cubicFactor N a b : ℂ) := by
    conv_lhs => rw [← (cubicBasis N).sum_repr z]
    rw [Finset.sum_mul, map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single a]
    · rw [cubicBasis_apply, smul_mul_assoc, weyl_mul, smul_smul, ← cubicBasis_apply, map_smul,
        Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
    · intro c _ hca
      have hne : c * b ≠ a * b := fun h ↦ hca (mul_right_cancel h)
      rw [cubicBasis_apply, smul_mul_assoc, weyl_mul, smul_smul, ← cubicBasis_apply, map_smul,
        Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_of_ne hne.symm, smul_zero]
    · intro ha'
      exact absurd (Finset.mem_univ a) ha'
  have hrhs :
      (cubicBasis N).repr (weyl N b * z) (a * b) =
        (cubicBasis N).repr z a * (cubicFactor N b a : ℂ) := by
    conv_lhs => rw [← (cubicBasis N).sum_repr z]
    rw [Finset.mul_sum, map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single a]
    · rw [cubicBasis_apply, mul_smul_comm, weyl_mul, smul_smul, mul_comm b a, ← cubicBasis_apply,
        map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
        mul_one]
    · intro c _ hca
      have hne : b * c ≠ a * b := by
        rw [mul_comm b c]
        exact fun h ↦ hca (mul_right_cancel h)
      rw [cubicBasis_apply, mul_smul_comm, weyl_mul, smul_smul, ← cubicBasis_apply, map_smul,
        Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_of_ne hne.symm, smul_zero]
    · intro ha'
      exact absurd (Finset.mem_univ a) ha'
  have heq : (cubicBasis N).repr z a * (cubicFactor N a b : ℂ) =
      (cubicBasis N).repr z a * (cubicFactor N b a : ℂ) := by
    rw [← hlhs, ← hrhs, hcomm]
  have hfac : cubicFactor N a b = cubicFactor N b a :=
    Units.ext (mul_left_cancel₀ hcoord heq)
  have h1 : cubeRootPow (chainForm N a.toAdd b.toAdd) = 1 := by
    rw [← cubicFactor_mul_swap_inv, hfac, mul_inv_cancel]
  simpa [b] using cubeRootPow_eq_one_iff.mp h1

private theorem finite_pow_eq_one {n : ℕ} (hn : n ≠ 0) :
    Finite {c : ℂ // c ^ n = 1} := by
  have : NeZero n := ⟨hn⟩
  refine Finite.of_injective
    (f := fun c : {c : ℂ // c ^ n = 1} ↦
      (⟨Units.mk0 c.1 fun h0 ↦ by simpa [h0, zero_pow hn] using c.2,
        (mem_rootsOfUnity' n _).mpr c.2⟩ : rootsOfUnity n ℂ)) ?_
  intro c₁ c₂ h
  apply Subtype.ext
  simpa using congrArg (fun u : rootsOfUnity n ℂ ↦ ((u : ℂˣ) : ℂ)) h

/-- **Finiteness of the cubic Gaussian braid group**: for every `N : ℕ`, the subgroup of
`(CubicTorus N)ˣ` generated by the Gaussian braid units `gaussianBraidUnit N j` is finite. -/
theorem finite_gaussianBraid_closure (N : ℕ) :
    Finite (Subgroup.closure (Set.range (gaussianBraidUnit N))) := by
  set G : Subgroup (CubicTorus N)ˣ := Subgroup.closure (Set.range (gaussianBraidUnit N))
  have hweyl_inj : Function.Injective (weyl N) := by
    intro x y hxy
    have := congrArg (fun t ↦ (cubicBasis N).repr t x) hxy
    rw [← cubicBasis_apply, ← cubicBasis_apply, Module.Basis.repr_self,
      Module.Basis.repr_self, Finsupp.single_eq_same] at this
    by_contra hne
    rw [Finsupp.single_eq_of_ne hne] at this
    exact one_ne_zero this
  -- Step 1: every `u ∈ G` permutes `{W(a)}` by conjugation.
  let P : Subgroup (CubicTorus N)ˣ :=
    { carrier := {u | ∀ a : Multiplicative (Fin N → ZMod 3),
        ∃ b : Multiplicative (Fin N → ZMod 3),
          (u : CubicTorus N) * weyl N a * ((u⁻¹ : (CubicTorus N)ˣ) : CubicTorus N) = weyl N b}
      one_mem' := fun a ↦ ⟨a, by simp⟩
      mul_mem' := fun {u v} hu hv a ↦ by
        obtain ⟨b, hb⟩ := hv a
        obtain ⟨c, hc⟩ := hu b
        refine ⟨c, ?_⟩
        calc
          ((u * v : (CubicTorus N)ˣ) : CubicTorus N) * weyl N a *
              (((u * v)⁻¹ : (CubicTorus N)ˣ) : CubicTorus N) =
              (u : CubicTorus N) *
                ((v : CubicTorus N) * weyl N a * ((v⁻¹ : (CubicTorus N)ˣ) : CubicTorus N)) *
                ((u⁻¹ : (CubicTorus N)ˣ) : CubicTorus N) := by
            simp only [Units.val_mul, mul_inv_rev, mul_assoc]
          _ = weyl N c := by rw [hb, hc]
      inv_mem' := fun {u} hu a ↦ by
        let σ : Multiplicative (Fin N → ZMod 3) → Multiplicative (Fin N → ZMod 3) :=
          fun x ↦ (hu x).choose
        have hσ : ∀ x, (u : CubicTorus N) * weyl N x * ((u⁻¹ : (CubicTorus N)ˣ) : CubicTorus N) =
            weyl N (σ x) := fun x ↦ (hu x).choose_spec
        have hσ_inj : Function.Injective σ := by
          intro x y hxy
          apply hweyl_inj
          have h1 : (u : CubicTorus N) * weyl N x * ((u⁻¹ : (CubicTorus N)ˣ) : CubicTorus N) =
              (u : CubicTorus N) * weyl N y * ((u⁻¹ : (CubicTorus N)ˣ) : CubicTorus N) := by
            rw [hσ x, hσ y, hxy]
          have h2 := congrArg (fun t ↦ ((u⁻¹ : (CubicTorus N)ˣ) : CubicTorus N) * t *
            (u : CubicTorus N)) h1
          simpa [mul_assoc, ← Units.val_mul] using h2
        obtain ⟨b, hb⟩ := Finite.injective_iff_surjective.mp hσ_inj a
        refine ⟨b, ?_⟩
        have hconj := congrArg (fun t ↦ ((u⁻¹ : (CubicTorus N)ˣ) : CubicTorus N) * t *
          (u : CubicTorus N)) (hσ b)
        rw [hb] at hconj
        simpa [mul_assoc, ← Units.val_mul] using hconj.symm }
  have hGP : G ≤ P := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩ a
    exact ⟨Multiplicative.ofAdd (a.toAdd + chainForm N a.toAdd (Pi.single j 1) • Pi.single j 1),
      gaussianBraidGenerator_conj_weyl N j a⟩
  -- Step 2: build the permutation homomorphism `φ : G →* Perm (Multiplicative (Fin N → ZMod 3))`.
  let act (g : G) (a : Multiplicative (Fin N → ZMod 3)) : Multiplicative (Fin N → ZMod 3) :=
    (hGP g.2 a).choose
  have hact : ∀ (g : G) (a : Multiplicative (Fin N → ZMod 3)),
      ((g : (CubicTorus N)ˣ) : CubicTorus N) * weyl N a *
          (((g : (CubicTorus N)ˣ)⁻¹ : (CubicTorus N)ˣ) : CubicTorus N) =
        weyl N (act g a) := fun g a ↦ (hGP g.2 a).choose_spec
  have hact_mul : ∀ (g₁ g₂ : G) (a : Multiplicative (Fin N → ZMod 3)),
      act (g₁ * g₂) a = act g₁ (act g₂ a) := by
    intro g₁ g₂ a
    apply hweyl_inj
    rw [← hact (g₁ * g₂) a, ← hact g₁ (act g₂ a), ← hact g₂ a]
    simp [Units.val_mul, mul_assoc]
  have hact_one : ∀ a : Multiplicative (Fin N → ZMod 3), act 1 a = a := by
    intro a
    apply hweyl_inj
    simpa using (hact 1 a).symm
  let φ : G →* Equiv.Perm (Multiplicative (Fin N → ZMod 3)) :=
    { toFun := fun g ↦
        { toFun := act g
          invFun := act g⁻¹
          left_inv := fun a ↦ by rw [← hact_mul, inv_mul_cancel, hact_one]
          right_inv := fun a ↦ by rw [← hact_mul, mul_inv_cancel, hact_one] }
      map_one' := Equiv.ext hact_one
      map_mul' := fun g₁ g₂ ↦ Equiv.ext (hact_mul g₁ g₂) }
  -- Since the codomain of `φ` is finite, it suffices to prove `Finite φ.ker`.
  rw [φ.finite_iff_finite_ker_range]
  refine ⟨?_, inferInstance⟩
  -- Every `g ∈ φ.ker` commutes with every `weyl N b`, and every representation of `G` has
  -- `det ^ 12 = 1`.
  have hker_comm : ∀ g : φ.ker, ∀ b : Multiplicative (Fin N → ZMod 3),
      ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N) * weyl N b =
        weyl N b * ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N) := by
    intro g b
    have hfix : act g.1 b = b := Equiv.congr_fun g.2 b
    have hconj := hact g.1 b
    rw [hfix] at hconj
    have hmul := congrArg (· * ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N)) hconj
    simpa [mul_assoc, ← Units.val_mul] using hmul
  have hdet12_of_rep : ∀ {W : Type} [AddCommGroup W] [Module ℂ W]
      (ρ : (CubicTorus N)ˣ →* Module.End ℂ W) (u : (CubicTorus N)ˣ), u ∈ G →
      (LinearMap.det (ρ u)) ^ 12 = 1 := by
    intro W _ _ ρ u hu
    let d : (CubicTorus N)ˣ →* ℂ := (powMonoidHom 12).comp (LinearMap.det.comp ρ)
    change d u = 1
    exact Subgroup.closure_induction
      (fun _ ⟨j, hj⟩ ↦ by
        subst hj
        change (LinearMap.det (ρ (gaussianBraidUnit N j))) ^ 12 = 1
        rw [← map_pow, ← map_pow, gaussianBraidUnit_pow_twelve, map_one, map_one])
      (map_one d)
      (fun x y _ _ hx hy ↦ by rw [map_mul, hx, hy, mul_one])
      (fun x _ hx ↦ by
        have hmul : d x * d x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        rw [hx, one_mul] at hmul
        exact hmul)
      hu
  -- Step 3: split by parity of `N` to bound central elements via determinants.
  rcases Nat.even_or_odd N with heven | hodd
  · -- Even `N`: every central element is a scalar `c • 1`, so `c ^ (3 ^ N * 12) = 1`.
    let L : (CubicTorus N)ˣ →* Module.End ℂ (CubicTorus N) :=
      { toFun := fun u ↦ LinearMap.mulLeft ℂ (u : CubicTorus N)
        map_one' := by ext x; simp
        map_mul' := fun u v ↦ by ext x; simp }
    have hscalar : ∀ g : φ.ker,
        ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N) =
          (cubicBasis N).repr ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N) 1 •
            (1 : CubicTorus N) := by
      intro g
      conv_lhs => rw [← (cubicBasis N).sum_repr ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N)]
      rw [Finset.sum_eq_single (1 : Multiplicative (Fin N → ZMod 3))]
      · simp
      · intro a _ ha1
        by_contra hne
        have hcoord : (cubicBasis N).repr ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N) a ≠ 0 := by
          intro h0
          exact hne (by simp [h0])
        have hrad := repr_eq_zero_of_commute_weyl_of_chainForm_ne_zero (hker_comm g) hcoord
        have ha0 : a.toAdd = 0 := chainForm_eq_zero_of_even heven hrad
        exact ha1 (Multiplicative.toAdd.injective (by simpa using ha0))
      · intro h1
        exact absurd (Finset.mem_univ _) h1
    have hn_ne : 3 ^ N * 12 ≠ 0 := by positivity
    have : Finite {c : ℂ // c ^ (3 ^ N * 12) = 1} := finite_pow_eq_one hn_ne
    refine Finite.of_injective
      (f := fun g : φ.ker ↦
        (⟨(cubicBasis N).repr ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N) 1, by
          have hL : L g.1.1 =
              ((cubicBasis N).repr ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N) 1) •
                (LinearMap.id : Module.End ℂ (CubicTorus N)) := by
            ext x
            change ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N) * x =
              ((cubicBasis N).repr ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N) 1) • x
            conv_lhs => rw [hscalar g]
            rw [smul_mul_assoc, one_mul]
          have hd := hdet12_of_rep L g.1.1 g.1.2
          rw [hL, LinearMap.det_smul, LinearMap.det_id, mul_one, finrank_cubicTorus,
            ← pow_mul] at hd
          exact hd⟩ : {c : ℂ // c ^ (3 ^ N * 12) = 1})) ?_
    intro g₁ g₂ h
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    have hc : (cubicBasis N).repr ((g₁.1.1 : (CubicTorus N)ˣ) : CubicTorus N) 1 =
        (cubicBasis N).repr ((g₂.1.1 : (CubicTorus N)ˣ) : CubicTorus N) 1 :=
      congrArg Subtype.val h
    rw [hscalar g₁, hscalar g₂, hc]
  · -- Odd `N`: decompose `CubicTorus N` by the three central idempotents of `w = W(altVec N)`.
    obtain ⟨m, hm⟩ := hodd
    have hN : 0 < N := by omega
    let w0 : Multiplicative (Fin N → ZMod 3) := Multiplicative.ofAdd (altVec N)
    let w : CubicTorus N := weyl N w0
    have hw_comm : ∀ x : CubicTorus N, w * x = x * w := by
      intro x
      rw [← (cubicBasis N).sum_repr x, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      rw [cubicBasis_apply, mul_smul_comm, smul_mul_assoc]
      congr 1
      rw [weyl_mul_comm, toAdd_ofAdd, chainForm_altVec_left ⟨m, hm⟩, cubeRootPow_zero,
        Units.val_one, one_smul]
    have hw3 : w ^ 3 = 1 := weyl_pow_three N w0
    have hw0_ne1 : w0 ≠ 1 := by
      intro h
      have h0 := congrFun (congrArg Multiplicative.toAdd h) ⟨0, hN⟩
      simp [w0, altVec] at h0
    have hw0_inv_ne1 : w0⁻¹ ≠ 1 := by
      intro h
      exact hw0_ne1 (inv_eq_one.mp h)
    let eIdem (r : ZMod 3) : CubicTorus N :=
      (3 : ℂ)⁻¹ • (1 + (cubeRootPow (-r) : ℂ) • w + (cubeRootPow r : ℂ) • w ^ 2)
    have he_comm : ∀ r x, eIdem r * x = x * eIdem r := by
      intro r x
      have hw2_comm : w ^ 2 * x = x * w ^ 2 := by
        rw [sq, mul_assoc, hw_comm x, ← mul_assoc, hw_comm x, mul_assoc, ← sq]
      simp only [eIdem, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, one_mul, mul_one,
        hw_comm x, hw2_comm]
    have hw_mul_e : ∀ r : ZMod 3, w * eIdem r = (cubeRootPow r : ℂ) • eIdem r := by
      intro r
      have h2r : r + r = -r := by revert r; decide
      have h1 : (cubeRootPow r : ℂ) * (cubeRootPow (-r) : ℂ) = 1 := by
        rw [cubeRootPow_neg]; exact (cubeRootPow r).mul_inv
      have h2 : (cubeRootPow r : ℂ) * (cubeRootPow r : ℂ) = (cubeRootPow (-r) : ℂ) := by
        rw [← Units.val_mul, ← cubeRootPow_add, h2r]
      have hw12 : w * w ^ 2 = 1 := by rw [← pow_succ', hw3]
      simp only [eIdem, mul_smul_comm]
      rw [smul_comm (cubeRootPow r : ℂ) (3 : ℂ)⁻¹]
      congr 1
      rw [mul_add, mul_add, mul_one, mul_smul_comm, mul_smul_comm, ← sq, hw12,
        smul_add, smul_add, smul_smul, smul_smul, h1, h2, one_smul]
      abel
    have hw2_mul_e : ∀ r : ZMod 3, w ^ 2 * eIdem r = (cubeRootPow (-r) : ℂ) • eIdem r := by
      intro r
      have h2r : r + r = -r := by revert r; decide
      rw [sq, mul_assoc, hw_mul_e, mul_smul_comm, hw_mul_e, smul_smul, ← Units.val_mul,
        ← cubeRootPow_add, h2r]
    have hsum_e : ∑ r : ZMod 3, eIdem r = 1 := by
      have hsum_zmod : ∀ f : ZMod 3 → CubicTorus N, ∑ r : ZMod 3, f r = f 0 + f 1 + f 2 := by
        intro f
        rw [show (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} by decide,
          Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
          add_assoc]
      rw [hsum_zmod]
      have hcyc : (1 : ℂ) + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2 = 0 :=
        one_add_cubeRootOfUnity_add_sq
      have hc0 : (cubeRootPow (0 : ZMod 3) : ℂ) = 1 := by simp
      have hcn0 : (cubeRootPow (-(0 : ZMod 3)) : ℂ) = 1 := by simp
      have hc1 : (cubeRootPow (1 : ZMod 3) : ℂ) = (cubeRootOfUnity : ℂ) := by simp
      have hcn1 : (cubeRootPow (-(1 : ZMod 3)) : ℂ) = (cubeRootOfUnity : ℂ) ^ 2 := by
        rw [cubeRootPow_neg, cubeRootPow_one, cubeRootOfUnity_inv_eq_sq, Units.val_pow_eq_pow_val]
      have hc2 : (cubeRootPow (2 : ZMod 3) : ℂ) = (cubeRootOfUnity : ℂ) ^ 2 := by
        rw [show (2 : ZMod 3) = -1 by decide, hcn1]
      have hcn2 : (cubeRootPow (-(2 : ZMod 3)) : ℂ) = (cubeRootOfUnity : ℂ) := by
        rw [show -(2 : ZMod 3) = 1 by decide, hc1]
      simp only [eIdem, hc0, hcn0, hc1, hcn1, hc2, hcn2, one_smul]
      rw [← smul_add, ← smul_add]
      have hsum_inner :
          (1 + w + w ^ 2) +
            (1 + ((cubeRootOfUnity : ℂ) ^ 2) • w + (cubeRootOfUnity : ℂ) • w ^ 2) +
            (1 + (cubeRootOfUnity : ℂ) • w + ((cubeRootOfUnity : ℂ) ^ 2) • w ^ 2) =
            (3 : ℂ) • (1 : CubicTorus N) +
              (1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2) • w +
              (1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2) • w ^ 2 := by
        module
      rw [hsum_inner, hcyc, zero_smul, zero_smul, add_zero, add_zero, smul_smul,
        inv_mul_cancel₀ (by norm_num), one_smul]
    have he_ne_zero : ∀ r : ZMod 3, eIdem r ≠ 0 := by
      intro r h0
      have hs := congrArg (cubicScalarCoefficient N) h0
      have hs_val : cubicScalarCoefficient N (eIdem r) = (3 : ℂ)⁻¹ := by
        simp only [eIdem, w, weyl_sq, map_smul, map_add, cubicScalarCoefficient_one,
          cubicScalarCoefficient_weyl, hw0_ne1, hw0_inv_ne1, ↓reduceIte, smul_eq_mul]
        ring
      rw [hs_val, map_zero] at hs
      exact inv_ne_zero (by norm_num : (3 : ℂ) ≠ 0) hs
    let V (r : ZMod 3) : Submodule ℂ (CubicTorus N) :=
      LinearMap.range (LinearMap.mulLeft ℂ (eIdem r))
    have hV_pos : ∀ r : ZMod 3, 0 < Module.finrank ℂ (V r) := by
      intro r
      have : Nontrivial (V r) :=
        ⟨⟨⟨eIdem r, ⟨1, by simp⟩⟩, 0, fun h ↦ he_ne_zero r (congrArg Subtype.val h)⟩⟩
      exact Module.finrank_pos
    have hV_inv : ∀ (r : ZMod 3) (x : CubicTorus N),
        ∀ v ∈ V r, LinearMap.mulLeft ℂ x v ∈ V r := by
      rintro r x _ ⟨y, rfl⟩
      exact ⟨x * y, by simp only [LinearMap.mulLeft_apply, ← mul_assoc, he_comm r x]⟩
    let Lr (r : ZMod 3) : (CubicTorus N)ˣ →* Module.End ℂ (V r) :=
      { toFun := fun u ↦ (LinearMap.mulLeft ℂ (u : CubicTorus N)).restrict (hV_inv r u)
        map_one' := by ext ⟨v, hv⟩; simp
        map_mul' := fun u₁ u₂ ↦ by ext ⟨v, hv⟩; simp }
    -- Every `g ∈ φ.ker` is a linear combination of `1, w, w ^ 2`.
    have hcentral_decomp : ∀ g : φ.ker,
        ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N) =
          (cubicBasis N).repr ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N) 1 • (1 : CubicTorus N) +
          (cubicBasis N).repr ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N) w0 • w +
          (cubicBasis N).repr ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N) w0⁻¹ • w ^ 2 := by
      intro g
      set z : CubicTorus N := ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N)
      have hw0_ne_inv : w0 ≠ w0⁻¹ := by
        intro h
        have h0 := congrFun (congrArg Multiplicative.toAdd h) ⟨0, hN⟩
        simp only [w0, toAdd_inv, toAdd_ofAdd, Pi.neg_apply, altVec, Even.zero, ↓reduceIte] at h0
        exact (by decide : (1 : ZMod 3) ≠ -1) h0
      conv_lhs => rw [← (cubicBasis N).sum_repr z]
      rw [← Finset.sum_subset (s₁ := {1, w0, w0⁻¹}) (Finset.subset_univ _)]
      · simp only [Finset.mem_insert, Finset.mem_singleton, hw0_ne1.symm, hw0_inv_ne1.symm,
          hw0_ne_inv, or_self, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton,
          cubicBasis_apply, weyl_one, ← weyl_sq, add_assoc]
        rfl
      · intro a _ ha
        by_contra hne
        have hcoord : (cubicBasis N).repr z a ≠ 0 := fun h0 ↦ hne (by simp [h0])
        have hrad := repr_eq_zero_of_commute_weyl_of_chainForm_ne_zero (hker_comm g) hcoord
        obtain ⟨c, hc⟩ := chainForm_eq_zero_of_odd ⟨m, hm⟩ hrad
        have hcval : c = 0 ∨ c = 1 ∨ c = 2 := by
          have : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
          exact this c
        apply ha
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hcval with rfl | rfl | rfl
        · left
          apply Multiplicative.toAdd.injective
          simpa using hc
        · right; left
          apply Multiplicative.toAdd.injective
          simpa [w0] using hc
        · right; right
          apply Multiplicative.toAdd.injective
          have h2neg : (2 : ZMod 3) • altVec N = -altVec N := by
            ext i
            simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
            have : (2 : ZMod 3) = -1 := by decide
            rw [this]
            ring
          simpa [w0, h2neg] using hc
    -- Define the three eigenvalues `λ_r(g)` of `g ∈ φ.ker` on `V_r`.
    let eig (g : φ.ker) (r : ZMod 3) : ℂ :=
      (cubicBasis N).repr ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N) 1 +
      (cubicBasis N).repr ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N) w0 * (cubeRootPow r : ℂ) +
      (cubicBasis N).repr ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N) w0⁻¹ * (cubeRootPow (-r) : ℂ)
    have hmul_e : ∀ (g : φ.ker) (r : ZMod 3),
        ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N) * eIdem r = eig g r • eIdem r := by
      intro g r
      rw [hcentral_decomp g, add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
        one_mul, hw_mul_e, hw2_mul_e, smul_smul, smul_smul]
      dsimp only [eig]
      module
    have hpow_eig : ∀ (g : φ.ker) (r : ZMod 3),
        eig g r ^ (Module.finrank ℂ (V r) * 12) = 1 := by
      intro g r
      have hLr : Lr r g.1.1 = eig g r • (LinearMap.id : Module.End ℂ (V r)) := by
        ext ⟨_, ⟨y, rfl⟩⟩
        change ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N) * (eIdem r * y) =
          eig g r • (eIdem r * y)
        rw [← mul_assoc, hmul_e g r, smul_mul_assoc]
      have hd := hdet12_of_rep (Lr r) g.1.1 g.1.2
      rw [hLr, LinearMap.det_smul, LinearMap.det_id, mul_one, ← pow_mul] at hd
      exact hd
    have : ∀ r : ZMod 3, Finite {c : ℂ // c ^ (Module.finrank ℂ (V r) * 12) = 1} := fun r ↦
      finite_pow_eq_one (Nat.mul_ne_zero (hV_pos r).ne' (by decide))
    refine Finite.of_injective
      (f := fun g : φ.ker ↦
        fun r : ZMod 3 ↦ (⟨eig g r, hpow_eig g r⟩ :
          {c : ℂ // c ^ (Module.finrank ℂ (V r) * 12) = 1})) ?_
    intro g₁ g₂ h
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    have hrecon : ∀ g : φ.ker,
        ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N) = ∑ r : ZMod 3, eig g r • eIdem r := by
      intro g
      calc
        ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N) =
            ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N) * ∑ r : ZMod 3, eIdem r := by
          rw [hsum_e, mul_one]
        _ = ∑ r : ZMod 3, ((g.1.1 : (CubicTorus N)ˣ) : CubicTorus N) * eIdem r :=
          Finset.mul_sum _ _ _
        _ = ∑ r : ZMod 3, eig g r • eIdem r :=
          Finset.sum_congr rfl fun r _ ↦ hmul_e g r
    rw [hrecon g₁, hrecon g₂]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have hr : eig g₁ r = eig g₂ r := congrArg Subtype.val (congrFun h r)
    rw [hr]

/-- Set-theoretic finiteness of the Gaussian braid subgroup in `(CubicTorus N)ˣ`. -/
theorem setFinite_gaussianBraid_closure (N : ℕ) :
    (Subgroup.closure (Set.range (gaussianBraidUnit N)) : Set (CubicTorus N)ˣ).Finite :=
  have := finite_gaussianBraid_closure N
  Set.toFinite _

/-- **Finiteness of the image of `gaussianBraidRep N`**: the Gaussian braid representation of
`BraidGroup (N + 1)` into `(cubicFixed N)ˣ` has finite image for every `N : ℕ`. -/
theorem finite_range_gaussianBraidRep (N : ℕ) :
    Finite (gaussianBraidRep N).range := by
  let ι : (cubicFixed N)ˣ →* (CubicTorus N)ˣ :=
    Units.map (cubicFixed N).toSubalgebra.val.toMonoidHom
  have hι_inj : Function.Injective ι := by
    intro u v huv
    exact Units.ext (Subtype.ext (congrArg Units.val huv))
  have hrange_le :
      (gaussianBraidRep N).range.map ι ≤ Subgroup.closure (Set.range (gaussianBraidUnit N)) := by
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    induction b using BraidGroup.sigma_induction_on with
    | one => simp
    | sigma j =>
      refine Subgroup.subset_closure ⟨j, ?_⟩
      rw [gaussianBraidRep_sigma]
      exact Units.ext rfl
    | mul b₁ b₂ ih₁ ih₂ =>
      simp only [map_mul]
      exact Subgroup.mul_mem _ ih₁ ih₂
    | inv b ih =>
      simp only [map_inv]
      exact Subgroup.inv_mem _ ih
  have := finite_gaussianBraid_closure N
  refine Finite.of_injective
    (f := fun x : (gaussianBraidRep N).range ↦
      (⟨ι x.1, hrange_le ⟨x.1, x.2, rfl⟩⟩ : Subgroup.closure (Set.range (gaussianBraidUnit N)))) ?_
  intro x y hxy
  exact Subtype.ext (hι_inj (congrArg Subtype.val hxy))

end TauCeti.TemperleyLieb
