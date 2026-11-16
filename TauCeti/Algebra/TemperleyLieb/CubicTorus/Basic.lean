/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Star
public import TauCeti.Algebra.TemperleyLieb.Star
-- Private: trace-rank formula and primitive roots of unity are used only in proofs.
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.LinearAlgebra.Trace.Idempotent

/-!
# The cubic quantum torus representation of the Temperley–Lieb algebra at `δ = √3`

At loop parameter `δ = √3 = 2 cos (π / 6)` (Jones index `δ² = 3`), the Temperley–Lieb algebra
`TemperleyLieb ℂ (√3 : ℂ) m` surjects onto the inversion-fixed subalgebra `cubicFixed (m - 1)`
of the `(m - 1)`-site cubic quantum torus `CubicTorus (m - 1)`.

Concretely, let `chainForm N` be the alternating `ZMod 3`-bilinear form on `Fin N → ZMod 3`
pairing adjacent sites,
`B(a, b) = ∑_{i + 1 = j} (a i * b j - a j * b i)`,
let `ω = cubeRootOfUnity = exp (2 * π * I / 3)`, and let `cubicFactor N` be the unitary factor set
`α(a, b) = ω ^ (2 * B(a, b))` on `Multiplicative (Fin N → ZMod 3)`. The cubic quantum torus
`CubicTorus N = twistedMonoidAlgebra ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)` has
complex dimension `3 ^ N` and canonical conjugate-linear `StarRing` structure
`star (weyl N a) = weyl N a⁻¹`.

The inversion automorphism `cubicInversion N : CubicTorus N →⋆ₐ[ℂ] CubicTorus N` sending
`weyl N a ↦ weyl N a⁻¹` is an involution whose fixed `⋆`-subalgebra `cubicFixed N` has
complex dimension `(3 ^ N + 1) / 2`. For each site `j : Fin N`, the site unitary
`U_j = cubicSite N j = weyl N (ofAdd (Pi.single j 1))` satisfies `U_j ^ 3 = 1`,
`star U_j = U_j ^ 2`, `U_j * U_{j + 1} = ω • (U_{j + 1} * U_j)`, and commutes at distance at
least two. The projections

  `cubicProjection N j = 3⁻¹ • (1 + U_j + U_j ^ 2)`

lie in `cubicFixed N`, are self-adjoint idempotents, satisfy `p_i * p_j * p_i = 3⁻¹ • p_i` when
`i` and `j` are adjacent, and commute when `|i - j| ≥ 2`. Rescaling by `√3` therefore yields a
`⋆`-algebra homomorphism

  `cubicFixedHom m : TemperleyLieb ℂ (√3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1)`

sending `e (√3 : ℂ) j` to `(√3 : ℂ) • p_j`. Surjectivity (`cubicFixedHom_surjective`) is
proved algebraically by showing that the symmetrized Weyl elements `weyl a + weyl a⁻¹` span
`cubicFixed` and are generated inductively from the single-site elements
`U_j + U_j ^ 2 = √3 • F_m (e j) - 1`.

Tower inclusions, the Markov trace identity, positivity at `δ = √3`, the Jones quotient
equivalence, and vanishing of the five-strand Jones–Wenzl projection are established in
`TauCeti.Algebra.TemperleyLieb.CubicTorus.Quotient`.

## Main definitions

* `TauCeti.TemperleyLieb.chainForm`: the alternating adjacent-site bilinear form on
  `Fin N → ZMod 3`.
* `TauCeti.TemperleyLieb.cubeRootOfUnity` and `TauCeti.TemperleyLieb.cubeRootPow`: the primitive
  cube root of unity `ω = exp (2 * π * I / 3)` and its `ZMod 3`-indexed powers.
* `TauCeti.TemperleyLieb.cubicFactor`, `TauCeti.TemperleyLieb.CubicTorus`, and
  `TauCeti.TemperleyLieb.weyl`: the unitary factor set, twisted group `⋆`-algebra `G_N`, and Weyl
  basis elements `W(a)`.
* `TauCeti.TemperleyLieb.cubicInversion` and `TauCeti.TemperleyLieb.cubicFixed`: the inversion
  `⋆`-automorphism `W(a) ↦ W(-a)` and its fixed `⋆`-subalgebra `C_N`.
* `TauCeti.TemperleyLieb.cubicSite` and `TauCeti.TemperleyLieb.cubicProjection`: the site unitaries
  `U_j` and self-adjoint projections `p_j = 3⁻¹ • (1 + U_j + U_j ^ 2)`.
* `TauCeti.TemperleyLieb.cubicFixedHom`: the `⋆`-algebra homomorphism
  `TemperleyLieb ℂ (√3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1)`.

## Main results

* `TauCeti.TemperleyLieb.finrank_cubicTorus` and `TauCeti.TemperleyLieb.finrank_cubicFixed`:
  `finrank ℂ (CubicTorus N) = 3 ^ N` and `finrank ℂ (cubicFixed N) = (3 ^ N + 1) / 2`.
* `TauCeti.TemperleyLieb.cubicProjection_mul_self`,
  `TauCeti.TemperleyLieb.cubicProjection_mul_cubicProjection_mul_cubicProjection`, and
  `TauCeti.TemperleyLieb.commute_cubicProjection`: the Jones projection relations at index `3`.
* `TauCeti.TemperleyLieb.cubicFixedHom_surjective`: surjectivity of `cubicFixedHom m` for every
  `m : ℕ`.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111 (p. 107, cubic quantum torus model at `t = exp (πi / 3)`).
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
* C. Galindo and E. C. Rowell, *Braid representations from unitary braided vector spaces*,
  J. Math. Phys. 55 (2014), 061702, Section 3.
-/

public section

open scoped ComplexConjugate

namespace TauCeti.TemperleyLieb

/-- Registers `IsSelfAdjoint (Real.sqrt 3 : ℂ)` as a `Fact` so that
`TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m` carries the analytic adjoint `StarRing` and
`StarModule ℂ` instances automatically. -/
instance : Fact (IsSelfAdjoint (Real.sqrt 3 : ℂ)) :=
  ⟨Complex.conj_ofReal _⟩

private theorem sqrt_three_coe_mul_self :
    (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
  exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)

/-! ### Alternating chain form on `(ZMod 3)^N` -/

/-- The alternating `ZMod 3`-bilinear form on `Fin N → ZMod 3` pairing adjacent sites:
`B(a, b) = ∑_{i + 1 = j} (a i * b j - a j * b i)`. -/
def chainForm (N : ℕ) : LinearMap.BilinForm (ZMod 3) (Fin N → ZMod 3) :=
  LinearMap.mk₂ (ZMod 3)
    (fun a b ↦ ∑ i : Fin N, ∑ j : Fin N,
      if (i : ℕ) + 1 = (j : ℕ) then a i * b j - a j * b i else 0)
    (fun a₁ a₂ b ↦ by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [Pi.add_apply]
      split_ifs <;> ring)
    (fun c a b ↦ by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      split_ifs <;> ring)
    (fun a b₁ b₂ ↦ by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [Pi.add_apply]
      split_ifs <;> ring)
    (fun c a b ↦ by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      split_ifs <;> ring)

/-- Explicit formula for `chainForm N`. -/
theorem chainForm_apply (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N a b = ∑ i : Fin N, ∑ j : Fin N,
      if (i : ℕ) + 1 = (j : ℕ) then a i * b j - a j * b i else 0 :=
  (rfl)

/-- `chainForm N` is alternating: `chainForm N a a = 0`. -/
@[simp]
theorem chainForm_self (N : ℕ) (a : Fin N → ZMod 3) : chainForm N a a = 0 := by
  rw [chainForm_apply]
  refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ ?_
  split_ifs <;> ring

/-- `chainForm N` is skew-symmetric: `chainForm N a b = -chainForm N b a`. -/
theorem chainForm_swap (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm N a b = -chainForm N b a := by
  rw [chainForm_apply, chainForm_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> ring

/-- Evaluation of `chainForm N` on a pair of standard basis vectors. -/
theorem chainForm_single_single (N : ℕ) (i j : Fin N) :
    chainForm N (Pi.single i 1) (Pi.single j 1) =
      if (i : ℕ) + 1 = (j : ℕ) then 1
      else if (j : ℕ) + 1 = (i : ℕ) then -1
      else 0 := by
  rw [chainForm_apply]
  have hsum (a b : Fin N) :
      (∑ r : Fin N, ∑ s : Fin N,
        if (r : ℕ) + 1 = (s : ℕ) then
          (Pi.single a (1 : ZMod 3) : Fin N → ZMod 3) r *
            (Pi.single b (1 : ZMod 3) : Fin N → ZMod 3) s
        else 0) = if (a : ℕ) + 1 = (b : ℕ) then 1 else 0 := by
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · simp
      · intro s _ hs
        simp [Pi.single_eq_of_ne hs]
      · exact fun hb ↦ absurd (Finset.mem_univ b) hb
    · intro r _ hr
      refine Finset.sum_eq_zero fun s _ ↦ ?_
      simp [Pi.single_eq_of_ne hr]
    · exact fun ha ↦ absurd (Finset.mem_univ a) ha
  have hsplit :
      (∑ r : Fin N, ∑ s : Fin N,
        if (r : ℕ) + 1 = (s : ℕ) then
          (Pi.single i (1 : ZMod 3) : Fin N → ZMod 3) r *
            (Pi.single j (1 : ZMod 3) : Fin N → ZMod 3) s -
          (Pi.single i (1 : ZMod 3) : Fin N → ZMod 3) s *
            (Pi.single j (1 : ZMod 3) : Fin N → ZMod 3) r
        else 0) =
      (if (i : ℕ) + 1 = (j : ℕ) then (1 : ZMod 3) else 0) -
      (if (j : ℕ) + 1 = (i : ℕ) then (1 : ZMod 3) else 0) := by
    rw [← hsum i j, ← hsum j i, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    split_ifs <;> ring
  rw [hsplit]
  by_cases hij : (i : ℕ) + 1 = (j : ℕ)
  · have hji : ¬ ((j : ℕ) + 1 = (i : ℕ)) := by omega
    simp [hij, hji]
  · by_cases hji : (j : ℕ) + 1 = (i : ℕ) <;> simp [hij, hji]

/-- If `a` is supported strictly below index `j + 1`, then
`chainForm N a (Pi.single ⟨j + 1, _⟩ 1)` equals `a ⟨j, _⟩`. -/
private theorem chainForm_single_succ_of_support {N j : ℕ} (hj : j + 1 < N)
    {a : Fin N → ZMod 3} (ha : ∀ r : Fin N, j + 1 ≤ (r : ℕ) → a r = 0) :
    chainForm N a (Pi.single ⟨j + 1, hj⟩ 1) = a ⟨j, by omega⟩ := by
  have hexp : a = ∑ r : Fin N, a r • (Pi.single r 1 : Fin N → ZMod 3) := by
    ext s
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hexp]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single ⟨j, by omega⟩]
  · rw [chainForm_single_single]
    simp
  · intro r _ hr
    rw [chainForm_single_single]
    by_cases h1 : (r : ℕ) = j
    · exact absurd (Fin.ext h1) hr
    · by_cases h2 : j + 1 + 1 = (r : ℕ)
      · rw [ha r (by omega), zero_mul]
      · simp [h1, h2]
  · exact fun hmem ↦ absurd (Finset.mem_univ _) hmem

/-! ### Primitive cube root of unity and unitary factor set -/

/-- The primitive cube root of unity `ω = exp (2 * π * I / 3)` as a unit of `ℂ`. -/
noncomputable def cubeRootOfUnity : ℂˣ :=
  Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / 3)) (Complex.exp_ne_zero _)

private theorem isPrimitiveRoot_cubeRootOfUnity :
    IsPrimitiveRoot (cubeRootOfUnity : ℂ) 3 := by
  simpa [cubeRootOfUnity] using Complex.isPrimitiveRoot_exp 3 (by norm_num)

/-- `ω ^ 3 = 1` in `ℂˣ`. -/
@[simp]
theorem cubeRootOfUnity_pow_three : cubeRootOfUnity ^ 3 = 1 :=
  Units.ext (by simpa using isPrimitiveRoot_cubeRootOfUnity.pow_eq_one)

/-- `ω ≠ 1` in `ℂ`. -/
theorem cubeRootOfUnity_ne_one : (cubeRootOfUnity : ℂ) ≠ 1 :=
  isPrimitiveRoot_cubeRootOfUnity.ne_one (by decide)

/-- The cyclotomic identity `1 + ω + ω ^ 2 = 0`. -/
theorem one_add_cubeRootOfUnity_add_sq :
    1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2 = 0 := by
  have h : ((cubeRootOfUnity : ℂ) - 1) *
      (1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2) = 0 := by
    have h3 : (cubeRootOfUnity : ℂ) ^ 3 = 1 := isPrimitiveRoot_cubeRootOfUnity.pow_eq_one
    linear_combination h3
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr cubeRootOfUnity_ne_one)

/-- Complex conjugation sends `ω` to `ω⁻¹`. -/
@[simp]
theorem star_cubeRootOfUnity :
    star (cubeRootOfUnity : ℂ) = ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ) := by
  have hmul : star (cubeRootOfUnity : ℂ) * (cubeRootOfUnity : ℂ) = 1 := by
    change starRingEnd ℂ (Complex.exp (2 * Real.pi * Complex.I / 3)) *
      Complex.exp (2 * Real.pi * Complex.I / 3) = 1
    rw [← Complex.exp_conj, ← Complex.exp_add]
    have hzero :
        starRingEnd ℂ (2 * (Real.pi : ℂ) * Complex.I / 3) +
          2 * (Real.pi : ℂ) * Complex.I / 3 = 0 := by
      simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [hzero, Complex.exp_zero]
  exact mul_right_cancel₀ (Units.ne_zero cubeRootOfUnity) (by rw [hmul, Units.inv_mul])

/-- `ω ^ x` for an exponent `x : ZMod 3`, additive in `x` since `ω ^ 3 = 1`. -/
noncomputable def cubeRootPow (x : ZMod 3) : ℂˣ :=
  cubeRootOfUnity ^ x.val

/-- `cubeRootPow 0 = 1`. -/
@[simp]
theorem cubeRootPow_zero : cubeRootPow 0 = 1 := by
  simp [cubeRootPow]

/-- `cubeRootPow 1 = cubeRootOfUnity`. -/
@[simp]
theorem cubeRootPow_one : cubeRootPow 1 = cubeRootOfUnity := by
  simp [cubeRootPow, ZMod.val_one]

/-- `cubeRootPow` converts addition in `ZMod 3` to multiplication in `ℂˣ`. -/
theorem cubeRootPow_add (x y : ZMod 3) :
    cubeRootPow (x + y) = cubeRootPow x * cubeRootPow y := by
  simp only [cubeRootPow, ZMod.val_add]
  rw [← pow_add, ← pow_eq_pow_mod _ cubeRootOfUnity_pow_three]

/-- `cubeRootPow (-x) = (cubeRootPow x)⁻¹`. -/
@[simp]
theorem cubeRootPow_neg (x : ZMod 3) : cubeRootPow (-x) = (cubeRootPow x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← cubeRootPow_add, neg_add_cancel, cubeRootPow_zero]

/-- Complex conjugation sends `cubeRootPow x` to its unit inverse. -/
@[simp]
theorem star_cubeRootPow (x : ZMod 3) :
    star (cubeRootPow x : ℂ) = (((cubeRootPow x)⁻¹ : ℂˣ) : ℂ) := by
  simp only [cubeRootPow, Units.val_pow_eq_pow_val, star_pow, star_cubeRootOfUnity,
    inv_pow, Units.val_inv_eq_inv_val]

/-- The unitary factor set `α(a, b) = ω ^ (2 * B(a, b))` of the `N`-site cubic quantum torus. -/
noncomputable def cubicFactor (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) : ℂˣ :=
  cubeRootPow (2 * chainForm N a.toAdd b.toAdd)

/-- Explicit formula for `cubicFactor N`. -/
theorem cubicFactor_apply (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a b = cubeRootPow (2 * chainForm N a.toAdd b.toAdd) :=
  (rfl)

/-- `cubicFactor N` is a normalized `2`-cocycle (factor set). -/
instance cubicFactor_isFactorSet (N : ℕ) : IsFactorSet (cubicFactor N) where
  cocycle g h j := by
    simp only [cubicFactor, toAdd_mul, ← cubeRootPow_add]
    congr 1
    simp only [map_add, LinearMap.add_apply]
    ring
  one_left g := by
    simp [cubicFactor]

/-- `cubicFactor N` takes values in unit-modulus roots of unity. -/
instance cubicFactor_isUnitaryFactorSet (N : ℕ) : IsUnitaryFactorSet (cubicFactor N) where
  star_val _ _ := star_cubeRootPow _

/-- `cubicFactor N` is trivial on every inverse pair `(a, a⁻¹)`. -/
@[simp]
theorem cubicFactor_inv_right (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a a⁻¹ = 1 := by
  simp [cubicFactor, toAdd_inv]

/-- `cubicFactor N` is invariant under simultaneous inversion of both arguments. -/
theorem cubicFactor_inv_inv (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a⁻¹ b⁻¹ = cubicFactor N a b := by
  simp [cubicFactor, toAdd_inv]

/-- Swapping arguments inverts `cubicFactor N`. -/
theorem cubicFactor_swap (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N b a = (cubicFactor N a b)⁻¹ := by
  rw [cubicFactor, cubicFactor, ← cubeRootPow_neg]
  congr 1
  rw [chainForm_swap]
  ring

/-- Negating the right argument inverts `cubicFactor N`. -/
theorem cubicFactor_inv_right_eq (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a b⁻¹ = (cubicFactor N a b)⁻¹ := by
  rw [cubicFactor, cubicFactor, toAdd_inv, map_neg, mul_neg, cubeRootPow_neg]

/-- Negating the left argument inverts `cubicFactor N`. -/
theorem cubicFactor_inv_left_eq (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor N a⁻¹ b = (cubicFactor N a b)⁻¹ := by
  rw [cubicFactor, cubicFactor, toAdd_inv, map_neg, LinearMap.neg_apply, mul_neg, cubeRootPow_neg]

/-! ### The cubic quantum torus `CubicTorus N` and inversion-fixed subalgebra `cubicFixed N` -/

/-- **The `N`-site cubic quantum torus** `G_N`: the twisted group `⋆`-algebra of
`Multiplicative (Fin N → ZMod 3)` for the unitary factor set `cubicFactor N`. -/
noncomputable abbrev CubicTorus (N : ℕ) :=
  twistedMonoidAlgebra ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)

/-- The Weyl basis element `W(a) = TwistedMonoidAlgebra.of a` of `CubicTorus N`. -/
noncomputable def weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) : CubicTorus N :=
  TwistedMonoidAlgebra.of a

/-- Unfolding `weyl N a` as `TwistedMonoidAlgebra.of a`. -/
theorem weyl_def (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weyl N a = TwistedMonoidAlgebra.of a :=
  (rfl)

/-- The identity Weyl basis element is `1`. -/
@[simp]
theorem weyl_one (N : ℕ) : weyl N 1 = 1 :=
  TwistedMonoidAlgebra.of_one

/-- Multiplication table of Weyl basis elements: `W(a) * W(b) = α(a, b) • W(a * b)`. -/
theorem weyl_mul_weyl (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    weyl N a * weyl N b = (cubicFactor N a b : ℂ) • weyl N (a * b) :=
  TwistedMonoidAlgebra.of_mul_of a b

/-- The canonical adjoint inverts Weyl basis elements: `star (weyl N a) = weyl N a⁻¹`. -/
@[simp]
theorem star_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    star (weyl N a) = weyl N a⁻¹ :=
  TwistedMonoidAlgebra.star_of_eq_of_inv (cubicFactor_inv_right N a)

/-- The `N`-site cubic quantum torus has complex dimension `3 ^ N`. -/
@[simp]
theorem finrank_cubicTorus (N : ℕ) : Module.finrank ℂ (CubicTorus N) = 3 ^ N := by
  rw [TwistedMonoidAlgebra.finrank_eq_natCard, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- The inversion `⋆`-automorphism `θ_N : W(a) ↦ W(a⁻¹)` of `CubicTorus N`. -/
noncomputable def cubicInversion (N : ℕ) : CubicTorus N →⋆ₐ[ℂ] CubicTorus N :=
  TwistedMonoidAlgebra.starMap
    (MulEquiv.inv (Multiplicative (Fin N → ZMod 3))).toMonoidHom
    (fun a b ↦ (cubicFactor_inv_inv N a b).symm)

/-- `cubicInversion N` acts on Weyl basis elements by inverting the group index. -/
@[simp]
theorem cubicInversion_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicInversion N (weyl N a) = weyl N a⁻¹ :=
  TwistedMonoidAlgebra.starMap_of _ _ a

/-- `cubicInversion N` is an involution. -/
@[simp]
theorem cubicInversion_cubicInversion (N : ℕ) (x : CubicTorus N) :
    cubicInversion N (cubicInversion N x) = x := by
  have h : (cubicInversion N).toAlgHom.comp (cubicInversion N).toAlgHom =
      AlgHom.id ℂ (CubicTorus N) := by
    refine TwistedMonoidAlgebra.algHom_ext fun a ↦ ?_
    change cubicInversion N (cubicInversion N (weyl N a)) = weyl N a
    simp
  exact AlgHom.congr_fun h x

/-- **The inversion-fixed `⋆`-subalgebra**
`C_N = {x ∈ CubicTorus N : cubicInversion N x = x}`. -/
noncomputable def cubicFixed (N : ℕ) : StarSubalgebra ℂ (CubicTorus N) :=
  StarAlgHom.equalizer (cubicInversion N) (StarAlgHom.id ℂ (CubicTorus N))

/-- Direct `Ring` instance on `cubicFixed N`, agreeing definitionally with the inherited
`Semiring` structure while avoiding reducible-unification failures through the nested `Subalgebra`
carrier of `CubicTorus N`. -/
noncomputable instance instRingCubicFixed (N : ℕ) : Ring (cubicFixed N) :=
  letI : SubringClass (StarSubalgebra ℂ (CubicTorus N)) (CubicTorus N) :=
    @StarSubalgebra.subringClass ℂ (CubicTorus N) _ _ _ _ _ _
  SubringClass.toRing (cubicFixed N)

/-- Membership in `cubicFixed N` is invariance under `cubicInversion N`. -/
@[simp]
theorem mem_cubicFixed_iff {N : ℕ} {x : CubicTorus N} :
    x ∈ cubicFixed N ↔ cubicInversion N x = x :=
  StarAlgHom.mem_equalizer (cubicInversion N) (StarAlgHom.id ℂ (CubicTorus N)) x

/-- The inversion-fixed subalgebra `cubicFixed N` has complex dimension `(3 ^ N + 1) / 2`. -/
@[simp]
theorem finrank_cubicFixed (N : ℕ) : Module.finrank ℂ (cubicFixed N) = (3 ^ N + 1) / 2 := by
  let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  let θ : Module.End ℂ (CubicTorus N) := (cubicInversion N).toAlgHom.toLinearMap
  have hsq : (1 + θ) * (1 + θ) = (2 : ℂ) • (1 + θ) := by
    ext x
    simp only [mul_apply_eq_comp, LinearMap.add_apply, one_apply_eq_self,
      LinearMap.smul_apply, map_add, θ, AlgHom.toLinearMap_apply,
      StarAlgHom.coe_toAlgHom, cubicInversion_cubicInversion]
    rw [show (2 : ℂ) = 1 + 1 by norm_num]
    simp only [add_smul, one_smul]
    rw [add_comm (cubicInversion N x) x]
  have hrange : LinearMap.range (1 + θ) = (cubicFixed N).toSubmodule := by
    ext x
    simp only [LinearMap.mem_range, LinearMap.add_apply, one_apply_eq_self, θ,
      AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom, Subalgebra.mem_toSubmodule,
      StarSubalgebra.mem_toSubalgebra, mem_cubicFixed_iff]
    constructor
    · rintro ⟨y, rfl⟩
      simp [add_comm]
    · intro hx
      refine ⟨(2 : ℂ)⁻¹ • x, ?_⟩
      rw [map_smul, hx, ← add_smul]
      norm_num
  have htrace : LinearMap.trace ℂ (CubicTorus N) θ = 1 := by
    rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
    have hdiag (a : Multiplicative (Fin N → ZMod 3)) :
        LinearMap.toMatrix b b θ a a = if a = 1 then (1 : ℂ) else 0 := by
      rw [LinearMap.toMatrix_apply, TwistedMonoidAlgebra.basis_apply]
      change b.repr (cubicInversion N (weyl N a)) a = if a = 1 then (1 : ℂ) else 0
      rw [cubicInversion_weyl,
        show weyl N a⁻¹ = b a⁻¹ from (TwistedMonoidAlgebra.basis_apply ..).symm,
        Module.Basis.repr_self]
      have hinv : a⁻¹ = a ↔ a = 1 := by
        constructor
        · intro h
          apply Multiplicative.toAdd.injective
          ext i
          have hi : -a.toAdd i = a.toAdd i := by
            have := congrFun (congrArg Multiplicative.toAdd h) i
            simpa [toAdd_inv] using this
          simpa using (by decide : ∀ z : ZMod 3, -z = z → z = 0) (a.toAdd i) hi
        · rintro rfl
          simp
      by_cases ha : a = 1
      · simp [ha]
      · have hne : a⁻¹ ≠ a := fun h ↦ ha (hinv.mp h)
        simp [ha, Finsupp.single_eq_of_ne hne.symm]
    simp [Matrix.diag_apply, hdiag]
  have hnat : 3 ^ N + 1 = 2 * Module.finrank ℂ (cubicFixed N) := by
    have h := TauCeti.LinearMap.trace_eq_mul_finrank_range (K := ℂ) (M := CubicTorus N) hsq
    rw [map_add, LinearMap.trace_one ℂ (CubicTorus N), finrank_cubicTorus, htrace, hrange] at h
    have hfin :
        Module.finrank ℂ (Subalgebra.toSubmodule (cubicFixed N).toSubalgebra) =
          Module.finrank ℂ (cubicFixed N) := rfl
    rw [hfin] at h
    exact_mod_cast h
  omega

/-! ### Site unitaries and Jones projections at index `3` -/

/-- The `j`-th site unitary `U_j = weyl N (ofAdd (Pi.single j 1))` in `CubicTorus N`. -/
noncomputable def cubicSite (N : ℕ) (j : Fin N) : CubicTorus N :=
  weyl N (Multiplicative.ofAdd (Pi.single j 1))

/-- Unfolding `cubicSite N j`. -/
theorem cubicSite_def (N : ℕ) (j : Fin N) :
    cubicSite N j = weyl N (Multiplicative.ofAdd (Pi.single j 1)) :=
  (rfl)

/-- The square of `cubicSite N j` is the Weyl element `W(2 e_j)`. -/
theorem cubicSite_sq (N : ℕ) (j : Fin N) :
    cubicSite N j ^ 2 = weyl N (Multiplicative.ofAdd (Pi.single j 2)) := by
  rw [pow_two, cubicSite_def, weyl_mul_weyl, cubicFactor_apply, toAdd_ofAdd, chainForm_self,
    mul_zero, cubeRootPow_zero, Units.val_one, one_smul, ← ofAdd_add]
  congr 2
  ext k
  simp only [Pi.add_apply, Pi.single_apply]
  split_ifs <;> decide

/-- Every site unitary has order dividing `3`: `U_j ^ 3 = 1`. -/
@[simp]
theorem cubicSite_pow_three (N : ℕ) (j : Fin N) : cubicSite N j ^ 3 = 1 := by
  let eⱼ : Fin N → ZMod 3 := Pi.single j 1
  have h3 : eⱼ + eⱼ + eⱼ = 0 := by
    ext k
    simp only [eⱼ, Pi.add_apply, Pi.zero_apply, Pi.single_apply]
    split_ifs <;> decide
  have hpow :
      Multiplicative.ofAdd eⱼ * Multiplicative.ofAdd eⱼ * Multiplicative.ofAdd eⱼ = 1 := by
    rw [← ofAdd_add, ← ofAdd_add, h3, ofAdd_zero]
  have hsq :
      cubicSite N j * cubicSite N j =
        weyl N (Multiplicative.ofAdd eⱼ * Multiplicative.ofAdd eⱼ) := by
    rw [cubicSite, weyl_mul_weyl, cubicFactor, toAdd_ofAdd, chainForm_self, mul_zero,
      cubeRootPow_zero, Units.val_one, one_smul]
  calc
    cubicSite N j ^ 3 = (cubicSite N j * cubicSite N j) * cubicSite N j := by
      rw [pow_succ, pow_two]
    _ = weyl N (Multiplicative.ofAdd eⱼ * Multiplicative.ofAdd eⱼ) *
          weyl N (Multiplicative.ofAdd eⱼ) := by rw [hsq, cubicSite]
    _ = (cubicFactor N
          (Multiplicative.ofAdd eⱼ * Multiplicative.ofAdd eⱼ)
          (Multiplicative.ofAdd eⱼ) : ℂ) • weyl N 1 := by
      rw [weyl_mul_weyl, hpow]
    _ = 1 := by
      simp [cubicFactor, toAdd_mul]

/-- `star (cubicSite N j) = cubicSite N j ^ 2`. -/
@[simp]
theorem star_cubicSite (N : ℕ) (j : Fin N) :
    star (cubicSite N j) = cubicSite N j ^ 2 := by
  let eⱼ : Fin N → ZMod 3 := Pi.single j 1
  have hneg : -eⱼ = eⱼ + eⱼ := by
    ext k
    simp only [eⱼ, Pi.neg_apply, Pi.add_apply, Pi.single_apply]
    split_ifs <;> decide
  have hsq : cubicSite N j ^ 2 = weyl N (Multiplicative.ofAdd (eⱼ + eⱼ)) := by
    rw [pow_two, cubicSite, weyl_mul_weyl, cubicFactor, toAdd_ofAdd, chainForm_self, mul_zero,
      cubeRootPow_zero, Units.val_one, one_smul, ← ofAdd_add]
  rw [hsq, cubicSite, star_weyl, ← ofAdd_neg, hneg]

/-- `cubicInversion N (cubicSite N j) = cubicSite N j ^ 2`. -/
@[simp]
theorem cubicInversion_cubicSite (N : ℕ) (j : Fin N) :
    cubicInversion N (cubicSite N j) = cubicSite N j ^ 2 := by
  rw [← star_cubicSite, cubicSite, cubicInversion_weyl, star_weyl]

/-- Adjacent site unitaries `q`-commute: if `i + 1 = j`, then `U_i * U_j = ω • (U_j * U_i)`. -/
theorem cubicSite_mul_cubicSite_of_succ {N : ℕ} {i j : Fin N} (h : (i : ℕ) + 1 = (j : ℕ)) :
    cubicSite N i * cubicSite N j =
      (cubeRootOfUnity : ℂ) • (cubicSite N j * cubicSite N i) := by
  rw [cubicSite, cubicSite, weyl_mul_weyl, weyl_mul_weyl, mul_comm (Multiplicative.ofAdd _),
    smul_smul]
  have hji : ¬ ((j : ℕ) + 1 = (i : ℕ)) := by omega
  have hij : chainForm N (Pi.single i 1) (Pi.single j 1) = 1 := by
    simp [chainForm_single_single, h]
  have hji' : chainForm N (Pi.single j 1) (Pi.single i 1) = -1 := by
    simp [chainForm_single_single, hji, h]
  have hcoef :
      (cubicFactor N (Multiplicative.ofAdd (Pi.single i 1))
          (Multiplicative.ofAdd (Pi.single j 1)) : ℂ) =
        (cubeRootOfUnity : ℂ) *
          (cubicFactor N (Multiplicative.ofAdd (Pi.single j 1))
            (Multiplicative.ofAdd (Pi.single i 1)) : ℂ) := by
    rw [cubicFactor, cubicFactor, toAdd_ofAdd, toAdd_ofAdd, hij, hji', ← Units.val_mul,
      ← cubeRootPow_one, ← cubeRootPow_add]
    have hexp : (2 : ZMod 3) * 1 = 1 + 2 * (-1) := by decide
    rw [hexp]
  rw [hcoef]

/-- Adjacent site unitaries in reverse order `q`-commute with `ω⁻¹`:
if `j + 1 = i`, then `U_i * U_j = ω⁻¹ • (U_j * U_i)`. -/
theorem cubicSite_mul_cubicSite_of_pred {N : ℕ} {i j : Fin N} (h : (j : ℕ) + 1 = (i : ℕ)) :
    cubicSite N i * cubicSite N j =
      ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ) • (cubicSite N j * cubicSite N i) := by
  rw [cubicSite_mul_cubicSite_of_succ h, smul_smul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_smul]

/-- Site unitaries at distance at least two commute. -/
theorem commute_cubicSite {N : ℕ} {i j : Fin N}
    (h : (i : ℕ) + 2 ≤ (j : ℕ) ∨ (j : ℕ) + 2 ≤ (i : ℕ)) :
    Commute (cubicSite N i) (cubicSite N j) := by
  have h1 : ¬ ((i : ℕ) + 1 = (j : ℕ)) := by omega
  have h2 : ¬ ((j : ℕ) + 1 = (i : ℕ)) := by omega
  have hij : chainForm N (Pi.single i 1) (Pi.single j 1) = 0 := by
    simp [chainForm_single_single, h1, h2]
  have hji : chainForm N (Pi.single j 1) (Pi.single i 1) = 0 := by
    simp [chainForm_single_single, h1, h2]
  rw [Commute, SemiconjBy, cubicSite, cubicSite, weyl_mul_weyl, weyl_mul_weyl,
    mul_comm (Multiplicative.ofAdd _)]
  simp [cubicFactor, hij, hji]

/-- The `j`-th Jones projection `p_j = 3⁻¹ • (1 + U_j + U_j ^ 2)` in `CubicTorus N`. -/
noncomputable def cubicProjection (N : ℕ) (j : Fin N) : CubicTorus N :=
  (3 : ℂ)⁻¹ • (1 + cubicSite N j + cubicSite N j ^ 2)

/-- Unfolding `cubicProjection N j`. -/
theorem cubicProjection_def (N : ℕ) (j : Fin N) :
    cubicProjection N j = (3 : ℂ)⁻¹ • (1 + cubicSite N j + cubicSite N j ^ 2) :=
  (rfl)

/-- Each projection `cubicProjection N j` is fixed by `cubicInversion N`. -/
@[simp]
theorem cubicInversion_cubicProjection (N : ℕ) (j : Fin N) :
    cubicInversion N (cubicProjection N j) = cubicProjection N j := by
  have hsq : cubicInversion N (cubicSite N j ^ 2) = cubicSite N j := by
    rw [map_pow, cubicInversion_cubicSite, ← pow_mul]
    calc
      cubicSite N j ^ (2 * 2) = cubicSite N j ^ 3 * cubicSite N j := by rw [pow_succ]
      _ = cubicSite N j := by rw [cubicSite_pow_three, one_mul]
  rw [cubicProjection_def, map_smul, map_add, map_add, map_one, cubicInversion_cubicSite, hsq]
  congr 1
  abel

/-- Each projection `cubicProjection N j` lies in the inversion-fixed subalgebra `cubicFixed N`. -/
theorem cubicProjection_mem_cubicFixed (N : ℕ) (j : Fin N) :
    cubicProjection N j ∈ cubicFixed N :=
  mem_cubicFixed_iff.mpr (cubicInversion_cubicProjection N j)

/-- Each projection `cubicProjection N j` is self-adjoint. -/
@[simp]
theorem star_cubicProjection (N : ℕ) (j : Fin N) :
    star (cubicProjection N j) = cubicProjection N j := by
  have hsq : star (cubicSite N j ^ 2) = cubicSite N j := by
    rw [star_pow, star_cubicSite, ← pow_mul]
    calc
      cubicSite N j ^ (2 * 2) = cubicSite N j ^ 3 * cubicSite N j := by rw [pow_succ]
      _ = cubicSite N j := by rw [cubicSite_pow_three, one_mul]
  rw [cubicProjection_def, star_smul, star_add, star_add, star_one, star_cubicSite, hsq]
  have h3 : star ((3 : ℂ)⁻¹) = (3 : ℂ)⁻¹ := by simp
  rw [h3]
  congr 1
  abel

/-- `U_j` acts as the identity on `p_j`. -/
private theorem cubicSite_mul_cubicProjection (N : ℕ) (j : Fin N) :
    cubicSite N j * cubicProjection N j = cubicProjection N j := by
  rw [cubicProjection_def, mul_smul_comm, mul_add, mul_add, mul_one, ← pow_two, ← pow_succ',
    cubicSite_pow_three]
  congr 1
  abel

/-- `U_j ^ 2` acts as the identity on `p_j`. -/
private theorem cubicSite_sq_mul_cubicProjection (N : ℕ) (j : Fin N) :
    cubicSite N j ^ 2 * cubicProjection N j = cubicProjection N j := by
  rw [pow_two, mul_assoc, cubicSite_mul_cubicProjection, cubicSite_mul_cubicProjection]

/-- Each `cubicProjection N j` is idempotent. -/
@[simp]
theorem cubicProjection_mul_self (N : ℕ) (j : Fin N) :
    cubicProjection N j * cubicProjection N j = cubicProjection N j := by
  conv_lhs =>
    arg 1
    rw [cubicProjection_def]
  rw [smul_mul_assoc, add_mul, add_mul, one_mul, cubicSite_mul_cubicProjection,
    cubicSite_sq_mul_cubicProjection]
  have h3 : cubicProjection N j + cubicProjection N j + cubicProjection N j =
      (3 : ℂ) • cubicProjection N j := by
    rw [show (3 : ℂ) = 1 + 1 + 1 by norm_num]
    simp only [add_smul, one_smul]
  rw [h3, smul_smul]
  norm_num

/-- If `U_i` `ζ`-commutes with `y` where `1 + ζ + ζ ^ 2 = 0`, then `p_i * y * p_i = 0`. -/
private theorem cubicProjection_mul_mul_cubicProjection_eq_zero {N : ℕ} {i : Fin N}
    {y : CubicTorus N} {ζ : ℂ} (hcomm : cubicSite N i * y = ζ • (y * cubicSite N i))
    (hcyc : 1 + ζ + ζ ^ 2 = 0) :
    cubicProjection N i * y * cubicProjection N i = 0 := by
  have hcomm2 : cubicSite N i ^ 2 * y = ζ ^ 2 • (y * cubicSite N i ^ 2) := by
    rw [pow_two, mul_assoc, hcomm, mul_smul_comm, ← mul_assoc, hcomm, smul_mul_assoc, smul_smul,
      mul_assoc, ← pow_two, ← pow_two]
  conv_lhs =>
    arg 1
    arg 1
    rw [cubicProjection_def]
  rw [smul_mul_assoc, smul_mul_assoc, add_mul, add_mul, add_mul, add_mul, one_mul,
    hcomm, hcomm2, smul_mul_assoc, smul_mul_assoc, mul_assoc, mul_assoc,
    cubicSite_mul_cubicProjection, cubicSite_sq_mul_cubicProjection]
  have hsum :
      y * cubicProjection N i + ζ • (y * cubicProjection N i) +
        ζ ^ 2 • (y * cubicProjection N i) = (1 + ζ + ζ ^ 2) • (y * cubicProjection N i) := by
    simp [add_smul]
  rw [hsum, hcyc, zero_smul, smul_zero]

/-- **The Jones braid relation for `cubicProjection`**: when `i` and `j` are adjacent,
`p_i * p_j * p_i = 3⁻¹ • p_i`. -/
theorem cubicProjection_mul_cubicProjection_mul_cubicProjection {N : ℕ} {i j : Fin N}
    (h : (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)) :
    cubicProjection N i * cubicProjection N j * cubicProjection N i =
      (3 : ℂ)⁻¹ • cubicProjection N i := by
  have hexists : ∃ η : ℂ,
      cubicSite N i * cubicSite N j = η • (cubicSite N j * cubicSite N i) ∧
      η ^ 3 = 1 ∧ 1 + η + η ^ 2 = 0 := by
    rcases h with hij | hji
    · refine ⟨cubeRootOfUnity, cubicSite_mul_cubicSite_of_succ hij,
        isPrimitiveRoot_cubeRootOfUnity.pow_eq_one, one_add_cubeRootOfUnity_add_sq⟩
    · refine ⟨((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ),
        cubicSite_mul_cubicSite_of_pred hji, ?_, ?_⟩
      · rw [← Units.val_pow_eq_pow_val, inv_pow, cubeRootOfUnity_pow_three, inv_one,
          Units.val_one]
      · have hinv : ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ) = (cubeRootOfUnity : ℂ) ^ 2 := by
          apply mul_right_cancel₀ (Units.ne_zero cubeRootOfUnity)
          rw [Units.inv_mul, ← pow_succ, isPrimitiveRoot_cubeRootOfUnity.pow_eq_one]
        have h3 : (cubeRootOfUnity : ℂ) ^ 3 = 1 := isPrimitiveRoot_cubeRootOfUnity.pow_eq_one
        rw [hinv]
        linear_combination one_add_cubeRootOfUnity_add_sq + (cubeRootOfUnity : ℂ) * h3
  obtain ⟨η, hη, hη3, hηcyc⟩ := hexists
  have h1 : cubicProjection N i * cubicSite N j * cubicProjection N i = 0 :=
    cubicProjection_mul_mul_cubicProjection_eq_zero hη hηcyc
  have h2 : cubicProjection N i * cubicSite N j ^ 2 * cubicProjection N i = 0 := by
    have hηsq : cubicSite N i * cubicSite N j ^ 2 =
        η ^ 2 • (cubicSite N j ^ 2 * cubicSite N i) := by
      rw [pow_two, ← mul_assoc, hη, smul_mul_assoc, mul_assoc, hη, mul_smul_comm, smul_smul,
        ← mul_assoc, ← pow_two]
    have hη2cyc : 1 + η ^ 2 + (η ^ 2) ^ 2 = 0 := by
      linear_combination hηcyc + η * hη3
    exact cubicProjection_mul_mul_cubicProjection_eq_zero hηsq hη2cyc
  conv_lhs =>
    arg 1
    arg 2
    rw [cubicProjection_def]
  rw [mul_smul_comm, smul_mul_assoc, mul_add, mul_add, add_mul, add_mul, mul_one,
    cubicProjection_mul_self, h1, h2, add_zero, add_zero]

/-- Projections at distance at least two commute. -/
theorem commute_cubicProjection {N : ℕ} {i j : Fin N}
    (h : (i : ℕ) + 2 ≤ (j : ℕ) ∨ (j : ℕ) + 2 ≤ (i : ℕ)) :
    Commute (cubicProjection N i) (cubicProjection N j) := by
  have hc := commute_cubicSite h
  rw [cubicProjection_def, cubicProjection_def]
  have hc1 : Commute (1 + cubicSite N i + cubicSite N i ^ 2)
      (1 + cubicSite N j + cubicSite N j ^ 2) :=
    ((Commute.one_right _).add_right
      (((Commute.one_left _).add_left hc).add_left (hc.pow_left 2))).add_right
      (((Commute.one_left _).add_left (hc.pow_right 2)).add_left
        ((hc.pow_left 2).pow_right 2))
  exact (hc1.smul_left _).smul_right _

/-- The canonical trace of each projection `cubicProjection N j` is `3⁻¹`. -/
@[simp]
theorem trace_cubicProjection (N : ℕ) (j : Fin N) :
    TwistedMonoidAlgebra.trace (cubicProjection N j) = (3 : ℂ)⁻¹ := by
  let e1 : Fin N → ZMod 3 := Pi.single j 1
  let e2 : Fin N → ZMod 3 := Pi.single j 2
  have h1 : Multiplicative.ofAdd e1 ≠ 1 := by
    intro h
    have := congrFun (congrArg Multiplicative.toAdd h) j
    simp [e1] at this
  have h2 : Multiplicative.ofAdd e2 ≠ 1 := by
    intro h
    have := congrFun (congrArg Multiplicative.toAdd h) j
    simp only [toAdd_ofAdd, toAdd_one, Pi.zero_apply, e2, Pi.single_eq_same] at this
    exact absurd this (by decide)
  rw [cubicProjection_def, map_smul, map_add, map_add, TwistedMonoidAlgebra.trace_one,
    cubicSite_sq, cubicSite_def, weyl_def, weyl_def, TwistedMonoidAlgebra.trace_of_ne_one h1,
    TwistedMonoidAlgebra.trace_of_ne_one h2]
  simp

/-! ### The comparison `⋆`-algebra homomorphism `cubicFixedHom` and surjectivity -/

/-- Underlying `ℂ`-algebra homomorphism of `cubicFixedHom m`. -/
private noncomputable def cubicFixedAlgHom (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1) :=
  TemperleyLieb.lift
    (fun j ↦ (Real.sqrt 3 : ℂ) •
      ⟨cubicProjection (m - 1) j, cubicProjection_mem_cubicFixed (m - 1) j⟩)
    (fun j ↦ Subtype.ext <| by
      simp [smul_smul, sqrt_three_coe_mul_self])
    (fun {i j} hij ↦ Subtype.ext <| by
      simp only [SetLike.val_smul, MulMemClass.coe_mul, smul_mul_smul_comm,
        cubicProjection_mul_cubicProjection_mul_cubicProjection hij, smul_smul]
      have hcoeff :
          (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) * (3 : ℂ)⁻¹ =
            (Real.sqrt 3 : ℂ) := by
        rw [sqrt_three_coe_mul_self]
        ring
      rw [hcoeff])
    (fun {i j} hij ↦ Subtype.ext <| by
      simpa using (commute_cubicProjection hij).eq)

private theorem coe_cubicFixedAlgHom_e (m : ℕ) (j : Fin (m - 1)) :
    (cubicFixedAlgHom m (e (Real.sqrt 3 : ℂ) j) : CubicTorus (m - 1)) =
      (Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j := by
  simp [cubicFixedAlgHom]

/-- **The cubic quantum torus representation of `TemperleyLieb ℂ (√3 : ℂ) m`**, mapping each
generator `e (√3 : ℂ) j` to `(√3 : ℂ) • cubicProjection (m - 1) j` inside
`cubicFixed (m - 1)`. -/
noncomputable def cubicFixedHom (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1) :=
  { cubicFixedAlgHom m with
    map_star' := (TemperleyLieb.map_star_iff (F := cubicFixedAlgHom m)).mpr fun j ↦ by
      rw [IsSelfAdjoint]
      apply Subtype.ext
      rw [StarMemClass.coe_star, coe_cubicFixedAlgHom_e, star_smul, star_cubicProjection,
        Complex.star_def, Complex.conj_ofReal] }

/-- On each Temperley–Lieb generator, `cubicFixedHom m` evaluates to
`(√3 : ℂ) • cubicProjection (m - 1) j` inside `CubicTorus (m - 1)`. -/
@[simp]
theorem coe_cubicFixedHom_e (m : ℕ) (j : Fin (m - 1)) :
    (cubicFixedHom m (e (Real.sqrt 3 : ℂ) j) : CubicTorus (m - 1)) =
      (Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j :=
  coe_cubicFixedAlgHom_e m j

/-- Symmetrized Weyl element `W(a) + W(a⁻¹)`, spanning `cubicFixed N`. -/
private noncomputable def symWeyl (N : ℕ)
    (a : Multiplicative (Fin N → ZMod 3)) : CubicTorus N :=
  weyl N a + weyl N a⁻¹

private theorem symWeyl_inv (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    symWeyl N a⁻¹ = symWeyl N a := by
  simp [symWeyl, add_comm]

private theorem symWeyl_one (N : ℕ) : symWeyl N 1 = (2 : ℂ) • 1 := by
  simp [symWeyl, two_smul]

private theorem symWeyl_mul (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    symWeyl N a * symWeyl N b =
      (cubicFactor N a b : ℂ) • symWeyl N (a * b) +
        (((cubicFactor N a b)⁻¹ : ℂˣ) : ℂ) • symWeyl N (a * b⁻¹) := by
  simp only [symWeyl, add_mul, mul_add, weyl_mul_weyl,
    cubicFactor_inv_right_eq, cubicFactor_inv_left_eq, smul_add]
  have h1 : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by rw [mul_inv]
  have h2 : a⁻¹ * b = (a * b⁻¹)⁻¹ := by rw [mul_inv, inv_inv]
  rw [h1, h2]
  abel

private theorem symWeyl_mul_swap (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    symWeyl N b * symWeyl N a =
      (((cubicFactor N a b)⁻¹ : ℂˣ) : ℂ) • symWeyl N (a * b) +
        (cubicFactor N a b : ℂ) • symWeyl N (a * b⁻¹) := by
  rw [symWeyl_mul, cubicFactor_swap, inv_inv, mul_comm b a]
  have hinv : b * a⁻¹ = (a * b⁻¹)⁻¹ := by rw [mul_inv, inv_inv, mul_comm]
  rw [hinv, symWeyl_inv]

/-- When `B(a, b) ≠ 0`, both `symWeyl (a * b)` and `symWeyl (a * b⁻¹)` lie in any subalgebra
containing `symWeyl a` and `symWeyl b`. -/
private theorem symWeyl_mul_and_mul_inv_mem {N : ℕ} {S : Subalgebra ℂ (CubicTorus N)}
    {a b : Multiplicative (Fin N → ZMod 3)}
    (ha : symWeyl N a ∈ S) (hb : symWeyl N b ∈ S)
    (hform : chainForm N a.toAdd b.toAdd ≠ 0) :
    symWeyl N (a * b) ∈ S ∧ symWeyl N (a * b⁻¹) ∈ S := by
  set u : ℂˣ := cubicFactor N a b with hu_def
  have hu3 : (u : ℂ) ^ 3 = 1 := by
    have hu : u = cubeRootPow (2 * chainForm N a.toAdd b.toAdd) := rfl
    rw [hu, cubeRootPow, ← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul,
      cubeRootOfUnity_pow_three, one_pow, Units.val_one]
  have hu_ne : (u : ℂ) ≠ 1 := by
    have hu : u = cubeRootPow (2 * chainForm N a.toAdd b.toAdd) := rfl
    have h3 : (cubeRootOfUnity : ℂ) ^ 3 = 1 := isPrimitiveRoot_cubeRootOfUnity.pow_eq_one
    rw [hu]
    rcases (by decide : ∀ t : ZMod 3, t = 0 ∨ t = 1 ∨ t = 2) (chainForm N a.toAdd b.toAdd)
      with ht | ht | ht
    · exact absurd ht hform
    · rw [ht]
      have h21 : (2 : ZMod 3) * 1 = 2 := by decide
      rw [h21]
      intro hsq
      have hsq' : (cubeRootOfUnity : ℂ) ^ 2 = 1 := by
        simpa [cubeRootPow, show (2 : ZMod 3).val = 2 from rfl] using hsq
      exact cubeRootOfUnity_ne_one (by
        calc
          (cubeRootOfUnity : ℂ) = (cubeRootOfUnity : ℂ) ^ 2 * (cubeRootOfUnity : ℂ) := by
            rw [hsq', one_mul]
          _ = (cubeRootOfUnity : ℂ) ^ 3 := by ring
          _ = 1 := h3)
    · rw [ht]
      have h22 : (2 : ZMod 3) * 2 = 1 := by decide
      rw [h22, cubeRootPow_one]
      exact cubeRootOfUnity_ne_one
  have hinv_sq : ((u⁻¹ : ℂˣ) : ℂ) ^ 2 = (u : ℂ) := by
    apply mul_right_cancel₀ (pow_ne_zero 2 (Units.ne_zero u))
    calc
      ((u⁻¹ : ℂˣ) : ℂ) ^ 2 * (u : ℂ) ^ 2
          = (((u⁻¹ : ℂˣ) : ℂ) * (u : ℂ)) ^ 2 := by ring
      _ = 1 := by rw [Units.inv_mul, one_pow]
      _ = (u : ℂ) * (u : ℂ) ^ 2 := by rw [← pow_succ', hu3]
  have hdet : (u : ℂ) ^ 2 - ((u⁻¹ : ℂˣ) : ℂ) ^ 2 ≠ 0 := by
    rw [hinv_sq, show (u : ℂ) ^ 2 - (u : ℂ) = (u : ℂ) * ((u : ℂ) - 1) by ring]
    exact mul_ne_zero (Units.ne_zero u) (sub_ne_zero.mpr hu_ne)
  have hcancel : (u : ℂ) * ((u⁻¹ : ℂˣ) : ℂ) = 1 := Units.mul_inv u
  have hcancel' : ((u⁻¹ : ℂˣ) : ℂ) * (u : ℂ) = 1 := Units.inv_mul u
  have hcomb1 :
      (u : ℂ) • (symWeyl N a * symWeyl N b) +
        (-((u⁻¹ : ℂˣ) : ℂ)) • (symWeyl N b * symWeyl N a) =
      ((u : ℂ) ^ 2 - ((u⁻¹ : ℂˣ) : ℂ) ^ 2) • symWeyl N (a * b) := by
    rw [symWeyl_mul N a b, symWeyl_mul_swap N a b, ← hu_def]
    simp only [smul_add, smul_smul, neg_mul, hcancel, hcancel']
    rw [add_add_add_comm, ← add_smul, ← add_smul, add_neg_cancel, zero_smul, add_zero]
    congr 1
    ring
  have hcomb2 :
      (u : ℂ) • (symWeyl N b * symWeyl N a) +
        (-((u⁻¹ : ℂˣ) : ℂ)) • (symWeyl N a * symWeyl N b) =
      ((u : ℂ) ^ 2 - ((u⁻¹ : ℂˣ) : ℂ) ^ 2) • symWeyl N (a * b⁻¹) := by
    rw [symWeyl_mul N a b, symWeyl_mul_swap N a b, ← hu_def]
    simp only [smul_add, smul_smul, neg_mul, hcancel, hcancel']
    rw [add_add_add_comm, ← add_smul, ← add_smul, add_neg_cancel, zero_smul, zero_add]
    congr 1
    ring
  constructor
  · have hmem : ((u : ℂ) ^ 2 - ((u⁻¹ : ℂˣ) : ℂ) ^ 2) • symWeyl N (a * b) ∈ S := by
      rw [← hcomb1]
      exact add_mem (S.smul_mem (mul_mem ha hb) _) (S.smul_mem (mul_mem hb ha) _)
    have hmem' := S.smul_mem hmem ((u : ℂ) ^ 2 - ((u⁻¹ : ℂˣ) : ℂ) ^ 2)⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hdet, one_smul] at hmem'
  · have hmem :
        ((u : ℂ) ^ 2 - ((u⁻¹ : ℂˣ) : ℂ) ^ 2) • symWeyl N (a * b⁻¹) ∈ S := by
      rw [← hcomb2]
      exact add_mem (S.smul_mem (mul_mem hb ha) _) (S.smul_mem (mul_mem ha hb) _)
    have hmem' := S.smul_mem hmem ((u : ℂ) ^ 2 - ((u⁻¹ : ℂˣ) : ℂ) ^ 2)⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hdet, one_smul] at hmem'

/-- Ambient `ℂ`-algebra homomorphism into `CubicTorus (m - 1)` used to prove surjectivity of
`cubicFixedHom m`. -/
private noncomputable def ambientCubicFixedHom (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₐ[ℂ] CubicTorus (m - 1) :=
  (cubicFixed (m - 1)).toSubalgebra.val.comp (cubicFixedHom m).toAlgHom

private theorem symWeyl_single_mem_range (m : ℕ) (j : Fin (m - 1)) :
    symWeyl (m - 1) (Multiplicative.ofAdd (Pi.single j 1)) ∈ (ambientCubicFixedHom m).range := by
  rw [AlgHom.mem_range]
  refine ⟨(Real.sqrt 3 : ℂ) • e (Real.sqrt 3 : ℂ) j - 1, ?_⟩
  have he : ambientCubicFixedHom m (e (Real.sqrt 3 : ℂ) j) =
      (Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j :=
    coe_cubicFixedHom_e m j
  rw [map_sub, map_smul, map_one, he, cubicProjection_def, smul_smul, smul_smul,
    sqrt_three_coe_mul_self]
  have h3 : (3 : ℂ) * (3 : ℂ)⁻¹ = 1 := by norm_num
  rw [h3, one_smul]
  have hsym : symWeyl (m - 1) (Multiplicative.ofAdd (Pi.single j 1)) =
      cubicSite (m - 1) j + cubicSite (m - 1) j ^ 2 := by
    rw [symWeyl, ← cubicSite, ← star_weyl, ← cubicSite, star_cubicSite]
  rw [hsym]
  abel

/-- Every `symWeyl (m - 1) (ofAdd v)` supported on indices `< k` lies in
`(ambientCubicFixedHom m).range`. -/
private theorem symWeyl_mem_range_of_support (m : ℕ) :
    ∀ {k : ℕ} (_hk : k ≤ m - 1) (v : Fin (m - 1) → ZMod 3),
      (∀ r : Fin (m - 1), k ≤ (r : ℕ) → v r = 0) →
      symWeyl (m - 1) (Multiplicative.ofAdd v) ∈ (ambientCubicFixedHom m).range
  | 0, _, v, hv => by
    have hv0 : v = 0 := funext fun r ↦ hv r (Nat.zero_le _)
    rw [hv0, ofAdd_zero, symWeyl_one]
    exact Subalgebra.smul_mem _ (one_mem _) _
  | k + 1, hk, v, hv => by
    let S := (ambientCubicFixedHom m).range
    let i₀ : Fin (m - 1) := ⟨k, by omega⟩
    let x : Fin (m - 1) → ZMod 3 := Function.update v i₀ 0
    have hxsupp : ∀ r : Fin (m - 1), k ≤ (r : ℕ) → x r = 0 := by
      intro r hr
      by_cases hri : r = i₀
      · simp [x, hri]
      · have hgt : k + 1 ≤ (r : ℕ) := by
          have : (r : ℕ) ≠ k := fun h ↦ hri (Fin.ext h)
          omega
        simp [x, hri, hv r hgt]
    have hxstep : ∀ (u : Fin (m - 1) → ZMod 3),
        (∀ r : Fin (m - 1), k ≤ (r : ℕ) → u r = 0) →
        symWeyl (m - 1) (Multiplicative.ofAdd (u + Pi.single i₀ 1)) ∈ S := by
      intro u husupp
      have huS : symWeyl (m - 1) (Multiplicative.ofAdd u) ∈ S :=
        symWeyl_mem_range_of_support m (by omega) u husupp
      have heiS : symWeyl (m - 1) (Multiplicative.ofAdd (Pi.single i₀ 1)) ∈ S :=
        symWeyl_single_mem_range m i₀
      cases k with
      | zero =>
        have hu0 : u = 0 := funext fun r ↦ husupp r (Nat.zero_le _)
        simpa [hu0] using heiS
      | succ j =>
        let j₀ : Fin (m - 1) := ⟨j, by omega⟩
        have hejS : symWeyl (m - 1) (Multiplicative.ofAdd (Pi.single j₀ 1)) ∈ S :=
          symWeyl_single_mem_range m j₀
        have hBu : chainForm (m - 1) u (Pi.single i₀ 1) = u j₀ :=
          chainForm_single_succ_of_support (by omega) husupp
        by_cases huj : u j₀ ≠ 0
        · have hne : chainForm (m - 1) (Multiplicative.ofAdd u).toAdd
              (Multiplicative.ofAdd (Pi.single i₀ 1)).toAdd ≠ 0 := by
            simpa [hBu] using huj
          rw [ofAdd_add]
          exact (symWeyl_mul_and_mul_inv_mem huS heiS hne).1
        · push Not at huj
          let y : Fin (m - 1) → ZMod 3 := u + Pi.single j₀ 1
          have hysupp : ∀ r : Fin (m - 1), j + 1 ≤ (r : ℕ) → y r = 0 := by
            intro r hr
            have hrj : r ≠ j₀ := fun h ↦ by
              have := congrArg Fin.val h
              dsimp [j₀] at this
              omega
            simp [y, husupp r hr, Pi.single_eq_of_ne hrj]
          have hyS : symWeyl (m - 1) (Multiplicative.ofAdd y) ∈ S :=
            symWeyl_mem_range_of_support m (by omega) y hysupp
          have hyj : y j₀ = 1 := by
            simp [y, huj]
          have hBy : chainForm (m - 1) y (Pi.single i₀ 1) = 1 := by
            rw [chainForm_single_succ_of_support (by omega) hysupp, hyj]
          have hpair := symWeyl_mul_and_mul_inv_mem hyS heiS (by simp [hBy])
          have hyplusS : symWeyl (m - 1) (Multiplicative.ofAdd (y + Pi.single i₀ 1)) ∈ S := by
            rw [ofAdd_add]
            exact hpair.1
          have hyminusS : symWeyl (m - 1) (Multiplicative.ofAdd (y - Pi.single i₀ 1)) ∈ S := by
            rw [sub_eq_add_neg, ofAdd_add, ofAdd_neg]
            exact hpair.2
          have hBdiff :
              chainForm (m - 1) (y + Pi.single i₀ 1) (Pi.single j₀ 1) -
                chainForm (m - 1) (y - Pi.single i₀ 1) (Pi.single j₀ 1) = 1 := by
            rw [← LinearMap.sub_apply, ← map_sub]
            have hsub : (y + Pi.single i₀ 1) - (y - Pi.single i₀ 1) =
                (2 : ZMod 3) • (Pi.single i₀ 1 : Fin (m - 1) → ZMod 3) := by
              ext r
              simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              ring
            rw [hsub, map_smul, LinearMap.smul_apply, smul_eq_mul, chainForm_single_single]
            have hnot : ¬ (j + 1 + 1 = j) := by omega
            simp only [i₀, j₀, hnot, ↓reduceIte]
            decide
          by_cases hplus : chainForm (m - 1) (y + Pi.single i₀ 1) (Pi.single j₀ 1) ≠ 0
          · have hres := (symWeyl_mul_and_mul_inv_mem hyplusS hejS (by simpa using hplus)).2
            have heq : (y + Pi.single i₀ 1) + -(Pi.single j₀ 1) = u + Pi.single i₀ 1 := by
              simp only [y]
              abel
            rw [← heq, ofAdd_add, ofAdd_neg]
            exact hres
          · push Not at hplus
            have hminus : chainForm (m - 1) (y - Pi.single i₀ 1) (Pi.single j₀ 1) ≠ 0 := by
              intro hzero
              rw [hplus, hzero, sub_self] at hBdiff
              exact zero_ne_one hBdiff
            have hres := (symWeyl_mul_and_mul_inv_mem hyminusS hejS (by simpa using hminus)).2
            have heq : (y - Pi.single i₀ 1) + -(Pi.single j₀ 1) = u - Pi.single i₀ 1 := by
              simp only [y]
              abel
            have huminusS :
                symWeyl (m - 1) (Multiplicative.ofAdd (u - Pi.single i₀ 1)) ∈ S := by
              rw [← heq, ofAdd_add, ofAdd_neg]
              exact hres
            have hmul0 :
                symWeyl (m - 1) (Multiplicative.ofAdd u) *
                  symWeyl (m - 1) (Multiplicative.ofAdd (Pi.single i₀ 1)) =
                symWeyl (m - 1) (Multiplicative.ofAdd (u + Pi.single i₀ 1)) +
                  symWeyl (m - 1) (Multiplicative.ofAdd (u - Pi.single i₀ 1)) := by
              rw [symWeyl_mul]
              have hfac :
                  cubicFactor (m - 1) (Multiplicative.ofAdd u)
                    (Multiplicative.ofAdd (Pi.single i₀ 1)) = 1 := by
                simp [cubicFactor, hBu, huj]
              rw [hfac, inv_one, Units.val_one, one_smul, one_smul,
                ← ofAdd_add, ← ofAdd_neg, ← ofAdd_add, ← sub_eq_add_neg]
            have heqsum :
                symWeyl (m - 1) (Multiplicative.ofAdd (u + Pi.single i₀ 1)) =
                  symWeyl (m - 1) (Multiplicative.ofAdd u) *
                    symWeyl (m - 1) (Multiplicative.ofAdd (Pi.single i₀ 1)) +
                  (-1 : ℂ) • symWeyl (m - 1) (Multiplicative.ofAdd (u - Pi.single i₀ 1)) := by
              rw [hmul0, add_assoc]
              have hzero :
                  symWeyl (m - 1) (Multiplicative.ofAdd (u - Pi.single i₀ 1)) +
                    (-1 : ℂ) •
                      symWeyl (m - 1) (Multiplicative.ofAdd (u - Pi.single i₀ 1)) = 0 := by
                conv_lhs =>
                  arg 1
                  rw [← one_smul ℂ
                    (symWeyl (m - 1) (Multiplicative.ofAdd (u - Pi.single i₀ 1)))]
                rw [← add_smul, add_neg_cancel, zero_smul]
              rw [hzero, add_zero]
            rw [heqsum]
            exact add_mem (mul_mem huS heiS) (S.smul_mem huminusS (-1 : ℂ))
    have hvdecomp : v = x + Pi.single i₀ (v i₀) := by
      ext r
      by_cases hri : r = i₀ <;> simp [x, hri]
    rw [hvdecomp]
    rcases (by decide : ∀ t : ZMod 3, t = 0 ∨ t = 1 ∨ t = 2) (v i₀) with hr | hr | hr
    · rw [hr, Pi.single_zero, add_zero]
      exact symWeyl_mem_range_of_support m (by omega) x hxsupp
    · rw [hr]
      exact hxstep x hxsupp
    · rw [hr]
      have hneg2 : (2 : ZMod 3) = -1 := by decide
      have heq : -(x + Pi.single i₀ (2 : ZMod 3)) = (-x) + Pi.single i₀ 1 := by
        rw [hneg2, Pi.single_neg]
        abel
      have hnegsupp : ∀ t : Fin (m - 1), k ≤ (t : ℕ) → (-x) t = 0 := fun t ht ↦ by
        simp [hxsupp t ht]
      rw [← symWeyl_inv, ← ofAdd_neg, heq]
      exact hxstep (-x) hnegsupp

/-- **Surjectivity of `cubicFixedHom m`**: for every `m : ℕ`, the `⋆`-algebra homomorphism
`cubicFixedHom m : TemperleyLieb ℂ (√3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1)` is surjective.
-/
theorem cubicFixedHom_surjective (m : ℕ) : Function.Surjective (cubicFixedHom m) := by
  rintro ⟨x, hx⟩
  have hfix : cubicInversion (m - 1) x = x := mem_cubicFixed_iff.mp hx
  let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin (m - 1) → ZMod 3))
    (cubicFactor (m - 1))
  have hspan : x = (2 : ℂ)⁻¹ • ∑ a : Multiplicative (Fin (m - 1) → ZMod 3),
      b.repr x a • symWeyl (m - 1) a := by
    have hxrepr :
        x = ∑ a : Multiplicative (Fin (m - 1) → ZMod 3), b.repr x a • weyl (m - 1) a := by
      conv_lhs => rw [← b.sum_repr x]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [TwistedMonoidAlgebra.basis_apply, weyl]
    have hinvrepr : cubicInversion (m - 1) x =
        ∑ a : Multiplicative (Fin (m - 1) → ZMod 3), b.repr x a • weyl (m - 1) a⁻¹ := by
      conv_lhs => rw [hxrepr]
      simp [map_sum, map_smul]
    have h2 : (2 : ℂ) • x =
        ∑ a : Multiplicative (Fin (m - 1) → ZMod 3), b.repr x a • symWeyl (m - 1) a := by
      calc
        (2 : ℂ) • x = x + cubicInversion (m - 1) x := by rw [hfix, two_smul]
        _ = (∑ a, b.repr x a • weyl (m - 1) a) +
              (∑ a, b.repr x a • weyl (m - 1) a⁻¹) := by
          conv_lhs =>
            arg 1
            rw [hxrepr]
          rw [hinvrepr]
        _ = ∑ a, b.repr x a • symWeyl (m - 1) a := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [symWeyl, smul_add]
    rw [← h2, smul_smul]
    norm_num
  have hmem : x ∈ (ambientCubicFixedHom m).range := by
    rw [hspan]
    refine Subalgebra.smul_mem _ (sum_mem fun a _ ↦ Subalgebra.smul_mem _ ?_ _) _
    have hsupp : ∀ r : Fin (m - 1), m - 1 ≤ (r : ℕ) → a.toAdd r = 0 := fun r hr ↦ by omega
    simpa [ofAdd_toAdd] using symWeyl_mem_range_of_support m (le_refl _) a.toAdd hsupp
  obtain ⟨t, ht⟩ := hmem
  exact ⟨t, Subtype.ext ht⟩

end TauCeti.TemperleyLieb
