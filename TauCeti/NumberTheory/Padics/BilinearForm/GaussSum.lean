/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.LinearAlgebra.BilinearForm.Characteristic
import TauCeti.Algebra.Group.AddChar
import TauCeti.Data.ZMod.MulCastHom.Sum
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.Odd.LocalRing
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.BilinearForm.Prod
import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.GaussSum
import TauCeti.LinearAlgebra.Matrix.GaussSum
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import TauCeti.NumberTheory.LegendreSymbol.ZModChar
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Gauss sums of unimodular forms over `ℤ_[2]`

Let `C` be a symmetric bilinear form over `ℤ_[2]` whose Gram matrix `A` in a basis of size `n` has
a unit determinant. For `k ≥ 2`, write `e(t) = exp (2πi t)`. This file evaluates the Gauss sum
of `A` modulo `2 ^ k`:

```text
∑_{x ∈ (ℤ/2^k)^n} e(xᵀ A x / 2^k) = √2^{n (k + 1)} · ε^{k + 1} · e(t / 8),
```

where `ε = χ₈(det A) = (2 / det A)` is the sign of `C` and `t` is its oddity, the self-pairing
`C w w` of a characteristic vector `w` modulo `8`. Both are the entries of the Conway–Sloane
`2`-adic symbol of a unimodular constituent: the sign and the oddity are read off from the Gauss
sums modulo `4` and `8`. The formula holds for odd and even forms alike; an even form has oddity
`0`.

The Gauss-sum invariants of a Jordan splitting over `ℤ_[2]`
(`LinearMap.BilinForm.IsJordanSplitting.sum_addChar_dotProduct_toMatrix_mulVec_eq_of_equivalent`)
are, up to powers of `2`, products of Gauss sums of the unimodular rescalings of its constituents
at various moduli. This evaluation expresses such factors through the ranks, signs and oddities of
the constituents.

## Main results

* `PadicInt.sum_stdAddChar_toZModPow_mul_sq_eq_χ₈`: for a unit `u` of `ℤ_[2]`,
  `∑_{y ∈ ℤ/2^k} e(u y² / 2^k) = √2^{k + 1} · χ₈(u)^{k + 1} · e(u / 8)`.
* `LinearMap.BilinForm.IsSymm.sum_stdAddChar_dotProduct_toMatrix_map_mulVec_eq_χ₈`: the Gauss
  sum of a unimodular form over `ℤ_[2]` in terms of its rank, sign and oddity.

## Implementation notes

The rank-one sum modulo `2 ^ (j + 1)` is twice the Gauss sum of Nikulin's dyadic generator
`q_θ^{(2)}(2^j)`, whose value `θ + 4jω(θ)` with `ω(θ) = (θ² - 1) / 8` is
`TauCeti.FiniteQuadraticModule.gaussSign_dyadicCyclic`, and `(-1)^{ω(θ)} = χ₈(θ)`. A diagonal
Gauss sum is a product of rank-one sums. A unimodular form need not be diagonalizable over
`ℤ_[2]`, but its orthogonal sum `C ⊥ ⟨1⟩` with the unit form is odd, so it has an orthogonal basis
with unit self-pairings
(`LinearMap.BilinForm.IsSymm.exists_orthogonal_basis_isUnit_of_exists_isUnit_apply_self`). Its
Gauss sum is the product of that of `C` and of `⟨1⟩`, and the sign and oddity of `C ⊥ ⟨1⟩` are
those of `C`, the oddity shifted by `1`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.11.2.
-/

public section

open Module Complex ZMod
open LinearMap (BilinForm)
open Real (pi)
open TauCeti TauCeti.FiniteQuadraticModule
open scoped Matrix

namespace PadicInt

/-- For `j ≥ 1`, the Gauss sum `∑_{y ∈ ℤ/2^{j+1}} e(θy² / 2^{j+1})` is twice the Gauss sum of
`q_θ^{(2)}(2^j)`: the summand depends only on `y` modulo `2^j`. -/
private theorem sum_stdAddChar_eq_two_mul_gaussSum_dyadicCyclic (j : ℕ) [NeZero j] (θ : ℤ) :
    ∑ y : ZMod (2 ^ (j + 1)), stdAddChar ((θ : ZMod (2 ^ (j + 1))) * y ^ 2) =
      2 * (dyadicCyclic j θ).gaussSum := by
  -- The carrier of `dyadicCyclic j θ` is `ℤ/2^j` only after unfolding, so its Gauss sum is
  -- computed on `ℤ/2^j` and transported by definitional unfolding.
  let : Fintype (dyadicCyclic j θ) := inferInstanceAs (Fintype (ZMod (2 ^ j)))
  have hF (y : ZMod (2 ^ (j + 1))) : stdAddChar ((θ : ZMod (2 ^ (j + 1))) * y ^ 2) =
      expCircle ((dyadicCyclic j θ).quadratic
        (castHom (Dvd.intro_left 2 (pow_succ' 2 j).symm) (ZMod (2 ^ j)) y)) := by
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective y
    rw [map_intCast, dyadicCyclic_quadratic_intCast, expCircle_coe, ← Int.cast_pow,
      ← Int.cast_mul, stdAddChar_coe]
    congr 1
    push_cast
    ring
  have h := ZMod.sum_comp_castHom (ι := Unit) (m := 2) (n := 2 ^ (j + 1)) (2 ^ j)
    (pow_succ' 2 j).symm fun y ↦ expCircle ((dyadicCyclic j θ).quadratic (y ()))
  simp only [Fintype.card_unit, pow_one, nsmul_eq_mul, Nat.cast_ofNat] at h
  rw [gaussSum_eq_sum, Fintype.sum_equiv (Equiv.funUnique Unit (ZMod (2 ^ (j + 1)))).symm _
    (fun w ↦ expCircle ((dyadicCyclic j θ).quadratic
      (castHom (Dvd.intro_left 2 (pow_succ' 2 j).symm) (ZMod (2 ^ j)) (w ()))))
    (fun y ↦ by simp [hF]), h]
  congr 1
  exact Fintype.sum_equiv (Equiv.funUnique Unit (ZMod (2 ^ j))) _ _ fun y ↦ rfl

/-- **The quadratic Gauss sum modulo a power of `2`.** For a unit `u` of `ℤ_[2]` and `k ≥ 2`,
with `e(t) = exp (2πi t)`,
`∑_{y ∈ ℤ/2^k} e(u y² / 2^k) = √2^{k + 1} · χ₈(u)^{k + 1} · e(u / 8)`. For `k = 1` the sum is
`0`. -/
theorem sum_stdAddChar_toZModPow_mul_sq_eq_χ₈ {k : ℕ} (hk : 2 ≤ k) {u : ℤ_[2]} (hu : IsUnit u) :
    ∑ y : ZMod (2 ^ k), stdAddChar (toZModPow k u * y ^ 2) =
      (√2 : ℂ) ^ (k + 1) * ((χ₈ (toZModPow 3 u) : ℤ) : ℂ) ^ (k + 1) *
        stdAddChar (toZModPow 3 u) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have : NeZero j := ⟨by omega⟩
  -- An integer `θ` congruent to `u` modulo `2 ^ (j + 2)`, hence modulo `2 ^ (j + 1)` and `8`.
  obtain ⟨θ, hθ⟩ := ZMod.intCast_surjective (toZModPow (j + 2) u)
  have hcast {m : ℕ} (hm : m ≤ j + 2) : toZModPow m u = (θ : ZMod (2 ^ m)) := by
    rw [← cast_toZModPow m (j + 2) hm, ← hθ, ZMod.cast_intCast (pow_dvd_pow 2 hm)]
  have hodd : Odd θ := by
    have h := isUnit_iff_toZModPow_three_mul_self.mp hu
    rw [hcast (by omega)] at h
    have h2 := congrArg (ZMod.castHom (dvd_pow_self 2 three_ne_zero) (ZMod 2)) h
    rw [map_mul, map_intCast, map_one] at h2
    refine Int.not_even_iff_odd.mp fun he ↦ ?_
    rw [(ZMod.intCast_zmod_eq_zero_iff_dvd θ 2).mpr (even_iff_two_dvd.mp he), zero_mul] at h2
    exact zero_ne_one h2
  set ω := (θ ^ 2 - 1) / 8
  -- Nikulin's evaluation: the sum is `2 √(2^j) e((θ + 4jω) / 8)`.
  have hgauss : ∑ y : ZMod (2 ^ (j + 1)), stdAddChar ((θ : ZMod (2 ^ (j + 1))) * y ^ 2) =
      2 * ((√(((2 ^ j : ℕ) : ℝ)) : ℂ) *
        exp (2 * pi * I * (((θ + 4 * (j : ℤ) * ω : ℤ) : ℚ) / ((8 : ℕ) : ℚ) : ℚ))) := by
    rw [sum_stdAddChar_eq_two_mul_gaussSum_dyadicCyclic,
      ((isNondegenerate_dyadicCyclic_iff j θ).2 hodd).gaussSum_eq,
      gaussSign_dyadicCyclic (k := j) hodd, natCard_dyadicCyclic, toRatAddCircle_intCast,
      expCircle_coe]
  -- `(-1)^ω = χ₈(θ)`, the second supplement to quadratic reciprocity.
  have hχ : ((χ₈ (θ : ZMod (2 ^ 3)) : ℤ) : ℂ) = (-1 : ℂ) ^ ω := by
    rw [ZMod.χ₈_intCast_eq_negOnePow hodd, Int.cast_negOnePow]
  rw [hcast (by omega), hcast (by omega), hgauss, hχ, stdAddChar_coe]
  -- `e((θ + 4jω) / 8) = e(θ / 8) (-1)^{jω}` and `2 √(2^j) = √2^{j + 2}`, with `((-1)^ω)² = 1`.
  have hexp : exp (2 * pi * I * (((θ + 4 * (j : ℤ) * ω : ℤ) : ℚ) / ((8 : ℕ) : ℚ) : ℚ)) =
      exp (2 * pi * I * θ / ((2 ^ 3 : ℕ) : ℂ)) * (-1 : ℂ) ^ (ω * j) := by
    rw [← Complex.exp_pi_mul_I, ← exp_int_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsqrt : (√(((2 ^ j : ℕ) : ℝ)) : ℂ) = (√2 : ℂ) ^ j := by
    have h : ((2 ^ j : ℕ) : ℝ) = (√2 ^ j) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt zero_le_two, Nat.cast_pow, Nat.cast_ofNat]
    rw [h, Real.sqrt_sq (by positivity), ofReal_pow]
  have h2 : (√2 : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt zero_le_two, ofReal_ofNat]
  have hsign : ((-1 : ℂ) ^ ω) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp
  rw [hexp, hsqrt, zpow_mul, zpow_natCast]
  calc (2 : ℂ) * ((√2 : ℂ) ^ j * (exp (2 * pi * I * θ / ((2 ^ 3 : ℕ) : ℂ)) * ((-1) ^ ω) ^ j))
      = (√2 : ℂ) ^ 2 * (√2 : ℂ) ^ j * (((-1 : ℂ) ^ ω) ^ j * ((-1) ^ ω) ^ 2) *
          exp (2 * pi * I * θ / ((2 ^ 3 : ℕ) : ℂ)) := by rw [h2, hsign]; ring
    _ = _ := by ring

end PadicInt

namespace LinearMap.BilinForm

variable {M ι : Type*} [AddCommGroup M] [Module ℤ_[2] M] [Fintype ι] [DecidableEq ι]

/-- The Gauss sum modulo `2 ^ k` of a diagonal matrix with unit entries `d i` over `ℤ_[2]`, in
terms of the product and the sum of the entries. -/
private theorem sum_stdAddChar_dotProduct_diagonal_map_mulVec_eq {k : ℕ} (hk : 2 ≤ k)
    {d : ι → ℤ_[2]} (hd : ∀ i, IsUnit (d i)) :
    ∑ x : ι → ZMod (2 ^ k), stdAddChar (x ⬝ᵥ (Matrix.diagonal d).map (PadicInt.toZModPow k) *ᵥ x) =
      (√2 : ℂ) ^ (Fintype.card ι * (k + 1)) *
        ((χ₈ (PadicInt.toZModPow 3 (∏ i, d i)) : ℤ) : ℂ) ^ (k + 1) *
          stdAddChar (PadicInt.toZModPow 3 (∑ i, d i)) := by
  rw [Matrix.diagonal_map (map_zero _), Matrix.sum_addChar_dotProduct_diagonal_mulVec]
  simp_rw [PadicInt.sum_stdAddChar_toZModPow_mul_sq_eq_χ₈ hk (hd _)]
  -- The additive character turns the sum of the entries into a product.
  rw [map_sum, AddChar.map_sum_eq_prod]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul',
    Finset.prod_pow, map_prod, Int.cast_prod]

/-- **The odd case.** If a form over `ℤ_[2]` has an orthogonal basis `c` with unit self-pairings,
then its Gauss sum modulo `2 ^ k` in any basis `e` of the same size is
`√2^{n (k + 1)} · χ₈(det)^{k + 1} · e(B w w / 8)` for every characteristic vector `w`: in the basis
`c` it is a product of rank-one sums, the determinants in `c` and `e` differ by the square of a
unit, and `∑ i, c i` is characteristic with self-pairing `∑ i, B (c i) (c i)`. -/
private theorem iIsOrtho.sum_stdAddChar_dotProduct_toMatrix_map_mulVec_eq {N : Type*}
    [AddCommGroup N] [Module ℤ_[2] N] {B : BilinForm ℤ_[2] N} {n : ℕ} {c : Basis (Fin n) ℤ_[2] N}
    (hc : B.iIsOrtho c) (hcu : ∀ i, IsUnit (B (c i) (c i))) (e : Basis (Fin n) ℤ_[2] N) {w : N}
    (hw : B.IsCharacteristic w) {k : ℕ} (hk : 2 ≤ k) :
    ∑ x : Fin n → ZMod (2 ^ k), stdAddChar (x ⬝ᵥ (B.toMatrix e).map (PadicInt.toZModPow k) *ᵥ x) =
      (√2 : ℂ) ^ (n * (k + 1)) *
        ((χ₈ (PadicInt.toZModPow 3 (B.toMatrix e).det) : ℤ) : ℂ) ^ (k + 1) *
          stdAddChar (PadicInt.toZModPow 3 (B w w)) := by
  -- In the basis `c`, the Gram matrix is diagonal with unit entries.
  have hcsum : ∑ x : Fin n → ZMod (2 ^ k),
      stdAddChar (x ⬝ᵥ (B.toMatrix c).map (PadicInt.toZModPow k) *ᵥ x) =
        (√2 : ℂ) ^ (n * (k + 1)) *
          ((χ₈ (PadicInt.toZModPow 3 (B.toMatrix c).det) : ℤ) : ℂ) ^ (k + 1) *
            stdAddChar (PadicInt.toZModPow 3 (B (∑ i, c i) (∑ i, c i))) := by
    rw [hc.det_toMatrix, hc.apply_sum_sum, hc.toMatrix_eq_diagonal]
    simpa only [Fintype.card_fin] using sum_stdAddChar_dotProduct_diagonal_map_mulVec_eq hk hcu
  rw [sum_addChar_dotProduct_toMatrix_map_mulVec_eq B c e, hcsum,
    det_toMatrix_eq_det_sq_mul_det e c]
  -- The sign: the determinants differ by the square of a unit.
  have hP : IsUnit (e.toMatrix c).det :=
    Matrix.isUnit_det_of_right_inverse (e.toMatrix_mul_toMatrix_flip c)
  have h1 : ∀ x : ZMod (2 ^ 3), x * x = 1 → χ₈ x ^ 2 = 1 := by decide
  rw [map_mul, map_mul, map_pow, map_pow,
    h1 _ (PadicInt.isUnit_iff_toZModPow_three_mul_self.mp hP), one_mul]
  -- The oddity: characteristic vectors have the same self-pairing modulo `8`.
  have : Module.Free ℤ_[2] N := .of_basis c
  have : B.IsPerfPair := c.isPerfPair_of_isUnit_det B (hc.isUnit_det_toMatrix hcu)
  have h8 := hw.eight_dvd_apply_self_sub_apply_self hc.isSymm
    (hc.isCharacteristic_sum PadicInt.two_dvd_sq_sub_self)
  rw [(PadicInt.eight_dvd_sub_iff_toZModPow_three_eq.mp h8).symm]

/-- **The Gauss sum of a unimodular form over `ℤ_[2]`.** Let `C` be a symmetric bilinear form over
`ℤ_[2]` whose Gram matrix `A` in a basis `b` of size `n` has a unit determinant, and let `w` be a
characteristic vector of `C`. For `k ≥ 2`, with `e(t) = exp (2πi t)`,
`∑_{x ∈ (ℤ/2^k)^n} e(xᵀ A x / 2^k) = √2^{n (k + 1)} · χ₈(det A)^{k + 1} · e(C w w / 8)`.

The sign `χ₈(det A)` and the oddity `C w w` modulo `8` are the invariants of the Conway–Sloane
`2`-adic symbol of `C`; the sum modulo `8` is `2^{2n} e(C w w / 8)`, and the sum modulo `4` brings
in the sign. -/
theorem IsSymm.sum_stdAddChar_dotProduct_toMatrix_map_mulVec_eq_χ₈ {C : BilinForm ℤ_[2] M}
    (hC : C.IsSymm) (b : Basis ι ℤ_[2] M) (hdet : IsUnit (C.toMatrix b).det) {w : M}
    (hw : C.IsCharacteristic w) {k : ℕ} (hk : 2 ≤ k) :
    ∑ x : ι → ZMod (2 ^ k), stdAddChar (x ⬝ᵥ (C.toMatrix b).map (PadicInt.toZModPow k) *ᵥ x) =
      (√2 : ℂ) ^ (Fintype.card ι * (k + 1)) *
        ((χ₈ (PadicInt.toZModPow 3 (C.toMatrix b).det) : ℤ) : ℂ) ^ (k + 1) *
          stdAddChar (PadicInt.toZModPow 3 (C w w)) := by
  -- The orthogonal sum `D = C ⊥ ⟨1⟩` on `M × ℤ_[2]`, with the basis `d` extending `b`.
  set f := PadicInt.toZModPow (p := 2) k
  set D : BilinForm ℤ_[2] (M × ℤ_[2]) := C.prod (LinearMap.mul ℤ_[2] ℤ_[2])
  set d := b.prod (Basis.singleton Unit ℤ_[2])
  have hDd : D.toMatrix d = Matrix.fromBlocks (C.toMatrix b) 0 0 1 := by
    ext (i | i) (j | j) <;> simp [D, d, toMatrix_apply, prod_apply, Basis.prod_apply]
  have hDs : D.IsSymm := isSymm_prod_iff.2
    ⟨hC, ⟨fun x y ↦ by rw [LinearMap.mul_apply', LinearMap.mul_apply', mul_comm]⟩⟩
  -- `D` represents the unit `1`, so it has an orthogonal basis with unit self-pairings.
  set e := d.reindex (Fintype.equivFin (ι ⊕ Unit))
  have hedet : (D.toMatrix e).det = (C.toMatrix b).det := by
    rw [det_toMatrix_reindex, hDd, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  obtain ⟨c, hc, hcu⟩ := hDs.exists_orthogonal_basis_isUnit_of_exists_isUnit_apply_self e
    (hedet ▸ hdet) ⟨(0, 1), by simp [D, prod_apply]⟩
  -- `(w, 1)` is a characteristic vector of `D`, with self-pairing `C w w + 1`.
  have hw' : D.IsCharacteristic (w, 1) := isCharacteristic_iff.mpr fun x ↦ by
    have h := dvd_sub (isCharacteristic_iff.mp hw x.1) (PadicInt.two_dvd_sq_sub_self x.2)
    simp only [D, prod_apply, LinearMap.mul_apply']
    convert h using 1
    ring
  have hD := hc.sum_stdAddChar_dotProduct_toMatrix_map_mulVec_eq hcu e hw' hk
  -- In the basis `d`, the Gauss sum of `D` is that of `C` times that of `⟨1⟩`.
  rw [sum_addChar_dotProduct_toMatrix_map_mulVec_eq D d e, hDd, Matrix.fromBlocks_map,
    Matrix.map_zero _ (map_zero f), Matrix.map_zero _ (map_zero f),
    Matrix.sum_addChar_dotProduct_fromBlocks_zero_zero_mulVec, ← Matrix.diagonal_one,
    sum_stdAddChar_dotProduct_diagonal_map_mulVec_eq hk fun _ ↦ isUnit_one, hedet] at hD
  simp only [D, prod_apply, LinearMap.mul_apply', mul_one, map_add, AddChar.map_add_eq_mul,
    Fintype.card_unit, one_mul, Finset.prod_const_one, map_one, Int.cast_one, one_pow,
    Fintype.sum_unique, Fintype.card_sum] at hD
  -- Cancel the Gauss sum `√2^{k + 1} e(1 / 8)` of `⟨1⟩`.
  refine mul_right_cancel₀ (mul_ne_zero (pow_ne_zero (k + 1) (by simp))
    (by rw [stdAddChar_apply]; exact Circle.coe_ne_zero _)) (hD.trans ?_)
  ring

end LinearMap.BilinForm
