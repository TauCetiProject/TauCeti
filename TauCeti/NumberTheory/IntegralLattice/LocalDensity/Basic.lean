/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Instances.Rat
public import TauCeti.Data.ZMod.MulCastHom
public import TauCeti.LinearAlgebra.Matrix.IsometryMatrices.Basic
public import TauCeti.LinearAlgebra.Matrix.IsometryMatrices.FiniteField
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import TauCeti.Algebra.BigOperators.Field
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Data.Nat.Choose.Basic
import TauCeti.LinearAlgebra.Matrix.Defs
import TauCeti.LinearAlgebra.Matrix.Symmetric
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# The local density of a `ℤ_p`-lattice

Let `A` be the Gram matrix of a nondegenerate `ℤ_p`-lattice of rank `n`. Its local
(automorphism) density is the limit

```text
α_p(A) = lim_{r → ∞} p^{-r n (n - 1) / 2} · #{X ∈ Mₙ(ℤ/pʳ) : Xᵀ A X ≡ A (mod pʳ)},
```

and the local densities at all primes are the local factors of the mass of a genus of
positive definite lattices. This file defines the count inside the limit,
`Matrix.localDensityCount A r`, shows that it only depends on `A` up to a change of basis, proves
that it stabilizes at every prime, defines the local density `Matrix.localDensity A` as the limit,
and evaluates it at a prime `p` not dividing `2 det A`.

**Stabilization.** Let `A` be symmetric with `2 det A ∣ pᵉ`, for instance `e = v_p(2 det A)`.
For every `r > 2 e` the count at level `r + 1` is `p ^ (n.choose 2)` times the count at level `r`,
so the normalized count is constant from `r₀ = 2 e + 1` on, and the local density exists and is a
positive rational number.

**Primes not dividing `2 det A`.** There one may take `e = 0`, so the normalized count is constant
from `r = 1` on, and the local density is `#O(A mod p) / p^{n (n - 1) / 2}`, where `O(A mod p)`
is the orthogonal group of the reduction of `A` modulo `p`. The orders of the finite orthogonal
groups then give the closed values

```text
n = 2m + 1:  α_p(A) = 2 ∏_{i=1}^{m} (1 - p^{-2i}),
n = 2m + 2:  α_p(A) = 2 (1 - ε p^{-(m+1)}) ∏_{i=1}^{m} (1 - p^{-2i}),  ε = ((-1)^{m+1} det A | p).
```

The sign `ε` is the character of the determinant twisted by `(-1)^{m+1}`, which records whether
the reduction is split; the hyperbolic plane at `p = 3` has `det = -1`, a nonsquare, and density
`4/3 = 2 (1 - 3⁻¹)`.

## Main definitions

* `Matrix.localDensityCount A r`: the number of `X ∈ Mₙ(ℤ/pʳ)` with `Xᵀ A X = A` modulo `pʳ`.
* `Matrix.localDensity A`: the local density `α_p(A)`, the limit of the normalized counts.

## Main results

* `Matrix.localDensityCount_transpose_mul_mul`, `Matrix.localDensity_transpose_mul_mul`: the count
  and the local density are unchanged by a change of basis `A ↦ Pᵀ A P`, so they only depend on
  the isometry class of the lattice.
* `Matrix.localDensityCount_succ_of_dvd`: for `A` symmetric with `2 det A ∣ pᵉ` and `r > 2 e`,
  the count at level `r + 1` is `p ^ (n.choose 2)` times the count at level `r`.
* `Matrix.localDensityCount_div_pow_of_dvd`, `Matrix.localDensityCount_div_pow_of_det_ne_zero`:
  the normalized count equals `α_p(A)` from level `2 e + 1` on, in particular from level
  `2 v_p(2 det A) + 1` on when `det A ≠ 0`.
* `Matrix.tendsto_localDensityCount_div_of_det_ne_zero`, `Matrix.localDensity_pos`: for symmetric
  `A` with `det A ≠ 0` the normalized count converges to `α_p(A)`, which is positive.
* `Matrix.localDensityCount_succ_of_isUnit_det`: for `p` odd, `A` symmetric with unit
  determinant and `r ≥ 1`, the count at level `r + 1` is `p ^ (n.choose 2)` times the count at
  level `r`.
* `Matrix.tendsto_localDensityCount_div_of_isUnit_det`, `Matrix.localDensity_eq_of_isUnit_det`: at
  such a prime the local density is the count at level `1` divided by `p ^ (n.choose 2)`.
* `Matrix.localDensityCount_one`: the count at level `1` is the number of matrices over `𝔽_p`
  preserving the reduction of `A` modulo `p`; when that reduction is nondegenerate, this is the
  order of its orthogonal group.
* `Matrix.isUnit_det_map_padicInt_iff`: an integer matrix has unit determinant over `ℤ_p` exactly
  when `p` does not divide its determinant, so the results above apply at every prime not
  dividing `2 det A`.
* `Matrix.tendsto_localDensityCount_div_of_card_eq_two_mul_add_one`,
  `Matrix.tendsto_localDensityCount_div_of_card_eq_two_mul_add_two`: the closed values of the
  local density at such a prime, in odd and in even rank.
* `Matrix.tendsto_localDensityCount_div_hyperbolicPlane_three`: the hyperbolic plane at `p = 3`.

## References

* C. L. Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. of Math. 36
  (1935).
* Y. Kitaoka, *Arithmetic of Quadratic Forms*, Cambridge Tracts in Mathematics 106 (1993),
  Chapter 5, for the stabilization of the local density counts.
* J. H. Conway, N. J. A. Sloane, *Low-dimensional lattices. IV. The mass formula*, Proc. Roy.
  Soc. London Ser. A 419 (1988), equation (6).
-/

public section

open Filter Topology

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {p : ℕ} [Fact p.Prime]

/-- The counting function of the local density of a Gram matrix `A` over `ℤ_p`: the number of
matrices `X ∈ Mₙ(ℤ/pʳ)` with `Xᵀ A X = A` modulo `pʳ`. -/
noncomputable def localDensityCount (A : Matrix n n ℤ_[p]) (r : ℕ) : ℕ :=
  Nat.card (isometryMatrices (A.map (PadicInt.toZModPow r)))

/-- The local density count is the cardinality of the solution set of `Xᵀ A X = A` over
`ℤ/pʳ`. -/
theorem localDensityCount_def (A : Matrix n n ℤ_[p]) (r : ℕ) :
    A.localDensityCount r = Nat.card (isometryMatrices (A.map (PadicInt.toZModPow r))) :=
  (rfl)

/-- The local density count is positive: the identity matrix is always counted. -/
theorem localDensityCount_pos (A : Matrix n n ℤ_[p]) (r : ℕ) :
    0 < A.localDensityCount r :=
  Nat.card_pos

/-- **The local density count does not depend on the basis**: replacing the Gram matrix `A` by
`Pᵀ A P` for an invertible `P` over `ℤ_p` leaves the count unchanged. -/
theorem localDensityCount_transpose_mul_mul {A P : Matrix n n ℤ_[p]} (hP : IsUnit P.det)
    (r : ℕ) : (Pᵀ * A * P).localDensityCount r = A.localDensityCount r := by
  rw [localDensityCount_def, localDensityCount_def, Matrix.map_mul, Matrix.map_mul,
    transpose_map]
  refine natCard_isometryMatrices_transpose_mul_mul ?_
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact hP.map _

/-! ### Stabilization at every prime -/

/- The proof of `localDensityCount_succ_of_dvd` has three steps, with `k = r - e > e`:

* for `r > e` every solution modulo `pʳ` has unit determinant, so the solutions form a group, and
  their number is the number of their images modulo `pᵏ` times the number of solutions that are
  `1` modulo `pᵏ`;
* one Newton step `X ↦ X + pᵏ Z`, with `Z` built from the adjugate of `Xᵀ A`, shows that the
  solutions at levels `r` and `r + 1` have the same images modulo `pᵏ`;
* the solutions that are `1` modulo `pᵏ` are the matrices `1 + pᵏ Z`, with `Z` modulo `pᵉ`
  (at level `r`) or modulo `pᵉ⁺¹` (at level `r + 1`) in the kernel of `Z ↦ A Z + (A Z)ᵀ`. This
  map takes symmetric values, and its image contains `pᵉ` times every symmetric matrix `H`, the
  image of `c adj(A) H` for `pᵉ = 2 det A · c`. So its image has the same index in the symmetric
  matrices at both levels, and its kernel grows by `p^{n²} / p^{n (n + 1) / 2} = p^{n (n - 1) / 2}`.
-/

/-- If `Xᵀ A X ≡ A` modulo `p ^ r`, where `det A` divides `p ^ e` for some `e < r`, then `X` has
unit determinant. -/
private theorem isUnit_det_of_map_mem_isometryMatrices {A X : Matrix n n ℤ_[p]} {e r : ℕ}
    (he : A.det ∣ (p : ℤ_[p]) ^ e) (her : e < r)
    (hX : X.map (PadicInt.toZModPow r) ∈ isometryMatrices (A.map (PadicInt.toZModPow r))) :
    IsUnit X.det := by
  rw [mem_isometryMatrices, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul] at hX
  have hdet := congrArg det hX
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det,
    PadicInt.toZModPow_eq_iff_dvd_sub, det_mul, det_mul, det_transpose] at hdet
  obtain ⟨s, hs⟩ := he
  obtain ⟨t, ht⟩ := hdet
  have hA0 : A.det ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hs
    exact pow_ne_zero e (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hs
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt her
  refine PadicInt.isUnit_of_dvd_one_sub_sq ⟨s * p ^ m * t, mul_left_cancel₀ hA0 ?_⟩
  calc A.det * (1 - X.det ^ 2) = (p : ℤ_[p]) ^ (e + m + 1) * t := by rw [← ht]; ring
    _ = A.det * (p * (s * p ^ m * t)) := by rw [pow_add, pow_add, hs]; ring

/-- The additive map `Z ↦ B Z + (B Z)ᵀ`, the derivative of `X ↦ Xᵀ B X` at the identity for
symmetric `B`. -/
private def tangentHom {R : Type*} [CommRing R] (B : Matrix n n R) :
    Matrix n n R →+ Matrix n n R where
  toFun Z := B * Z + (B * Z)ᵀ
  map_zero' := by simp
  map_add' Z W := by rw [Matrix.mul_add, transpose_add]; abel

/-- The value of `tangentHom B` at `Z`. -/
private theorem tangentHom_apply {R : Type*} [CommRing R] (B Z : Matrix n n R) :
    tangentHom B Z = B * Z + (B * Z)ᵀ :=
  rfl

/-- `tangentHom` commutes with ring homomorphisms of the coefficients. -/
private theorem map_tangentHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (B Z : Matrix n n R) : (tangentHom B Z).map f = tangentHom (B.map f) (Z.map f) := by
  rw [tangentHom_apply, tangentHom_apply, Matrix.map_add f (map_add f), Matrix.map_mul,
    transpose_map, Matrix.map_mul]

/-- **The adjugate inverts `tangentHom B` on symmetric matrices up to `2 det B`**: if
`t = 2 det B · c` and `T` is symmetric, then `Z ↦ B Z + (B Z)ᵀ` sends `c adj(B) T` to `t T`. -/
private theorem tangentHom_smul_adjugate_mul {R : Type*} [CommRing R] {B T : Matrix n n R}
    (hT : Tᵀ = T) {c t : R} (hc : t = 2 * B.det * c) :
    tangentHom B (c • (adjugate B * T)) = t • T := by
  have hBZ : B * (c • (adjugate B * T)) = (c * B.det) • T := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, mul_adjugate, smul_one_mul, smul_smul]
  rw [tangentHom_apply, hBZ, transpose_smul, hT, ← add_smul, hc]
  congr 1
  ring

/-- The expansion of `(X + t Z)ᵀ A (X + t Z)` for symmetric `A`: its linear term in `t` is the
value of `tangentHom (Xᵀ A)` at `Z`. -/
private theorem transpose_add_smul_mul_mul_add_smul {R : Type*} [CommRing R] {A : Matrix n n R}
    (hA : Aᵀ = A) (X Z : Matrix n n R) (t : R) :
    (X + t • Z)ᵀ * A * (X + t • Z) =
      Xᵀ * A * X + t • tangentHom (Xᵀ * A) Z + (t * t) • (Zᵀ * A * Z) := by
  simp [tangentHom_apply, hA, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
  module

/-- A symmetric matrix over `ℤ_p` vanishing modulo `p ^ r` is `p ^ r` times a symmetric matrix. -/
private theorem exists_pow_smul_eq_of_map_eq_zero {ι : Type*}
    {M : Matrix ι ι ℤ_[p]} (hM : Mᵀ = M) {r : ℕ} (h0 : M.map (PadicInt.toZModPow r) = 0) :
    ∃ H : Matrix ι ι ℤ_[p], Hᵀ = H ∧ (p : ℤ_[p]) ^ r • H = M := by
  choose H hH using fun i j =>
    (PadicInt.toZModPow_eq_zero_iff_dvd r (M i j)).mp (congrFun (congrFun h0 i) j)
  have hpH : (p : ℤ_[p]) ^ r • of H = M := by
    ext i j
    simp [hH]
  have hp : (p : ℤ_[p]) ^ r ≠ 0 :=
    pow_ne_zero r (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  refine ⟨of H, ?_, hpH⟩
  ext i j
  have h' : H j i = H i j := by
    apply mul_left_cancel₀ hp
    calc
      (p : ℤ_[p]) ^ r * H j i = M j i := by
        simpa using congrFun (congrFun hpH j) i
      _ = M i j := by simpa using congrFun (congrFun hM i) j
      _ = (p : ℤ_[p]) ^ r * H i j := by
        simpa using (congrFun (congrFun hpH i) j).symm
  simp only [transpose_apply, of_apply, h']

/-- A matrix `p ^ s N` over `ℤ_p` vanishes modulo `p ^ r` for `r ≤ s`. -/
private theorem map_pow_smul_eq_zero {ι κ : Type*} {r s : ℕ} (hrs : r ≤ s)
    (N : Matrix ι κ ℤ_[p]) :
    ((p : ℤ_[p]) ^ s • N).map (PadicInt.toZModPow r) = 0 := by
  ext i j
  exact (PadicInt.toZModPow_eq_zero_iff_dvd r _).mpr ((pow_dvd_pow _ hrs).mul_right _)

/-- `X` solves `Xᵀ A X = A` modulo `p ^ r` exactly when `A - Xᵀ A X` vanishes modulo `p ^ r`. -/
private theorem map_mem_isometryMatrices_map_iff {A X : Matrix n n ℤ_[p]} {r : ℕ} :
    X.map (PadicInt.toZModPow r) ∈ isometryMatrices (A.map (PadicInt.toZModPow r)) ↔
      (A - Xᵀ * A * X).map (PadicInt.toZModPow r) = 0 := by
  rw [mem_isometryMatrices, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
    Matrix.map_sub _ (map_sub _), sub_eq_zero, eq_comm]

/-- **One Newton step for `Xᵀ A X = A` over `ℤ_p`.** Let `A` be symmetric with `2 det A ∣ p ^ e`,
and let `Xᵀ A X ≡ A` modulo `p ^ (k + e)` with `k > e`. Then some `Y ≡ X` modulo `p ^ k` has
`Yᵀ A Y ≡ A` modulo `p ^ (k + e + 1)`. -/
private theorem exists_map_mem_isometryMatrices_succ {A X : Matrix n n ℤ_[p]} (hA : Aᵀ = A)
    {e k : ℕ} (he : 2 * A.det ∣ (p : ℤ_[p]) ^ e) (hek : e < k)
    (hX : X.map (PadicInt.toZModPow (k + e)) ∈
      isometryMatrices (A.map (PadicInt.toZModPow (k + e)))) :
    ∃ Y : Matrix n n ℤ_[p], Y.map (PadicInt.toZModPow (k + e + 1)) ∈
        isometryMatrices (A.map (PadicInt.toZModPow (k + e + 1))) ∧
      Y.map (PadicInt.toZModPow k) = X.map (PadicInt.toZModPow k) := by
  have hXu : IsUnit X.det :=
    isUnit_det_of_map_mem_isometryMatrices ((dvd_mul_left _ _).trans he) (by omega) hX
  -- the error `A - Xᵀ A X` is `p ^ (k + e)` times a symmetric matrix `H`
  obtain ⟨H, hHt, hH⟩ := exists_pow_smul_eq_of_map_eq_zero
    (by simp [hA, Matrix.mul_assoc])
    (map_mem_isometryMatrices_map_iff.mp hX)
  -- the correction `Z = c det(X)⁻¹ adj(Xᵀ A) H` has `tangentHom (Xᵀ A) Z = pᵉ H`
  obtain ⟨c, hc⟩ := he
  set Z := (c * ↑hXu.unit⁻¹) • (adjugate (Xᵀ * A) * H)
  have hZ : tangentHom (Xᵀ * A) Z = (p : ℤ_[p]) ^ e • H := by
    refine tangentHom_smul_adjugate_mul hHt ?_
    rw [det_mul, det_transpose]
    linear_combination hc - 2 * A.det * c * hXu.mul_val_inv
  have hXAX : Xᵀ * A * X = A - (p : ℤ_[p]) ^ (k + e) • H := by rw [hH, sub_sub_cancel]
  refine ⟨X + (p : ℤ_[p]) ^ k • Z, map_mem_isometryMatrices_map_iff.mpr ?_, ?_⟩
  · rw [transpose_add_smul_mul_mul_add_smul hA, hZ, hXAX]
    convert map_pow_smul_eq_zero (r := k + e + 1) (s := k + k) (by omega) (-(Zᵀ * A * Z)) using 2
    rw [pow_add, pow_add]
    module
  · rw [Matrix.map_add _ (map_add _), map_pow_smul_eq_zero le_rfl, add_zero]

/-- Truncating modulo `p ^ b` and then reducing modulo `p ^ a`, for `a ≤ b`, is truncating modulo
`p ^ a`. -/
private theorem map_castHom_map_toZModPow {ι κ : Type*} {a b : ℕ} (hab : a ≤ b)
    (h : p ^ a ∣ p ^ b) (M : Matrix ι κ ℤ_[p]) :
    (M.map (PadicInt.toZModPow b)).map (ZMod.castHom h (ZMod (p ^ a))) =
      M.map (PadicInt.toZModPow a) := by
  rw [Matrix.map_map, ← RingHom.coe_comp, PadicInt.zmod_cast_comp_toZModPow a b hab]

/-- **The images modulo `p ^ k` of the solutions at levels `k + e` and `k + e + 1` agree**, for
`A` symmetric with `2 det A ∣ p ^ e` and `k > e`. -/
private theorem map_castHom_isometryMatrices_succ {A : Matrix n n ℤ_[p]} (hA : Aᵀ = A)
    {e k : ℕ} (he : 2 * A.det ∣ (p : ℤ_[p]) ^ e) (hek : e < k) (h₁ : p ^ k ∣ p ^ (k + e + 1))
    (h₂ : p ^ k ∣ p ^ (k + e)) :
    (isometryMatrices (A.map (PadicInt.toZModPow (k + e + 1)))).map
        (ZMod.castHom h₁ (ZMod (p ^ k))).mapMatrix =
      (isometryMatrices (A.map (PadicInt.toZModPow (k + e)))).map
        (ZMod.castHom h₂ (ZMod (p ^ k))).mapMatrix := by
  ext W
  simp only [Submonoid.mem_map, RingHom.mapMatrix_apply]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    have h₃ : p ^ (k + e) ∣ p ^ (k + e + 1) := pow_dvd_pow p (k + e).le_succ
    refine ⟨Y.map (ZMod.castHom h₃ _), ?_, ?_⟩
    · have := map_mem_isometryMatrices_map (ZMod.castHom h₃ (ZMod (p ^ (k + e)))) hY
      rwa [map_castHom_map_toZModPow (k + e).le_succ] at this
    · rw [Matrix.map_map, ← RingHom.coe_comp, RingHom.ext_zmod
        ((ZMod.castHom h₂ _).comp (ZMod.castHom h₃ _)) (ZMod.castHom h₁ _)]
  · rintro ⟨X, hX, rfl⟩
    obtain ⟨X, rfl⟩ := map_surjective (ZMod.ringHom_surjective (PadicInt.toZModPow _)) X
    obtain ⟨Y, hY, hYX⟩ := exists_map_mem_isometryMatrices_succ hA he hek hX
    refine ⟨_, hY, ?_⟩
    rw [map_castHom_map_toZModPow (by omega), map_castHom_map_toZModPow (by omega), hYX]

/-- **The matrices modulo `l = m k` congruent to `1` modulo `k`** are the matrices `1 + k Z`,
with `Z` a matrix modulo `m`: this is the exactness of `ℤ/m → ℤ/l → ℤ/k`, entrywise. -/
private theorem map_castHom_eq_one_iff {ι : Type*} [DecidableEq ι] {m l k : ℕ} (h : m * k = l)
    (W : Matrix ι ι (ZMod l)) :
    W.map (ZMod.castHom (Dvd.intro_left m h) (ZMod k)) = 1 ↔
      ∃ Z, 1 + (ZMod.mulCastHom k h).mapMatrix Z = W := by
  set c := ZMod.castHom (Dvd.intro_left m h) (ZMod k)
  rw [← sub_eq_zero, ← Matrix.map_one c (map_zero c) (map_one c), ← Matrix.map_sub c (map_sub c)]
  simp only [← eq_sub_iff_add_eq']
  refine ⟨fun hW => ?_, ?_⟩
  · choose Z hZ using fun i j =>
      (ZMod.exact_mulCastHom_castHom k h _).mp (congrFun (congrFun hW i) j)
    exact ⟨of Z, ext hZ⟩
  · rintro ⟨Z, hZ⟩
    ext i j
    rw [← hZ]
    exact ZMod.castHom_mulCastHom k h (Z i j)

/-- Multiplication by `k`, from matrices modulo `m` to matrices modulo `l = m k`, commutes with
`tangentHom`, the matrix `B` modulo `l` acting through its reduction modulo `m`. -/
private theorem tangentHom_mapMatrix_mulCastHom {m l k : ℕ} (h : m * k = l)
    (B : Matrix n n (ZMod l)) (Z : Matrix n n (ZMod m)) :
    tangentHom B ((ZMod.mulCastHom k h).mapMatrix Z) = (ZMod.mulCastHom k h).mapMatrix
      (tangentHom (B.map (ZMod.castHom (Dvd.intro k h) (ZMod m))) Z) := by
  have hBZ : B * (ZMod.mulCastHom k h).mapMatrix Z =
      (ZMod.mulCastHom k h).mapMatrix (B.map (ZMod.castHom (Dvd.intro k h) (ZMod m)) * Z) := by
    ext i j
    simp only [mul_apply, AddMonoidHom.mapMatrix_apply, map_apply, map_sum,
      ZMod.mulCastHom_castHom_mul]
  rw [tangentHom_apply, tangentHom_apply, hBZ, map_add]
  simp only [AddMonoidHom.mapMatrix_apply, transpose_map]

/-- For symmetric `B` and `D` with entries in a square-zero ideal, `1 + D` preserves `B` exactly
when `D` is in the kernel of `tangentHom B`. -/
private theorem one_add_mem_isometryMatrices_iff {R : Type*} [CommRing R] {I : Ideal R}
    (hI : I ^ 2 = ⊥) {B D : Matrix n n R} (hB : Bᵀ = B) (hD : ∀ i j, D i j ∈ I) :
    1 + D ∈ isometryMatrices B ↔ D ∈ (tangentHom B).ker := by
  rw [mem_isometryMatrices,
    add_transpose_mul_mul_add_of_sq_eq_bot hI hB (isometryMatrices B).one_mem hD]
  simp [tangentHom_apply, add_assoc]

/-- **The solutions congruent to `1` modulo `p ^ k` at level `k + j`**, for `j ≤ k`, are the
matrices `1 + pᵏ Z` with `Z` modulo `p ^ j` in the kernel of `Z ↦ A Z + (A Z)ᵀ`. -/
private theorem natCard_setOf_mem_isometryMatrices_map_eq_one {A : Matrix n n ℤ_[p]}
    (hA : Aᵀ = A) {j k r : ℕ} (hjk : j ≤ k) (hr : k + j = r) (h : p ^ k ∣ p ^ r) :
    Nat.card {W ∈ isometryMatrices (A.map (PadicInt.toZModPow r)) |
        W.map (ZMod.castHom h (ZMod (p ^ k))) = 1} =
      Nat.card (tangentHom (A.map (PadicInt.toZModPow (p := p) j))).ker := by
  subst hr
  have hjkr : p ^ j * p ^ k = p ^ (k + j) := by rw [← pow_add, add_comm]
  -- the multiplication `μ` by `p ^ k`, from matrices modulo `p ^ j` to those modulo `p ^ (k + j)`
  set μ : Matrix n n (ZMod (p ^ j)) →+ Matrix n n (ZMod (p ^ (k + j))) :=
    (ZMod.mulCastHom (p ^ k) hjkr).mapMatrix
  have hμ : Function.Injective μ := Matrix.map_injective
    (ZMod.mulCastHom_injective _ hjkr (pow_ne_zero k (Fact.out : p.Prime).ne_zero))
  -- `1 + μ Z` is a solution exactly when `Z` is in the kernel at level `j`
  have hmem (Z : Matrix n n (ZMod (p ^ j))) :
      1 + μ Z ∈ isometryMatrices (A.map (PadicInt.toZModPow (k + j))) ↔
        Z ∈ (tangentHom (A.map (PadicInt.toZModPow j))).ker := by
    rw [one_add_mem_isometryMatrices_iff (B := A.map (PadicInt.toZModPow (k + j))) (D := μ Z)
      (ZMod.ker_castHom_sq_eq_bot (p ^ k) hjkr (pow_dvd_pow p hjk)) (by rw [← transpose_map, hA])
      fun i l => RingHom.mem_ker.mpr (ZMod.castHom_mulCastHom _ hjkr _)]
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, tangentHom_mapMatrix_mulCastHom,
      map_castHom_map_toZModPow (by omega), map_eq_zero_iff _ hμ]
  -- the matrices `≡ 1` modulo `p ^ k` are the `1 + μ Z`
  have hset : {W ∈ isometryMatrices (A.map (PadicInt.toZModPow (k + j))) |
      W.map (ZMod.castHom h (ZMod (p ^ k))) = 1} =
        (1 + μ ·) '' (tangentHom (A.map (PadicInt.toZModPow j))).ker := by
    ext W
    simp only [Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe, map_castHom_eq_one_iff hjkr]
    exact ⟨fun ⟨hW, Z, hZ⟩ => ⟨Z, (hmem Z).mp (hZ ▸ hW), hZ⟩,
      fun ⟨Z, hZ, hZW⟩ => ⟨hZW ▸ (hmem Z).mpr hZ, Z, hZW⟩⟩
  rw [hset]
  exact Nat.card_image_of_injective (fun Z Z' hZZ => hμ (add_left_cancel hZZ)) _

/-- **The image of `Z ↦ A Z + (A Z)ᵀ` modulo `p ^ (e + 1)` contains `pᵉ` times every symmetric
matrix**, when `2 det A ∣ p ^ e`: every symmetric `W` modulo `p ^ (e + 1)` that vanishes modulo
`p ^ e` is a value of this map. -/
private theorem exists_tangentHom_eq_of_map_castHom_eq_zero {A : Matrix n n ℤ_[p]} {e : ℕ}
    (he : 2 * A.det ∣ (p : ℤ_[p]) ^ e) (hdvd : p ^ e ∣ p ^ (e + 1))
    {W : Matrix n n (ZMod (p ^ (e + 1)))} (hW : W.map (ZMod.castHom hdvd (ZMod (p ^ e))) = 0)
    (hWsym : W.IsSymm) : ∃ Z, tangentHom (A.map (PadicInt.toZModPow (e + 1))) Z = W := by
  -- lift `W` entrywise to `pᵉ T` over `ℤ_p`; the entrywise lift keeps `W` symmetric
  have hτ := ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) (e + 1))
  obtain ⟨T, hT, hWT⟩ := exists_pow_smul_eq_of_map_eq_zero (M := W.map (Function.surjInv hτ))
    (by rw [← transpose_map, hWsym.eq])
    (by rw [← map_castHom_map_toZModPow e.le_succ hdvd, map_map_surjInv hτ, hW])
  -- with `pᵉ = 2 det A c`, the matrix `c adj(A) T` maps to `pᵉ T`
  obtain ⟨c, hc⟩ := he
  refine ⟨(c • (adjugate A * T)).map (PadicInt.toZModPow (e + 1)), ?_⟩
  rw [← map_tangentHom, tangentHom_smul_adjugate_mul hT hc, hWT, map_map_surjInv]

/-- For a homomorphism `ρ` and subgroups `R ≤ S` meeting `ker ρ` in the same subgroup, `|R| / |S|`
is the ratio of the sizes of their images, stated as an identity of `Nat.card`s. -/
private theorem natCard_mul_natCard_map_eq {M₁ M₀ : Type*} [AddGroup M₁] [AddGroup M₀]
    (ρ : M₁ →+ M₀) {R S : AddSubgroup M₁} (hRS : R ≤ S) (hker : ρ.ker ⊓ S ≤ R) :
    Nat.card R * Nat.card (S.map ρ) = Nat.card S * Nat.card (R.map ρ) := by
  have hmap (K : AddSubgroup M₁) : Nat.card K = Nat.card (K.map ρ) * Nat.card ↥(ρ.ker ⊓ K) := by
    rw [← AddSubgroup.relIndex_ker, AddSubgroup.relIndex_mul_card]
  have hinf : ρ.ker ⊓ R = ρ.ker ⊓ S :=
    le_antisymm (inf_le_inf_left _ hRS) (le_inf inf_le_left hker)
  rw [hmap R, hmap S, hinf]
  ring

/-- A surjective ring homomorphism `f` maps the image of `tangentHom B` onto that of
`tangentHom (B.map f)`. -/
private theorem map_range_tangentHom {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : Function.Surjective f) (B : Matrix n n R) :
    (tangentHom B).range.map f.toAddMonoidHom.mapMatrix = (tangentHom (B.map f)).range := by
  have hρ (X : Matrix n n R) : f.toAddMonoidHom.mapMatrix X = X.map f := by
    rw [AddMonoidHom.mapMatrix_apply, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_ofClass]
  have hcomp : f.toAddMonoidHom.mapMatrix.comp (tangentHom B) =
      (tangentHom (B.map f)).comp f.toAddMonoidHom.mapMatrix := by
    apply AddMonoidHom.ext
    intro Z
    change f.toAddMonoidHom.mapMatrix (tangentHom B Z) =
      tangentHom (B.map f) (f.toAddMonoidHom.mapMatrix Z)
    rw [hρ, hρ]
    exact map_tangentHom f B Z
  rw [AddMonoidHom.map_range, hcomp, AddMonoidHom.range_comp,
    AddMonoidHom.range_eq_top_of_surjective _ (map_surjective hf), ← AddMonoidHom.range_eq_map]

/-- **The image of `Z ↦ A Z + (A Z)ᵀ` grows by `p ^ ((n + 1).choose 2)` from level `e` to
`e + 1`**, when `2 det A ∣ p ^ e`: it consists of symmetric matrices and contains `pᵉ` times all
of them, so its index in the symmetric matrices is the same at both levels. -/
private theorem natCard_range_tangentHom_succ {A : Matrix n n ℤ_[p]} {e : ℕ}
    (he : 2 * A.det ∣ (p : ℤ_[p]) ^ e) :
    Nat.card (tangentHom (A.map (PadicInt.toZModPow (p := p) (e + 1)))).range =
      p ^ (Fintype.card n + 1).choose 2 *
        Nat.card (tangentHom (A.map (PadicInt.toZModPow (p := p) e))).range := by
  have hdvd : p ^ e ∣ p ^ (e + 1) := pow_dvd_pow p e.le_succ
  have hσ := ZMod.ringHom_surjective (ZMod.castHom hdvd (ZMod (p ^ e)))
  have hρ (X : Matrix n n (ZMod (p ^ (e + 1)))) :
      (ZMod.castHom hdvd (ZMod (p ^ e))).toAddMonoidHom.mapMatrix X =
        X.map (ZMod.castHom hdvd (ZMod (p ^ e))) := by
    rw [AddMonoidHom.mapMatrix_apply, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_ofClass]
  -- the symmetric matrices `S j` modulo `p ^ j`; membership in `eqLocus` is `Mᵀ = M` by
  -- definition, and Mathlib states no membership lemma for the additive `AddMonoidHom.eqLocus`
  let S (j : ℕ) : AddSubgroup (Matrix n n (ZMod (p ^ j))) :=
    (transposeAddEquiv n n (ZMod (p ^ j))).toAddMonoidHom.eqLocus (AddMonoidHom.id _)
  have hS (j : ℕ) (M : Matrix n n (ZMod (p ^ j))) : M ∈ S j ↔ M.IsSymm := Iff.rfl
  have hcardS (j : ℕ) : Nat.card (S j) = (p ^ j) ^ (Fintype.card n + 1).choose 2 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight (hS j)), natCard_isSymm n _, Nat.card_zmod]
  -- the reduction maps `S (e + 1)` onto `S e`, since entrywise lifts keep a matrix symmetric
  have hsym : (S (e + 1)).map (ZMod.castHom hdvd (ZMod (p ^ e))).toAddMonoidHom.mapMatrix =
      S e := by
    ext M
    simp only [AddSubgroup.mem_map]
    constructor
    · rintro ⟨N, hN, hNM⟩
      rw [hρ N] at hNM
      exact (hS _ M).mpr (hNM ▸ ((hS _ N).mp hN).map _)
    · intro hM
      refine ⟨M.map (Function.surjInv hσ), (hS _ _).mpr (((hS _ M).mp hM).map _), ?_⟩
      rw [hρ]
      exact map_map_surjInv hσ M
  have h := natCard_mul_natCard_map_eq (ZMod.castHom hdvd (ZMod (p ^ e))).toAddMonoidHom.mapMatrix
    (R := (tangentHom (A.map (PadicInt.toZModPow (e + 1)))).range) (S := S (e + 1))
    (by rintro _ ⟨Z, rfl⟩; exact (hS _ _).mpr (isSymm_add_transpose_self (_ * Z)))
    fun W hW => exists_tangentHom_eq_of_map_castHom_eq_zero he hdvd
      (by simpa only [hρ] using AddMonoidHom.mem_ker.mp hW.1) ((hS _ W).mp hW.2)
  rw [hsym, map_range_tangentHom hσ, map_castHom_map_toZModPow e.le_succ, hcardS, hcardS] at h
  refine Nat.eq_of_mul_eq_mul_right
    (pow_pos (pow_pos (Fact.out : p.Prime).pos e) ((Fintype.card n + 1).choose 2)) ?_
  rw [h]
  ring

/-- **The kernel of `Z ↦ A Z + (A Z)ᵀ` grows by `p ^ (n.choose 2)` from level `e` to `e + 1`**,
when `2 det A ∣ p ^ e`. -/
private theorem natCard_ker_tangentHom_succ {A : Matrix n n ℤ_[p]} {e : ℕ}
    (he : 2 * A.det ∣ (p : ℤ_[p]) ^ e) :
    Nat.card (tangentHom (A.map (PadicInt.toZModPow (p := p) (e + 1)))).ker =
      p ^ (Fintype.card n).choose 2 *
        Nat.card (tangentHom (A.map (PadicInt.toZModPow (p := p) e))).ker := by
  set c := Fintype.card n
  have hM (j : ℕ) : Nat.card (Matrix n n (ZMod (p ^ j))) = (p ^ j) ^ (c * c) := by
    rw [card_matrix, Nat.card_zmod, Nat.card_eq_fintype_card]
  -- `c² = (c + 1).choose 2 + c.choose 2`, the sizes of the symmetric and the alternating parts
  have hc2 : c * c = (c + 1).choose 2 + c.choose 2 := by
    rw [← Nat.choose_two_add_mul_succ_div_two, Nat.choose_two_right (c + 1), Nat.add_sub_cancel,
      Nat.mul_comm (c + 1), Nat.add_comm]
  have h₁ := AddSubgroup.card_ker_mul_card_range (tangentHom (A.map (PadicInt.toZModPow (e + 1))))
  have h₀ := AddSubgroup.card_ker_mul_card_range (tangentHom (A.map (PadicInt.toZModPow e)))
  rw [natCard_range_tangentHom_succ he, hM, hc2] at h₁
  rw [hM, hc2] at h₀
  refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (pow_pos (Fact.out : p.Prime).pos
    ((c + 1).choose 2)) (Nat.card_pos (α := (tangentHom (A.map (PadicInt.toZModPow e))).range))) ?_
  rw [h₁, pow_succ', mul_pow, ← h₀]
  ring

/-- **The local density count stabilizes at every prime.** Let `A` be a symmetric matrix over
`ℤ_p` and let `2 det A` divide `p ^ e`. Then for every `r > 2 e` the count at level `r + 1` is
`p ^ (n.choose 2)` times the count at level `r`. -/
theorem localDensityCount_succ_of_dvd {A : Matrix n n ℤ_[p]} (hA : Aᵀ = A) {e : ℕ}
    (he : 2 * A.det ∣ (p : ℤ_[p]) ^ e) {r : ℕ} (hr : 2 * e < r) :
    A.localDensityCount (r + 1) = p ^ (Fintype.card n).choose 2 * A.localDensityCount r := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + e := ⟨r - e, by omega⟩
  have hek : e < k := by omega
  have hunit (r' : ℕ) (hr' : e < r') :
      ∀ X ∈ isometryMatrices (A.map (PadicInt.toZModPow r')), IsUnit X.det := by
    intro X hX
    obtain ⟨X, rfl⟩ := map_surjective (ZMod.ringHom_surjective (PadicInt.toZModPow _)) X
    dsimp only at hX ⊢
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_det_of_map_mem_isometryMatrices ((dvd_mul_left _ _).trans he) hr' hX).map _
  have h₁ : p ^ k ∣ p ^ (k + e + 1) := pow_dvd_pow p (by omega)
  have h₂ : p ^ k ∣ p ^ (k + e) := pow_dvd_pow p (by omega)
  rw [localDensityCount_def, localDensityCount_def,
    natCard_isometryMatrices_eq_mul (ZMod.castHom h₁ (ZMod (p ^ k))) (hunit _ (by omega)),
    natCard_isometryMatrices_eq_mul (ZMod.castHom h₂ (ZMod (p ^ k))) (hunit _ (by omega)),
    map_castHom_isometryMatrices_succ hA he hek h₁ h₂,
    natCard_setOf_mem_isometryMatrices_map_eq_one hA (j := e + 1) (by omega) (by omega) h₁,
    natCard_setOf_mem_isometryMatrices_map_eq_one hA (j := e) hek.le rfl h₂,
    natCard_ker_tangentHom_succ he]
  ring

/-- At a level `r > 2 e` the normalized local density count does not change at the next level. -/
private theorem localDensityCount_div_pow_succ_of_dvd {A : Matrix n n ℤ_[p]} (hA : Aᵀ = A)
    {e : ℕ} (he : 2 * A.det ∣ (p : ℤ_[p]) ^ e) {r : ℕ} (hr : 2 * e < r) :
    (A.localDensityCount (r + 1) : ℚ) / (p : ℚ) ^ ((r + 1) * (Fintype.card n).choose 2) =
      A.localDensityCount r / (p : ℚ) ^ (r * (Fintype.card n).choose 2) := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [localDensityCount_succ_of_dvd hA he hr, Nat.cast_mul, Nat.cast_pow,
    div_eq_div_iff (pow_ne_zero _ hp0) (pow_ne_zero _ hp0), add_one_mul, pow_add]
  ring

/-- **The local density** `α_p(A)` of a Gram matrix `A` over `ℤ_p`: the limit as `r → ∞` of the
normalized counts `#{X ∈ Mₙ(ℤ/pʳ) : Xᵀ A X = A} / p ^ (r * n.choose 2)`. For symmetric `A` with
nonzero determinant the normalized counts are constant from `r = 2 v_p(2 det A) + 1` on
(`Matrix.localDensityCount_div_pow_of_det_ne_zero`), so the limit exists; for other `A` this is
a junk value. -/
noncomputable def localDensity (A : Matrix n n ℤ_[p]) : ℚ :=
  limUnder atTop fun r => (A.localDensityCount r : ℚ) / (p : ℚ) ^ (r * (Fintype.card n).choose 2)

/-- **The local density does not depend on the basis**: replacing the Gram matrix `A` by `Pᵀ A P`
for an invertible `P` over `ℤ_p` leaves it unchanged. -/
theorem localDensity_transpose_mul_mul {A P : Matrix n n ℤ_[p]} (hP : IsUnit P.det) :
    (Pᵀ * A * P).localDensity = A.localDensity := by
  simp only [localDensity, localDensityCount_transpose_mul_mul hP]

/-- **The normalized local density count is the local density from level `2 e + 1` on.** If `A`
is symmetric and `2 det A ∣ p ^ e`, then for every `r > 2 e` the normalized count
`#{X ∈ Mₙ(ℤ/pʳ) : Xᵀ A X = A} / p ^ (r * n.choose 2)` equals `α_p(A)`. -/
theorem localDensityCount_div_pow_of_dvd {A : Matrix n n ℤ_[p]} (hA : Aᵀ = A) {e : ℕ}
    (he : 2 * A.det ∣ (p : ℤ_[p]) ^ e) {r : ℕ} (hr : 2 * e < r) :
    (A.localDensityCount r : ℚ) / (p : ℚ) ^ (r * (Fintype.card n).choose 2) = A.localDensity := by
  set f : ℕ → ℚ := fun s => (A.localDensityCount s : ℚ) / (p : ℚ) ^ (s * (Fintype.card n).choose 2)
  have hconst (s : ℕ) (hs : 2 * e + 1 ≤ s) : f s = f (2 * e + 1) := by
    induction s, hs using Nat.le_induction with
    | base => rfl
    | succ s hs ih => exact (localDensityCount_div_pow_succ_of_dvd hA he hs).trans ih
  have ht : Tendsto f atTop (𝓝 (f (2 * e + 1))) :=
    tendsto_const_nhds.congr' ((eventually_ge_atTop _).mono fun s hs => (hconst s hs).symm)
  rw [localDensity, ht.limUnder_eq]
  exact hconst r hr

/-- **The local density count stabilizes from `r₀ = 2 v_p(2 det A) + 1` on.** If `A` is symmetric
with nonzero determinant, then for every `r > 2 v_p(2 det A)` the normalized count
`#{X ∈ Mₙ(ℤ/pʳ) : Xᵀ A X = A} / p ^ (r * n.choose 2)` equals `α_p(A)`. -/
theorem localDensityCount_div_pow_of_det_ne_zero {A : Matrix n n ℤ_[p]} (hA : Aᵀ = A)
    (hdet : A.det ≠ 0) {r : ℕ} (hr : 2 * (2 * A.det).valuation < r) :
    (A.localDensityCount r : ℚ) / (p : ℚ) ^ (r * (Fintype.card n).choose 2) = A.localDensity :=
  localDensityCount_div_pow_of_dvd hA (PadicInt.dvd_pow_valuation (mul_ne_zero two_ne_zero hdet)) hr

/-- **The local density exists**: for symmetric `A` with nonzero determinant, the normalized count
`#{X ∈ Mₙ(ℤ/pʳ) : Xᵀ A X = A} / p ^ (r * n.choose 2)` converges to `α_p(A)`. -/
theorem tendsto_localDensityCount_div_of_det_ne_zero {A : Matrix n n ℤ_[p]} (hA : Aᵀ = A)
    (hdet : A.det ≠ 0) :
    Tendsto (fun r => (A.localDensityCount r : ℚ) / (p : ℚ) ^ (r * (Fintype.card n).choose 2))
      atTop (𝓝 A.localDensity) :=
  tendsto_const_nhds.congr' <| (eventually_gt_atTop _).mono fun _ hr =>
    (localDensityCount_div_pow_of_det_ne_zero hA hdet hr).symm

/-- **The local density is positive** for symmetric `A` with nonzero determinant. -/
theorem localDensity_pos {A : Matrix n n ℤ_[p]} (hA : Aᵀ = A) (hdet : A.det ≠ 0) :
    0 < A.localDensity := by
  rw [← localDensityCount_div_pow_of_det_ne_zero hA hdet (Nat.lt_succ_self _)]
  exact div_pos (Nat.cast_pos.mpr (localDensityCount_pos A _))
    (pow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) _)

/-! ### Primes not dividing `2 det A` -/

/-- **The local density count at a prime not dividing `2 det A` grows by `p ^ (n.choose 2)` at
each level `r ≥ 1`.** -/
theorem localDensityCount_succ_of_isUnit_det (hp : p ≠ 2) {A : Matrix n n ℤ_[p]} (hA : Aᵀ = A)
    (hdet : IsUnit A.det) {r : ℕ} (hr : r ≠ 0) :
    A.localDensityCount (r + 1) = p ^ (Fintype.card n).choose 2 * A.localDensityCount r :=
  localDensityCount_succ_of_dvd hA (e := 0)
    (by rw [pow_zero]; exact ((PadicInt.isUnit_two hp).mul hdet).dvd) (Nat.pos_of_ne_zero hr)

/-- At a prime not dividing `2 det A`, the local density count at level `r + 1` is
`p ^ (r * n.choose 2)` times the count at level `1`. -/
theorem localDensityCount_succ_eq_pow_mul_one (hp : p ≠ 2) {A : Matrix n n ℤ_[p]}
    (hA : Aᵀ = A) (hdet : IsUnit A.det) (r : ℕ) :
    A.localDensityCount (r + 1) =
      p ^ (r * (Fintype.card n).choose 2) * A.localDensityCount 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [localDensityCount_succ_of_isUnit_det hp hA hdet r.succ_ne_zero, ih, ← mul_assoc,
      ← pow_add, add_one_mul, add_comm]

/-- **The local density at a prime not dividing `2 det A`.** The normalized count
`#{X ∈ Mₙ(ℤ/pʳ) : Xᵀ A X = A} / p ^ (r * n.choose 2)` takes the same value for every `r ≥ 1`,
namely the count at level `1` divided by `p ^ (n.choose 2)`. -/
theorem localDensityCount_div_pow_of_isUnit_det (hp : p ≠ 2) {A : Matrix n n ℤ_[p]}
    (hA : Aᵀ = A) (hdet : IsUnit A.det) {r : ℕ} (hr : r ≠ 0) :
    (A.localDensityCount r : ℚ) / (p : ℚ) ^ (r * (Fintype.card n).choose 2) =
      A.localDensityCount 1 / (p : ℚ) ^ (Fintype.card n).choose 2 := by
  have he : 2 * A.det ∣ (p : ℤ_[p]) ^ 0 := by
    rw [pow_zero]; exact ((PadicInt.isUnit_two hp).mul hdet).dvd
  simpa using (localDensityCount_div_pow_of_dvd hA he (Nat.pos_of_ne_zero hr)).trans
    (localDensityCount_div_pow_of_dvd hA he one_pos).symm

/-- **The local density exists at a prime not dividing `2 det A`**: the normalized count
converges, to the count at level `1` divided by `p ^ (n.choose 2)`, i.e. to
`#O(A mod p) / p^{n (n - 1) / 2}`. -/
theorem tendsto_localDensityCount_div_of_isUnit_det (hp : p ≠ 2) {A : Matrix n n ℤ_[p]}
    (hA : Aᵀ = A) (hdet : IsUnit A.det) :
    Tendsto (fun r => (A.localDensityCount r : ℚ) / (p : ℚ) ^ (r * (Fintype.card n).choose 2))
      atTop (𝓝 (A.localDensityCount 1 / (p : ℚ) ^ (Fintype.card n).choose 2)) :=
  tendsto_const_nhds.congr' <| (eventually_ne_atTop 0).mono fun _ hr =>
    (localDensityCount_div_pow_of_isUnit_det hp hA hdet hr).symm

/-- **The local density at a prime not dividing `2 det A`** is the count at level `1` divided by
`p ^ (n.choose 2)`, i.e. `#O(A mod p) / p^{n (n - 1) / 2}`. -/
theorem localDensity_eq_of_isUnit_det (hp : p ≠ 2) {A : Matrix n n ℤ_[p]} (hA : Aᵀ = A)
    (hdet : IsUnit A.det) :
    A.localDensity = A.localDensityCount 1 / (p : ℚ) ^ (Fintype.card n).choose 2 :=
  tendsto_nhds_unique (tendsto_localDensityCount_div_of_det_ne_zero hA hdet.ne_zero)
    (tendsto_localDensityCount_div_of_isUnit_det hp hA hdet)

/-- **The local density count at level `1` is a count over `𝔽_p`**: it is the number of
`X ∈ Mₙ(𝔽_p)` with `Xᵀ Ā X = Ā`, for `Ā` the reduction of `A` modulo `p`. When `Ā` is symmetric
and nondegenerate, this is the order of the orthogonal group of `Ā`. -/
theorem localDensityCount_one (A : Matrix n n ℤ_[p]) :
    A.localDensityCount 1 = Nat.card (isometryMatrices (A.map PadicInt.toZMod)) := by
  set e := ZMod.ringEquivCongr (pow_one p)
  have he : (e : ZMod (p ^ 1) →+* ZMod p) = ZMod.castHom (dvd_pow_self p one_ne_zero) _ :=
    RingHom.ext_zmod _ _
  have hfun : ⇑e ∘ ⇑(PadicInt.toZModPow 1) = ⇑PadicInt.toZMod :=
    funext fun x => by simp [← RingEquiv.coe_toRingHom, he]
  rw [localDensityCount_def, ← natCard_isometryMatrices_map_ringEquiv e, Matrix.map_map, hfun]

/-- An integer matrix has unit determinant over `ℤ_p` exactly when `p` does not divide its
determinant. -/
theorem isUnit_det_map_padicInt_iff {A : Matrix n n ℤ} :
    IsUnit (A.map (Int.castRingHom ℤ_[p])).det ↔ ¬ (p : ℤ) ∣ A.det := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast,
    ← PadicInt.norm_int_lt_one_iff_dvd, ← PadicInt.mem_nonunits, mem_nonunits_iff, not_not]

/-- The reduction modulo an odd prime `p` of a symmetric matrix with unit determinant over `ℤ_p`
is a nondegenerate symmetric matrix over a field of characteristic different from two. -/
private theorem isSymm_map_toZMod (hp : p ≠ 2) {A : Matrix n n ℤ_[p]} (hA : Aᵀ = A)
    (hdet : IsUnit A.det) :
    (A.map PadicInt.toZMod).IsSymm ∧ (A.map PadicInt.toZMod).det ≠ 0 ∧ ringChar (ZMod p) ≠ 2 := by
  refine ⟨IsSymm.map hA _, ?_, by rwa [ZMod.ringChar_zmod_n]⟩
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (hdet.map _).ne_zero

/-- **The local density at a prime not dividing `2 det A`, in odd rank.** If `p` is odd and `A` is
a symmetric `(2m + 1) × (2m + 1)` matrix over `ℤ_p` with unit determinant, the normalized count
`#{X ∈ Mₙ(ℤ/pʳ) : Xᵀ A X = A} / p ^ (r * n.choose 2)` converges to `2 ∏_{i=1}^{m} (1 - p^{-2i})`. -/
theorem tendsto_localDensityCount_div_of_card_eq_two_mul_add_one (hp : p ≠ 2)
    {A : Matrix n n ℤ_[p]} (hA : Aᵀ = A) (hdet : IsUnit A.det) {m : ℕ}
    (hn : Fintype.card n = 2 * m + 1) :
    Tendsto (fun r => (A.localDensityCount r : ℚ) / (p : ℚ) ^ (r * (Fintype.card n).choose 2))
      atTop (𝓝 (2 * ∏ i ∈ Finset.range m, (1 - ((p : ℚ) ^ (2 * (i + 1)))⁻¹))) := by
  convert tendsto_localDensityCount_div_of_isUnit_det hp hA hdet using 2
  obtain ⟨hsymm, hdet', hchar⟩ := isSymm_map_toZMod hp hA hdet
  have h := hsymm.natCard_isometryMatrices_eq_of_card_eq_two_mul_add_one hchar hdet' hn
  rw [ZMod.card] at h
  have hchoose : (Fintype.card n).choose 2 = m ^ 2 + m * (m + 1) := by
    rw [hn, Nat.choose_two_right, Nat.add_sub_cancel,
      show (2 * m + 1) * (2 * m) = (m ^ 2 + m * (m + 1)) * 2 by ring, Nat.mul_div_cancel _ two_pos]
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have h' := congrArg (Int.cast : ℤ → ℚ) h
  push_cast at h'
  rw [localDensityCount_one, h', hchoose, Finset.prod_pow_sub_one hp0,
    Finset.sum_range_two_mul_succ]
  field_simp
  ring

/-- **The local density at a prime not dividing `2 det A`, in even rank.** If `p` is odd and `A`
is a symmetric `(2m + 2) × (2m + 2)` matrix over `ℤ_p` with unit determinant, the normalized count
`#{X ∈ Mₙ(ℤ/pʳ) : Xᵀ A X = A} / p ^ (r * n.choose 2)` converges to
`2 (1 - ε p^{-(m+1)}) ∏_{i=1}^{m} (1 - p^{-2i})`, where `ε = ((-1)^{m+1} det A | p)` is the
quadratic character of the signed determinant modulo `p`: it is `+1` exactly when the reduction of
`A` is split. -/
theorem tendsto_localDensityCount_div_of_card_eq_two_mul_add_two (hp : p ≠ 2)
    {A : Matrix n n ℤ_[p]} (hA : Aᵀ = A) (hdet : IsUnit A.det) {m : ℕ}
    (hn : Fintype.card n = 2 * m + 2) :
    Tendsto (fun r => (A.localDensityCount r : ℚ) / (p : ℚ) ^ (r * (Fintype.card n).choose 2))
      atTop (𝓝 (2 * (1 - quadraticChar (ZMod p) ((-1) ^ (m + 1) * (A.map PadicInt.toZMod).det) *
        ((p : ℚ) ^ (m + 1))⁻¹) * ∏ i ∈ Finset.range m, (1 - ((p : ℚ) ^ (2 * (i + 1)))⁻¹))) := by
  convert tendsto_localDensityCount_div_of_isUnit_det hp hA hdet using 2
  obtain ⟨hsymm, hdet', hchar⟩ := isSymm_map_toZMod hp hA hdet
  have h := hsymm.natCard_isometryMatrices_eq_of_card_eq_two_mul_add_two hchar hdet' hn
  rw [ZMod.card] at h
  have hchoose : (Fintype.card n).choose 2 = 2 * (m * (m + 1)) + (m + 1) := by
    rw [hn, Nat.choose_two_right, show 2 * m + 2 - 1 = 2 * m + 1 by omega,
      show (2 * m + 2) * (2 * m + 1) = (2 * (m * (m + 1)) + (m + 1)) * 2 by ring,
      Nat.mul_div_cancel _ two_pos]
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have h' := congrArg (Int.cast : ℤ → ℚ) h
  push_cast at h'
  rw [localDensityCount_one, h', hchoose, Finset.prod_pow_sub_one hp0,
    Finset.sum_range_two_mul_succ]
  field_simp
  ring

/-- **The hyperbolic plane at `p = 3` has local density `4/3`.** Its Gram matrix `!![0, 1; 1, 0]`
has determinant `-1`, a nonsquare modulo `3`, yet the plane is split: the sign in the even-rank
density is the character of the signed determinant `(-1)^1 · (-1) = 1`, not of the determinant. -/
theorem tendsto_localDensityCount_div_hyperbolicPlane_three :
    Tendsto (fun r => ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[3]).localDensityCount r : ℚ) /
      (3 : ℚ) ^ (r * (Fintype.card (Fin 2)).choose 2)) atTop (𝓝 (4 / 3)) := by
  have hA : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[3])ᵀ = !![0, 1; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hdet : IsUnit (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[3]).det := by
    simp [det_fin_two]
  convert tendsto_localDensityCount_div_of_card_eq_two_mul_add_two (by norm_num) hA hdet
    (m := 0) (by simp) using 2
  simp [det_fin_two]
  norm_num

end Matrix
