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
import TauCeti.Algebra.BigOperators.Field
import TauCeti.Algebra.BigOperators.Finset.Range
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
positive rational number. The argument has three steps, with `k = r - e > e`:

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

* `Matrix.localDensityCount_transpose_mul_mul`: the count is unchanged by a change of basis
  `A ↦ Pᵀ A P`, so it only depends on the isometry class of the lattice.
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
    0 < A.localDensityCount r := by
  have : NeZero (p ^ r) := ⟨pow_ne_zero r (Fact.out : p.Prime).ne_zero⟩
  have : Nonempty (isometryMatrices (A.map (PadicInt.toZModPow r))) :=
    ⟨⟨1, (isometryMatrices _).one_mem⟩⟩
  exact Nat.card_pos

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

/-- A `p`-adic integer `d` with `p ∣ 1 - d ^ 2` is a unit. -/
private theorem isUnit_of_dvd_one_sub_sq {d : ℤ_[p]} (h : (p : ℤ_[p]) ∣ 1 - d ^ 2) :
    IsUnit d := by
  by_contra hd
  have hpd : (p : ℤ_[p]) ∣ d :=
    (PadicInt.norm_lt_one_iff_dvd d).mp (PadicInt.mem_nonunits.mp hd)
  have h1 : (p : ℤ_[p]) ∣ 1 := by
    simpa using h.add (dvd_pow hpd two_ne_zero)
  exact PadicInt.irreducible_p.not_isUnit (isUnit_of_dvd_one h1)

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
  refine isUnit_of_dvd_one_sub_sq ⟨s * p ^ m * t, mul_left_cancel₀ hA0 ?_⟩
  calc A.det * (1 - X.det ^ 2) = (p : ℤ_[p]) ^ (e + m + 1) * t := by rw [← ht]; ring
    _ = A.det * (p * (s * p ^ m * t)) := by rw [pow_add, pow_add, hs]; ring

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
  rw [mem_isometryMatrices, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul] at hX
  -- the error `A - Xᵀ A X` is `p ^ (k + e)` times a symmetric matrix `H`
  have hdiv (i j : n) : (p : ℤ_[p]) ^ (k + e) ∣ (A - Xᵀ * A * X) i j := by
    simpa [sub_apply] using (PadicInt.toZModPow_eq_iff_dvd_sub _).mp (congrFun (congrFun hX i) j)
  choose H hH using hdiv
  have hEH : A - Xᵀ * A * X = (p : ℤ_[p]) ^ (k + e) • of H := by
    ext i j
    simp [hH]
  have hp0 : ((p : ℤ_[p]) ^ (k + e)) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hHt : (of H)ᵀ = of H := by
    refine smul_right_injective _ hp0 ?_
    simp only [← transpose_smul, ← hEH, transpose_sub, transpose_mul, transpose_transpose, hA,
      Matrix.mul_assoc]
  -- the correction `Z`, with `C Z = c det A • H` for `C = Xᵀ A`
  obtain ⟨c, hc⟩ := he
  set C := Xᵀ * A with hC
  set Z : Matrix n n ℤ_[p] := (c * ↑hXu.unit⁻¹) • (adjugate C * of H) with hZ
  have hCZ : C * Z = (c * A.det) • of H := by
    rw [hZ, mul_smul_comm, ← Matrix.mul_assoc, mul_adjugate, hC, det_mul, det_transpose,
      smul_mul_assoc, Matrix.one_mul, smul_smul]
    congr 1
    calc c * ↑hXu.unit⁻¹ * (X.det * A.det) = c * A.det * (X.det * ↑hXu.unit⁻¹) := by ring
      _ = c * A.det := by rw [hXu.mul_val_inv, mul_one]
  have hZt : Zᵀ * A * X = (C * Z)ᵀ := by
    rw [hC, transpose_mul, transpose_mul, transpose_transpose, hA, Matrix.mul_assoc]
  refine ⟨X + (p : ℤ_[p]) ^ k • Z, ?_, ?_⟩
  · have hexp : (X + (p : ℤ_[p]) ^ k • Z)ᵀ * A * (X + (p : ℤ_[p]) ^ k • Z) =
        A + ((p : ℤ_[p]) ^ k * (p : ℤ_[p]) ^ k) • (Zᵀ * A * Z) := by
      have h2 : C * Z + (C * Z)ᵀ = (p : ℤ_[p]) ^ e • of H := by
        rw [hCZ, transpose_smul, hHt, ← add_smul, hc]
        congr 1
        ring
      calc (X + (p : ℤ_[p]) ^ k • Z)ᵀ * A * (X + (p : ℤ_[p]) ^ k • Z)
          = Xᵀ * A * X + (p : ℤ_[p]) ^ k • (C * Z + Zᵀ * A * X) +
              ((p : ℤ_[p]) ^ k * (p : ℤ_[p]) ^ k) • (Zᵀ * A * Z) := by
            simp only [hC, transpose_add, transpose_smul, Matrix.add_mul, Matrix.mul_add,
              Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, Matrix.mul_assoc]
            abel
        _ = A + ((p : ℤ_[p]) ^ k * (p : ℤ_[p]) ^ k) • (Zᵀ * A * Z) := by
            rw [hZt, h2, smul_smul, ← pow_add, ← hEH, ← hC, add_sub_cancel]
    rw [mem_isometryMatrices, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hexp]
    ext i j
    simp only [map_apply, add_apply, smul_apply, smul_eq_mul]
    rw [PadicInt.toZModPow_eq_iff_dvd_sub, sub_add_cancel_left, dvd_neg, ← pow_add]
    exact (pow_dvd_pow _ (by omega)).mul_right _
  · ext i j
    simp only [map_apply, add_apply, smul_apply, smul_eq_mul]
    rw [PadicInt.toZModPow_eq_iff_dvd_sub]
    exact ⟨-Z i j, by ring⟩

/-- Every matrix over `ℤ/pʳ` is the reduction of a matrix over `ℤ_p`. -/
private theorem exists_map_toZModPow_eq {m l : Type*} {r : ℕ} (X : Matrix m l (ZMod (p ^ r))) :
    ∃ X' : Matrix m l ℤ_[p], X'.map (PadicInt.toZModPow r) = X :=
  ⟨X.map (Function.surjInv (ZMod.ringHom_surjective (PadicInt.toZModPow r))), by
    ext i j
    exact Function.surjInv_eq (ZMod.ringHom_surjective (PadicInt.toZModPow r)) (X i j)⟩

/-- **The images modulo `p ^ k` of the solutions at levels `k + e` and `k + e + 1` agree**, for
`A` symmetric with `2 det A ∣ p ^ e` and `k > e`. -/
private theorem map_castHom_isometryMatrices_succ {A : Matrix n n ℤ_[p]} (hA : Aᵀ = A)
    {e k : ℕ} (he : 2 * A.det ∣ (p : ℤ_[p]) ^ e) (hek : e < k) (h₁ : p ^ k ∣ p ^ (k + e + 1))
    (h₂ : p ^ k ∣ p ^ (k + e)) :
    (isometryMatrices (A.map (PadicInt.toZModPow (k + e + 1)))).map
        (ZMod.castHom h₁ (ZMod (p ^ k))).mapMatrix =
      (isometryMatrices (A.map (PadicInt.toZModPow (k + e)))).map
        (ZMod.castHom h₂ (ZMod (p ^ k))).mapMatrix := by
  have hcomp (a b : ℕ) (hab : a ≤ b) (h : p ^ a ∣ p ^ b) :
      (ZMod.castHom h (ZMod (p ^ a))).comp (PadicInt.toZModPow b) = PadicInt.toZModPow a :=
    PadicInt.zmod_cast_comp_toZModPow a b hab
  ext W
  simp only [Submonoid.mem_map, RingHom.mapMatrix_apply]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    have h₃ : p ^ (k + e) ∣ p ^ (k + e + 1) := pow_dvd_pow p (k + e).le_succ
    refine ⟨Y.map (ZMod.castHom h₃ _), ?_, ?_⟩
    · have := map_mem_isometryMatrices_map (ZMod.castHom h₃ (ZMod (p ^ (k + e)))) hY
      rwa [Matrix.map_map, ← RingHom.coe_comp, hcomp _ _ (k + e).le_succ] at this
    · rw [Matrix.map_map, ← RingHom.coe_comp, RingHom.ext_zmod
        ((ZMod.castHom h₂ _).comp (ZMod.castHom h₃ _)) (ZMod.castHom h₁ _)]
  · rintro ⟨X, hX, rfl⟩
    obtain ⟨X, rfl⟩ := exists_map_toZModPow_eq X
    obtain ⟨Y, hY, hYX⟩ := exists_map_mem_isometryMatrices_succ hA he hek hX
    refine ⟨_, hY, ?_⟩
    rw [Matrix.map_map, Matrix.map_map, ← RingHom.coe_comp, ← RingHom.coe_comp,
      hcomp _ _ (by omega), hcomp _ _ (by omega), hYX]

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

/-- **The solutions congruent to `1` modulo `p ^ k` at level `k + j`**, for `j ≤ k`, are the
matrices `1 + pᵏ Z` with `Z` modulo `p ^ j` in the kernel of `Z ↦ A Z + (A Z)ᵀ`. -/
private theorem natCard_setOf_mem_isometryMatrices_map_eq_one {A : Matrix n n ℤ_[p]}
    (hA : Aᵀ = A) {j k r : ℕ} (hjk : j ≤ k) (hr : k + j = r) (h : p ^ k ∣ p ^ r) :
    Nat.card {W ∈ isometryMatrices (A.map (PadicInt.toZModPow r)) |
        W.map (ZMod.castHom h (ZMod (p ^ k))) = 1} =
      Nat.card (tangentHom (A.map (PadicInt.toZModPow (p := p) j))).ker := by
  subst hr
  have hjkr : p ^ j * p ^ k = p ^ (k + j) := by rw [← pow_add, add_comm]
  have hp : p ^ k ≠ 0 := pow_ne_zero k (Fact.out : p.Prime).ne_zero
  set μ := ZMod.mulCastHom (p ^ k) hjkr
  set A' := A.map (PadicInt.toZModPow (p := p) (k + j)) with hA'
  have hμinj : Function.Injective (μ.mapMatrix : Matrix n n _ →+ Matrix n n _) :=
    Matrix.map_injective (ZMod.mulCastHom_injective _ hjkr hp)
  -- multiplying by `A` commutes with `μ`
  have hAμ (Z : Matrix n n (ZMod (p ^ j))) :
      A' * μ.mapMatrix Z = μ.mapMatrix (A.map (PadicInt.toZModPow j) * Z) := by
    ext i l
    simp only [mul_apply, AddMonoidHom.mapMatrix_apply, map_apply, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← PadicInt.zmod_cast_comp_toZModPow j (k + j) (by omega), RingHom.comp_apply,
      ZMod.mulCastHom_castHom_mul, hA', map_apply]
  have hker := ZMod.ker_castHom_sq_eq_bot (p ^ k) hjkr (pow_dvd_pow p hjk)
  have hmem (Z : Matrix n n (ZMod (p ^ j))) :
      1 + μ.mapMatrix Z ∈ isometryMatrices A' ↔
        tangentHom (A.map (PadicInt.toZModPow j)) Z = 0 := by
    rw [mem_isometryMatrices, add_transpose_mul_mul_add_of_sq_eq_bot (D := μ.mapMatrix Z) hker
      (by rw [← transpose_map, hA]) (isometryMatrices A').one_mem
      (fun i l => RingHom.mem_ker.mpr (ZMod.castHom_mulCastHom _ hjkr _)),
      transpose_one, Matrix.one_mul, add_assoc, add_eq_left, hAμ, AddMonoidHom.mapMatrix_apply,
      ← transpose_map, ← AddMonoidHom.mapMatrix_apply, ← AddMonoidHom.mapMatrix_apply,
      ← map_add μ.mapMatrix, ← tangentHom_apply, ← μ.mapMatrix.map_zero, hμinj.eq_iff]
  have hone (Z : Matrix n n (ZMod (p ^ j))) :
      (1 + μ.mapMatrix Z).map (ZMod.castHom h (ZMod (p ^ k))) = 1 := by
    have h0 : (μ.mapMatrix Z).map (ZMod.castHom h (ZMod (p ^ k))) = 0 := by
      ext i l
      exact ZMod.castHom_mulCastHom _ hjkr _
    rw [Matrix.map_add _ (map_add _), h0, add_zero, Matrix.map_one _ (map_zero _) (map_one _)]
  let F : (tangentHom (A.map (PadicInt.toZModPow (p := p) j))).ker →
      {W ∈ isometryMatrices A' | W.map (ZMod.castHom h (ZMod (p ^ k))) = 1} :=
    fun Z => ⟨1 + μ.mapMatrix Z.1, (hmem Z.1).mpr (AddMonoidHom.mem_ker.mp Z.2), hone Z.1⟩
  refine (Nat.card_congr (Equiv.ofBijective F ⟨fun Z Z' hZ => ?_, ?_⟩)).symm
  · exact Subtype.ext (hμinj (add_left_cancel (congrArg Subtype.val hZ)))
  · rintro ⟨W, hW, hWρ⟩
    have hex (i l : n) : ∃ z, μ z = (W - 1) i l := by
      refine (ZMod.exact_mulCastHom_castHom _ hjkr _).mp ?_
      have hW0 : (W - 1).map (ZMod.castHom h (ZMod (p ^ k))) = 0 := by
        rw [Matrix.map_sub _ (map_sub _), hWρ, Matrix.map_one _ (map_zero _) (map_one _),
          sub_self]
      exact congrFun (congrFun hW0 i) l
    choose Z hZ using hex
    have hWZ : 1 + μ.mapMatrix (of Z) = W := by
      rw [← add_sub_cancel 1 W, add_right_inj]
      ext i l
      exact hZ i l
    exact ⟨⟨of Z, AddMonoidHom.mem_ker.mpr ((hmem (of Z)).mp (by rw [hWZ]; exact hW))⟩,
      Subtype.ext hWZ⟩

/-- **The kernel of `Z ↦ A Z + (A Z)ᵀ` grows by `p ^ (n.choose 2)` from level `e` to `e + 1`**,
when `2 det A ∣ p ^ e`. The image of the map consists of symmetric matrices and contains `pᵉ`
times all of them, so its index in the symmetric matrices is the same at both levels. -/
private theorem natCard_ker_tangentHom_succ {A : Matrix n n ℤ_[p]} {e : ℕ}
    (he : 2 * A.det ∣ (p : ℤ_[p]) ^ e) :
    Nat.card (tangentHom (A.map (PadicInt.toZModPow (p := p) (e + 1)))).ker =
      p ^ (Fintype.card n).choose 2 *
        Nat.card (tangentHom (A.map (PadicInt.toZModPow (p := p) e))).ker := by
  have hdvd : p ^ e ∣ p ^ (e + 1) := pow_dvd_pow p e.le_succ
  set L₁ := tangentHom (A.map (PadicInt.toZModPow (p := p) (e + 1)))
  set L₀ := tangentHom (A.map (PadicInt.toZModPow (p := p) e))
  -- the reduction `ρ` modulo `p ^ e`, and the symmetric matrices `S j` modulo `p ^ j`
  set ρ : Matrix n n (ZMod (p ^ (e + 1))) →+ Matrix n n (ZMod (p ^ e)) :=
    (ZMod.castHom hdvd (ZMod (p ^ e))).toAddMonoidHom.mapMatrix
  have hρ (M : Matrix n n (ZMod (p ^ (e + 1)))) :
      ρ M = M.map (ZMod.castHom hdvd (ZMod (p ^ e))) :=
    rfl
  let S (j : ℕ) : AddSubgroup (Matrix n n (ZMod (p ^ j))) :=
    (transposeAddEquiv n n (ZMod (p ^ j))).toAddMonoidHom.eqLocus (AddMonoidHom.id _)
  have hS (j : ℕ) (M : Matrix n n (ZMod (p ^ j))) : M ∈ S j ↔ M.IsSymm :=
    Iff.rfl
  have hAρ : (A.map (PadicInt.toZModPow (e + 1))).map (ZMod.castHom hdvd (ZMod (p ^ e))) =
      A.map (PadicInt.toZModPow e) := by
    rw [Matrix.map_map, ← RingHom.coe_comp, PadicInt.zmod_cast_comp_toZModPow e (e + 1) e.le_succ]
  have hρL (Z : Matrix n n (ZMod (p ^ (e + 1)))) : ρ (L₁ Z) = L₀ (ρ Z) := by
    rw [hρ, hρ, map_tangentHom, hAρ]
  set σ := Function.surjInv (ZMod.ringHom_surjective (ZMod.castHom hdvd (ZMod (p ^ e))))
  have hρσ (M : Matrix n n (ZMod (p ^ e))) : ρ (M.map σ) = M := by
    ext i l
    exact Function.surjInv_eq _ _
  -- `ρ` maps the image of `L₁` onto that of `L₀`, and the symmetric matrices onto themselves
  have hrange : L₁.range.map ρ = L₀.range := by
    ext M
    simp only [AddSubgroup.mem_map, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨_, ⟨Z, rfl⟩, rfl⟩
      exact ⟨ρ Z, (hρL Z).symm⟩
    · rintro ⟨Z, rfl⟩
      exact ⟨L₁ (Z.map σ), ⟨_, rfl⟩, by rw [hρL, hρσ]⟩
  have hsym : (S (e + 1)).map ρ = S e := by
    ext M
    simp only [AddSubgroup.mem_map, hS]
    constructor
    · rintro ⟨N, hN, rfl⟩
      rw [hρ]
      exact hN.map _
    · exact fun hM => ⟨M.map σ, hM.map _, hρσ M⟩
  -- the image of `L₁` is symmetric and contains the symmetric matrices killed by `ρ`
  have hrangeS : L₁.range ≤ S (e + 1) := by
    rintro _ ⟨Z, rfl⟩
    rw [hS, IsSymm, tangentHom_apply, transpose_add, transpose_transpose]
    exact add_comm _ _
  have hkerS : ρ.ker ⊓ S (e + 1) ≤ L₁.range := by
    intro W hW
    obtain ⟨hWker, hWsym⟩ := AddSubgroup.mem_inf.mp hW
    rw [AddMonoidHom.mem_ker, hρ] at hWker
    rw [hS, IsSymm] at hWsym
    -- lift `W` to a symmetric matrix `pᵉ T` over `ℤ_p`
    set τ := Function.surjInv (ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) (e + 1)))
    have hτ : (W.map τ).map (PadicInt.toZModPow (e + 1)) = W := by
      ext i l
      exact Function.surjInv_eq (ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) (e + 1))) _
    have hdiv (i l : n) : (p : ℤ_[p]) ^ e ∣ W.map τ i l := by
      rw [← PadicInt.toZModPow_eq_zero_iff_dvd, ← PadicInt.zmod_cast_comp_toZModPow e (e + 1)
        e.le_succ, RingHom.comp_apply, ← map_apply (f := PadicInt.toZModPow (e + 1)), hτ]
      exact congrFun (congrFun hWker i) l
    choose T hT using hdiv
    have hWT : W.map τ = (p : ℤ_[p]) ^ e • of T := by
      ext i l
      rw [smul_apply, of_apply, smul_eq_mul, ← hT]
    have hpe : (p : ℤ_[p]) ^ e ≠ 0 :=
      pow_ne_zero e (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    have hTsym : (of T)ᵀ = of T := by
      refine smul_right_injective _ hpe ?_
      simp only [← transpose_smul, ← hWT, ← transpose_map, hWsym]
    -- with `pᵉ = 2 det A c`, the matrix `c adj(A) T` maps to `pᵉ T`
    obtain ⟨c, hc⟩ := he
    refine ⟨(c • (adjugate A * of T)).map (PadicInt.toZModPow (e + 1)), ?_⟩
    rw [← map_tangentHom, ← hτ, hWT, tangentHom_apply, mul_smul_comm, ← Matrix.mul_assoc,
      mul_adjugate, smul_mul_assoc, Matrix.one_mul, transpose_smul, transpose_smul, hTsym,
      smul_smul, ← add_smul, hc]
    congr 2
    ring
  have hinf : ρ.ker ⊓ L₁.range = ρ.ker ⊓ S (e + 1) :=
    le_antisymm (inf_le_inf_left _ hrangeS) (le_inf inf_le_left hkerS)
  -- the cardinality bookkeeping
  have hcardS (j : ℕ) : Nat.card (S j) = (p ^ j) ^ (Fintype.card n + 1).choose 2 :=
    calc Nat.card (S j) = Nat.card {M : Matrix n n (ZMod (p ^ j)) // M.IsSymm} :=
          Nat.card_congr (Equiv.subtypeEquivRight (hS j))
      _ = _ := by rw [natCard_isSymm, Nat.card_zmod]
  have hcardM (j : ℕ) : Nat.card (Matrix n n (ZMod (p ^ j))) =
      (p ^ j) ^ (Fintype.card n * Fintype.card n) := by
    rw [Matrix, Nat.card_fun, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, ← pow_mul]
  have hmap (K : AddSubgroup (Matrix n n (ZMod (p ^ (e + 1))))) :
      Nat.card K = Nat.card (K.map ρ) * Nat.card ↥(ρ.ker ⊓ K) := by
    rw [← AddSubgroup.relIndex_ker, AddSubgroup.relIndex_mul_card]
  have h₁ := AddSubgroup.card_ker_mul_card_range L₁
  have h₀ := AddSubgroup.card_ker_mul_card_range L₀
  rw [hmap L₁.range, hrange, hinf, hcardM] at h₁
  rw [hcardM] at h₀
  have hSS := hmap (S (e + 1))
  rw [hsym, hcardS, hcardS] at hSS
  set c := Fintype.card n
  set m := Nat.card ↥(ρ.ker ⊓ S (e + 1))
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hm : m = p ^ (c + 1).choose 2 := by
    refine Nat.eq_of_mul_eq_mul_left (pow_pos (pow_pos hp e) ((c + 1).choose 2)) ?_
    rw [← hSS, ← mul_pow, ← pow_succ]
  -- `c² = (c + 1).choose 2 + c.choose 2`, the sizes of the symmetric and the alternating parts
  have hc2 (c : ℕ) : c * c = (c + 1).choose 2 + c.choose 2 := by
    induction c with
    | zero => rfl
    | succ c ih =>
      have h₂ : (c + 1).choose 2 = c + c.choose 2 := by
        rw [Nat.choose_succ_succ' c 1, Nat.choose_one_right]
      rw [Nat.choose_succ_succ' (c + 1) 1, Nat.choose_one_right, h₂]
      rw [h₂] at ih
      nlinarith [ih]
  have hR : 0 < Nat.card L₀.range * p ^ (c + 1).choose 2 :=
    Nat.mul_pos Nat.card_pos (pow_pos hp _)
  refine Nat.eq_of_mul_eq_mul_right hR ?_
  calc Nat.card L₁.ker * (Nat.card L₀.range * p ^ (c + 1).choose 2)
      = (p ^ (e + 1)) ^ (c * c) := by rw [← h₁, hm]
    _ = (Nat.card L₀.ker * Nat.card L₀.range) * (p ^ (c + 1).choose 2 * p ^ c.choose 2) := by
      rw [h₀, ← pow_add, ← hc2 c, ← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      ring
    _ = p ^ c.choose 2 * Nat.card L₀.ker * (Nat.card L₀.range * p ^ (c + 1).choose 2) := by
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
    obtain ⟨X, rfl⟩ := exists_map_toZModPow_eq X
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

/-- `2 det A` divides `p ^ v_p(2 det A)` when `det A ≠ 0`. -/
private theorem two_mul_det_dvd_pow_valuation {A : Matrix n n ℤ_[p]} (hdet : A.det ≠ 0) :
    2 * A.det ∣ (p : ℤ_[p]) ^ (2 * A.det).valuation := by
  nth_rewrite 1 [PadicInt.unitCoeff_spec (mul_ne_zero two_ne_zero hdet)]
  exact Units.mul_left_dvd.mpr dvd_rfl

/-- **The local density count stabilizes from `r₀ = 2 v_p(2 det A) + 1` on.** If `A` is symmetric
with nonzero determinant, then for every `r > 2 v_p(2 det A)` the normalized count
`#{X ∈ Mₙ(ℤ/pʳ) : Xᵀ A X = A} / p ^ (r * n.choose 2)` equals `α_p(A)`. -/
theorem localDensityCount_div_pow_of_det_ne_zero {A : Matrix n n ℤ_[p]} (hA : Aᵀ = A)
    (hdet : A.det ≠ 0) {r : ℕ} (hr : 2 * (2 * A.det).valuation < r) :
    (A.localDensityCount r : ℚ) / (p : ℚ) ^ (r * (Fintype.card n).choose 2) = A.localDensity :=
  localDensityCount_div_pow_of_dvd hA (two_mul_det_dvd_pow_valuation hdet) hr

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
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [localDensityCount_succ_eq_pow_mul_one hp hA hdet, Nat.cast_mul, Nat.cast_pow,
    div_eq_div_iff (pow_ne_zero _ hp0) (pow_ne_zero _ hp0), Nat.succ_mul, pow_add]
  ring

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
  set f := ZMod.castHom (dvd_pow_self p one_ne_zero) (ZMod p)
  have hf : Function.Bijective f :=
    (Fintype.bijective_iff_surjective_and_card f).mpr ⟨ZMod.ringHom_surjective f, by simp⟩
  have hfun : ⇑(RingEquiv.ofBijective f hf) ∘ ⇑(PadicInt.toZModPow 1) = ⇑PadicInt.toZMod :=
    funext fun x => by simp [f]
  rw [localDensityCount_def, ← natCard_isometryMatrices_map_ringEquiv (RingEquiv.ofBijective f hf),
    Matrix.map_map, hfun]

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
