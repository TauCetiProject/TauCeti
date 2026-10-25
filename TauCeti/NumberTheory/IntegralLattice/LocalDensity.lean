/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Instances.Rat
public import TauCeti.Data.ZMod.MulCastHom
public import TauCeti.LinearAlgebra.Matrix.IsometryMatrices

/-!
# The counting function of the local density

Let `A` be the Gram matrix of a nondegenerate `ℤ_p`-lattice of rank `n`. Its local
(automorphism) density is the limit

```text
α_p(A) = lim_{r → ∞} p^{-r n (n - 1) / 2} · #{X ∈ Mₙ(ℤ/pʳ) : Xᵀ A X ≡ A (mod pʳ)},
```

and the local densities at all primes are the local factors of the mass of a genus of
positive definite lattices. This file defines the count inside the limit,
`Matrix.localDensityCount A r`, shows that it only depends on `A` up to a change of basis, and
evaluates it at a prime `p` not dividing `2 det A`.

At such a prime the reduction `ℤ/pʳ⁺¹ → ℤ/pʳ` is a square-zero extension for `r ≥ 1`, `2` is
a unit, and `A` is symmetric with unit determinant, so the lifting count
`Matrix.natCard_isometryMatrices_eq_pow_mul` multiplies the count by `p ^ (n.choose 2)` at
each step. The normalized count is therefore constant from `r = 1` on, and the local density
is `#O(A mod p) / p^{n (n - 1) / 2}`, where `O(A mod p)` is the orthogonal group of the
reduction of `A` modulo `p`.

## Main definitions

* `Matrix.localDensityCount A r`: the number of `X ∈ Mₙ(ℤ/pʳ)` with `Xᵀ A X = A` modulo `pʳ`.

## Main results

* `Matrix.localDensityCount_transpose_mul_mul`: the count is unchanged by a change of basis
  `A ↦ Pᵀ A P`, so it only depends on the isometry class of the lattice.
* `Matrix.localDensityCount_succ_of_isUnit_det`: for `p` odd, `A` symmetric with unit
  determinant and `r ≥ 1`, the count at level `r + 1` is `p ^ (n.choose 2)` times the count at
  level `r`.
* `Matrix.tendsto_localDensityCount_div_of_isUnit_det`: at such a prime the normalized count
  converges, and its limit, the local density, is the count at level `1` divided by
  `p ^ (n.choose 2)`.

## References

* C. L. Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. of Math. 36
  (1935).
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

/-- **The local density count at a prime not dividing `2 det A` grows by `p ^ (n.choose 2)` at
each level `r ≥ 1`.** -/
theorem localDensityCount_succ_of_isUnit_det (hp : p ≠ 2) {A : Matrix n n ℤ_[p]} (hA : Aᵀ = A)
    (hdet : IsUnit A.det) {r : ℕ} (hr : r ≠ 0) :
    A.localDensityCount (r + 1) = p ^ (Fintype.card n).choose 2 * A.localDensityCount r := by
  have hpr : p * p ^ r = p ^ (r + 1) := (pow_succ' p r).symm
  have hpr0 : p ^ r ≠ 0 := pow_ne_zero r (Fact.out : p.Prime).ne_zero
  set f := ZMod.castHom (Dvd.intro_left p hpr) (ZMod (p ^ r))
  have hcomp : f.comp (PadicInt.toZModPow (r + 1)) = PadicInt.toZModPow r :=
    PadicInt.zmod_cast_comp_toZModPow r (r + 1) r.le_succ
  have h2 : IsUnit (2 : ZMod (p ^ (r + 1))) := by
    have hcop : Nat.Coprime 2 (p ^ (r + 1)) :=
      ((Nat.coprime_primes Nat.prime_two Fact.out).mpr hp.symm).pow_right _
    simpa using (ZMod.isUnit_iff_coprime 2 (p ^ (r + 1))).mpr hcop
  have hdet' : IsUnit (A.map (PadicInt.toZModPow (r + 1))).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hdet.map _
  rw [localDensityCount_def, localDensityCount_def,
    natCard_isometryMatrices_eq_pow_mul (f := f) (ZMod.ringHom_surjective f)
      (ZMod.ker_castHom_sq_eq_bot _ hpr (dvd_pow_self p hr)) h2
      (by rw [← transpose_map, hA]) hdet',
    ZMod.natCard_ker_castHom _ hpr hpr0, Matrix.map_map, ← RingHom.coe_comp, hcomp]

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

end Matrix
