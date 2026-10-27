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
import TauCeti.NumberTheory.Padics.RingHoms

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
reduction of `A` modulo `p`. The orders of the finite orthogonal groups then give the closed
values

```text
n = 2m + 1:  α_p(A) = 2 ∏_{i=1}^{m} (1 - p^{-2i}),
n = 2m + 2:  α_p(A) = 2 (1 - ε p^{-(m+1)}) ∏_{i=1}^{m} (1 - p^{-2i}),  ε = ((-1)^{m+1} det A | p).
```

The sign `ε` is the character of the determinant twisted by `(-1)^{m+1}`, which records whether
the reduction is split; the hyperbolic plane at `p = 3` has `det = -1`, a nonsquare, and density
`4/3 = 2 (1 - 3⁻¹)`.

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
* `Matrix.localDensityCount_one`: the count at level `1` is the number of matrices over `𝔽_p`
  preserving the reduction of `A` modulo `p`; when that reduction is nondegenerate, this is the
  order of its orthogonal group.
* `Matrix.tendsto_localDensityCount_div_of_card_eq_two_mul_add_one`,
  `Matrix.tendsto_localDensityCount_div_of_card_eq_two_mul_add_two`: the closed values of the
  local density at such a prime, in odd and in even rank.
* `Matrix.tendsto_localDensityCount_div_hyperbolicPlane_three`: the hyperbolic plane at `p = 3`.

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
