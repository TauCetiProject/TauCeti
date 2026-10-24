/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.LinearAlgebra.Basis.Basic
public import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Positive

/-!
# The Frobenius–Perron character of a transitive ℤ₊-ring

Let `R` be a ring with a finite nonempty `ℤ`-basis `b` whose structure constants are nonnegative:
every product `b i * b j` is a nonnegative integer combination of basis elements (a **ℤ₊-ring**
in the sense of Etingof–Gelaki–Nikshych–Ostrik). Suppose it is **transitive** on one side: every
basis element occurs in `b j * s` for every `j`, where `s = ∑ i, b i` is the sum of the basis.
Then `R` has exactly one character `χ : R →+* ℝ` taking nonnegative values on the basis, and
its values on the basis are strictly positive. Its value at an element `x` with nonnegative
coordinates is the spectral radius of the matrix of left multiplication by `x`.

This is the character that defines the Frobenius–Perron dimension of a fusion category, whose
Grothendieck ring is a transitive ℤ₊-ring with basis the classes of the simple objects. The
character cannot be defined from each multiplication matrix separately: such a matrix may be
reducible (the matrix of the unit is the identity), so its nonnegative eigenvectors need not be
proportional and do not single out a value for the character, and its spectral radius alone is
not visibly additive or multiplicative. The character is instead constructed as below, and only
afterwards is its value at an element with nonnegative coordinates identified with the spectral
radius of the corresponding left-multiplication matrix.

The construction follows Etingof–Gelaki–Nikshych–Ostrik. The matrix of right multiplication by
`s` has strictly positive entries, so by the Perron–Frobenius theorem it has an eigenvector `v`
with positive entries whose eigenline contains every eigenvector for the same eigenvalue. Left
multiplications commute with right multiplications, so each of them preserves that eigenline, and
the scalar by which left multiplication by `x` acts on `v` is the character. Uniqueness comes from
the transposed matrix: the values of any character on the basis form an eigenvector of it, so when
they are nonnegative they are positive, and any two such eigenvectors are proportional.

## Main results

* `Module.Basis.exists_ringHom_apply_pos`: a transitive ℤ₊-ring of finite rank has a character
  which is positive on the basis.
* `Module.Basis.existsUnique_ringHom_nonneg`: it is the only character which is nonnegative on the
  basis.
* `Module.Basis.ringHom_eq_of_nonneg` and `Module.Basis.ringHom_apply_pos_of_nonneg`: two
  characters which are nonnegative on the basis are equal, and such a character is positive on the
  basis. These need only transitivity, not the nonnegativity of the structure constants.
* `Module.Basis.spectralRadius_leftMulMatrix`: its value at an element with nonnegative
  coordinates is the spectral radius of the matrix of left multiplication by that element.

## References

* P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*, Mathematical Surveys and
  Monographs **205**, AMS (2015), Section 3.3 (Proposition 3.3.6: Frobenius–Perron dimensions of
  a transitive ℤ₊-ring).
-/

public section

open scoped Matrix

open Matrix

namespace Module.Basis

variable {ι R : Type*} [Fintype ι] [Ring R] (b : Basis ι ℤ R)

section Matrices

variable [DecidableEq ι]

/-- The real matrix of left multiplication. -/
private noncomputable def leftMulReal : R →+* Matrix ι ι ℝ :=
  (Int.castRingHom ℝ).mapMatrix.comp (Algebra.leftMulMatrix b).toRingHom

private theorem leftMulReal_apply (x : R) (l j : ι) :
    leftMulReal b x l j = b.repr (x * b j) l := by
  simp [leftMulReal, Algebra.leftMulMatrix_eq_repr_mul]

/-- The real matrix of right multiplication by the sum of the basis. -/
private noncomputable def rightMulSum : Matrix ι ι ℝ :=
  (Int.castRingHom ℝ).mapMatrix (LinearMap.toMatrix b b (LinearMap.mulRight ℤ (∑ i, b i)))

private theorem rightMulSum_apply (l j : ι) :
    rightMulSum b l j = b.repr (b j * ∑ i, b i) l := by
  simp [rightMulSum, LinearMap.toMatrix_apply]

/-- Left multiplications commute with right multiplication by the sum of the basis. -/
private theorem leftMulReal_mul_rightMulSum (x : R) :
    leftMulReal b x * rightMulSum b = rightMulSum b * leftMulReal b x := by
  have h : Algebra.leftMulMatrix b x * LinearMap.toMatrix b b (LinearMap.mulRight ℤ (∑ i, b i)) =
      LinearMap.toMatrix b b (LinearMap.mulRight ℤ (∑ i, b i)) * Algebra.leftMulMatrix b x := by
    rw [← Algebra.toMatrix_lmul_eq, ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul,
      (LinearMap.commute_mulLeft_right x _).eq]
  rw [leftMulReal, rightMulSum, RingHom.comp_apply, ← map_mul, ← map_mul]
  exact congrArg _ h

/-- Transitivity says exactly that the matrix of right multiplication by the sum of the basis has
positive entries. -/
private theorem rightMulSum_pos (ht : ∀ j l, 0 < ∑ i, b.repr (b j * b i) l) (l j : ι) :
    0 < rightMulSum b l j := by
  rw [rightMulSum_apply, Finset.mul_sum, map_sum, Finsupp.finsetSum_apply]
  exact_mod_cast ht j l

/-- The values of a character on the basis form an eigenvector of the transpose of the matrix of
right multiplication by the sum of the basis, for the value of the character at that sum. -/
private theorem rightMulSum_transpose_mulVec (ψ : R →+* ℝ) :
    (rightMulSum b)ᵀ *ᵥ (fun l ↦ ψ (b l)) = ψ (∑ i, b i) • fun l ↦ ψ (b l) := by
  ext j
  rw [Pi.smul_apply, smul_eq_mul, mul_comm, ← map_mul, ringHom_apply_eq_sum b ψ]
  simp [mulVec, dotProduct, rightMulSum_apply, mul_comm]

end Matrices

section Transitive

variable (ht : ∀ j l, 0 < ∑ i, b.repr (b j * b i) l)

include ht

/-- If every basis element occurs in `b j * ∑ i, b i` for every `j`, then a character to `ℝ`
which is nonnegative on the basis is positive on the basis. -/
theorem ringHom_apply_pos_of_nonneg {χ : R →+* ℝ} (hχ : ∀ i, 0 ≤ χ (b i)) (i : ι) :
    0 < χ (b i) := by
  classical
  exact pos_of_mulVec_eq_smul (fun i j ↦ rightMulSum_pos b ht j i) hχ (ringHom_apply_ne_zero b χ)
    (rightMulSum_transpose_mulVec b χ) i

/-- **Uniqueness of the Frobenius–Perron character.** If every basis element occurs in
`b j * ∑ i, b i` for every `j`, then two characters to `ℝ` which are nonnegative on the basis are
equal. -/
theorem ringHom_eq_of_nonneg {χ ψ : R →+* ℝ} (hχ : ∀ i, 0 ≤ χ (b i)) (hψ : ∀ i, 0 ≤ ψ (b i)) :
    χ = ψ := by
  classical
  -- The values of `ψ` on the basis are a nonnegative eigenvector of a positive matrix of which
  -- the values of `χ` are a positive eigenvector, so they are proportional.
  obtain ⟨c, -, hc⟩ := exists_pos_eq_smul_of_mulVec_eq_smul
    (fun i j ↦ rightMulSum_pos b ht j i) (ringHom_apply_pos_of_nonneg b ht hχ)
    (rightMulSum_transpose_mulVec b χ) hψ (ringHom_apply_ne_zero b ψ)
    (rightMulSum_transpose_mulVec b ψ)
  have hψc (l : ι) : ψ (b l) = c * χ (b l) := congrFun hc l
  -- Evaluating at `1` shows that the proportionality constant is `1`.
  have hc1 : c = 1 := by
    have h := ringHom_apply_eq_sum b ψ 1
    simp_rw [hψc, mul_left_comm _ c, ← Finset.mul_sum, ← ringHom_apply_eq_sum, map_one,
      mul_one] at h
    exact h.symm
  ext y
  simp [ringHom_apply_eq_sum b _ y, hψc, hc1]

end Transitive

variable (hb : ∀ i j l, 0 ≤ b.repr (b i * b j) l) (ht : ∀ j l, 0 < ∑ i, b.repr (b j * b i) l)

include hb ht

/-- A ring with a finite nonempty `ℤ`-basis with nonnegative structure constants, such that every
basis element occurs in `b j * ∑ i, b i` for every `j`, has a character to `ℝ` taking positive
values on the basis. -/
theorem exists_ringHom_apply_pos [Nonempty ι] : ∃ χ : R →+* ℝ, ∀ i, 0 < χ (b i) := by
  classical
  have hQ := rightMulSum_pos b ht
  obtain ⟨r, -, v, hv, hQv⟩ := exists_mulVec_eq_smul_of_pos hQ
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hv0 : v ≠ 0 := fun h ↦ (hv i₀).ne' (congrFun h i₀)
  let f (x : R) : ℝ := (leftMulReal b x *ᵥ v) i₀ / v i₀
  -- Left multiplications commute with right multiplication by the sum of the basis, so they
  -- preserve its Perron eigenline; `f x` is the scalar by which `x` acts on it.
  have hf (x : R) : leftMulReal b x *ᵥ v = f x • v := by
    obtain ⟨c, hc⟩ := exists_eq_smul_of_mulVec_eq_smul hQ hv hQv (w := leftMulReal b x *ᵥ v)
      (by rw [mulVec_mulVec, ← leftMulReal_mul_rightMulSum, ← mulVec_mulVec, hQv, mulVec_smul])
    simp [f, hc, (hv i₀).ne']
  have key {c d : ℝ} (h : c • v = d • v) : c = d := smul_left_injective ℝ hv0 h
  let χ : R →+* ℝ :=
    { toFun := f
      map_one' := key <| by rw [← hf, map_one, one_mulVec, one_smul]
      map_mul' x y := key <| by
        rw [← hf, map_mul, ← mulVec_mulVec, hf y, mulVec_smul, hf x, smul_smul, mul_comm]
      map_zero' := key <| by rw [← hf, map_zero, zero_mulVec, zero_smul]
      map_add' x y := key <| by rw [← hf, map_add, add_mulVec, hf x, hf y, add_smul] }
  refine ⟨χ, fun i ↦ div_pos ?_ (hv i₀)⟩
  -- The entry of `b i * v` at `i₀` is a sum of nonnegative terms, one of which is positive.
  obtain ⟨j, -, hj⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ ↦ (0 : ℤ))
    (by simpa using ht i i₀)
  exact Finset.sum_pos' (fun j _ ↦ mul_nonneg (by simpa [leftMulReal_apply] using hb i j i₀)
    (hv j).le) ⟨j, Finset.mem_univ j, mul_pos (by simpa [leftMulReal_apply] using hj) (hv j)⟩

/-- **The Frobenius–Perron character.** A ring with a finite nonempty `ℤ`-basis with nonnegative
structure constants, such that every basis element occurs in `b j * ∑ i, b i` for every `j`, has
exactly one character to `ℝ` which is nonnegative on the basis. -/
theorem existsUnique_ringHom_nonneg [Nonempty ι] : ∃! χ : R →+* ℝ, ∀ i, 0 ≤ χ (b i) :=
  let ⟨χ, hχ⟩ := exists_ringHom_apply_pos b hb ht
  ⟨χ, fun i ↦ (hχ i).le, fun _ hψ ↦ ringHom_eq_of_nonneg b ht hψ fun i ↦ (hχ i).le⟩

/-- **The Frobenius–Perron character is a spectral radius.** If `χ` is a character of a transitive
ℤ₊-ring which is nonnegative on the basis, then for every `x` with nonnegative coordinates, `χ x`
is the spectral radius of the matrix of left multiplication by `x`. -/
theorem spectralRadius_leftMulMatrix [DecidableEq ι] {χ : R →+* ℝ} (hχ : ∀ i, 0 ≤ χ (b i))
    {x : R} (hx : ∀ i, 0 ≤ b.repr x i) :
    spectralRadius ℂ ((Algebra.leftMulMatrix b x).map (Int.cast : ℤ → ℂ)) =
      ENNReal.ofReal (χ x) := by
  have := χ.domain_nontrivial
  have := b.index_nonempty
  -- The coordinates of `x * b j` are nonnegative.
  have hN (j l : ι) : 0 ≤ (leftMulReal b x)ᵀ j l := by
    rw [transpose_apply, leftMulReal_apply, Int.cast_nonneg_iff]
    conv_rhs => rw [← b.sum_repr x]
    simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_zsmul, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, smul_eq_mul]
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hx i) (hb i j l)
  have hNχ : (leftMulReal b x)ᵀ *ᵥ (fun l ↦ χ (b l)) = χ x • fun l ↦ χ (b l) := by
    ext j
    simp only [mulVec, dotProduct, transpose_apply, leftMulReal_apply, Pi.smul_apply, smul_eq_mul,
      ← ringHom_apply_eq_sum, map_mul]
  have hmap : ((leftMulReal b x)ᵀ).map ((↑) : ℝ → ℂ) =
      ((Algebra.leftMulMatrix b x).map (Int.cast : ℤ → ℂ))ᵀ := by
    ext l j
    simp [leftMulReal_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rw [← spectralRadius_transpose, ← hmap,
    spectralRadius_eq_of_mulVec_eq_smul hN (ringHom_apply_pos_of_nonneg b ht hχ) hNχ]

end Module.Basis
