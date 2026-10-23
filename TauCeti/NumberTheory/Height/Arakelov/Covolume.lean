/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Covolume
public import TauCeti.Algebra.Module.ZLattice.RationalSubspace
public import TauCeti.NumberTheory.Height.Arakelov.Subspace

/-!
# The covolume of the lattice of integral points of a rational subspace

For a subspace `V` of `ℚ^ι`, the covolume of the lattice `V ∩ ℤ^ι` in the real span of `V`
(`Submodule.intLattice`) is the absolute Euclidean height of `V`:
`covolume (V ∩ ℤ^ι) = subspaceHeight V`.
This is the identity through which theorems of the geometry of numbers about the lattice
`V ∩ ℤ^ι`, such as Minkowski's theorems, become statements about the height of `V`. It is the
case `K = ℚ` of Schmidt's identity between the covolume of the lattice `V ∩ 𝓞_K^ι` and the height
of a subspace `V` of `K^ι`, which over a general number field also involves the discriminant and
the complex places of `K`.

The lattice is the whole intersection `V ∩ ℤ^ι`, which is saturated in `ℤ^ι`. The covolume of a
sublattice of finite index is larger by the index, while the height of `V` does not change.

## Main results

* `Submodule.covolume_intLattice`: the covolume of `V.intLattice` is `V.subspaceHeight`.

## Implementation notes

Both sides of the identity are computed from the Plücker coordinates `p` of a `ℤ`-basis of
`V ∩ ℤ^ι`. The squared covolume is the Gram determinant of the basis
(`ZLattice.covolume_sq_eq_det_gram`), which is `∑ s, p s ^ 2` by the Cauchy–Binet formula. The
height is `√(∑ s, p s ^ 2)`: saturation makes `p` primitive (`TauCeti.gcd_plucker_eq_one`), so the
finite places contribute nothing (`TauCeti.height2_intCast_eq_sqrt_of_gcd_eq_one`).

## References

* W. M. Schmidt, *On heights of algebraic subspaces and diophantine approximations*, Ann. of
  Math. **85** (1967), 430–472, §3, Theorem 1.
* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32.

The proof plan is adapted from Ralf Stephan's `ArithmeticHeights/RationalLattice.lean` in
[`rwst/Subspace-Theorems`](https://github.com/rwst/Subspace-Theorems/blob/9894a1c4baf805296b249e95575f0e16e8e1afa3/ArithmeticHeights/RationalLattice.lean),
commit `9894a1c4baf805296b249e95575f0e16e8e1afa3` (Apache 2.0).
-/

public section

noncomputable section

open Module

namespace Submodule

variable {ι : Type*}

section Plucker

variable [Fintype ι] [LinearOrder ι] {V : Submodule ℚ (ι → ℚ)} {n : ℕ}
  (b : Basis (Fin n) ℤ V.intPoints)

/-- The squared covolume of the lattice of integral points of `V` is the Gram determinant of a
basis, the sum of the squared Plücker coordinates of the basis by the Cauchy–Binet formula. -/
private theorem covolume_sq_eq_sum_plucker_sq :
    ZLattice.covolume V.intLattice ^ 2 =
      ∑ s, ((TauCeti.plucker (fun i ↦ (b i : ι → ℤ)) s : ℤ) : ℝ) ^ 2 := by
  have h := ZLattice.covolume_sq_eq_det_gram V.intLattice (b.map V.intPointsEquivIntLattice)
  rw [h]
  have hgram : Matrix.gram ℝ (fun i ↦ (b.map V.intPointsEquivIntLattice i : V.realSpan)) =
      (Matrix.of (fun i ↦ (b i : ι → ℤ)) * (Matrix.of fun i ↦ (b i : ι → ℤ)).transpose).map
        fun x ↦ (x : ℝ) := by
    ext i j
    simp [Matrix.gram_apply, Matrix.mul_apply, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, mul_comm]
  rw [hgram, ← Int.cast_det, TauCeti.det_mul_transpose_eq_sum_plucker_mul]
  simp [sq]

/-- The height of `V` is the Euclidean norm of the Plücker coordinates of a basis of its
integral points: these are coprime, so the finite places do not contribute. -/
private theorem subspaceHeight_eq_sqrt_sum_plucker_sq :
    V.subspaceHeight = √(∑ s, ((TauCeti.plucker (fun i ↦ (b i : ι → ℤ)) s : ℤ) : ℝ) ^ 2) := by
  rw [congrArg subspaceHeight (span_intCast_basis_intPoints b).symm,
    subspaceHeight_span_range (linearIndependent_intCast_basis_intPoints b ℚ)]
  have hp : TauCeti.plucker (fun i j ↦ ((b i : ι → ℤ) j : ℚ)) =
      ((↑) : ℤ → ℚ) ∘ TauCeti.plucker fun i ↦ (b i : ι → ℤ) :=
    funext (TauCeti.plucker_map (Int.castRingHom ℚ) _)
  rw [hp]
  exact TauCeti.height2_intCast_eq_sqrt_of_gcd_eq_one
    (TauCeti.gcd_plucker_eq_one (fun _ _ hc h ↦ mem_intPoints_of_smul_mem hc h) b)

end Plucker

/-- **The covolume of the lattice of integral points of a rational subspace is its absolute
Euclidean height.** For a subspace `V` of `ℚ^ι`, the lattice `V ∩ ℤ^ι` in the real span of `V`
has covolume `V.subspaceHeight`. -/
theorem covolume_intLattice [Fintype ι] [LinearOrder ι] (V : Submodule ℚ (ι → ℚ)) :
    ZLattice.covolume V.intLattice = V.subspaceHeight := by
  rw [subspaceHeight_eq_sqrt_sum_plucker_sq (Module.finBasis ℤ V.intPoints),
    ← covolume_sq_eq_sum_plucker_sq, Real.sqrt_sq (ZLattice.covolume_pos _ _).le]

/-- The line through `(1, 2)` in `ℚ²` cuts out a lattice of covolume `√5` in its real span. -/
example : ZLattice.covolume (ℚ ∙ ![(1 : ℚ), 2]).intLattice = √5 := by
  have h : ![(1 : ℚ), 2] = ((↑) : ℤ → ℚ) ∘ ![1, 2] := by
    ext i
    fin_cases i <;> simp
  rw [covolume_intLattice, subspaceHeight_span_singleton (by simp), h,
    TauCeti.height2_intCast_eq_sqrt_of_gcd_eq_one (by decide)]
  norm_num [Fin.sum_univ_two]

end Submodule

end
