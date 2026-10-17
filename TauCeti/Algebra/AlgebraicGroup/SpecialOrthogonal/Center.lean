/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Basic
public import TauCeti.Algebra.AlgebraicGroup.Center.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Center

/-!
# The scheme-theoretic center of the special orthogonal group

For `n ≥ 3`, over a commutative value algebra where two is a non-zero-divisor, universal centrality
of an `SOₙ`-point is equivalent to membership in the center of its special orthogonal matrix group.
The matrix-center computation in
`TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Center` identifies these as the scalar
matrices `c • 1` with `c² = 1` and `c^n = 1`.

In odd dimension these conditions force `c = 1`. Thus the full scheme-theoretic center is
trivial over every field of characteristic different from two. The argument allows nonreduced
value algebras, retaining the infinitesimal information absent from a calculation on field-valued
points alone.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.3 and Chapter 21.
-/

public section

open WithConv

namespace TauCeti.SpecialOrthogonal

universe u v

section Ring

variable {R : Type u} [CommRing R] (n : ℕ) (hn : 3 ≤ n)
variable {A : Type v} [CommRing A] [Algebra R A] (h2 : IsRegular (2 : A))

include hn h2 in
/-- In dimension at least three, a special orthogonal point over a ring where two is
a non-zero-divisor is universally central exactly when its matrix is central. -/
theorem isCentralPoint_iff_mem_center_pointsMulEquiv
    (g : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    HopfAlgebra.IsCentralPoint g ↔
      pointsMulEquiv R n (A := A) g ∈
        Subgroup.center (Matrix.specialOrthogonalGroup (Fin n) A) := by
  constructor
  · exact fun hg ↦ MulEquivClass.apply_mem_center (pointsMulEquiv R n (A := A))
      (HopfAlgebra.center_le_center (HopfAlgebra.mem_center.mpr hg))
  · intro hg
    obtain ⟨c, hc, _, _⟩ :=
      (Matrix.SpecialOrthogonalGroup.mem_center_iff h2 (pointsMulEquiv R n (A := A) g)
        (by simpa using hn)).mp hg
    rw [HopfAlgebra.isCentralPoint_def]
    intro B _ _ φ h
    apply (pointsMulEquiv R n (A := B)).injective
    rw [map_mul, map_mul]
    have hscalar : (pointsMulEquiv R n (A := B) (AlgHom.mapValue φ g) :
        Matrix (Fin n) (Fin n) B) = Matrix.scalar (Fin n) (φ c) := by
      rw [pointsMulEquiv_mapValue, Matrix.SpecialOrthogonalGroup.coe_map, hc]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.map_apply, hij]
    exact (Subgroup.mem_center_iff.mp
      (Matrix.SpecialOrthogonalGroup.mem_center_of_coe_eq_scalar _ (φ c) hscalar)
        (pointsMulEquiv R n (A := B) h)).symm

include hn h2 in
/-- Every universally central point of an odd-dimensional special orthogonal group is the
identity, including points with values in nonreduced algebras. -/
theorem eq_one_of_isCentralPoint_of_odd (hodd : Odd n)
    (g : WithConv (coordinateHopfAlgebra R n →ₐ[R] A))
    (hg : HopfAlgebra.IsCentralPoint g) : g = 1 := by
  have hmatrix := Matrix.SpecialOrthogonalGroup.eq_one_of_mem_center_of_odd h2
    (pointsMulEquiv R n (A := A) g) (by simpa using hn) (by simpa using hodd)
    ((isCentralPoint_iff_mem_center_pointsMulEquiv n hn h2 g).mp hg)
  exact (pointsMulEquiv R n).injective (hmatrix.trans (map_one _).symm)

end Ring

/-- The full scheme-theoretic center of odd-dimensional `SOₙ`, for `n ≥ 3`, is trivial over
every field of characteristic different from two. -/
theorem centerDefiningIdeal_eq_augmentation_of_odd (k : Type u) [Field k] [NeZero (2 : k)]
    (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n) =
      HopfIdeal.augmentation k (coordinateHopfAlgebra k n) := by
  apply (CommHopfAlgCat.centerDefiningIdeal_eq_augmentation_iff_forall_isCentralPoint_eq_one
    (coordinateHopfAlgebra k n)).mpr
  intro A g hg
  have htwo : IsUnit (2 : A) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (NeZero.ne (2 : k))).map (algebraMap k A)
  exact eq_one_of_isCentralPoint_of_odd n hn htwo.isRegular hodd g hg

end TauCeti.SpecialOrthogonal
