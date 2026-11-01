/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Orientation

/-!
# The special orthogonal group of a real inner product space

The orthogonal group of a real Hilbert space `V` is the unitary group `unitary (V →L[ℝ] V)` of its
operator algebra, which acts on orthonormal frames by precomposition. Its subgroup
`TauCeti.specialOrthogonalGroup V` consists of the orthogonal transformations of positive
determinant. When `V` is finite-dimensional these are exactly the orthogonal transformations
preserving an orientation of `V`
(`Orientation.map_linearIsometryEquiv_eq_iff_mem_specialOrthogonalGroup`); this is the structure
group of the positively oriented orthonormal frames of an oriented vector bundle.

When `V` is infinite-dimensional, `LinearMap.det` is identically `1`, so the subgroup is the whole
orthogonal group.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (the oriented structure group `SO(n)`).
-/

public section

namespace TauCeti

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The special orthogonal group of a real Hilbert space `V`: the orthogonal transformations of
`V`, as elements of the unitary group of `V →L[ℝ] V`, whose determinant is positive. -/
def specialOrthogonalGroup : Subgroup (unitary (V →L[ℝ] V)) where
  carrier := {g | 0 < (g : V →L[ℝ] V).det}
  mul_mem' {g h} hg hh := by
    simpa [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_mul, LinearMap.det_comp] using
      mul_pos hg hh
  one_mem' := by simp [ContinuousLinearMap.det]
  inv_mem' {g} hg := by
    -- `det g⁻¹ * det g = det 1 = 1`, and `det g` is positive.
    have h : (((g⁻¹ : unitary (V →L[ℝ] V)) : V →L[ℝ] V).det) * (g : V →L[ℝ] V).det = 1 := by
      rw [ContinuousLinearMap.det, ContinuousLinearMap.det, ← map_mul,
        ← ContinuousLinearMap.toLinearMap_mul, ← Submonoid.coe_mul, inv_mul_cancel]
      simp
    exact pos_of_mul_pos_left (h ▸ one_pos) hg.le

variable {V}

@[simp]
theorem mem_specialOrthogonalGroup_iff {g : unitary (V →L[ℝ] V)} :
    g ∈ specialOrthogonalGroup V ↔ 0 < (g : V →L[ℝ] V).det :=
  Iff.rfl

end TauCeti

namespace Orientation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} [Fintype ι]

/-- An orthogonal transformation of a finite-dimensional real inner product space preserves an
orientation exactly when it lies in the special orthogonal group. -/
theorem map_linearIsometryEquiv_eq_iff_mem_specialOrthogonalGroup
    (hι : Fintype.card ι = Module.finrank ℝ V) (o : Orientation ℝ V ι)
    (g : unitary (V →L[ℝ] V)) :
    Orientation.map ι (Unitary.linearIsometryEquiv g).toLinearEquiv o = o ↔
      g ∈ TauCeti.specialOrthogonalGroup V :=
  o.map_eq_iff_det_pos _ hι

end Orientation
