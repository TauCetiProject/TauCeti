/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Generators
public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Norm
import TauCeti.LinearAlgebra.CliffordAlgebra.Basic

/-!
# The kernel of the Lipschitz action

The Lipschitz group acts on its quadratic space by twisted conjugation,
`lipschitzToOrthogonal Q : lipschitzGroup Q →* O(Q)`. Scalars act trivially. Conversely, an
element acting trivially graded-commutes with every vector, and for a nondegenerate form on a
finite-dimensional space over a field in which `2` is invertible such an element is a scalar
(`CliffordAlgebra.exists_eq_algebraMap_of_involute_mul_ι_eq_ι_mul`). So the kernel of the action is
exactly the group of scalar units. This is the statement that makes the spinor norm of an isometry
independent of the Lipschitz element chosen to lift it: two lifts differ by a scalar.

## Main results

* `CliffordAlgebra.lipschitzToOrthogonal_eq_one_of_coe_eq_algebraMap`: a scalar acts trivially.
* `CliffordAlgebra.lipschitzNorm_scalarUnits`: the norm of a scalar unit is its square.
* `CliffordAlgebra.mem_ker_lipschitzToOrthogonal_iff`: an element of the Lipschitz group acts
  trivially exactly when it is a scalar unit.
* `CliffordAlgebra.ker_lipschitzToOrthogonal`: the kernel of the Lipschitz action is the range of
  `CliffordAlgebra.scalarUnits`.

## References

See C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II, and H. B. Lawson and
M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

universe u v

namespace CliffordAlgebra

section CommRing

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M} [Invertible (2 : R)]

/-- A Lipschitz element that is a scalar acts trivially on the quadratic space. -/
theorem lipschitzToOrthogonal_eq_one_of_coe_eq_algebraMap {x : lipschitzGroup Q} {a : R}
    (hx : ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = algebraMap R (CliffordAlgebra Q) a) :
    lipschitzToOrthogonal Q x = 1 := by
  ext m
  apply ι_injective Q
  rw [coe_lipschitzToOrthogonal_apply, ι_lipschitzVectorAction_apply, hx, AlgHom.commutes,
    Algebra.commutes, ← hx, mul_assoc, Units.mul_inv, mul_one]
  simp

/-- The scalar units act trivially on the quadratic space. -/
@[simp]
theorem lipschitzToOrthogonal_scalarUnits (hQ : ∃ v, IsUnit (Q v)) (a : Rˣ) :
    lipschitzToOrthogonal Q (scalarUnits Q hQ a) = 1 :=
  lipschitzToOrthogonal_eq_one_of_coe_eq_algebraMap (coe_scalarUnits hQ a)

/-- A Lipschitz element equal to a scalar unit has norm equal to the square of that scalar. -/
theorem lipschitzNorm_eq_of_coe_eq_algebraMap {x : lipschitzGroup Q} {a : Rˣ}
    (hx : ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q) a) : lipschitzNorm Q x = a * a := by
  apply Units.ext
  apply algebraMap_injective Q
  rw [← star_mul_self_eq_algebraMap_lipschitzNorm, hx, star_algebraMap, ← map_mul,
    Units.val_mul]

/-- The norm of a scalar unit in the Lipschitz group is its square. -/
@[simp]
theorem lipschitzNorm_scalarUnits (hQ : ∃ v, IsUnit (Q v)) (a : Rˣ) :
    lipschitzNorm Q (scalarUnits Q hQ a) = a * a :=
  lipschitzNorm_eq_of_coe_eq_algebraMap (coe_scalarUnits hQ a)

end CommRing

section Field

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Invertible (2 : K)] {Q : QuadraticForm K V}

/-- **An element of the Lipschitz group acts trivially exactly when it is a scalar unit**, for a
nondegenerate form on a finite-dimensional space over a field in which `2` is invertible. -/
theorem mem_ker_lipschitzToOrthogonal_iff (hQ : Q.Nondegenerate) {x : lipschitzGroup Q} :
    x ∈ (lipschitzToOrthogonal Q).ker ↔
      ∃ r : Kˣ, ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = algebraMap K _ r := by
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := exists_eq_algebraMap_of_involute_mul_ι_eq_ι_mul Q hQ _ fun w ↦ by
      have haction : lipschitzVectorAction Q x w = w := by
        rw [← coe_lipschitzToOrthogonal_apply, MonoidHom.mem_ker.mp hx]
        simp
      have h := ι_lipschitzVectorAction_apply x w
      rw [haction] at h
      conv_rhs => rw [h]
      rw [mul_assoc _ _ ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q), Units.inv_mul,
        mul_one]
    have hr₀ : r ≠ 0 := by
      rintro rfl
      exact Units.ne_zero _ (hr.trans (map_zero _))
    exact ⟨Units.mk0 r hr₀, by simpa using hr⟩
  · rintro ⟨r, hr⟩
    exact lipschitzToOrthogonal_eq_one_of_coe_eq_algebraMap hr

/-- **The kernel of the Lipschitz action is the group of scalar units**, for a nondegenerate form
on a finite-dimensional space over a field in which `2` is invertible, provided some vector is
anisotropic so that the scalar units lie in the Lipschitz group. -/
theorem ker_lipschitzToOrthogonal (hQ : Q.Nondegenerate) (hv : ∃ v, IsUnit (Q v)) :
    (lipschitzToOrthogonal Q).ker = (scalarUnits Q hv).range := by
  ext x
  rw [mem_ker_lipschitzToOrthogonal_iff hQ]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, Subtype.ext (Units.ext (by rw [coe_scalarUnits, hr]))⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, coe_scalarUnits hv a⟩

end Field

end CliffordAlgebra
