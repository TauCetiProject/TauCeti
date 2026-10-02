/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Lipschitz.OpenMap
public import TauCeti.Topology.Algebra.CliffordAlgebra.Lipschitz.Norm
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic
import Mathlib.Analysis.Normed.Field.ProperSpace

/-!
# The spinor kernel is open

Let `Q` be a nondegenerate quadratic form on a finite-dimensional space over a locally compact
nontrivially normed field `K` in which `2` is invertible, such as `ℝ` or `ℚ_p`, and suppose that
the squares are open in `Kˣ`. Then the kernel of the spinor norm `θ : O(Q) → Kˣ ⧸ (Kˣ)²` is open
in the orthogonal group, and so are the kernel of its restriction to `SO(Q)` and the image of the
Spin group in `SO(Q)`, which is that kernel.

The spinor norm is the Clifford norm `N x = reverse x * x` of a Lipschitz lift read modulo squares.
So the kernel of `θ` is the image, under the vector representation, of the Lipschitz elements whose
Clifford norm is a square. That set is open because the Clifford norm is continuous and the squares
are open, and its image is open because the vector representation is an open map.

The openness of the squares cannot be dropped, and it does not follow from the topology on `V`:
over `ℝ` the squares are the positive reals, while over `ℚ_p` it is the local-field fact that the
units deep enough in the unit filtration are squares. Discreteness of the square-class group alone
would only show that a *continuous* map into it is locally constant.

## Main results

* `CliffordAlgebra.isOpen_ker_orthogonalSpinorNorm`: the kernel of the spinor norm on `O(Q)` is
  open.
* `CliffordAlgebra.isOpen_ker_spinorNorm`: the kernel of the spinor norm on `SO(Q)` is open.
* `CliffordAlgebra.isOpen_range_spinToSpecialOrthogonal`: the image of the Spin group in `SO(Q)`
  is open.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §55.
-/

public section

namespace CliffordAlgebra

open TauCeti

variable {K V : Type*} [NontriviallyNormedField K] [LocallyCompactSpace K]
  [Invertible (2 : K)] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (Q : QuadraticForm K V)

/-- **The spinor kernel of `O(Q)` is open.** For a nondegenerate quadratic form on a
finite-dimensional space over a locally compact nontrivially normed field in which `2` is
invertible and the squares are open in the units, the kernel of the spinor norm is an open
subgroup of the orthogonal group. -/
theorem isOpen_ker_orthogonalSpinorNorm (hQ : Q.Nondegenerate)
    (hsq : IsOpen (Subgroup.square Kˣ : Set Kˣ)) :
    IsOpen ((orthogonalSpinorNorm Q hQ).ker : Set (QuadraticMap.orthogonalGroup Q)) := by
  have : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  have hcomp : (orthogonalSpinorNorm Q hQ).comp (lipschitzToOrthogonal Q) =
      squareClassHom.comp (cliffordNorm Q) :=
    MonoidHom.ext (orthogonalSpinorNorm_lipschitzToOrthogonal Q hQ)
  -- The Lipschitz lifts of the kernel of `θ` are the elements of square Clifford norm.
  have hlift : (orthogonalSpinorNorm Q hQ).ker.comap (lipschitzToOrthogonal Q) =
      (Subgroup.square Kˣ).comap (cliffordNorm Q) := by
    rw [MonoidHom.comap_ker, hcomp, ← MonoidHom.comap_ker, ker_squareClassHom]
  rw [← Subgroup.map_comap_eq_self_of_surjective (lipschitzToOrthogonal_surjective Q hQ)
    (orthogonalSpinorNorm Q hQ).ker, hlift, Subgroup.coe_map, Subgroup.coe_comap]
  exact isOpenMap_lipschitzToOrthogonal Q hQ _ (hsq.preimage (continuous_cliffordNorm Q))

/-- **The spinor kernel of `SO(Q)` is open.** Under the hypotheses of
`isOpen_ker_orthogonalSpinorNorm`, the kernel of the spinor norm on the special orthogonal group
is open. -/
theorem isOpen_ker_spinorNorm (hQ : Q.Nondegenerate)
    (hsq : IsOpen (Subgroup.square Kˣ : Set Kˣ)) :
    IsOpen ((spinorNorm Q hQ).ker : Set (QuadraticMap.specialOrthogonalGroup Q)) := by
  have hker : (spinorNorm Q hQ).ker = (orthogonalSpinorNorm Q hQ).ker.comap
      (_root_.QuadraticMap.specialOrthogonalToOrthogonal Q) := by
    ext g
    simp only [MonoidHom.mem_ker, Subgroup.mem_comap, spinorNorm_apply]
  have hcont : Continuous (_root_.QuadraticMap.specialOrthogonalToOrthogonal Q) :=
    continuous_induced_rng.mpr (continuous_subtype_val.congr fun g =>
      (_root_.QuadraticMap.coe_specialOrthogonalToOrthogonal g).symm)
  rw [hker, Subgroup.coe_comap]
  exact (isOpen_ker_orthogonalSpinorNorm Q hQ hsq).preimage hcont

/-- **The image of Spin is open in `SO(Q)`.** Under the hypotheses of
`isOpen_ker_orthogonalSpinorNorm`, the image of the Spin group in the special orthogonal group is
open, being the kernel of the spinor norm. -/
theorem isOpen_range_spinToSpecialOrthogonal (hQ : Q.Nondegenerate)
    (hsq : IsOpen (Subgroup.square Kˣ : Set Kˣ)) :
    IsOpen ((spinToSpecialOrthogonal Q).range : Set (QuadraticMap.specialOrthogonalGroup Q)) := by
  rw [range_spinToSpecialOrthogonal_eq_ker_spinorNorm Q hQ]
  exact isOpen_ker_spinorNorm Q hQ hsq

end CliffordAlgebra
