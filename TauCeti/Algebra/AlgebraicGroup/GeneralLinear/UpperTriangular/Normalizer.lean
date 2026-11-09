/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.TitsSystem
import TauCeti.GroupTheory.TitsSystem.Parabolic.Normalizer

/-!
# Pointwise normalizers of closed overgroups of the upper-triangular subgroup

A closed subgroup scheme of `GLₙ₊₁` containing the upper-triangular subgroup has no
additional rational points in its normalizer. More precisely, its defining Hopf ideal
is fixed by conjugation by `g` exactly when `g` belongs to the subgroup. Equivalently,
the stabilizer of that ideal under the rational-point conjugation action is the
subgroup of rational points it cuts out.

The point subgroup is self-normalizing by the general-linear Tits system and
`TitsSystem.normalizer_eq_of_subgroupB_le`. The converse at the level of ideals uses
conjugation on all value algebras, not point separation. Thus no smoothness or
reducedness assumption on the closed subgroup is required, even in positive
characteristic. These are pointwise statements, not assertions about normalizer
subgroup schemes.

The unit group of the field is assumed nontrivial, as required by the existing Tits
system built from the diagonal-torus normalizer. In particular this applies over
algebraically closed fields.

## References

* T. A. Springer, *Linear Algebraic Groups*, second edition (1998), §8.3.
* J. S. Milne, *Algebraic Groups* (2017), Corollary 17.49.
-/

public section

namespace TauCeti.GeneralLinear.UpperTriangular

universe u

variable {k : Type u} [Field k] [Nontrivial kˣ] {n : ℕ}
variable (I : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k (n + 1)))

/-- The rational-point subgroup of any closed overgroup of the upper-triangular subgroup
is self-normalizing. No reducedness hypothesis on the subgroup scheme is needed. -/
theorem normalizer_quotientPointsSubgroup (hI : I ≤ definingHopfIdeal k (n + 1)) :
    Subgroup.normalizer
        (CommHopfAlgCat.quotientPointsSubgroup (GeneralLinear.coordinateHopfAlgebra k (n + 1)) I
          (CommAlgCat.of k k) : Set _) =
      CommHopfAlgCat.quotientPointsSubgroup (GeneralLinear.coordinateHopfAlgebra k (n + 1)) I
        (CommAlgCat.of k k) := by
  let e := GeneralLinear.pointsMulEquiv (R := k) (A := k) (n + 1)
  let P := CommHopfAlgCat.quotientPointsSubgroup
    (GeneralLinear.coordinateHopfAlgebra k (n + 1)) I (CommAlgCat.of k k)
  have hB : (glTitsSystem k n).subgroupB ≤ P.map e.toMonoidHom := by
    rw [glTitsSystem_subgroupB]
    intro g hg
    apply Subgroup.mem_map_equiv.mpr
    exact CommHopfAlgCat.quotientPointsSubgroup_le_of_le _ hI _
      ((mem_definingPointsSubgroup_iff k (n + 1) _).mpr (by simpa [e] using hg))
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_equiv_normalizer_eq, (glTitsSystem k n).normalizer_eq_of_subgroupB_le hB]

/-- A rational point fixes the defining ideal of a closed overgroup of the upper-triangular
subgroup exactly when it belongs to that closed subgroup. -/
theorem conjugate_eq_self_iff (hI : I ≤ definingHopfIdeal k (n + 1))
    (g : WithConv (GeneralLinear.coordinateHopfAlgebra k (n + 1) →ₐ[k] k)) :
    I.conjugate g = I ↔
      g ∈ CommHopfAlgCat.quotientPointsSubgroup (GeneralLinear.coordinateHopfAlgebra k (n + 1)) I
        (CommAlgCat.of k k) := by
  refine ⟨fun hg ↦ ?_, I.conjugate_eq_self_of_mem_quotientPointsSubgroup⟩
  rw [← normalizer_quotientPointsSubgroup I hI]
  exact I.mem_normalizer_quotientPointsSubgroup_of_conjugate_eq_self g hg

/-- Under rational-point conjugation, the stabilizer of the ideal of a closed overgroup
of the upper-triangular subgroup is precisely its subgroup of rational points. -/
theorem stabilizer_eq_quotientPointsSubgroup (hI : I ≤ definingHopfIdeal k (n + 1)) :
    MulAction.stabilizer (WithConv (GeneralLinear.coordinateHopfAlgebra k (n + 1) →ₐ[k] k)) I =
      CommHopfAlgCat.quotientPointsSubgroup (GeneralLinear.coordinateHopfAlgebra k (n + 1)) I
        (CommAlgCat.of k k) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, HopfIdeal.smul_eq_conjugate, conjugate_eq_self_iff I hI]

end TauCeti.GeneralLinear.UpperTriangular
