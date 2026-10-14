/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction
public import TauCeti.RepresentationTheory.InvariantForm
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.Algebra.Coalgebra.Subcomodule.PointSeparation

/-!
# Orthogonal subrepresentations

For a reduced affine group of finite type over an algebraically closed field, a bilinear
form invariant under rational points makes the orthogonal complement of a subrepresentation
a subrepresentation. Point separation retains the full comodule structure, rather than just
stability under rational points. This permits orthogonal subquotients in symplectic
representations, including in characteristic two.

## References

* J. S. Milne, *Algebraic Groups* (2017), §16 (representations and Lie--Kolchin).
-/

public section

open scoped TensorProduct

namespace TauCeti.Subcomodule

variable {k H M : Type*} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsReduced H] [AddCommGroup M] [Module k M] [Comodule k H M]

/-- The orthogonal complement of a subrepresentation for a rational-point-invariant form,
with its induced comodule structure. -/
noncomputable def orthogonal (N : Subcomodule k H M) (B : LinearMap.BilinForm k M)
    (hB : Representation.IsInvariantForm (Comodule.basePointsRepresentation (H := H) M) B) :
    Subcomodule k H M :=
  ofEndOfPointStable (K := k) (B.orthogonal N.toSubmodule) fun g m hm ↦ by
    rw [Comodule.endOfPoint_tmul, one_smul,
      Comodule.endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation]
    apply Submodule.tmul_mem_baseChange_of_mem
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hm ⊢
    intro n hn
    simpa only [inv_inv] using (hB.apply_left (WithConv.toConv g)⁻¹ n m).symm.trans
      (hm _ (Comodule.basePointsRepresentation_mem N _ hn))

/-- The orthogonal subcomodule has the usual orthogonal complement as underlying subspace. -/
@[simp]
theorem orthogonal_toSubmodule (N : Subcomodule k H M) (B : LinearMap.BilinForm k M)
    (hB : Representation.IsInvariantForm (Comodule.basePointsRepresentation (H := H) M) B) :
    (N.orthogonal B hB).toSubmodule = B.orthogonal N.toSubmodule := by
  rw [orthogonal, ofEndOfPointStable_toSubmodule]

/-- Membership in the orthogonal subrepresentation is vanishing of all pairings with it. -/
@[simp]
theorem mem_orthogonal (N : Subcomodule k H M) (B : LinearMap.BilinForm k M)
    (hB : Representation.IsInvariantForm (Comodule.basePointsRepresentation (H := H) M) B)
    (m : M) : m ∈ N.orthogonal B hB ↔ ∀ n ∈ N, B n m = 0 := by
  rw [← mem_toSubmodule, orthogonal_toSubmodule, LinearMap.BilinForm.mem_orthogonal_iff]
  rfl

end TauCeti.Subcomodule
