/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FixedSubmodule.Permutation
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.DiagramAutomorphism

/-!
# The integral fixed lattice of a native diagram automorphism

The actual coweight map of the pinned root datum has an integral fixed basis
consisting of sums of simple coroots over node orbits. Choosing one node per
orbit gives a retraction of the ambient cocharacter lattice onto this fixed
submodule. No orbit cardinality is inverted. This is the lattice prerequisite
for the orbit-sum Cartan construction; identification with a fixed Lie algebra
is a separate step.
-/

public noncomputable section

namespace TauCeti.DynkinType

variable {t : DynkinType} (ht : t.Valid) {σ : Equiv.Perm (Fin t.rank)}

/-- The forward cocharacter action and the native transpose action have equal fixed lattices. -/
theorem diagramAut_fixedSubmodule_symm (hσ : σ ∈ t.diagramSymmetry) :
    (RootPairing.Equiv.coweightEquiv (diagramAut ht hσ)).symm.toLinearMap.fixedSubmodule =
      (RootPairing.Equiv.coweightEquiv (diagramAut ht hσ)).toLinearMap.fixedSubmodule :=
  LinearEquiv.fixedSubmodule_symm_eq _

/-- Transport the orbit indicator basis to the actual native fixed submodule. -/
def diagramFixedBasis (hσ : σ ∈ t.diagramSymmetry) :
    Module.Basis (Quotient (Equiv.Perm.SameCycle.setoid σ)) ℤ
      (RootPairing.Equiv.coweightEquiv (diagramAut ht hσ)).toLinearMap.fixedSubmodule :=
  (Equiv.Perm.permutationFixedBasis (R := ℤ) σ).map
    (LinearEquiv.ofEq _ _ (by rw [diagramAut_coweightEquiv]))

/-- Native fixed coordinates recover each ambient simple-coroot coordinate. -/
@[simp]
theorem diagramFixedBasis_repr (hσ : σ ∈ t.diagramSymmetry)
    (v : (RootPairing.Equiv.coweightEquiv (diagramAut ht hσ)).toLinearMap.fixedSubmodule)
    (i : Fin t.rank) :
    (diagramFixedBasis ht hσ).repr v (Quotient.mk _ i) = v.val i := by
  simp only [diagramFixedBasis, Module.Basis.map_repr, LinearEquiv.trans_apply,
    LinearEquiv.ofEq_symm, Equiv.Perm.permutationFixedBasis_repr,
    LinearEquiv.coe_ofEq_apply]

/-- A native basis vector is one on its node orbit and zero elsewhere. -/
@[simp]
theorem diagramFixedBasis_apply (hσ : σ ∈ t.diagramSymmetry)
    [DecidableEq (Quotient (Equiv.Perm.SameCycle.setoid σ))]
    (c : Quotient (Equiv.Perm.SameCycle.setoid σ)) (i : Fin t.rank) :
    (diagramFixedBasis ht hσ c).val i = if Quotient.mk _ i = c then 1 else 0 := by
  simp only [diagramFixedBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Equiv.Perm.permutationFixedBasis_apply]

/-- Native fixed basis vectors are literal sums of the pinned simple coroots. -/
theorem diagramFixedBasis_eq_sum_coroot (hσ : σ ∈ t.diagramSymmetry)
    [DecidableEq (Quotient (Equiv.Perm.SameCycle.setoid σ))]
    (c : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    (diagramFixedBasis ht hσ c).val =
      ∑ i ∈ Finset.univ.filter (fun i ↦ Quotient.mk _ i = c),
        (t.simplyConnectedRootDatum ht).coroot (t.simpleIndex ht i) := by
  simp only [diagramFixedBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    coroot_simpleIndex]
  exact Equiv.Perm.permutationFixedBasis_eq_sum σ c

/-- Read chosen node representatives and extend their coordinates over the node orbits. -/
def diagramFixedProjection (hσ : σ ∈ t.diagramSymmetry)
    (r : Quotient (Equiv.Perm.SameCycle.setoid σ) → Fin t.rank) :
    (Fin t.rank → ℤ) →ₗ[ℤ]
      (RootPairing.Equiv.coweightEquiv (diagramAut ht hσ)).toLinearMap.fixedSubmodule :=
  (LinearEquiv.ofEq _ _ (by rw [diagramAut_coweightEquiv ht hσ])).toLinearMap.comp
    (Equiv.Perm.permutationFixedProjection σ r)

/-- The chosen representative determines every coordinate of the native projection. -/
@[simp]
theorem diagramFixedProjection_apply (hσ : σ ∈ t.diagramSymmetry)
    (r : Quotient (Equiv.Perm.SameCycle.setoid σ) → Fin t.rank)
    (v : Fin t.rank → ℤ) (i : Fin t.rank) :
    (diagramFixedProjection ht hσ r v).val i = v (r (Quotient.mk _ i)) := by
  simp only [diagramFixedProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_ofEq_apply, Equiv.Perm.permutationFixedProjection_apply]

/-- A section of the node quotient makes the native projection a retraction. -/
@[simp]
theorem diagramFixedProjection_fixed (hσ : σ ∈ t.diagramSymmetry)
    (r : Quotient (Equiv.Perm.SameCycle.setoid σ) → Fin t.rank)
    (hr : Function.RightInverse r (Quotient.mk (Equiv.Perm.SameCycle.setoid σ)))
    (v : (RootPairing.Equiv.coweightEquiv (diagramAut ht hσ)).toLinearMap.fixedSubmodule) :
    diagramFixedProjection ht hσ r v.val = v := by
  apply Subtype.ext
  funext i
  rw [diagramFixedProjection_apply, ← diagramFixedBasis_repr ht hσ v,
    hr, diagramFixedBasis_repr]

/-- The native fixed-lattice projection splits its actual inclusion into the cocharacter lattice. -/
theorem diagramFixedProjection_comp_subtype (hσ : σ ∈ t.diagramSymmetry)
    (r : Quotient (Equiv.Perm.SameCycle.setoid σ) → Fin t.rank)
    (hr : Function.RightInverse r (Quotient.mk (Equiv.Perm.SameCycle.setoid σ))) :
    (diagramFixedProjection ht hσ r).comp
      (RootPairing.Equiv.coweightEquiv (diagramAut ht hσ)).toLinearMap.fixedSubmodule.subtype =
      LinearMap.id := by
  ext v i
  exact congrFun (congrArg Subtype.val (diagramFixedProjection_fixed ht hσ r hr v)) i

end TauCeti.DynkinType
