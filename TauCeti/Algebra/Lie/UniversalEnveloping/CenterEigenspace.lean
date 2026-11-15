/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import TauCeti.Algebra.Lie.UniversalEnveloping.Module

/-!
# Simultaneous eigenspaces of the centre of the enveloping algebra

Let `M` be a module over a Lie algebra `L` over a commutative ring `R`, and let
`Z(U(L)) = Subalgebra.center R (UniversalEnvelopingAlgebra R L)` be the centre of the universal
enveloping algebra. For a candidate eigenvalue function `χ : Z(U(L)) → R`, the **centre
eigenspace**

`M_χ = {m ∈ M | z • m = χ z • m for every z ∈ Z(U(L))}`

is a Lie submodule of `M`, because a central element acts by a map commuting with the Lie action
(`TauCeti.UniversalEnvelopingAlgebra.representation_lie_of_mem_center`). It is the simultaneous
eigenspace of the commuting family of operators by which the centre acts, in the same way that
Mathlib's `LieModule.genWeightSpace` is the simultaneous generalized eigenspace of a nilpotent Lie
algebra. The eigenvalue function is an arbitrary function, as for weight spaces; the central
characters of highest weight modules (`TauCeti.vermaCentralCharacter`) are the functions it is used
with.

Over a domain, and for a torsion-free module, centre eigenspaces for distinct eigenvalue functions
are independent (`TauCeti.UniversalEnvelopingAlgebra.iSupIndep_centerEigenspace`): this is
Mathlib's independence of simultaneous generalized eigenspaces of a commuting family,
`Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo`, restricted to genuine
eigenspaces. A homomorphism of Lie modules intertwines the actions of the centre, so it carries
each centre eigenspace into the corresponding one (`LieModuleHom.map_centerEigenspace_le`).

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.centerEigenspace`: the simultaneous eigenspace of the centre
  of `U(L)` for an eigenvalue function, as a Lie submodule.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.mem_centerEigenspace`: membership is the eigenvector
  equation for every central element.
* `LieModuleHom.map_centerEigenspace_le`: Lie module homomorphisms preserve centre eigenspaces.
* `TauCeti.UniversalEnvelopingAlgebra.centerEigenspace_eq_top_iff`: the centre acts on the whole
  module through `χ` exactly when the centre eigenspace is everything.
* `TauCeti.UniversalEnvelopingAlgebra.iSupIndep_centerEigenspace`: centre eigenspaces for distinct
  eigenvalue functions are independent.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.2.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open Module

universe u v w x

variable (R : Type u) (L : Type v) (M : Type w) (N : Type x)
variable [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- The **centre eigenspace** of a Lie module for an eigenvalue function `χ` on the centre of the
universal enveloping algebra: the Lie submodule of vectors on which every central element `z` of
`U(L)` acts as multiplication by `χ z`. It is a Lie submodule because central elements act by maps
commuting with the Lie action. -/
noncomputable def centerEigenspace (χ : Subalgebra.center R U → R) : LieSubmodule R L M where
  toSubmodule := ⨅ z : Subalgebra.center R U, (representation R L M z).eigenspace (χ z)
  lie_mem {x m} hm := by
    simp only [Submodule.mem_carrier, SetLike.mem_coe, Submodule.mem_iInf,
      End.mem_eigenspace_iff] at hm ⊢
    intro z
    rw [representation_lie_of_mem_center R L M z.2, hm z, lie_smul]

variable {R L M N}

/-- A vector lies in the centre eigenspace for `χ` exactly when every central element `z` of
`U(L)` acts on it as multiplication by `χ z`. -/
@[simp]
theorem mem_centerEigenspace {χ : Subalgebra.center R U → R} {m : M} :
    m ∈ centerEigenspace R L M χ ↔
      ∀ z : Subalgebra.center R U, representation R L M (z : U) m = χ z • m := by
  simp [← LieSubmodule.mem_toSubmodule, centerEigenspace]

/-- The underlying submodule of a centre eigenspace is the intersection of the eigenspaces of the
operators by which the central elements act. -/
theorem centerEigenspace_toSubmodule (χ : Subalgebra.center R U → R) :
    (centerEigenspace R L M χ).toSubmodule =
      ⨅ z : Subalgebra.center R U, (representation R L M (z : U)).eigenspace (χ z) := by
  ext m
  simp [Submodule.mem_iInf]

/-- **The centre acts on a Lie module through `χ` exactly when the centre eigenspace for `χ` is
the whole module.** -/
theorem centerEigenspace_eq_top_iff {χ : Subalgebra.center R U → R} :
    centerEigenspace R L M χ = ⊤ ↔
      ∀ (z : Subalgebra.center R U) (m : M), representation R L M (z : U) m = χ z • m := by
  rw [eq_top_iff]
  exact ⟨fun h z m ↦ mem_centerEigenspace.mp (h (LieSubmodule.mem_top m)) z,
    fun h m _ ↦ mem_centerEigenspace.mpr fun z ↦ h z m⟩

/-- **A homomorphism of Lie modules carries a centre eigenspace into the centre eigenspace of the
same eigenvalue function**, since it intertwines the actions of `U(L)`. -/
theorem _root_.LieModuleHom.map_centerEigenspace_le (f : M →ₗ⁅R,L⁆ N)
    (χ : Subalgebra.center R U → R) :
    (centerEigenspace R L M χ).map f ≤ centerEigenspace R L N χ := by
  rw [LieSubmodule.map_le_iff_le_comap]
  intro m hm
  rw [LieSubmodule.mem_comap, mem_centerEigenspace]
  intro z
  rw [← map_representation, mem_centerEigenspace.mp hm z, map_smul]

/-- A Lie submodule is contained in a centre eigenspace exactly when a Lie-generating set of it
is: centrality propagates the eigenvector equation from generators. -/
theorem lieSpan_le_centerEigenspace_iff {χ : Subalgebra.center R U → R} {S : Set M} :
    LieSubmodule.lieSpan R L S ≤ centerEigenspace R L M χ ↔
      ∀ v ∈ S, ∀ z : Subalgebra.center R U, representation R L M (z : U) v = χ z • v := by
  rw [LieSubmodule.lieSpan_le]
  simp only [Set.subset_def, SetLike.mem_coe, mem_centerEigenspace]

section Independence

variable [IsDomain R] [IsTorsionFree R M]

/-- **Centre eigenspaces for distinct eigenvalue functions are independent**: they form an
independent family of Lie submodules. The operators by which the central elements act commute
with each other, so this is the independence of simultaneous generalized eigenspaces of a
commuting family, restricted to genuine eigenspaces. -/
theorem iSupIndep_centerEigenspace :
    iSupIndep fun χ : Subalgebra.center R U → R ↦ centerEigenspace R L M χ := by
  rw [← LieSubmodule.iSupIndep_toSubmodule]
  simp only [centerEigenspace_toSubmodule]
  refine (End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (fun z : Subalgebra.center R U ↦ representation R L M (z : U)) fun z w φ ↦
      End.mapsTo_maxGenEigenspace_of_comm ?_ φ).mono fun χ ↦
    iInf_mono fun z ↦ End.eigenspace_le_maxGenEigenspace
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, (Subalgebra.mem_center_iff.mp z.2) (w : U)]

/-- Centre eigenspaces for distinct eigenvalue functions meet only in zero. -/
theorem disjoint_centerEigenspace {χ₁ χ₂ : Subalgebra.center R U → R} (h : χ₁ ≠ χ₂) :
    Disjoint (centerEigenspace R L M χ₁) (centerEigenspace R L M χ₂) :=
  iSupIndep_centerEigenspace.pairwiseDisjoint h

end Independence

end TauCeti.UniversalEnvelopingAlgebra
