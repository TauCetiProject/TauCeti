/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Basic
public import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine

import TauCeti.GroupTheory.Amenable.Affine
import TauCeti.GroupTheory.Amenable.Abelian
import TauCeti.GroupTheory.Amenable.Extension
import TauCeti.Topology.Compactification.OnePoint.Stabilizer

/-!
# Amenable stabilizers on the projective line

Point stabilizers for the action of `PGL(2, K)` on `OnePoint K` are amenable for
every group topology: transitivity identifies each with the stabilizer of infinity,
and `OnePoint.pglStabilizerInftyEquiv` identifies the latter with the affine group.
The stabilizers in `GL(2, K)` are amenable too, since the kernel of the projection
to `PGL(2, K)` is central. Thus every subgroup of `GL(2, K)` has amenable point
stabilizers, including subgroups of `SL(2, ℤ)` acting on the real projective line.

We first establish amenability with the discrete topology; the subgroup transfer
then applies to every group topology on the represented group.
The native projective-line stabilizer equivalence and the amenable-extension
theorem provide the two steps of the proof.
-/

public section

open Matrix MulAction
open scoped MatrixGroups IsMulCommutative

namespace OnePoint

variable {K : Type*} [Field K] [DecidableEq K]

/-- Every projective-linear point stabilizer is amenable for every group topology. -/
theorem amenable_pgl_stabilizer [TopologicalSpace PGL(2, K)] [IsTopologicalGroup PGL(2, K)]
    (x : OnePoint K) : TauCeti.Amenable (stabilizer PGL(2, K) x) := by
  let : TopologicalSpace (K ≃ᵃ[K] K) := ⊥
  let : DiscreteTopology (K ≃ᵃ[K] K) := ⟨rfl⟩
  have : IsPretransitive (GL (Fin 2) K) (OnePoint K) :=
    isPretransitive_of_is_two_pretransitive
  obtain ⟨g, hg⟩ := exists_smul_eq (GL (Fin 2) K) (∞ : OnePoint K) x
  have hpg : ProjGenLinGroup.mk g • (∞ : OnePoint K) = x := by simpa using hg
  let e := (stabilizerEquivStabilizer hpg.symm).symm.trans
    (pglStabilizerInftyEquiv (K := K))
  exact TauCeti.Amenable.of_injective e.toMonoidHom e.injective

/-- Every general-linear point stabilizer is amenable for every group topology. -/
theorem amenable_gl_stabilizer [TopologicalSpace (GL (Fin 2) K)]
    [IsTopologicalGroup (GL (Fin 2) K)] (x : OnePoint K) :
    TauCeti.Amenable (stabilizer (GL (Fin 2) K) x) := by
  apply TauCeti.Amenable.of_discrete
  let : TopologicalSpace (stabilizer (GL (Fin 2) K) x) := ⊥
  let : DiscreteTopology (stabilizer (GL (Fin 2) K) x) := ⟨rfl⟩
  let : TopologicalSpace (GL (Fin 2) K) := ⊥
  let : DiscreteTopology (GL (Fin 2) K) := ⟨rfl⟩
  let : TopologicalSpace PGL(2, K) := ⊥
  let : DiscreteTopology PGL(2, K) := ⟨rfl⟩
  have := amenable_pgl_stabilizer x
  let φ : stabilizer (GL (Fin 2) K) x →* stabilizer PGL(2, K) x :=
    (ProjGenLinGroup.mk.subgroupComap _).comp
      (MulEquiv.subgroupCongr (comap_mk_stabilizer x).symm).toMonoidHom
  have hφ (g : stabilizer (GL (Fin 2) K) x) : (φ g : PGL(2, K)) = ProjGenLinGroup.mk g := rfl
  let ψ : φ.ker →* Subgroup.center (GL (Fin 2) K) :=
    ((stabilizer (GL (Fin 2) K) x).subtype.comp φ.ker.subtype).codRestrict
      (Subgroup.center (GL (Fin 2) K)) fun g => by
        apply ProjGenLinGroup.mk_eq_one.mp
        simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, hφ, OneMemClass.coe_one] using
          congrArg Subtype.val (MonoidHom.mem_ker.mp g.property)
  have hψ : Function.Injective ψ := by
    apply (MonoidHom.injective_codRestrict _ _ _).2
    exact (stabilizer (GL (Fin 2) K) x).subtype_injective.comp φ.ker.subtype_injective
  have : TauCeti.Amenable φ.ker := TauCeti.Amenable.of_injective ψ hψ
  exact TauCeti.Amenable.of_ker_le_range φ.ker.subtype φ (by simp)

end OnePoint

namespace MonoidHom

/-- An injective matrix representation has amenable projective-line point stabilizers.
The subgroup is written as a comap so that no choice of a pulled-back action is needed.
Its amenability holds for every group topology on the represented group. -/
theorem amenable_comap_onePoint_stabilizer {K : Type*} [Field K] [DecidableEq K]
    {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (φ : G →* GL (Fin 2) K) (hφ : Function.Injective φ)
    (x : OnePoint K) : TauCeti.Amenable ((stabilizer (GL (Fin 2) K) x).comap φ) := by
  let : TopologicalSpace (GL (Fin 2) K) := ⊥
  let : DiscreteTopology (GL (Fin 2) K) := ⟨rfl⟩
  have := OnePoint.amenable_gl_stabilizer x
  exact TauCeti.Amenable.of_injective (φ.subgroupComap _)
    (φ.subgroupComap_injective _ hφ)

end MonoidHom
