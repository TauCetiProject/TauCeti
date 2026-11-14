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

## Main results

* `OnePoint.amenable_pgl_stabilizer`, `OnePoint.amenable_gl_stabilizer`: point stabilizers on
  `OnePoint K` in `PGL(2, K)` and `GL(2, K)` are amenable.
* `Projectivization.amenable_gl_stabilizer`, `Projectivization.amenable_sl_stabilizer`: point
  stabilizers on `ℙ K (Fin 2 → K)` in `GL(2, K)` and `SL(2, K)` are amenable without
  `[DecidableEq K]`.
* `MonoidHom.amenable_comap_onePoint_stabilizer`,
  `MonoidHom.amenable_comap_projectivization_stabilizer`: preimages of point stabilizers along an
  injective homomorphism into `GL(2, K)` are amenable.
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

namespace Projectivization

open scoped LinearAlgebra.Projectivization

variable {K : Type*} [Field K]

/-- Every general-linear point stabilizer on the projective line `ℙ K (Fin 2 → K)` is amenable
for every group topology. -/
theorem amenable_gl_stabilizer [TopologicalSpace (GL (Fin 2) K)]
    [IsTopologicalGroup (GL (Fin 2) K)] (x : ℙ K (Fin 2 → K)) :
    TauCeti.Amenable (stabilizer (GL (Fin 2) K) x) := by
  classical
  have hstab : stabilizer (GL (Fin 2) K) x =
      stabilizer (GL (Fin 2) K) ((OnePoint.equivProjectivization K).symm x) := by
    ext g
    simp only [mem_stabilizer_iff]
    rw [← (OnePoint.equivProjectivization K).injective.eq_iff,
      OnePoint.equivProjectivization_smul, Equiv.apply_symm_apply]
  exact hstab ▸ OnePoint.amenable_gl_stabilizer _

/-- Every special-linear point stabilizer on the projective line `ℙ K (Fin 2 → K)` is amenable
for every group topology. -/
theorem amenable_sl_stabilizer [TopologicalSpace SL(2, K)] [IsTopologicalGroup SL(2, K)]
    (x : ℙ K (Fin 2 → K)) :
    TauCeti.Amenable (stabilizer SL(2, K) x) := by
  let : TopologicalSpace (GL (Fin 2) K) := ⊥
  let : DiscreteTopology (GL (Fin 2) K) := ⟨rfl⟩
  have := amenable_gl_stabilizer x
  have hstab : stabilizer SL(2, K) x =
      (stabilizer (GL (Fin 2) K) x).comap Matrix.SpecialLinearGroup.toGL := by
    ext g
    -- Both actions multiply representatives on `ℙ K (Fin 2 → K)` by the underlying matrix.
    have hsmul : Matrix.SpecialLinearGroup.toGL g • x = g • x := rfl
    simp [mem_stabilizer_iff, hsmul]
  exact hstab ▸ TauCeti.Amenable.of_injective
    (Matrix.SpecialLinearGroup.toGL.subgroupComap _)
    (Matrix.SpecialLinearGroup.toGL.subgroupComap_injective _
      Matrix.SpecialLinearGroup.toGL_injective)

end Projectivization

namespace MonoidHom

open scoped LinearAlgebra.Projectivization

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

/-- An injective `2 × 2` matrix representation has amenable point stabilizers on the projective
line `ℙ K (Fin 2 → K)`, for every group topology on the represented group. -/
theorem amenable_comap_projectivization_stabilizer {K : Type*} [Field K]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G →* GL (Fin 2) K) (hφ : Function.Injective φ) (x : ℙ K (Fin 2 → K)) :
    TauCeti.Amenable ((stabilizer (GL (Fin 2) K) x).comap φ) := by
  let : TopologicalSpace (GL (Fin 2) K) := ⊥
  let : DiscreteTopology (GL (Fin 2) K) := ⟨rfl⟩
  have := Projectivization.amenable_gl_stabilizer x
  exact TauCeti.Amenable.of_injective (φ.subgroupComap _)
    (φ.subgroupComap_injective _ hφ)

end MonoidHom
