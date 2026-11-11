/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.BaseChange
public import TauCeti.Topology.Algebra.CliffordAlgebra.Basic
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Closed

/-!
# Continuous scalar extension for Clifford point groups

For a continuous homomorphism of commutative rings carrying topologies `K → L`, with `2`
invertible in `K`, the canonical map from a Clifford algebra over `K` to the Clifford algebra of
the scalar-extended quadratic space over `L` is continuous in the module topologies. Its
restrictions to the Lipschitz and Spin groups are therefore continuous as well.

This supplies the topological compatibility needed to compare Clifford point groups over a global
field with their localizations.

For a finite-dimensional quadratic space over a complete nontrivially normed field and a Hausdorff
topological field extension, the canonical map is moreover a closed embedding, being an injective
linear map out of a finite-dimensional space; for a nondegenerate form so is its restriction to the
Spin groups. In particular the real Spin group of a nondegenerate real quadratic form sits in the
complex Spin group of its complexification as a closed subgroup with the subspace topology.

## Main results

* `CliffordAlgebra.continuous_ofBaseChangeAux`: the canonical Clifford-algebra map is continuous.
* `CliffordAlgebra.continuous_lipschitzGroupBaseChange`: scalar extension on Lipschitz groups is
  continuous.
* `CliffordAlgebra.continuous_spinGroupBaseChange`: scalar extension on Spin groups is continuous.
* `CliffordAlgebra.isClosedEmbedding_ofBaseChangeAux`: over a complete field and a Hausdorff
  extension field, the canonical Clifford-algebra map is a closed embedding.
* `CliffordAlgebra.isClosedEmbedding_spinGroupBaseChange`: for a nondegenerate form, scalar
  extension on Spin groups is a closed embedding.
-/

public section

open scoped TensorProduct
open Topology

namespace CliffordAlgebra

universe u v w

variable {K : Type u} {L : Type v} {V : Type w}
  [CommRing K] [CommRing L] [Algebra K L]
  [TopologicalSpace K] [TopologicalSpace L]
  [AddCommGroup V] [Module K V] [Invertible (2 : K)]

/-- The canonical map to the Clifford algebra of a scalar extension is continuous for the module
topologies when the scalar homomorphism is continuous. -/
@[fun_prop]
theorem continuous_ofBaseChangeAux (hKL : Continuous (algebraMap K L))
    (Q : QuadraticForm K V) : Continuous (ofBaseChangeAux L Q) := by
  let F : CliffordAlgebra Q →ₛₗ[algebraMap K L] CliffordAlgebra (Q.baseChange L) :=
    { (ofBaseChangeAux L Q).toLinearMap with
      map_smul' := fun c x =>
        (map_smul (ofBaseChangeAux L Q) c x).trans
          (IsScalarTower.algebraMap_smul L c (ofBaseChangeAux L Q x)).symm }
  let _ : ContinuousAdd (CliffordAlgebra (Q.baseChange L)) :=
    IsModuleTopology.toContinuousAdd L _
  exact IsModuleTopology.continuous_of_linearMapₛₗ hKL F

/-- Extension of scalars is continuous on Lipschitz groups when the scalar homomorphism is
continuous. -/
@[fun_prop]
theorem continuous_lipschitzGroupBaseChange (hKL : Continuous (algebraMap K L))
    (Q : QuadraticForm K V) : Continuous (lipschitzGroupBaseChange (A := L) Q) := by
  apply continuous_induced_rng.mpr
  have hUnits : Continuous (Units.map (ofBaseChangeAux L Q).toMonoidHom) :=
    (continuous_ofBaseChangeAux hKL Q).units_map _
  exact (hUnits.comp continuous_subtype_val).congr fun x => by
    apply Units.ext
    exact (coe_lipschitzGroupBaseChange_apply (A := L) Q x).symm

/-- Extension of scalars is continuous on Spin groups when the scalar homomorphism is continuous. -/
@[fun_prop]
theorem continuous_spinGroupBaseChange (hKL : Continuous (algebraMap K L))
    (Q : QuadraticForm K V) : Continuous (spinGroupBaseChange (A := L) Q) := by
  apply continuous_induced_rng.mpr
  exact ((continuous_ofBaseChangeAux hKL Q).comp continuous_subtype_val).congr fun x =>
    (coe_spinGroupBaseChange_apply (A := L) Q x).symm

section ClosedEmbedding

variable {K : Type u} {L : Type v} {V : Type w}
  [NontriviallyNormedField K] [CompleteSpace K] [Invertible (2 : K)]
  [Field L] [TopologicalSpace L] [IsTopologicalSemiring L] [T2Space L] [Algebra K L]
  [ContinuousSMul K L] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (Q : QuadraticForm K V)

/-- Over a complete nontrivially normed field, the canonical map from the Clifford algebra of a
finite-dimensional quadratic space to that of its extension to a Hausdorff topological field is a
closed embedding: it is an injective linear map out of a finite-dimensional space. -/
theorem isClosedEmbedding_ofBaseChangeAux : IsClosedEmbedding (ofBaseChangeAux L Q) := by
  have : ContinuousSMul K (CliffordAlgebra (Q.baseChange L)) := IsScalarTower.continuousSMul L
  exact LinearMap.isClosedEmbedding_of_injective (f := (ofBaseChangeAux L Q).toLinearMap)
    (LinearMap.ker_eq_bot.2 (ofBaseChangeAux_injective (A := L) Q))

/-- For a nondegenerate form on a finite-dimensional space over a complete nontrivially normed
field, extension of scalars to a Hausdorff topological field is a closed embedding of Spin
groups. -/
theorem isClosedEmbedding_spinGroupBaseChange (hQ : Q.Nondegenerate) :
    IsClosedEmbedding (spinGroupBaseChange (A := L) Q) := by
  have he := isClosedEmbedding_ofBaseChangeAux (L := L) Q
  have hmaps : Set.MapsTo (ofBaseChangeAux L Q) (spinGroup Q) (spinGroup (Q.baseChange L)) :=
    fun x hx => by simpa using (spinGroupBaseChange (A := L) Q ⟨x, hx⟩).2
  refine ⟨?_, ?_⟩
  · convert he.isEmbedding.restrict hmaps using 1
    ext x
    exact coe_spinGroupBaseChange_apply (A := L) Q x
  · -- The range is the preimage of the image of the closed Spin group of `Q`, which is closed.
    convert (he.isClosedMap _ (isClosed_spinGroup Q hQ)).preimage continuous_subtype_val using 1
    ext g
    simp only [Set.mem_range, Set.mem_preimage, Set.mem_image, SetLike.mem_coe]
    refine ⟨fun ⟨x, hx⟩ => ⟨x, x.2, ?_⟩, fun ⟨x, hx, hxg⟩ => ⟨⟨x, hx⟩, Subtype.ext ?_⟩⟩
    · rw [← hx, coe_spinGroupBaseChange_apply]
    · rw [coe_spinGroupBaseChange_apply, hxg]

end ClosedEmbedding

end CliffordAlgebra
