/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Action
public import TauCeti.Topology.Algebra.CliffordAlgebra.Basic
public import TauCeti.Topology.Algebra.Module.GeneralLinearGroup

/-!
# Continuity of the Lipschitz action

The Lipschitz group of a finite-dimensional quadratic space acts continuously on the space by
twisted Clifford conjugation. Consequently its vector representation into the orthogonal group is
continuous for the canonical topologies: the subgroup topology on the Lipschitz group inside the
units of the Clifford algebra, and the subgroup topology on the orthogonal group inside the linear
automorphism group.

Joint continuity holds over a commutative base ring when the quadratic space carries its module
topology and multiplication in the Clifford algebra is continuous. Over a topological field, the
representation is continuous when the quadratic space is finite-dimensional and carries its module
topology.

## Main results

* `CliffordAlgebra.continuous_lipschitzVectorAction`: the action is jointly continuous in the
  Lipschitz element and the vector.
* `CliffordAlgebra.instContinuousSMulLipschitzGroup`: the standard Lipschitz-group action is a
  continuous scalar action.
* `CliffordAlgebra.continuous_lipschitzVectorAction_apply`: the image of a fixed vector varies
  continuously with the Lipschitz element.
* `CliffordAlgebra.continuous_lipschitzVectorAction_toLinearMap`: the underlying endomorphism
  varies continuously.
* `CliffordAlgebra.continuous_lipschitzVectorAction_linearEquiv`: the automorphism-valued action
  varies continuously.
* `CliffordAlgebra.continuous_lipschitzToOrthogonal`: the vector representation is continuous.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
-/

public section

namespace CliffordAlgebra

open TauCeti

noncomputable section

section Action

variable {R V : Type*} [CommRing R] [TopologicalSpace R]
  [Invertible (2 : R)] [AddCommGroup V] [Module R V]
  [TopologicalSpace V] [IsModuleTopology R V]
  (Q : QuadraticForm R V) [ContinuousMul (CliffordAlgebra Q)]

/-- The action of the Lipschitz group on its quadratic space is jointly continuous. -/
@[fun_prop]
theorem continuous_lipschitzVectorAction :
    Continuous (fun p : lipschitzGroup Q × V => lipschitzVectorAction Q p.1 p.2) := by
  have hunits : Continuous (fun p : lipschitzGroup Q × V =>
      ((p.1 : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ)) :=
    continuous_subtype_val.comp continuous_fst
  have hval : Continuous (fun p : lipschitzGroup Q × V =>
      (((p.1 : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) :=
    Units.continuous_val.comp hunits
  have hinvUnits : Continuous (fun p : lipschitzGroup Q × V =>
      (((p.1 : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ)⁻¹ :
        (CliffordAlgebra Q)ˣ)) :=
    continuous_inv.comp hunits
  have hinv : Continuous (fun p : lipschitzGroup Q × V =>
      (((((p.1 : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ)⁻¹ :
        (CliffordAlgebra Q)ˣ)) : CliffordAlgebra Q)) :=
    Units.continuous_val.comp hinvUnits
  have hι : Continuous (fun p : lipschitzGroup Q × V => ι Q p.2) :=
    (continuous_ι Q).comp continuous_snd
  have hprod : Continuous (fun p : lipschitzGroup Q × V =>
      involute (Q := Q)
          (((p.1 : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        ι Q p.2 *
        (((((p.1 : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ)⁻¹ :
          (CliffordAlgebra Q)ˣ)) : CliffordAlgebra Q)) :=
    (((continuous_involute Q).comp hval).mul hι).mul hinv
  have hvector := (continuous_ιInv Q).comp hprod
  refine hvector.congr fun p => ?_
  rw [← ιInv_ι Q (lipschitzVectorAction Q p.1 p.2),
    ι_lipschitzVectorAction_apply]
  rfl

/-- The standard action of the Lipschitz group on its quadratic space is continuous. -/
instance instContinuousSMulLipschitzGroup : ContinuousSMul (lipschitzGroup Q) V where
  continuous_smul := (continuous_lipschitzVectorAction Q).congr fun p => by
    exact (lipschitzGroup_smul_apply Q p.1 p.2).symm

/-- For a fixed vector, its image under a Lipschitz element varies continuously. -/
@[fun_prop]
theorem continuous_lipschitzVectorAction_apply (v : V) :
    Continuous (fun x : lipschitzGroup Q => lipschitzVectorAction Q x v) := by
  have hpair : Continuous (fun x : lipschitzGroup Q => (x, v)) := by fun_prop
  exact ((continuous_lipschitzVectorAction Q).comp hpair).congr fun _ => rfl

end Action

section FiniteDimensional

variable {K V : Type*} [Field K] [TopologicalSpace K] [IsTopologicalSemiring K]
  [Invertible (2 : K)] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [TopologicalSpace V] [IsModuleTopology K V]
  (Q : QuadraticForm K V)

local instance : IsTopologicalRing K := IsTopologicalSemiring.toIsTopologicalRing inferInstance

/-- The underlying endomorphism of the Lipschitz action varies continuously. -/
@[fun_prop]
theorem continuous_lipschitzVectorAction_toLinearMap :
    Continuous (fun x : lipschitzGroup Q =>
      (lipschitzVectorAction Q x : Module.End K V)) := by
  let b := Module.finBasis K V
  rw [b.continuous_iff_apply]
  intro j
  exact (continuous_lipschitzVectorAction_apply Q (b j)).congr fun _ => rfl

/-- The linear-automorphism-valued Lipschitz action varies continuously. -/
@[fun_prop]
theorem continuous_lipschitzVectorAction_linearEquiv :
    Continuous (fun x : lipschitzGroup Q => lipschitzVectorAction Q x) := by
  rw [continuous_linearEquiv_iff]
  constructor
  · exact continuous_lipschitzVectorAction_toLinearMap Q
  · have h := (continuous_lipschitzVectorAction_toLinearMap Q).comp
        (continuous_inv : Continuous fun x : lipschitzGroup Q => x⁻¹)
    convert h using 1
    funext x
    congr 1
    apply inv_eq_of_mul_eq_one_left
    rw [← lipschitzVectorAction_mul, inv_mul_cancel, lipschitzVectorAction_one]
    rfl

/-- The twisted-conjugation homomorphism from the Lipschitz group to the orthogonal group is
continuous for the canonical subgroup topologies. -/
@[fun_prop]
theorem continuous_lipschitzToOrthogonal : Continuous (lipschitzToOrthogonal Q) := by
  apply continuous_induced_rng.mpr
  convert continuous_lipschitzVectorAction_linearEquiv Q using 1
  funext x
  apply LinearEquiv.ext
  intro v
  exact coe_lipschitzToOrthogonal_apply Q x v

end FiniteDimensional

end

end CliffordAlgebra
