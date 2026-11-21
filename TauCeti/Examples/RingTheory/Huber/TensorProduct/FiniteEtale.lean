/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.FiniteEtale
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.Topology.Instances.ZMod

/-!
# Finite étale base change along a nonflat map

Split covers `Fin n → ℤ` of every degree `n` stay finite étale after reduction modulo two,
even though the new base map is neither injective nor flat. The `n = 0` case gives the
zero completed algebra; finiteness does not require surjectivity on spectra.
-/

public section

open TauCeti.Huber

namespace TauCeti.Examples.FiniteEtaleBaseChange

/-- The additive uniformity of the discrete field with two elements. -/
noncomputable local instance modTwoUniformSpace : UniformSpace (ZMod 2) :=
  IsTopologicalAddGroup.rightUniformSpace _
local instance : IsUniformAddGroup (ZMod 2) := isUniformAddGroup_of_addCommGroup

local instance : IsAdicHom (algebraMap ℤ (ZMod 2)) :=
  IsAdicHom.of_discrete_iff.mpr inferInstance

local instance (n : ℕ) : IsAdicHom (algebraMap ℤ (Fin n → ℤ)) :=
  IsAdicHom.of_discrete_iff.mpr inferInstance

/-- Split covers remain finite étale under reduction modulo two. -/
example (n : ℕ) :
    (Pair.completedTensor.inl ℤ (Pair.discrete (ZMod 2))
      ((Pair.discrete ℤ).finiteAlgebra (Fin n → ℤ))).IsFiniteEtale := by
  let f : Pair.Hom (Pair.discrete ℤ) (Pair.discrete (ZMod 2)) :=
    { toRingHom := algebraMap ℤ (ZMod 2)
      continuous_toRingHom := continuous_of_discreteTopology
      map_mem_plus := fun _ _ ↦ by simp }
  exact Pair.completedTensor.isFiniteEtale_inl f rfl
    (Pair.finiteAlgebra.algebraHom (Pair.discrete ℤ) (Fin n → ℤ))
    (Pair.finiteAlgebra.algebraHom_toRingHom _ _)
    (Pair.finiteAlgebra.isFiniteEtale_algebraHom _ _)

/-- The completed base change of the empty cover is still zero. -/
example : Subsingleton (CompletedTensor ℤ (ZMod 2) (Fin 0 → ℤ)) :=
  (Pair.finiteAlgebra.baseChangeEquiv ℤ (ZMod 2) (Fin 0 → ℤ)).symm.injective.subsingleton

/-- The new base map in these checks is genuinely noninjective. -/
example : ¬ Function.Injective (algebraMap ℤ (ZMod 2)) := by
  intro h
  have heq := h (a₁ := 2) (a₂ := 0) (by norm_num; decide)
  norm_num at heq

end TauCeti.Examples.FiniteEtaleBaseChange
