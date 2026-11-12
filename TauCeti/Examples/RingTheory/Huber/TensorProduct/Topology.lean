/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Huber.TensorProduct.Topology

/-!
# Examples of the tensor topology

For discrete rings `A`, `B` and `C`, the tensor topology on `B ⊗[A] C` is discrete. The pairs of
definition `(A, 0)`, `(B, 0)` and `(C, 0)` are compatible, so the ideal of definition `J` of the
tensor product is zero and `{0}`, the image of `J`, is open.
-/

open TensorProduct TauCeti.Huber

-- Three discrete rings give the discrete tensor topology.
example {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [DiscreteTopology A] [DiscreteTopology B] [DiscreteTopology C]
    [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
    [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)] :
    @DiscreteTopology (B ⊗[A] C) (tensorTopology A B C) := by
  let D : TensorDatum A B C :=
    { base := .discrete A
      left := .discrete B
      right := .discrete C
      algebraMap_mem_left := by simp
      algebraMap_mem_right := by simp
      map_idealOfDefinition_left := by simp
      map_idealOfDefinition_right := by simp }
  rw [tensorTopology_eq A B C D]
  let _ := D.topology
  have _ := D.isTopologicalRing
  refine discreteTopology_of_isOpen_singleton_zero ?_
  convert D.isOpen_idealImage 1
  ext x
  simp [D, TensorDatum.idealOfDefinition_def, eq_comm]
