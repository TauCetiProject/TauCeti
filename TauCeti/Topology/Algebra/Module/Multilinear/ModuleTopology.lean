/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.LinearAlgebra.Multilinear.Basis

/-!
# Multilinear maps out of finite modules with the module topology

A multilinear map `f` out of finitely many finite modules `M i` over a topological commutative
ring `R`, each with its module topology, into any topological `R`-module is continuous
(`IsModuleTopology.continuous_multilinearMap`). Choose linear surjections `φ i : Rⁿⁱ → M i`; their
product `Pi.map φ` is an open quotient map, so it suffices that `f ∘ Pi.map φ` is continuous. In
the standard bases this is the finite sum `∑ s, (∏ i, x i (s i)) • f (fun i ↦ φ i (single (s i)))`
of products of coordinates. This is a multilinear analogue of Mathlib's continuity of bilinear
maps out of finite modules (`IsModuleTopology.continuous_bilinear_of_finite_left`).

## Main results

* `IsModuleTopology.continuous_multilinearMap`: a multilinear map out of finitely many finite
  modules with their module topologies is continuous.
-/

public section

open Module

namespace IsModuleTopology

variable {R ι N : Type*} {M : ι → Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [Finite ι] [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, TopologicalSpace (M i)]
  [∀ i, IsModuleTopology R (M i)] [∀ i, Module.Finite R (M i)] [AddCommMonoid N] [Module R N]
  [TopologicalSpace N] [ContinuousAdd N] [ContinuousSMul R N]

/-- A multilinear map out of finitely many finite modules, each with its module topology, into a
topological `R`-module with continuous addition and scalar multiplication is continuous. -/
theorem continuous_multilinearMap (f : MultilinearMap (RingHom.id R) M N) : Continuous f := by
  classical
  have := Fintype.ofFinite ι
  choose n φ hφ using fun i ↦ Module.Finite.exists_fin' R (M i)
  have hq : IsOpenQuotientMap (Pi.map fun i ↦ φ i) :=
    .piMap fun i ↦ isOpenQuotientMap_of_surjective (hφ i)
  rw [← hq.continuous_comp_iff, show ⇑f ∘ Pi.map (fun i ↦ φ i) = f.compLinearMap φ from
    funext fun x ↦ (f.compLinearMap_apply φ x).symm]
  have hf : ⇑(f.compLinearMap φ) = fun x ↦ ∑ s : ∀ i, Fin (n i),
      (∏ i, x i (s i)) • f.compLinearMap φ fun i ↦ Pi.basisFun R (Fin (n i)) (s i) :=
    funext fun x ↦ by
      simpa using (f.compLinearMap φ).apply_eq_sum_prod_repr_smul (fun i ↦ Pi.basisFun R _) x
  rw [hf]
  exact continuous_finsetSum _ fun s _ ↦ (continuous_finsetProd _ fun i _ ↦
    (continuous_apply (s i)).comp (continuous_apply i)).smul continuous_const

end IsModuleTopology
