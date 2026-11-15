/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Logic.Small.Basic
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import TauCeti.Topology.Algebra.Module.Compact

/-!
# Duality for compact Hausdorff linearly topologized vector spaces

Let `k` be a field equipped with the discrete topology and `V` a compact Hausdorff linearly
topologized `k`-vector space (`[IsLinearTopology k V]`). In Lefschetz's linear topology (and in the
special case `k = 𝔽_p`, Pontryagin duality for elementary abelian profinite `p`-groups), `V` is
canonically dual to its discrete vector space `D = (V →L[k] k)` of continuous `k`-linear
functionals, and choosing a `k`-basis of `D` identifies `V` topologically and `k`-linearly with a
product `I → k`.

Concretely:

1. **Separation of points** (`TauCeti.IsLinearTopology.exists_continuousLinearMap_ne_zero`): for any
   `T1` linearly topologized vector space `V` over a discrete division ring `k` and any `v ≠ 0`, an
   open subspace `U ≤ V` missing `v` admits a `k`-linear functional vanishing on `U` and nonzero at
   `v`; openness of `U` makes that functional continuous.
2. **Surjectivity on finite linearly independent families**
   (`TauCeti.IsLinearTopology.surjective_pi_of_linearIndependent`): if `(φ_i)_{i ∈ s}` is a finite
   `k`-linearly independent family in `V →L[k] k`, the joint evaluation `V → (s → k)` is
   surjective, since a nontrivial `k`-linear functional vanishing on its image would produce a
   nontrivial `k`-linear relation among the `φ_i`.
3. **Topological product decomposition**
   (`TauCeti.IsLinearTopology.exists_continuousLinearEquiv_pi`): when `V : Type v` is compact and
   Hausdorff, evaluating on a `k`-basis `(b_j)_{j ∈ J}` of `V →L[k] k` gives a continuous `k`-linear
   bijection `V ≃L[k] (J → k)` (injective by separation of points, with dense compact range by
   finite surjectivity), and shrinking `J` along the inverse coordinate embeddings lands the index
   type in `Type v`.

## Main results

* `TauCeti.IsLinearTopology.exists_continuousLinearMap_ne_zero`: continuous linear functionals
  separate points of a `T1` linearly topologized vector space over a discrete division ring.
* `TauCeti.IsLinearTopology.continuousLinearEquivOfBasisDual`: a basis of `V →L[k] k` induces a
  continuous linear equivalence `V ≃L[k] (J → k)` when `V` is compact and Hausdorff.
* `TauCeti.IsLinearTopology.exists_continuousLinearEquiv_pi`: every compact Hausdorff linearly
  topologized `k`-vector space `V : Type v` over a discrete field `k` is continuously `k`-linearly
  equivalent to `I → k` for some `I : Type v`.

## References

* S. Lefschetz, *Algebraic Topology*, Amer. Math. Soc. Colloq. Publ. 27 (1942), Chapter II, §6.
* N. Bourbaki, *Algebra II*, Chapter II, §7, Exercise 20.
-/

public section

open Filter Topology

namespace TauCeti.IsLinearTopology

section Ring

variable {R V W : Type*} [Ring R]
  [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [AddCommGroup W] [Module R W] [TopologicalSpace W] [DiscreteTopology W]

/-- A linear map from a topological module into a discrete module is continuous whenever its kernel
contains an open submodule. -/
theorem continuous_of_isOpen_le_ker {f : V →ₗ[R] W} {U : Submodule R V}
    (hU : IsOpen (U : Set V)) (hUf : U ≤ LinearMap.ker f) : Continuous f := by
  refine continuous_of_continuousAt_zero f.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, nhds_discrete W, tendsto_pure]
  exact Filter.mem_of_superset (hU.mem_nhds U.zero_mem) fun x hx ↦ hUf hx

end Ring

section DivisionRing

variable {k V : Type*} [DivisionRing k] [TopologicalSpace k] [DiscreteTopology k]
  [AddCommGroup V] [Module k V] [TopologicalSpace V] [IsTopologicalAddGroup V]

/-- In a `T1` linearly topologized vector space over a discrete division ring, continuous linear
functionals separate nonzero vectors from `0`. -/
theorem exists_continuousLinearMap_ne_zero [IsLinearTopology k V] [T1Space V] {v : V}
    (hv : v ≠ 0) : ∃ φ : V →L[k] k, φ v ≠ 0 := by
  obtain ⟨U, hU, hvU⟩ : ∃ U : Submodule k V, IsOpen (U : Set V) ∧ v ∉ U := by
    by_contra! h
    exact hv (eq_zero_of_forall_mem_of_isOpen h)
  obtain ⟨f, hfv, hfU⟩ := U.exists_dual_map_eq_bot_of_notMem hvU inferInstance
  have hker : U ≤ LinearMap.ker f := by
    intro x hx
    rw [LinearMap.mem_ker, ← Submodule.mem_bot k, ← hfU]
    exact Submodule.mem_map_of_mem hx
  exact ⟨⟨f, continuous_of_isOpen_le_ker hU hker⟩, hfv⟩

end DivisionRing

section Field

universe u v w

variable {k : Type u} [Field k] [TopologicalSpace k] [DiscreteTopology k]
  {V : Type v} [AddCommGroup V] [Module k V] [TopologicalSpace V]

/-- Joint evaluation of a finite `k`-linearly independent family of continuous linear functionals is
surjective onto `ι → k`. -/
theorem surjective_pi_of_linearIndependent {ι : Type w} [Finite ι] {φ : ι → (V →L[k] k)}
    (hli : LinearIndependent k φ) :
    Function.Surjective (fun v : V ↦ fun i : ι ↦ φ i v) := by
  classical
  let _ := Fintype.ofFinite ι
  let ev : V →ₗ[k] (ι → k) := LinearMap.pi fun i ↦ (φ i).toLinearMap
  change Function.Surjective ev
  rw [← LinearMap.range_eq_top]
  by_contra hlt
  obtain ⟨μ, hμ0, hμ⟩ :=
    (LinearMap.range ev).exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hlt) inferInstance
  have hrel : ∑ i : ι, μ (Pi.single i 1) • φ i = 0 := by
    ext v
    simp only [sum_apply, smul_apply, smul_eq_mul, zero_apply]
    have hv : ev v = ∑ i : ι, ev v i • Pi.single i (1 : k) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    have hmem : μ (ev v) = 0 := by
      rw [← Submodule.mem_bot k, ← hμ]
      exact Submodule.mem_map_of_mem (LinearMap.mem_range_self ev v)
    rw [hv, map_sum] at hmem
    simpa [ev, mul_comm] using hmem
  have hcoeff := Fintype.linearIndependent_iff.mp hli (fun i ↦ μ (Pi.single i 1)) hrel
  refine hμ0 (LinearMap.ext fun g ↦ ?_)
  have hg : g = ∑ i : ι, g i • Pi.single i (1 : k) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hg, map_sum]
  simp [hcoeff]

section BasisDual

variable [IsTopologicalAddGroup V] [IsLinearTopology k V] [CompactSpace V] [T2Space V]

private theorem bijective_evalOfBasisDual {J : Type w} (b : Module.Basis J k (V →L[k] k)) :
    Function.Bijective (LinearMap.pi fun j ↦ (b j).toLinearMap) := by
  let ev : V →ₗ[k] (J → k) := LinearMap.pi fun j ↦ (b j).toLinearMap
  have hcont : Continuous ev := continuous_pi fun j ↦ (b j).continuous
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    by_contra hv0
    obtain ⟨φ, hφv⟩ := exists_continuousLinearMap_ne_zero (k := k) hv0
    have hφ : φ = ∑ j ∈ (b.repr φ).support, b.repr φ j • b j := by
      simpa [Finsupp.linearCombination_apply, Finsupp.sum] using (b.linearCombination_repr φ).symm
    rw [hφ, sum_apply] at hφv
    refine hφv (Finset.sum_eq_zero fun j _ ↦ ?_)
    have hbj : b j v = 0 := congrFun (LinearMap.mem_ker.mp hv) j
    simp [hbj]
  · have hdense : DenseRange ev := by
      rw [denseRange_iff_closure_range]
      refine Set.eq_univ_of_forall fun g ↦ mem_closure_iff_nhds.mpr fun U hU ↦ ?_
      rw [nhds_pi, Filter.mem_pi] at hU
      obtain ⟨I, hIfin, t, ht, hIt⟩ := hU
      have : Finite I := hIfin.to_subtype
      have hsurj := surjective_pi_of_linearIndependent (ι := I)
        (b.linearIndependent.comp Subtype.val Subtype.val_injective)
      obtain ⟨v, hv⟩ := hsurj fun i : I ↦ g i
      refine ⟨ev v, hIt fun i hi ↦ ?_, LinearMap.mem_range_self ev v⟩
      have hvi : ev v i = g i := congrFun hv ⟨i, hi⟩
      rw [hvi]
      exact mem_of_mem_nhds (ht i)
    rw [← Set.range_eq_univ, ← (isCompact_range hcont).isClosed.closure_eq]
    exact hdense.closure_eq

/-- Given a `k`-basis `b` of `V →L[k] k`, evaluation against `b` is a continuous `k`-linear
equivalence `V ≃L[k] (J → k)` whenever `V` is compact and Hausdorff. -/
noncomputable def continuousLinearEquivOfBasisDual {J : Type w}
    (b : Module.Basis J k (V →L[k] k)) : V ≃L[k] (J → k) where
  toLinearEquiv := LinearEquiv.ofBijective (LinearMap.pi fun j ↦ (b j).toLinearMap)
    (bijective_evalOfBasisDual b)
  continuous_toFun := continuous_pi fun j ↦ (b j).continuous
  continuous_invFun :=
    (Continuous.homeoOfEquivCompactToT2
      (f := (LinearEquiv.ofBijective (LinearMap.pi fun j ↦ (b j).toLinearMap)
        (bijective_evalOfBasisDual b)).toEquiv)
      (continuous_pi fun j ↦ (b j).continuous)).symm.continuous

@[simp]
theorem continuousLinearEquivOfBasisDual_apply {J : Type w}
    (b : Module.Basis J k (V →L[k] k)) (v : V) (j : J) :
    continuousLinearEquivOfBasisDual b v j = b j v :=
  (rfl)

variable (k V) in
/-- Every compact Hausdorff linearly topologized vector space `V : Type v` over a discrete field `k`
is continuously `k`-linearly isomorphic to a product `I → k` with `I : Type v`. -/
theorem exists_continuousLinearEquiv_pi :
    ∃ I : Type v, Nonempty (V ≃L[k] (I → k)) := by
  classical
  let b := Module.Basis.ofVectorSpace k (V →L[k] k)
  let e := continuousLinearEquivOfBasisDual b
  have hinj : Function.Injective fun j : Module.Basis.ofVectorSpaceIndex k (V →L[k] k) ↦
      e.symm (Pi.single j (1 : k)) := fun i j hij ↦ by
    have hsingle : (Pi.single i (1 : k) : _ → k) = Pi.single j 1 := e.symm.injective hij
    by_contra hne
    have h10 : (1 : k) = 0 := by
      simpa [Pi.single_eq_same, Pi.single_eq_of_ne hne] using congrFun hsingle i
    exact one_ne_zero h10
  have : Small.{v} (Module.Basis.ofVectorSpaceIndex k (V →L[k] k)) := small_of_injective hinj
  let eqv := (equivShrink.{v} (Module.Basis.ofVectorSpaceIndex k (V →L[k] k))).symm
  exact ⟨Shrink.{v} (Module.Basis.ofVectorSpaceIndex k (V →L[k] k)),
    ⟨e.trans (ContinuousLinearEquiv.piCongrLeft k (fun _ ↦ k) eqv).symm⟩⟩

end BasisDual

end Field

end TauCeti.IsLinearTopology
