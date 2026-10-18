/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.Basic
public import Mathlib.RingTheory.AdicCompletion.Topology

import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import TauCeti.RingTheory.AdicCompletion.Finite
import TauCeti.RingTheory.Finiteness.Tower

/-!
# Separatedness and closed submodules of finite modules over a Huber ring

Let `A` be a complete Hausdorff Huber ring with a pair of definition `(A₀, I)` such that `A₀` is
noetherian, and let `M` be a finitely generated `A`-module with its natural topology
(`IsModuleTopology A M`). This file proves that `M` is Hausdorff and that every `A`-submodule of
`M` is closed, and that every `A₀`-submodule `M₀ ⊆ M` spanning `M` over `A` is open in `M`
(Huber, *A generalization of formal schemes and rigid analytic varieties*, Lemma 2.3(ii)).

The ring of definition of a complete Hausdorff Huber ring is `I`-adically complete
(`TauCeti.Huber.PairOfDefinition.isAdicComplete_idealOfDefinition`). When `A₀` is noetherian,
every finitely generated `A₀`-submodule `M₀ ⊆ M` is therefore `I`-adically complete, by
`IsAdicComplete.of_finite`, and in particular `I`-adically separated. If `M₀` spans `M` over `A`,
the submodules `Iⁿ • M₀` form a neighbourhood basis of `0` in `M`, so this separatedness makes
`M` Hausdorff; applied to `M ⧸ N`, it makes every submodule `N` closed. Completeness of `M`
itself needs no noetherian hypothesis: it holds over any complete first-countable ring, by
`IsOpenQuotientMap.completeSpace` (see `TauCeti.completeSpace_moduleTopology`).

These are the facts about finite modules that Huber's sheafiness theorem for rings with a
noetherian ring of definition uses, alongside the strictness of linear maps
(`TauCeti.Huber.PairOfDefinition.isStrictMap_of_isNoetherianRing`). For strongly noetherian Tate
rings the corresponding statements are `TauCeti.Huber.IsTateRing.t2Space_moduleTopology` and
`TauCeti.Huber.isClosed_of_isNoetherian`; here `A` need not be Tate.

## Main results

* `TauCeti.Huber.PairOfDefinition.isAdicComplete_idealOfDefinition`: the ring of definition of a
  complete Hausdorff Huber ring is complete for its ideal of definition.
* `TauCeti.Huber.PairOfDefinition.isOpen_of_span_eq_top`: an `A₀`-submodule spanning a finite
  module over `A` is open.
* `TauCeti.Huber.PairOfDefinition.t2Space_of_isNoetherianRing`: a finite module is Hausdorff.
* `TauCeti.Huber.PairOfDefinition.isClosed_of_isNoetherianRing`: every submodule of a finite
  module is closed.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, Lemma 2.3(ii) and its proof.
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I*, Chapitre 0, (7.3.6).
-/

public section

open Filter Topology

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A]

/-- **The ring of definition of a complete Hausdorff Huber ring is adically complete.** If `A` is
complete and Hausdorff, then for every pair of definition `(A₀, I)` the ring `A₀` is `I`-adically
complete: being an open subgroup it is closed, hence complete, and its topology is `I`-adic. -/
instance isAdicComplete_idealOfDefinition [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
    [T0Space A] (P : PairOfDefinition A) :
    IsAdicComplete P.idealOfDefinition P.ringOfDefinition := by
  have : IsUniformAddGroup P.ringOfDefinition := P.ringOfDefinition.toAddSubgroup.isUniformAddGroup
  have hclosed : IsClosed (P.ringOfDefinition : Set A) :=
    P.ringOfDefinition.toAddSubgroup.isClosed_of_isOpen P.isOpen_ringOfDefinition
  have : CompleteSpace P.ringOfDefinition := hclosed.completeSpace_coe
  exact P.isAdic_idealOfDefinition.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩

variable {M : Type*} [AddCommGroup M] [Module A M]

section TopologicalSpace

variable [Module.Finite A M] [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace M]
  [IsModuleTopology A M]

/-- **A spanning lattice is open.** If `M` is a finite `A`-module with its natural topology, every
`A₀`-submodule of `M` spanning `M` over `A` is open in `M`. -/
theorem isOpen_of_span_eq_top (P : PairOfDefinition A) {M₀ : Submodule P.ringOfDefinition M}
    (hspan : Submodule.span A (M₀ : Set M) = ⊤) : IsOpen (M₀ : Set M) := by
  have := IsModuleTopology.isTopologicalAddGroup A M
  -- `M₀` contains the `A₀`-span `L` of finitely many of its elements, still spanning `M`.
  obtain ⟨t, htM₀, ht⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (M₀ : Set M)).mp
    (hspan ▸ Module.Finite.fg_top)
  let L := Submodule.span P.ringOfDefinition (t : Set M)
  have hLspan : Submodule.span A (L : Set M) = ⊤ := by
    rw [Submodule.span_span_of_tower, ← ht, hspan]
  have hL : (L : Set M) ∈ 𝓝 0 := by
    simpa using (P.hasBasis_nhds_zero_idealOfDefinition_pow_smul ⟨t, rfl⟩ hLspan).mem_of_mem
      (i := 0) trivial
  exact M₀.toAddSubgroup.isOpen_of_mem_nhds
    (mem_of_superset hL (Submodule.span_le.mpr htM₀))

end TopologicalSpace

section Complete

variable [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A] [T0Space A] [IsTopologicalRing A]
  [Module.Finite A M] [TopologicalSpace M] [IsModuleTopology A M]

/-- **Finite modules over a complete Huber ring with a noetherian ring of definition are
Hausdorff** (Huber, Lemma 2.3(ii)). If `A` is complete and Hausdorff with a noetherian ring of
definition, every finite `A`-module is Hausdorff in its natural topology. -/
theorem t2Space_of_isNoetherianRing (P : PairOfDefinition A)
    [IsNoetherianRing P.ringOfDefinition] : T2Space M := by
  have := IsModuleTopology.isTopologicalAddGroup A M
  obtain ⟨M₀, hM₀, hspan⟩ :=
    Module.Finite.exists_fg_span_eq_top P.ringOfDefinition (A := A) (M := M)
  have hbasis := P.hasBasis_nhds_zero_idealOfDefinition_pow_smul hM₀ hspan
  have : Module.Finite P.ringOfDefinition M₀ := Module.Finite.iff_fg.mpr hM₀
  have hH := IsHausdorff.of_le_jacobson P.idealOfDefinition M₀ (IsAdicComplete.le_jacobson_bot _)
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx ↦ ?_
  by_contra! h
  -- `x` lies in every `Iⁿ • M₀`, so Krull's intersection theorem in `M₀` forces `x = 0`.
  have hmem (n : ℕ) : x ∈ P.idealOfDefinition ^ n • M₀ := h _ (hbasis.mem_of_mem trivial)
  have hx₀ : x ∈ M₀ := by simpa using hmem 0
  refine hx (congrArg Subtype.val (hH.haus ⟨x, hx₀⟩ fun n ↦ ?_))
  rw [SModEq.zero, Submodule.mem_smul_top_iff]
  exact hmem n

/-- **Submodules of finite modules over a complete Huber ring with a noetherian ring of definition
are closed** (Huber, Lemma 2.3(ii)). If `A` is complete and Hausdorff with a noetherian ring of
definition, every `A`-submodule of a finite `A`-module is closed in its natural topology. -/
theorem isClosed_of_isNoetherianRing (P : PairOfDefinition A)
    [IsNoetherianRing P.ringOfDefinition] (N : Submodule A M) : IsClosed (N : Set M) := by
  -- The quotient `M ⧸ N` is a finite module, hence Hausdorff, and `N` is the kernel of `M → M ⧸ N`.
  let _ : TopologicalSpace (M ⧸ N) := moduleTopology A (M ⧸ N)
  have : IsModuleTopology A (M ⧸ N) := ⟨rfl⟩
  have := IsModuleTopology.isTopologicalAddGroup A (M ⧸ N)
  have := P.t2Space_of_isNoetherianRing (M := M ⧸ N)
  convert (isClosed_singleton (x := (0 : M ⧸ N))).preimage
    (IsModuleTopology.continuous_of_linearMap N.mkQ) using 1
  ext x
  simp [Submodule.Quotient.mk_eq_zero]

end Complete

end TauCeti.Huber.PairOfDefinition
