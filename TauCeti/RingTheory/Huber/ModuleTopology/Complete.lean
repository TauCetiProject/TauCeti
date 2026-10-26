/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.Basic

import Mathlib.RingTheory.AdicCompletion.Noetherian
import TauCeti.RingTheory.Finiteness.Tower

/-!
# Separatedness and closed submodules of finite modules over a Huber ring

Let `A` be a complete Hausdorff Huber ring with a pair of definition `(A₀, I)` such that `A₀` is
noetherian, and let `M` be a finitely generated `A`-module with its natural topology
(`IsModuleTopology A M`). This file proves that `M` is Hausdorff and that every `A`-submodule of
`M` is closed (Huber, *A generalization of formal schemes and rigid analytic varieties*,
Lemma 2.3(ii)).

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
(`TauCeti.Huber.PairOfDefinition.isStrictMap_of_isNoetherianRing`). For complete noetherian Tate
rings the corresponding statements are `TauCeti.Huber.IsTateRing.t2Space_moduleTopology` and
`TauCeti.Huber.isClosed_of_isNoetherian`; here `A` need not be Tate.

## Main results

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

variable {M : Type*} [AddCommGroup M] [Module A M]

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
