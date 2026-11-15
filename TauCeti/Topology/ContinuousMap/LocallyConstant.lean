/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.LocallyConstant
import Mathlib.Topology.Separation.DisjointCover

/-!
# Density of locally constant functions

On a profinite space `X`, the locally constant functions are dense in `C(X, V)` for every
topological space `V`, with the compact-open topology:
`LocallyConstant.denseRange_toContinuousMap`. In particular, every continuous function to a
uniform space is a uniform limit of locally constant functions. This is the density
statement used to extend functionals from locally constant test functions to all continuous
ones, for instance to extend the coefficients of measures on profinite spaces.

`ContinuousMap.intCastLocallyConstant` casts integer-valued continuous functions to locally
constant functions with values in any type with an integer cast.
-/

public section

namespace LocallyConstant

open Set Topology

variable {X V : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TotallyDisconnectedSpace X] [TopologicalSpace V]

/-- On a profinite space, locally constant functions are dense in the continuous functions to any
topological space, for the compact-open topology. When `V` is a uniform space, this is the
topology of uniform convergence. -/
theorem denseRange_toContinuousMap :
    DenseRange (fun f : LocallyConstant X V ↦ (f : C(X, V))) := by
  refine fun f ↦ (mem_closure_iff_nhds_basis f.hasBasis_nhds).mpr fun S ⟨hSf, hS⟩ ↦ ?_
  -- `T` relates `x` to `y` when `f y ∈ U` for every `(K, U) ∈ S` with `x ∈ K`. It is open since
  -- each `K` is closed and each `U` is open, and it contains the diagonal since `f` maps each `K`
  -- into its `U`.
  let T : Set (X × X) := ⋂ KU ∈ S, (Prod.fst ⁻¹' KU.1)ᶜ ∪ Prod.snd ⁻¹' (f ⁻¹' KU.2)
  have hT : T ∈ 𝓝ˢ (diagonal X) := by
    refine (hSf.isOpen_biInter fun KU hKU ↦ ?_).mem_nhdsSet.mpr ?_
    · obtain ⟨hK, hU, -⟩ := hS KU.1 KU.2 hKU
      exact (hK.isClosed.isOpen_compl.preimage continuous_fst).union
        (hU.preimage (f.continuous.comp continuous_snd))
    · rintro ⟨x, y⟩ (rfl : x = y)
      exact mem_iInter₂_of_mem fun KU hKU ↦
        (em' (x ∈ KU.1)).imp_right fun hx ↦ (hS KU.1 KU.2 hKU).2.2 hx
  -- Approximate the identity of `X` within `T` by a map `g ∘ q` factoring through the finite
  -- discrete space `Fin n`; then `f ∘ g ∘ q` is locally constant and maps each `K` into its `U`.
  obtain ⟨n, q, g, hq, hqg⟩ :=
    (ContinuousMap.id X).exists_finite_approximation_of_mem_nhds_diagonal hT
  refine ⟨_, ⟨⟨(f ∘ g) ∘ q, (IsLocallyConstant.of_discrete _).comp_continuous hq⟩, rfl⟩,
    mem_iInter₂_of_mem fun KU hKU x hx ↦ ?_⟩
  exact (mem_iInter₂.mp (hqg x) KU hKU).resolve_left (not_not_intro hx)

end LocallyConstant

namespace ContinuousMap

/-- Cast an integer-valued continuous function to a locally constant function. -/
def intCastLocallyConstant {X R : Type*} [TopologicalSpace X] [IntCast R]
    (f : C(X, ℤ)) : LocallyConstant X R :=
  ⟨fun x ↦ (f x : R), ((IsLocallyConstant.iff_continuous _).mpr f.continuous).comp Int.cast⟩

/-- The locally constant integer cast agrees pointwise with the integer cast. -/
@[simp]
theorem intCastLocallyConstant_apply {X R : Type*} [TopologicalSpace X] [IntCast R]
    (f : C(X, ℤ)) (x : X) : f.intCastLocallyConstant (R := R) x = (f x : R) :=
  (rfl)

end ContinuousMap
