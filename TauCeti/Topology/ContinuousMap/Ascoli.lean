/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UniformSpace.Ascoli

import Mathlib.Topology.UniformSpace.Completion

/-!
# The Arzelà–Ascoli theorem in `C(X, Y)`

Mathlib proves the Arzelà–Ascoli theorem for a family of functions viewed inside a space of
uniform convergence on a family of compact sets
(`ArzelaAscoli.isCompact_closure_of_isClosedEmbedding`).
This file states it directly for subsets of the space `C(X, Y)` of continuous maps with its
compact-open topology, which is the space of continuous curves when `X` is a compact interval,
and adds companion statements used for compactness and finite approximation of families of curves.

* An equicontinuous set `A ⊆ C(X, Y)` whose values at each point lie in a common compact set has
  compact closure.
* If `Y` is complete, it is enough that the values are totally bounded at the points of a dense
  set `D ⊆ X`: equicontinuity spreads total boundedness from `D` to every point, and completeness
  turns it into compactness of the closure.
* An equicontinuous family with pointwise totally bounded values has finite uniform
  approximations on compact sets, with approximants drawn from the family itself.
* Conversely, on a compact domain, a compact subset of `C(X, Y)` is equicontinuous.

The pointwise hypothesis cannot be replaced by equicontinuity and a common starting point when `Y`
is not proper. The curves `γₙ(t) = t • eₙ`, `t ∈ [0, 1]`, along the standard basis vectors of
`ℓ²` are `1`-Lipschitz and all start at `0`, but no subsequence converges uniformly, because the
endpoints `eₙ` stay at distance at least `1` from each other
(`TauCeti.exists_lipschitzWith_one_not_isCompact_closure_range`).

## Main results

* `ArzelaAscoli.isCompact_closure_of_equicontinuous`: equicontinuity and pointwise relative
  compactness give compact closure.
* `EquicontinuousOn.exists_finite_approx_of_isCompact`: finite uniform approximation on a compact
  set by members of the family.
* `ContinuousMap.isClosedEmbedding_toUniformOnFunIsCompact`: `C(X, Y)` is a closed subspace of
  the space of functions with the topology of uniform convergence on compacts.
* `Equicontinuous.totallyBounded_range_eval`: equicontinuity spreads total boundedness of the
  values from a dense set of points to every point.
* `ArzelaAscoli.isCompact_closure_of_equicontinuous_of_totallyBounded`: for a complete target,
  total boundedness of the values at the points of a dense set suffices.
* `IsCompact.equicontinuous`: a compact set of continuous maps on a compact space is
  equicontinuous.

## References

* J. R. Munkres, *Topology*, 2nd ed., Prentice Hall 2000, §47 (Ascoli's theorem).
-/

public section

open Filter Set Topology Uniformity

variable {X Y : Type*} [TopologicalSpace X]

namespace ContinuousMap

/-- `C(X, Y)` sits inside the space of functions with the topology of uniform convergence on
compacts as a closed subspace, when the topology of `X` is coherent with its compact sets: the
coercion is a uniform embedding (`ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact`), and
its range is the set of continuous maps, which is closed. -/
theorem isClosedEmbedding_toUniformOnFunIsCompact [CompactlyCoherentSpace X] [UniformSpace Y] :
    IsClosedEmbedding (toUniformOnFunIsCompact : C(X, Y) → UniformOnFun X Y {K | IsCompact K}) := by
  refine ⟨isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
  rw [range_toUniformOnFunIsCompact]
  exact UniformOnFun.isClosed_setOfPred_continuous CompactlyCoherentSpace.isCoherentWith

end ContinuousMap

namespace ArzelaAscoli

/-- **The Arzelà–Ascoli theorem in `C(X, Y)`.** On a space `X` whose topology is coherent with its
compact sets (for instance a locally compact space), an equicontinuous set of continuous maps
whose values at each point lie in a common compact set has compact closure in the compact-open
topology. -/
theorem isCompact_closure_of_equicontinuous [CompactlyCoherentSpace X] [UniformSpace Y]
    {A : Set C(X, Y)} (hA : Equicontinuous fun f : A ↦ ⇑(f : C(X, Y)))
    (hApt : ∀ x, ∃ Q, IsCompact Q ∧ ∀ f ∈ A, f x ∈ Q) : IsCompact (closure A) := by
  rw [isCompact_iff_compactSpace]
  refine ArzelaAscoli.compactSpace_of_isClosedEmbedding (fun _ hK ↦ hK)
    (ContinuousMap.isClosedEmbedding_toUniformOnFunIsCompact.comp
      isClosed_closure.isClosedEmbedding_subtypeVal)
    (fun K _ ↦ (hA.closure' continuous_coeFun).equicontinuousOn K) ?_
  intro _ _ x _
  obtain ⟨Q, hQ, hAQ⟩ := hApt x
  -- Closing the compact bounds keeps them compact in a uniform space, without Hausdorffness.
  have hpoint : closure A ⊆ {f : C(X, Y) | f x ∈ closure Q} :=
    closure_minimal (fun f hf ↦ subset_closure (hAQ f hf))
      (isClosed_closure.preimage (continuous_eval_const x))
  exact ⟨closure Q, hQ.closure, fun f ↦ hpoint f.2⟩

end ArzelaAscoli

/-- An equicontinuous family with pointwise totally bounded values has a finite uniform
approximation on every compact set, with approximants drawn from the family itself. -/
theorem EquicontinuousOn.exists_finite_approx_of_isCompact [UniformSpace Y]
    {ι : Type*} {g : ι → X → Y} {K : Set X} (hequi : EquicontinuousOn g K)
    (hK : IsCompact K) (hg : ∀ x ∈ K, TotallyBounded (range fun i ↦ g i x))
    {U : Set (Y × Y)} (hU : U ∈ 𝓤 Y) :
    ∃ t : Set ι, t.Finite ∧ ∀ i, ∃ j ∈ t, ∀ x ∈ K, (g i x, g j x) ∈ U := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  -- In the completion, pointwise total boundedness gives compact closures.
  have hgequi :=
    (UniformSpace.Completion.isUniformInducing_coe Y).equicontinuousOn_iff.mp hequi
  let φ : ι → C(K, UniformSpace.Completion Y) := fun i ↦
    ⟨K.domRestrict (fun x ↦ (g i x : UniformSpace.Completion Y)),
      (hgequi.continuousOn i).domRestrict⟩
  have hφequi : Equicontinuous fun i ↦ ⇑(φ i) :=
    (equicontinuous_restrict_iff _).2 hgequi
  have hrange : IsCompact (closure (range φ)) :=
    ArzelaAscoli.isCompact_closure_of_equicontinuous (by
      rw [← Set.comp_rangeSplitting φ]
      exact hφequi.comp (Set.rangeSplitting φ)) fun x ↦ by
        have hpoint : TotallyBounded (range fun i ↦ (g i x : UniformSpace.Completion Y)) := by
          simpa only [← range_comp, Function.comp_def] using
            (hg x x.2).image (UniformSpace.Completion.uniformContinuous_coe Y)
        exact ⟨closure (range fun i ↦ (g i x : UniformSpace.Completion Y)),
          hpoint.closure.isCompact_of_isClosed isClosed_closure,
          fun _ ⟨i, hi⟩ ↦ hi ▸ subset_closure (mem_range_self i)⟩
  have htb : TotallyBounded (range φ) := hrange.totallyBounded.subset subset_closure
  obtain ⟨V, hV, hVU⟩ := ((UniformSpace.Completion.isUniformInducing_coe Y).basis_uniformity
    (Filter.basis_sets _)).mem_iff.mp hU
  have hV' :=
    (ContinuousMap.hasBasis_compactConvergenceUniformity_of_compact (α := K)).mem_of_mem hV
  obtain ⟨t, -, htfin, htcover⟩ := (exists_subset_image_finite_and (f := φ) (s := univ)).mp
    (by simpa only [image_univ] using htb.exists_subset hV')
  refine ⟨t, htfin, fun i ↦ ?_⟩
  obtain ⟨_, ⟨j, hj, rfl⟩, hij⟩ := mem_iUnion₂.mp (htcover (mem_range_self i))
  exact ⟨j, hj, fun x hx ↦ hVU (hij ⟨x, hx⟩)⟩

/-- Equicontinuity spreads total boundedness of the values from a dense set of points to every
point. -/
theorem Equicontinuous.totallyBounded_range_eval [UniformSpace Y] {ι : Type*} {F : ι → X → Y}
    (hF : Equicontinuous F) {D : Set X} (hD : Dense D)
    (hFD : ∀ x ∈ D, TotallyBounded (range fun i ↦ F i x)) (x : X) :
    TotallyBounded (range fun i ↦ F i x) := by
  intro U hU
  obtain ⟨V, hV, hVU⟩ := comp_mem_uniformity_sets hU
  obtain ⟨x', hx'D, hx'⟩ := hD.inter_nhds_nonempty (hF x V hV)
  obtain ⟨t, ht, hcover⟩ := hFD x' hx'D V hV
  refine ⟨t, ht, ?_⟩
  rintro _ ⟨i, rfl⟩
  obtain ⟨y, hy, hiy⟩ := mem_iUnion₂.mp (hcover ⟨i, rfl⟩)
  exact mem_iUnion₂.mpr ⟨y, hy, hVU ⟨F i x', hx' i, hiy⟩⟩

namespace ArzelaAscoli

/-- **The Arzelà–Ascoli theorem in `C(X, Y)`, with a dense set of points.** For a complete
target `Y`, an equicontinuous set of continuous maps whose values are totally bounded at
the points of a dense set `D ⊆ X` has compact closure in the compact-open topology. -/
theorem isCompact_closure_of_equicontinuous_of_totallyBounded [CompactlyCoherentSpace X]
    [UniformSpace Y] [CompleteSpace Y] {A : Set C(X, Y)} {D : Set X} (hD : Dense D)
    (hA : Equicontinuous fun f : A ↦ ⇑(f : C(X, Y)))
    (hAD : ∀ x ∈ D, TotallyBounded ((fun f : C(X, Y) ↦ f x) '' A)) : IsCompact (closure A) :=
  isCompact_closure_of_equicontinuous hA fun x ↦
    ⟨_, ((hA.totallyBounded_range_eval hD (fun x hx ↦ image_eq_range (· x) A ▸ hAD x hx)
      x).closure).isCompact_of_isClosed isClosed_closure, fun f hf ↦ subset_closure ⟨⟨f, hf⟩, rfl⟩⟩

end ArzelaAscoli

/-- **A compact set of continuous maps is equicontinuous.** On a compact space `X`, every compact
subset of `C(X, Y)` is equicontinuous; this is the converse of
`ArzelaAscoli.isCompact_closure_of_equicontinuous`. -/
theorem IsCompact.equicontinuous [CompactSpace X] [UniformSpace Y] {K : Set C(X, Y)}
    (hK : IsCompact K) : Equicontinuous fun f : K ↦ ⇑(f : C(X, Y)) := by
  intro x U hU
  obtain ⟨V, hV, hVsymm, hVU⟩ := comp_comp_symm_mem_uniformity_sets hU
  -- On a compact domain, uniform `V`-closeness is an entourage of `C(X, Y)`.
  obtain ⟨t, ht, hcover⟩ := hK.totallyBounded _
    (ContinuousMap.hasBasis_compactConvergenceUniformity_of_compact.mem_of_mem hV)
  have hnear : ∀ᶠ x' in 𝓝 x, ∀ g ∈ t, (g x, g x') ∈ V :=
    ht.eventually_all.mpr fun g _ ↦ g.continuous.tendsto x (UniformSpace.ball_mem_nhds _ hV)
  filter_upwards [hnear] with x' hx'
  rintro ⟨f, hf⟩
  obtain ⟨g, hg, hfg⟩ := mem_iUnion₂.mp (hcover hf)
  exact hVU ⟨g x', ⟨g x, hfg x, hx' g hg⟩, hVsymm.symm _ _ (hfg x')⟩
