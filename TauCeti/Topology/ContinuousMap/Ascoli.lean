/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Topology.MetricSpace.Pseudo.Real
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
public import Mathlib.Topology.UnitInterval

import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Completion
import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.Topology.MetricSpace.Holder
import TauCeti.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# The Arzelà–Ascoli theorem in `C(X, Y)`

Mathlib proves the Arzelà–Ascoli theorem for a family of functions viewed inside a space of
uniform convergence on a family of compact sets
(`ArzelaAscoli.isCompact_closure_of_isClosedEmbedding`), and shows that an equicontinuous set of
continuous maps that is compact for pointwise convergence is compact
(`ArzelaAscoli.isCompact_of_equicontinuous`).
This file states it directly for subsets of the space `C(X, Y)` of continuous maps with its
compact-open topology, which is the space of continuous curves when `X` is a compact interval,
and adds companion statements used for compactness and finite approximation of families of curves.

* An equicontinuous family in `C(X, Y)` whose values at each point lie in a common compact set has
  relatively compact range.
* If `Y` is complete, it is enough that the values are totally bounded at the points of a dense
  set `D ⊆ X`: equicontinuity spreads total boundedness from `D` to every point
  (`EquicontinuousWithinAt.totallyBounded_range_eval`), and completeness turns it into
  compactness of the closure.
* An equicontinuous family with pointwise totally bounded values has finite uniform
  approximations on compact sets, with approximants drawn from the family itself.
* Conversely, on a weakly locally compact domain, a compact subset of `C(X, Y)` is equicontinuous.
* On an open subset `U` of a second-countable locally compact space, a sequence that is
  equicontinuous on `U` with pointwise relatively compact values has a subsequence converging
  locally uniformly on `U`. In particular this applies to maps that are Hölder on each compact
  subset of `U` with a common constant, and the limit inherits those Hölder bounds.
* A sequence of continuous `1`-periodic loops in a compact subset of a pseudometric space, with a
  common modulus of continuity on `[0, 1]`, has a subsequence converging uniformly on `ℝ`. In
  particular the `1`-periodic `L`-Lipschitz loops in a compact set form a compact subset of
  `ℝ →ᵤ M`.
* A sequence of maps on `ℝ × ℝ` that are uniformly Lipschitz with values in a compact set on
  exhausting bands `[-Rₙ, Rₙ] × ℝ` has a subsequence converging locally uniformly on the plane.
  In particular, so do the translates `(s, t) ↦ u(s + σₙ, t)`, `σₙ → ∞`, of a Lipschitz map on a
  half-plane `s ≥ b` with values in a compact set.
* The `C`-Lipschitz maps `X → Y` whose value at a fixed point `x₀` lies in a closed set `K` form a
  compact subset of `C(X, Y)` when the closed `(C * dist x x₀)`-thickening of `K` is compact for
  every `x`, in particular when `Y` is proper and `K` is compact. For paths on `I`, compactness
  of the closed `C`-thickening suffices; for `K = {y}` this is the closed ball about `y`.

The pointwise hypothesis cannot be replaced by equicontinuity and a common starting point when `Y`
is not proper. The curves `γₙ(t) = t • eₙ`, `t ∈ [0, 1]`, along the standard basis vectors of
`ℓ²` are `1`-Lipschitz and all start at `0`, but no subsequence converges uniformly, because the
endpoints `eₙ` stay at distance at least `1` from each other
(`TauCeti.exists_lipschitzWith_one_not_isCompact_closure_range`).

## Main results

* `ArzelaAscoli.isCompact_closure_range_of_equicontinuous`: equicontinuity and pointwise relative
  compactness give compact closure.
* `EquicontinuousOn.exists_finite_approx_of_isCompact`: finite uniform approximation on a compact
  set by members of the family.
* `ContinuousMap.isClosedEmbedding_toUniformOnFunIsCompact`: `C(X, Y)` is a closed subspace of
  the space of functions with the topology of uniform convergence on compacts.
* `ArzelaAscoli.isCompact_closure_of_equicontinuous_of_totallyBounded`: for a complete target,
  total boundedness of the values at the points of a dense set suffices.
* `ArzelaAscoli.totallyBounded_range_mkOfCompact_of_equicontinuous`: on a compact space, an
  equicontinuous and pointwise totally bounded family into a pseudometric space has totally bounded
  range in `X →ᵇ Y`.
* `IsCompact.equicontinuous`: a compact set of continuous maps on a weakly locally compact space
  is equicontinuous.
* `EquicontinuousOn.exists_strictMono_tendstoLocallyUniformlyOn`: a locally uniformly convergent
  subsequence of a sequence that is equicontinuous on an open set.
* `TauCeti.exists_tendstoUniformly_subseq_of_periodic_of_modulus`: Arzelà–Ascoli for periodic
  loops with a common modulus of continuity.
* `TauCeti.isCompact_setOf_periodic_lipschitzWith`: the `1`-periodic `L`-Lipschitz loops in a
  compact set are compact for uniform convergence on `ℝ`.
* `TauCeti.exists_subseq_tendstoLocallyUniformlyOn_of_holderOnWith`: Arzelà–Ascoli for families
  with a common Hölder bound on each compact subset of an open set.
* `TauCeti.exists_subseq_tendstoLocallyUniformly_of_lipschitzOnWith`: Arzelà–Ascoli for maps that
  are uniformly Lipschitz with values in a compact set on exhausting bands of the plane.
* `TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_of_equicontinuousOn`: an equicontinuous
  sequence of maps on an open subset of a second-countable locally compact space, with values at
  each point in a compact set, has a locally uniformly convergent subsequence, with a limit
  continuous on that subset.
* `TauCeti.exists_subseq_tendstoLocallyUniformly_of_lipschitzOnWith_closedBall`: Arzelà–Ascoli
  for uniformly Lipschitz maps with values in a compact set on exhausting discs of the plane.
* `TauCeti.exists_subseq_tendstoLocallyUniformly_comp_add`: translates `u(s + σₙ, t)`, `σₙ → ∞`,
  of a Lipschitz map on a half-plane `s ≥ b` with values in a compact set have a locally
  uniformly convergent subsequence.
* `TauCeti.exists_subseq_tendstoLocallyUniformly_comp_add_of_lipschitzWith`: translates
  `uₙ(s + σₙ, t)` of uniformly Lipschitz maps with values in a compact set, by arbitrary shifts,
  have a locally uniformly convergent subsequence.
* `TauCeti.isCompact_setOf_lipschitzWith_apply_mem`: for a proper target, uniformly Lipschitz
  maps whose value at a fixed point lies in a compact set form a compact set, with
  `TauCeti.isCompact_setOf_lipschitzWith_apply_mem_of_forall_isCompact_cthickening` its form for
  a closed set with compact closed thickenings and
  `TauCeti.isCompact_setOf_lipschitzWith_apply_mem_of_isCompact_cthickening` its interval form.
* `TauCeti.isCompact_setOf_lipschitzWith_apply_eq`: for a proper target, uniformly Lipschitz
  maps with a common value at a fixed point form a compact set, with
  `TauCeti.isCompact_setOf_lipschitzWith_apply_eq_of_isCompact_closedBall` its interval form for
  a compact closed ball.

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

/-- **The Arzelà–Ascoli theorem in `C(X, Y)`.** An equicontinuous family of continuous maps
whose values at each point lie in a common compact set has relatively compact range in the
compact-open topology. No assumption on the topology of `X` is needed. -/
theorem isCompact_closure_range_of_equicontinuous [UniformSpace Y]
    {ι : Type*} {f : ι → C(X, Y)} (hf : Equicontinuous fun i ↦ ⇑(f i))
    (hfpt : ∀ x, ∃ Q, IsCompact Q ∧ ∀ i, f i x ∈ Q) : IsCompact (closure (range f)) := by
  choose Q hQ hfQ using hfpt
  -- The pointwise closure `P` of the family is equicontinuous, and compact by Tychonoff.
  set P : Set (X → Y) := closure (range fun i ↦ ⇑(f i))
  have hPeq : P.Equicontinuous := by
    refine Set.Equicontinuous.closure ?_
    rw [Set.Equicontinuous, ← comp_rangeSplitting (fun i ↦ ⇑(f i))]
    exact hf.comp (rangeSplitting _)
  have hP : IsCompact P :=
    (isCompact_univ_pi fun x ↦ (hQ x).closure).of_isClosed_subset isClosed_closure
      (closure_minimal (range_subset_iff.2 fun i x _ ↦ subset_closure (hfQ x i))
        (isClosed_set_pi fun x _ ↦ isClosed_closure))
  -- The continuous maps whose underlying functions lie in `P` form a compact set, since
  -- pointwise and compact convergence agree on equicontinuous sets. It is closed and contains
  -- the family, hence contains its closure.
  set S : Set C(X, Y) := {g | ⇑g ∈ P}
  have hS : IsCompact S := by
    have himage : ContinuousMap.toFun '' S = P :=
      Subset.antisymm (image_subset_iff.2 fun _ hg ↦ hg)
        fun p hp ↦ ⟨⟨p, hPeq.continuous_of_mem hp⟩, hp, rfl⟩
    exact ArzelaAscoli.isCompact_of_equicontinuous S (himage ▸ hP)
      (hPeq.comp fun g : S ↦ (⟨⇑(g : C(X, Y)), g.property⟩ : P))
  exact hS.of_isClosed_subset isClosed_closure (closure_minimal
    (range_subset_iff.2 fun i ↦ subset_closure (mem_range_self i))
    (isClosed_closure.preimage (continuous_pi continuous_eval_const)))

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
    ArzelaAscoli.isCompact_closure_range_of_equicontinuous hφequi fun x ↦ by
      have hpoint : TotallyBounded (range fun i ↦ (g i x : UniformSpace.Completion Y)) := by
        simpa only [← range_comp, Function.comp_def] using
          (hg x x.property).image (UniformSpace.Completion.uniformContinuous_coe Y)
      exact ⟨closure (range fun i ↦ (g i x : UniformSpace.Completion Y)),
        hpoint.closure.isCompact_of_isClosed isClosed_closure,
        fun i ↦ subset_closure (mem_range_self i)⟩
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

namespace ArzelaAscoli

/-- **The Arzelà–Ascoli theorem in `C(X, Y)`, with a dense set of points.** For a complete
target `Y`, an equicontinuous set of continuous maps whose values are totally bounded at
the points of a dense set `D ⊆ X` has compact closure in the compact-open topology. -/
theorem isCompact_closure_of_equicontinuous_of_totallyBounded [UniformSpace Y] [CompleteSpace Y]
    {A : Set C(X, Y)} {D : Set X} (hD : Dense D)
    (hA : Equicontinuous fun f : A ↦ ⇑(f : C(X, Y)))
    (hAD : ∀ x ∈ D, TotallyBounded ((fun f : C(X, Y) ↦ f x) '' A)) : IsCompact (closure A) :=
  Subtype.range_coe (s := A) ▸ isCompact_closure_range_of_equicontinuous hA fun x ↦
    ⟨_, (((hA x).equicontinuousWithinAt D).totallyBounded_range_eval (hD x)
      (fun x hx ↦ image_eq_range (· x) A ▸ hAD x hx)).closure.isCompact_of_isClosed
      isClosed_closure, fun f ↦ subset_closure (mem_range_self f)⟩

/-- On a compact space, an equicontinuous and pointwise totally bounded family of functions into a
pseudometric space has totally bounded range when bundled into `X →ᵇ Y`. -/
theorem totallyBounded_range_mkOfCompact_of_equicontinuous [CompactSpace X] [PseudoMetricSpace Y]
    {ι : Type*} {g : ι → X → Y} (hequi : Equicontinuous g)
    (hg : ∀ x, TotallyBounded (range fun i ↦ g i x)) :
    TotallyBounded
      (range fun i ↦ BoundedContinuousFunction.mkOfCompact ⟨g i, hequi.continuous i⟩) := by
  refine Metric.totallyBounded_iff.2 fun r hr ↦ ?_
  obtain ⟨t, htf, hcov⟩ := (hequi.equicontinuousOn univ).exists_finite_approx_of_isCompact
    isCompact_univ (fun x _ ↦ hg x) (Metric.dist_mem_uniformity (half_pos hr))
  refine ⟨(fun j ↦ BoundedContinuousFunction.mkOfCompact ⟨g j, hequi.continuous j⟩) '' t,
    htf.image _, ?_⟩
  rintro _ ⟨i, rfl⟩
  obtain ⟨j, hjt, hij⟩ := hcov i
  refine mem_iUnion₂.2 ⟨_, mem_image_of_mem _ hjt, Metric.mem_ball.2 ?_⟩
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (half_pos hr).le).2 fun x ↦ ?_)
    (half_lt_self hr)
  rw [BoundedContinuousFunction.mkOfCompact_apply, BoundedContinuousFunction.mkOfCompact_apply,
    ContinuousMap.coe_mk, ContinuousMap.coe_mk]
  have hmem := hij x (mem_univ x)
  rw [mem_ofPred] at hmem
  exact hmem.le

end ArzelaAscoli

/-- **A compact set of continuous maps is equicontinuous.** On a weakly locally compact space `X`
(for instance a compact space), every compact subset of `C(X, Y)` is equicontinuous; this is a
converse of `ArzelaAscoli.isCompact_closure_range_of_equicontinuous`. -/
theorem IsCompact.equicontinuous [WeaklyLocallyCompactSpace X] [UniformSpace Y]
    {K : Set C(X, Y)} (hK : IsCompact K) : Equicontinuous fun f : K ↦ ⇑(f : C(X, Y)) := by
  intro x U hU
  obtain ⟨V, hV, hVsymm, hVU⟩ := comp_comp_symm_mem_uniformity_sets hU
  obtain ⟨N, hN, hNx⟩ := exists_compact_mem_nhds x
  -- Uniform `V`-closeness on the compact neighbourhood `N` is an entourage of `C(X, Y)`.
  obtain ⟨t, ht, hcover⟩ := hK.totallyBounded _
    (ContinuousMap.hasBasis_compactConvergenceUniformity.mem_of_mem (i := (N, V)) ⟨hN, hV⟩)
  have hnear : ∀ᶠ x' in 𝓝 x, ∀ g ∈ t, (g x, g x') ∈ V :=
    ht.eventually_all.mpr fun g _ ↦ by
      have hg := (g.continuous.tendsto x).eventually (SetRel.ball_mem_nhds _ hV)
      exact hg.mono fun x' hx' ↦ hVsymm.symm _ _ hx'
  filter_upwards [hnear, hNx] with x' hx' hx'N
  rintro ⟨f, hf⟩
  obtain ⟨g, hg, hfg⟩ := mem_iUnion₂.mp (hcover hf)
  exact hVU ⟨g x', ⟨g x, hfg x (mem_of_mem_nhds hNx), hx' g hg⟩, hVsymm.symm _ _ (hfg x' hx'N)⟩

/-- **Arzelà–Ascoli on an open set.** On an open subset `U` of a second-countable locally compact
space, a sequence of maps into a uniform space with countably generated uniformity, for instance a
pseudometric space, that is equicontinuous on `U`, with values at each point of `U` in a common
compact set, has a subsequence converging locally uniformly on `U`. -/
theorem EquicontinuousOn.exists_strictMono_tendstoLocallyUniformlyOn [LocallyCompactSpace X]
    [SecondCountableTopology X] [UniformSpace Y] [(𝓤 Y).IsCountablyGenerated] {u : ℕ → X → Y}
    {U : Set X} (hequi : EquicontinuousOn u U) (hU : IsOpen U)
    (hQ : ∀ x ∈ U, ∃ Q, IsCompact Q ∧ ∀ n, u n x ∈ Q) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : X → Y,
      TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop U := by
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  -- A subsequence of the restrictions converges in `C(U, Y)`, that is, locally uniformly on `U`.
  set f : ℕ → C(U, Y) := fun n ↦ ⟨U.domRestrict (u n), (hequi.continuousOn n).domRestrict⟩
  obtain ⟨a, -, φ, hφ, hconv⟩ := (ArzelaAscoli.isCompact_closure_range_of_equicontinuous (f := f)
    ((equicontinuous_restrict_iff _).2 hequi) fun x ↦ hQ x x.property).tendsto_subseq
    fun n ↦ subset_closure (mem_range_self n)
  refine ⟨φ, hφ, Function.extend Subtype.val a (u 0), ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe,
    Function.extend_comp Subtype.val_injective]
  exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.1 hconv

namespace TauCeti

open Function
open scoped NNReal UniformConvergence

/-- **Periodic Arzelà–Ascoli.** A sequence of continuous `1`-periodic loops in a compact set `K`,
sharing a modulus of continuity `ρ` with `ρ(h) → 0` as `h → 0` on `[0, 1]`, has a subsequence
converging uniformly on `ℝ` to a continuous `1`-periodic loop. -/
theorem exists_tendstoUniformly_subseq_of_periodic_of_modulus {M : Type*} [PseudoMetricSpace M]
    {K : Set M} (hK : IsCompact K) {y : ℕ → ℝ → M} (hy : ∀ n, Continuous (y n))
    (hper : ∀ n, Periodic (y n) 1) (hyK : ∀ n t, y n t ∈ K) {ρ : ℝ → ℝ}
    (hρ : Tendsto ρ (𝓝 0) (𝓝 0))
    (hmod : ∀ n, ∀ t₁ ∈ Icc (0 : ℝ) 1, ∀ t₂ ∈ Icc (0 : ℝ) 1, t₁ ≤ t₂ →
      dist (y n t₂) (y n t₁) ≤ ρ (t₂ - t₁)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ x : ℝ → M, Periodic x 1 ∧ Continuous x ∧
      TendstoUniformly (fun n ↦ y (ψ n)) x atTop := by
  -- Arzelà–Ascoli on `C([0, 1], M)`.
  let G : ℕ → C(Icc (0 : ℝ) 1, M) := fun n ↦ ⟨fun t ↦ y n t, (hy n).comp continuous_subtypeVal⟩
  have hGeq : Equicontinuous fun n ↦ ⇑(G n) := by
    refine Metric.equicontinuous_of_continuity_modulus ρ hρ _ fun t₁ t₂ n ↦ ?_
    rw [Subtype.dist_eq, Real.dist_eq]
    rcases le_total (t₁ : ℝ) t₂ with h | h
    · rw [dist_comm, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
      exact hmod n t₁ t₁.property t₂ t₂.property h
    · rw [abs_of_nonneg (sub_nonneg.2 h)]
      exact hmod n t₂ t₂.property t₁ t₁.property h
  obtain ⟨g, -, ψ, hψ, hlim⟩ :=
    (ArzelaAscoli.isCompact_closure_range_of_equicontinuous hGeq fun t ↦
      ⟨K, hK, fun n ↦ hyK n t⟩).tendsto_subseq
      (fun n ↦ subset_closure (mem_range_self n))
  have hunif := ContinuousMap.tendsto_iff_tendstoUniformly.1 hlim
  -- The limit loop, extended periodically.
  let p : ℝ → Icc (0 : ℝ) 1 := fun t ↦ ⟨Int.fract t, Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  set x : ℝ → M := fun t ↦ g (p t)
  have hxper : Periodic x 1 := fun t ↦ by simp only [x, p, Int.fract_add_one]
  have hux : TendstoUniformly (fun n ↦ y (ψ n)) x atTop := by
    have heq : (fun n ↦ y (ψ n)) = fun n ↦ ⇑((G ∘ ψ) n) ∘ p := by
      funext n t
      exact ((hper (ψ n)).apply_fract t).symm
    rw [heq]
    exact hunif.comp p
  exact ⟨ψ, hψ, x, hxper, hux.continuous (Frequently.of_forall fun n ↦ hy _), hux⟩

/-- **Periodic Arzelà–Ascoli, compact form.** In the topology of uniform convergence on `ℝ`, the
`1`-periodic `L`-Lipschitz loops with values in a compact set `K` form a compact set. -/
theorem isCompact_setOf_periodic_lipschitzWith {M : Type*} [MetricSpace M] {K : Set M}
    (hK : IsCompact K) (L : ℝ≥0) :
    IsCompact {f : ℝ →ᵤ M | Periodic (UniformFun.toFun f) 1 ∧
      (∀ t, UniformFun.toFun f t ∈ K) ∧ LipschitzWith L (UniformFun.toFun f)} := by
  refine IsSeqCompact.isCompact fun f hf ↦ ?_
  have hρ : Tendsto (fun h : ℝ ↦ L * h) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul (L : ℝ)
  obtain ⟨ψ, hψ, x, hxper, -, hux⟩ := exists_tendstoUniformly_subseq_of_periodic_of_modulus hK
    (fun n ↦ (hf n).2.2.continuous) (fun n ↦ (hf n).1) (fun n ↦ (hf n).2.1) hρ
    fun n t₁ _ t₂ _ ht ↦ by
      simpa [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 ht)] using (hf n).2.2.dist_le_mul t₂ t₁
  -- The limit is again periodic, `L`-Lipschitz and with values in `K`.
  refine ⟨UniformFun.ofFun x, ⟨hxper, fun t ↦ hK.isClosed.mem_of_tendsto (hux.tendsto_at t)
    (Eventually.of_forall fun n ↦ (hf (ψ n)).2.1 t), LipschitzWith.of_dist_le_mul fun t t' ↦
      le_of_tendsto ((hux.tendsto_at t).dist (hux.tendsto_at t'))
        (Eventually.of_forall fun n ↦ (hf (ψ n)).2.2.dist_le_mul t t')⟩, ψ, hψ,
    UniformFun.tendsto_iff_tendstoUniformly.2 hux⟩

/-- **Arzelà–Ascoli on an open set, with a continuous limit.** Let `u n` be an equicontinuous
sequence of maps on an open subset `Ω` of a second-countable locally compact space, for instance a
proper metric space, with values in a pseudometric space, such that for each `x ∈ Ω` the values
`u n x` lie in a common compact set. A subsequence of the `u n` converges locally uniformly on `Ω`
to a map continuous on `Ω`. -/
theorem exists_strictMono_tendstoLocallyUniformlyOn_of_equicontinuousOn {X M : Type*}
    [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [PseudoMetricSpace M]
    {Ω : Set X} (hΩ : IsOpen Ω)
    {u : ℕ → X → M} (hu : EquicontinuousOn u Ω)
    (hbd : ∀ x ∈ Ω, ∃ Q, IsCompact Q ∧ ∀ n, u n x ∈ Q) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : X → M, ContinuousOn g Ω ∧
      TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) g atTop Ω := by
  -- The limit of a locally uniformly convergent sequence of continuous maps is continuous.
  obtain ⟨φ, hφ, g, hconv⟩ := hu.exists_strictMono_tendstoLocallyUniformlyOn hΩ hbd
  exact ⟨φ, hφ, g, hconv.continuousOn
    (Eventually.of_forall fun n ↦ hu.continuousOn (φ n)).frequently, hconv⟩

/-- Arzelà–Ascoli along exhausting discs of nonnegative radii. -/
private theorem exists_subseq_tendstoLocallyUniformly_of_lipschitzOnWith_closedBall_of_nonneg
    {M : Type*} [PseudoMetricSpace M] {K : Set M} (hK : IsCompact K) {w : ℕ → ℝ × ℝ → M} {R : ℕ → ℝ}
    {L : NNReal} (hR₀ : ∀ n, 0 ≤ R n) (hR : Tendsto R atTop atTop)
    (hL : ∀ n, LipschitzOnWith L (w n) (Metric.closedBall 0 (R n)))
    (hwK : ∀ n, MapsTo (w n) (Metric.closedBall 0 (R n)) K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : C(ℝ × ℝ, M),
      TendstoLocallyUniformly (fun n ↦ w (φ n)) g atTop := by
  -- Clamping both coordinates to `[-R n, R n]` retracts the plane onto the disc, and is
  -- `1`-Lipschitz for the sup norm.
  set c : ℕ → ℝ → ℝ := fun n a ↦ max (-R n) (min a (R n))
  have hc (n : ℕ) : LipschitzWith 1 (c n) :=
    (LipschitzWith.id.min_const (R n)).const_max (-R n)
  have hcR (n : ℕ) (a : ℝ) : |c n a| ≤ R n :=
    abs_le.2 ⟨le_max_left _ _, max_le (by linarith [hR₀ n]) (min_le_right _ _)⟩
  set p : ℕ → ℝ × ℝ → ℝ × ℝ := fun n z ↦ (c n z.1, c n z.2)
  have hp (n : ℕ) : LipschitzWith 1 (p n) := by
    simpa using ((hc n).comp LipschitzWith.prod_fst).prodMk ((hc n).comp LipschitzWith.prod_snd)
  have hpR (n : ℕ) (z : ℝ × ℝ) : p n z ∈ Metric.closedBall 0 (R n) := by
    rw [mem_closedBall_zero_iff, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le (hcR n _) (hcR n _)
  set w' : ℕ → ℝ × ℝ → M := fun n ↦ w n ∘ p n
  have hw' (n : ℕ) : LipschitzWith L (w' n) := by
    have h := (hL n).comp ((hp n).lipschitzOnWith (s := univ)) fun z _ ↦ hpR n z
    rwa [mul_one, lipschitzOnWith_univ] at h
  -- A subsequence converges in `C(ℝ × ℝ, M)`.
  set G : ℕ → C(ℝ × ℝ, M) := fun n ↦ ⟨w' n, (hw' n).continuous⟩
  obtain ⟨g, -, φ, hφ, hlim⟩ := (ArzelaAscoli.isCompact_closure_range_of_equicontinuous
    (f := G) (LipschitzWith.uniformEquicontinuous w' L hw').equicontinuous
    fun z ↦ ⟨K, hK, fun n ↦ hwK n (hpR n z)⟩).tendsto_subseq
    (fun n ↦ subset_closure (mem_range_self n))
  have hgw := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.1 hlim
  refine ⟨φ, hφ, g, ?_⟩
  -- On each compact set the clamped maps are eventually the maps themselves.
  rw [tendstoLocallyUniformly_iff_forall_isCompact] at hgw ⊢
  intro C hC
  obtain ⟨m, hm⟩ := (hC.image (continuous_norm (E := ℝ × ℝ))).bddAbove
  refine (hgw C hC).congr ?_
  filter_upwards [(hR.comp hφ.tendsto_atTop).eventually_ge_atTop m] with n hn z hz
  have hmz : ‖z‖ ≤ m := hm (mem_image_of_mem _ hz)
  simp only [Function.comp_apply] at hn
  have hclamp (a : ℝ) (ha : |a| ≤ ‖z‖) : c (φ n) a = a := by
    rw [abs_le] at ha
    simp only [c]
    rw [min_eq_left (by linarith), max_eq_right (by linarith)]
  have h1 := hclamp z.1 (by simpa using norm_fst_le z)
  have h2 := hclamp z.2 (by simpa using norm_snd_le z)
  simp only [G, ContinuousMap.coe_mk, w', p, Function.comp_apply, h1, h2]

/-- **Arzelà–Ascoli along exhausting discs.** Let `w n` be `L`-Lipschitz on the closed disc
`closedBall 0 (R n)` of `ℝ × ℝ` (for the sup norm, the square `[-R n, R n]²`), with values there in
a compact subset `K` of a pseudometric space, where `R n → ∞`. A subsequence of the `w n`
converges locally uniformly on `ℝ × ℝ` to a continuous map. For instance, `w n` may be a sequence
of rescaled solutions of an equation, on discs where their derivatives are known to be bounded. -/
theorem exists_subseq_tendstoLocallyUniformly_of_lipschitzOnWith_closedBall {M : Type*}
    [PseudoMetricSpace M] {K : Set M} (hK : IsCompact K) {w : ℕ → ℝ × ℝ → M} {R : ℕ → ℝ}
    {L : NNReal} (hR : Tendsto R atTop atTop)
    (hL : ∀ n, LipschitzOnWith L (w n) (Metric.closedBall 0 (R n)))
    (hwK : ∀ n, MapsTo (w n) (Metric.closedBall 0 (R n)) K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : C(ℝ × ℝ, M),
      TendstoLocallyUniformly (fun n ↦ w (φ n)) g atTop := by
  -- From the index `N` on, the radii are nonnegative.
  obtain ⟨N, hN⟩ := (hR.eventually_ge_atTop 0).exists_forall_of_atTop
  obtain ⟨φ, hφ, g, hg⟩ :=
    exists_subseq_tendstoLocallyUniformly_of_lipschitzOnWith_closedBall_of_nonneg hK
      (fun n ↦ hN _ (Nat.le_add_left N n)) (hR.comp (tendsto_add_atTop_nat N))
      (fun n ↦ hL (n + N)) fun n ↦ hwK (n + N)
  exact ⟨fun n ↦ φ n + N, fun m n hmn ↦ Nat.add_lt_add_right (hφ hmn) N, g, hg⟩

/-- **Arzelà–Ascoli along exhausting bands.** Let `w n` be `L`-Lipschitz on the band
`[-R n, R n] × ℝ` of `ℝ × ℝ`, with values there in a compact subset `K` of a pseudometric space,
where `R n → ∞`. A subsequence of the `w n` converges locally uniformly on `ℝ × ℝ` to a
continuous map. For instance, `w n` may be a sequence of solutions of an equation translated along
an end, on bands where the solutions are known to have bounded derivatives. -/
theorem exists_subseq_tendstoLocallyUniformly_of_lipschitzOnWith {M : Type*}
    [PseudoMetricSpace M] {K : Set M} (hK : IsCompact K) {w : ℕ → ℝ × ℝ → M} {R : ℕ → ℝ}
    {L : NNReal} (hR : Tendsto R atTop atTop)
    (hL : ∀ n, LipschitzOnWith L (w n) (Icc (-R n) (R n) ×ˢ univ))
    (hwK : ∀ n, MapsTo (w n) (Icc (-R n) (R n) ×ˢ univ) K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : C(ℝ × ℝ, M),
      TendstoLocallyUniformly (fun n ↦ w (φ n)) g atTop := by
  -- For the sup norm, the disc of radius `R n` lies in the band.
  have hsub (n : ℕ) : Metric.closedBall (0 : ℝ × ℝ) (R n) ⊆ Icc (-R n) (R n) ×ˢ univ :=
    fun z hz ↦ ⟨abs_le.1 ((Real.norm_eq_abs z.1).symm.le.trans
      ((norm_fst_le z).trans (mem_closedBall_zero_iff.1 hz))), mem_univ _⟩
  exact exists_subseq_tendstoLocallyUniformly_of_lipschitzOnWith_closedBall hK hR
    (fun n ↦ (hL n).mono (hsub n)) fun n ↦ (hwK n).mono_left (hsub n)

/-- **Arzelà–Ascoli for translates along an end.** Let `u` be Lipschitz on the half-plane
`s ≥ b` of `ℝ × ℝ`, with values there in a compact subset of a pseudometric space, and let
`σₙ → ∞`. A subsequence of the translates `(s, t) ↦ u(s + σₙ, t)` converges locally uniformly on
`ℝ × ℝ` to a continuous map. -/
theorem exists_subseq_tendstoLocallyUniformly_comp_add {M : Type*} [PseudoMetricSpace M]
    {K : Set M} (hK : IsCompact K) {u : ℝ × ℝ → M} {b : ℝ} {L : NNReal}
    (hL : LipschitzOnWith L u (Ici b ×ˢ univ)) (huK : MapsTo u (Ici b ×ˢ univ) K) {σ : ℕ → ℝ}
    (hσ : Tendsto σ atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : C(ℝ × ℝ, M),
      TendstoLocallyUniformly (fun n z ↦ u (z + (σ (φ n), 0))) g atTop := by
  -- The band `[-(σₙ - b), σₙ - b] × ℝ` is translated into `s ≥ b`.
  have hR : Tendsto (fun n ↦ σ n - b) atTop atTop := tendsto_atTop_add_const_right _ _ hσ
  have hmaps (n : ℕ) : MapsTo (fun z : ℝ × ℝ ↦ z + (σ n, 0)) (Icc (-(σ n - b)) (σ n - b) ×ˢ univ)
      (Ici b ×ˢ univ) := fun z hz ↦
    ⟨mem_Ici.2 (by simp only [Prod.fst_add]; linarith [hz.1.1]), mem_univ _⟩
  have hadd (n : ℕ) : LipschitzWith 1 fun z : ℝ × ℝ ↦ z + (σ n, 0) :=
    (IsometryEquiv.addRight ((σ n, 0) : ℝ × ℝ)).isometry.lipschitzWith
  exact exists_subseq_tendstoLocallyUniformly_of_lipschitzOnWith hK hR
    (fun n ↦ by simpa using hL.comp ((hadd n).lipschitzOnWith) (hmaps n))
    fun n ↦ huK.comp (hmaps n)

/-- **Arzelà–Ascoli for translates of a sequence.** Let `u n` be `L`-Lipschitz maps on `ℝ × ℝ`
with values in a compact subset of a pseudometric space, and let `σ n` be arbitrary shifts. A
subsequence of the translates `(s, t) ↦ u n (s + σ n, t)` converges locally uniformly on `ℝ × ℝ`
to a continuous map. -/
theorem exists_subseq_tendstoLocallyUniformly_comp_add_of_lipschitzWith {M : Type*}
    [PseudoMetricSpace M] {K : Set M} (hK : IsCompact K) {u : ℕ → ℝ × ℝ → M} {L : NNReal}
    (hL : ∀ n, LipschitzWith L (u n)) (huK : ∀ n z, u n z ∈ K) (σ : ℕ → ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : C(ℝ × ℝ, M),
      TendstoLocallyUniformly (fun n z ↦ u (φ n) (z + (σ (φ n), 0))) g atTop := by
  have hw (n : ℕ) : LipschitzWith L fun z ↦ u n (z + (σ n, 0)) :=
    ((hL n).comp (IsometryEquiv.addRight ((σ n, 0) : ℝ × ℝ)).isometry.lipschitzWith).weaken
      (mul_one L).le
  exact exists_subseq_tendstoLocallyUniformly_of_lipschitzOnWith hK (R := fun n ↦ (n : ℝ))
    tendsto_natCast_atTop_atTop (fun n ↦ (hw n).lipschitzOnWith) fun _ _ _ ↦ huK _ _

/-- **Arzelà–Ascoli for locally Hölder families.** Let `U` be an open subset of a second-countable
locally compact pseudometric space, let `r > 0`, and let `u n` be maps into a pseudometric space
that are Hölder continuous of exponent `r` on each compact subset of `U` with a constant
independent of `n`, with the values at each point of `U` lying in a common compact set. Then a
subsequence of the `u n` converges locally uniformly on `U` to a map that is continuous on `U`,
and the limit satisfies every Hölder bound on a subset of `U` shared by all the `u n`. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_of_holderOnWith {Z M : Type*}
    [PseudoMetricSpace Z] [LocallyCompactSpace Z] [SecondCountableTopology Z]
    [PseudoMetricSpace M] {U : Set Z} (hU : IsOpen U) {r : ℝ≥0} (hr : 0 < r) {u : ℕ → Z → M}
    (hholder : ∀ K ⊆ U, IsCompact K → ∃ C : ℝ≥0, ∀ n, HolderOnWith C r (u n) K)
    (hpt : ∀ x ∈ U, ∃ Q, IsCompact Q ∧ ∀ n, u n x ∈ Q) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : Z → M, ContinuousOn v U ∧
      TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop U ∧
      ∀ K ⊆ U, ∀ C : ℝ≥0, (∀ n, HolderOnWith C r (u n) K) → HolderOnWith C r v K := by
  -- Near each point of `U` the maps share a Hölder bound on a compact neighbourhood.
  have hequi : EquicontinuousOn u U := equicontinuousOn_of_forall_holderOnWith hr fun x hx ↦ by
    obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU hx
    obtain ⟨C, hC⟩ := hholder K hKU hK
    exact ⟨C, K, mem_interior_iff_mem_nhds.1 hxK, hC⟩
  obtain ⟨φ, hφ, v, hv, hconv⟩ :=
    exists_strictMono_tendstoLocallyUniformlyOn_of_equicontinuousOn hU hequi hpt
  -- A common Hölder bound passes to the limit.
  exact ⟨φ, hφ, v, hv, hconv, fun K hKU C hC ↦ HolderOnWith.of_tendsto
    (fun x hx ↦ hconv.tendsto_at (hKU hx)) (Eventually.of_forall fun n ↦ hC (φ n))⟩

section Lipschitz

open ContinuousMap
open scoped NNReal unitInterval

/-- The `C`-Lipschitz maps whose value at `x₀` lies in a closed set `K` form a compact subset
of `C(X, Y)` when the closed `(C * dist x x₀)`-thickening of `K` is compact for every `x`. -/
theorem isCompact_setOf_lipschitzWith_apply_mem_of_forall_isCompact_cthickening
    {X Y : Type*} [PseudoMetricSpace X] [PseudoEMetricSpace Y] (C : ℝ≥0) (x₀ : X)
    {K : Set Y} (hK : IsClosed K)
    (hKC : ∀ x : X, IsCompact (Metric.cthickening (C * dist x x₀) K)) :
    IsCompact {f : C(X, Y) | LipschitzWith C f ∧ f x₀ ∈ K} := by
  set A := {f : C(X, Y) | LipschitzWith C f ∧ f x₀ ∈ K}
  have hA : IsClosed A :=
    ((isClosed_setOfPred_lipschitzWith C).preimage continuous_coeFun).inter
      (hK.preimage (continuous_eval_const x₀))
  have hequi : Equicontinuous fun f : A ↦ ⇑(f : C(X, Y)) :=
    (LipschitzWith.uniformEquicontinuous _ C fun f ↦ f.property.1).equicontinuous
  have hball (x : X) : ∃ Q : Set Y, IsCompact Q ∧ ∀ f : A, (f : C(X, Y)) x ∈ Q := by
    refine ⟨_, hKC x, fun f ↦ Metric.mem_cthickening_of_edist_le _ _ _ _ f.property.2 ?_⟩
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal, ← edist_dist]
    exact f.property.1 x x₀
  have hrange := ArzelaAscoli.isCompact_closure_range_of_equicontinuous hequi hball
  rw [Subtype.range_coe] at hrange
  exact hrange.of_isClosed_subset hA subset_closure

/-- The `C`-Lipschitz paths on the unit interval whose value at a time `t₀` lies in a closed set
`K` form a compact subset of `C(I, Y)` when the closed `C`-thickening of `K` is compact. -/
theorem isCompact_setOf_lipschitzWith_apply_mem_of_isCompact_cthickening
    {Y : Type*} [PseudoEMetricSpace Y] (C : ℝ≥0) (t₀ : I)
    {K : Set Y} (hK : IsClosed K) (hKC : IsCompact (Metric.cthickening C K)) :
    IsCompact {f : C(I, Y) | LipschitzWith C f ∧ f t₀ ∈ K} :=
  isCompact_setOf_lipschitzWith_apply_mem_of_forall_isCompact_cthickening C t₀ hK fun t ↦
    hKC.of_isClosed_subset Metric.isClosed_cthickening
      (Metric.cthickening_mono
        (mul_le_of_le_one_right C.property (Real.dist_le_of_mem_Icc_01 t.property t₀.property)) K)

/-- For a proper target `Y`, the `C`-Lipschitz maps whose value at `x₀` lies in a compact set `K`
form a compact subset of `C(X, Y)`. -/
theorem isCompact_setOf_lipschitzWith_apply_mem {X Y : Type*} [PseudoMetricSpace X]
    [MetricSpace Y] [ProperSpace Y] (C : ℝ≥0) (x₀ : X) {K : Set Y}
    (hK : IsCompact K) : IsCompact {f : C(X, Y) | LipschitzWith C f ∧ f x₀ ∈ K} :=
  isCompact_setOf_lipschitzWith_apply_mem_of_forall_isCompact_cthickening C x₀ hK.isClosed
    fun _ ↦ hK.cthickening

variable {Y : Type*} [MetricSpace Y]

/-- The `C`-Lipschitz paths on the unit interval taking value `x` at `t₀` form a compact subset of
`C(I, Y)` when the closed ball of radius `C` about `x` is compact. -/
theorem isCompact_setOf_lipschitzWith_apply_eq_of_isCompact_closedBall (C : ℝ≥0) (t₀ : I)
    (x : Y) (hx : IsCompact (Metric.closedBall x C)) :
    IsCompact {f : C(I, Y) | LipschitzWith C f ∧ f t₀ = x} := by
  simpa only [mem_singleton_iff] using
    isCompact_setOf_lipschitzWith_apply_mem_of_isCompact_cthickening C t₀ isClosed_singleton
      ((Metric.cthickening_singleton x C.property).symm ▸ hx)

/-- For a proper target `Y`, the `C`-Lipschitz maps taking value `y` at `x₀` form a compact
subset of `C(X, Y)`. -/
theorem isCompact_setOf_lipschitzWith_apply_eq {X Y : Type*} [PseudoMetricSpace X]
    [MetricSpace Y] [ProperSpace Y] (C : ℝ≥0) (x₀ : X) (y : Y) :
    IsCompact {f : C(X, Y) | LipschitzWith C f ∧ f x₀ = y} := by
  simpa only [mem_singleton_iff] using
    isCompact_setOf_lipschitzWith_apply_mem C x₀ (isCompact_singleton (x := y))

end Lipschitz

end TauCeti
