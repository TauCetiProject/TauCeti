/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Topology.MetricSpace.Pseudo.Real
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
public import Mathlib.Topology.UnitInterval

import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Completion
import TauCeti.Algebra.Order.Floor.Ring
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
* `IsCompact.equicontinuous`: a compact set of continuous maps on a weakly locally compact space
  is equicontinuous.
* `TauCeti.exists_tendstoUniformly_subseq_of_periodic_of_modulus`: Arzelà–Ascoli for periodic
  loops with a common modulus of continuity.
* `TauCeti.isCompact_setOf_periodic_lipschitzWith`: the `1`-periodic `L`-Lipschitz loops in a
  compact set are compact for uniform convergence on `ℝ`.
* `TauCeti.exists_subseq_tendstoLocallyUniformly_of_lipschitzOnWith`: Arzelà–Ascoli for maps that
  are uniformly Lipschitz with values in a compact set on exhausting bands of the plane.
* `TauCeti.exists_subseq_tendstoLocallyUniformly_comp_add`: translates `u(s + σₙ, t)`, `σₙ → ∞`,
  of a Lipschitz map on a half-plane `s ≥ b` with values in a compact set have a locally
  uniformly convergent subsequence.
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
      (hPeq.comp fun g : S ↦ (⟨⇑(g : C(X, Y)), g.2⟩ : P))
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
          (hg x x.2).image (UniformSpace.Completion.uniformContinuous_coe Y)
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
  let G : ℕ → C(Icc (0 : ℝ) 1, M) := fun n ↦ ⟨fun t ↦ y n t, (hy n).comp continuous_subtype_val⟩
  have hGeq : Equicontinuous fun n ↦ ⇑(G n) := by
    refine Metric.equicontinuous_of_continuity_modulus ρ hρ _ fun t₁ t₂ n ↦ ?_
    rw [Subtype.dist_eq, Real.dist_eq]
    rcases le_total (t₁ : ℝ) t₂ with h | h
    · rw [dist_comm, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
      exact hmod n t₁ t₁.2 t₂ t₂.2 h
    · rw [abs_of_nonneg (sub_nonneg.2 h)]
      exact hmod n t₂ t₂.2 t₁ t₁.2 h
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

/-- **Arzelà–Ascoli along exhausting bands.** Let `w n` be `L`-Lipschitz on the band
`[-R n, R n] × ℝ` of `ℝ × ℝ`, with values there in a compact subset `K` of a pseudometric space,
where `0 ≤ R n → ∞`. A subsequence of the `w n` converges locally uniformly on `ℝ × ℝ` to a
continuous map. For instance, `w n` may be a sequence of solutions of an equation translated along
an end, on bands where the solutions are known to have bounded derivatives. -/
theorem exists_subseq_tendstoLocallyUniformly_of_lipschitzOnWith {M : Type*}
    [PseudoMetricSpace M] {K : Set M} (hK : IsCompact K) {w : ℕ → ℝ × ℝ → M} {R : ℕ → ℝ}
    {L : NNReal} (hR₀ : ∀ n, 0 ≤ R n) (hR : Tendsto R atTop atTop)
    (hL : ∀ n, LipschitzOnWith L (w n) (Icc (-R n) (R n) ×ˢ univ))
    (hwK : ∀ n, MapsTo (w n) (Icc (-R n) (R n) ×ˢ univ) K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : C(ℝ × ℝ, M),
      TendstoLocallyUniformly (fun n ↦ w (φ n)) g atTop := by
  -- The maps, with the first coordinate clamped to `[-R n, R n]`, are uniformly Lipschitz on the
  -- whole plane.
  set p : ℕ → ℝ × ℝ → ℝ × ℝ := fun n z ↦ (max (-R n) (min z.1 (R n)), z.2)
  have hp (n : ℕ) : LipschitzWith 1 (p n) := by
    simpa using ((LipschitzWith.prod_fst.min_const (R n)).const_max (-R n)).prodMk
      LipschitzWith.prod_snd
  have hpR (n : ℕ) (z : ℝ × ℝ) : p n z ∈ Icc (-R n) (R n) ×ˢ univ :=
    ⟨⟨le_max_left _ _, max_le (by linarith [hR₀ n]) (min_le_right _ _)⟩, mem_univ _⟩
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
  obtain ⟨m, hm⟩ := (hC.image (by fun_prop : Continuous fun z : ℝ × ℝ ↦ |z.1|)).bddAbove
  refine (hgw C hC).congr ?_
  filter_upwards [(hR.comp hφ.tendsto_atTop).eventually_ge_atTop m] with n hn z hz
  have hmz : |z.1| ≤ m := hm (mem_image_of_mem _ hz)
  simp only [Function.comp_apply] at hn
  rw [abs_le] at hmz
  simp only [G, ContinuousMap.coe_mk, w', p, Function.comp_apply,
    min_eq_left (by linarith : z.1 ≤ R (φ n)), max_eq_right (by linarith : -R (φ n) ≤ z.1)]

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
  -- From the index `N` on, the band `[-(σₙ - b), σₙ - b] × ℝ` is translated into `s ≥ b`.
  obtain ⟨N, hN⟩ := (hσ.eventually_ge_atTop b).exists_forall_of_atTop
  have hR : Tendsto (fun n ↦ σ (n + N) - b) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (hσ.comp (tendsto_add_atTop_nat N))
  have hmaps (n : ℕ) : MapsTo (fun z : ℝ × ℝ ↦ z + (σ (n + N), 0))
      (Icc (-(σ (n + N) - b)) (σ (n + N) - b) ×ˢ univ) (Ici b ×ˢ univ) := fun z hz ↦
    ⟨mem_Ici.2 (by simp only [Prod.fst_add]; linarith [hz.1.1]), mem_univ _⟩
  have hadd (n : ℕ) : LipschitzWith 1 fun z : ℝ × ℝ ↦ z + (σ (n + N), 0) :=
    (IsometryEquiv.addRight ((σ (n + N), 0) : ℝ × ℝ)).isometry.lipschitzWith
  obtain ⟨φ, hφ, g, htr⟩ := exists_subseq_tendstoLocallyUniformly_of_lipschitzOnWith hK
    (fun n ↦ sub_nonneg.2 (hN _ (Nat.le_add_left N n))) hR
    (fun n ↦ by simpa using hL.comp ((hadd n).lipschitzOnWith) (hmaps n))
    fun n ↦ huK.comp (hmaps n)
  exact ⟨fun n ↦ φ n + N, fun m n hmn ↦ Nat.add_lt_add_right (hφ hmn) N, g, htr⟩

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
    (LipschitzWith.uniformEquicontinuous _ C fun f ↦ f.2.1).equicontinuous
  have hball (x : X) : ∃ Q : Set Y, IsCompact Q ∧ ∀ f : A, (f : C(X, Y)) x ∈ Q := by
    refine ⟨_, hKC x, fun f ↦ Metric.mem_cthickening_of_edist_le _ _ _ _ f.2.2 ?_⟩
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal, ← edist_dist]
    exact f.2.1 x x₀
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
        (mul_le_of_le_one_right C.2 (Real.dist_le_of_mem_Icc_01 t.2 t₀.2)) K)

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
      ((Metric.cthickening_singleton x C.2).symm ▸ hx)

/-- For a proper target `Y`, the `C`-Lipschitz maps taking value `y` at `x₀` form a compact
subset of `C(X, Y)`. -/
theorem isCompact_setOf_lipschitzWith_apply_eq {X Y : Type*} [PseudoMetricSpace X]
    [MetricSpace Y] [ProperSpace Y] (C : ℝ≥0) (x₀ : X) (y : Y) :
    IsCompact {f : C(X, Y) | LipschitzWith C f ∧ f x₀ = y} := by
  simpa only [mem_singleton_iff] using
    isCompact_setOf_lipschitzWith_apply_mem C x₀ (isCompact_singleton (x := y))

end Lipschitz

end TauCeti
