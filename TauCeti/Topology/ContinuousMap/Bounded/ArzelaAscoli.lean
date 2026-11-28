/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.UniformSpace.Equicontinuity
import TauCeti.Topology.ContinuousMap.Ascoli
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Compact operators into spaces of bounded continuous functions

Let `F` be a pseudometric space and `α` a compact space. An operator `T : E → α →ᵇ F` is
compact as soon as it maps a neighborhood of `0` to an equicontinuous family whose values at
each point lie in a compact set (`TauCeti.isCompactOperator_of_equicontinuous`). This is the
Arzelà–Ascoli theorem in operator form.

In the form used for restriction maps, an operator `E → β →ᵇ F` that reads the functions
`Φ f : α → F` along a continuous map `j : β → α` with values in a compact set `K` is compact as
soon as a neighborhood of `0` gives a family that is equicontinuous on `K` with pointwise
relatively compact values there (`IsCompact.isCompactOperator_of_equicontinuousOn`). For spaces
of bounded holomorphic functions, Cauchy estimates give the equicontinuity, and the result is
Montel's theorem.

In sequential form, a sequence of functions on a compact set `S` with a common modulus of
continuity, whose values on `S` are uniformly close to compact sets, has a subsequence that is
uniformly Cauchy on `S` (`TauCeti.exists_subseq_uniformCauchySeqOn_of_continuity_modulus`).
-/

public section

open BoundedContinuousFunction Set Filter
open scoped Topology

variable {E α β F : Type*} [TopologicalSpace E] [Zero E] [TopologicalSpace α]
  [TopologicalSpace β] [PseudoMetricSpace F]

namespace TauCeti

/-- **Arzelà–Ascoli for operators.** Let `α` be compact. If an operator `T : E → α →ᵇ F` maps
a neighborhood `V` of `0` to an equicontinuous family whose values at each point lie in a
compact set, then `T` is a compact operator. -/
theorem isCompactOperator_of_equicontinuous [CompactSpace α] {T : E → α →ᵇ F} {V : Set E}
    (hV : V ∈ 𝓝 0) (hTV : ∀ x, ∃ Q : Set F, IsCompact Q ∧ ∀ f ∈ V, T f x ∈ Q)
    (hT : Equicontinuous fun f : V => (T f : α → F)) :
    IsCompactOperator T := by
  let e := ContinuousMap.isometryEquivBoundedOfCompact α F
  have h := ArzelaAscoli.isCompact_closure_range_of_equicontinuous (f := fun f : V => e.symm (T f))
    hT fun x => let ⟨Q, hQ, hTQ⟩ := hTV x; ⟨Q, hQ, fun f => hTQ f f.property⟩
  refine ⟨_, h.image e.continuous, Filter.mem_of_superset hV fun f hf => ?_⟩
  exact ⟨_, subset_closure ⟨⟨f, hf⟩, rfl⟩, e.apply_symm_apply _⟩

/-- **Arzelà–Ascoli for sequences.** Let `S` be a compact set in a pseudometric space and let the
functions `v n` have the common modulus of continuity `b` on `S`, with `b d → 0` as `d → 0`. If for
every `δ > 0` the values of all `v n` on `S` lie within `δ` of some compact set, then a subsequence
of `v n` is uniformly Cauchy on `S`. -/
theorem exists_subseq_uniformCauchySeqOn_of_continuity_modulus {T G : Type*}
    [PseudoMetricSpace T] [MetricSpace G] [CompleteSpace G] {S : Set T} (hS : IsCompact S)
    {b : ℝ → ℝ} (hb : Tendsto b (𝓝 0) (𝓝 0)) {v : ℕ → T → G}
    (hmod : ∀ n, ∀ s ∈ S, ∀ t ∈ S, dist (v n s) (v n t) ≤ b (dist s t))
    (happrox : ∀ δ > 0, ∃ Q, IsCompact Q ∧ ∀ n, ∀ t ∈ S, ∃ q ∈ Q, dist (v n t) q ≤ δ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ UniformCauchySeqOn (fun n ↦ v (φ n)) atTop S := by
  have : CompactSpace S := isCompact_iff_compactSpace.1 hS
  have hcont : Equicontinuous fun n (t : S) ↦ v n t :=
    Metric.equicontinuous_of_continuity_modulus b hb _ fun s t n ↦ hmod n s s.property t t.property
  let F : ℕ → S →ᵇ G := fun n ↦ mkOfCompact ⟨fun t ↦ v n t, hcont.continuous n⟩
  have hF : ∀ n (t : S), F n t = v n t := fun _ _ ↦ rfl
  -- The set of all values of all the `F n` is totally bounded, so its closure is compact.
  have hV : TotallyBounded (⋃ n, range (F n)) := by
    refine Metric.totallyBounded_iff.2 fun ε hε ↦ ?_
    obtain ⟨Q, hQ, hQv⟩ := happrox (ε / 2) (half_pos hε)
    obtain ⟨R, -, hR, hQR⟩ := finite_cover_balls_of_compact hQ (half_pos hε)
    refine ⟨R, hR, ?_⟩
    rintro _ ⟨_, ⟨n, rfl⟩, ⟨t, rfl⟩⟩
    obtain ⟨q, hq, hqv⟩ := hQv n t t.property
    obtain ⟨y, hy, hqy⟩ := mem_iUnion₂.1 (hQR hq)
    refine mem_iUnion₂.2 ⟨y, hy, Metric.mem_ball.2 ?_⟩
    calc dist (F n t) y ≤ dist (F n t) q + dist q y := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hqv (Metric.mem_ball.1 hqy)
      _ = ε := add_halves ε
  have heq : Equicontinuous ((↑) : range F → S → G) :=
    Metric.equicontinuous_of_continuity_modulus b hb _ fun s t ⟨_, n, hn⟩ ↦ by
      subst hn; exact hmod n s s.property t t.property
  obtain ⟨H, -, φ, hφ, hlim⟩ := (BoundedContinuousFunction.arzela_ascoli _
    (hV.closure.isCompact_of_isClosed isClosed_closure) (range F)
    (by rintro _ t ⟨n, rfl⟩; exact subset_closure (mem_iUnion.2 ⟨n, t, rfl⟩)) heq).tendsto_subseq
    (fun n ↦ subset_closure ⟨n, rfl⟩)
  refine ⟨φ, hφ, Metric.uniformCauchySeqOn_iff.2 fun δ hδ ↦ ?_⟩
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hlim.cauchySeq δ hδ
  refine ⟨N, fun m hm n hn t ht ↦ ?_⟩
  rw [← hF _ ⟨t, ht⟩, ← hF _ ⟨t, ht⟩]
  exact (BoundedContinuousFunction.dist_coe_le_dist _).trans_lt (hN m hm n hn)

end TauCeti

/-- **Arzelà–Ascoli for restriction operators.** Let `T` send `f : E` to the function
`Φ f ∘ j` in `β →ᵇ F`, where `j` takes values in a compact set `K`. If `Φ` maps a neighborhood
`V` of `0` to a family that is equicontinuous on `K` and whose values at each point of `K` lie in
a compact set, then `T` is a compact operator. -/
theorem IsCompact.isCompactOperator_of_equicontinuousOn {K : Set α} (hK : IsCompact K)
    (j : C(β, α)) (hjK : ∀ z, j z ∈ K) {Φ : E → α → F} {T : E → β →ᵇ F}
    (hT : ∀ f z, T f z = Φ f (j z)) {V : Set E} (hV : V ∈ 𝓝 0)
    (hΦV : ∀ x ∈ K, ∃ Q : Set F, IsCompact Q ∧ ∀ f ∈ V, Φ f x ∈ Q)
    (hs : EquicontinuousOn (fun f : V => Φ f) K) :
    IsCompactOperator T := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let σ : C(β, K) := ⟨fun z => ⟨j z, hjK z⟩, j.continuous.subtype_mk _⟩
  -- Only the functions indexed by `V` matter; `p` projects every `f` to one of them, and
  -- equicontinuity makes each `Φ (p f)` continuous on `K`.
  classical
  let p : E → V := fun f => if h : f ∈ V then ⟨f, h⟩ else ⟨0, mem_of_mem_nhds hV⟩
  obtain ⟨Q, hQ, hRQ⟩ := TauCeti.isCompactOperator_of_equicontinuous
    (T := fun f => mkOfCompact ⟨K.domRestrict (Φ (p f)), (hs.continuousOn (p f)).domRestrict⟩)
    hV (fun x => let ⟨Q, hQ, hΦQ⟩ := hΦV x x.property; ⟨Q, hQ, fun f _ => hΦQ _ (p f).property⟩)
    (((equicontinuous_restrict_iff _).mpr hs).comp fun f : V => p f)
  refine ⟨_, hQ.image (continuous_compContinuous σ),
    Filter.mem_of_superset (Filter.inter_mem hV hRQ) fun f hf => ⟨_, hf.right, ext fun z => ?_⟩⟩
  simp [p, hf.left, hT, σ]
