/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.IntermediateValue
public import TauCeti.Analysis.Fredholm.SpectralFlow.Cutoff

/-!
# Spectral flow

The spectral flow of a continuous path `A` of bounded self-adjoint Fredholm operators on a Hilbert
space is the net number of eigenvalues of `A t` that cross `0` from below as `t` runs from `a` to
`b`. We follow Phillips' definition by finite spectral projections. Near each time `t₀` there is a
finite spectral cutoff `c` of `A t` for all `t` near `t₀`, and there the spectral count
`(A t).spectralCount c`, the number of eigenvalues in `[0, c)`, changes exactly by the crossings
of `0`. The spectral flow adds up these local changes.

Rather than choosing partitions, we package the local data as a *spectral flow primitive*: an
integer-valued function `g` such that near every point `g t - (A t).spectralCount c` is constant
for some finite spectral cutoff `c` there (`TauCeti.IsSpectralFlowPrimitive`). Two primitives on
a preconnected set differ by a constant, because the difference of the spectral counts at two
cutoffs is locally constant (`TauCeti.IsSpectralFlowPrimitive.sub_eq_sub`). On an interval of
`ℝ`, a continuous family with finite spectral cutoffs (for instance a path of self-adjoint
Fredholm operators, by `IsSelfAdjoint.exists_isFiniteSpectralCutoff_of_isFredholm`) has a
primitive, glued from the local spectral counts (`TauCeti.exists_isSpectralFlowPrimitive_uIcc`). The
spectral flow from `a` to `b` is then `g b - g a` for any primitive `g` on `[[a, b]]`
(`TauCeti.spectralFlow`); this is independent of every choice made, which is Phillips' partition
independence. It is additive under concatenation of paths and changes sign under reversal.

Uniqueness and gluing of primitives hold for families over any topological space, as needed for
homotopies; existence is proved for intervals.

## Main definitions

* `TauCeti.IsSpectralFlowPrimitive A s g`: `g` is a spectral flow primitive of `A` on `s`.
* `TauCeti.spectralFlow A a b`: the spectral flow of the path `A` from `a` to `b`.

## Main results

* `TauCeti.IsSpectralFlowPrimitive.of_forall_isFiniteSpectralCutoff`: on a set where `c` is a
  finite spectral cutoff throughout, the spectral count below `c` is a primitive.
* `TauCeti.IsSpectralFlowPrimitive.sub_eq_sub`: two primitives on a preconnected set differ by a
  constant.
* `TauCeti.IsSpectralFlowPrimitive.exists_union`: primitives on two closed sets with preconnected
  intersection glue to a primitive on their union.
* `TauCeti.exists_isSpectralFlowPrimitive_uIcc`: existence of primitives on intervals.
* `TauCeti.IsSpectralFlowPrimitive.spectralFlow_eq`: the spectral flow is computed by any
  primitive.
* `TauCeti.spectralFlow_add_spectralFlow`: additivity under concatenation.
* `TauCeti.spectralFlow_symm`: reversing the path negates the spectral flow.

## References

* J. Phillips, *Self-adjoint Fredholm operators and spectral flow*, Canad. Math. Bull. **39**
  (1996), 460–467.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33.
-/

public section

open Set Filter Topology

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAlgebra ℝ (E →L[𝕜] E)] [IsometricContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]
  {X : Type*} [TopologicalSpace X]

/-- A **spectral flow primitive** of a family `A` of operators on a set `s`: an integer-valued
function `g` such that near every point `x₀` of `s` some `c` is a finite spectral cutoff of the
operators `A x` and `g x - (A x).spectralCount c` is constant. For a path `A`, the spectral flow
from `a` to `b` is `g b - g a`. -/
def IsSpectralFlowPrimitive (A : X → E →L[𝕜] E) (s : Set X) (g : X → ℤ) : Prop :=
  ∀ x₀ ∈ s, ∃ c, ∀ᶠ x in 𝓝[s] x₀, IsFiniteSpectralCutoff (A x) c ∧
    g x - (A x).spectralCount c = g x₀ - (A x₀).spectralCount c

theorem isSpectralFlowPrimitive_iff {A : X → E →L[𝕜] E} {s : Set X} {g : X → ℤ} :
    IsSpectralFlowPrimitive A s g ↔ ∀ x₀ ∈ s, ∃ c, ∀ᶠ x in 𝓝[s] x₀,
      IsFiniteSpectralCutoff (A x) c ∧
        g x - (A x).spectralCount c = g x₀ - (A x₀).spectralCount c :=
  Iff.rfl

namespace IsSpectralFlowPrimitive

variable {A : X → E →L[𝕜] E} {s t : Set X} {g g₁ g₂ : X → ℤ}

/-- If `c` is a finite spectral cutoff of every `A x` with `x ∈ s`, then the spectral count below
`c` is a spectral flow primitive of `A` on `s`. -/
theorem of_forall_isFiniteSpectralCutoff {c : ℝ} (hc : ∀ x ∈ s, IsFiniteSpectralCutoff (A x) c) :
    IsSpectralFlowPrimitive A s fun x ↦ (A x).spectralCount c :=
  fun _ _ ↦ ⟨c, eventually_nhdsWithin_of_forall fun x hx ↦ ⟨hc x hx, by ring⟩⟩

theorem mono (h : IsSpectralFlowPrimitive A t g) (hst : s ⊆ t) : IsSpectralFlowPrimitive A s g :=
  fun x₀ hx₀ ↦ (h x₀ (hst hx₀)).imp fun _ hc ↦ nhdsWithin_mono x₀ hst hc

theorem add_const (h : IsSpectralFlowPrimitive A s g) (k : ℤ) :
    IsSpectralFlowPrimitive A s fun x ↦ g x + k :=
  fun x₀ hx₀ ↦ (h x₀ hx₀).imp fun _ hc ↦ hc.mono fun _ ⟨hcut, heq⟩ ↦ ⟨hcut, by linarith⟩

/-- The operators of a family with a spectral flow primitive on `s` are self-adjoint on `s`. -/
theorem isSelfAdjoint (h : IsSpectralFlowPrimitive A s g) {x : X} (hx : x ∈ s) :
    IsSelfAdjoint (A x) :=
  have ⟨_, hc⟩ := h x hx
  (hc.self_of_nhdsWithin hx).1.isSelfAdjoint

/-- Every point of `s` has a finite spectral cutoff, for a family with a primitive on `s`. -/
theorem exists_isFiniteSpectralCutoff (h : IsSpectralFlowPrimitive A s g) {x : X} (hx : x ∈ s) :
    ∃ c, IsFiniteSpectralCutoff (A x) c :=
  have ⟨c, hc⟩ := h x hx
  ⟨c, (hc.self_of_nhdsWithin hx).1⟩

variable [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]

/-- **Any finite spectral cutoff computes a primitive locally.** If `g` is a spectral flow
primitive of `A` on `s` and `c` is a finite spectral cutoff of `A x₀`, then
`g x - (A x).spectralCount c` is constant near `x₀` in `s`. -/
theorem eventually_sub_spectralCount_eq (h : IsSpectralFlowPrimitive A s g)
    (hA : ContinuousOn A s) {x₀ : X} (hx₀ : x₀ ∈ s) {c : ℝ}
    (hc : IsFiniteSpectralCutoff (A x₀) c) :
    ∀ᶠ x in 𝓝[s] x₀, g x - (A x).spectralCount c = g x₀ - (A x₀).spectralCount c := by
  obtain ⟨c', hc'⟩ := h x₀ hx₀
  have hcut' := (hc'.self_of_nhdsWithin hx₀).1
  have hT : Tendsto A (𝓝[s] x₀) (𝓝[{T | IsSelfAdjoint T}] (A x₀)) :=
    tendsto_nhdsWithin_iff.2 ⟨hA x₀ hx₀, eventually_nhdsWithin_of_forall fun _ ↦ h.isSelfAdjoint⟩
  filter_upwards [hc', hT.eventually (hc.eventually_spectralCount_sub_eq hcut')]
    with x ⟨_, hx⟩ hx'
  linarith

/-- **Primitives are unique up to a constant**: two spectral flow primitives of a continuous
family on a preconnected set have the same increments. -/
theorem sub_eq_sub (h₁ : IsSpectralFlowPrimitive A s g₁) (h₂ : IsSpectralFlowPrimitive A s g₂)
    (hA : ContinuousOn A s) (hs : IsPreconnected s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    g₁ y - g₁ x = g₂ y - g₂ x := by
  refine hs.induction₂ (fun x y ↦ g₁ y - g₁ x = g₂ y - g₂ x) (fun x hx ↦ ?_)
    (fun _ _ _ _ _ _ h h' ↦ by linarith) (fun _ _ _ _ h ↦ by linarith) hx hy
  obtain ⟨c, hc⟩ := h₁.exists_isFiniteSpectralCutoff hx
  filter_upwards [h₁.eventually_sub_spectralCount_eq hA hx hc,
    h₂.eventually_sub_spectralCount_eq hA hx hc] with y hy₁ hy₂
  linarith

/-- On a closed piece `s'` of `t` on which `g` agrees with a primitive `g'`, a finite spectral
cutoff at any point `x₀` of `t` computes `g` near `x₀` within `s'`. -/
private theorem eventually_nhdsWithin_sub_spectralCount_eq {s' : Set X} {g' : X → ℤ}
    (hprim : IsSpectralFlowPrimitive A s' g') (hA : ContinuousOn A s') (hcl : IsClosed s')
    (hgg' : ∀ x ∈ s', g x = g' x) {x₀ : X} {c : ℝ} (hc : IsFiniteSpectralCutoff (A x₀) c) :
    ∀ᶠ x in 𝓝[s'] x₀, g x - (A x).spectralCount c = g x₀ - (A x₀).spectralCount c := by
  by_cases hx₀ : x₀ ∈ s'
  · filter_upwards [hprim.eventually_sub_spectralCount_eq hA hx₀ hc, self_mem_nhdsWithin]
      with x hx hxs
    rw [hgg' x hxs, hgg' x₀ hx₀, hx]
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hcl.isOpen_compl.mem_nhds hx₀)] with x h1 h2
    exact (h2 h1).elim

/-- **Gluing primitives.** Spectral flow primitives of a continuous family on two closed sets whose
intersection is preconnected glue to a primitive on their union. -/
theorem exists_union {s₁ s₂ : Set X} (h₁ : IsSpectralFlowPrimitive A s₁ g₁)
    (h₂ : IsSpectralFlowPrimitive A s₂ g₂) (hA : ContinuousOn A (s₁ ∪ s₂)) (hs₁ : IsClosed s₁)
    (hs₂ : IsClosed s₂) (hs : IsPreconnected (s₁ ∩ s₂)) :
    ∃ g, IsSpectralFlowPrimitive A (s₁ ∪ s₂) g := by
  classical
  -- Shift `g₂` so that it agrees with `g₁` on the overlap.
  obtain ⟨k, hk⟩ : ∃ k : ℤ, ∀ x ∈ s₁ ∩ s₂, g₁ x = g₂ x + k := by
    rcases (s₁ ∩ s₂).eq_empty_or_nonempty with he | ⟨z, hz⟩
    · exact ⟨0, by simp [he]⟩
    refine ⟨g₁ z - g₂ z, fun x hx ↦ ?_⟩
    have := (h₁.mono inter_subset_left).sub_eq_sub (h₂.mono inter_subset_right)
      (hA.mono (inter_subset_left.trans subset_union_left)) hs hz hx
    linarith
  have h₂' := h₂.add_const k
  set g : X → ℤ := s₁.piecewise g₁ fun x ↦ g₂ x + k
  have hg₁ : ∀ x ∈ s₁, g x = g₁ x := fun x hx ↦ piecewise_eq_of_mem _ _ _ hx
  have hg₂ : ∀ x ∈ s₂, g x = g₂ x + k := fun x hx ↦ by
    by_cases hx₁ : x ∈ s₁
    · rw [hg₁ x hx₁, hk x ⟨hx₁, hx⟩]
    · exact piecewise_eq_of_notMem _ _ _ hx₁
  have hsa : ∀ x ∈ s₁ ∪ s₂, IsSelfAdjoint (A x) := by
    rintro x (hx | hx)
    exacts [h₁.isSelfAdjoint hx, h₂.isSelfAdjoint hx]
  -- On each side, a cutoff at `x₀` computes the corresponding primitive near `x₀`.
  refine ⟨g, fun x₀ hx₀ ↦ ?_⟩
  obtain ⟨c, hc⟩ : ∃ c, IsFiniteSpectralCutoff (A x₀) c := by
    rcases hx₀ with hx₀ | hx₀
    exacts [h₁.exists_isFiniteSpectralCutoff hx₀, h₂.exists_isFiniteSpectralCutoff hx₀]
  refine ⟨c, (hc.eventually_of_continuousWithinAt (hA x₀ hx₀) hsa).and ?_⟩
  rw [nhdsWithin_union, eventually_sup]
  exact ⟨eventually_nhdsWithin_sub_spectralCount_eq h₁ (hA.mono subset_union_left) hs₁ hg₁ hc,
    eventually_nhdsWithin_sub_spectralCount_eq h₂' (hA.mono subset_union_right) hs₂ hg₂ hc⟩

end IsSpectralFlowPrimitive

variable [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]

/-- **Existence of spectral flow primitives on intervals.** A continuous family of operators on an
order-connected set `s ⊆ ℝ` each of which has a finite spectral cutoff, for instance a path of
self-adjoint Fredholm operators, has a spectral flow primitive on `[[a, b]]` for all `a, b ∈ s`. -/
theorem exists_isSpectralFlowPrimitive_uIcc {A : ℝ → E →L[𝕜] E} {s : Set ℝ} (hs : s.OrdConnected)
    (hA : ContinuousOn A s) (hc : ∀ x ∈ s, ∃ c, IsFiniteSpectralCutoff (A x) c) {a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) : ∃ g, IsSpectralFlowPrimitive A (uIcc a b) g := by
  have hsa : ∀ x ∈ s, IsSelfAdjoint (A x) := fun x hx ↦ (hc x hx).choose_spec.isSelfAdjoint
  refine hs.isPreconnected.induction₂' (fun x y ↦ ∃ g, IsSpectralFlowPrimitive A (uIcc x y) g)
    (fun x hx ↦ ?_) (fun x y z hx hy hz ⟨g₁, h₁⟩ ⟨g₂, h₂⟩ ↦ ?_) ha hb
  · -- Near `x`, one cutoff serves every point, and the spectral count itself is a primitive.
    obtain ⟨c, hcx⟩ := hc x hx
    obtain ⟨ε, hε, hball⟩ :=
      Metric.mem_nhdsWithin_iff.1 (hcx.eventually_of_continuousWithinAt (hA x hx) hsa)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hε)]
      with y hy hyb
    have hsub : uIcc x y ⊆ Metric.ball x ε ∩ s := by
      refine subset_inter ?_ (hs.uIcc_subset hx hy)
      rw [Real.ball_eq_Ioo]
      exact ordConnected_Ioo.uIcc_subset (by rw [← Real.ball_eq_Ioo]; exact Metric.mem_ball_self hε)
        (by rwa [← Real.ball_eq_Ioo])
    have hprim : IsSpectralFlowPrimitive A (uIcc x y) fun t ↦ (A t).spectralCount c :=
      .of_forall_isFiniteSpectralCutoff fun t ht ↦ hball (hsub ht)
    exact ⟨⟨_, hprim⟩, ⟨_, uIcc_comm x y ▸ hprim⟩⟩
  · -- Glue along `[[x, y]] ∩ [[y, z]]`, then restrict to `[[x, z]]`.
    obtain ⟨g, hg⟩ := h₁.exists_union h₂
      (hA.mono (union_subset (hs.uIcc_subset hx hy) (hs.uIcc_subset hy hz))) isClosed_Icc
      isClosed_Icc (ordConnected_uIcc.inter ordConnected_uIcc).isPreconnected
    exact ⟨g, hg.mono uIcc_subset_uIcc_union_uIcc⟩

open Classical in
/-- The **spectral flow** of a path `A` of self-adjoint operators from `a` to `b`: the increment
`g b - g a` of a spectral flow primitive `g` of `A` on `[[a, b]]`. Such a primitive exists when
`A` is continuous with finite spectral cutoffs, as for a path of self-adjoint Fredholm operators,
and then the increment does not depend on it (`TauCeti.IsSpectralFlowPrimitive.spectralFlow_eq`).
Without a primitive, the spectral flow is `0`. -/
noncomputable def spectralFlow (A : ℝ → E →L[𝕜] E) (a b : ℝ) : ℤ :=
  if h : ∃ g, IsSpectralFlowPrimitive A (uIcc a b) g then h.choose b - h.choose a else 0

omit [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)] in
/-- The spectral flow from a point to itself vanishes. -/
@[simp]
theorem spectralFlow_self (A : ℝ → E →L[𝕜] E) (a : ℝ) : spectralFlow A a a = 0 := by
  unfold spectralFlow
  split_ifs <;> simp

/-- **The spectral flow is computed by any primitive.** For a family `A` continuous on `[[a, b]]`
and any spectral flow primitive `g` of `A` on a set containing `[[a, b]]`, the spectral flow from
`a` to `b` is `g b - g a`. -/
theorem IsSpectralFlowPrimitive.spectralFlow_eq {A : ℝ → E →L[𝕜] E} {s : Set ℝ} {g : ℝ → ℤ}
    (h : IsSpectralFlowPrimitive A s g) {a b : ℝ} (hab : uIcc a b ⊆ s)
    (hA : ContinuousOn A (uIcc a b)) : spectralFlow A a b = g b - g a := by
  have h' := h.mono hab
  have hex : ∃ g, IsSpectralFlowPrimitive A (uIcc a b) g := ⟨g, h'⟩
  unfold spectralFlow
  split_ifs
  exact hex.choose_spec.sub_eq_sub h' hA isPreconnected_uIcc left_mem_uIcc right_mem_uIcc

variable {A : ℝ → E →L[𝕜] E} {s : Set ℝ} {a b : ℝ}

/-- **Concatenation.** For a continuous family with finite spectral cutoffs on an order-connected
set `s ⊆ ℝ`, the spectral flow from `a` to `b` and on to `c` is the spectral flow from `a` to
`c`. -/
theorem spectralFlow_add_spectralFlow (hs : s.OrdConnected) (hA : ContinuousOn A s)
    (hc : ∀ x ∈ s, ∃ c, IsFiniteSpectralCutoff (A x) c) {a b c : ℝ} (ha : a ∈ s) (hb : b ∈ s)
    (hc' : c ∈ s) : spectralFlow A a b + spectralFlow A b c = spectralFlow A a c := by
  obtain ⟨g₁, h₁⟩ := exists_isSpectralFlowPrimitive_uIcc hs hA hc ha hb
  obtain ⟨g₂, h₂⟩ := exists_isSpectralFlowPrimitive_uIcc hs hA hc hb hc'
  have hsub := union_subset (hs.uIcc_subset ha hb) (hs.uIcc_subset hb hc')
  obtain ⟨g, hg⟩ := h₁.exists_union h₂ (hA.mono hsub) isClosed_Icc isClosed_Icc
    (ordConnected_uIcc.inter ordConnected_uIcc).isPreconnected
  rw [hg.spectralFlow_eq subset_union_left (hA.mono (hs.uIcc_subset ha hb)),
    hg.spectralFlow_eq subset_union_right (hA.mono (hs.uIcc_subset hb hc')),
    hg.spectralFlow_eq uIcc_subset_uIcc_union_uIcc (hA.mono (hs.uIcc_subset ha hc'))]
  ring

/-- **Reversal.** For a continuous family with finite spectral cutoffs on `[[a, b]]`, running the
path backwards negates the spectral flow. -/
theorem spectralFlow_symm (hA : ContinuousOn A (uIcc a b))
    (hc : ∀ x ∈ uIcc a b, ∃ c, IsFiniteSpectralCutoff (A x) c) :
    spectralFlow A b a = -spectralFlow A a b := by
  obtain ⟨g, hg⟩ := exists_isSpectralFlowPrimitive_uIcc ordConnected_uIcc hA hc left_mem_uIcc
    right_mem_uIcc
  rw [hg.spectralFlow_eq le_rfl hA, hg.spectralFlow_eq (uIcc_comm b a).le (uIcc_comm a b ▸ hA)]
  ring

/-- **A single upward crossing.** On a finite-dimensional space, along the scalar path
`t ↦ t • 1` from `-1` to `1` every eigenvalue crosses `0` upwards once, so the spectral flow is the
dimension. For `E = 𝕜` it is `1`, as for the path `t ↦ tanh t`. -/
theorem spectralFlow_algebraMap_neg_one_one [FiniteDimensional 𝕜 E] :
    spectralFlow (algebraMap ℝ (E →L[𝕜] E)) (-1) 1 = Module.finrank 𝕜 E := by
  set A := algebraMap ℝ (E →L[𝕜] E)
  have hcut : ∀ t ∈ uIcc (-1 : ℝ) 1, IsFiniteSpectralCutoff (A t) 2 := fun t ht ↦ by
    rw [uIcc_of_le (by norm_num)] at ht
    have hsp := CFC.spectrum_algebraMap_subset (A := E →L[𝕜] E) (p := IsSelfAdjoint) t
    exact ⟨cfc_predicate_algebraMap t, two_pos,
      fun h ↦ by linarith [ht.2, mem_singleton_iff.1 (hsp h)],
      fun h ↦ by linarith [ht.1, mem_singleton_iff.1 (hsp h)], inferInstance⟩
  -- Instance search does not find the bounded scalar action of an abstract normed real algebra
  -- structure on the operators, so it is supplied from the normed space structure.
  have := NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[𝕜] E)
  rw [(IsSpectralFlowPrimitive.of_forall_isFiniteSpectralCutoff hcut).spectralFlow_eq le_rfl
    (continuous_algebraMap ℝ _).continuousOn, ContinuousLinearMap.spectralCount_def,
    ContinuousLinearMap.spectralCount_def, cfc_algebraMap, cfc_algebraMap]
  rw [indicator_of_mem (by norm_num : (1 : ℝ) ∈ Ico 0 2),
    indicator_of_notMem (by norm_num : (-1 : ℝ) ∉ Ico 0 2), Pi.one_apply, map_one, map_zero]
  rw [ContinuousLinearMap.toLinearMap_one, ContinuousLinearMap.toLinearMap_zero,
    Module.End.one_eq_id, LinearMap.range_id, LinearMap.range_zero, finrank_top, finrank_bot]
  ring

end TauCeti
