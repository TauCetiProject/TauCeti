/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
public import TauCeti.Topology.Homotopy.AddCircle
public import TauCeti.Topology.Homotopy.Proper
public import TauCeti.Topology.Homotopy.Trans
import TauCeti.Topology.Homotopy.StarConvexComplement

/-!
# Simple connectivity at infinity

A space `X` is *simply connected at infinity* (`TauCeti.SimplyConnectedAtInfinity`) when for every
compact `K ⊆ X` there is a compact `L ⊇ K` such that every continuous circle
`f : AddCircle 1 → X` missing `L` is null-homotopic in `X \ K`: there is a homotopy from `f` to a
constant map that never meets `K`. Loops far enough out can be contracted while staying out of any
prescribed compact set. This says nothing about connectedness at infinity or the number of ends,
which is a separate condition.

This is the hypothesis of the proper Whitehead theorem for simply connected complexes, and of the
characterizations of Euclidean space among contractible manifolds (Stallings, Siebenmann,
Freedman).

## Main results

* `TauCeti.simplyConnectedAtInfinity_iff` unfolds the definition, and
  `TauCeti.SimplyConnectedAtInfinity.exists_isCompact_superset` supplies, for a compact `K`, the
  compact `L ⊇ K` outside which circles contract away from `K`.
* `CompactExhaustion.simplyConnectedAtInfinity_iff`: along any compact exhaustion `K₀ ⊆ K₁ ⊆ ⋯`
  of `X`, simple connectivity at infinity says that for every `n` there is an `m` such that
  circles missing `Kₘ` are null-homotopic in `X \ Kₙ`. Any two compact exhaustions therefore give
  equivalent conditions; locally compact σ-compact spaces have one (`CompactExhaustion.choice`).
* `TauCeti.SimplyConnectedAtInfinity.of_isProperMap`: if proper maps `f : X → Y`, `g : Y → X`
  satisfy `f ∘ g ≃ id` through a proper homotopy `I × Y → Y`, then simple connectivity at
  infinity passes from `X` to `Y`.
* `ContinuousMap.HasProperHomotopyInverse.simplyConnectedAtInfinity_iff`: simple connectivity at
  infinity is invariant under proper homotopy equivalences, and in particular under
  homeomorphisms (`Homeomorph.simplyConnectedAtInfinity_iff`).
* `TauCeti.simplyConnectedAtInfinity_of_two_lt_rank`: a real normed space of rank greater than
  two in which closed balls are compact, for instance `ℝⁿ` for `n ≥ 3`
  (`TauCeti.simplyConnectedAtInfinity_euclideanSpace`), is simply connected at infinity: a circle
  outside a large ball pushes radially onto a sphere, which is simply connected.
  Compact spaces are simply connected at infinity
  (`TauCeti.SimplyConnectedAtInfinity.of_compactSpace`).

## References

* J. Stallings, *The piecewise-linear structure of Euclidean space*, Proc. Cambridge Philos. Soc.
  58 (1962), 481–488, for simple connectivity at infinity.
* F. T. Farrell, L. R. Taylor, J. B. Wagoner, *The Whitehead theorem in the proper category*,
  Compositio Math. 27 (1973), 1–23, for proper homotopy equivalences.
-/

public section

open Set Metric Topology ContinuousMap
open scoped unitInterval

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A space is **simply connected at infinity** if for every compact `K` there is a compact
`L ⊇ K` such that every continuous circle missing `L` is null-homotopic through a homotopy that
misses `K`. -/
def SimplyConnectedAtInfinity (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ K : Set X, IsCompact K → ∃ L : Set X, IsCompact L ∧ K ⊆ L ∧
    ∀ f : C(AddCircle (1 : ℝ), X), (∀ z, f z ∉ L) →
      ∃ p ∉ K, ∃ H : Homotopy f (const (AddCircle (1 : ℝ)) p), ∀ z, H z ∉ K

/-- The defining property of simple connectivity at infinity: for every compact `K` there is a
compact `L ⊇ K` such that every continuous circle missing `L` is null-homotopic through a homotopy
that misses `K`. -/
theorem simplyConnectedAtInfinity_iff : SimplyConnectedAtInfinity X ↔
    ∀ K : Set X, IsCompact K → ∃ L : Set X, IsCompact L ∧ K ⊆ L ∧
      ∀ f : C(AddCircle (1 : ℝ), X), (∀ z, f z ∉ L) →
        ∃ p ∉ K, ∃ H : Homotopy f (const (AddCircle (1 : ℝ)) p), ∀ z, H z ∉ K :=
  Iff.rfl

namespace SimplyConnectedAtInfinity

/-- In a space simply connected at infinity, every compact `K` lies in a compact `L` such that
every continuous circle missing `L` is null-homotopic through a homotopy that misses `K`. -/
theorem exists_isCompact_superset (h : SimplyConnectedAtInfinity X) {K : Set X}
    (hK : IsCompact K) : ∃ L : Set X, IsCompact L ∧ K ⊆ L ∧
      ∀ f : C(AddCircle (1 : ℝ), X), (∀ z, f z ∉ L) →
        ∃ p ∉ K, ∃ H : Homotopy f (const (AddCircle (1 : ℝ)) p), ∀ z, H z ∉ K :=
  h K hK

/-- A compact space is simply connected at infinity: take `L` to be the whole space. -/
theorem of_compactSpace [CompactSpace X] : SimplyConnectedAtInfinity X :=
  fun _ _ => ⟨univ, isCompact_univ, subset_univ _, fun f hf => absurd (mem_univ (f 0)) (hf 0)⟩

/-- Simple connectivity at infinity passes to a space `Y` properly dominated by `X`: if `f : X → Y`
and `g : Y → X` are proper and `f ∘ g` is homotopic to the identity through a homotopy that is
proper as a map `I × Y → Y`, then `Y` is simply connected at infinity whenever `X` is.

A circle `γ` far out in `Y` is moved by `g` far out in `X`, contracted there away from
`f⁻¹(K)`, and the contraction is pushed back by `f`; the homotopy `f ∘ g ≃ id` joins `γ` to
`f ∘ g ∘ γ` away from `K` once `γ` misses the compact projection of the preimage of `K`. -/
theorem of_isProperMap (hX : SimplyConnectedAtInfinity X) {f : C(X, Y)} {g : C(Y, X)}
    (hf : IsProperMap f) (hg : IsProperMap g) (H : Homotopy (f.comp g) (ContinuousMap.id Y))
    (hH : IsProperMap H) : SimplyConnectedAtInfinity Y := by
  refine simplyConnectedAtInfinity_iff.2 fun K hK => ?_
  obtain ⟨L, hL, -, hXL⟩ := hX.exists_isCompact_superset (hf.isCompact_preimage hK)
  -- the points of `Y` whose track under `H` meets `K`
  have hC : IsCompact (Prod.snd '' (H ⁻¹' K)) := (hH.isCompact_preimage hK).image continuous_snd
  refine ⟨K ∪ Prod.snd '' (H ⁻¹' K) ∪ g ⁻¹' L, (hK.union hC).union (hg.isCompact_preimage hL),
    subset_union_left.trans subset_union_left, fun γ hγ => ?_⟩
  obtain ⟨p, hp, G, hG⟩ := hXL (g.comp γ) fun z hz => hγ z (Or.inr hz)
  let F := (H.symm.compContinuousMap γ).cast (ContinuousMap.id_comp γ)
    (ContinuousMap.comp_assoc _ _ _)
  have hF (z) : F z ∉ K := fun hz =>
    hγ z.2 (Or.inl (Or.inr ⟨(σ z.1, γ z.2), by simpa [F] using hz, rfl⟩))
  let G' := ((Homotopy.refl f).comp G).cast rfl (ContinuousMap.comp_const f p)
  have hG' (z) : G' z ∉ K := by simpa [G'] using hG z
  exact ⟨f p, hp, F.trans G', Homotopy.trans_apply_mem (S := Kᶜ) hF hG'⟩

end SimplyConnectedAtInfinity

/-- A real normed space of rank greater than two in which closed balls are compact is simply
connected at infinity. For a compact `K` inside the closed ball of radius `R`, a circle missing
that ball is pushed radially onto the sphere of radius `R + 1`, which is simply connected, without
entering the ball. -/
theorem simplyConnectedAtInfinity_of_two_lt_rank {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] (h : 2 < Module.rank ℝ E) : SimplyConnectedAtInfinity E := by
  refine simplyConnectedAtInfinity_iff.2 fun K hK => ?_
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  set R := max r 0
  have hKR : K ⊆ closedBall 0 R := hr.trans (closedBall_subset_closedBall (le_max_left _ _))
  refine ⟨closedBall 0 R, isCompact_closedBall 0 R, hKR, fun f hf => ?_⟩
  have h0 : (0 : E) ∈ closedBall 0 R := mem_closedBall_self (le_max_right r 0)
  have hB : closedBall (0 : E) R ⊆ ball 0 (R + 1) := closedBall_subset_ball (lt_add_one R)
  have hR : 0 < R + 1 := by linarith [le_max_right r 0]
  have : SimplyConnectedSpace (sphere (0 : E) (R + 1)) := simplyConnectedSpace_sphere h 0 hR.le
  -- `f` as a circle in the complement of the ball, and its radial projection onto the sphere
  let f' : C(AddCircle (1 : ℝ), ↥(closedBall (0 : E) R)ᶜ) := ⟨fun z => ⟨f z, hf z⟩, by fun_prop⟩
  let g := (complRadialProjection h0 hR).comp f'
  obtain ⟨q, ⟨G⟩⟩ := nullhomotopic_addCircle_of_simplyConnectedSpace g
  let j := ContinuousMap.inclusion (sphere_disjoint_ball.mono_right hB).subset_compl_right
  -- contract `f'` inside the complement: deform it radially onto the sphere, then contract there
  let F := ((convex_closedBall (0 : E) R).starConvex h0).complRadialHomotopy h0 hB
    |>.symm.compContinuousMap f' |>.cast (ContinuousMap.id_comp f') (ContinuousMap.comp_assoc _ _ _)
  let H := F.trans (((Homotopy.refl j).comp G).cast rfl (ContinuousMap.comp_const j q))
  exact ⟨j q, fun h => (j q).2 (hKR h),
    ((Homotopy.refl (ContinuousMap.subtypeVal _)).comp H).cast rfl
      (ContinuousMap.comp_const _ _), fun x h => (H x).2 (hKR h)⟩

/-- **`ℝⁿ` is simply connected at infinity for `n ≥ 3`.** -/
theorem simplyConnectedAtInfinity_euclideanSpace {n : ℕ} (hn : 3 ≤ n) :
    SimplyConnectedAtInfinity (EuclideanSpace ℝ (Fin n)) := by
  refine simplyConnectedAtInfinity_of_two_lt_rank ?_
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  exact_mod_cast (by omega : 2 < n)

end TauCeti

/-- Simple connectivity at infinity read along a compact exhaustion `K₀ ⊆ K₁ ⊆ ⋯`: for every `n`
there is an `m` such that every circle missing `Kₘ` is null-homotopic through a homotopy missing
`Kₙ`. In particular the condition does not depend on the chosen exhaustion. -/
theorem CompactExhaustion.simplyConnectedAtInfinity_iff {X : Type*} [TopologicalSpace X]
    (K : CompactExhaustion X) :
    TauCeti.SimplyConnectedAtInfinity X ↔ ∀ n, ∃ m, ∀ f : C(AddCircle (1 : ℝ), X),
      (∀ z, f z ∉ K m) →
        ∃ p ∉ K n, ∃ H : ContinuousMap.Homotopy f (ContinuousMap.const _ p), ∀ z, H z ∉ K n := by
  constructor
  · intro h n
    obtain ⟨L, hL, -, hf⟩ := h.exists_isCompact_superset (K.isCompact n)
    obtain ⟨m, hm⟩ := K.exists_superset_of_isCompact hL
    exact ⟨m, fun f hfm => hf f fun z hz => hfm z (hm hz)⟩
  · refine fun h => TauCeti.simplyConnectedAtInfinity_iff.2 fun C hC => ?_
    obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hC
    obtain ⟨m, hm⟩ := h n
    refine ⟨C ∪ K m, hC.union (K.isCompact m), Set.subset_union_left, fun f hf => ?_⟩
    obtain ⟨p, hp, H, hH⟩ := hm f fun z hz => hf z (Or.inr hz)
    exact ⟨p, fun h => hp (hn h), H, fun z h => hH z (hn h)⟩

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Simple connectivity at infinity is invariant under proper homotopy equivalences.** -/
theorem HasProperHomotopyInverse.simplyConnectedAtInfinity_iff {f : C(X, Y)}
    (hf : f.HasProperHomotopyInverse) :
    TauCeti.SimplyConnectedAtInfinity X ↔ TauCeti.SimplyConnectedAtInfinity Y := by
  obtain ⟨g, hg, H, H', hH, hH'⟩ := hf.exists_inverse
  have hf := hf.isProperMap
  exact ⟨fun h => h.of_isProperMap hf hg H' hH', fun h => h.of_isProperMap hg hf H hH⟩

end ContinuousMap

/-- **Simple connectivity at infinity is invariant under homeomorphisms.** -/
theorem Homeomorph.simplyConnectedAtInfinity_iff {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) :
    TauCeti.SimplyConnectedAtInfinity X ↔ TauCeti.SimplyConnectedAtInfinity Y :=
  e.hasProperHomotopyInverse.simplyConnectedAtInfinity_iff
