/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
public import TauCeti.Topology.Homotopy.AddCircle

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

/-- A homotopy missing `K` followed by a null-homotopy missing `K` is a null-homotopy missing
`K`. -/
private theorem exists_homotopy_const_of_homotopy {Z : Type*} [TopologicalSpace Z] {K : Set X}
    {f g : C(Z, X)} (F : Homotopy f g) (hF : ∀ z, F z ∉ K)
    (hg : ∃ p ∉ K, ∃ H : Homotopy g (const Z p), ∀ z, H z ∉ K) :
    ∃ p ∉ K, ∃ H : Homotopy f (const Z p), ∀ z, H z ∉ K := by
  obtain ⟨p, hp, H, hH⟩ := hg
  refine ⟨p, hp, F.trans H, fun z => ?_⟩
  rw [Homotopy.trans_apply]
  split_ifs
  exacts [hF _, hH _]

namespace SimplyConnectedAtInfinity

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
  intro K hK
  obtain ⟨L, hL, -, hXL⟩ := hX (f ⁻¹' K) (hf.isCompact_preimage hK)
  -- the points of `Y` whose track under `H` meets `K`
  have hC : IsCompact (Prod.snd '' (H ⁻¹' K)) := (hH.isCompact_preimage hK).image continuous_snd
  refine ⟨K ∪ Prod.snd '' (H ⁻¹' K) ∪ g ⁻¹' L, (hK.union hC).union (hg.isCompact_preimage hL),
    subset_union_left.trans subset_union_left, fun γ hγ => ?_⟩
  obtain ⟨p, hp, G, hG⟩ := hXL (g.comp γ) fun z hz => hγ z (Or.inr hz)
  refine exists_homotopy_const_of_homotopy
    ((H.symm.compContinuousMap γ).cast (ContinuousMap.id_comp γ) (ContinuousMap.comp_assoc _ _ _))
    (fun z hz => hγ z.2 (Or.inl (Or.inr ⟨(σ z.1, γ z.2), by simpa using hz, rfl⟩)))
    ⟨f p, hp, ((Homotopy.refl f).comp G).cast rfl (ContinuousMap.comp_const f p),
      fun z => by simpa using hG z⟩

end SimplyConnectedAtInfinity

/-- A real normed space of rank greater than two in which closed balls are compact is simply
connected at infinity. For a compact `K` inside the closed ball of radius `R`, a circle missing
that ball is pushed radially onto the sphere of radius `R + 1`, which is simply connected, without
entering the ball. -/
theorem simplyConnectedAtInfinity_of_two_lt_rank {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] (h : 2 < Module.rank ℝ E) : SimplyConnectedAtInfinity E := by
  intro K hK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  set R := max r 0
  have hKR : K ⊆ closedBall 0 R := hr.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hout {x : E} (hx : R < ‖x‖) : x ∉ K := fun hxK =>
    (mem_closedBall_zero_iff.1 (hKR hxK)).not_gt hx
  refine ⟨closedBall 0 R, isCompact_closedBall 0 R, hKR, fun f hf => ?_⟩
  have hfR (z) : R < ‖f z‖ := not_le.1 fun h => hf z (mem_closedBall_zero_iff.2 h)
  have hf0 (z) : 0 < ‖f z‖ := (le_max_right r 0).trans_lt (hfR z)
  have hR : 0 ≤ R + 1 := by positivity
  have := simplyConnectedSpace_sphere h (0 : E) hR
  -- the radial projection of `f` onto the sphere of radius `R + 1`
  have hmem (z) : ((R + 1) / ‖f z‖) • f z ∈ sphere (0 : E) (R + 1) := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg hR,
      abs_norm, div_mul_cancel₀ _ (hf0 z).ne']
  have hcont : Continuous fun z => ((R + 1) / ‖f z‖) • f z :=
    (continuous_const.div (by fun_prop) fun z => (hf0 z).ne').smul f.continuous
  let g : C(AddCircle (1 : ℝ), sphere (0 : E) (R + 1)) := ⟨_, hcont.subtype_mk hmem⟩
  obtain ⟨q, ⟨G⟩⟩ := nullhomotopic_addCircle_of_simplyConnectedSpace g
  let ι : C(sphere (0 : E) (R + 1), E) := ⟨Subtype.val, continuous_subtype_val⟩
  have hι (y : sphere (0 : E) (R + 1)) : ι y ∉ K := hout (by
    rw [show ‖ι y‖ = R + 1 from norm_eq_of_mem_sphere y]
    linarith)
  -- the straight-line homotopy from `f` to its radial projection, along rays out of the ball
  let F : Homotopy f (ι.comp g) :=
    { toFun := fun x => ((1 - x.1 : ℝ) + x.1 * ((R + 1) / ‖f x.2‖)) • f x.2
      continuous_toFun := by
        refine Continuous.smul ?_ (f.continuous.comp continuous_snd)
        exact (continuous_const.sub (by fun_prop)).add ((by fun_prop : Continuous fun x :
          I × AddCircle (1 : ℝ) => (x.1 : ℝ)).mul (continuous_const.div (by fun_prop)
            fun x => (hf0 x.2).ne'))
      map_zero_left := fun z => by simp
      map_one_left := fun z => by simp [ι, g] }
  refine exists_homotopy_const_of_homotopy F (fun x => hout ?_)
    ⟨ι q, hι q, ((Homotopy.refl ι).comp G).cast rfl (ContinuousMap.comp_const ι q),
      fun z => by simpa using hι (G z)⟩
  -- the norm along the straight-line homotopy is a convex combination of `‖f z‖` and `R + 1`
  obtain ⟨t, z⟩ := x
  obtain ⟨ht₀, ht₁⟩ := t.2
  have hc : 0 ≤ (1 - t : ℝ) + t * ((R + 1) / ‖f z‖) := by
    have := hf0 z
    positivity
  -- unfold the value of the straight-line homotopy `F` at `(t, z)`
  change R < ‖((1 - t : ℝ) + t * ((R + 1) / ‖f z‖)) • f z‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, add_mul, mul_assoc,
    div_mul_cancel₀ _ (hf0 z).ne']
  have := mul_nonneg (sub_nonneg.2 ht₁) (sub_nonneg.2 (hfR z).le)
  rcases ht₀.eq_or_lt with ht | ht
  · rw [← ht]
    linarith [hfR z]
  · linarith

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
    obtain ⟨L, hL, -, hf⟩ := h (K n) (K.isCompact n)
    obtain ⟨m, hm⟩ := K.exists_superset_of_isCompact hL
    exact ⟨m, fun f hfm => hf f fun z hz => hfm z (hm hz)⟩
  · intro h C hC
    obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hC
    obtain ⟨m, hm⟩ := h n
    refine ⟨C ∪ K m, hC.union (K.isCompact m), Set.subset_union_left, fun f hf => ?_⟩
    obtain ⟨p, hp, H, hH⟩ := hm f fun z hz => hf z (Or.inr hz)
    exact ⟨p, fun h => hp (hn h), H, fun z h => hH z (hn h)⟩

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous map `f : X → Y` is a **proper homotopy equivalence** if it is proper and has a
proper homotopy inverse `g`, with both homotopies `g ∘ f ≃ id` and `f ∘ g ≃ id` proper as maps
`I × X → X` and `I × Y → Y`. -/
def HasProperHomotopyInverse (f : C(X, Y)) : Prop :=
  IsProperMap f ∧ ∃ g : C(Y, X), IsProperMap g ∧
    ∃ H : Homotopy (g.comp f) (ContinuousMap.id X), ∃ H' : Homotopy (f.comp g) (ContinuousMap.id Y),
      IsProperMap H ∧ IsProperMap H'

/-- **Simple connectivity at infinity is invariant under proper homotopy equivalences.** -/
theorem HasProperHomotopyInverse.simplyConnectedAtInfinity_iff {f : C(X, Y)}
    (hf : f.HasProperHomotopyInverse) :
    TauCeti.SimplyConnectedAtInfinity X ↔ TauCeti.SimplyConnectedAtInfinity Y := by
  obtain ⟨hf, g, hg, H, H', hH, hH'⟩ := hf
  exact ⟨fun h => h.of_isProperMap hf hg H' hH', fun h => h.of_isProperMap hg hf H hH⟩

end ContinuousMap

/-- A homeomorphism is a proper homotopy equivalence, with constant homotopies: these are the
projections `I × X → X` and `I × Y → Y`, which are proper as `I` is compact. -/
theorem Homeomorph.hasProperHomotopyInverse {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) : (e : C(X, Y)).HasProperHomotopyInverse := by
  refine ⟨e.isProperMap, e.symm, e.symm.isProperMap,
    (ContinuousMap.Homotopy.refl _).cast rfl e.symm_comp_toContinuousMap,
    (ContinuousMap.Homotopy.refl _).cast rfl e.toContinuousMap_comp_symm, ?_, ?_⟩ <;>
  · convert isProperMap_snd_of_compactSpace (X := I) using 1
    ext x
    simp

/-- **Simple connectivity at infinity is invariant under homeomorphisms.** -/
theorem Homeomorph.simplyConnectedAtInfinity_iff {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) :
    TauCeti.SimplyConnectedAtInfinity X ↔ TauCeti.SimplyConnectedAtInfinity Y :=
  e.hasProperHomotopyInverse.simplyConnectedAtInfinity_iff
