/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Gluing.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Compactifying local glued Morse trajectories

Record a trajectory through a split hyperbolic box by its entrance and exit points.
When these lie on transverse Lipschitz discs, their pairs form a half-open arc. Its closure
adds exactly the broken pair `((g 0, 0), (0, k 0))` and is homeomorphic to a closed interval.
The inverse coordinate is the norm of the expanding entrance coordinate divided by the
box radius. Thus the topology remembers both halves of a broken trajectory.

The contraction construction in
`TauCeti.exists_setOf_mem_splitPassage_source_graph_eq_image` supplies every unbroken
trajectory, not just a family approaching the broken one. Here it yields a topological boundary
chart for the local gluing problem. This does not compactify global trajectory spaces or
assert smoothness of the gluing chart.

For families of discs `g p` and `k p`, indexed by a compact set `S` of parameters, Lipschitz with
uniform constants and continuous in `p`, the closure of the pairs of all members adds exactly
their broken pairs, and it is compact. When any two distinct members have disjoint entrance discs
or disjoint exit discs, that closure is homeomorphic to `[0, r₀] × S`, with the broken pairs at
the parameter `0`. When the Morse indices of the broken trajectory are not consecutive, `p` ranges
over pairs of a trajectory into the middle critical point and a trajectory out of it, with `g p`
depending on the first and `k p` on the second. In the split box, this chart is the model from
which a collar along once-broken trajectories is expected to come.

## Main results

* `TauCeti.closure_splitGluingPairs`: precisely one broken pair is added.
* `TauCeti.exists_homeomorph_closure_splitGluingPairs`: a closed interval chart with explicit
  inverse coordinate and broken endpoint.
* `TauCeti.isCompact_closure_splitGluingPairs`: compactness of the paired local gluing space.
* `TauCeti.closure_biUnion_splitGluingPairs`: for a compact family of pairs of discs, precisely
  the broken pairs of its members are added.
* `TauCeti.isCompact_closure_biUnion_splitGluingPairs`: for a compact family of pairs of discs,
  compactness of the closure of their gluing pairs.
* `TauCeti.exists_homeomorph_closure_biUnion_splitGluingPairs`: for a compact family of pairs of
  discs, a chart by `[0, r₀] × S` with the gluing parameter as first coordinate and the broken
  pairs at `0`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (gluing with a pseudo-gradient linear near critical points).
-/

public section

open Function Metric Set Topology
open scoped NNReal

namespace TauCeti

variable {Eₛ Eᵤ : Type*} [NormedAddCommGroup Eₛ] [NormedSpace ℝ Eₛ]
  [NormedAddCommGroup Eᵤ] [NormedSpace ℝ Eᵤ]
  {ε r₀ : ℝ} {Kg Kk : ℝ≥0} {g : Eᵤ → Eₛ} {k : Eₛ → Eᵤ}

/-- Entrance and exit pairs of unbroken trajectories through the split box, with entrance
on the graph of `g`, exit on the graph of `k`, and gluing parameter at most `r₀`. -/
def splitGluingPairs (ε r₀ : ℝ) (g : Eᵤ → Eₛ) (k : Eₛ → Eᵤ) :
    Set (WithLp 2 (Eₛ × Eᵤ) × WithLp 2 (Eₛ × Eᵤ)) :=
  {p | p.1 ∈ (splitPassage ε).source ∧ ‖p.1.snd‖ ≤ r₀ * ε ∧
    p.1.fst = g p.1.snd ∧ p.2 = splitPassage ε p.1 ∧ p.2.snd = k p.2.fst}

/-- The entrance and exit conditions defining the unbroken gluing pairs. -/
@[simp]
theorem mem_splitGluingPairs {p : WithLp 2 (Eₛ × Eᵤ) × WithLp 2 (Eₛ × Eᵤ)} :
    p ∈ splitGluingPairs ε r₀ g k ↔
      p.1 ∈ (splitPassage ε).source ∧ ‖p.1.snd‖ ≤ r₀ * ε ∧
        p.1.fst = g p.1.snd ∧ p.2 = splitPassage ε p.1 ∧ p.2.snd = k p.2.fst :=
  Iff.rfl

/-- If the entrance points over `Ioc 0 r₀` are parametrized by an exhaustive family `w` of the
sphere of radius `ε`, then the entrance and exit pairs built from `w` over `Ioc 0 δ` are exactly the
pairs of the split gluing. -/
theorem image_pairs_eq_splitGluingPairs {δ : ℝ} {w : ℝ → Eᵤ}
    (hδr : δ ≤ r₀) (hwnorm : ∀ r ∈ Ioc 0 r₀, ‖w r‖ = ε)
    (himage : {z | z ∈ (splitPassage ε).source ∧ ‖z.snd‖ ≤ r₀ * ε ∧ z.fst = g z.snd ∧
        (splitPassage ε z).snd = k (splitPassage ε z).fst} =
      (fun r ↦ WithLp.toLp 2 (g (r • w r), r • w r)) '' Ioc 0 r₀) :
    (fun r ↦ (WithLp.toLp 2 (g (r • w r), r • w r),
      WithLp.toLp 2 (r • g (r • w r), w r))) '' Ioc 0 δ = splitGluingPairs ε δ g k := by
  let F : ℝ → WithLp 2 (Eₛ × Eᵤ) × WithLp 2 (Eₛ × Eᵤ) := fun r ↦
    (WithLp.toLp 2 (g (r • w r), r • w r), WithLp.toLp 2 (r • g (r • w r), w r))
  have hentry {r : ℝ} (hr : r ∈ Ioc 0 δ) :
      (F r).1 ∈ {z | z ∈ (splitPassage ε).source ∧ ‖z.snd‖ ≤ r₀ * ε ∧
        z.fst = g z.snd ∧ (splitPassage ε z).snd = k (splitPassage ε z).fst} := by
    rw [himage]
    exact ⟨r, ⟨hr.1, hr.2.trans hδr⟩, rfl⟩
  have hpass {r : ℝ} (hr : r ∈ Ioc 0 δ) :
      (F r).2 = splitPassage ε (F r).1 :=
    (splitPassage_toLp_smul (g (r • w r)) (hwnorm r ⟨hr.1, hr.2.trans hδr⟩)
      (pos_of_mem_splitPassage_source (hentry hr).1) hr.1).symm
  ext p
  rw [mem_splitGluingPairs]
  constructor
  · rintro ⟨r, hr, rfl⟩
    have hrentry := hentry hr
    refine ⟨hrentry.1, ?_, hrentry.2.2.1, hpass hr, ?_⟩
    · simp only [WithLp.toLp_snd, norm_smul, Real.norm_of_nonneg hr.1.le,
        hwnorm r ⟨hr.1, hr.2.trans hδr⟩]
      exact mul_le_mul_of_nonneg_right hr.2 (pos_of_mem_splitPassage_source hrentry.1).le
    · rw [hpass hr]
      exact hrentry.2.2.2
  · rintro ⟨hsrc, hbound, hgraph, hexit, hkgraph⟩
    have hε := pos_of_mem_splitPassage_source hsrc
    have hentry' : p.1 ∈ {z | z ∈ (splitPassage ε).source ∧ ‖z.snd‖ ≤ r₀ * ε ∧
        z.fst = g z.snd ∧ (splitPassage ε z).snd = k (splitPassage ε z).fst} :=
      ⟨hsrc, hbound.trans (mul_le_mul_of_nonneg_right hδr hε.le), hgraph,
        by rwa [← hexit]⟩
    rw [himage] at hentry'
    obtain ⟨r, hr, hre⟩ := hentry'
    have hnormr : r * ε = ‖p.1.snd‖ := by
      simpa only [WithLp.toLp_snd, norm_smul, Real.norm_of_nonneg hr.1.le,
        hwnorm r hr] using congrArg (fun z ↦ ‖z.snd‖) hre
    have hrδ : r ∈ Ioc 0 δ := ⟨hr.1, (mul_le_mul_iff_left₀ hε).mp
      (by simpa only [mul_comm ε] using hnormr.trans_le hbound)⟩
    have hFe : (F r).1 = p.1 := by
      simpa only [F] using hre
    refine ⟨r, hrδ, Prod.ext hFe ?_⟩
    rw [hpass hrδ, hFe, ← hexit]

/-- The gluing parametrization of a family of pairs of discs, extended continuously to the gluing
parameter `0`. Its image over `[0, r₀] × S` consists of the unbroken pairs of all members of the
family together with their broken pairs, its first coordinate is recovered by the norm of the
expanding entrance coordinate, and its value at `(r, p)` is a pair of points of the entrance disc
and the exit disc of the member `p`. -/
private theorem exists_splitGluingPairs_family_parametrization [CompleteSpace Eᵤ]
    {P : Type*} [TopologicalSpace P] {S : Set P} {g : P → Eᵤ → Eₛ} {k : P → Eₛ → Eᵤ}
    (hg : ∀ p ∈ S, LipschitzOnWith Kg (g p) (closedBall 0 (r₀ * ε)))
    (hgε : ∀ p ∈ S, ∀ y ∈ closedBall 0 (r₀ * ε), ‖g p y‖ = ε)
    (hk : ∀ p ∈ S, LipschitzOnWith Kk (k p) (closedBall 0 (r₀ * ε)))
    (hkε : ∀ p ∈ S, ∀ x ∈ closedBall 0 (r₀ * ε), ‖k p x‖ = ε)
    (hgc : ∀ y ∈ closedBall 0 (r₀ * ε), ContinuousOn (fun p ↦ g p y) S)
    (hkc : ∀ x ∈ closedBall 0 (r₀ * ε), ContinuousOn (fun p ↦ k p x) S)
    (hε : 0 < ε) (hr₀ : 0 ≤ r₀) (hr₀₁ : r₀ ≤ 1) (hK : Kk * Kg * r₀ ^ 2 < 1) :
    ∃ F : ℝ × P → WithLp 2 (Eₛ × Eᵤ) × WithLp 2 (Eₛ × Eᵤ),
      ContinuousOn F (Icc 0 r₀ ×ˢ S) ∧
      F '' (Icc 0 r₀ ×ˢ S) = (⋃ p ∈ S, splitGluingPairs ε r₀ (g p) (k p)) ∪
        (fun p ↦ (WithLp.toLp 2 (g p 0, 0), WithLp.toLp 2 (0, k p 0))) '' S ∧
      (∀ p ∈ S, (fun r ↦ F (r, p)) '' Ioc 0 r₀ = splitGluingPairs ε r₀ (g p) (k p)) ∧
      (∀ p ∈ S, F (0, p) = (WithLp.toLp 2 (g p 0, 0), WithLp.toLp 2 (0, k p 0))) ∧
      (∀ q ∈ Icc 0 r₀ ×ˢ S, ‖(F q).1.snd‖ / ε = q.1) ∧
      ∀ q ∈ Icc 0 r₀ ×ˢ S, (F q).1.fst = g q.2 (F q).1.snd ∧
        (F q).1.snd ∈ closedBall 0 (r₀ * ε) ∧ (F q).2.snd = k q.2 (F q).2.fst ∧
        (F q).2.fst ∈ closedBall 0 (r₀ * ε) := by
  obtain ⟨w, hw, hwp⟩ := exists_continuousOn_and_forall_setOf_mem_splitPassage_source_graph_eq_image
    hg hgε hk hkε hgc hkc hε hr₀₁ hK
  -- Name the properties of the parametrization of each member of the family.
  choose _ hw₀ hwnorm hwfix hwimage using hwp
  -- Pair the entrance parametrization with its exit formula, as for a single pair of discs.
  let v : ℝ × P → Eᵤ := fun q ↦ q.1 • w q.1 q.2
  let a : ℝ × P → Eₛ := fun q ↦ g q.2 (v q)
  let F : ℝ × P → WithLp 2 (Eₛ × Eᵤ) × WithLp 2 (Eₛ × Eᵤ) :=
    fun q ↦ (WithLp.toLp 2 (a q, v q), WithLp.toLp 2 (q.1 • a q, w q.1 q.2))
  have hnormv (q : ℝ × P) (hq : q ∈ Icc 0 r₀ ×ˢ S) : ‖v q‖ = q.1 * ε := by
    simp only [v, norm_smul, Real.norm_of_nonneg hq.1.1, hwnorm _ hq.2 _ hq.1]
  have hvball (q : ℝ × P) (hq : q ∈ Icc 0 r₀ ×ˢ S) : v q ∈ closedBall 0 (r₀ * ε) := by
    rw [mem_closedBall_zero_iff, hnormv q hq]
    exact mul_le_mul_of_nonneg_right hq.1.2 hε.le
  have hxball (q : ℝ × P) (hq : q ∈ Icc 0 r₀ ×ˢ S) : q.1 • a q ∈ closedBall 0 (r₀ * ε) := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg hq.1.1, hgε _ hq.2 _ (hvball q hq)]
    exact mul_le_mul_of_nonneg_right hq.1.2 hε.le
  have hv : ContinuousOn v (Icc 0 r₀ ×ˢ S) := continuousOn_fst.smul hw
  have ha : ContinuousOn a (Icc 0 r₀ ×ˢ S) :=
    (continuousOn_prod_of_continuousOn_lipschitzOnWith' (fun q : P × Eᵤ ↦ g q.1 q.2) Kg hg
      hgc).comp (continuousOn_snd.prodMk hv) fun q hq ↦ ⟨hq.2, hvball q hq⟩
  have hF : ContinuousOn F (Icc 0 r₀ ×ˢ S) :=
    ((WithLp.prod_continuous_toLp 2 Eₛ Eᵤ).comp_continuousOn (ha.prodMk hv)).prodMk
      ((WithLp.prod_continuous_toLp 2 Eₛ Eᵤ).comp_continuousOn
        ((continuousOn_fst.smul ha).prodMk hw))
  have himage (p : P) (hp : p ∈ S) :
      (fun r ↦ F (r, p)) '' Ioc 0 r₀ = splitGluingPairs ε r₀ (g p) (k p) :=
    image_pairs_eq_splitGluingPairs le_rfl
      (fun r hr ↦ hwnorm p hp r (Ioc_subset_Icc_self hr)) (hwimage p hp)
  have hF₀ (p : P) (hp : p ∈ S) :
      F (0, p) = (WithLp.toLp 2 (g p 0, 0), WithLp.toLp 2 (0, k p 0)) := by
    simp [F, a, v, hw₀ p hp]
  refine ⟨F, hF, ?_, himage, hF₀, fun q hq ↦ ?_, fun q hq ↦
    ⟨rfl, hvball q hq, (hwfix _ hq.2 _ hq.1).symm, hxball q hq⟩⟩
  · -- The parameter `0` gives the broken pairs and the positive parameters the unbroken ones.
    ext x
    simp only [mem_image, mem_union, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨⟨r, p⟩, ⟨hr, hp⟩, rfl⟩
      rcases hr.1.eq_or_lt with rfl | hr0
      · exact Or.inr ⟨p, hp, (hF₀ p hp).symm⟩
      · exact Or.inl ⟨p, hp, himage p hp ▸ ⟨r, ⟨hr0, hr.2⟩, rfl⟩⟩
    · rintro (⟨p, hp, hx⟩ | ⟨p, hp, rfl⟩)
      · rw [← himage p hp] at hx
        obtain ⟨r, hr, rfl⟩ := hx
        exact ⟨(r, p), ⟨Ioc_subset_Icc_self hr, hp⟩, rfl⟩
      · exact ⟨(0, p), ⟨left_mem_Icc.2 hr₀, hp⟩, hF₀ p hp⟩
  · simp only [F, WithLp.toLp_snd, hnormv q hq]
    exact mul_div_cancel_right₀ _ hε.ne'

/-- Extend the paired gluing parametrization continuously to parameter zero. The norm
coordinate recovers the parameter even at the broken pair. This is the case of a constant family
in `exists_splitGluingPairs_family_parametrization`. -/
private theorem exists_splitGluingPairs_parametrization [CompleteSpace Eᵤ]
    (hg : LipschitzOnWith Kg g (closedBall 0 (r₀ * ε)))
    (hgε : ∀ y ∈ closedBall 0 (r₀ * ε), ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 (r₀ * ε)))
    (hkε : ∀ x ∈ closedBall 0 (r₀ * ε), ‖k x‖ = ε)
    (hε : 0 < ε) (hr₀ : 0 ≤ r₀) (hr₀₁ : r₀ ≤ 1) (hK : Kk * Kg * r₀ ^ 2 < 1) :
    ∃ F : ℝ → WithLp 2 (Eₛ × Eᵤ) × WithLp 2 (Eₛ × Eᵤ),
      ContinuousOn F (Icc 0 r₀) ∧ F '' Ioc 0 r₀ = splitGluingPairs ε r₀ g k ∧
      F 0 = (WithLp.toLp 2 (g 0, 0), WithLp.toLp 2 (0, k 0)) ∧
      ∀ r ∈ Icc 0 r₀, ‖(F r).1.snd‖ / ε = r := by
  obtain ⟨F, hF, -, himage, hF₀, hnorm, -⟩ :=
    exists_splitGluingPairs_family_parametrization (S := (univ : Set Unit))
      (g := fun _ ↦ g) (k := fun _ ↦ k) (fun _ _ ↦ hg) (fun _ _ ↦ hgε) (fun _ _ ↦ hk)
      (fun _ _ ↦ hkε) (fun _ _ ↦ continuousOn_const) (fun _ _ ↦ continuousOn_const) hε hr₀ hr₀₁ hK
  exact ⟨fun r ↦ F (r, ()),
    hF.comp (continuousOn_id.prodMk continuousOn_const) fun _ hr ↦ ⟨hr, mem_univ _⟩,
    himage () (mem_univ _), hF₀ () (mem_univ _), fun r hr ↦ hnorm (r, ()) ⟨hr, mem_univ _⟩⟩

section Single

variable [CompleteSpace Eᵤ]
  (hg : LipschitzOnWith Kg g (closedBall 0 (r₀ * ε)))
  (hgε : ∀ y ∈ closedBall 0 (r₀ * ε), ‖g y‖ = ε)
  (hk : LipschitzOnWith Kk k (closedBall 0 (r₀ * ε)))
  (hkε : ∀ x ∈ closedBall 0 (r₀ * ε), ‖k x‖ = ε)
  (hε : 0 < ε) (hr₀ : 0 < r₀) (hr₀₁ : r₀ ≤ 1) (hK : Kk * Kg * r₀ ^ 2 < 1)

include hg hgε hk hkε hε hr₀ hr₀₁ hK

/-- The closure of the unbroken entrance/exit pairs adds exactly the pair of stable entrance
and unstable exit points of the broken trajectory. No other limiting configurations occur. -/
theorem closure_splitGluingPairs :
    closure (splitGluingPairs ε r₀ g k) =
      insert (WithLp.toLp 2 (g 0, 0), WithLp.toLp 2 (0, k 0)) (splitGluingPairs ε r₀ g k) := by
  obtain ⟨F, hF, himage, hF₀, -⟩ :=
    exists_splitGluingPairs_parametrization hg hgε hk hkε hε hr₀.le hr₀₁ hK
  have hclosure : closure (F '' Ioc 0 r₀) = F '' Icc 0 r₀ := by
    refine subset_antisymm
      (closure_minimal (image_mono Ioc_subset_Icc_self)
        (isCompact_Icc.image_of_continuousOn hF).isClosed)
      ?_
    have h := ContinuousOn.image_closure (s := Ioc 0 r₀) (f := F)
      (by rwa [closure_Ioc hr₀.ne])
    simpa only [closure_Ioc hr₀.ne] using h
  rw [← himage, hclosure, ← insert_left_Ioc hr₀.le, image_insert_eq, hF₀]

end Single

/-! ### Families of discs -/

section Family

variable {P : Type*} [TopologicalSpace P] {S : Set P}

/-- **The closure of the gluing pairs of a family of discs.** For a compact family of pairs of
discs, Lipschitz with uniform constants and continuous in the parameter, the closure of the
unbroken entrance and exit pairs of all members of the family adds exactly the broken pairs
`((g p 0, 0), (0, k p 0))` of the members `p ∈ S`. -/
theorem closure_biUnion_splitGluingPairs [CompleteSpace Eᵤ] {g : P → Eᵤ → Eₛ} {k : P → Eₛ → Eᵤ}
    (hg : ∀ p ∈ S, LipschitzOnWith Kg (g p) (closedBall 0 (r₀ * ε)))
    (hgε : ∀ p ∈ S, ∀ y ∈ closedBall 0 (r₀ * ε), ‖g p y‖ = ε)
    (hk : ∀ p ∈ S, LipschitzOnWith Kk (k p) (closedBall 0 (r₀ * ε)))
    (hkε : ∀ p ∈ S, ∀ x ∈ closedBall 0 (r₀ * ε), ‖k p x‖ = ε)
    (hgc : ∀ y ∈ closedBall 0 (r₀ * ε), ContinuousOn (fun p ↦ g p y) S)
    (hkc : ∀ x ∈ closedBall 0 (r₀ * ε), ContinuousOn (fun p ↦ k p x) S)
    (hε : 0 < ε) (hr₀ : 0 < r₀) (hr₀₁ : r₀ ≤ 1) (hK : Kk * Kg * r₀ ^ 2 < 1)
    (hS : IsCompact S) :
    closure (⋃ p ∈ S, splitGluingPairs ε r₀ (g p) (k p)) =
      (⋃ p ∈ S, splitGluingPairs ε r₀ (g p) (k p)) ∪
        (fun p ↦ (WithLp.toLp 2 (g p 0, 0), WithLp.toLp 2 (0, k p 0))) '' S := by
  obtain ⟨F, hF, hFD, -⟩ :=
    exists_splitGluingPairs_family_parametrization hg hgε hk hkε hgc hkc hε hr₀.le hr₀₁ hK
  refine subset_antisymm ?_ (union_subset subset_closure ?_)
  · -- The pairs and the broken pairs form the compact image of `[0, r₀] × S`.
    rw [← hFD]
    exact closure_minimal (hFD ▸ subset_union_left)
      ((isCompact_Icc.prod hS).image_of_continuousOn hF).isClosed
  · -- Each broken pair is a limit of unbroken pairs of its own member of the family.
    rintro _ ⟨p, hp, rfl⟩
    refine closure_mono (subset_biUnion_of_mem (u := fun p ↦ splitGluingPairs ε r₀ (g p) (k p))
      hp) ?_
    rw [closure_splitGluingPairs (hg p hp) (hgε p hp) (hk p hp) (hkε p hp) hε hr₀ hr₀₁ hK]
    exact mem_insert _ _

/-- For a compact family of pairs of discs, Lipschitz with uniform constants and continuous in the
parameter, the closure of the unbroken entrance and exit pairs of all members of the family is
compact, even when the stable and unstable ambient spaces are infinite dimensional. -/
theorem isCompact_closure_biUnion_splitGluingPairs [CompleteSpace Eᵤ]
    {g : P → Eᵤ → Eₛ} {k : P → Eₛ → Eᵤ}
    (hg : ∀ p ∈ S, LipschitzOnWith Kg (g p) (closedBall 0 (r₀ * ε)))
    (hgε : ∀ p ∈ S, ∀ y ∈ closedBall 0 (r₀ * ε), ‖g p y‖ = ε)
    (hk : ∀ p ∈ S, LipschitzOnWith Kk (k p) (closedBall 0 (r₀ * ε)))
    (hkε : ∀ p ∈ S, ∀ x ∈ closedBall 0 (r₀ * ε), ‖k p x‖ = ε)
    (hgc : ∀ y ∈ closedBall 0 (r₀ * ε), ContinuousOn (fun p ↦ g p y) S)
    (hkc : ∀ x ∈ closedBall 0 (r₀ * ε), ContinuousOn (fun p ↦ k p x) S)
    (hε : 0 < ε) (hr₀₁ : r₀ ≤ 1) (hK : Kk * Kg * r₀ ^ 2 < 1) (hS : IsCompact S) :
    IsCompact (closure (⋃ p ∈ S, splitGluingPairs ε r₀ (g p) (k p))) := by
  rcases lt_or_ge r₀ 0 with hr₀ | hr₀
  · -- If `r₀ < 0` no entrance point satisfies the bound `‖y‖ ≤ r₀ * ε`, so there are no pairs.
    have hempty : (⋃ p ∈ S, splitGluingPairs ε r₀ (g p) (k p)) = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx ↦ ?_
      obtain ⟨p, -, hx⟩ := mem_iUnion₂.1 hx
      exact (norm_nonneg _).not_gt
        ((mem_splitGluingPairs.1 hx).2.1.trans_lt (mul_neg_of_neg_of_pos hr₀ hε))
    simp [hempty]
  · -- The closure lies in the compact image of `[0, r₀] × S` under the gluing parametrization.
    obtain ⟨F, hF, hFD, -⟩ :=
      exists_splitGluingPairs_family_parametrization hg hgε hk hkε hgc hkc hε hr₀ hr₀₁ hK
    have hcpt := (isCompact_Icc.prod hS).image_of_continuousOn hF
    exact hcpt.of_isClosed_subset isClosed_closure
      (closure_minimal (hFD ▸ subset_union_left) hcpt.isClosed)

/-- The closure of the paired local gluing space is compact, even when the stable and
unstable ambient spaces are infinite dimensional. This is the case of a constant family in
`isCompact_closure_biUnion_splitGluingPairs`. -/
theorem isCompact_closure_splitGluingPairs [CompleteSpace Eᵤ]
    (hg : LipschitzOnWith Kg g (closedBall 0 (r₀ * ε)))
    (hgε : ∀ y ∈ closedBall 0 (r₀ * ε), ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 (r₀ * ε)))
    (hkε : ∀ x ∈ closedBall 0 (r₀ * ε), ‖k x‖ = ε)
    (hε : 0 < ε) (hr₀₁ : r₀ ≤ 1) (hK : Kk * Kg * r₀ ^ 2 < 1) :
    IsCompact (closure (splitGluingPairs ε r₀ g k)) := by
  simpa only [biUnion_univ, iUnion_const] using
    isCompact_closure_biUnion_splitGluingPairs (S := (univ : Set Unit))
      (g := fun _ ↦ g) (k := fun _ ↦ k) (fun _ _ ↦ hg) (fun _ _ ↦ hgε) (fun _ _ ↦ hk)
      (fun _ _ ↦ hkε) (fun _ _ ↦ continuousOn_const) (fun _ _ ↦ continuousOn_const) hε hr₀₁ hK
      isCompact_univ

/-- **The local compactified gluing space of a family of discs is `[0, r₀] × S`.** Let the
families of discs `y ↦ (g p y, y)` and `x ↦ (x, k p x)` be Lipschitz with uniform constants and
continuous in the parameter `p` of a compact set `S`, and suppose that any two distinct members of
the family have disjoint entrance discs or disjoint exit discs. Then the closure of the unbroken
entrance and exit pairs of all members is homeomorphic to `[0, r₀] × S`. The first coordinate of
the inverse is the gluing parameter, the norm of the expanding entrance coordinate divided by the
box radius; the parameter `0` gives the broken pairs, and a positive parameter `r` paired with `p`
gives an unbroken pair of the member `p`.

In the gluing of broken trajectories, `p` ranges over pairs of a trajectory into the middle
critical point and a trajectory out of it. In the split box, this is the model chart from which a
collar along once-broken trajectories is expected to come. -/
theorem exists_homeomorph_closure_biUnion_splitGluingPairs [CompleteSpace Eᵤ]
    {g : P → Eᵤ → Eₛ} {k : P → Eₛ → Eᵤ}
    (hg : ∀ p ∈ S, LipschitzOnWith Kg (g p) (closedBall 0 (r₀ * ε)))
    (hgε : ∀ p ∈ S, ∀ y ∈ closedBall 0 (r₀ * ε), ‖g p y‖ = ε)
    (hk : ∀ p ∈ S, LipschitzOnWith Kk (k p) (closedBall 0 (r₀ * ε)))
    (hkε : ∀ p ∈ S, ∀ x ∈ closedBall 0 (r₀ * ε), ‖k p x‖ = ε)
    (hgc : ∀ y ∈ closedBall 0 (r₀ * ε), ContinuousOn (fun p ↦ g p y) S)
    (hkc : ∀ x ∈ closedBall 0 (r₀ * ε), ContinuousOn (fun p ↦ k p x) S)
    (hε : 0 < ε) (hr₀ : 0 < r₀) (hr₀₁ : r₀ ≤ 1) (hK : Kk * Kg * r₀ ^ 2 < 1)
    (hS : IsCompact S)
    (hinj : ∀ p ∈ S, ∀ p' ∈ S, ∀ y ∈ closedBall (0 : Eᵤ) (r₀ * ε),
      ∀ x ∈ closedBall (0 : Eₛ) (r₀ * ε), g p y = g p' y → k p x = k p' x → p = p') :
    ∃ e : (Icc 0 r₀ ×ˢ S : Set (ℝ × P)) ≃ₜ closure (⋃ p ∈ S, splitGluingPairs ε r₀ (g p) (k p)),
      (∀ x, (e.symm x : ℝ × P).1 = ‖x.val.1.snd‖ / ε) ∧
      (∀ q : (Icc 0 r₀ ×ˢ S : Set (ℝ × P)), 0 < (q : ℝ × P).1 →
        (e q).val ∈ splitGluingPairs ε r₀ (g (q : ℝ × P).2) (k (q : ℝ × P).2)) ∧
      ∀ p (hp : p ∈ S), (e ⟨(0, p), left_mem_Icc.2 hr₀.le, hp⟩).val =
        (WithLp.toLp 2 (g p 0, 0), WithLp.toLp 2 (0, k p 0)) := by
  obtain ⟨F, hF, hFD, himage, hF₀, hnorm, hdisc⟩ :=
    exists_splitGluingPairs_family_parametrization hg hgε hk hkε hgc hkc hε hr₀.le hr₀₁ hK
  have hclosure : F '' (Icc 0 r₀ ×ˢ S) = closure (⋃ p ∈ S, splitGluingPairs ε r₀ (g p) (k p)) := by
    rw [hFD, closure_biUnion_splitGluingPairs hg hgε hk hkε hgc hkc hε hr₀ hr₀₁ hK hS]
  let f : (Icc 0 r₀ ×ˢ S : Set (ℝ × P)) → closure (⋃ p ∈ S, splitGluingPairs ε r₀ (g p) (k p)) :=
    fun q ↦ ⟨F q, hclosure ▸ mem_image_of_mem F q.property⟩
  have hf : Continuous f := hF.domRestrict.codRestrict _
  have hfinj : Injective f := by
    rintro ⟨q, hq⟩ ⟨q', hq'⟩ hqq'
    have hFq : F q = F q' := congrArg Subtype.val hqq'
    have h₁ : q.1 = q'.1 := by rw [← hnorm q hq, ← hnorm q' hq', hFq]
    -- Equal pairs share the entrance point and the exit point of the two members of the family.
    obtain ⟨hgq, hy, hkq, hx⟩ := hdisc q hq
    obtain ⟨hgq', -, hkq', -⟩ := hdisc q' hq'
    refine Subtype.ext (Prod.ext h₁ (hinj _ hq.2 _ hq'.2 _ hy _ hx ?_ ?_))
    · rw [← hgq, hFq]
      exact hgq'
    · rw [← hkq, hFq]
      exact hkq'
  have hfsurj : Surjective f := by
    rintro ⟨x, hx⟩
    rw [← hclosure] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    exact ⟨⟨q, hq⟩, rfl⟩
  have : CompactSpace (Icc 0 r₀ ×ˢ S : Set (ℝ × P)) :=
    isCompact_iff_compactSpace.1 (isCompact_Icc.prod hS)
  -- A continuous bijection from a compact space to a Hausdorff space is a homeomorphism.
  let e := hf.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
  -- Both `homeoOfEquivCompactToT2` and `Equiv.ofBijective` keep `f` as the forward map.
  have he (q : (Icc 0 r₀ ×ˢ S : Set (ℝ × P))) : (e q).val = F q := rfl
  refine ⟨e, fun x ↦ ?_, fun q hq ↦ ?_, fun p hp ↦ he _ ▸ hF₀ p hp⟩
  · rw [← e.apply_symm_apply x, he, hnorm _ (e.symm x).property, e.apply_symm_apply]
  · rw [he, ← himage _ q.property.2]
    exact ⟨_, ⟨hq, q.property.1.2⟩, rfl⟩

/-- The local compactified gluing space is a closed interval. Its inverse gluing coordinate
is the expanding entrance norm divided by the box radius, and parameter zero is the broken
trajectory. The assertion includes all unbroken pairs in the prescribed range. This is the case of
a constant family in `exists_homeomorph_closure_biUnion_splitGluingPairs`. -/
theorem exists_homeomorph_closure_splitGluingPairs [CompleteSpace Eᵤ]
    (hg : LipschitzOnWith Kg g (closedBall 0 (r₀ * ε)))
    (hgε : ∀ y ∈ closedBall 0 (r₀ * ε), ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 (r₀ * ε)))
    (hkε : ∀ x ∈ closedBall 0 (r₀ * ε), ‖k x‖ = ε)
    (hε : 0 < ε) (hr₀ : 0 < r₀) (hr₀₁ : r₀ ≤ 1) (hK : Kk * Kg * r₀ ^ 2 < 1) :
    ∃ e : Icc (0 : ℝ) r₀ ≃ₜ closure (splitGluingPairs ε r₀ g k),
      (∀ p, (e.symm p : ℝ) = ‖p.val.1.snd‖ / ε) ∧
      (e ⟨0, by constructor <;> linarith⟩).val =
        (WithLp.toLp 2 (g 0, 0), WithLp.toLp 2 (0, k 0)) := by
  obtain ⟨e, hcoord, -, he₀⟩ :=
    exists_homeomorph_closure_biUnion_splitGluingPairs (S := (univ : Set Unit))
      (g := fun _ ↦ g) (k := fun _ ↦ k) (fun _ _ ↦ hg) (fun _ _ ↦ hgε) (fun _ _ ↦ hk)
      (fun _ _ ↦ hkε) (fun _ _ ↦ continuousOn_const) (fun _ _ ↦ continuousOn_const) hε hr₀ hr₀₁ hK
      isCompact_univ fun _ _ _ _ _ _ _ _ _ _ ↦ Subsingleton.elim _ _
  -- Identify `[0, r₀]` with `[0, r₀] × univ` over the one-point parameter space.
  let i : Icc (0 : ℝ) r₀ ≃ₜ (Icc 0 r₀ ×ˢ (univ : Set Unit) : Set (ℝ × Unit)) :=
    { toFun r := ⟨(r, ()), r.property, mem_univ _⟩
      invFun q := ⟨q.val.1, q.property.1⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hset : closure (⋃ p ∈ (univ : Set Unit), splitGluingPairs ε r₀ g k) =
      closure (splitGluingPairs ε r₀ g k) := by
    rw [biUnion_univ, iUnion_const]
  exact ⟨(i.trans e).trans (Homeomorph.setCongr hset), fun x ↦ hcoord _,
    he₀ () (mem_univ _)⟩

end Family

end TauCeti
