/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.PiLex
public import Mathlib.Topology.MetricSpace.PiNat

/-!
# Lexicographically least points of closed subsets of Baire space

Every nonempty closed subset `F` of the Baire space `ℕ → ℕ`, and more generally of a product
`∀ n, E n` of well-ordered spaces, has a least element for the lexicographic order. Its
coordinates are chosen one at a time: the `n`-th coordinate is the least value of the `n`-th
coordinate among the points of `F` that share its first `n` coordinates. The points chosen at the
successive stages converge to it, so it lies in `F` because `F` is closed.

This "leftmost branch" is the canonical choice of a point in a closed subset of Baire space, and it
is the choice behind the Jankov–von Neumann uniformization theorem: a set whose points are
parametrised continuously by Baire space has a section selecting, over each point of its
projection, the image of the lexicographically least parameter. The coordinatewise
characterisation `TauCeti.isLeast_image_toLex_iff` is the form in which that proof consumes it.

The file also records that distinct points of a sequence space eventually have distinct initial
segments, uniformly over an injective finite family (`PiNat.eventually_injective_res`).

## Main results

* `TauCeti.isLeast_image_toLex_iff`: a point `β ∈ F` is lexicographically least in `F` exactly
  when, for every `n`, its `n`-th coordinate is the least `n`-th coordinate among the points of
  `F` in the cylinder of its first `n` coordinates.
* `IsClosed.exists_isLeast_image_toLex`: a nonempty closed subset of `∀ n, E n`, with each
  `E n` well-ordered, has a lexicographically least element.
* `PiNat.eventually_injective_res`: the initial segments of an injective finite family of
  sequences are pairwise distinct from some length on.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Springer-Verlag, 1995, the proof of
  Theorem 18.1, for the leftmost branch of a closed subset of Baire space.
-/

public section

open Filter Set Topology PiNat

namespace TauCeti

variable {E : ℕ → Type*}

/-- A point `β` of `F ⊆ ∀ n, E n` is the lexicographically least element of `F` exactly when, for
every `n`, its `n`-th coordinate is the least `n`-th coordinate among the points of `F` whose first
`n` coordinates agree with those of `β`. -/
theorem isLeast_image_toLex_iff [∀ n, LinearOrder (E n)] {F : Set (∀ n, E n)} {β : ∀ n, E n}
    (hβ : β ∈ F) :
    IsLeast (toLex '' F) (toLex β) ↔ ∀ n, IsLeast ((· n) '' (F ∩ cylinder β n)) (β n) := by
  refine ⟨fun h n => ⟨⟨β, ⟨hβ, self_mem_cylinder β n⟩, rfl⟩, ?_⟩, fun h => ⟨⟨β, hβ, rfl⟩, ?_⟩⟩
  · rintro _ ⟨γ, ⟨hγ, hγn⟩, rfl⟩
    exact Pi.apply_le_of_toLex (h.2 ⟨γ, hγ, rfl⟩) fun j hj => (mem_cylinder_iff.1 hγn j hj).symm
  · rintro _ ⟨γ, hγ, rfl⟩
    rcases eq_or_ne β γ with rfl | hne
    · exact le_rfl
    -- `β` and `γ` agree below `firstDiff β γ`, and `β` is smaller at that coordinate
    have hle : β (firstDiff β γ) ≤ γ (firstDiff β γ) :=
      (h _).2 ⟨γ, ⟨hγ, (mem_cylinder_comm _ _ _).1 (mem_cylinder_firstDiff β γ)⟩, rfl⟩
    exact le_of_lt ⟨firstDiff β γ, fun _ => apply_eq_of_lt_firstDiff,
      hle.lt_of_ne (apply_firstDiff_ne hne)⟩

/-- The sets cut out at the successive stages of the construction of the lexicographically least
point of `F`: stage `n + 1` keeps the points of stage `n` whose `n`-th coordinate is least. -/
private def lexLeastStage [∀ n, LE (E n)] (F : Set (∀ n, E n)) : ℕ → Set (∀ n, E n)
  | 0 => F
  | n + 1 => {γ ∈ lexLeastStage F n | ∀ δ ∈ lexLeastStage F n, γ n ≤ δ n}

private theorem mem_lexLeastStage_succ [∀ n, LE (E n)] {F : Set (∀ n, E n)} {n : ℕ}
    {γ : ∀ n, E n} : γ ∈ lexLeastStage F (n + 1) ↔
      γ ∈ lexLeastStage F n ∧ ∀ δ ∈ lexLeastStage F n, γ n ≤ δ n := by
  rw [lexLeastStage, mem_sep_iff]

private theorem lexLeastStage_nonempty [∀ n, LinearOrder (E n)] [∀ n, WellFoundedLT (E n)]
    {F : Set (∀ n, E n)} (hF : F.Nonempty) (n : ℕ) : (lexLeastStage F n).Nonempty := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    obtain ⟨_, ⟨γ, hγ, rfl⟩, hmin⟩ := wellFounded_lt.has_min _ (ih.image (· n))
    exact ⟨γ, mem_lexLeastStage_succ.2 ⟨hγ, fun δ hδ => not_lt.1 (hmin _ ⟨δ, hδ, rfl⟩)⟩⟩

/-- If `γ n` lies in stage `n` for every `n`, then stage `n` consists of the points of `F` whose
first `n` coordinates are those of the diagonal point `i ↦ γ (i + 1) i`. -/
private theorem lexLeastStage_eq [∀ n, LinearOrder (E n)] {F : Set (∀ n, E n)}
    {γ : ℕ → ∀ n, E n} (hγ : ∀ n, γ n ∈ lexLeastStage F n) (n : ℕ) :
    lexLeastStage F n = F ∩ cylinder (fun i => γ (i + 1) i) n := by
  induction n with
  | zero => simp [lexLeastStage]
  | succ n ih =>
    obtain ⟨hγS, hγmin⟩ := mem_lexLeastStage_succ.1 (hγ (n + 1))
    rw [ih] at hγS hγmin
    ext δ
    rw [mem_lexLeastStage_succ, ih, mem_inter_iff, mem_inter_iff, mem_cylinder_iff,
      mem_cylinder_iff, Nat.forall_lt_succ_right, ← and_assoc]
    exact and_congr_right fun hδ =>
      ⟨fun h => le_antisymm (h _ hγS) (hγmin δ hδ), fun h δ' hδ' => h ▸ hγmin δ' hδ'⟩

/-- A nonempty closed subset of a product `∀ n, E n` of well-ordered spaces, such as the Baire
space `ℕ → ℕ`, has a lexicographically least element. -/
theorem _root_.IsClosed.exists_isLeast_image_toLex [∀ n, LinearOrder (E n)]
    [∀ n, WellFoundedLT (E n)] [∀ n, TopologicalSpace (E n)] {F : Set (∀ n, E n)}
    (hF : IsClosed F) (hne : F.Nonempty) : ∃ β ∈ F, IsLeast (toLex '' F) (toLex β) := by
  choose γ hγ using lexLeastStage_nonempty hne
  have hstage n : γ n ∈ F ∩ cylinder (fun i => γ (i + 1) i) n := lexLeastStage_eq hγ n ▸ hγ n
  -- the point of stage `n` agrees with the diagonal point on its first `n` coordinates
  have hlim : Tendsto γ atTop (𝓝 fun i => γ (i + 1) i) :=
    tendsto_pi_nhds.2 fun i => tendsto_atTop_of_eventually_const (i₀ := i + 1)
      fun n hn => mem_cylinder_iff.1 (hstage n).2 i (by omega)
  have hmem := hF.mem_of_tendsto hlim (Eventually.of_forall fun n => (hstage n).1)
  refine ⟨_, hmem, (isLeast_image_toLex_iff hmem).2 fun n => ?_⟩
  obtain ⟨hγS, hγmin⟩ := mem_lexLeastStage_succ.1 (hγ (n + 1))
  rw [← lexLeastStage_eq hγ]
  exact ⟨⟨γ (n + 1), hγS, rfl⟩, by rintro _ ⟨δ, hδ, rfl⟩; exact hγmin δ hδ⟩

end TauCeti

namespace PiNat

/-- Distinct branches of a tree eventually separate: for an injective finite family `a` of
sequences, the initial segments `PiNat.res (a i) j` of length `j` are pairwise distinct for all
large `j`. -/
theorem eventually_injective_res {ι β : Type*} [Finite ι] {a : ι → ℕ → β}
    (ha : Function.Injective a) :
    ∀ᶠ j in atTop, Function.Injective fun i => PiNat.res (a i) j := by
  have (p : ι × ι) : ∀ᶠ j in atTop, PiNat.res (a p.1) j = PiNat.res (a p.2) j → p.1 = p.2 := by
    by_cases hp : p.1 = p.2
    · exact Eventually.of_forall fun _ _ => hp
    obtain ⟨q, hq⟩ := Function.ne_iff.1 (ha.ne hp)
    filter_upwards [eventually_gt_atTop q] with j hj hres
    exact absurd (PiNat.res_eq_res.1 hres hj) hq
  filter_upwards [eventually_all.2 this] with j hj i i' hii'
  exact hj (i, i') hii'

end PiNat
