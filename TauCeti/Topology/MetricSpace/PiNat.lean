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

Every nonempty closed subset `F` of the Baire space `ℕ → ℕ` has a least element for the
lexicographic order. Its coordinates are chosen one at a time: the `n`-th coordinate is the least
value of the `n`-th coordinate among the points of `F` that share its first `n` coordinates. The
points chosen at the successive stages converge to it, so it lies in `F` because `F` is closed.

This "leftmost branch" is the canonical choice of a point in a closed subset of Baire space, and it
is the choice behind the Jankov–von Neumann uniformization theorem: a set whose points are
parametrised continuously by Baire space has a section selecting, over each point of its
projection, the image of the lexicographically least parameter. The coordinatewise
characterisation `TauCeti.isLeast_image_toLex_iff` is the form in which that proof consumes it.

## Main results

* `TauCeti.isLeast_image_toLex_iff`: a point `β ∈ F` is lexicographically least in `F` exactly
  when, for every `n`, its `n`-th coordinate is the least `n`-th coordinate among the points of
  `F` in the cylinder of its first `n` coordinates.
* `IsClosed.exists_isLeast_image_toLex`: a nonempty closed subset of `ℕ → ℕ` has a
  lexicographically least element.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Springer-Verlag, 1995, the proof of
  Theorem 18.1, for the leftmost branch of a closed subset of Baire space.
-/

public section

open Filter Set Topology PiNat

namespace TauCeti

/-- A point `β` of `F ⊆ ℕ → ℕ` is the lexicographically least element of `F` exactly when, for
every `n`, its `n`-th coordinate is the least `n`-th coordinate among the points of `F` whose first
`n` coordinates agree with those of `β`. -/
theorem isLeast_image_toLex_iff {F : Set (ℕ → ℕ)} {β : ℕ → ℕ} (hβ : β ∈ F) :
    IsLeast (toLex '' F) (toLex β) ↔ ∀ n, IsLeast ((· n) '' (F ∩ cylinder β n)) (β n) := by
  refine ⟨fun h n => ⟨⟨β, ⟨hβ, self_mem_cylinder β n⟩, rfl⟩, ?_⟩, fun h => ⟨⟨β, hβ, rfl⟩, ?_⟩⟩
  · rintro _ ⟨γ, ⟨hγ, hγn⟩, rfl⟩
    exact Pi.apply_le_of_toLex (h.2 ⟨γ, hγ, rfl⟩) fun j hj => (mem_cylinder_iff.1 hγn j hj).symm
  · rintro _ ⟨γ, hγ, rfl⟩
    rcases eq_or_ne β γ with rfl | hne
    · exact le_rfl
    classical
    -- `i` is the first coordinate where `β` and `γ` differ
    have hex : ∃ i, β i ≠ γ i := Function.ne_iff.1 hne
    set i := Nat.find hex
    have hagree : ∀ j < i, β j = γ j := fun j hj => not_not.1 (Nat.find_min hex hj)
    have hle : β i ≤ γ i :=
      (h i).2 ⟨γ, ⟨hγ, mem_cylinder_iff.2 fun j hj => (hagree j hj).symm⟩, rfl⟩
    exact le_of_lt ⟨i, hagree, lt_of_le_of_ne hle (Nat.find_spec hex)⟩

/-- The sets cut out at the successive stages of the construction of the lexicographically least
point of `F`: stage `n + 1` keeps the points of stage `n` whose `n`-th coordinate is least. -/
private noncomputable def lexLeastStage (F : Set (ℕ → ℕ)) : ℕ → Set (ℕ → ℕ)
  | 0 => F
  | n + 1 => lexLeastStage F n ∩ {γ | γ n = sInf ((· n) '' lexLeastStage F n)}

/-- The point whose `n`-th coordinate is the least `n`-th coordinate on stage `n`. -/
private noncomputable def lexLeast (F : Set (ℕ → ℕ)) : ℕ → ℕ :=
  fun n => sInf ((· n) '' lexLeastStage F n)

private theorem lexLeastStage_eq (F : Set (ℕ → ℕ)) (n : ℕ) :
    lexLeastStage F n = F ∩ cylinder (lexLeast F) n := by
  induction n with
  | zero => simp [lexLeastStage]
  | succ n ih =>
    have hsucc : lexLeastStage F (n + 1) = lexLeastStage F n ∩ {γ | γ n = lexLeast F n} := rfl
    ext γ
    simp only [hsucc, ih, mem_inter_iff, mem_cylinder_iff, mem_ofPred_eq,
      Nat.forall_lt_succ_right, and_assoc]

private theorem lexLeastStage_nonempty {F : Set (ℕ → ℕ)} (hF : F.Nonempty) (n : ℕ) :
    (lexLeastStage F n).Nonempty := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    obtain ⟨γ, hγ, hγn⟩ := Nat.sInf_mem (ih.image (· n))
    exact ⟨γ, hγ, hγn⟩

/-- A nonempty closed subset of the Baire space `ℕ → ℕ` has a lexicographically least element. -/
theorem _root_.IsClosed.exists_isLeast_image_toLex {F : Set (ℕ → ℕ)} (hF : IsClosed F)
    (hne : F.Nonempty) : ∃ β ∈ F, IsLeast (toLex '' F) (toLex β) := by
  -- a point of each stage agrees with `lexLeast F` on more and more coordinates
  have hstage n := lexLeastStage_nonempty hne n
  simp only [lexLeastStage_eq] at hstage
  choose γ hγ using hstage
  have hlim : Tendsto γ atTop (𝓝 (lexLeast F)) :=
    tendsto_pi_nhds.2 fun i => tendsto_atTop_of_eventually_const (i₀ := i + 1)
      fun n hn => mem_cylinder_iff.1 (hγ n).2 i (by omega)
  have hmem : lexLeast F ∈ F := hF.mem_of_tendsto hlim (Eventually.of_forall fun n => (hγ n).1)
  refine ⟨lexLeast F, hmem, (isLeast_image_toLex_iff hmem).2 fun n => ?_⟩
  rw [← lexLeastStage_eq]
  exact ⟨Nat.sInf_mem ((lexLeastStage_nonempty hne n).image _), fun m hm => Nat.sInf_le hm⟩

end TauCeti
