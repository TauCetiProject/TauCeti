/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# Tied boundaries of a generalised equation

A boundary `p` of a variable base `μ` of a generalised equation `Ω` is *`μ`-tied* to a boundary
`q` of the dual base `Δ(μ)` when `(p, μ, q)` is a boundary connection (Kharlampovich–Myasnikov,
§5.1, ET2 and ET4). It is convenient to extend this to the end-points of `μ`, as the source does
for the removal of a lonely base: `α(μ)` is tied to `α(Δμ)` and `β(μ)` to `β(Δμ)` when
`ε(μ) = ε(Δμ)`, and `α(μ)` is tied to `β(Δμ)` and `β(μ)` to `α(Δμ)` otherwise.

In a formally consistent generalised equation a boundary of `μ` is tied to at most one boundary,
and the tie is strictly increasing when `ε(μ) = ε(Δμ)` and strictly decreasing otherwise. The
source states the weak monotonicity (Definition 10(2)); the tie is strict because the dual
connections are monotone as well. This is what makes the transfer of a base (ET2) and the removal
of a lonely base (ET4) well defined: the boundaries of `μ` cut `Δ(μ)` into consecutive nonempty
segments.

## Main definitions

* `TauCeti.GenEq.IsTiedTo`: the boundary `p` of `μ` is tied to the boundary `q` of `Δ(μ)`, with a
  `Decidable` instance.
* `TauCeti.GenEq.tiedBoundary`: the boundary of `Δ(μ)` to which a boundary of `μ` is tied.

## Main results

* `TauCeti.GenEq.IsTiedTo.dual`: ties are symmetric under passing to the dual base.
* `TauCeti.GenEq.IsFormallyConsistent.isTiedTo_unique`: in a formally consistent generalised
  equation a boundary is tied to at most one boundary.
* `TauCeti.GenEq.IsFormallyConsistent.lt_of_isTiedTo_of_sign_eq`,
  `TauCeti.GenEq.IsFormallyConsistent.lt_of_isTiedTo_of_sign_ne`: the tie is strictly increasing
  for dual bases of equal signs and strictly decreasing for dual bases of opposite signs.
* `TauCeti.GenEq.IsFormallyConsistent.strictMonoOn_tiedBoundary_of_sign_eq`,
  `TauCeti.GenEq.IsFormallyConsistent.strictAntiOn_tiedBoundary_of_sign_ne`: the same for the
  function `tiedBoundary μ` on the tied boundaries of `μ`.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §4.1, Definition 10, and §5.1, ET2 and ET4.
-/

public section

namespace TauCeti

namespace GenEq

variable {A : Type*} (Ω : GenEq A)

/-- The boundary `p` of the variable base `μ` is tied to the boundary `q` of `Δ(μ)`: either
`(p, μ, q)` is a boundary connection, or `p` is an end-point of `μ` and `q` is the corresponding
end-point of `Δ(μ)`, that is the end-point on the same side when `ε(μ) = ε(Δμ)` and on the
opposite side otherwise. -/
def IsTiedTo (μ : Fin Ω.numBases) (p q : Fin (Ω.numItems + 1)) : Prop :=
  (p, μ, q) ∈ Ω.connections ∨
    (p = Ω.left μ ∧ q = if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.left (Ω.dual μ)
      else Ω.right (Ω.dual μ)) ∨
    (p = Ω.right μ ∧ q = if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.right (Ω.dual μ)
      else Ω.left (Ω.dual μ))

/-- A boundary is tied through a boundary connection, or as an end-point of the base to the
corresponding end-point of the dual base. -/
theorem isTiedTo_iff {μ : Fin Ω.numBases} {p q : Fin (Ω.numItems + 1)} :
    Ω.IsTiedTo μ p q ↔ (p, μ, q) ∈ Ω.connections ∨
      (p = Ω.left μ ∧ q = if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.left (Ω.dual μ)
        else Ω.right (Ω.dual μ)) ∨
      (p = Ω.right μ ∧ q = if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.right (Ω.dual μ)
        else Ω.left (Ω.dual μ)) :=
  Iff.rfl

/-- Whether a boundary of `μ` is tied to a boundary of `Δ(μ)` is decidable. -/
instance (μ : Fin Ω.numBases) (p q : Fin (Ω.numItems + 1)) : Decidable (Ω.IsTiedTo μ p q) :=
  decidable_of_iff _ Ω.isTiedTo_iff.symm

variable {Ω} {μ : Fin Ω.numBases} {p p' q q' : Fin (Ω.numItems + 1)}

/-- A boundary connection is a tie. -/
@[grind →]
theorem isTiedTo_of_mem_connections (hc : (p, μ, q) ∈ Ω.connections) : Ω.IsTiedTo μ p q :=
  Or.inl hc

/-- Away from the end-points of `μ`, a boundary is tied exactly through a boundary connection. -/
theorem isTiedTo_iff_mem_connections (hp₁ : p ≠ Ω.left μ) (hp₂ : p ≠ Ω.right μ) :
    Ω.IsTiedTo μ p q ↔ (p, μ, q) ∈ Ω.connections := by
  simp [isTiedTo_iff, hp₁, hp₂]

/-- The initial boundary of `μ` is tied exactly to the initial boundary of `Δ(μ)` when
`ε(μ) = ε(Δμ)`, and exactly to its terminal boundary otherwise. -/
@[simp, grind =]
theorem isTiedTo_left_iff : Ω.IsTiedTo μ (Ω.left μ) q ↔
    q = if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.left (Ω.dual μ) else Ω.right (Ω.dual μ) := by
  refine ⟨?_, fun h => Or.inr (Or.inl ⟨rfl, h⟩)⟩
  rintro (h | ⟨-, h⟩ | ⟨h, -⟩)
  exacts [absurd (Ω.bounds_of_mem_connections _ h).1 (lt_irrefl _), h,
    absurd h (Ω.left_lt_right μ).ne]

/-- The terminal boundary of `μ` is tied exactly to the terminal boundary of `Δ(μ)` when
`ε(μ) = ε(Δμ)`, and exactly to its initial boundary otherwise. -/
@[simp, grind =]
theorem isTiedTo_right_iff : Ω.IsTiedTo μ (Ω.right μ) q ↔
    q = if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.right (Ω.dual μ) else Ω.left (Ω.dual μ) := by
  refine ⟨?_, fun h => Or.inr (Or.inr ⟨rfl, h⟩)⟩
  rintro (h | ⟨h, -⟩ | ⟨-, h⟩)
  exacts [absurd (Ω.bounds_of_mem_connections _ h).2.1 (lt_irrefl _),
    absurd h (Ω.left_lt_right μ).ne', h]

/-- A tied boundary of `μ` is not to the left of `μ`. -/
@[grind →]
theorem IsTiedTo.left_le (h : Ω.IsTiedTo μ p q) : Ω.left μ ≤ p := by
  rcases h with h | ⟨rfl, -⟩ | ⟨rfl, -⟩
  exacts [(Ω.bounds_of_mem_connections _ h).1.le, le_rfl, (Ω.left_lt_right μ).le]

/-- A tied boundary of `μ` is not to the right of `μ`. -/
@[grind →]
theorem IsTiedTo.le_right (h : Ω.IsTiedTo μ p q) : p ≤ Ω.right μ := by
  rcases h with h | ⟨rfl, -⟩ | ⟨rfl, -⟩
  exacts [(Ω.bounds_of_mem_connections _ h).2.1.le, (Ω.left_lt_right μ).le, le_rfl]

/-- Ties are symmetric: if `p` is `μ`-tied to `q`, then `q` is `Δ(μ)`-tied to `p`. -/
theorem IsTiedTo.dual (h : Ω.IsTiedTo μ p q) : Ω.IsTiedTo (Ω.dual μ) q p := by
  rw [isTiedTo_iff, Ω.dual_involutive μ]
  rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl (Ω.dual_mem_connections _ h)
  all_goals by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ) <;> simp [hs, eq_comm]

/-- The boundary `q` is `Δ(μ)`-tied to `p` exactly when `p` is `μ`-tied to `q`. -/
theorem isTiedTo_dual_iff : Ω.IsTiedTo (Ω.dual μ) q p ↔ Ω.IsTiedTo μ p q :=
  ⟨fun h => Ω.dual_involutive μ ▸ h.dual, IsTiedTo.dual⟩

/-- A boundary to which a boundary of `μ` is tied is not to the left of `Δ(μ)`. -/
@[grind →]
theorem IsTiedTo.left_dual_le (h : Ω.IsTiedTo μ p q) : Ω.left (Ω.dual μ) ≤ q :=
  h.dual.left_le

/-- A boundary to which a boundary of `μ` is tied is not to the right of `Δ(μ)`. -/
@[grind →]
theorem IsTiedTo.le_right_dual (h : Ω.IsTiedTo μ p q) : q ≤ Ω.right (Ω.dual μ) :=
  h.dual.le_right

/-- In a formally consistent generalised equation a boundary of `μ` is tied to at most one
boundary of `Δ(μ)`. -/
@[grind →]
theorem IsFormallyConsistent.isTiedTo_unique (hΩ : Ω.IsFormallyConsistent)
    (h : Ω.IsTiedTo μ p q) (h' : Ω.IsTiedTo μ p q') : q = q' := by
  rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases h' with h' | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · have h₁ := hΩ.connections_monotone_or_antitone _ h _ h' rfl le_rfl
      have h₂ := hΩ.connections_monotone_or_antitone _ h' _ h rfl le_rfl
      grind
    · exact absurd (Ω.bounds_of_mem_connections _ h).1 (lt_irrefl _)
    · exact absurd (Ω.bounds_of_mem_connections _ h).2.1 (lt_irrefl _)
  · exact (isTiedTo_left_iff.1 h').symm
  · exact (isTiedTo_right_iff.1 h').symm

/-- In a formally consistent generalised equation the ties of a base `μ` with `ε(μ) = ε(Δμ)` are
strictly increasing. -/
@[grind =>]
theorem IsFormallyConsistent.lt_of_isTiedTo_of_sign_eq (hΩ : Ω.IsFormallyConsistent)
    (hs : Ω.sign μ = Ω.sign (Ω.dual μ)) (h : Ω.IsTiedTo μ p q) (h' : Ω.IsTiedTo μ p' q')
    (hp : p < p') : q < q' := by
  have hne : q ≠ q' := fun hq => hp.ne (hΩ.isTiedTo_unique h.dual (hq ▸ h'.dual))
  rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h' with h' | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h₁ := hΩ.connections_monotone_or_antitone _ h _ h' rfl hp.le
    grind
  all_goals grind [left_lt_right]

/-- In a formally consistent generalised equation the ties of a base `μ` with `ε(μ) ≠ ε(Δμ)` are
strictly decreasing. -/
@[grind =>]
theorem IsFormallyConsistent.lt_of_isTiedTo_of_sign_ne (hΩ : Ω.IsFormallyConsistent)
    (hs : Ω.sign μ ≠ Ω.sign (Ω.dual μ)) (h : Ω.IsTiedTo μ p q) (h' : Ω.IsTiedTo μ p' q')
    (hp : p < p') : q' < q := by
  have hne : q ≠ q' := fun hq => hp.ne (hΩ.isTiedTo_unique h.dual (hq ▸ h'.dual))
  rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h' with h' | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h₁ := hΩ.connections_monotone_or_antitone _ h _ h' rfl hp.le
    grind
  all_goals grind [left_lt_right]

variable (Ω) in
/-- The boundary of `Δ(μ)` to which the boundary `p` of `μ` is tied; the boundary `p` itself if
`p` is not tied. -/
def tiedBoundary (μ : Fin Ω.numBases) (p : Fin (Ω.numItems + 1)) : Fin (Ω.numItems + 1) :=
  if h : ∃ q, Ω.IsTiedTo μ p q then Fin.find (Ω.IsTiedTo μ p) h else p

/-- A boundary of `μ` is tied to `tiedBoundary μ p` exactly when it is tied to some boundary. -/
@[simp, grind =]
theorem isTiedTo_tiedBoundary_iff :
    Ω.IsTiedTo μ p (Ω.tiedBoundary μ p) ↔ ∃ q, Ω.IsTiedTo μ p q := by
  refine ⟨fun h => ⟨_, h⟩, fun h => ?_⟩
  rw [tiedBoundary, dite_eq_left h]
  exact Fin.find_spec h

/-- A boundary of `μ` that is not tied is its own `tiedBoundary`. -/
theorem tiedBoundary_of_not_exists (h : ¬ ∃ q, Ω.IsTiedTo μ p q) : Ω.tiedBoundary μ p = p :=
  dite_eq_right h

/-- The initial boundary of `μ` is tied to the initial boundary of `Δ(μ)` when `ε(μ) = ε(Δμ)`, and
to its terminal boundary otherwise. -/
@[simp, grind =]
theorem tiedBoundary_left : Ω.tiedBoundary μ (Ω.left μ) =
    if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.left (Ω.dual μ) else Ω.right (Ω.dual μ) :=
  isTiedTo_left_iff.1 (isTiedTo_tiedBoundary_iff.2 ⟨_, isTiedTo_left_iff.2 rfl⟩)

/-- The terminal boundary of `μ` is tied to the terminal boundary of `Δ(μ)` when `ε(μ) = ε(Δμ)`,
and to its initial boundary otherwise. -/
@[simp, grind =]
theorem tiedBoundary_right : Ω.tiedBoundary μ (Ω.right μ) =
    if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.right (Ω.dual μ) else Ω.left (Ω.dual μ) :=
  isTiedTo_right_iff.1 (isTiedTo_tiedBoundary_iff.2 ⟨_, isTiedTo_right_iff.2 rfl⟩)

/-- In a formally consistent generalised equation, `tiedBoundary` is the boundary to which a
tied boundary is tied. -/
@[grind =>]
theorem IsFormallyConsistent.tiedBoundary_eq (hΩ : Ω.IsFormallyConsistent)
    (h : Ω.IsTiedTo μ p q) : Ω.tiedBoundary μ p = q :=
  hΩ.isTiedTo_unique (isTiedTo_tiedBoundary_iff.2 ⟨q, h⟩) h

/-- In a formally consistent generalised equation `tiedBoundary μ` is strictly increasing on the
tied boundaries of a base `μ` with `ε(μ) = ε(Δμ)`. -/
theorem IsFormallyConsistent.strictMonoOn_tiedBoundary_of_sign_eq (hΩ : Ω.IsFormallyConsistent)
    (hs : Ω.sign μ = Ω.sign (Ω.dual μ)) :
    StrictMonoOn (Ω.tiedBoundary μ) {p | ∃ q, Ω.IsTiedTo μ p q} := fun _ hp _ hp' =>
  hΩ.lt_of_isTiedTo_of_sign_eq hs (isTiedTo_tiedBoundary_iff.2 hp) (isTiedTo_tiedBoundary_iff.2 hp')

/-- In a formally consistent generalised equation `tiedBoundary μ` is strictly decreasing on the
tied boundaries of a base `μ` with `ε(μ) ≠ ε(Δμ)`. -/
theorem IsFormallyConsistent.strictAntiOn_tiedBoundary_of_sign_ne (hΩ : Ω.IsFormallyConsistent)
    (hs : Ω.sign μ ≠ Ω.sign (Ω.dual μ)) :
    StrictAntiOn (Ω.tiedBoundary μ) {p | ∃ q, Ω.IsTiedTo μ p q} := fun _ hp _ hp' =>
  hΩ.lt_of_isTiedTo_of_sign_ne hs (isTiedTo_tiedBoundary_iff.2 hp) (isTiedTo_tiedBoundary_iff.2 hp')

/-! ### Examples -/

/-- The generalised equation with four items, the dual bases `μ = [0, 2]` and `Δ(μ) = [2, 4]` of
signs `+1` and `s`, and the boundary connection `(1, μ, 3)` with its dual. For `s = true` its
equations are `h₀h₁ = h₂h₃` and `h₀ = h₂`; for `s = false` they are `h₀h₁ = (h₂h₃)⁻¹` and
`h₀ = h₃⁻¹`. -/
private abbrev tiedExample (s : Bool) : GenEq (Fin 2) where
  numItems := 4
  numBases := 2
  left := ![0, 2]
  right := ![2, 4]
  left_lt_right := by decide
  sign := ![true, s]
  dual := ![1, 0]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := {(1, 0, 3), (3, 1, 1)}
  bounds_of_mem_connections := by decide
  dual_mem_connections := by decide

private theorem isFormallyConsistent_tiedExample (s : Bool) :
    (tiedExample s).IsFormallyConsistent := by
  cases s <;> decide

/-- For equal signs the boundaries `0, 1, 2` of `μ = [0, 2]` are tied to the boundaries `2, 3, 4`
of `Δ(μ) = [2, 4]`, in this order. -/
example : (tiedExample true).tiedBoundary 0 0 = 2 ∧ (tiedExample true).tiedBoundary 0 1 = 3 ∧
    (tiedExample true).tiedBoundary 0 2 = 4 :=
  have hΩ := isFormallyConsistent_tiedExample true
  ⟨hΩ.tiedBoundary_eq (isTiedTo_left_iff.2 rfl),
    hΩ.tiedBoundary_eq (isTiedTo_of_mem_connections (by decide)),
    hΩ.tiedBoundary_eq (isTiedTo_right_iff.2 rfl)⟩

/-- For opposite signs the boundaries `0, 1, 2` of `μ = [0, 2]` are tied to the boundaries
`4, 3, 2` of `Δ(μ) = [2, 4]`: the order is reversed. -/
example : (tiedExample false).tiedBoundary 0 0 = 4 ∧ (tiedExample false).tiedBoundary 0 1 = 3 ∧
    (tiedExample false).tiedBoundary 0 2 = 2 :=
  have hΩ := isFormallyConsistent_tiedExample false
  ⟨hΩ.tiedBoundary_eq (isTiedTo_left_iff.2 rfl),
    hΩ.tiedBoundary_eq (isTiedTo_of_mem_connections (by decide)),
    hΩ.tiedBoundary_eq (isTiedTo_right_iff.2 rfl)⟩

/-- The boundary `3` lies outside `μ = [0, 2]`, so it is not `μ`-tied. -/
example (s : Bool) (q : Fin 5) : ¬ (tiedExample s).IsTiedTo 0 3 q :=
  fun h => absurd h.le_right (by cases s <;> decide)

end GenEq

end TauCeti
