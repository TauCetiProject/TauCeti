/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Colimit.Ring.Basic
public import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Data.Fintype.Order

/-!
# Idempotents in directed colimits of rings

An idempotent in a directed colimit of commutative rings comes from an idempotent at a finite
stage. Finitely many idempotents can be lifted simultaneously, above any prescribed stage.
Neither injectivity nor flatness of the transition maps is required: an arbitrary lift need
not be idempotent, but its idempotence equation holds at a later stage.

These lifts allow finite products of quotients by idempotents, hence totally split algebras
with varying ranks, to be constructed over a single stage of a directed system.
-/

public section

namespace Ring.DirectLimit

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {G : ι → Type*}
  [∀ i, CommRing (G i)] {f : ∀ i j, i ≤ j → G i →+* G j}
  [DirectedSystem G (f · · ·)]

/-- If the image of a stage element in a directed colimit is idempotent, its image at some
later stage is already idempotent. -/
theorem exists_isIdempotentElem {i : ι} {x : G i}
    (hx : IsIdempotentElem (of G (f · · ·) i x)) :
    ∃ j, ∃ hij : i ≤ j, IsIdempotentElem (f i j hij x) := by
  have heq : of G (f · · ·) i (x * x) = of G (f · · ·) i x := by
    simpa only [map_mul] using hx.eq
  obtain ⟨j, hij, _, hj⟩ := TauCeti.Ring.DirectLimit.of_eq_of_iff.mp heq
  exact ⟨j, hij, by simpa only [IsIdempotentElem, map_mul] using hj⟩

variable [Nonempty ι]

/-- Every finite family of idempotents in a directed colimit lifts to idempotents at a common
stage above any prescribed index. The finite family may be empty. -/
theorem exists_idempotents {κ : Type*} [Finite κ]
    (e : κ → DirectLimit G (f · · ·)) (he : ∀ k, IsIdempotentElem (e k)) (i : ι) :
    ∃ j, i ≤ j ∧ ∃ e' : κ → G j,
      (∀ k, IsIdempotentElem (e' k)) ∧ ∀ k, of G (f · · ·) j (e' k) = e k := by
  classical
  choose a x hx using fun k ↦ exists_of (e k)
  choose b hab hb using fun k ↦ exists_isIdempotentElem (hx k ▸ he k)
  obtain ⟨c, hc⟩ := Finite.exists_le b
  obtain ⟨j, hij, hcj⟩ := exists_ge_ge i c
  let hbj (k : κ) : b k ≤ j := (hc k).trans hcj
  refine ⟨j, hij, fun k ↦ f (b k) j (hbj k) (f (a k) (b k) (hab k) (x k)),
    fun k ↦ (hb k).map _, fun k ↦ ?_⟩
  rw [of_f, of_f, hx]

end Ring.DirectLimit
