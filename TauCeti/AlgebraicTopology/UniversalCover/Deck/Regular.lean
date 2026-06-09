/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.GroupTheory.GroupAction.Transitive
import TauCeti.AlgebraicTopology.UniversalCover.Deck.Connected
import TauCeti.AlgebraicTopology.UniversalCover.Deck.FiberTransport

/-!
# Regular deck actions on fibres

For a map `p : E → B`, regularity of the deck action is the statement that `p` is
surjective and the deck transformation group acts transitively on every fibre. This is the
deck-action formulation of regular covers used by the universal-covers roadmap before the
later theorem identifying the deck group of the cover associated to `H ≤ π₁(X, x₀)`.

The definition in this file is deliberately phrased only in terms of the existing
`Deck p` group and Mathlib's `MulAction.IsPretransitive`. It does not assert that `p` is a
covering map; the covering hypothesis is needed only for the connected-cover freeness result
that turns fibre transitivity into a canonical equivalence between the deck group and a
chosen fibre.

## Main declarations

* `TauCeti.Deck.IsRegular`: `p` is surjective and `Deck p` acts transitively on each fibre.
* `TauCeti.Deck.isRegular_iff_exists_apply_eq`: regularity is equivalent to surjectivity
  plus pointwise deck transitivity on fibres.
* `TauCeti.Deck.IsRegular.exists_apply_eq`: regularity moves any point of a fibre to any
  other point of the same fibre by a deck transformation.
* `TauCeti.Deck.IsRegular.conj`: regularity is invariant under isomorphism of maps over the
  same base.
* `TauCeti.Deck.deckEquivFiberOfSurjective`: for a preconnected covering whose orbit map at
  one fibre point is surjective, evaluation at that point identifies the deck group with
  that fibre.

## References

This supplies a prerequisite for the Tau Ceti universal-covers roadmap, Stage 2, where
regular covers are characterized by transitivity of the deck action on fibres and the deck
group of the cover associated to a subgroup is computed as a normalizer quotient.
-/

namespace TauCeti

namespace Deck

variable {E F B : Type*} [TopologicalSpace E] [TopologicalSpace F] {p : E → B} {q : F → B}

/-- The deck action of a map is regular when the map is surjective and the deck group acts
transitively on every fibre.

For covering maps between connected, locally path-connected spaces this is the usual
deck-action formulation of a regular covering. The definition is kept independent of
`IsCoveringMap` so it can also be transported along isomorphisms of maps without carrying
unused topological hypotheses. -/
def IsRegular (p : E → B) : Prop :=
  Function.Surjective p ∧ ∀ b : B, MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})

/-- Characteristic restatement of regularity of the deck action. -/
lemma isRegular_iff :
    IsRegular p ↔
      Function.Surjective p ∧ ∀ b : B, MulAction.IsPretransitive (Deck p) (p ⁻¹' {b}) :=
  Iff.rfl

/-- Characteristic pointwise restatement of regularity of the deck action. -/
lemma isRegular_iff_exists_apply_eq :
    IsRegular p ↔
      Function.Surjective p ∧
        ∀ {e e' : E}, p e = p e' → ∃ φ : Deck p, φ.1 e = e' := by
  constructor
  · intro hreg
    refine ⟨hreg.1, ?_⟩
    intro e e' heq
    let b := p e
    let x : p ⁻¹' {b} := ⟨e, by simp [b]⟩
    let y : p ⁻¹' {b} := ⟨e', by simp [b, heq.symm]⟩
    letI := hreg.2 b
    rcases MulAction.exists_smul_eq (Deck p) x y with ⟨φ, hφ⟩
    exact ⟨φ, by simpa [fiber_smul_coe] using congrArg Subtype.val hφ⟩
  · rintro ⟨hsurj, hpoint⟩
    refine ⟨hsurj, fun b => ?_⟩
    refine MulAction.IsPretransitive.mk ?_
    intro x y
    have hxy : p x.1 = p y.1 := by
      have hx : p x.1 = b := Set.mem_singleton_iff.mp x.2
      have hy : p y.1 = b := Set.mem_singleton_iff.mp y.2
      rw [hx, hy]
    rcases hpoint hxy with ⟨φ, hφ⟩
    exact ⟨φ, by ext; simpa [fiber_smul_coe] using hφ⟩

namespace IsRegular

/-- A regular deck action has nonempty fibres. -/
lemma nonempty_fiber (hreg : IsRegular p) (b : B) : Nonempty (p ⁻¹' {b}) := by
  rcases hreg.1 b with ⟨e, he⟩
  exact ⟨⟨e, by simpa [Set.mem_preimage, Set.mem_singleton_iff] using he⟩⟩

/-- The deck action on each fibre of a regular map is transitive. -/
lemma fiber_isPretransitive (hreg : IsRegular p) (b : B) :
    MulAction.IsPretransitive (Deck p) (p ⁻¹' {b}) :=
  hreg.2 b

/-- For a regular map, any two points with the same projection differ by a deck
transformation. -/
lemma exists_apply_eq (hreg : IsRegular p) {e e' : E} (heq : p e = p e') :
    ∃ φ : Deck p, φ.1 e = e' :=
  isRegular_iff_exists_apply_eq.mp hreg |>.2 heq

/-- Regularity of the deck action is transported by an over-base homeomorphism. -/
lemma conj (hreg : IsRegular p) (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) : IsRegular q := by
  refine ⟨?_, fun b => ?_⟩
  · intro b
    rcases hreg.1 b with ⟨e, he⟩
    exact ⟨h e, by rw [hpq, he]⟩
  · refine MulAction.IsPretransitive.mk ?_
    intro f f'
    let e : p ⁻¹' {b} := (fiberMap h hpq b).symm f
    let e' : p ⁻¹' {b} := (fiberMap h hpq b).symm f'
    letI := hreg.fiber_isPretransitive b
    rcases MulAction.exists_smul_eq (Deck p) e e' with ⟨φ, hφ⟩
    refine ⟨conjMulEquiv h hpq φ, ?_⟩
    have hmap := congrArg (fiberMap h hpq b) hφ
    rw [fiberMap_smul h hpq φ e] at hmap
    have he : fiberMap h hpq b e = f := by
      simpa [e] using (fiberMap h hpq b).apply_symm_apply f
    have he' : fiberMap h hpq b e' = f' := by
      simpa [e'] using (fiberMap h hpq b).apply_symm_apply f'
    rwa [he, he'] at hmap

/-- Regularity is invariant under an over-base homeomorphism. -/
lemma conj_iff (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) :
    IsRegular q ↔ IsRegular p := by
  constructor
  · intro hq
    simpa using hq.conj h.symm (map_symm_eq_of_map_eq h hpq)
  · intro hp
    exact hp.conj h hpq

end IsRegular

section Connected

variable [TopologicalSpace B] {b : B}

/-- Evaluation at a point in a fibre is injective for a preconnected covering. -/
lemma orbitMap_injective [PreconnectedSpace E] (hp : IsCoveringMap p) (e : p ⁻¹' {b}) :
    Function.Injective fun φ : Deck p => φ • e := by
  intro φ ψ hφψ
  exact eq_of_fiber_smul_eq_fiber_smul hp φ ψ hφψ

/-- For a preconnected covering whose orbit map at the chosen fibre point is surjective,
evaluation at that point identifies the deck group with that fibre.

This is the simply-transitive fibre action package used later when regular covers are
compared with normal subgroups and normalizer quotients. -/
noncomputable def deckEquivFiberOfSurjective [PreconnectedSpace E] (hp : IsCoveringMap p)
    (e : p ⁻¹' {b}) (hsurj : Function.Surjective fun φ : Deck p => φ • e) :
    Deck p ≃ p ⁻¹' {b} :=
  Equiv.ofBijective (fun φ : Deck p => φ • e)
    ⟨orbitMap_injective hp e, hsurj⟩

/-- For a preconnected covering with regular deck action, evaluation at a chosen fibre point
identifies the deck group with that fibre. -/
noncomputable def deckEquivFiber [PreconnectedSpace E] (hp : IsCoveringMap p)
    (hreg : IsRegular p) (e : p ⁻¹' {b}) : Deck p ≃ p ⁻¹' {b} := by
  letI := hreg.fiber_isPretransitive b
  exact deckEquivFiberOfSurjective hp e (MulAction.surjective_smul (Deck p) e)

/-- The local equivalence from deck transformations to a fibre evaluates a deck
transformation at the chosen fibre point. -/
@[simp]
lemma deckEquivFiberOfSurjective_apply [PreconnectedSpace E] (hp : IsCoveringMap p)
    (e : p ⁻¹' {b}) (hsurj : Function.Surjective fun φ : Deck p => φ • e) (φ : Deck p) :
    deckEquivFiberOfSurjective hp e hsurj φ = φ • e :=
  rfl

/-- On underlying points, the local deck-to-fibre equivalence is evaluation of the
underlying homeomorphism. -/
@[simp]
lemma deckEquivFiberOfSurjective_apply_coe [PreconnectedSpace E] (hp : IsCoveringMap p)
    (e : p ⁻¹' {b}) (hsurj : Function.Surjective fun φ : Deck p => φ • e) (φ : Deck p) :
    (deckEquivFiberOfSurjective hp e hsurj φ : E) = φ.1 e.1 := by
  rw [deckEquivFiberOfSurjective_apply]
  exact fiber_smul_coe φ e

/-- The inverse of `deckEquivFiberOfSurjective` is characterized by the deck transformation it
returns: it sends the chosen fibre point to the requested fibre point. -/
@[simp]
lemma deckEquivFiberOfSurjective_symm_smul [PreconnectedSpace E] (hp : IsCoveringMap p)
    (e : p ⁻¹' {b}) (hsurj : Function.Surjective fun φ : Deck p => φ • e)
    (e' : p ⁻¹' {b}) :
    (deckEquivFiberOfSurjective hp e hsurj).symm e' • e = e' :=
  (deckEquivFiberOfSurjective hp e hsurj).apply_symm_apply e'

/-- On underlying points, the inverse of `deckEquivFiberOfSurjective` sends the chosen point to
the requested point. -/
@[simp]
lemma deckEquivFiberOfSurjective_symm_apply_coe [PreconnectedSpace E]
    (hp : IsCoveringMap p) (e : p ⁻¹' {b})
    (hsurj : Function.Surjective fun φ : Deck p => φ • e) (e' : p ⁻¹' {b}) :
    (((deckEquivFiberOfSurjective hp e hsurj).symm e').1 e.1 : E) = e'.1 := by
  simpa [fiber_smul_coe] using
    congrArg Subtype.val (deckEquivFiberOfSurjective_symm_smul hp e hsurj e')

/-- The equivalence from deck transformations to a fibre evaluates a deck transformation at
the chosen fibre point. -/
@[simp]
lemma deckEquivFiber_apply [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (e : p ⁻¹' {b}) (φ : Deck p) :
    deckEquivFiber hp hreg e φ = φ • e :=
  rfl

/-- On underlying points, the deck-to-fibre equivalence is evaluation of the underlying
homeomorphism. -/
@[simp]
lemma deckEquivFiber_apply_coe [PreconnectedSpace E] (hp : IsCoveringMap p)
    (hreg : IsRegular p) (e : p ⁻¹' {b}) (φ : Deck p) :
    (deckEquivFiber hp hreg e φ : E) = φ.1 e.1 := by
  rw [deckEquivFiber_apply]
  exact fiber_smul_coe φ e

/-- The inverse of `deckEquivFiber` is characterized by the deck transformation it returns:
it sends the chosen fibre point to the requested fibre point. -/
@[simp]
lemma deckEquivFiber_symm_smul [PreconnectedSpace E] (hp : IsCoveringMap p)
    (hreg : IsRegular p) (e e' : p ⁻¹' {b}) :
    (deckEquivFiber hp hreg e).symm e' • e = e' :=
  (deckEquivFiber hp hreg e).apply_symm_apply e'

/-- On underlying points, the inverse of `deckEquivFiber` sends the chosen point to the
requested point. -/
@[simp]
lemma deckEquivFiber_symm_apply_coe [PreconnectedSpace E] (hp : IsCoveringMap p)
    (hreg : IsRegular p) (e e' : p ⁻¹' {b}) :
    (((deckEquivFiber hp hreg e).symm e').1 e.1 : E) = e'.1 := by
  simpa [fiber_smul_coe] using congrArg Subtype.val (deckEquivFiber_symm_smul hp hreg e e')

end Connected

end Deck

end TauCeti
