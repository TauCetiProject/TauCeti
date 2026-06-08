/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Homeomorph.Lemmas
import TauCeti.Topology.Algebra.HomeomorphAction

/-!
# Deck transformations of a map

For a map `p : E → B`, its deck transformations are the homeomorphisms of `E` over `B`,
viewed as a subgroup of the homeomorphism group `E ≃ₜ E`. This is the first algebraic
piece needed by the universal-covers roadmap Stage 0.4: for a covering projection `p`, the
subgroup `Deck p` will be the deck transformation group.

The action of `Deck p` on the total space is inherited, by subgroup transfer, from the
tautological action of the ambient homeomorphism group `E ≃ₜ E` on `E`
(`TauCeti.Homeomorph.applyMulAction`). Each deck transformation preserves `p`, hence
preserves every fibre of `p`.

A homeomorphism between two total spaces over the same base also transports deck
transformations by conjugation. This is the small bookkeeping API needed before comparing
deck groups of isomorphic covers.

## References

This file follows the deck-transformation target in the Tau Ceti universal-covers roadmap,
Stage 0.4, and the shape of the construction in Kim Morrison's mathlib4#40135.
-/

namespace TauCeti

variable {E B : Type*} [TopologicalSpace E] (p : E → B)

/-- The deck transformations of a map `p : E → B`, as the subgroup of homeomorphisms of `E`
which commute with `p`. For a covering projection, this is the usual deck transformation
group. -/
def Deck : Subgroup (E ≃ₜ E) where
  carrier := {φ | ∀ e, p (φ e) = p e}
  one_mem' e := rfl
  mul_mem' hφ hψ e := by
    rw [Homeomorph.mul_apply, hφ, hψ]
  inv_mem' := by
    intro φ hφ e
    have h := hφ (φ⁻¹ e)
    simpa only [Homeomorph.inv_apply, Homeomorph.apply_symm_apply] using h.symm

namespace Deck

variable {p}

/-- A homeomorphism lies in `Deck p` exactly when it preserves `p` pointwise. -/
@[simp]
lemma mem_iff (φ : E ≃ₜ E) : φ ∈ Deck p ↔ ∀ e, p (φ e) = p e :=
  Iff.rfl

/-- A deck transformation preserves the projection map pointwise. -/
lemma map_proj (φ : Deck p) (e : E) : p (φ.1 e) = p e :=
  φ.2 e

/-- A deck transformation preserves each fibre of the projection. -/
lemma mapsTo_fiber (φ : Deck p) (b : B) : Set.MapsTo φ.1 (p ⁻¹' {b}) (p ⁻¹' {b}) := by
  intro e he
  simpa only [Set.mem_preimage, Set.mem_singleton_iff, map_proj] using he

/-- The inverse of a deck transformation also preserves each fibre of the projection. -/
lemma mapsTo_fiber_symm (φ : Deck p) (b : B) :
    Set.MapsTo φ.1.symm (p ⁻¹' {b}) (p ⁻¹' {b}) := by
  intro e he
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at he ⊢
  rw [← map_proj φ (φ.1.symm e), Homeomorph.apply_symm_apply]
  exact he

/-- A deck transformation restricts to a homeomorphism of every fibre of the projection,
the restriction of its underlying homeomorphism along `Homeomorph.subtype`. -/
def fiberHomeomorph (φ : Deck p) (b : B) : p ⁻¹' {b} ≃ₜ p ⁻¹' {b} :=
  φ.1.subtype fun e => by simp [Set.mem_preimage, eq_comm, map_proj]

/-- On points, the fibre homeomorphism induced by a deck transformation is just evaluation
of that transformation. -/
@[simp]
lemma fiberHomeomorph_apply (φ : Deck p) (b : B) (e : p ⁻¹' {b}) :
    (fiberHomeomorph φ b e : E) = φ.1 e.1 :=
  rfl

/-- On points, the inverse fibre homeomorphism induced by a deck transformation is
evaluation of the inverse homeomorphism. -/
@[simp]
lemma fiberHomeomorph_symm_apply (φ : Deck p) (b : B) (e : p ⁻¹' {b}) :
    ((fiberHomeomorph φ b).symm e : E) = φ.1.symm e.1 :=
  rfl

/-- On points, the action of a deck transformation is evaluation of its underlying
homeomorphism. The action itself is inherited, by subgroup transfer, from the tautological
action of `E ≃ₜ E` on `E`. -/
@[simp]
lemma smul_eq_apply (φ : Deck p) (e : E) : φ • e = φ.1 e :=
  rfl

-- `FaithfulSMul (Deck p) E` and `ContinuousConstSMul (Deck p) E` are inherited from the generic
-- subgroup instances in `TauCeti.Topology.Algebra.HomeomorphAction`; `Deck p` is a `Subgroup`.

variable {F : Type*} {q : F → B}

omit [TopologicalSpace E] in
/-- The compatibility condition for the inverse of an equivalence over a common base. -/
lemma projection_symm_eq (e : E ≃ F) (h : ∀ x, q (e x) = p x) (y : F) :
    p (e.symm y) = q y := by
  calc
    p (e.symm y) = q (e (e.symm y)) := (h (e.symm y)).symm
    _ = q y := by simp

variable [TopologicalSpace F]

/-- Conjugating by a homeomorphism of total spaces over the same base sends deck
transformations of `p` to deck transformations of `q`. -/
def conj (e : E ≃ₜ F) (h : ∀ x, q (e x) = p x) (φ : Deck p) : Deck q where
  val := (e.symm.trans φ.1).trans e
  property y := by
    calc
      q (((e.symm.trans φ.1).trans e) y) = q (e (φ.1 (e.symm y))) := rfl
      _ = p (φ.1 (e.symm y)) := h (φ.1 (e.symm y))
      _ = p (e.symm y) := map_proj φ (e.symm y)
      _ = q y := projection_symm_eq (e : E ≃ F) h y

/-- The underlying map of the conjugated deck transformation. -/
@[simp]
lemma conj_apply (e : E ≃ₜ F) (h : ∀ x, q (e x) = p x) (φ : Deck p) (y : F) :
    (conj e h φ).1 y = e (φ.1 (e.symm y)) :=
  rfl

/-- The inverse underlying map of the conjugated deck transformation. -/
@[simp]
lemma conj_symm_apply (e : E ≃ₜ F) (h : ∀ x, q (e x) = p x) (φ : Deck p) (y : F) :
    (conj e h φ).1.symm y = e (φ.1.symm (e.symm y)) :=
  rfl

/-- Conjugating the identity deck transformation gives the identity deck transformation. -/
@[simp]
lemma conj_one (e : E ≃ₜ F) (h : ∀ x, q (e x) = p x) :
    conj e h (1 : Deck p) = 1 := by
  ext y
  simp [conj]

/-- Conjugation by a homeomorphism over the base respects multiplication of deck
transformations. -/
@[simp]
lemma conj_mul (e : E ≃ₜ F) (h : ∀ x, q (e x) = p x) (φ ψ : Deck p) :
    conj e h (φ * ψ) = conj e h φ * conj e h ψ := by
  ext y
  simp [conj]

/-- A homeomorphism of total spaces over a common base identifies the two deck groups by
conjugation. This is the deck-group invariance under isomorphism of covers. -/
def conjMulEquiv (e : E ≃ₜ F) (h : ∀ x, q (e x) = p x) : Deck p ≃* Deck q where
  toFun := conj e h
  invFun := conj e.symm (projection_symm_eq (e : E ≃ F) h)
  left_inv φ := by
    ext x
    simp [conj]
  right_inv ψ := by
    ext y
    simp [conj]
  map_mul' := conj_mul e h

/-- The deck-group equivalence induced by a homeomorphism over the base acts by
conjugation. -/
@[simp]
lemma conjMulEquiv_apply (e : E ≃ₜ F) (h : ∀ x, q (e x) = p x) (φ : Deck p) :
    conjMulEquiv e h φ = conj e h φ :=
  rfl

/-- Pointwise form of `Deck.conjMulEquiv_apply`. -/
@[simp]
lemma conjMulEquiv_apply_coe (e : E ≃ₜ F) (h : ∀ x, q (e x) = p x) (φ : Deck p) (y : F) :
    ((conjMulEquiv e h φ : Deck q).1 y) = e (φ.1 (e.symm y)) :=
  rfl

/-- The inverse of the deck-group equivalence induced by a homeomorphism over the base is
conjugation by the inverse homeomorphism. -/
@[simp]
lemma conjMulEquiv_symm_apply (e : E ≃ₜ F) (h : ∀ x, q (e x) = p x) (ψ : Deck q) :
    (conjMulEquiv e h).symm ψ = conj e.symm (projection_symm_eq (e : E ≃ F) h) ψ :=
  rfl

/-- Pointwise form of `Deck.conjMulEquiv_symm_apply`. -/
@[simp]
lemma conjMulEquiv_symm_apply_coe
    (e : E ≃ₜ F) (h : ∀ x, q (e x) = p x) (ψ : Deck q) (x : E) :
    (((conjMulEquiv e h).symm ψ : Deck p).1 x) = e.symm (ψ.1 (e x)) :=
  rfl

end Deck

end TauCeti
