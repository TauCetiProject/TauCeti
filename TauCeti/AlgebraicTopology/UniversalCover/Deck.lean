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
preserves every fibre of `p`. Restricting to a fixed fibre is compatible with the group
operation, so each fibre carries the induced action of the deck group.

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

/-- The identity deck transformation restricts to the identity homeomorphism on each fibre. -/
@[simp]
lemma fiberHomeomorph_one (b : B) :
    fiberHomeomorph (1 : Deck p) b = Homeomorph.refl (p ⁻¹' {b}) := by
  ext e
  rfl

/-- Restricting deck transformations to a fibre respects multiplication. -/
@[simp]
lemma fiberHomeomorph_mul (φ ψ : Deck p) (b : B) :
    fiberHomeomorph (φ * ψ) b = fiberHomeomorph φ b * fiberHomeomorph ψ b := by
  ext e
  rfl

/-- Restricting deck transformations to a fibre respects inverse. -/
@[simp]
lemma fiberHomeomorph_inv (φ : Deck p) (b : B) :
    fiberHomeomorph φ⁻¹ b = (fiberHomeomorph φ b)⁻¹ := by
  ext e
  rfl

/-- Restricting deck transformations to a fibre respects division. -/
@[simp]
lemma fiberHomeomorph_div (φ ψ : Deck p) (b : B) :
    fiberHomeomorph (φ / ψ) b = fiberHomeomorph φ b / fiberHomeomorph ψ b := by
  ext e
  rfl

/-- Restriction to a fixed fibre, as a monoid homomorphism from deck transformations to
homeomorphisms of that fibre. This records the composition convention used by the deck group:
the restriction of `φ * ψ` is the composite of the restriction of `φ` with the restriction of
`ψ`. -/
def fiberHomeomorphHom (b : B) : Deck p →* p ⁻¹' {b} ≃ₜ p ⁻¹' {b} where
  toFun φ := fiberHomeomorph φ b
  map_one' := fiberHomeomorph_one b
  map_mul' φ ψ := fiberHomeomorph_mul φ ψ b

/-- The monoid homomorphism to homeomorphisms of a fibre is restriction of deck
transformations. -/
@[simp]
lemma fiberHomeomorphHom_apply (b : B) (φ : Deck p) :
    fiberHomeomorphHom (p := p) b φ = fiberHomeomorph φ b :=
  rfl

/-- A deck transformation acts on each fibre by restricting its underlying homeomorphism. -/
instance fiberMulAction (b : B) : MulAction (Deck p) (p ⁻¹' {b}) where
  __ := MulAction.compHom _ (fiberHomeomorphHom (p := p) b)

/-- On points of a fibre, the induced fibre action is evaluation of the underlying
homeomorphism. -/
@[simp]
lemma fiber_smul_eq_apply (φ : Deck p) (b : B) (e : p ⁻¹' {b}) :
    (φ • e : E) = φ.1 e.1 :=
  rfl

/-- The induced action on a fibre agrees with the restricted homeomorphism. -/
lemma fiber_smul_eq_fiberHomeomorph (φ : Deck p) (b : B) (e : p ⁻¹' {b}) :
    φ • e = fiberHomeomorph φ b e :=
  rfl

/-- On points, the action of a deck transformation is evaluation of its underlying
homeomorphism. The action itself is inherited, by subgroup transfer, from the tautological
action of `E ≃ₜ E` on `E`. -/
@[simp]
lemma smul_eq_apply (φ : Deck p) (e : E) : φ • e = φ.1 e :=
  rfl

-- `FaithfulSMul (Deck p) E` and `ContinuousConstSMul (Deck p) E` are inherited from the generic
-- subgroup instances in `TauCeti.Topology.Algebra.HomeomorphAction`; `Deck p` is a `Subgroup`.

end Deck

end TauCeti
