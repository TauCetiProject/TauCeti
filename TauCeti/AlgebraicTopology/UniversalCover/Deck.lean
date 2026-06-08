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
preserves every fibre of `p`; restricting to a fibre gives a monoid homomorphism into the
homeomorphism group of that fibre, and hence an action on the fibre.

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

/-- The fibre homeomorphism induced by the identity deck transformation is the identity. -/
@[simp]
lemma fiberHomeomorph_one (b : B) : fiberHomeomorph (1 : Deck p) b = 1 := by
  ext e
  rfl

/-- The fibre homeomorphism induced by a product of deck transformations is the product of
the induced fibre homeomorphisms. -/
@[simp]
lemma fiberHomeomorph_mul (φ ψ : Deck p) (b : B) :
    fiberHomeomorph (φ * ψ) b = fiberHomeomorph φ b * fiberHomeomorph ψ b := by
  ext e
  rfl

/-- The fibre homeomorphism induced by an inverse deck transformation is the inverse of the
induced fibre homeomorphism. -/
@[simp]
lemma fiberHomeomorph_inv (φ : Deck p) (b : B) :
    fiberHomeomorph φ⁻¹ b = (fiberHomeomorph φ b)⁻¹ := by
  ext e
  rfl

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

/-- Restricting deck transformations to a fibre is a monoid homomorphism into the
homeomorphism group of that fibre. This is the algebraic form of the deck action on a
single sheet over the base point. -/
def fiberHomeomorphMonoidHom (b : B) : Deck p →* (p ⁻¹' {b} ≃ₜ p ⁻¹' {b}) where
  toFun φ := fiberHomeomorph φ b
  map_one' := fiberHomeomorph_one b
  map_mul' φ ψ := fiberHomeomorph_mul φ ψ b

/-- The fibre-restriction monoid homomorphism evaluates to `fiberHomeomorph`. -/
@[simp]
lemma fiberHomeomorphMonoidHom_apply (b : B) (φ : Deck p) :
    fiberHomeomorphMonoidHom b φ = fiberHomeomorph φ b :=
  rfl

/-- A fixed fibre of `p` carries the action of `Deck p` induced by restriction of deck
transformations. -/
instance fiberMulAction (b : B) : MulAction (Deck p) (p ⁻¹' {b}) where
  smul φ e := fiberHomeomorph φ b e
  one_smul e := by
    ext
    rfl
  mul_smul φ ψ e := by
    ext
    rfl

/-- The action of a deck transformation on a point in a fibre is just evaluation of the
underlying homeomorphism. -/
@[simp]
lemma fiber_smul_coe (φ : Deck p) (b : B) (e : p ⁻¹' {b}) :
    (φ • e : E) = φ.1 e.1 :=
  rfl

/-- The inverse deck transformation acts on a fibre by the inverse homeomorphism. -/
@[simp]
lemma inv_fiber_smul_coe (φ : Deck p) (b : B) (e : p ⁻¹' {b}) :
    (φ⁻¹ • e : E) = φ.1.symm e.1 :=
  rfl

/-- Acting by a deck transformation keeps a point in the same fibre. -/
lemma fiber_smul_mem (φ : Deck p) (b : B) (e : p ⁻¹' {b}) :
    p ((φ • e : p ⁻¹' {b}) : E) = b :=
  (φ • e).2

/-- The action of a fixed deck transformation on a fibre is continuous. -/
instance fiberContinuousConstSMul (b : B) : ContinuousConstSMul (Deck p) (p ⁻¹' {b}) :=
  ⟨fun φ => (fiberHomeomorph φ b).continuous⟩

/-- Evaluation at a chosen point of a fibre, as a map from deck transformations to that
fibre. For a connected covering space this map is the usual way to identify deck
transformations with their value on one lift. -/
def evalAtFiber {b : B} (e : p ⁻¹' {b}) : Deck p → p ⁻¹' {b} :=
  fun φ => φ • e

/-- Evaluation at a fibre point is the fibre action. -/
@[simp]
lemma evalAtFiber_apply {b : B} (e : p ⁻¹' {b}) (φ : Deck p) :
    evalAtFiber e φ = φ • e :=
  rfl

/-- Coercing evaluation at a fibre point to the total space is evaluation of the underlying
homeomorphism. -/
@[simp]
lemma evalAtFiber_apply_coe {b : B} (e : p ⁻¹' {b}) (φ : Deck p) :
    (evalAtFiber e φ : E) = φ.1 e.1 :=
  rfl

/-- A deck transformation stabilizes a fibre point exactly when its underlying
homeomorphism fixes the corresponding point of the total space. -/
lemma mem_fiber_stabilizer_iff {b : B} (e : p ⁻¹' {b}) (φ : Deck p) :
    φ ∈ MulAction.stabilizer (Deck p) e ↔ φ.1 e.1 = e.1 := by
  constructor
  · intro h
    exact Subtype.ext_iff.mp h
  · intro h
    exact Subtype.ext h

/-- If two deck transformations have the same value at a fibre point, then their quotient
fixes that point. -/
lemma div_mem_stabilizer_of_smul_eq {b : B} {e : p ⁻¹' {b}} {φ ψ : Deck p}
    (h : φ • e = ψ • e) : ψ⁻¹ * φ ∈ MulAction.stabilizer (Deck p) e := by
  rw [mem_fiber_stabilizer_iff]
  calc
    ((ψ⁻¹ * φ : Deck p) : E ≃ₜ E) e.1 = ψ.1.symm (φ.1 e.1) := rfl
    _ = ψ.1.symm (ψ.1 e.1) := by
      rw [show φ.1 e.1 = ψ.1 e.1 from Subtype.ext_iff.mp h]
    _ = e.1 := Homeomorph.symm_apply_apply ψ.1 e.1

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
