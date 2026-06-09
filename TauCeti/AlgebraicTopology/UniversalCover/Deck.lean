/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Algebra.MulAction
import Mathlib.GroupTheory.GroupAction.SubMulAction
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
preserves every fibre of `p`; consequently each fibre inherits an action of `Deck p`, and
the restriction to a fibre is a monoid homomorphism into the homeomorphism group of that
fibre.

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

/-- On points, the action of a deck transformation is evaluation of its underlying
homeomorphism. The action itself is inherited, by subgroup transfer, from the tautological
action of `E ≃ₜ E` on `E`. -/
@[simp]
lemma smul_eq_apply (φ : Deck p) (e : E) : φ • e = φ.1 e := by
  rw [MulAction.subgroup_smul_def, Homeomorph.smul_def]

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

/-- Each fibre of the projection is invariant under the deck-transformation action. -/
def fiberSubMulAction (b : B) : SubMulAction (Deck p) E where
  carrier := p ⁻¹' {b}
  smul_mem' φ e he := by
    simpa only [smul_eq_apply] using mapsTo_fiber φ b he

/-- Membership in the fibre subaction is membership in the corresponding fibre. -/
@[simp]
lemma mem_fiberSubMulAction {b : B} {e : E} :
    e ∈ fiberSubMulAction (p := p) b ↔ p e = b :=
  Iff.rfl

/-- The underlying set of the fibre subaction is the corresponding fibre. -/
@[simp]
lemma coe_fiberSubMulAction (b : B) :
    (fiberSubMulAction (p := p) b : Set E) = p ⁻¹' {b} :=
  rfl

/-- Acting by a deck transformation preserves membership in a named fibre. -/
@[simp]
lemma smul_mem_fiber_iff (φ : Deck p) {b : B} {e : E} :
    p (φ • e) = b ↔ p e = b := by
  simp only [smul_eq_apply, map_proj]

/-- Acting by a deck transformation preserves a named fibre. -/
lemma smul_mem_fiber (φ : Deck p) {b : B} {e : E} (he : p e = b) : p (φ • e) = b :=
  (smul_mem_fiber_iff φ).2 he

/-- The action of `Deck p` on a fibre is the action inherited from its invariant-subset
structure. -/
instance fiberMulAction (b : B) : MulAction (Deck p) (p ⁻¹' {b}) :=
  (fiberSubMulAction (p := p) b).mulAction

/-- On a fibre, the inherited action is evaluation of the underlying homeomorphism. -/
@[simp]
lemma coe_fiber_smul (φ : Deck p) {b : B} (e : p ⁻¹' {b}) :
    ((φ • e : p ⁻¹' {b}) : E) = φ.1 e.1 := by
  exact smul_eq_apply φ e.1

/-- On each fibre, scalar multiplication by a deck transformation is continuous. -/
instance fiberContinuousConstSMul (b : B) :
    ContinuousConstSMul (Deck p) (p ⁻¹' {b}) where
  continuous_const_smul φ :=
    ((continuous_const_smul (Γ := Deck p) (T := E) φ).comp continuous_subtype_val).subtype_mk
      fun e => smul_mem_fiber (p := p) φ e.2

/-- A deck transformation restricts to a homeomorphism of every fibre of the projection,
as the homeomorphism attached to the inherited fibre action. -/
def fiberHomeomorph (φ : Deck p) (b : B) : p ⁻¹' {b} ≃ₜ p ⁻¹' {b} :=
  Homeomorph.smul φ

/-- On points, the fibre homeomorphism induced by a deck transformation is just evaluation
of that transformation. -/
@[simp]
lemma fiberHomeomorph_apply (φ : Deck p) (b : B) (e : p ⁻¹' {b}) :
    (fiberHomeomorph φ b e : E) = φ.1 e.1 := by
  rw [fiberHomeomorph, Homeomorph.smul_apply, coe_fiber_smul (p := p) φ e]

/-- On points, the inverse fibre homeomorphism induced by a deck transformation is
evaluation of the inverse homeomorphism. -/
@[simp]
lemma fiberHomeomorph_symm_apply (φ : Deck p) (b : B) (e : p ⁻¹' {b}) :
    ((fiberHomeomorph φ b).symm e : E) = φ.1.symm e.1 := by
  rw [fiberHomeomorph, Homeomorph.smul_symm_apply]
  rw [coe_fiber_smul (p := p) (φ⁻¹) e]
  simp [Homeomorph.inv_apply]

/-- The fibre homeomorphism induced by a deck transformation is the permutation coming from
the induced fibre action. -/
lemma fiberHomeomorph_toEquiv (φ : Deck p) (b : B) :
    (fiberHomeomorph φ b).toEquiv = MulAction.toPerm φ := by
  ext e
  simp [fiberHomeomorph, Homeomorph.smul_apply]

/-- The identity deck transformation restricts to the identity on each fibre. -/
@[simp]
lemma fiberHomeomorph_one (b : B) :
    fiberHomeomorph (p := p) (1 : Deck p) b = 1 := by
  ext e
  simp [fiberHomeomorph]

/-- Restricting a product of deck transformations to a fibre is the product of the
restrictions. -/
@[simp]
lemma fiberHomeomorph_mul (φ ψ : Deck p) (b : B) :
    fiberHomeomorph (φ * ψ) b = fiberHomeomorph φ b * fiberHomeomorph ψ b := by
  ext e
  simp [fiberHomeomorph, mul_smul]

/-- Restriction of deck transformations to a fixed fibre, as a homomorphism into the
homeomorphism group of that fibre. -/
def fiberHomeomorphHom (b : B) : Deck p →* (p ⁻¹' {b} ≃ₜ p ⁻¹' {b}) :=
  { toFun := fun φ => fiberHomeomorph φ b
    map_one' := fiberHomeomorph_one (p := p) b
    map_mul' := fun φ ψ => fiberHomeomorph_mul φ ψ b }

/-- The fibre restriction homomorphism sends a deck transformation to its induced
homeomorphism of that fibre. -/
@[simp]
lemma fiberHomeomorphHom_apply (b : B) (φ : Deck p) :
    fiberHomeomorphHom (p := p) b φ = fiberHomeomorph φ b :=
  rfl

/-- The homeomorphism attached to a deck transformation acts on a fibre as scalar
multiplication by that deck transformation. -/
@[simp]
lemma fiberHomeomorph_apply_eq_smul (φ : Deck p) (b : B) (e : p ⁻¹' {b}) :
    fiberHomeomorph φ b e = φ • e :=
  Subtype.ext (by rw [fiberHomeomorph_apply, coe_fiber_smul (p := p) φ e])

-- `FaithfulSMul (Deck p) E` and `ContinuousConstSMul (Deck p) E` are inherited from the generic
-- subgroup instances in `TauCeti.Topology.Algebra.HomeomorphAction`; `Deck p` is a `Subgroup`.

end Deck

end TauCeti
