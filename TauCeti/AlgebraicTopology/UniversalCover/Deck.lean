/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Homeomorph.Defs

/-!
# Deck transformations of a map

For a map `p : E → B`, its deck transformations are the homeomorphisms of `E` over `B`,
viewed as a subgroup of the homeomorphism group `E ≃ₜ E`. This is the first algebraic
piece needed by the universal-covers roadmap Stage 0.4: for a covering projection `p`, the
subgroup `Deck p` will be the deck transformation group.

The action of `Deck p` on the total space is inherited from the ambient homeomorphism
group. Each deck transformation preserves `p`, hence preserves every fibre of `p`.

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
  exact mapsTo_fiber (φ⁻¹ : Deck p) b

/-- A deck transformation restricts to an equivalence of every fibre of the projection. -/
def fiberEquiv (φ : Deck p) (b : B) : p ⁻¹' {b} ≃ p ⁻¹' {b} where
  toFun e := ⟨φ.1 e.1, mapsTo_fiber φ b e.2⟩
  invFun e := ⟨φ.1.symm e.1, mapsTo_fiber_symm φ b e.2⟩
  left_inv e := by
    ext
    simp
  right_inv e := by
    ext
    simp

/-- On points, the fibre equivalence induced by a deck transformation is just evaluation of
that transformation. -/
@[simp]
lemma fiberEquiv_apply (φ : Deck p) (b : B) (e : p ⁻¹' {b}) :
    (fiberEquiv φ b e : E) = φ.1 e.1 :=
  rfl

/-- On points, the inverse fibre equivalence induced by a deck transformation is evaluation
of the inverse homeomorphism. -/
@[simp]
lemma fiberEquiv_symm_apply (φ : Deck p) (b : B) (e : p ⁻¹' {b}) :
    ((fiberEquiv φ b).symm e : E) = φ.1.symm e.1 :=
  rfl

/-- Deck transformations act on the total space by evaluation of their underlying
homeomorphisms. -/
instance instSMul : SMul (Deck p) E where
  smul φ e := φ.1 e

@[simp]
lemma smul_eq_apply (φ : Deck p) (e : E) : φ • e = φ.1 e :=
  rfl

instance instMulAction : MulAction (Deck p) E where
  one_smul e := by
    simp [smul_eq_apply]
  mul_smul φ ψ e := by
    simp [smul_eq_apply]

/-- The action of deck transformations preserves the projection. -/
lemma proj_smul (φ : Deck p) (e : E) : p (φ • e) = p e :=
  map_proj φ e

/-- If two deck transformations have the same action on every point, they are equal. -/
instance instFaithfulSMul : FaithfulSMul (Deck p) E where
  eq_of_smul_eq_smul hφψ := by
    ext e
    simpa only [smul_eq_apply] using hφψ e

/-- Each deck transformation acts continuously on the total space. -/
instance instContinuousConstSMul : ContinuousConstSMul (Deck p) E where
  continuous_const_smul φ := by
    simpa only [smul_eq_apply] using φ.1.continuous

end Deck

end TauCeti
