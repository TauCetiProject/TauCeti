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
preserves every fibre of `p`. We also package these restricted homeomorphisms as
homomorphisms from `Deck p` to the homeomorphism group of a single fibre, and to the
pointwise product of the homeomorphism groups of all fibres. This records the elementary
but useful fact that a deck transformation is determined by its action on all fibres.

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

/-- A deck transformation maps the preimage of a set in the base onto itself. -/
@[simp]
lemma image_preimage (φ : Deck p) (s : Set B) : φ.1 '' (p ⁻¹' s) = p ⁻¹' s := by
  refine Set.Subset.antisymm ?_ ?_
  · intro e he
    rcases he with ⟨e, he, rfl⟩
    simpa only [Set.mem_preimage, map_proj] using he
  · intro e he
    refine ⟨φ.1.symm e, ?_, Homeomorph.apply_symm_apply φ.1 e⟩
    rw [Set.mem_preimage, ← map_proj φ (φ.1.symm e), Homeomorph.apply_symm_apply]
    exact he

/-- The preimage of the preimage of a set in the base under a deck transformation is itself. -/
@[simp]
lemma preimage_preimage (φ : Deck p) (s : Set B) : φ.1 ⁻¹' (p ⁻¹' s) = p ⁻¹' s := by
  ext e
  simp only [Set.mem_preimage, map_proj]

/-- A deck transformation maps each fibre of the projection onto itself. -/
@[simp]
lemma image_fiber (φ : Deck p) (b : B) : φ.1 '' (p ⁻¹' {b}) = p ⁻¹' {b} := by
  simpa only using image_preimage (p := p) φ ({b} : Set B)

/-- The preimage of a fibre under a deck transformation is that fibre. -/
@[simp]
lemma preimage_fiber (φ : Deck p) (b : B) : φ.1 ⁻¹' (p ⁻¹' {b}) = p ⁻¹' {b} := by
  simpa only using preimage_preimage (p := p) φ ({b} : Set B)

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

/-- The identity deck transformation induces the identity homeomorphism on every fibre. -/
@[simp]
lemma fiberHomeomorph_one (b : B) : fiberHomeomorph (1 : Deck p) b = 1 := by
  ext e
  change (fiberHomeomorph (1 : Deck p) b e : E) = e.1
  simp only [fiberHomeomorph_apply, OneMemClass.coe_one, Homeomorph.one_apply]

/-- The fibre homeomorphism induced by a product of deck transformations is the product of
the induced fibre homeomorphisms. -/
@[simp]
lemma fiberHomeomorph_mul (φ ψ : Deck p) (b : B) :
    fiberHomeomorph (φ * ψ) b = fiberHomeomorph φ b * fiberHomeomorph ψ b := by
  ext e
  change (fiberHomeomorph (φ * ψ) b e : E) = φ.1 (ψ.1 e.1)
  simp only [fiberHomeomorph_apply, Subgroup.coe_mul, Homeomorph.mul_apply]

/-- The induced action of deck transformations on one fibre, as a group homomorphism to the
homeomorphism group of that fibre. -/
def fiberHomeomorphHom (b : B) : Deck p →* (p ⁻¹' {b} ≃ₜ p ⁻¹' {b}) where
  toFun φ := fiberHomeomorph φ b
  map_one' := fiberHomeomorph_one b
  map_mul' φ ψ := fiberHomeomorph_mul φ ψ b

/-- Evaluating `fiberHomeomorphHom` is the same as restricting the deck transformation to
the chosen fibre. -/
@[simp]
lemma fiberHomeomorphHom_apply (b : B) (φ : Deck p) :
    fiberHomeomorphHom (p := p) b φ = fiberHomeomorph φ b :=
  rfl

/-- On points, the fibre action homomorphism is evaluation of the underlying deck
transformation. -/
@[simp]
lemma fiberHomeomorphHom_apply_apply (b : B) (φ : Deck p) (e : p ⁻¹' {b}) :
    (fiberHomeomorphHom (p := p) b φ e : E) = φ.1 e.1 :=
  rfl

/-- The simultaneous action of deck transformations on every fibre, as a group homomorphism
to the pointwise product of the fibre homeomorphism groups. -/
def fiberHomeomorphPiHom : Deck p →* ∀ b : B, p ⁻¹' {b} ≃ₜ p ⁻¹' {b} where
  toFun φ b := fiberHomeomorph φ b
  map_one' := funext fun b => fiberHomeomorph_one b
  map_mul' φ ψ := funext fun b => fiberHomeomorph_mul φ ψ b

/-- Evaluating `fiberHomeomorphPiHom` at a base point is `fiberHomeomorphHom`. -/
@[simp]
lemma fiberHomeomorphPiHom_apply (φ : Deck p) (b : B) :
    fiberHomeomorphPiHom (p := p) φ b = fiberHomeomorph φ b :=
  rfl

/-- On points, the simultaneous fibre action homomorphism is evaluation of the underlying
deck transformation. -/
@[simp]
lemma fiberHomeomorphPiHom_apply_apply (φ : Deck p) (b : B) (e : p ⁻¹' {b}) :
    (fiberHomeomorphPiHom (p := p) φ b e : E) = φ.1 e.1 :=
  rfl

/-- A deck transformation is determined by its induced homeomorphisms on all fibres. -/
lemma fiberHomeomorphPiHom_injective :
    Function.Injective (fiberHomeomorphPiHom (p := p)) := by
  intro φ ψ h
  ext e
  have hb := congrFun h (p e)
  have he := congrArg (fun f : p ⁻¹' {p e} ≃ₜ p ⁻¹' {p e} => (f ⟨e, by simp⟩ : E)) hb
  simpa only [fiberHomeomorphPiHom_apply, fiberHomeomorph_apply] using he

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
