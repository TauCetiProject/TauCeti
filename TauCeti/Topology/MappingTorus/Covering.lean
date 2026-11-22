/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MappingTorus.Basic
public import Mathlib.Topology.Covering.Quotient
import TauCeti.Topology.Homeomorph.Semiconj

/-!
# The infinite cyclic cover of a mapping torus

The mapping torus of a homeomorphism `φ : F ≃ₜ F` is the orbit space of the action of `ℤ` on the
cylinder `F × ℝ` by `n +ᵥ (x, t) = (φⁿ x, t + n)`.  This action is free and every point has a
neighbourhood, a slab of height less than one, whose translates are pairwise disjoint.  So the
quotient map `F × ℝ → MappingTorus φ` is a quotient covering map for this `ℤ`-action
(`TauCeti.MappingTorus.isAddQuotientCoveringMap_coverMap`): it is the infinite cyclic cover of the
mapping torus.  (When `F` is disconnected the covering may have further deck transformations; only
the `ℤ`-action is used here.)

The deck transformation generating the action is `TauCeti.MappingTorus.deck φ`,
`(x, t) ↦ (φ x, t + 1)`.  It lies over the monodromy `φ` under the projection `F × ℝ → F`, which
is a homotopy equivalence, inverse to the zero section
(`ContinuousMap.HomotopyEquiv.prodZeroSection`).  This is the starting point of Milnor's
derivation of the Wang sequence from the infinite cyclic cover.

A continuous map of cylinders `Φ : F × ℝ → G × ℝ` intertwining the deck transformations of `φ`
and `ψ` descends to a map of mapping tori (`TauCeti.MappingTorus.descend`).  The maps
`TauCeti.MappingTorus.map` induced by maps of fibres intertwining the monodromies are the case
`Φ = g × 𝟙ℝ` (`TauCeti.MappingTorus.descend_prodMap`), but `Φ` need not preserve the product
structure: a family of sections of the mapping torus, read on the cylinder, is such a map out of
the cylinder of a product with the circle.

## References

* J. Milnor, *Infinite cyclic coverings*, Conference on the Topology of Manifolds (1968),
  Section 1.
* A. Hatcher, *Algebraic Topology*, Section 2.2 (the mapping-torus construction).
-/

public section

noncomputable section

open Set Topology ContinuousMap

namespace TauCeti.MappingTorus

variable {F : Type*} [TopologicalSpace F] (φ : F ≃ₜ F)

/-- The quotient map from the cylinder `F × ℝ` onto the mapping torus, as a continuous map. -/
def coverMap : C(F × ℝ, MappingTorus φ) :=
  ⟨fun p ↦ mk φ p.1 p.2, continuous_mk φ⟩

@[simp]
lemma coverMap_apply (p : F × ℝ) : coverMap φ p = mk φ p.1 p.2 :=
  (rfl)

/-- **The mapping torus is the quotient of the cylinder by a covering action of `ℤ`.**  The
quotient map `F × ℝ → MappingTorus φ` is a quotient covering map for the action
`n +ᵥ (x, t) = (φⁿ x, t + n)` of `ℤ`. -/
theorem isAddQuotientCoveringMap_coverMap :
    letI := action φ
    IsAddQuotientCoveringMap (coverMap φ) ℤ := by
  let := action φ
  refine
    { toIsQuotientMap := (isOpenMap_mk φ).isQuotientMap (continuous_mk φ) (mk_surjective φ)
      continuous_const_vadd n := by
        simp only [action_vadd]
        exact ((φ ^ n).continuous.comp continuous_fst).prodMk
          (continuous_snd.add continuous_const)
      apply_eq_iff_mem_orbit {p q} := by
        simp only [coverMap_apply, mk_eq_iff, AddAction.mem_orbit_iff, action_vadd, Prod.ext_iff]
      disjoint p := ?_ }
  -- A slab of height one around `p` meets its translate by `n` only for `n = 0`.
  refine ⟨univ ×ˢ Ioo (p.2 - 2⁻¹) (p.2 + 2⁻¹),
    prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds (by linarith) (by linarith)), fun n hn ↦ ?_⟩
  obtain ⟨_, ⟨q, hq, rfl⟩, hnq⟩ := hn
  simp only [action_vadd, mem_prod, mem_univ, mem_Ioo, true_and] at hq hnq
  have h1 : (n : ℝ) < 1 := by linarith
  have h2 : (-1 : ℝ) < n := by linarith
  have : n < 1 := by exact_mod_cast h1
  have : -1 < n := by exact_mod_cast h2
  omega

/-- The deck transformation `(x, t) ↦ (φ x, t + 1)` of the cylinder over the mapping torus: the
action of the generator `1 : ℤ`. -/
def deck : F × ℝ ≃ₜ F × ℝ :=
  φ.prodCongr (Homeomorph.addRight 1)

@[simp]
lemma deck_apply (p : F × ℝ) : deck φ p = (φ p.1, p.2 + 1) :=
  (rfl)

/-- The deck transformation is the action of `1 : ℤ`. -/
lemma deck_eq_vadd (p : F × ℝ) :
    letI := action φ
    deck φ p = (1 : ℤ) +ᵥ p := by
  simp [action_vadd]

/-- The deck transformation covers the identity of the mapping torus. -/
lemma coverMap_deck (p : F × ℝ) : coverMap φ (deck φ p) = coverMap φ p := by
  simp

/-- The `n`-th power of the deck transformation is the action of `n : ℤ`,
`(x, t) ↦ (φⁿ x, t + n)`. -/
lemma deck_zpow_apply (n : ℤ) (p : F × ℝ) : (deck φ ^ n) p = ((φ ^ n) p.1, p.2 + n) := by
  induction n using Int.induction_on generalizing p with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, Homeomorph.mul_apply, ih, deck_apply, zpow_add_one, Homeomorph.mul_apply]
    push_cast
    ring_nf
  | pred n ih =>
    -- the action of `-n - 1` is that of `-1` followed by that of `-n`
    have h₁ : (deck φ ^ (-1 : ℤ)) p = ((φ ^ (-1 : ℤ)) p.1, p.2 - 1) := by
      rw [zpow_neg_one, zpow_neg_one]
      exact (deck φ).symm_apply_eq.2 (by simp)
    rw [sub_eq_add_neg, zpow_add, Homeomorph.mul_apply, h₁, ih, zpow_add, Homeomorph.mul_apply]
    push_cast
    ring_nf

section Descend

variable {G : Type*} [TopologicalSpace G] (ψ : G ≃ₜ G)

/-- **A map of cylinders intertwining the deck transformations descends to the mapping tori.**
For `Φ : F × ℝ → G × ℝ` with `Φ ∘ deck φ = deck ψ ∘ Φ`, the map `mk φ x t ↦ mk ψ (Φ (x, t))`. -/
def descend (Φ : C(F × ℝ, G × ℝ)) (hΦ : Function.Semiconj Φ (deck φ) (deck ψ)) :
    C(MappingTorus φ, MappingTorus ψ) where
  toFun := lift φ (fun p ↦ coverMap ψ (Φ p)) fun n x t ↦ by
    have h := hΦ.homeomorph_zpow_right n (x, t)
    rw [deck_zpow_apply, deck_zpow_apply] at h
    rw [h, coverMap_apply, coverMap_apply, mk_vadd]
  continuous_toFun := continuous_lift φ _ ((coverMap ψ).continuous.comp Φ.continuous)

variable {ψ}

/-- The map descended from `Φ` sends `mk φ x t` to the image of `Φ (x, t)`. -/
@[simp]
lemma descend_mk (Φ : C(F × ℝ, G × ℝ)) (hΦ : Function.Semiconj Φ (deck φ) (deck ψ)) (x : F)
    (t : ℝ) : descend φ ψ Φ hΦ (mk φ x t) = mk ψ (Φ (x, t)).1 (Φ (x, t)).2 :=
  lift_mk φ _ _ x t

/-- The map descended from `Φ` lifts to `Φ` through the covering maps. -/
lemma descend_comp_coverMap (Φ : C(F × ℝ, G × ℝ)) (hΦ : Function.Semiconj Φ (deck φ) (deck ψ)) :
    (descend φ ψ Φ hΦ).comp (coverMap φ) = (coverMap ψ).comp Φ := by
  ext p
  exact descend_mk φ Φ hΦ p.1 p.2

/-- A map of fibres intertwining the monodromies gives a map of cylinders intertwining the deck
transformations. -/
lemma semiconj_prodMap_deck {g : C(F, G)} (h : Function.Semiconj g φ ψ) :
    Function.Semiconj (g.prodMap (ContinuousMap.id ℝ)) (deck φ) (deck ψ) := fun p ↦ by
  simp [h.eq p.1]

/-- The map of mapping tori induced by a map of fibres intertwining the monodromies is the map
descended from its product with the identity of `ℝ`. -/
lemma descend_prodMap {g : C(F, G)} (h : Function.Semiconj g φ ψ) :
    descend φ ψ (g.prodMap (ContinuousMap.id ℝ)) (semiconj_prodMap_deck φ h) = map φ ψ g h := by
  ext z
  obtain ⟨⟨x, t⟩, rfl⟩ := mk_surjective φ z
  exact (descend_mk φ _ _ x t).trans (map_mk φ ψ g h x t).symm

end Descend

end TauCeti.MappingTorus
