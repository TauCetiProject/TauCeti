/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MappingTorus.Basic
public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Topology.Homotopy.Equiv

/-!
# The infinite cyclic cover of a mapping torus

The mapping torus of a homeomorphism `φ : F ≃ₜ F` is the orbit space of the action of `ℤ` on the
cylinder `F × ℝ` by `n +ᵥ (x, t) = (φⁿ x, t + n)`.  This action is free and every point has a
neighbourhood, a slab of height less than one, whose translates are pairwise disjoint.  So the
quotient map `F × ℝ → MappingTorus φ` is a covering map with deck group `ℤ`
(`TauCeti.MappingTorus.isAddQuotientCoveringMap_coverMap`): it is the infinite cyclic cover of the
mapping torus.

The deck transformation generating the action is `TauCeti.MappingTorus.deck φ`,
`(x, t) ↦ (φ x, t + 1)`.  It lies over the monodromy `φ` under the projection `F × ℝ → F`, which
is a homotopy equivalence (`TauCeti.MappingTorus.cylinderHomotopyEquiv`).  This is the starting
point of Milnor's derivation of the Wang sequence from the infinite cyclic cover.

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
  simpa using mk_vadd φ 1 p.1 p.2

variable (F) in
/-- The projection of the cylinder `F × ℝ` onto `F` is a homotopy equivalence, whose homotopy
inverse is the inclusion at height zero: the cylinder deformation retracts onto `F × {0}` by
scaling the height. -/
def cylinderHomotopyEquiv : F × ℝ ≃ₕ F where
  toFun := .fst
  invFun := ⟨fun x ↦ (x, 0), by fun_prop⟩
  left_inv := ⟨
    { toFun p := (p.2.1, (p.1 : ℝ) * p.2.2)
      continuous_toFun := by fun_prop
      map_zero_left := by simp
      map_one_left := by simp }⟩
  right_inv := ⟨.refl _⟩

@[simp]
lemma cylinderHomotopyEquiv_apply (p : F × ℝ) : cylinderHomotopyEquiv F p = p.1 :=
  (rfl)

@[simp]
lemma cylinderHomotopyEquiv_invFun_apply (x : F) :
    (cylinderHomotopyEquiv F).invFun x = (x, 0) :=
  (rfl)

end TauCeti.MappingTorus
