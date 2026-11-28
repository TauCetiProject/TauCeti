/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Cocycle.GroupAlgebra
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Cocycle.Ribet

/-!
# Character cocycles in Ribet's method

A character cocycle is a scalar Ribet cocycle with one additional constraint: if it vanishes at
`γ`, its value at `a` is invariant under the character action. This is a condition on individual
cocycles; in a length argument it can be imposed on every member of a chosen submodule.

If the character is trivial at `γ`, the group algebra relation coming from the normalizer has
cocycle value `(χ(g) - 1) • (r • c(γ) + c(a))` at a left multiple by `g - 1`. In particular,
cocycles satisfying these relations satisfy the conditional constraint. The intended coefficient
module is often a cyclic quotient of the base ring, but neither the formula nor the implication
requires cyclicity.

The condition and the use of normalizer relations follow `New.Selmer.IsCharacterCocycle` and
`New.Selmer.nonempty_characterRows` in `New/Congruences/FirstOrder/FittingBlock.lean` and
`New/Congruences/FirstOrder/RibetMatrices.lean` of [grh-lean](https://github.com/lsernau/grh-lean),
revision `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open MonoidAlgebra
open scoped MonoidAlgebra

namespace TauCeti

variable {O G M V : Type*} [CommRing O] [Monoid G] [AddCommMonoid M] [Module O M]
  [AddCommGroup V] [Module O V]

/-- A scalar Ribet cocycle vanishing on `T` is a character cocycle for `γ, a` if its
value at `a` is fixed by the character whenever its value at `γ` vanishes. -/
def IsRibetCharacterCocycle (z : G → M) (χ : G →* O) (T : Set G) (γ a : G) (c : G → V) : Prop :=
  c ∈ ribetCocycles O V z (χ : G → O) T ∧ (c γ = 0 → ∀ g, (χ g - 1) • c a = 0)

/-- The Ribet condition and the conditional invariance characterize character cocycles. -/
theorem isRibetCharacterCocycle_iff {z : G → M} {χ : G →* O} {T : Set G} {γ a : G} {c : G → V} :
    IsRibetCharacterCocycle z χ T γ a c ↔
      c ∈ ribetCocycles O V z (χ : G → O) T ∧ (c γ = 0 → ∀ g, (χ g - 1) • c a = 0) :=
  (Iff.rfl)

variable {z : G → M} {χ : G →* O} {T : Set G} {γ a : G} {c : G → V}

/-- A character cocycle is a Ribet cocycle. -/
theorem IsRibetCharacterCocycle.mem_ribetCocycles (hc : IsRibetCharacterCocycle z χ T γ a c) :
    c ∈ ribetCocycles O V z (χ : G → O) T :=
  (isRibetCharacterCocycle_iff.mp hc).1

/-- If a character cocycle vanishes at `γ`, its value at `a` is fixed by the character. -/
theorem IsRibetCharacterCocycle.sub_one_smul_eq_zero (hc : IsRibetCharacterCocycle z χ T γ a c)
    (hγ : c γ = 0) (g : G) : (χ g - 1) • c a = 0 :=
  (isRibetCharacterCocycle_iff.mp hc).2 hγ g

/-- The linear extension of a scalar cocycle evaluates the normalizer relation at `g` by
multiplying the indicated combination of its values at `γ` and `a` by `χ(g) - 1`. -/
theorem constr_mul_normalizer_of_cocycle {χ : G →* O} {c : G → V}
    (hc : ∀ g h, c (g * h) = c g + χ g • c h) (γ a g : G) (r : O) :
    let n : O[G] := r • (of O G γ - 1)
    (basis G O).constr O c ((of O G g - 1) * (n + (1 - n) * (of O G a - 1))) =
      (χ g - 1) • (r • c γ + (1 - r * (χ γ - 1)) • c a) := by
  intro n
  let D := (basis G O).constr O c
  have hD (g : G) : D (of O G g) = c g := by
    rw [of_apply, ← basis_apply, Module.Basis.constr_basis]
  have hzero : c 1 = 0 := by simpa using hc 1 1
  have hD₁ : D 1 = 0 := by simpa only [map_one, hzero] using hD (1 : G)
  have haug (g : G) : augmentation O G (of O G g - 1) = 0 := by simp [of_apply]
  have hDn : D n = r • c γ := by simp only [n, map_smul, map_sub, hD, hD₁, sub_zero]
  have hχn : lift O O G χ n = r * (χ γ - 1) := by simp [n]
  have htail : D ((1 - n) * (of O G a - 1)) = (1 - r * (χ γ - 1)) • c a := by
    rw [constr_mul_of_cocycle χ hc]
    simp only [haug, zero_smul, zero_add, map_sub, map_one, hχn]
    rw [hD a, hD₁, sub_zero]
  have haug' : augmentation O G (n + (1 - n) * (of O G a - 1)) = 0 := by
    simp [n]
  rw [constr_mul_of_cocycle χ hc, haug', zero_smul, zero_add, map_sub, lift_of, map_one]
  exact congrArg ((χ g - 1) • ·) ((D.map_add _ _).trans (by rw [hDn, htail]))

/-- A Ribet cocycle killed by all the normalizer relations satisfies the conditional
invariance required of a character cocycle. -/
theorem isRibetCharacterCocycle_of_normalizer
    (hc : c ∈ ribetCocycles O V z (χ : G → O) T) (hγ : χ γ = 1) (r : O)
    (h : let n : O[G] := r • (of O G γ - 1)
      ∀ g, (basis G O).constr O c ((of O G g - 1) * (n + (1 - n) * (of O G a - 1))) = 0) :
    IsRibetCharacterCocycle z χ T γ a c := by
  refine isRibetCharacterCocycle_iff.mpr ⟨hc, fun hcγ g ↦ ?_⟩
  simpa [hcγ, hγ] using
    (constr_mul_normalizer_of_cocycle (apply_mul_of_mem_ribetCocycles hc) γ a g r).symm.trans
      (h g)

end TauCeti
