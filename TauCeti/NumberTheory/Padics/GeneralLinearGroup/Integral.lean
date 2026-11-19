/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `ℤ_[p]`, `ℚ_[p]` and the inclusion `PadicInt.Coe.ringHom` occur in the statements below.
public import Mathlib.NumberTheory.Padics.PadicIntegers
-- `Matrix.GeneralLinearGroup.map` and the `GL` notation occur in the statements below.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- Non-public: injectivity of `Matrix.GeneralLinearGroup.map` along an injective ring hom, used only
-- to build `TauCeti.GLPadicInt.mulEquiv`.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# The integral subgroup `GLₙ(ℤ_p)` of `GLₙ(ℚ_p)`

The group `GLₙ(ℤ_p)` of invertible matrices over the `p`-adic integers is a subgroup of
`GLₙ(ℚ_p)` through the entrywise inclusion `ℤ_p ⊆ ℚ_p`. For `n = 2` it is the maximal compact
subgroup `K = GL₂(ℤ_p)` of `GL₂(ℚ_p)`, whose product `KZ` with the centre is the stabiliser of
the standard vertex of the Bruhat–Tits tree, and from which the representations
`c-Ind_{KZ}^G σ` of `GL₂(ℚ_p)` are compactly induced.

The subgroup is defined as the image of `Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom`; the
main result describes it intrinsically. An invertible matrix over `ℚ_p` comes from `GLₙ(ℤ_p)`
exactly when all of its entries have norm at most `1` and its determinant has norm `1`. Integrality
of the entries alone is not enough: `!![p, 0; 0, 1]` has integral entries, but its inverse does not.

## Main definitions

* `TauCeti.GLPadicInt n p`: the subgroup `GLₙ(ℤ_p)` of `GL n ℚ_[p]`.
* `TauCeti.GLPadicInt.mulEquiv`: the isomorphism `GL n ℤ_[p] ≃* GLPadicInt n p`.

## Main results

* `TauCeti.GLPadicInt.mem_iff`: `g ∈ GLₙ(ℤ_p)` if and only if every entry of `g` has norm at most
  `1` and `‖det g‖ = 1`.
-/

public section

namespace TauCeti

open Matrix

variable (n : Type*) [Fintype n] [DecidableEq n] (p : ℕ) [Fact p.Prime]

/-- The subgroup `GLₙ(ℤ_p)` of `GLₙ(ℚ_p)`: the image of the invertible matrices over `ℤ_p` under
the entrywise inclusion `ℤ_p ⊆ ℚ_p`. -/
noncomputable def GLPadicInt : Subgroup (GL n ℚ_[p]) :=
  (GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p))).range

namespace GLPadicInt

variable {n p}

/-- Membership in `GLₙ(ℤ_p)` is coming from an invertible matrix over `ℤ_p`. -/
theorem mem_iff_exists_map {g : GL n ℚ_[p]} :
    g ∈ GLPadicInt n p ↔ ∃ γ : GL n ℤ_[p], GeneralLinearGroup.map PadicInt.Coe.ringHom γ = g :=
  Iff.rfl

/-- An invertible matrix over `ℤ_p` lies in `GLₙ(ℤ_p)`. -/
theorem map_mem (γ : GL n ℤ_[p]) :
    GeneralLinearGroup.map PadicInt.Coe.ringHom γ ∈ GLPadicInt n p :=
  ⟨γ, rfl⟩

/-- **The integral subgroup, intrinsically.** An invertible matrix over `ℚ_p` lies in `GLₙ(ℤ_p)`
exactly when all of its entries have norm at most `1` and its determinant has norm `1`. -/
theorem mem_iff {g : GL n ℚ_[p]} :
    g ∈ GLPadicInt n p ↔
      (∀ i j, ‖(g : Matrix n n ℚ_[p]) i j‖ ≤ 1) ∧ ‖(g : Matrix n n ℚ_[p]).det‖ = 1 := by
  constructor
  · rintro ⟨γ, rfl⟩
    refine ⟨fun i j ↦ ?_, ?_⟩
    · rw [GeneralLinearGroup.map_apply, PadicInt.Coe.ringHom_apply, PadicInt.norm_coe]
      exact PadicInt.norm_le_one _
    · rw [← GeneralLinearGroup.val_det_apply, GeneralLinearGroup.map_det]
      simpa [PadicInt.norm_coe] using PadicInt.isUnit_iff.mp (GeneralLinearGroup.det γ).isUnit
  · rintro ⟨h, hdet⟩
    -- The entries of `g` lift to `ℤ_p`, and the lifted matrix has a unit determinant.
    let A : Matrix n n ℤ_[p] := Matrix.of fun i j ↦ Padic.lift ((g : Matrix n n ℚ_[p]) i j) (h i j)
    have hA : PadicInt.Coe.ringHom.mapMatrix A = g := by
      ext i j
      simp [A]
    have hu : IsUnit A.det := by
      rw [PadicInt.isUnit_iff, ← PadicInt.norm_coe, ← PadicInt.Coe.ringHom_apply,
        RingHom.map_det, hA, hdet]
    refine ⟨GeneralLinearGroup.mk'' A hu, ?_⟩
    ext i j
    simp [A]

variable (n p) in
/-- `GLₙ(ℤ_p)` is isomorphic to its image in `GLₙ(ℚ_p)`: the entrywise inclusion `ℤ_p ⊆ ℚ_p` is
injective. -/
noncomputable def mulEquiv : GL n ℤ_[p] ≃* GLPadicInt n p :=
  MonoidHom.ofInjective (GeneralLinearGroup.map_injective (f := PadicInt.Coe.ringHom (p := p))
    Subtype.val_injective)

@[simp]
theorem coe_mulEquiv_apply (γ : GL n ℤ_[p]) :
    ((mulEquiv n p γ : GLPadicInt n p) : GL n ℚ_[p]) =
      GeneralLinearGroup.map PadicInt.Coe.ringHom γ :=
  (rfl)

end GLPadicInt

end TauCeti
