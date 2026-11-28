/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Solvable

/-!
# Restrictions of Lie algebra equivalences to the derived series

Every Lie algebra equivalence `e : L ≃ₗ⁅R⁆ M` carries each term of the derived series onto the
corresponding term of `M` (`LieEquiv.map_derivedSeries`), inducing `LieEquiv.restrictDerivedSeries`.

## Main definitions and results

* `LieEquiv.map_derivedSeries`, `LieEquiv.restrictDerivedSeries`,
  `LieEquiv.restrictDerivedSeries_refl`, `LieEquiv.restrictDerivedSeries_symm`,
  `LieEquiv.restrictDerivedSeries_trans`.
-/

public section

open LieAlgebra

namespace LieEquiv

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

/-- Every Lie algebra equivalence maps each term of the derived series onto the corresponding term
of the target. -/
theorem map_derivedSeries (e : L ≃ₗ⁅R⁆ M) (k : ℕ) :
    (derivedSeries R L k).toLieSubalgebra.map e.toLieHom =
      (derivedSeries R M k).toLieSubalgebra := by
  ext y
  rw [LieIdeal.mem_toLieSubalgebra,
    ← LieIdeal.derivedSeries_map_eq (f := e.toLieHom) k e.surjective, LieSubalgebra.mem_map]
  exact ⟨fun ⟨x, hx, hxy⟩ ↦ hxy ▸ LieIdeal.mem_map hx,
    fun hy ↦ let ⟨x, hx⟩ := LieIdeal.mem_map_of_surjective e.surjective hy; ⟨x, x.property, hx⟩⟩

/-- Restriction of a Lie algebra equivalence to the `k`-th term of the derived series. -/
def restrictDerivedSeries (e : L ≃ₗ⁅R⁆ M) (k : ℕ) :
    derivedSeries R L k ≃ₗ⁅R⁆ derivedSeries R M k :=
  e.ofSubalgebras (derivedSeries R L k).toLieSubalgebra (derivedSeries R M k).toLieSubalgebra
    (e.map_derivedSeries k)

@[simp, grind =]
theorem coe_restrictDerivedSeries (e : L ≃ₗ⁅R⁆ M) (k : ℕ) (x : derivedSeries R L k) :
    (e.restrictDerivedSeries k x : M) = e x :=
  e.ofSubalgebras_apply _ _ (e.map_derivedSeries k) x

@[simp, grind =]
theorem coe_restrictDerivedSeries_symm (e : L ≃ₗ⁅R⁆ M) (k : ℕ) (y : derivedSeries R M k) :
    ((e.restrictDerivedSeries k).symm y : L) = e.symm y :=
  e.ofSubalgebras_symm_apply _ _ (e.map_derivedSeries k) y

/-- Restricting the identity equivalence to a derived-series term gives the identity. -/
@[simp]
theorem restrictDerivedSeries_refl (k : ℕ) :
    (LieEquiv.refl : L ≃ₗ⁅R⁆ L).restrictDerivedSeries k = LieEquiv.refl := by
  ext x; simp

/-- Restricting the inverse equivalence to a derived-series term equals the inverse of the
restriction. -/
@[simp]
theorem restrictDerivedSeries_symm (e : L ≃ₗ⁅R⁆ M) (k : ℕ) :
    e.symm.restrictDerivedSeries k = (e.restrictDerivedSeries k).symm := by
  ext x; simp

/-- Restricting a composite equivalence to a term of the derived series composes the
restrictions. -/
@[simp]
theorem restrictDerivedSeries_trans {N : Type*} [LieRing N] [LieAlgebra R N]
    (e₁ : L ≃ₗ⁅R⁆ M) (e₂ : M ≃ₗ⁅R⁆ N) (k : ℕ) :
    (e₁.trans e₂).restrictDerivedSeries k =
      (e₁.restrictDerivedSeries k).trans (e₂.restrictDerivedSeries k) := by
  ext x; simp

end LieEquiv
