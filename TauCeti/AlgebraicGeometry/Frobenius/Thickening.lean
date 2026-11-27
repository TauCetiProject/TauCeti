/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Frobenius.Iterate

/-!
# Frobenius through a square-zero quotient

Positive iterates of the absolute Frobenius of an affine scheme factor through any
square-zero closed subscheme. This lets one evaluate Frobenius on a lifted point
using just its reduction.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {p : ℕ} [Fact p.Prime]

/-- Absolute Frobenius, iterated a positive number of times, factors through the inclusion
of the spectrum of a square-zero quotient. -/
theorem exists_comp_SpecMap_quotient_mk_eq_iterateFrobenius {B : CommRingCat.{u}}
    (hB : (p : Γ(Spec B, ⊤)) = 0) (I : Ideal B) (hI : I ^ 2 = ⊥) {n : ℕ} (hn : 0 < n) :
    ∃ v : Spec B ⟶ Spec (.of (B ⧸ I)),
      v ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
        (Spec B).iterateFrobenius p hB n := by
  have hBp : (p : B) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (ΓSpecIso B).hom hB
  have hpow (b : B) (hb : b ∈ I) : TauCeti.powRingHom B p hBp b = 0 := by
    rw [TauCeti.powRingHom_apply]
    exact Ideal.pow_eq_zero_of_mem hI (Fact.out : p.Prime).two_le hb
  let φ := Ideal.Quotient.lift I (TauCeti.powRingHom B p hBp) hpow
  have hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = (Spec B).frobenius p hB := by
    rw [← Spec_map_powRingHom B hBp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Ideal.Quotient.lift_comp_mk]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact ⟨_ ≫ Spec.map (CommRingCat.ofHom φ), by
    rw [Category.assoc, hφ, iterateFrobenius_succ]⟩

end AlgebraicGeometry.Scheme
