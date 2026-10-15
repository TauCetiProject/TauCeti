/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic

/-!
# Equality of degree-zero localization maps

For a degree-one denominator, equality of degree-zero localization maps is equivalent
to unit rescaling of homogeneous coordinates. This is the algebraic criterion for
comparing scheme-valued points in a standard projective chart, including over rings
with nilpotents.
-/

public section

namespace HomogeneousLocalization.Away

variable {A B σ : Type*} [CommRing A] [CommRing B] [SetLike σ A]
  [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- On a degree-one chart, equal degree-zero localization maps are precisely unit
rescalings of the homogeneous coordinates. -/
theorem lift_eq_iff_exists_unit (f g : A →+* B) {t : A} (ht : t ∈ 𝒜 1)
    (hf : IsUnit (f t)) (hg : IsUnit (g t)) :
    lift 𝒜 f hf = lift 𝒜 g hg ↔
      ∃ c : Bˣ, ∀ n, ∀ a ∈ 𝒜 n, g a = c ^ n * f a := by
  constructor
  · intro h
    refine ⟨hg.unit * hf.unit⁻¹, fun n a ha ↦ ?_⟩
    have ha' : a ∈ 𝒜 (n • (1 : ℕ)) := by simpa using ha
    have he := RingHom.congr_fun h (Away.mk 𝒜 ht n a ha')
    rw [lift_mk, lift_mk] at he
    rw [Units.eq_mul_inv_iff_mul_eq] at he
    simpa only [mul_pow, Units.val_mul, ← inv_pow, Units.val_pow_eq_pow_val,
      mul_assoc, mul_comm, mul_left_comm] using he.symm
  · rintro ⟨c, hc⟩
    exact (lift_eq_of_forall_mem f g c hc ht hg hf).symm

end HomogeneousLocalization.Away
