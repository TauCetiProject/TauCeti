/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Filtration

/-!
# Separation by powers of all maximal ideals

For a finite module over a noetherian commutative ring, the intersection of all positive powers
of all maximal ideals acting on the module is zero. The quantifier over all maximal ideals is
essential: the powers of one maximal ideal need not separate a nonlocal ring.

The proof uses Mathlib's Krull intersection criterion
`Ideal.mem_iInf_smul_pow_eq_bot_iff` at a maximal ideal containing the annihilator of an element.
-/

public section

namespace Ideal

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]

/-- Positive powers of all maximal ideals separate a finite module over a noetherian ring. -/
theorem iInf_isMaximal_pow_smul_eq_bot :
    (⨅ (m : Ideal R) (_ : m.IsMaximal) (n : ℕ) (_ : 0 < n),
      m ^ n • ⊤ : Submodule R M) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  by_contra hzero
  have hx0 : x ≠ 0 := by simpa using hzero
  obtain ⟨m, hm, hle⟩ := (Submodule.span R {x}).annihilator.exists_le_maximal (by
    simpa [Submodule.annihilator_eq_top_iff, Submodule.span_singleton_eq_bot] using hx0)
  have hxpow : x ∈ (⨅ n : ℕ, m ^ n • ⊤ : Submodule R M) := by
    simp only [Submodule.mem_iInf] at hx ⊢
    intro n
    rcases n with _ | n
    · simp
    · exact hx m hm (n + 1) (Nat.succ_pos n)
  obtain ⟨r, hr⟩ := (m.mem_iInf_smul_pow_eq_bot_iff x).mp hxpow
  have hsub : 1 - (r : R) ∈ m := hle <|
    (Submodule.mem_annihilator_span_singleton x _).mpr (by simp [sub_smul, hr])
  exact hm.ne_top ((Ideal.eq_top_iff_one m).mpr (by simpa using m.add_mem hsub r.property))

/-- Positive powers of all maximal ideals of a noetherian ring have zero intersection. -/
theorem iInf_isMaximal_pow_eq_bot :
    (⨅ (m : Ideal R) (_ : m.IsMaximal) (n : ℕ) (_ : 0 < n), m ^ n) = ⊥ := by
  simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using
    (iInf_isMaximal_pow_smul_eq_bot (R := R) (M := R))

end Ideal
