/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Filtration

/-!
# Consequences of Krull's intersection theorem

For a finite module over a noetherian commutative ring:
* the intersection of all positive powers of all maximal ideals acting on the module is zero
  (`Ideal.iInf_isMaximal_pow_smul_eq_bot`), where the quantifier over all maximal ideals is
  essential because the powers of one maximal ideal need not separate a nonlocal ring;
* every submodule `N` is closed in the `I`-adic topology for any ideal `I` contained in the
  Jacobson radical (`Ideal.iInf_sup_pow_smul_eq_of_le_jacobson`), and in particular every ideal `J`
  satisfies `⨅ n, J ⊔ I ^ n = J` (`Ideal.iInf_sup_pow_eq_of_le_jacobson`).

The proofs use Mathlib's Krull intersection theorems `Ideal.mem_iInf_smul_pow_eq_bot_iff` and
`Ideal.iInf_pow_smul_eq_bot_of_le_jacobson`.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 8.10.
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

/-- Every submodule `N` of a finite module over a noetherian ring `R` is closed in the `I`-adic
topology for any ideal `I ≤ Ring.jacobson R`: `⨅ n, N ⊔ I ^ n • ⊤ = N`. -/
theorem iInf_sup_pow_smul_eq_of_le_jacobson (I : Ideal R) (hI : I ≤ Ring.jacobson R)
    (N : Submodule R M) :
    (⨅ n : ℕ, N ⊔ I ^ n • ⊤) = N := by
  refine le_antisymm (fun x hx ↦ ?_) (le_iInf fun _ ↦ le_sup_left)
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mem_bot (R := R),
    ← I.iInf_pow_smul_eq_bot_of_le_jacobson (M := M ⧸ N) hI, Submodule.mem_iInf]
  intro n
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp ((Submodule.mem_iInf _).mp hx n)
  rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero N).mpr hu, zero_add, ← N.mkQ_apply]
  exact Submodule.smul_top_le_comap_smul_top (I ^ n) N.mkQ hv

/-- Every ideal `J` of a noetherian ring `R` is closed in the `I`-adic topology for any ideal
`I ≤ Ring.jacobson R`: `⨅ n, J ⊔ I ^ n = J`. -/
theorem iInf_sup_pow_eq_of_le_jacobson (I : Ideal R) (hI : I ≤ Ring.jacobson R) (J : Ideal R) :
    (⨅ n : ℕ, J ⊔ I ^ n) = J := by
  simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using
    I.iInf_sup_pow_smul_eq_of_le_jacobson (M := R) hI J

end Ideal
