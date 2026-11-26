/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.Noetherian.Defs

import Mathlib.RingTheory.Filtration
import TauCeti.RingTheory.Ideal.Extended

/-!
# Consequences of Krull's intersection theorem

For a finite module over a noetherian commutative ring:
* the intersection of all positive powers of all maximal ideals acting on the module is zero
  (`Ideal.iInf_isMaximal_pow_smul_eq_bot`), where the quantifier over all maximal ideals is
  essential because the powers of one maximal ideal need not separate a nonlocal ring;
* every submodule `N` is closed in the `I`-adic topology for any ideal `I` contained in the
  Jacobson radical (`Ideal.iInf_sup_pow_smul_eq_of_le_jacobson`), and in particular every ideal `J`
  satisfies `⨅ n, J ⊔ I ^ n = J` (`Ideal.iInf_sup_pow_eq_of_le_jacobson`);
* for an arbitrary ideal `I`, an element `x` lies in the `I`-adic closure `⨅ n, N ⊔ I ^ n • ⊤` of
  a submodule `N` exactly when `(1 - r) • x ∈ N` for some `r ∈ I`
  (`Ideal.mem_iInf_sup_pow_smul_iff`), and likewise for ideals (`Ideal.mem_iInf_sup_pow_iff`).

For an algebra `A` over a noetherian commutative ring `R`, finite as an `R`-module but not
necessarily commutative, the powers of the two-sided ideal of `A` extended from an ideal `I` of
`R` are the modules `I ^ n • A` (`Ideal.pow_smul_top_eq_restrictScalars_map_pow`), so:
* an element of every power of the extended ideal is fixed by multiplication by a scalar in `I`
  (`Ideal.mem_iInf_map_algebraMap_pow_iff`);
* the powers of the extended ideal meet in zero exactly when `1 - r` is left regular in `A` for
  every scalar `r ∈ I` (`Ideal.iInf_map_algebraMap_pow_eq_bot_iff`), for instance when `A` has no
  zero divisors and no scalar in `I` becomes `1`.

The proofs use Mathlib's Krull intersection theorem `Ideal.mem_iInf_smul_pow_eq_bot_iff`.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 8.10.
* G. Hochschild, *An Addition to Ado's Theorem*, Proceedings of the American Mathematical
  Society **17** (1966), 531-533, for the extended-ideal form.
-/

public section

namespace Ideal

section Module

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

/-- **The `I`-adic closure of a submodule.** For a finite module `M` over a noetherian ring, `x`
lies in every `N ⊔ I ^ n • ⊤` exactly when `(1 - r) • x ∈ N` for some `r ∈ I`. -/
theorem mem_iInf_sup_pow_smul_iff (I : Ideal R) (N : Submodule R M) (x : M) :
    x ∈ ⨅ n : ℕ, N ⊔ I ^ n • ⊤ ↔ ∃ r ∈ I, (1 - r) • x ∈ N := by
  refine ⟨fun hx ↦ ?_, fun ⟨r, hr, hx⟩ ↦ (Submodule.mem_iInf _).mpr fun n ↦ ?_⟩
  · -- The class of `x` in `M ⧸ N` lies in every `I ^ n • (M ⧸ N)`; apply Krull's theorem there.
    have hmem : (Submodule.Quotient.mk x : M ⧸ N) ∈ (⨅ n : ℕ, I ^ n • ⊤ : Submodule R (M ⧸ N)) := by
      refine (Submodule.mem_iInf _).mpr fun n ↦ ?_
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp ((Submodule.mem_iInf _).mp hx n)
      rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero N).mpr hu, zero_add,
        ← N.mkQ_apply]
      exact Submodule.smul_top_le_comap_smul_top (I ^ n) N.mkQ hv
    obtain ⟨⟨r, hr⟩, hrx⟩ := (I.mem_iInf_smul_pow_eq_bot_iff _).mp hmem
    refine ⟨r, hr, (Submodule.Quotient.mk_eq_zero N).mp ?_⟩
    rw [sub_smul, one_smul, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, hrx, sub_self]
  · -- `x = (1 + r + ⋯ + r ^ (n - 1)) • (1 - r) • x + r ^ n • x`.
    have hx' : x = (∑ i ∈ Finset.range n, r ^ i) • ((1 - r) • x) + r ^ n • x := by
      rw [smul_smul, geom_sum_mul_neg, sub_smul, one_smul, sub_add_cancel]
    rw [hx']
    exact add_mem (Submodule.mem_sup_left (N.smul_mem _ hx))
      (Submodule.mem_sup_right (Submodule.smul_mem_smul (pow_mem_pow hr n) Submodule.mem_top))

/-- Every submodule `N` of a finite module over a noetherian ring `R` is closed in the `I`-adic
topology for any ideal `I ≤ Ring.jacobson R`: `⨅ n, N ⊔ I ^ n • ⊤ = N`. -/
theorem iInf_sup_pow_smul_eq_of_le_jacobson (I : Ideal R) (hI : I ≤ Ring.jacobson R)
    (N : Submodule R M) :
    (⨅ n : ℕ, N ⊔ I ^ n • ⊤) = N := by
  refine le_antisymm (fun x hx ↦ ?_) (le_iInf fun _ ↦ le_sup_left)
  obtain ⟨r, hr, hrx⟩ := (I.mem_iInf_sup_pow_smul_iff N x).mp hx
  -- `1 - r` is a unit because `r` lies in the Jacobson radical.
  have hu : IsUnit (1 - r) := by
    simpa [sub_eq_neg_add] using Ring.mem_jacobson_iff.mp (neg_mem (hI hr)) 1
  exact (N.smul_mem_iff_of_isUnit hu).mp hrx

/-- Every ideal `J` of a noetherian ring `R` is closed in the `I`-adic topology for any ideal
`I ≤ Ring.jacobson R`: `⨅ n, J ⊔ I ^ n = J`. -/
theorem iInf_sup_pow_eq_of_le_jacobson (I : Ideal R) (hI : I ≤ Ring.jacobson R) (J : Ideal R) :
    (⨅ n : ℕ, J ⊔ I ^ n) = J := by
  simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using
    I.iInf_sup_pow_smul_eq_of_le_jacobson (M := R) hI J

/-- **The `I`-adic closure of an ideal.** In a noetherian ring, `x` lies in every `J ⊔ I ^ n`
exactly when `(1 - r) * x ∈ J` for some `r ∈ I`. -/
theorem mem_iInf_sup_pow_iff (I J : Ideal R) (x : R) :
    x ∈ ⨅ n : ℕ, J ⊔ I ^ n ↔ ∃ r ∈ I, (1 - r) * x ∈ J := by
  simpa only [Ideal.smul_eq_mul, Ideal.mul_top, smul_eq_mul] using
    I.mem_iInf_sup_pow_smul_iff (M := R) J x

end Module

section ExtendedIdeal

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- **The Krull intersection theorem for an extended ideal.** If `R` is Noetherian and `A` is a
finite `R`-module, an element of every power of the two-sided ideal of `A` generated by `I` is
fixed by multiplication by some scalar in `I`. -/
theorem mem_iInf_map_algebraMap_pow_iff [IsNoetherianRing R] [Module.Finite R A] (I : Ideal R)
    (x : A) :
    x ∈ ⨅ n : ℕ, (I.map (algebraMap R A)) ^ n ↔ ∃ r ∈ I, algebraMap R A r * x = x := by
  have hmem : x ∈ ⨅ n : ℕ, (I.map (algebraMap R A)) ^ n ↔
      x ∈ ⨅ n : ℕ, I ^ n • (⊤ : Submodule R A) := by
    simp only [Submodule.mem_iInf, pow_smul_top_eq_restrictScalars_map_pow,
      Submodule.restrictScalars_mem]
  rw [hmem, I.mem_iInf_smul_pow_eq_bot_iff]
  exact ⟨fun ⟨r, hr⟩ ↦ ⟨r, r.property, by rwa [← Algebra.smul_def]⟩,
    fun ⟨r, hrI, hr⟩ ↦ ⟨⟨r, hrI⟩, by rwa [Algebra.smul_def]⟩⟩

/-- **The powers of an extended ideal meet in zero.** If `R` is Noetherian and `A` is a finite
`R`-module, the powers of the two-sided ideal of `A` generated by `I` have zero intersection if
and only if `1 - r` is left regular in `A` for every scalar `r ∈ I`. Both directions come from
`Ideal.mem_iInf_map_algebraMap_pow_iff`: an element of every power is killed by some `1 - r`, and
conversely an element killed by `1 - r` is fixed by `r` and so lies in every power. The
regularity holds, for instance, when `A` has no zero divisors and no scalar in `I` becomes `1`,
as for an augmentation whose kernel contains the image of `I`.

Together with `Ideal.mem_iInf_map_algebraMap_pow_iff` this is the passage from the commutative
Krull intersection theorem to a two-sided ideal of a noncommutative ring. -/
theorem iInf_map_algebraMap_pow_eq_bot_iff [IsNoetherianRing R] [Module.Finite R A]
    (I : Ideal R) :
    ⨅ n : ℕ, (I.map (algebraMap R A)) ^ n = ⊥ ↔
      ∀ r ∈ I, IsLeftRegular (1 - algebraMap R A r) := by
  refine ⟨fun h r hrI ↦ isLeftRegular_iff_right_eq_zero_of_mul.mpr fun x hx ↦ ?_,
    fun h ↦ eq_bot_iff.mpr fun x hx ↦ (Submodule.mem_bot A).mpr ?_⟩
  · rw [← Submodule.mem_bot A, ← h, mem_iInf_map_algebraMap_pow_iff]
    exact ⟨r, hrI, by rwa [sub_mul, one_mul, sub_eq_zero, eq_comm] at hx⟩
  · obtain ⟨r, hrI, hr⟩ := (mem_iInf_map_algebraMap_pow_iff I x).mp hx
    exact (h r hrI).mul_left_eq_zero_iff.mp (by rw [sub_mul, hr, one_mul, sub_self])

end ExtendedIdeal

end Ideal
