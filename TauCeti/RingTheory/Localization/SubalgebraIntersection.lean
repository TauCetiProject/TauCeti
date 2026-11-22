/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Coprime.Basic

/-!
# Intersections of embedded principal localizations

A family of embedded principal localizations whose denominators generate the unit ideal
intersects in the coefficient image. This recovers global coefficient membership from a
cover by principal localizations and supplies denominator patching in a common ambient algebra.
The coefficient and ambient commutative semirings need not be domains, and the family may be
infinite. For a total quotient ring, the embedded models `Localization.subalgebra` require
non-zero-divisor denominators. Those denominators must still generate the unit ideal.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics
  195 (2005), §5, for denominator patching in a common ambient ring.
-/

public section

namespace TauCeti.Localization.subalgebra

variable {R K : Type*} [CommSemiring R] [CommSemiring K] [Algebra R K]

/-- Embedded principal localizations at a unit-ideal generating family intersect in the
coefficient image. In total quotient models the denominators must be non-zero-divisors. -/
theorem iInf_subalgebra_powers_eq_bot_of_span_range_eq_top {ι : Type*} (a : ι → R)
    (A : ι → Subalgebra R K) [∀ i, IsLocalization (Submonoid.powers (a i)) (A i)]
    (hcover : Ideal.span (Set.range a) = ⊤) : (⨅ i, A i) = ⊥ := by
  refine bot_unique fun x hx ↦ ?_
  rw [← Subalgebra.mem_toSubmodule, Algebra.toSubmodule_bot]
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (1 : Submodule R K)
    (Set.range a) hcover x ?_
  rintro ⟨_, i, rfl⟩
  have hi := (mem_iff_exists_mem_denIdeal (Submonoid.powers (a i)) (A i) x).mp
    (Algebra.mem_iInf.mp hx i)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a i ^ n ∈ Algebra.denIdeal K x := by
    simpa only [Submonoid.mem_powers_iff, exists_exists_eq_and] using hi
  exact ⟨n, by rwa [Algebra.denIdeal_def, Submodule.mem_colon_singleton] at hn⟩

/-- Two embedded principal localizations at coprime elements intersect in the coefficient
image. Regularity is supplied by the chosen models when they lie in a total quotient ring. -/
theorem inf_subalgebra_powers_eq_bot_of_isCoprime (a b : R) (A B : Subalgebra R K)
    [IsLocalization (Submonoid.powers a) A] [IsLocalization (Submonoid.powers b) B]
    (hab : IsCoprime a b) : A ⊓ B = ⊥ := by
  let d : Bool → R := fun i ↦ if i then b else a
  let C : Bool → Subalgebra R K := fun i ↦ if i then B else A
  have : ∀ i, IsLocalization (Submonoid.powers (d i)) (C i) := by
    intro i
    cases i <;> dsimp [d, C] <;> infer_instance
  have hc : Ideal.span (Set.range d) = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    obtain ⟨r, s, hrs⟩ := hab
    rw [← hrs]
    exact Ideal.add_mem _
      ((Ideal.span (Set.range d)).mul_mem_left r (Ideal.subset_span ⟨false, rfl⟩))
      ((Ideal.span (Set.range d)).mul_mem_left s (Ideal.subset_span ⟨true, rfl⟩))
  simpa [C, iInf_bool_eq, inf_comm] using iInf_subalgebra_powers_eq_bot_of_span_range_eq_top d C hc

end TauCeti.Localization.subalgebra
