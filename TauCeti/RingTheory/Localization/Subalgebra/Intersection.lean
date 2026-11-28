/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Localization.Subalgebra.Membership
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Data.Bool.Set

/-!
# Intersections of embedded principal localizations

A family of embedded principal localizations whose denominators generate the unit ideal
intersects in the coefficient image. This recovers global coefficient membership from a
cover by principal localizations and supplies denominator patching in a common ambient algebra.
The coefficient and ambient commutative semirings need not be domains, and the family may be
infinite. `Localization.subalgebra` and `ofField` provide the required `IsLocalization`
instances for their embedded models.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics
  195 (2005), §5, for denominator patching in a common ambient ring.
-/

public section

namespace TauCeti.IsLocalization

variable {R K : Type*} [CommSemiring R] [CommSemiring K] [Algebra R K]

/-- Embedded principal localizations at a unit-ideal generating family intersect in the
coefficient image. -/
theorem iInf_subalgebra_powers_eq_bot_of_span_range_eq_top {ι : Type*} (a : ι → R)
    (A : ι → Subalgebra R K) [∀ i, IsLocalization (Submonoid.powers (a i)) (A i)]
    (hcover : Ideal.span (Set.range a) = ⊤) : (⨅ i, A i) = ⊥ := by
  refine bot_unique fun x hx ↦ ?_
  rw [← Subalgebra.mem_toSubmodule, Algebra.toSubmodule_bot]
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (1 : Submodule R K)
    (Set.range a) hcover x ?_
  rintro ⟨_, i, rfl⟩
  obtain ⟨n, hn⟩ := (mem_subalgebra_iff_exists_pow_mul_mem_range (a i) (A i) x).mp
    (Algebra.mem_iInf.mp hx i)
  refine ⟨n, ?_⟩
  rw [Algebra.smul_def, Submodule.mem_one]
  simpa only [Set.mem_range, map_pow] using hn

/-- Two embedded principal localizations at coprime elements intersect in the coefficient
image. -/
theorem inf_subalgebra_powers_eq_bot_of_isCoprime (a b : R) (A B : Subalgebra R K)
    [IsLocalization (Submonoid.powers a) A] [IsLocalization (Submonoid.powers b) B]
    (hab : IsCoprime a b) : A ⊓ B = ⊥ := by
  let d : Bool → R := fun i ↦ if i then b else a
  let C : Bool → Subalgebra R K := fun i ↦ if i then B else A
  have : ∀ i, IsLocalization (Submonoid.powers (d i)) (C i) := by
    intro i
    cases i <;> dsimp [d, C] <;> infer_instance
  have hr : Set.range d = {a, b} := by
    simpa only [d, Bool.false_eq_true, ↓reduceIte] using Bool.range_eq d
  have hc : Ideal.span (Set.range d) = ⊤ := by
    rw [hr, Ideal.span_insert]
    exact ((Ideal.isCoprime_span_singleton_iff a b).mpr hab).sup_eq
  simpa only [C, iInf_bool_eq, Bool.false_eq_true, ↓reduceIte, inf_comm] using
    iInf_subalgebra_powers_eq_bot_of_span_range_eq_top d C hc

end TauCeti.IsLocalization
