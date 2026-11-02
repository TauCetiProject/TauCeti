/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Normal domains descend along faithfully flat maps

If `A → B` is faithfully flat and `B` is an integrally closed domain, then `A` is integrally
closed. The map is injective, so `A` is a domain (Mathlib's `IsDomain.of_faithfulSMul`). If `a / b`
is integral over `A`, its image is integral over `B`, hence `a ∈ bB`; faithful flatness gives
`bB ∩ A = bA` (`Ideal.comap_map_eq_self_of_faithfullyFlat`), so `a ∈ bA` and `a / b ∈ A`.

## Main results

* `TauCeti.IsIntegrallyClosed.of_faithfullyFlat`: if `B` is an integrally closed domain that is
  faithfully flat over `A`, then `A` is integrally closed.

## References

* [Stacks Project, Lemma 10.164.3](https://stacks.math.columbia.edu/tag/033G).
-/

public section

namespace TauCeti

open scoped nonZeroDivisors

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
  [IsDomain B]

/-- **Normality descends along faithfully flat maps.** If `B` is an integrally closed domain that
is faithfully flat over `A`, then `A` is integrally closed. Stacks, Lemma 10.164.3 (033G), for
domains. -/
@[stacks 033G "for domains"]
theorem IsIntegrallyClosed.of_faithfullyFlat [IsIntegrallyClosed B] : IsIntegrallyClosed A := by
  have := IsDomain.of_faithfulSMul A B
  let : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra A _
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
  have hbB : algebraMap A (FractionRing B) b ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A (FractionRing B))).mpr
      (nonZeroDivisors.ne_zero hb)
  have hint : IsIntegral B (algebraMap (FractionRing A) (FractionRing B)
      (algebraMap A _ a / algebraMap A _ b)) :=
    (hx.map (IsScalarTower.toAlgHom A (FractionRing A) (FractionRing B))).tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hdvd : algebraMap A B a = y * algebraMap A B b := by
    apply IsFractionRing.injective B (FractionRing B)
    rw [map_mul, hy]
    simp [← IsScalarTower.algebraMap_apply, hbB]
  have hmem : a ∈ ((Ideal.span {b}).map (algebraMap A B)).comap (algebraMap A B) := by
    rw [Ideal.mem_comap, Ideal.map_span, Set.image_singleton]
    exact Ideal.mem_span_singleton'.mpr ⟨y, hdvd.symm⟩
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat, Ideal.mem_span_singleton'] at hmem
  obtain ⟨c, rfl⟩ := hmem
  refine ⟨c, ?_⟩
  have hbA : algebraMap A (FractionRing A) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  rw [map_mul, mul_div_cancel_right₀ _ hbA]

end TauCeti
