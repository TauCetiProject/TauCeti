/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.RingTheory.Flat.NonZeroDivisors

/-!
# Integral closedness descends along faithfully flat maps

If `A → B` is faithfully flat and `B` is integrally closed, then `A` is integrally closed. A
nonzerodivisor `b` of `A` stays a nonzerodivisor in `B` by flatness. If `a / b` is integral over
`A`, its image in the total ring of fractions of `B` is integral over `B`, hence `a ∈ bB`;
faithful flatness gives `bB ∩ A = bA` (`Ideal.comap_map_eq_self_of_faithfullyFlat`), so `a ∈ bA`
and `a / b ∈ A`.

## Main results

* `TauCeti.IsIntegrallyClosed.of_faithfullyFlat`: if `B` is integrally closed and
  faithfully flat over `A`, then `A` is integrally closed.

## References

* [Stacks Project, Lemma 10.164.3](https://stacks.math.columbia.edu/tag/033G), of which
  `TauCeti.IsIntegrallyClosed.of_faithfullyFlat` is a variant for integral closedness in the total
  ring of fractions.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]

/-- **Integral closedness descends along faithfully flat maps.** If `B` is integrally closed and
faithfully flat over `A`, then `A` is integrally closed. This is a variant of Stacks,
Lemma 10.164.3 (033G), with `normal ring` replaced by integral closedness in the total ring of
fractions. -/
@[stacks 033G "with integrally closed in the total ring of fractions in place of normal"]
theorem IsIntegrallyClosed.of_faithfullyFlat [IsIntegrallyClosed B] : IsIntegrallyClosed A := by
  have hreg : A⁰ ≤ B⁰.comap (algebraMap A B) := fun _ hb ↦
    Module.Flat.algebraMap_mem_nonZeroDivisors hb
  let f := IsLocalization.map (S := FractionRing A) (FractionRing B) (algebraMap A B)
    (M := A⁰) (T := B⁰) hreg
  let : Algebra (FractionRing A) (FractionRing B) := f.toAlgebra
  have : IsScalarTower A (FractionRing A) (FractionRing B) :=
    .of_algebraMap_eq fun a ↦ (IsLocalization.map_eq (T := B⁰) hreg a).symm
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro x hx
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective A⁰ x
  have hint : IsIntegral B (algebraMap (FractionRing A) (FractionRing B)
      (IsLocalization.mk' (FractionRing A) a b)) :=
    (hx.map (IsScalarTower.toAlgHom A (FractionRing A) (FractionRing B))).tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hdvd : algebraMap A B a = y * algebraMap A B b := by
    apply IsFractionRing.injective B (FractionRing B)
    rw [map_mul, hy]
    have := IsLocalization.map_mk' (S := FractionRing A) (Q := FractionRing B)
      (g := algebraMap A B) (hy := hreg) a b
    refine (IsLocalization.mk'_eq_iff_eq_mul.mp this.symm)
  have hmem : a ∈ ((Ideal.span {(b : A)}).map (algebraMap A B)).comap (algebraMap A B) := by
    rw [Ideal.mem_comap, Ideal.map_span, Set.image_singleton]
    exact Ideal.mem_span_singleton'.mpr ⟨y, hdvd.symm⟩
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat, Ideal.mem_span_singleton'] at hmem
  obtain ⟨c, rfl⟩ := hmem
  exact ⟨c, (IsLocalization.mk'_eq_iff_eq_mul.mpr (by simp)).symm⟩

end TauCeti
