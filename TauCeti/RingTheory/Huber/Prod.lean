/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Divisibility.Prod
public import TauCeti.RingTheory.Huber.Uniform

/-!
# Products of Tate rings

The product `A × B` of two topological rings carries the product topology, and the notions of
the Huber theory treated here are computed componentwise on it. An element `x` of `A × B` is
power-bounded, or a pseudouniformiser, exactly when both of its components are, so the
power-bounded subring of `A × B` is `A° × B°`, and `A × B` is uniform exactly when `A` and `B` are.

If `A` and `B` are Tate rings, with open bounded subrings `A₀`, `B₀` and pseudouniformisers `ϖ_A`,
`ϖ_B`, then `A₀ × B₀` is an open bounded subring of `A × B` and `(ϖ_A, ϖ_B)` is a pseudouniformiser,
so `A × B` is a Tate ring. For a perfectoid field `K` of characteristic zero with tilt `K♭`, the
product `K × K♭` is such a Tate ring: it contains no field, and `p = (p, 0)` is a nonzero nonunit.

## Main results

* `TauCeti.Huber.isPowerBounded_prod_iff`, `TauCeti.Huber.isPseudoUniformizer_prod_iff`: the
  componentwise characterisations of power-bounded elements and of pseudouniformisers.
* `TauCeti.Huber.powerBoundedSubring_prod`: `(A × B)° = A° × B°`, and
  `TauCeti.Huber.powerBoundedSubringProdEquiv`, the resulting ring isomorphism, along which
  divisibility is componentwise (`TauCeti.Huber.dvd_iff_powerBoundedSubringProdEquiv`).
* `TauCeti.Huber.isUniform_prod_iff`: `A × B` is uniform exactly when `A` and `B` are, with the
  instance `TauCeti.Huber.IsUniform.instProd`.
* `TauCeti.Huber.IsTateRing.instProd`: a product of Tate rings is a Tate ring.

## References

* P. Scholze, *Étale cohomology of diamonds*, Example 3.4.
-/

public section

open Filter Topology

namespace TauCeti.Huber

section MonoidWithZero

variable {M N : Type*} [MonoidWithZero M] [MonoidWithZero N] [TopologicalSpace M]
  [TopologicalSpace N]

/-- An element of a product is power-bounded exactly when both of its components are. -/
@[simp]
theorem isPowerBounded_prod_iff {x : M × N} :
    IsPowerBounded x ↔ IsPowerBounded x.1 ∧ IsPowerBounded x.2 := by
  simp only [isPowerBounded_iff, isBounded_prod_iff, ← Set.range_comp, Function.comp_def,
    Prod.pow_fst, Prod.pow_snd]

/-- An element of a product is a pseudouniformiser exactly when both of its components are. -/
theorem isPseudoUniformizer_prod_iff {x : M × N} :
    IsPseudoUniformizer x ↔ IsPseudoUniformizer x.1 ∧ IsPseudoUniformizer x.2 := by
  simp only [isPseudoUniformizer_iff, Prod.isUnit_iff, Prod.isTopologicallyNilpotent_iff]
  tauto

/-- **A product is uniform exactly when both factors are**: the power-bounded elements of `M × N`
are the pairs of power-bounded elements. -/
@[simp]
theorem isUniform_prod_iff : IsUniform (M × N) ↔ IsUniform M ∧ IsUniform N := by
  have h : {x : M × N | IsPowerBounded x} =
      {a : M | IsPowerBounded a} ×ˢ {b : N | IsPowerBounded b} := by
    ext x
    simp
  rw [isUniform_iff, isUniform_iff, isUniform_iff, h, isBounded_prod_iff,
    Set.fst_image_prod _ ⟨0, isPowerBounded_zero⟩, Set.snd_image_prod ⟨0, isPowerBounded_zero⟩]

/-- A product of uniform topological rings is uniform. -/
instance IsUniform.instProd [IsUniform M] [IsUniform N] : IsUniform (M × N) :=
  isUniform_prod_iff.mpr ⟨‹_›, ‹_›⟩

end MonoidWithZero

section Nonarchimedean

variable {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
  [NonarchimedeanAddGroup A] [NonarchimedeanAddGroup B]

/-- **The power-bounded subring of a product is the product of the power-bounded subrings**:
`(A × B)° = A° × B°`. -/
@[simp]
theorem powerBoundedSubring_prod :
    powerBoundedSubring (A × B) = (powerBoundedSubring A).prod (powerBoundedSubring B) := by
  ext x
  simp [Subring.mem_prod]

variable (A B) in
/-- The ring isomorphism `(A × B)° ≃+* A° × B°` given by
`TauCeti.Huber.powerBoundedSubring_prod`. -/
def powerBoundedSubringProdEquiv :
    powerBoundedSubring (A × B) ≃+* powerBoundedSubring A × powerBoundedSubring B :=
  (RingEquiv.subringCongr powerBoundedSubring_prod).trans (Subring.prodEquiv _ _)

/-- The first component of `powerBoundedSubringProdEquiv A B x` is the first coordinate of `x`. -/
@[simp]
theorem coe_powerBoundedSubringProdEquiv_fst (x : powerBoundedSubring (A × B)) :
    ((powerBoundedSubringProdEquiv A B x).1 : A) = (x : A × B).1 := (rfl)

/-- The second component of `powerBoundedSubringProdEquiv A B x` is the second coordinate of `x`. -/
@[simp]
theorem coe_powerBoundedSubringProdEquiv_snd (x : powerBoundedSubring (A × B)) :
    ((powerBoundedSubringProdEquiv A B x).2 : B) = (x : A × B).2 := (rfl)

/-- The inverse of `powerBoundedSubringProdEquiv A B` pairs the two components. -/
@[simp]
theorem coe_powerBoundedSubringProdEquiv_symm
    (y : powerBoundedSubring A × powerBoundedSubring B) :
    ((powerBoundedSubringProdEquiv A B).symm y : A × B) = ((y.1 : A), (y.2 : B)) := (rfl)

/-- Divisibility in `(A × B)°` is componentwise, read through `(A × B)° ≃+* A° × B°`. -/
theorem dvd_iff_powerBoundedSubringProdEquiv {a b : powerBoundedSubring (A × B)} :
    a ∣ b ↔ (powerBoundedSubringProdEquiv A B a).1 ∣ (powerBoundedSubringProdEquiv A B b).1 ∧
      (powerBoundedSubringProdEquiv A B a).2 ∣ (powerBoundedSubringProdEquiv A B b).2 := by
  rw [← map_dvd_iff (powerBoundedSubringProdEquiv A B), prod_dvd_iff]

end Nonarchimedean

section Tate

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [CommRing B]
  [TopologicalSpace B] [IsTopologicalRing B]

/-- **A product of Tate rings is a Tate ring**: if `A₀ ⊆ A` and `B₀ ⊆ B` are open bounded subrings
and `ϖ_A`, `ϖ_B` are pseudouniformisers, then `A₀ × B₀` is an open bounded subring of `A × B` and
`(ϖ_A, ϖ_B)` is a pseudouniformiser (Scholze, *Étale cohomology of diamonds*, Example 3.4). -/
instance IsTateRing.instProd [IsTateRing A] [IsTateRing B] : IsTateRing (A × B) := by
  obtain ⟨⟨A₀, hA₀, hbA⟩, ϖ, hϖ⟩ := isTateRing_iff_exists_isOpen_isBounded.mp ‹IsTateRing A›
  obtain ⟨⟨B₀, hB₀, hbB⟩, ϖ', hϖ'⟩ := isTateRing_iff_exists_isOpen_isBounded.mp ‹IsTateRing B›
  refine IsTateRing.of_isOpen_isBounded (A₀.prod B₀) ?_ ?_
    (isPseudoUniformizer_prod_iff.mpr ⟨hϖ, hϖ'⟩ : IsPseudoUniformizer (ϖ, ϖ'))
  · rw [Subring.coe_prod]
    exact hA₀.prod hB₀
  · rw [Subring.coe_prod]
    exact hbA.prod hbB

end Tate

end TauCeti.Huber
