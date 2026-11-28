/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.LaurentCover.Exactness
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.SheafyRing
public import TauCeti.RingTheory.Huber.Glueing.Square
public import TauCeti.RingTheory.Huber.LocalizationTopology.Laurent.Restriction
public import TauCeti.Topology.Algebra.Ring.Ideal

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.LaurentCover.Proper
import TauCeti.RingTheory.Huber.LocalizationTopology.Laurent.RationalCompletion

/-!
# Simple Laurent covers of sheafy Tate rings form glueing squares

Let `R` be a complete Hausdorff Tate ring and `Aplus` a subring whose presentation-limit
structure presheaf is a sheaf (`IsSheafyForEveryPresentation Aplus`). For any `f : R` and models
`R₁`, `R₂`, `R₁₂` of `R⟨{f, 1}/1⟩ = R⟨f⟩`, `R⟨{1}/f⟩ = R⟨1/f⟩`, and `R⟨{f², 1}/f⟩ = R⟨f, 1/f⟩`
with continuous `R`-algebra transition maps `R₁ → R₁₂` and `R₂ → R₁₂`, the square
`R → R₁, R₂ → R₁₂` is a `TauCeti.Huber.GlueingSquare`.

This bridges sheafiness and Kedlaya–Liu Lemma 2.4.22 to Definition 2.7.3:
* *Exactness (`0 → R → R₁ × R₂ → R₁₂`)* comes from
  `laurent_injective_and_exact_of_isSheafyForEveryPresentation`.
* *Surjectivity of `(r₁, r₂) ↦ r₁ - r₂`* comes from
  `IsRationalCompletion.surjective_algebraMap_sub_laurent`.
* *Topological strictness* follows automatically from `GlueingSquare.of_exact` via Henkel's open
  mapping theorem and transport along `GlueingSquare.congr`.
* *Dense range of `R₂ → R₁₂`* follows from the shared denominator `f`, and *maximal-ideal prime
  contraction* follows from `exists_prime_comap_eq_of_mem_rationalSubset` and Wedhorn's
  Proposition 7.51 (`exists_mem_spa_supp_eq_of_isMaximal`).

## Main results

* `TauCeti.Huber.GlueingSquare.of_simpleLaurent` and `of_simpleLaurent_of_isSheafyRing`: simple
  Laurent covers of sheafy complete Hausdorff Tate rings form glueing squares.
* `TauCeti.Huber.GlueingSquare.of_simpleLaurent_ratLoc`: canonical `GlueingSquare` on the three
  explicit `ratLoc` carriers with `laurentLeftAlgHom` and `laurentRightAlgHom`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  §2.4, Lemma 2.4.22 and proof of Theorem 2.4.23; §2.7, Definition 2.7.3.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 7.51 and §8.1.
-/

public section

open TauCeti.Huber TauCeti.ValuationSpectrum

namespace TauCeti.Huber

section Main

variable {R R₁ R₂ R₁₂ : Type*} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing R₁₂]
  [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R] [CompleteSpace R] [T0Space R]
  [TopologicalSpace R₁] [TopologicalSpace R₂] [TopologicalSpace R₁₂]
  [Algebra R R₁] [Algebra R R₂] [Algebra R₁ R₁₂] [Algebra R₂ R₁₂] [Algebra R R₁₂]
  [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂] [DecidableEq R]
  {P : PairOfDefinition R} {f : R}
  {hT₁ : IsOpen (Ideal.span (({f, 1} : Finset R) : Set R) : Set R)}
  {hT₂ : IsOpen (Ideal.span (({1} : Finset R) : Set R) : Set R)}
  {hT₁₂ : IsOpen (Ideal.span (({f * f, 1} : Finset R) : Set R) : Set R)}

-- Transport `algebraMap B B'` along `ratLocEquiv` to obtain an `R`-algebra map between the
-- canonical `ratLoc` carriers together with its scalar tower and continuity.
omit [IsUniformAddGroup R] [CompleteSpace R] [T0Space R] [DecidableEq R] in
private theorem isScalarTower_and_continuous_toAlgebra_ratLocEquiv
    {T T' : Finset R} {s s' : R}
    {hT : IsOpen (Ideal.span (T : Set R) : Set R)}
    {hT' : IsOpen (Ideal.span (T' : Set R) : Set R)}
    {B B' : Type*} [CommRing B] [TopologicalSpace B] [Algebra R B]
    [CommRing B'] [TopologicalSpace B'] [Algebra R B'] [Algebra B B'] [IsScalarTower R B B']
    (hB : IsRationalCompletion P T s hT B) (hB' : IsRationalCompletion P T' s' hT' B')
    (hc : Continuous (algebraMap B B')) :
    letI : Algebra (ratLoc P T s (P.hasDenominatorPower_of_isOpen_span T s _ hT))
        (ratLoc P T' s' (P.hasDenominatorPower_of_isOpen_span T' s' _ hT')) :=
      (hB'.ratLocEquiv.symm.toRingHom.comp
        ((algebraMap B B').comp hB.ratLocEquiv.toRingHom)).toAlgebra
    IsScalarTower R (ratLoc P T s (P.hasDenominatorPower_of_isOpen_span T s _ hT))
        (ratLoc P T' s' (P.hasDenominatorPower_of_isOpen_span T' s' _ hT')) ∧
      Continuous (algebraMap
        (ratLoc P T s (P.hasDenominatorPower_of_isOpen_span T s _ hT))
        (ratLoc P T' s' (P.hasDenominatorPower_of_isOpen_span T' s' _ hT'))) := by
  let L := ratLoc P T s (P.hasDenominatorPower_of_isOpen_span T s _ hT)
  let L' := ratLoc P T' s' (P.hasDenominatorPower_of_isOpen_span T' s' _ hT')
  let _ : Algebra L L' := (hB'.ratLocEquiv.symm.toRingHom.comp
    ((algebraMap B B').comp hB.ratLocEquiv.toRingHom)).toAlgebra
  refine ⟨IsScalarTower.of_algebraMap_eq fun r ↦ ?_, ?_⟩
  · rw [RingHom.algebraMap_toAlgebra]
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      AlgEquiv.coe_toRingEquiv, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply R B B']
  · rw [RingHom.algebraMap_toAlgebra]
    exact hB'.continuous_ratLocEquiv_symm.comp (hc.comp hB.continuous_ratLocEquiv)

/-- A simple Laurent cover `{|f| ≤ 1}`, `{|f| ≥ 1}` of a complete Hausdorff Tate ring `R` equipped
with a subring `Aplus` satisfying `IsSheafyForEveryPresentation Aplus` forms a `GlueingSquare`
(Kedlaya–Liu, §2.4, Lemma 2.4.22 and proof of Theorem 2.4.23). -/
theorem GlueingSquare.of_simpleLaurent [IsTateRing R] {Aplus : Subring R}
    (hs : IsSheafyForEveryPresentation Aplus) (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ R₁)
    (h₂ : IsRationalCompletion P {1} f hT₂ R₂) (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ R₁₂)
    (hc₁ : Continuous (algebraMap R₁ R₁₂)) (hc₂ : Continuous (algebraMap R₂ R₁₂)) :
    GlueingSquare R R₁ R₂ R₁₂ := by
  let L₁ := ratLoc P {f, 1} 1 (P.hasDenominatorPower_of_isOpen_span _ _ _ hT₁)
  let L₂ := ratLoc P {1} f (P.hasDenominatorPower_of_isOpen_span _ _ _ hT₂)
  let L₁₂ := ratLoc P {f * f, 1} f (P.hasDenominatorPower_of_isOpen_span _ _ _ hT₁₂)
  let _ : Algebra L₁ L₁₂ := (h₁₂.ratLocEquiv.symm.toRingHom.comp
    ((algebraMap R₁ R₁₂).comp h₁.ratLocEquiv.toRingHom)).toAlgebra
  let _ : Algebra L₂ L₁₂ := (h₁₂.ratLocEquiv.symm.toRingHom.comp
    ((algebraMap R₂ R₁₂).comp h₂.ratLocEquiv.toRingHom)).toAlgebra
  obtain ⟨_, hcL₁⟩ := isScalarTower_and_continuous_toAlgebra_ratLocEquiv h₁ h₁₂ hc₁
  obtain ⟨_, hcL₂⟩ := isScalarTower_and_continuous_toAlgebra_ratLocEquiv h₂ h₁₂ hc₂
  have hL₁ := isRationalCompletion_ratLoc P {f, 1} 1 hT₁
  have hL₂ := isRationalCompletion_ratLoc P {1} f hT₂
  have hL₁₂ := isRationalCompletion_ratLoc P {f * f, 1} f hT₁₂
  obtain ⟨hinj, hexact⟩ :=
    laurent_injective_and_exact_of_isSheafyForEveryPresentation hs hL₁ hL₂ hL₁₂ hcL₁ hcL₂
  obtain ⟨P₀, hP₀, -⟩ := hs.exists_compatible_isSheaf
  have hsqL : GlueingSquare R L₁ L₂ L₁₂ :=
    GlueingSquare.of_exact hL₁.continuous_algebraMap hL₂.continuous_algebraMap hcL₁ hcL₂
      hinj hexact (hL₁.surjective_algebraMap_sub_laurent hL₂ hL₁₂ hcL₁ hcL₂)
      (hL₂.denseRange_of_comp_algebraMap_eq hL₁₂
        (RingHom.ext fun x ↦ (IsScalarTower.algebraMap_apply R L₂ L₁₂ x).symm))
      (exists_prime_comap_eq_of_simpleLaurent Aplus hs.isRingOfIntegralElements hP₀ f hL₁ hL₂)
  exact hsqL.congr h₁.ratLocEquiv h₁.continuous_ratLocEquiv h₁.continuous_ratLocEquiv_symm
    h₂.ratLocEquiv h₂.continuous_ratLocEquiv h₂.continuous_ratLocEquiv_symm
    h₁₂.ratLocEquiv.toRingEquiv h₁₂.continuous_ratLocEquiv h₁₂.continuous_ratLocEquiv_symm
    (fun _ ↦ h₁₂.ratLocEquiv.apply_symm_apply _) (fun _ ↦ h₁₂.ratLocEquiv.apply_symm_apply _)

/-- Convenience form of `GlueingSquare.of_simpleLaurent` for any sheafy complete Hausdorff Tate
ring `R`, using the canonical Huber pair `(R, R°)`. -/
theorem GlueingSquare.of_simpleLaurent_of_isSheafyRing [IsTateRing R] (hs : IsSheafyRing R)
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ R₁) (h₂ : IsRationalCompletion P {1} f hT₂ R₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ R₁₂)
    (hc₁ : Continuous (algebraMap R₁ R₁₂)) (hc₂ : Continuous (algebraMap R₂ R₁₂)) :
    GlueingSquare R R₁ R₂ R₁₂ :=
  GlueingSquare.of_simpleLaurent
    (hs.isSheafyForEveryPresentation (Pair.powerBounded R).isRingOfIntegralElements)
    h₁ h₂ h₁₂ hc₁ hc₂

end Main

section RatLoc

open scoped TauCeti.Huber.Laurent in
/-- Canonical `GlueingSquare` on the three explicit `ratLoc` carriers `R⟨{f, 1}/1⟩`, `R⟨{1}/f⟩`,
and `R⟨{f², 1}/f⟩`, with overlap algebra structures `laurentLeftAlgebra` and
`laurentRightAlgebra`. -/
theorem GlueingSquare.of_simpleLaurent_ratLoc {R : Type*} [CommRing R] [UniformSpace R]
    [IsUniformAddGroup R] [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R] [T0Space R]
    [DecidableEq R] (hs : IsSheafyRing R) (P : PairOfDefinition R) (f : R) :
    GlueingSquare R
      (ratLoc P {f, 1} 1 (P.hasDenominatorPower_of_isOpen_span _ _ _
        (isOpen_span_of_one_mem (by simp))))
      (ratLoc P {1} f (P.hasDenominatorPower_of_isOpen_span _ _ _
        (isOpen_span_of_one_mem (by simp))))
      (ratLoc P {f * f, 1} f (P.hasDenominatorPower_of_isOpen_span _ _ _
        (isOpen_span_of_one_mem (by simp)))) :=
  GlueingSquare.of_simpleLaurent_of_isSheafyRing hs
    (isRationalCompletion_ratLoc P {f, 1} 1 (isOpen_span_of_one_mem (by simp)))
    (isRationalCompletion_ratLoc P {1} f (isOpen_span_of_one_mem (by simp)))
    (isRationalCompletion_ratLoc P {f * f, 1} f (isOpen_span_of_one_mem (by simp)))
    (continuous_algebraMap_laurentLeftAlgebra P f) (continuous_algebraMap_laurentRightAlgebra P f)

end RatLoc

end TauCeti.Huber

end
