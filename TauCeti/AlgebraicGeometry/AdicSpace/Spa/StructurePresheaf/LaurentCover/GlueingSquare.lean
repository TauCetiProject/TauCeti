/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.LaurentCover.Exactness
public import TauCeti.RingTheory.Huber.Glueing.Square
public import TauCeti.RingTheory.Huber.LocalizationTopology.Laurent.Restriction
public import TauCeti.Topology.Algebra.Ring.Ideal

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Proper
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Laurent.Basic
import TauCeti.RingTheory.Huber.LocalizationTopology.Laurent.RationalCompletion

/-!
# Simple Laurent covers of sheafy Tate rings form glueing squares

Let `R` be a complete Hausdorff Tate ring and `S = (R, R⁺)` a Huber pair whose presentation-limit
structure presheaf is a sheaf (`IsSheafyForEveryPresentation S.plus`). For any `f : R` and models
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

* `TauCeti.Huber.GlueingSquare.of_simpleLaurent` and
  `TauCeti.Huber.GlueingSquare.of_simpleLaurent_of_isSheafyRing`: simple Laurent covers of sheafy
  complete Hausdorff Tate rings form glueing squares.
* `TauCeti.Huber.GlueingSquare.of_simpleLaurent_ratLoc`: canonical `GlueingSquare` on the three
  explicit `ratLoc` carriers with `laurentLeftAlgHom` and `laurentRightAlgHom`.
* `TauCeti.Huber.exists_simpleLaurent_glueingSquare`: existential packaging of the canonical
  `ratLoc` glueing square.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  §2.4, Lemma 2.4.22 and proof of Theorem 2.4.23; §2.7, Definition 2.7.3.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 7.51 and §8.1.
-/

public section

open TauCeti.Huber TauCeti.ValuationSpectrum

namespace TauCeti.Huber

/-- Maximal-ideal prime contraction for a simple Laurent cover: every maximal ideal of `R` is the
contraction of a prime ideal of `R₁ × R₂` via a point of `Spa(R, R⁺)`. -/
private theorem exists_prime_comap_eq_of_simpleLaurent {R : Type*} [CommRing R] [UniformSpace R]
    [IsUniformAddGroup R] [IsTopologicalRing R] [CompleteSpace R] [T0Space R] [IsHuberRing R]
    [DecidableEq R] (P : PairOfDefinition R) (S : Pair R)
    (hs : IsSheafyForEveryPresentation S.plus) (f : R)
    {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂] [TopologicalSpace R₁] [TopologicalSpace R₂]
    [Algebra R R₁] [Algebra R R₂]
    {hT₁ : IsOpen (Ideal.span (({f, 1} : Finset R) : Set R) : Set R)}
    {hT₂ : IsOpen (Ideal.span (({1} : Finset R) : Set R) : Set R)}
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ R₁)
    (h₂ : IsRationalCompletion P {1} f hT₂ R₂)
    (m : Ideal R) (hm : m.IsMaximal) :
    ∃ p : Ideal (R₁ × R₂), p.IsPrime ∧
      p.comap ((algebraMap R R₁).prod (algebraMap R R₂)) = m := by
  have := hm
  obtain ⟨P₀, hP₀, -⟩ := hs.exists_compatible_isSheaf
  obtain ⟨v, hv, rfl⟩ := exists_mem_spa_supp_eq_of_isMaximal S.plus S.isRingOfIntegralElements m
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (spa_subset_iUnion_laurentCover S.plus f hv)
  cases b with
  | true =>
    obtain ⟨q, hq, hqm⟩ := exists_prime_comap_eq_of_mem_rationalSubset hP₀ h₁
      (by simpa [mem_rationalSubset_iff] using hb) hm
    exact ⟨q.comap (RingHom.fst R₁ R₂), hq.comap _, by rw [Ideal.comap_comap]; exact hqm⟩
  | false =>
    obtain ⟨q, hq, hqm⟩ := exists_prime_comap_eq_of_mem_rationalSubset hP₀ h₂
      (by simpa [mem_rationalSubset_iff] using hb) hm
    exact ⟨q.comap (RingHom.snd R₁ R₂), hq.comap _, by rw [Ideal.comap_comap]; exact hqm⟩

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

/-- A simple Laurent cover `{|f| ≤ 1}`, `{|f| ≥ 1}` of a complete Hausdorff Tate ring `R` equipped
with a Huber pair `S` satisfying `IsSheafyForEveryPresentation S.plus` forms a `GlueingSquare`
(Kedlaya–Liu, §2.4, Lemma 2.4.22 and proof of Theorem 2.4.23). -/
theorem GlueingSquare.of_simpleLaurent [IsTateRing R] (S : Pair R)
    (hs : IsSheafyForEveryPresentation S.plus) (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ R₁)
    (h₂ : IsRationalCompletion P {1} f hT₂ R₂) (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ R₁₂)
    (hc₁ : Continuous (algebraMap R₁ R₁₂)) (hc₂ : Continuous (algebraMap R₂ R₁₂)) :
    GlueingSquare R R₁ R₂ R₁₂ := by
  obtain ⟨e₁, he₁, he₁'⟩ := (isRationalCompletion_iff_ratLoc P {f, 1} 1 hT₁ R₁).mp h₁
  obtain ⟨e₂, he₂, he₂'⟩ := (isRationalCompletion_iff_ratLoc P {1} f hT₂ R₂).mp h₂
  obtain ⟨e₁₂, he₁₂, he₁₂'⟩ := (isRationalCompletion_iff_ratLoc P {f * f, 1} f hT₁₂ R₁₂).mp h₁₂
  let L₁ := ratLoc P {f, 1} 1 (P.hasDenominatorPower_of_isOpen_span _ _ _ hT₁)
  let L₂ := ratLoc P {1} f (P.hasDenominatorPower_of_isOpen_span _ _ _ hT₂)
  let L₁₂ := ratLoc P {f * f, 1} f (P.hasDenominatorPower_of_isOpen_span _ _ _ hT₁₂)
  let φ₁ : L₁ →+* L₁₂ := e₁₂.symm.toRingHom.comp ((algebraMap R₁ R₁₂).comp e₁.toRingHom)
  let φ₂ : L₂ →+* L₁₂ := e₁₂.symm.toRingHom.comp ((algebraMap R₂ R₁₂).comp e₂.toRingHom)
  let _ : Algebra L₁ L₁₂ := φ₁.toAlgebra
  let _ : Algebra L₂ L₁₂ := φ₂.toAlgebra
  have _ : IsScalarTower R L₁ L₁₂ := IsScalarTower.of_algebraMap_eq fun r ↦ by
    simp only [RingHom.algebraMap_toAlgebra, φ₁, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, AlgEquiv.coe_toRingEquiv]
    rw [e₁.commutes, ← IsScalarTower.algebraMap_apply R R₁ R₁₂, ← e₁₂.commutes,
      AlgEquiv.symm_apply_apply]
  have _ : IsScalarTower R L₂ L₁₂ := IsScalarTower.of_algebraMap_eq fun r ↦ by
    simp only [RingHom.algebraMap_toAlgebra, φ₂, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, AlgEquiv.coe_toRingEquiv]
    rw [e₂.commutes, ← IsScalarTower.algebraMap_apply R R₂ R₁₂, ← e₁₂.commutes,
      AlgEquiv.symm_apply_apply]
  have hL₁ := isRationalCompletion_ratLoc P {f, 1} 1 hT₁
  have hL₂ := isRationalCompletion_ratLoc P {1} f hT₂
  have hL₁₂ := isRationalCompletion_ratLoc P {f * f, 1} f hT₁₂
  have hcL₁ : Continuous (algebraMap L₁ L₁₂) := by
    rw [RingHom.algebraMap_toAlgebra]; exact he₁₂'.comp (hc₁.comp he₁)
  have hcL₂ : Continuous (algebraMap L₂ L₁₂) := by
    rw [RingHom.algebraMap_toAlgebra]; exact he₁₂'.comp (hc₂.comp he₂)
  obtain ⟨hinj, hexact⟩ :=
    laurent_injective_and_exact_of_isSheafyForEveryPresentation S hs hL₁ hL₂ hL₁₂ hcL₁ hcL₂
  have hsqL : GlueingSquare R L₁ L₂ L₁₂ :=
    GlueingSquare.of_exact hL₁.continuous_algebraMap hL₂.continuous_algebraMap hcL₁ hcL₂
      hinj hexact (hL₁.surjective_algebraMap_sub_laurent hL₂ hL₁₂ hcL₁ hcL₂)
      (hL₂.denseRange_of_comp_algebraMap_eq hL₁₂
        (RingHom.ext fun x ↦ (IsScalarTower.algebraMap_apply R L₂ L₁₂ x).symm))
      (exists_prime_comap_eq_of_simpleLaurent P S hs f hL₁ hL₂)
  exact hsqL.congr e₁ he₁ he₁' e₂ he₂ he₂' e₁₂.toRingEquiv he₁₂ he₁₂'
    (fun x ↦ by simp only [RingHom.algebraMap_toAlgebra, φ₁, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_toRingEquiv,
      AlgEquiv.apply_symm_apply])
    (fun x ↦ by simp only [RingHom.algebraMap_toAlgebra, φ₂, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_toRingEquiv,
      AlgEquiv.apply_symm_apply])

/-- Convenience form of `GlueingSquare.of_simpleLaurent` for any sheafy complete Hausdorff Tate
ring `R`, using the canonical Huber pair `(R, R°)`. -/
theorem GlueingSquare.of_simpleLaurent_of_isSheafyRing [IsTateRing R] (hs : IsSheafyRing R)
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ R₁) (h₂ : IsRationalCompletion P {1} f hT₂ R₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ R₁₂)
    (hc₁ : Continuous (algebraMap R₁ R₁₂)) (hc₂ : Continuous (algebraMap R₂ R₁₂)) :
    GlueingSquare R R₁ R₂ R₁₂ :=
  GlueingSquare.of_simpleLaurent (Pair.powerBounded R)
    (hs.isSheafyForEveryPresentation (Pair.powerBounded R).isRingOfIntegralElements)
    h₁ h₂ h₁₂ hc₁ hc₂

end Main

section RatLoc

open Classical in
open scoped TauCeti.Huber.Laurent in
/-- Canonical `GlueingSquare` on the three explicit `ratLoc` carriers `R⟨{f, 1}/1⟩`, `R⟨{1}/f⟩`,
and `R⟨{f², 1}/f⟩`, with overlap algebra structures `laurentLeftAlgebra` and
`laurentRightAlgebra`. -/
theorem GlueingSquare.of_simpleLaurent_ratLoc {R : Type*} [CommRing R] [UniformSpace R]
    [IsUniformAddGroup R] [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R] [T0Space R]
    (hs : IsSheafyRing R) (P : PairOfDefinition R) (f : R) :
    let hden₁ := P.hasDenominatorPower_of_isOpen_span ({f, 1} : Finset R) 1
      (Localization.Away (1 : R)) (isOpen_span_of_one_mem (by simp))
    let hden₂ := P.hasDenominatorPower_of_isOpen_span ({1} : Finset R) f
      (Localization.Away f) (isOpen_span_of_one_mem (by simp))
    let hden₁₂ := P.hasDenominatorPower_of_isOpen_span ({f * f, 1} : Finset R) f
      (Localization.Away f) (isOpen_span_of_one_mem (by simp))
    GlueingSquare R
      (ratLoc P {f, 1} 1 hden₁) (ratLoc P {1} f hden₂) (ratLoc P {f * f, 1} f hden₁₂) :=
  GlueingSquare.of_simpleLaurent_of_isSheafyRing hs
    (isRationalCompletion_ratLoc P {f, 1} 1 (isOpen_span_of_one_mem (by simp)))
    (isRationalCompletion_ratLoc P {1} f (isOpen_span_of_one_mem (by simp)))
    (isRationalCompletion_ratLoc P {f * f, 1} f (isOpen_span_of_one_mem (by simp)))
    (continuous_algebraMap_laurentLeftAlgebra P f) (continuous_algebraMap_laurentRightAlgebra P f)

open Classical in
open scoped TauCeti.Huber.Laurent in
/-- For any complete Hausdorff sheafy Tate ring `R`, pair of definition `P`, and `f : R`, there
exist models `R₁`, `R₂`, `R₁₂` of `R⟨f, 1/1⟩`, `R⟨1/f⟩`, and `R⟨f², 1/f⟩` (constructed from
`ratLoc` and `laurentLeftAlgebra` / `laurentRightAlgebra`) that form a `GlueingSquare`. -/
theorem exists_simpleLaurent_glueingSquare {R : Type u} [CommRing R] [UniformSpace R]
    [IsUniformAddGroup R] [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R] [T0Space R]
    (hs : IsSheafyRing R) (P : PairOfDefinition R) (f : R) :
    ∃ (R₁ R₂ R₁₂ : Type u) (_ : CommRing R₁) (_ : CommRing R₂) (_ : CommRing R₁₂)
      (_ : TopologicalSpace R₁) (_ : TopologicalSpace R₂) (_ : TopologicalSpace R₁₂)
      (_ : Algebra R R₁) (_ : Algebra R R₂) (_ : Algebra R R₁₂)
      (_ : Algebra R₁ R₁₂) (_ : Algebra R₂ R₁₂)
      (_ : IsScalarTower R R₁ R₁₂) (_ : IsScalarTower R R₂ R₁₂),
      IsRationalCompletion P {f, 1} 1 (isOpen_span_of_one_mem (by simp)) R₁ ∧
        IsRationalCompletion P {1} f (isOpen_span_of_one_mem (by simp)) R₂ ∧
        IsRationalCompletion P {f * f, 1} f (isOpen_span_of_one_mem (by simp)) R₁₂ ∧
        GlueingSquare R R₁ R₂ R₁₂ :=
  ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance,
    isRationalCompletion_ratLoc P {f, 1} 1 (isOpen_span_of_one_mem (by simp)),
    isRationalCompletion_ratLoc P {1} f (isOpen_span_of_one_mem (by simp)),
    isRationalCompletion_ratLoc P {f * f, 1} f (isOpen_span_of_one_mem (by simp)),
    GlueingSquare.of_simpleLaurent_ratLoc hs P f⟩

end RatLoc

end TauCeti.Huber

end
