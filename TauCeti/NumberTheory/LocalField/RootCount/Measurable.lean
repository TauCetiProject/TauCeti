/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.FieldTheory.IntermediateField.RootCount
public import TauCeti.MeasureTheory.Group.LocalFieldScaling
public import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
public import TauCeti.RingTheory.Valuation.ValuativeRel.Extension
import TauCeti.NumberTheory.LocalField.IntegerRing.Basic
import TauCeti.RingTheory.Polynomial.Monic.Roots
import TauCeti.Topology.Algebra.Polynomial.Basic
import TauCeti.Topology.Algebra.ValuativeRel.ContinuousRingHom

/-!
# Measurability of root counts over a nonarchimedean local field

Let `L / K` be an extension of nonarchimedean local fields. A monic polynomial of degree `n` over
`K` is its coefficient vector `a : Fin n → K`, through `TauCeti.Polynomial.monicOfCoeff`. This file
proves that the number of roots of `monicOfCoeff a` in `L`, counted with multiplicity, is a
measurable function of `a` on the integer box `𝒪[K] ^ n`: for every `k`, the integral coefficient
vectors whose polynomial has at least `k` roots in `L` form a compact set.

This is what lets root counts be integrated over coefficient space, as in Serre's proof of his mass
formula, where the root count in each totally ramified extension is integrated over the Eisenstein
polynomials. The statement holds at every integral coefficient vector, separable or not: at an
inseparable polynomial the root count need not be locally constant, but it is still measurable.

## Main results

* `TauCeti.isCompact_setOf_le_card_aroots`: the integral coefficient vectors whose polynomial has
  at least `k` roots in `L` form a compact subset of `Fin n → K`.
* `TauCeti.aemeasurable_card_aroots`: the root count in `L` is almost everywhere measurable for
  every measure carried by the integer box.
* `IntermediateField.aemeasurable_rootCount`: the same for the root count
  `IntermediateField.rootCount` in a finite intermediate field of any extension of `K`.

## Implementation notes

The roots in `L` of a monic polynomial `p` over `𝒪[K]` lie in `𝒪[L]`
(`TauCeti.aroots_eq_map_roots_integerRing`), and `p` has at least `k` of them exactly when it
factors over `𝒪[L]` as `∏ j, (X - x j) * q` with `q` monic of degree `n - k`. The tuples
`(x, q, p)` satisfying this form a closed subset of a product of copies of `𝒪[L]` and `𝒪[K]`,
which is compact, and the set of the statement is its image under the projection to `p`.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, §2.
-/

public section

open Polynomial ValuativeRel MeasureTheory

namespace TauCeti

open TauCeti.Polynomial (monicOfCoeff monic_monicOfCoeff natDegree_monicOfCoeff map_monicOfCoeff
  continuous_coeff_monicOfCoeff continuous_coeff_prod_X_sub_C)

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

section Extension

variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] in
/-- For integral coefficients `α`, the roots of `monicOfCoeff α` in `L` are its roots in `𝒪[L]`. -/
private theorem card_aroots_monicOfCoeff_coe {n : ℕ} (α : Fin n → 𝒪[K]) :
    ((monicOfCoeff fun i ↦ (α i : K)).aroots L).card =
      ((monicOfCoeff α).map (algebraMap 𝒪[K] 𝒪[L])).roots.card := by
  have hmap : (monicOfCoeff α).map (algebraMap 𝒪[K] K) = monicOfCoeff fun i ↦ (α i : K) := by
    rw [map_monicOfCoeff]
    simp only [Algebra.algebraMap_ofSubsemiring_apply]
  rw [← hmap, aroots_eq_map_roots_integerRing L (monic_monicOfCoeff α), Multiset.card_map]

/-- **The superlevel sets of the root count are compact.** For an extension `L / K` of
nonarchimedean local fields, the coefficient vectors `a` in the integer box `𝒪[K] ^ n` whose monic
polynomial `monicOfCoeff a` has at least `k` roots in `L`, counted with multiplicity, form a compact
subset of `Fin n → K`. -/
theorem isCompact_setOf_le_card_aroots (n k : ℕ) :
    IsCompact {a : Fin n → K | a ∈ integerBox K (Fin n) ∧
      k ≤ ((monicOfCoeff a).aroots L).card} := by
  set φ := algebraMap 𝒪[K] 𝒪[L]
  have := finite_of_valuativeExtension K L
  have hφ : Continuous φ := continuous_algebraMap_integerRing K L
  -- The factorizations `∏ j, (X - x j) * q = p` over `𝒪[L]`, recorded by their coefficients.
  set C : Set (((Fin k → 𝒪[L]) × (Fin (n - k) → 𝒪[L])) × (Fin n → 𝒪[K])) :=
    {z | (∏ j, (X - Polynomial.C (z.1.1 j))) * monicOfCoeff z.1.2 = (monicOfCoeff z.2).map φ}
  have hC : IsClosed C := by
    simp only [C, Polynomial.ext_iff, Set.ofPred_forall]
    refine isClosed_iInter fun i ↦ isClosed_eq ?_ ?_
    · refine continuous_iff_continuousAt.2 fun z ↦ continuousAt_coeff_mul
        (fun j _ ↦ ((continuous_coeff_prod_X_sub_C _ j).comp
          (continuous_fst.comp continuous_fst)).continuousAt)
        fun j _ ↦ ((continuous_coeff_monicOfCoeff j).comp
          (continuous_snd.comp continuous_fst)).continuousAt
    · simp only [map_monicOfCoeff]
      exact (continuous_coeff_monicOfCoeff i).comp
        (continuous_pi fun j ↦ hφ.comp ((continuous_apply j).comp continuous_snd))
  -- `C` is closed in a compact space, and the set of the statement is its image.
  convert hC.isCompact.image (f := fun z i ↦ (z.2 i : K)) (continuous_pi fun i ↦
    continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)) using 1
  have hfac (α : Fin n → 𝒪[K]) := Monic.le_card_roots_iff_exists_prod_mul_monicOfCoeff_eq (k := k)
    ((monic_monicOfCoeff α).map φ) (by rw [(monic_monicOfCoeff α).natDegree_map,
      natDegree_monicOfCoeff])
  ext a
  constructor
  · rintro ⟨ha, hcard⟩
    set α : Fin n → 𝒪[K] := fun i ↦ ⟨a i, mem_integerBox.1 ha i⟩
    rw [show a = fun i ↦ (α i : K) from rfl, card_aroots_monicOfCoeff_coe] at hcard
    obtain ⟨x, b, h⟩ := (hfac α).1 hcard
    exact ⟨((x, b), α), h, rfl⟩
  · rintro ⟨⟨⟨x, b⟩, α⟩, h, rfl⟩
    refine ⟨mem_integerBox.2 fun i ↦ (α i).2, ?_⟩
    rw [card_aroots_monicOfCoeff_coe]
    exact (hfac α).2 ⟨x, b, h⟩

/-- **The root count is measurable on the integer box.** For an extension `L / K` of
nonarchimedean local fields and a measure `ν` on `Fin n → K` carried by the integer box
`𝒪[K] ^ n`, the number of roots in `L` of `monicOfCoeff a`, counted with multiplicity, is an almost
everywhere measurable function of `a`. -/
theorem aemeasurable_card_aroots {n : ℕ} [MeasurableSpace (Fin n → K)]
    [OpensMeasurableSpace (Fin n → K)] {ν : Measure (Fin n → K)}
    (hν : ∀ᵐ a ∂ν, a ∈ integerBox K (Fin n)) :
    AEMeasurable (fun a ↦ ((monicOfCoeff a).aroots L).card) ν := by
  classical
  set B := integerBox K (Fin n)
  set f := fun a : Fin n → K ↦ ((monicOfCoeff a).aroots L).card
  have hS (m : ℕ) : MeasurableSet {a | a ∈ B ∧ m ≤ f a} :=
    (isCompact_setOf_le_card_aroots L n m).measurableSet
  refine ⟨B.piecewise f 0, measurable_to_countable' fun m ↦ ?_, ?_⟩
  · -- On the integer box, `f a = m` is the difference of two compact superlevel sets.
    have : B.piecewise f 0 ⁻¹' {m} =
        ({a | a ∈ B ∧ m ≤ f a} \ {a | a ∈ B ∧ m + 1 ≤ f a}) ∪ (Bᶜ ∩ {_a | 0 = m}) := by
      ext a
      by_cases ha : a ∈ B
      · simp [ha]
        omega
      · simp [ha]
    rw [this]
    exact ((hS m).diff (hS (m + 1))).union
      (isCompact_integerBox.measurableSet.compl.inter (MeasurableSet.const _))
  · filter_upwards [hν] with a ha
    simp [ha]

end Extension

/-- **The root count in a finite subextension is measurable on the integer box.** For a finite
intermediate field `L` of an extension `Ω / K` and a measure `ν` on `Fin n → K` carried by the
integer box `𝒪[K] ^ n`, the root count `L.rootCount a` is an almost everywhere measurable function
of `a`. No topology or valuation on `Ω` is needed: `L` carries its canonical structure of a
nonarchimedean local field. -/
theorem _root_.IntermediateField.aemeasurable_rootCount {Ω : Type*} [Field Ω] [Algebra K Ω]
    (L : IntermediateField K Ω) [FiniteDimensional K L] {n : ℕ} [MeasurableSpace (Fin n → K)]
    [OpensMeasurableSpace (Fin n → K)] {ν : Measure (Fin n → K)}
    (hν : ∀ᵐ a ∂ν, a ∈ integerBox K (Fin n)) :
    AEMeasurable (fun a ↦ L.rootCount a) ν := by
  let _ := finiteIntermediateFieldValuativeRel K Ω L
  let _ := finiteIntermediateFieldTopology K Ω L
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω L
  have := finiteIntermediateField_valuativeExtension K Ω L
  simpa only [IntermediateField.rootCount_def] using aemeasurable_card_aroots L hν

end TauCeti
