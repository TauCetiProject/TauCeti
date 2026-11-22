/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Law.Realization

/-!
# Free additive convolution of compactly supported measures

For compactly supported probability measures `μ` and `ν` on `ℝ`, the **free additive
convolution** `μ ⊞ ν` is the law of `a + b`, where `a` and `b` are freely independent selfadjoint
elements of a C⋆-algebra with a state, with laws `μ` and `ν`. Such elements exist, as the
coordinate functions in a reduced free product of commutative C⋆-algebras, and the law of
`a + b` depends only on `μ` and `ν`, because freeness determines the joint distribution of `a` and
`b` from their individual moments.

This file defines `μ ⊞ ν` as `MeasureTheory.Measure.freeConv μ ν` and proves the basic laws of
the operation: it is again a compactly supported probability measure, with support in
`[α + γ, β + δ]` when `μ` and `ν` are supported in `[α, β]` and `[γ, δ]`; it is commutative and
associative; the point mass `δ_c` acts as the translation by `c`, so that `δ₀` is the identity;
and it commutes with dilations and translations. The characterizing theorem
`TauCeti.IsFreelyIndependentElements.law_add` computes the law of a sum of two free selfadjoint
elements in any C⋆-probability space.

## Main declarations

* `MeasureTheory.Measure.freeConv`: the free additive convolution `μ ⊞ ν`.
* `TauCeti.IsFreelyIndependentElements.law_add`: `μ_{a + b} = μ_a ⊞ μ_b` for free selfadjoint
  `a` and `b`.
* `MeasureTheory.Measure.freeConv_comm`, `MeasureTheory.Measure.freeConv_assoc`: commutativity
  and associativity.
* `MeasureTheory.Measure.freeConv_dirac`: `μ ⊞ δ_c` is the translate of `μ` by `c`.
* `MeasureTheory.Measure.map_mul_left_freeConv_map_mul_left`: compatibility with dilations.
* `MeasureTheory.Measure.support_freeConv_subset_Icc`: the support bound.

## Implementation notes

`freeConv μ ν` is chosen among the laws of `a + b` over free realizations of `μ` and `ν` on
C⋆-algebras in `Type`. When `μ` or `ν` is not a compactly supported probability measure there is
no such realization, and `freeConv μ ν = 0` by convention (`freeConv_of_not`). No notation is
introduced, since `⊞` already denotes biproducts in Mathlib.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 12.
* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, §3.1.
-/

public section

noncomputable section

open TauCeti PositiveLinearMap
open scoped ComplexOrder

namespace MeasureTheory.Measure

open Classical in
/-- The **free additive convolution** `μ ⊞ ν` of compactly supported probability measures `μ`
and `ν` on `ℝ`: the law `μ_{a + b}` of the sum of freely independent selfadjoint elements `a` and
`b` of a C⋆-algebra with a state, with laws `μ_a = μ` and `μ_b = ν`. Such elements exist
(`TauCeti.exists_isFreelyIndependentElements_law_eq`), and `μ_{a + b}` does not depend on their
choice (`TauCeti.IsFreelyIndependentElements.law_add`). If `μ` or `ν` is not a compactly
supported probability measure, `freeConv μ ν = 0` (`freeConv_of_not`). -/
def freeConv (μ ν : Measure ℝ) : Measure ℝ :=
  if h : ∃ ρ : Measure ℝ, ∃ (A : Type) (_ : CStarAlgebra A) (_ : PartialOrder A)
      (_ : StarOrderedRing A) (φ : A →ₚ[ℂ] ℂ) (a : Fin 2 → A), φ 1 = 1 ∧
        (∀ i, IsSelfAdjoint (a i)) ∧ IsFreelyIndependentElements φ.toLinearMap a ∧
          law φ (a 0) = μ ∧ law φ (a 1) = ν ∧ law φ (a 0 + a 1) = ρ then
    h.choose
  else 0

/-- The law of the sum of a free pair of selfadjoint elements is the free convolution of their
laws. This is `TauCeti.IsFreelyIndependentElements.law_add` for the family `a` itself. -/
private theorem freeConv_law_law {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {φ : A →ₚ[ℂ] ℂ} (hφ : φ 1 = 1) {a : Fin 2 → A}
    (ha : ∀ i, IsSelfAdjoint (a i)) (h : IsFreelyIndependentElements φ.toLinearMap a) :
    (law φ (a 0)).freeConv (law φ (a 1)) = law φ (a 0 + a 1) := by
  have := fun i => isProbabilityMeasure_law φ hφ (ha i)
  obtain ⟨B, _, _, _, ψ, b, hψ, hb, hfb, hlaw, -⟩ :=
    exists_isFreelyIndependentElements_law_eq (fun i => law φ (a i))
      fun i => isCompact_support_law φ (a i)
  have hex : ∃ ρ : Measure ℝ, ∃ (A : Type) (_ : CStarAlgebra A) (_ : PartialOrder A)
      (_ : StarOrderedRing A) (φ' : A →ₚ[ℂ] ℂ) (c : Fin 2 → A), φ' 1 = 1 ∧
        (∀ i, IsSelfAdjoint (c i)) ∧ IsFreelyIndependentElements φ'.toLinearMap c ∧
          law φ' (c 0) = law φ (a 0) ∧ law φ' (c 1) = law φ (a 1) ∧ law φ' (c 0 + c 1) = ρ :=
    ⟨_, B, _, _, _, ψ, b, hψ, hb, hfb, hlaw 0, hlaw 1, rfl⟩
  rw [freeConv, dite_eq_left hex]
  obtain ⟨C, _, _, _, ω, c, hω, hc, hfc, h0, h1, hρ⟩ := hex.choose_spec
  rw [← hρ]
  have hlaw' (i : Fin 2) : law ω (c i) = law φ (a i) := by
    fin_cases i
    · exact h0
    · exact h1
  have hc' : FreeAlgebra.lift ℂ c (FreeAlgebra.ι ℂ 0 + FreeAlgebra.ι ℂ 1) = c 0 + c 1 := by
    simp
  have ha' : FreeAlgebra.lift ℂ a (FreeAlgebra.ι ℂ 0 + FreeAlgebra.ι ℂ 1) = a 0 + a 1 := by
    simp
  have key := hfc.law_lift_eq_law_lift h hω hφ hc ha hlaw'
    (p := FreeAlgebra.ι ℂ 0 + FreeAlgebra.ι ℂ 1) (hc' ▸ (hc 0).add (hc 1))
    (ha' ▸ (ha 0).add (ha 1))
  rwa [hc', ha'] at key

end MeasureTheory.Measure

namespace TauCeti.IsFreelyIndependentElements

open MeasureTheory

/-- **The law of a sum of free elements is the free convolution of their laws.** If `c i` and
`c j`, for `i ≠ j`, are selfadjoint members of a freely independent family for a state `φ` on a
C⋆-algebra, then `μ_{c i + c j} = μ_{c i} ⊞ μ_{c j}`. -/
theorem law_add {ι A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {φ : A →ₚ[ℂ] ℂ} {c : ι → A} (h : IsFreelyIndependentElements φ.toLinearMap c) (hφ : φ 1 = 1)
    {i j : ι} (hij : i ≠ j) (hi : IsSelfAdjoint (c i)) (hj : IsSelfAdjoint (c j)) :
    law φ (c i + c j) = (law φ (c i)).freeConv (law φ (c j)) := by
  have he : Function.Injective ![i, j] := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [hij.symm]
  have ha (k : Fin 2) : IsSelfAdjoint ((c ∘ ![i, j]) k) := by
    fin_cases k
    · exact hi
    · exact hj
  simpa using (Measure.freeConv_law_law hφ ha (h.comp he)).symm

end TauCeti.IsFreelyIndependentElements

namespace MeasureTheory.Measure

/-- A free pair realizing two compactly supported probability measures, with spectra in their
supports. -/
private theorem exists_pair (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    ∃ (A : Type) (_ : CStarAlgebra A) (_ : PartialOrder A) (_ : StarOrderedRing A)
      (φ : A →ₚ[ℂ] ℂ) (a : Fin 2 → A), φ 1 = 1 ∧ (∀ i, IsSelfAdjoint (a i)) ∧
        IsFreelyIndependentElements φ.toLinearMap a ∧ law φ (a 0) = μ ∧ law φ (a 1) = ν ∧
          spectrum ℝ (a 0) ⊆ μ.support ∧ spectrum ℝ (a 1) ⊆ ν.support := by
  have : ∀ i, IsProbabilityMeasure (![μ, ν] i) := Fin.forall_fin_two.2 ⟨‹_›, ‹_›⟩
  obtain ⟨A, _, _, _, φ, a, hφ, ha, hfree, hlaw, hspec⟩ :=
    exists_isFreelyIndependentElements_law_eq ![μ, ν] (Fin.forall_fin_two.2 ⟨hμ, hν⟩)
  exact ⟨A, _, _, _, φ, a, hφ, ha, hfree, hlaw 0, hlaw 1, hspec 0, hspec 1⟩

/-- `freeConv μ ν` is the zero measure unless `μ` and `ν` are both compactly supported
probability measures. -/
theorem freeConv_of_not {μ ν : Measure ℝ}
    (h : ¬(IsProbabilityMeasure μ ∧ IsCompact μ.support ∧ IsProbabilityMeasure ν ∧
      IsCompact ν.support)) :
    μ.freeConv ν = 0 := by
  rw [freeConv, dite_eq_right]
  rintro ⟨ρ, A, _, _, _, φ, a, hφ, ha, -, rfl, rfl, -⟩
  exact h ⟨isProbabilityMeasure_law φ hφ (ha 0), isCompact_support_law φ (a 0),
    isProbabilityMeasure_law φ hφ (ha 1), isCompact_support_law φ (a 1)⟩

/-- The free convolution with the zero measure is zero. -/
@[simp]
theorem zero_freeConv (ν : Measure ℝ) : (0 : Measure ℝ).freeConv ν = 0 :=
  freeConv_of_not fun h => by simpa using h.1.measure_univ

/-- The free convolution with the zero measure is zero. -/
@[simp]
theorem freeConv_zero (μ : Measure ℝ) : μ.freeConv 0 = 0 :=
  freeConv_of_not fun h => by simpa using h.2.2.1.measure_univ

/-- The free convolution of compactly supported probability measures is a probability
measure. -/
theorem isProbabilityMeasure_freeConv {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    IsProbabilityMeasure (μ.freeConv ν) := by
  obtain ⟨A, _, _, _, φ, a, hφ, ha, hfree, rfl, rfl, -⟩ := exists_pair μ ν hμ hν
  rw [freeConv_law_law hφ ha hfree]
  exact isProbabilityMeasure_law φ hφ ((ha 0).add (ha 1))

/-- The free convolution of two measures has compact support. -/
theorem isCompact_support_freeConv (μ ν : Measure ℝ) : IsCompact (μ.freeConv ν).support := by
  by_cases h : IsProbabilityMeasure μ ∧ IsCompact μ.support ∧ IsProbabilityMeasure ν ∧
      IsCompact ν.support
  · obtain ⟨_, hμ, _, hν⟩ := h
    obtain ⟨A, _, _, _, φ, a, hφ, ha, hfree, rfl, rfl, -⟩ := exists_pair μ ν hμ hν
    rw [freeConv_law_law hφ ha hfree]
    exact isCompact_support_law φ _
  · simp [freeConv_of_not h]

/-- **Support bound.** If `μ` is supported in `[α, β]` and `ν` in `[γ, δ]`, then `μ ⊞ ν` is
supported in `[α + γ, β + δ]`. -/
theorem support_freeConv_subset_Icc {μ ν : Measure ℝ} {α β γ δ : ℝ}
    (hμ : μ.support ⊆ Set.Icc α β) (hν : ν.support ⊆ Set.Icc γ δ) :
    (μ.freeConv ν).support ⊆ Set.Icc (α + γ) (β + δ) := by
  by_cases h : IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν
  swap
  · simp [freeConv_of_not fun h' => h ⟨h'.1, h'.2.2.1⟩]
  obtain ⟨_, _⟩ := h
  obtain ⟨A, _, _, _, φ, a, hφ, ha, hfree, rfl, rfl, h0, h1⟩ :=
    exists_pair _ _ (isCompact_Icc.of_isClosed_subset isClosed_support hμ)
      (isCompact_Icc.of_isClosed_subset isClosed_support hν)
  rw [freeConv_law_law hφ ha hfree]
  refine (support_law_subset_spectrum φ _).trans fun x hx => ?_
  have h0 := h0.trans hμ
  have h1 := h1.trans hν
  have hl : algebraMap ℝ A (α + γ) ≤ a 0 + a 1 := by
    rw [map_add]
    exact add_le_add ((algebraMap_le_iff_le_spectrum (ha 0)).2 fun y hy => (h0 hy).1)
      ((algebraMap_le_iff_le_spectrum (ha 1)).2 fun y hy => (h1 hy).1)
  have hu : a 0 + a 1 ≤ algebraMap ℝ A (β + δ) := by
    rw [map_add]
    exact add_le_add ((le_algebraMap_iff_spectrum_le (ha 0)).2 fun y hy => (h0 hy).2)
      ((le_algebraMap_iff_spectrum_le (ha 1)).2 fun y hy => (h1 hy).2)
  exact ⟨(algebraMap_le_iff_le_spectrum ((ha 0).add (ha 1))).1 hl x hx,
    (le_algebraMap_iff_spectrum_le ((ha 0).add (ha 1))).1 hu x hx⟩

/-- Free convolution is commutative. -/
theorem freeConv_comm (μ ν : Measure ℝ) : μ.freeConv ν = ν.freeConv μ := by
  by_cases h : IsProbabilityMeasure μ ∧ IsCompact μ.support ∧ IsProbabilityMeasure ν ∧
      IsCompact ν.support
  · obtain ⟨_, hμ, _, hν⟩ := h
    obtain ⟨A, _, _, _, φ, a, hφ, ha, hfree, rfl, rfl, -⟩ := exists_pair μ ν hμ hν
    rw [freeConv_law_law hφ ha hfree, ← hfree.law_add hφ one_ne_zero (ha 1) (ha 0), add_comm]
  · rw [freeConv_of_not h, freeConv_of_not fun h' => h ⟨h'.2.2.1, h'.2.2.2, h'.1, h'.2.1⟩]

/-- Free convolution is associative. -/
theorem freeConv_assoc (μ ν ρ : Measure ℝ) :
    (μ.freeConv ν).freeConv ρ = μ.freeConv (ν.freeConv ρ) := by
  by_cases hμ : IsProbabilityMeasure μ ∧ IsCompact μ.support
  swap
  · rw [freeConv_of_not (μ := μ) (ν := ν) fun h => hμ ⟨h.1, h.2.1⟩, zero_freeConv,
      freeConv_of_not fun h => hμ ⟨h.1, h.2.1⟩]
  by_cases hν : IsProbabilityMeasure ν ∧ IsCompact ν.support
  swap
  · rw [freeConv_of_not (μ := μ) (ν := ν) fun h => hν ⟨h.2.2.1, h.2.2.2⟩, zero_freeConv,
      freeConv_of_not (μ := ν) (ν := ρ) fun h => hν ⟨h.1, h.2.1⟩, freeConv_zero]
  by_cases hρ : IsProbabilityMeasure ρ ∧ IsCompact ρ.support
  swap
  · rw [freeConv_of_not (ν := ρ) fun h => hρ ⟨h.2.2.1, h.2.2.2⟩,
      freeConv_of_not (μ := ν) (ν := ρ) fun h => hρ ⟨h.2.2.1, h.2.2.2⟩, freeConv_zero]
  obtain ⟨_, hμ⟩ := hμ
  obtain ⟨_, hν⟩ := hν
  obtain ⟨_, hρ⟩ := hρ
  have : ∀ i, IsProbabilityMeasure (![μ, ν, ρ] i) := by
    intro i
    fin_cases i <;> assumption
  obtain ⟨A, _, _, _, φ, a, hφ, ha, hfree, hlaw, -⟩ :=
    exists_isFreelyIndependentElements_law_eq ![μ, ν, ρ] (by intro i; fin_cases i <;> assumption)
  -- Grouping the three free elements as `{0, 1}, {2}` and as `{0}, {1, 2}` gives free pairs.
  have hmem (g : Fin 3 → Fin 2) (i : Fin 3) : a i ∈ Algebra.adjoin ℂ (a '' (g ⁻¹' {g i})) :=
    Algebra.subset_adjoin ⟨i, rfl, rfl⟩
  have hl : IsFreelyIndependentElements φ.toLinearMap ![a 0 + a 1, a 2] := by
    refine hfree.of_mem_adjoin_image_fiber hφ ![0, 0, 1] fun k => ?_
    fin_cases k
    · exact add_mem (hmem ![0, 0, 1] 0) (hmem ![0, 0, 1] 1)
    · exact hmem ![0, 0, 1] 2
  have hr : IsFreelyIndependentElements φ.toLinearMap ![a 0, a 1 + a 2] := by
    refine hfree.of_mem_adjoin_image_fiber hφ ![0, 1, 1] fun k => ?_
    fin_cases k
    · exact hmem ![0, 1, 1] 0
    · exact add_mem (hmem ![0, 1, 1] 1) (hmem ![0, 1, 1] 2)
  have h01 := hfree.law_add hφ (by decide : (0 : Fin 3) ≠ 1) (ha 0) (ha 1)
  have h12 := hfree.law_add hφ (by decide : (1 : Fin 3) ≠ 2) (ha 1) (ha 2)
  have hl' := hl.law_add hφ (by decide : (0 : Fin 2) ≠ 1) ((ha 0).add (ha 1)) (ha 2)
  have hr' := hr.law_add hφ (by decide : (0 : Fin 2) ≠ 1) (ha 0) ((ha 1).add (ha 2))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hl' hr'
  have h0 : law φ (a 0) = μ := hlaw 0
  have h1 : law φ (a 1) = ν := hlaw 1
  have h2 : law φ (a 2) = ρ := hlaw 2
  rw [← h0, ← h1, ← h2, ← h01, ← h12, ← hl', ← hr', add_assoc]

/-- The free convolution with a point mass `δ_c` is the translation by `c`. -/
theorem freeConv_dirac (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    (c : ℝ) : μ.freeConv (dirac c) = μ.map (· + c) := by
  obtain ⟨A, _, _, _, φ, a, hφ, ha, -, hlaw, -⟩ :=
    exists_isFreelyIndependentElements_law_eq (fun _ : Unit => μ) fun _ => hμ
  have hc : IsSelfAdjoint (algebraMap ℝ A c) := IsSelfAdjoint.algebraMap A (IsSelfAdjoint.all c)
  -- A scalar is free from any element.
  have hfree : IsFreelyIndependentElements φ.toLinearMap ![a (), algebraMap ℝ A c] := by
    refine (isFreelyIndependentElements_domRestrict_iff (s := {0}) hφ fun i hi => ?_).1
      (isFreelyIndependentElements_of_subsingleton _ _)
    fin_cases i
    · exact absurd rfl hi
    · exact ⟨c, (IsScalarTower.algebraMap_apply ℝ ℂ A c).symm ▸ rfl⟩
  have hdirac : law φ (algebraMap ℝ A c) = dirac c := by
    simpa [map_const, hlaw] using law_smul_add_algebraMap φ (ha ()) 0 c
  have htrans : law φ (a () + algebraMap ℝ A c) = μ.map (· + c) := by
    simpa [hlaw] using law_smul_add_algebraMap φ (ha ()) 1 c
  simpa [hlaw, hdirac, htrans] using
    (hfree.law_add hφ (by decide : (0 : Fin 2) ≠ 1) (ha ()) hc).symm

/-- The free convolution of a point mass `δ_c` with `μ` is the translation of `μ` by `c`. -/
theorem dirac_freeConv (c : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) : (dirac c).freeConv μ = μ.map (c + ·) := by
  rw [freeConv_comm, freeConv_dirac μ hμ c]
  simp_rw [add_comm _ c]

/-- `δ₀` is a right identity for free convolution of compactly supported probability
measures. -/
@[simp]
theorem freeConv_dirac_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) :
    μ.freeConv (dirac 0) = μ := by
  simp [freeConv_dirac μ hμ 0]

/-- `δ₀` is a left identity for free convolution of compactly supported probability measures. -/
@[simp]
theorem dirac_zero_freeConv (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) :
    (dirac 0).freeConv μ = μ := by
  rw [freeConv_comm, freeConv_dirac_zero μ hμ]

/-- The free convolution of two point masses is the point mass at the sum. -/
@[simp]
theorem dirac_freeConv_dirac (x y : ℝ) : (dirac x).freeConv (dirac y) = dirac (x + y) := by
  have hx : IsCompact (dirac x).support :=
    isCompact_singleton.of_isClosed_subset isClosed_support (support_subset_of_isClosed
      isClosed_singleton ((mem_ae_dirac_iff (measurableSet_singleton x)).2 rfl))
  rw [freeConv_dirac _ hx y, map_dirac' (measurable_add_const y)]

/-- Free convolution commutes with dilations: `(μ ⊞ ν) ∘ (r ·)⁻¹ = μ ∘ (r ·)⁻¹ ⊞ ν ∘ (r ·)⁻¹`. -/
theorem map_freeConv_const_mul (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) (r : ℝ) :
    (μ.freeConv ν).map (r * ·) = (μ.map (r * ·)).freeConv (ν.map (r * ·)) := by
  obtain ⟨A, _, _, _, φ, a, hφ, ha, hfree, rfl, rfl, -⟩ := exists_pair μ ν hμ hν
  have hsmul (i : Fin 2) : law φ (r • a i) = (law φ (a i)).map (r * ·) := by
    simpa using law_smul_add_algebraMap φ (ha i) r 0
  have hra (i : Fin 2) : IsSelfAdjoint (r • a i) := (IsSelfAdjoint.all r).smul (ha i)
  have hrfree : IsFreelyIndependentElements φ.toLinearMap fun i => r • a i :=
    isFreelyIndependentElements_iff.2 ((isFreelyIndependentElements_iff.1 hfree).mono fun i =>
      Algebra.adjoin_le
      (Set.singleton_subset_iff.2 (by
        rw [← Complex.coe_smul]
        exact Subalgebra.smul_mem _ (Algebra.self_mem_adjoin_singleton ℂ (a i)) _)))
  rw [← hfree.law_add hφ (by decide : (0 : Fin 2) ≠ 1) (ha 0) (ha 1), ← hsmul, ← hsmul,
    ← hrfree.law_add hφ (by decide : (0 : Fin 2) ≠ 1) (hra 0) (hra 1), ← smul_add]
  simpa using (law_smul_add_algebraMap φ ((ha 0).add (ha 1)) r 0).symm

/-- Free convolution commutes with translations: translating `μ ⊞ ν` by `c` is the free
convolution of the translate of `μ` with `ν`. -/
theorem map_freeConv_add_const (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) (c : ℝ) :
    (μ.freeConv ν).map (· + c) = (μ.map (· + c)).freeConv ν := by
  have := isProbabilityMeasure_freeConv hμ hν
  rw [← freeConv_dirac _ (isCompact_support_freeConv μ ν), ← freeConv_dirac μ hμ, freeConv_assoc,
    freeConv_assoc, freeConv_comm ν]

end MeasureTheory.Measure
