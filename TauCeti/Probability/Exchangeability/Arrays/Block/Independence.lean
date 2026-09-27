/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Block.Basic
public import Mathlib.Probability.Independence.Conditional
import TauCeti.Probability.Independence.Conditional
import TauCeti.MeasureTheory.Function.ConditionalExpectation
import TauCeti.Data.Set.Infinite

/-!
# Local conditional independence of finite array blocks

For a separately exchangeable array, any finite block of entries inside an infinite rectangle is
conditionally independent of the entries outside the block given the other entries of the
rectangle. This is the finite-block form of the local conditional-independence principle used to
factor the visible-cell laws in the Aldous--Hoover representation.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
  {ρ : Measure (ℕ × ℕ → α)} [IsFiniteMeasure ρ]

/-- Conditional independence obtained by reindexing an array while fixing the observed entries and
moving the remaining entries into an intermediate conditioning set. -/
theorem SeparatelyExchangeable.condIndepFun_domRestrict_of_reindexing
    (hρ : SeparatelyExchangeable ρ fun p x ↦ x p) (C R D : Set (ℕ × ℕ))
    (hRD : R ⊆ D) (a b : ℕ → ℕ) (ha : Function.Injective a) (hb : Function.Injective b)
    (hfix : ∀ p ∈ C, (a p.1, b p.2) = p) (hinto : ∀ p ∈ D, (a p.1, b p.2) ∈ R) :
    C.domRestrict ⟂ᵢ[R.domRestrict, Set.measurable_restrict _; ρ] D.domRestrict := by
  let H : (ℕ × ℕ → α) → ℕ × ℕ → α := fun x p ↦ x (a p.1, b p.2)
  have hH : Measurable H := measurable_blockReadOff a b
  have hlaw : ρ.map H = ρ := by
    simpa only [Measure.map_id'] using
      hρ.map_arrayBlock_eq (fun p ↦ (measurable_pi_apply p).aemeasurable) ha hb
  have hfixed : ∀ x, C.domRestrict (H x) = C.domRestrict x := by
    intro x
    funext c
    simp only [Set.domRestrict_apply, H, hfix c.1 c.2]
  let K : (R → α) → D → α := fun y q ↦ y ⟨(a q.1.1, b q.1.2), hinto q.1 q.2⟩
  have hK : Measurable K := Measurable.of_eval fun _ ↦ measurable_pi_apply _
  let W : (ℕ × ℕ → α) → D → α := K ∘ R.domRestrict
  have hW_eq : W = fun x ↦ D.domRestrict (H x) := by
    funext x q
    simp only [W, K, Function.comp_apply, Set.domRestrict_apply, H]
  have hW : Measurable W := hK.comp (Set.measurable_restrict R)
  have hWR : MeasurableSpace.comap W inferInstance ≤
      MeasurableSpace.comap (R.domRestrict (π := fun _ ↦ α)) inferInstance := by
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hK.comap_le
  have hRD' : MeasurableSpace.comap (R.domRestrict (π := fun _ ↦ α)) inferInstance ≤
      MeasurableSpace.comap (D.domRestrict (π := fun _ ↦ α))
        (inferInstance : MeasurableSpace (D → α)) := by
    rw [← Set.domRestrict₂_comp_domRestrict hRD, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (Set.measurable_restrict₂ hRD).comap_le
  have hpair : ρ.map (fun x ↦ (C.domRestrict x, W x)) =
      ρ.map (fun x ↦ (C.domRestrict x, D.domRestrict x)) := by
    have hcomp : (fun x ↦ (C.domRestrict x, W x)) =
        (fun x ↦ (C.domRestrict x, D.domRestrict x)) ∘ H := by
      funext x
      exact Prod.ext (hfixed x).symm (congrFun hW_eq x)
    rw [hcomp, ← Measure.map_map (by fun_prop) hH, hlaw]
  rw [condIndepFun_iff_condIndep]
  refine CondIndep.symm ?_
  refine condIndep_of_indicator_condExp_eq (Set.measurable_restrict D).comap_le
    (Set.measurable_restrict R).comap_le (Set.measurable_restrict C).comap_le ?_
  rintro _ ⟨A, hA, rfl⟩
  rw [sup_eq_left.mpr hRD']
  have hcontr := condExp_indicator_eq_of_law_eq_of_comap_le C.domRestrict W D.domRestrict
    (Set.measurable_restrict C) hW (Set.measurable_restrict D) hpair (hWR.trans hRD') hA
  exact hcontr.trans (TauCeti.MeasureTheory.condExp_ae_eq_of_le_of_le hWR hRD'
    (Set.measurable_restrict D).comap_le hcontr).symm

/-- A finite set of array entries in an infinite rectangle is conditionally independent of the
rest of the array given the other entries of that rectangle. -/
theorem SeparatelyExchangeable.condIndepFun_domRestrict_compl_of_finite
    (hρ : SeparatelyExchangeable ρ fun p x ↦ x p) {S T : Set ℕ} (hS : S.Infinite)
    (hT : T.Infinite) {C : Set (ℕ × ℕ)} (hC : C.Finite) (hCsub : C ⊆ S ×ˢ T) :
    C.domRestrict ⟂ᵢ[(S ×ˢ T \ C).domRestrict, Set.measurable_restrict _; ρ]
      Cᶜ.domRestrict := by
  let F : Set ℕ := Prod.fst '' C
  let G : Set ℕ := Prod.snd '' C
  have hFS : F ⊆ S := by
    rintro i ⟨p, hp, rfl⟩
    exact (hCsub hp).1
  have hGT : G ⊆ T := by
    rintro j ⟨p, hp, rfl⟩
    exact (hCsub hp).2
  -- Reindex each axis into the rectangle while fixing every coordinate used by the block.
  obtain ⟨a, ha, haF, haS⟩ := hS.exists_injective_into_eqOn_of_finite
    (hC.image Prod.fst) hFS
  obtain ⟨b, hb, hbG, hbT⟩ := hT.exists_injective_into_eqOn_of_finite
    (hC.image Prod.snd) hGT
  let R : Set (ℕ × ℕ) := S ×ˢ T \ C
  let D : Set (ℕ × ℕ) := Cᶜ
  have hRD : R ⊆ D := Set.sdiff_subset_compl _ _
  have hfixed : ∀ c ∈ C, (a c.1, b c.2) = c := by
    intro c hc
    exact Prod.ext (haF c.1 ⟨c, hc, rfl⟩) (hbG c.2 ⟨c, hc, rfl⟩)
  have hmem : ∀ q ∈ D, (a q.1, b q.2) ∈ R := by
    intro q hq
    refine ⟨⟨haS _, hbT _⟩, fun hc ↦ hq ?_⟩
    have hq1 : q.1 = a q.1 :=
      ha (haF (a q.1) ⟨(a q.1, b q.2), hc, rfl⟩).symm
    have hq2 : q.2 = b q.2 :=
      hb (hbG (b q.2) ⟨(a q.1, b q.2), hc, rfl⟩).symm
    have hqeq : q = (a q.1, b q.2) := Prod.ext hq1 hq2
    exact hqeq ▸ hc
  exact hρ.condIndepFun_domRestrict_of_reindexing C R D hRD a b ha hb hfixed hmem

end TauCeti.Probability

end

end
