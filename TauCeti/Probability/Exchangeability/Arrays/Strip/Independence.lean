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
import Mathlib.Probability.Independence.Process.Basic

/-!
# Conditional independence of crossing array strips

For a separately exchangeable array, the columns in `T` and the rows in `S` are
conditionally independent given their intersection `S ×ˢ T` whenever either index set
is infinite. Thus the two
families of strips used in the hidden/visible array decomposition are independent given
the entire hidden block, not merely given a directing measure.

## References

* The finite-observation argument is adapted from
  `TauCeti.Probability.SeparatelyExchangeable.condIndepFun_domRestrict_compl_of_finite` in
  `TauCeti.Probability.Exchangeability.Arrays.Block.Independence`.
* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581–598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005,
  Lemma 1.3 and Chapter 7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
  {ρ : Measure (ℕ × ℕ → α)} [IsFiniteMeasure ρ]

private theorem SeparatelyExchangeable.condIndepFun_strip_of_reindexing
    (hρ : SeparatelyExchangeable ρ fun p x ↦ x p) (R D U : Set (ℕ × ℕ))
    (hRD : R ⊆ D)
    (hreindex : ∀ C : Set (ℕ × ℕ), C.Finite → C ⊆ U →
      ∃ a b : ℕ → ℕ, Function.Injective a ∧ Function.Injective b ∧
        (∀ p ∈ C, (a p.1, b p.2) = p) ∧ ∀ p ∈ D, (a p.1, b p.2) ∈ R) :
    U.domRestrict ⟂ᵢ[R.domRestrict, Set.measurable_restrict _; ρ] D.domRestrict := by
  classical
  -- Extend independence of finite observations to the entire strip.
  apply Kernel.IndepFun.process_indepFun
    (fun p : U ↦ measurable_pi_apply p.1) (Set.measurable_restrict _)
  intro F
  let C : Set (ℕ × ℕ) := Subtype.val '' (F : Set U)
  have hC : C.Finite := F.finite_toSet.image Subtype.val
  have hCU : C ⊆ U := by rintro p ⟨q, _, rfl⟩; exact q.2
  suffices h : C.domRestrict ⟂ᵢ[R.domRestrict, Set.measurable_restrict _; ρ]
      D.domRestrict by
    exact h.comp (Measurable.of_eval fun p : F ↦
      measurable_pi_apply (⟨p.1.1, ⟨p.1, p.2, rfl⟩⟩ : C)) measurable_id
  -- Fix the observed coordinates while moving the other strip into the conditioning block.
  obtain ⟨a, b, ha, hb, hfix, hinto⟩ := hreindex C hC hCU
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
  -- Contract the unchanged joint law, then pass to the intermediate conditioning block.
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

/-- The columns in `T` and the rows in `S` are conditionally independent given the entire
intersection block whenever at least one of `S` and `T` is infinite. -/
theorem SeparatelyExchangeable.condIndepFun_colStrip_rowStrip
    (hρ : SeparatelyExchangeable ρ fun p x ↦ x p) (S : Set ℕ)
    {T : Set ℕ} (hST : S.Infinite ∨ T.Infinite) :
    (Set.univ ×ˢ T).domRestrict ⟂ᵢ[(S ×ˢ T).domRestrict, Set.measurable_restrict _; ρ]
      (S ×ˢ Set.univ).domRestrict := by
  rcases hST with hS | hT
  · apply CondIndepFun.symm
    refine hρ.condIndepFun_strip_of_reindexing (S ×ˢ T) (Set.univ ×ˢ T)
      (S ×ˢ Set.univ) (Set.prod_mono_left (Set.subset_univ S)) ?_
    intro C hC hCS
    obtain ⟨a, ha, haC, haS⟩ := hS.exists_injective_into_eqOn_of_finite
      (hC.image Prod.fst) (by rintro i ⟨p, hp, rfl⟩; exact (hCS hp).1)
    exact ⟨a, id, ha, Function.injective_id,
      fun p hp ↦ Prod.ext (haC p.1 ⟨p, hp, rfl⟩) rfl,
      fun p hp ↦ ⟨haS _, hp.2⟩⟩
  · refine hρ.condIndepFun_strip_of_reindexing (S ×ˢ T) (S ×ˢ Set.univ)
      (Set.univ ×ˢ T) (Set.prod_mono_right (Set.subset_univ T)) ?_
    intro C hC hCT
    obtain ⟨b, hb, hbC, hbT⟩ := hT.exists_injective_into_eqOn_of_finite
      (hC.image Prod.snd) (by rintro j ⟨p, hp, rfl⟩; exact (hCT hp).2)
    exact ⟨id, b, Function.injective_id, hb,
      fun p hp ↦ Prod.ext rfl (hbC p.2 ⟨p, hp, rfl⟩),
      fun p hp ↦ ⟨hp.1, hbT _⟩⟩

end TauCeti.Probability
