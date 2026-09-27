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
# Local conditional independence of finite array blocks

For a separately exchangeable array, any finite block of entries inside an infinite rectangle is
conditionally independent of the entries outside the block given the other entries of the
rectangle. This is the finite-block form of the local conditional-independence principle used to
factor the visible-cell laws in the Aldous--Hoover representation.

The block whose law is controlled may be a sub-block of the hidden block: if `C` is a finite set
of cells in the rectangle and `B ⊆ C`, then `B` is conditionally independent of the complement of
the hidden block `C` given the reservoir, the rectangle with `C` removed. Nothing forces `B` to
be all of `C`, and `C` need not be minimal, so the reservoir -- the rest of the rectangle -- may be
chosen coarsely as long as it still avoids `B`.

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

/-- Conditional independence of all entries in `U` follows when every finite subset can be fixed
by a reindexing that moves `D` into the intermediate conditioning set `R`. -/
theorem SeparatelyExchangeable.condIndepFun_domRestrict_of_finite_reindexing
    (hρ : SeparatelyExchangeable ρ fun p x ↦ x p) (R D U : Set (ℕ × ℕ))
    (hRD : R ⊆ D)
    (hreindex : ∀ C : Set (ℕ × ℕ), C.Finite → C ⊆ U →
      ∃ a b : ℕ → ℕ, Function.Injective a ∧ Function.Injective b ∧
        (∀ p ∈ C, (a p.1, b p.2) = p) ∧ ∀ p ∈ D, (a p.1, b p.2) ∈ R) :
    U.domRestrict ⟂ᵢ[R.domRestrict, Set.measurable_restrict _; ρ] D.domRestrict := by
  classical
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
  obtain ⟨a, b, ha, hb, hfix, hinto⟩ := hreindex C hC hCU
  exact hρ.condIndepFun_domRestrict_of_reindexing C R D hRD a b ha hb hfix hinto

/-- **A finite block of array entries in an infinite rectangle is conditionally independent of
everything outside a finite block containing it, given the rest of the rectangle.**

The entries that are read off are the sub-block `B ⊆ C`, while the conditioning set is the
rectangle with the whole hidden block `C` removed, and the events compared are those of the
complement of `C`. Taking `B = C` recovers the statement that one finite block is conditionally
independent of the rest of the array given the other entries of the rectangle; taking `B` to be
a proper sub-block of `C` says the same for a part of the hidden block, with a reservoir that is
allowed to hide more of the hidden block than that part needs.

`C` is the only set that has to be finite: `B` needs no finiteness hypothesis of its own, since
`B ⊆ C`. -/
theorem SeparatelyExchangeable.condIndepFun_domRestrict_subblock_compl_of_finite_block_of_subset
    (hρ : SeparatelyExchangeable ρ fun p x ↦ x p) {S T : Set ℕ} (hS : S.Infinite)
    (hT : T.Infinite) {B C : Set (ℕ × ℕ)} (hC : C.Finite) (hBsub : B ⊆ C)
    (hCsub : C ⊆ S ×ˢ T) :
    B.domRestrict ⟂ᵢ[((S ×ˢ T) \ C).domRestrict, Set.measurable_restrict _; ρ]
      Cᶜ.domRestrict := by
  have hFS : Prod.fst '' C ⊆ S := by
    rintro i ⟨p, hp, rfl⟩
    exact (hCsub hp).1
  have hGT : Prod.snd '' C ⊆ T := by
    rintro j ⟨p, hp, rfl⟩
    exact (hCsub hp).2
  -- Each axis of the rectangle reindexes into itself while fixing every coordinate used by `C`.
  obtain ⟨a, ha, haF, haS⟩ := hS.exists_injective_into_eqOn_of_finite
    (hC.image Prod.fst) hFS
  obtain ⟨b, hb, hbG, hbT⟩ := hT.exists_injective_into_eqOn_of_finite
    (hC.image Prod.snd) hGT
  refine hρ.condIndepFun_domRestrict_of_finite_reindexing (S ×ˢ T \ C) Cᶜ B
    (Set.sdiff_subset_compl _ _) ?_
  intro C' _ hC'B
  refine ⟨a, b, ha, hb, fun p hp => ?_, fun p hp => ?_⟩
  · exact Prod.ext (haF p.1 ⟨p, hBsub (hC'B hp), rfl⟩) (hbG p.2 ⟨p, hBsub (hC'B hp), rfl⟩)
  · refine ⟨⟨haS p.1, hbT p.2⟩, fun hc ↦ hp ?_⟩
    have hp1 : p.1 = a p.1 :=
      ha (haF (a p.1) ⟨(a p.1, b p.2), hc, rfl⟩).symm
    have hp2 : p.2 = b p.2 :=
      hb (hbG (b p.2) ⟨(a p.1, b p.2), hc, rfl⟩).symm
    have hpEq : p = (a p.1, b p.2) := Prod.ext hp1 hp2
    exact hpEq ▸ hc

end TauCeti.Probability

end

end
