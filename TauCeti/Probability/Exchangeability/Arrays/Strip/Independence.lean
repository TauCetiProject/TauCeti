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

For a separately exchangeable array, the columns in an infinite set `T` and the rows in a
set `S` are conditionally independent given their intersection `S ×ˢ T`. Thus the two
families of strips used in the hidden/visible array decomposition are independent given
the entire hidden block, not merely given a directing measure.

The proof first fixes a finite observation in the columns `T`. An injective column
reindexing into `T` fixes that observation and compresses the rows `S` into the intersection.
Kallenberg's contraction lemma gives conditional independence. Mathlib's extension from finite
observations then recovers the whole collection of columns.

## References

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

private theorem SeparatelyExchangeable.condIndepFun_finite_strip
    (hρ : SeparatelyExchangeable ρ fun p x ↦ x p) (S : Set ℕ)
    {T : Set ℕ} (hT : T.Infinite) {C : Set (ℕ × ℕ)} (hC : C.Finite)
    (hCT : C ⊆ Set.univ ×ˢ T) :
    C.domRestrict ⟂ᵢ[(S ×ˢ T).domRestrict, Set.measurable_restrict _; ρ]
      (S ×ˢ Set.univ).domRestrict := by
  obtain ⟨b, hb, hbC, hbT⟩ := hT.exists_injective_into_eqOn_of_finite
    (hC.image Prod.snd) (by rintro j ⟨p, hp, rfl⟩; exact (hCT hp).2)
  let R := S ×ˢ T
  let D := S ×ˢ (Set.univ : Set ℕ)
  let H : (ℕ × ℕ → α) → ℕ × ℕ → α := fun x p ↦ x (p.1, b p.2)
  have hH : Measurable H := measurable_blockReadOff id b
  have hlaw : ρ.map H = ρ := by
    simpa only [arrayBlock_apply, id_eq, Measure.map_id'] using
      hρ.map_arrayBlock_eq (fun p ↦ (measurable_pi_apply p).aemeasurable)
        Function.injective_id hb
  have hfixed : ∀ x, C.domRestrict (H x) = C.domRestrict x := by
    intro x
    funext c
    simp only [Set.domRestrict_apply, H, hbC c.1.2 ⟨c.1, c.2, rfl⟩]
  let K : (R → α) → D → α := fun y q ↦ y ⟨(q.1.1, b q.1.2), q.2.1, hbT _⟩
  have hK : Measurable K := Measurable.of_eval fun _ ↦ measurable_pi_apply _
  let W : (ℕ × ℕ → α) → D → α := K ∘ R.domRestrict
  have hW : Measurable W := hK.comp (Set.measurable_restrict R)
  have hWR : MeasurableSpace.comap W inferInstance ≤
      MeasurableSpace.comap (R.domRestrict (π := fun _ ↦ α)) inferInstance := by
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hK.comap_le
  have hRD : R ⊆ D := Set.prod_mono_right (Set.subset_univ T)
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
      exact Prod.ext (hfixed x).symm rfl
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

/-- The columns in an infinite set `T` and the rows in `S` are conditionally independent
given the entire intersection block. No infinitude assumption on `S` is needed. -/
theorem SeparatelyExchangeable.condIndepFun_strips
    (hρ : SeparatelyExchangeable ρ fun p x ↦ x p) (S : Set ℕ)
    {T : Set ℕ} (hT : T.Infinite) :
    (Set.univ ×ˢ T).domRestrict ⟂ᵢ[(S ×ˢ T).domRestrict, Set.measurable_restrict _; ρ]
      (S ×ˢ Set.univ).domRestrict := by
  classical
  let U := (Set.univ : Set ℕ) ×ˢ T
  -- Conditional independence is kernel independence for the conditional-expectation kernel,
  -- so Mathlib's process extension applies directly.
  apply Kernel.IndepFun.process_indepFun
    (fun p : U ↦ measurable_pi_apply p.1) (Set.measurable_restrict _)
  intro F
  let C : Set (ℕ × ℕ) := Subtype.val '' (F : Set U)
  have hC : C.Finite := F.finite_toSet.image Subtype.val
  have hCU : C ⊆ U := by rintro p ⟨q, _, rfl⟩; exact q.2
  have h := hρ.condIndepFun_finite_strip S hT hC hCU
  exact h.comp (Measurable.of_eval fun p : F ↦
    measurable_pi_apply (⟨p.1.1, ⟨p.1, p.2, rfl⟩⟩ : C)) measurable_id

/-- The joint law of the hidden block and its two crossing strips factors through the
product of the two strip kernels conditional on the hidden block. This allows the two
strip families to be sampled independently once that block is given. -/
theorem SeparatelyExchangeable.jointLaw_strips_eq_prod_condDistrib [Nonempty α]
    (hρ : SeparatelyExchangeable ρ fun p x ↦ x p) (S : Set ℕ)
    {T : Set ℕ} (hT : T.Infinite) :
    let R := (S ×ˢ T).domRestrict (π := fun _ ↦ α)
    let A := (Set.univ ×ˢ T).domRestrict (π := fun _ ↦ α)
    let B := (S ×ˢ Set.univ).domRestrict (π := fun _ ↦ α)
    ρ.map (fun x ↦ (R x, A x, B x)) =
      (Kernel.id ×ₖ (condDistrib A R ρ ×ₖ condDistrib B R ρ)) ∘ₘ ρ.map R := by
  exact (condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
    (Set.measurable_restrict _) (Set.measurable_restrict _)
    (Set.measurable_restrict _)).mp (hρ.condIndepFun_strips S hT)

end TauCeti.Probability
