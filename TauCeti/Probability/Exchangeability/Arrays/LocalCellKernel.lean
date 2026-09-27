/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.CellIndependence
public import TauCeti.Probability.Kernel.Randomization

/-!
# The local conditional law of an array cell

For a separately exchangeable array, the conditional law of one cell given every other cell
depends only on the rest of any infinite rectangle through that cell. This is the conditional
kernel used to generate the cell noise in the Aldous--Hoover representation. The joint-law form
keeps both the local rectangle and the remaining observations, so that the kernel can be used
without choosing versions of conditional probabilities at individual array realizations.

The result follows from local conditional independence and the characterization of conditional
independence by regular conditional distributions.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
  {ρ : Measure (ℕ × ℕ → α)} [IsFiniteMeasure ρ]

/-- Conditional on the local rectangle and the rest of the array, the distribution of a cell
depends only on the local rectangle. The equality is almost everywhere for the joint law of
the two observations. -/
theorem SeparatelyExchangeable.condDistrib_cell_rest_ae_eq_local
    (hρ : SeparatelyExchangeable ρ fun p x ↦ x p)
    {S T : Set ℕ} (hS : S.Infinite) (hT : T.Infinite)
    {c : ℕ × ℕ} (hc₁ : c.1 ∈ S) (hc₂ : c.2 ∈ T) :
    let R : Set (ℕ × ℕ) := S ×ˢ T \ {c}
    let D : Set (ℕ × ℕ) := {c}ᶜ
    condDistrib (fun x : ℕ × ℕ → α ↦ x c)
        (fun x ↦ (R.domRestrict x, D.domRestrict x)) ρ
      =ᵐ[ρ.map fun x ↦ (R.domRestrict x, D.domRestrict x)]
        (condDistrib (fun x : ℕ × ℕ → α ↦ x c) R.domRestrict ρ).prodMkRight _ := by
  dsimp
  have hk : Measurable fun x : ℕ × ℕ → α ↦ (S ×ˢ T \ {c}).domRestrict x :=
    Set.measurable_restrict _
  have hg : Measurable fun x : ℕ × ℕ → α ↦ ({c}ᶜ : Set (ℕ × ℕ)).domRestrict x :=
    Set.measurable_restrict _
  have hf : Measurable fun x : ℕ × ℕ → α ↦ x c := measurable_pi_apply c
  exact (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hf hg hk).mp
    (hρ.condIndepFun_apply_domRestrict_compl hS hT hc₁ hc₂).symm

/-- The full joint law of the local observations, the rest of the array, and one cell factors
through the conditional kernel given just the local rectangle. -/
theorem SeparatelyExchangeable.jointLaw_cell_rest_eq_compProd_local
    (hρ : SeparatelyExchangeable ρ fun p x ↦ x p)
    {S T : Set ℕ} (hS : S.Infinite) (hT : T.Infinite)
    {c : ℕ × ℕ} (hc₁ : c.1 ∈ S) (hc₂ : c.2 ∈ T) :
    let R : Set (ℕ × ℕ) := S ×ˢ T \ {c}
    let D : Set (ℕ × ℕ) := {c}ᶜ
    ρ.map (fun x : ℕ × ℕ → α ↦ ((R.domRestrict x, D.domRestrict x), x c)) =
      (ρ.map fun x ↦ (R.domRestrict x, D.domRestrict x)) ⊗ₘ
        (condDistrib (fun x : ℕ × ℕ → α ↦ x c) R.domRestrict ρ).prodMkRight _ := by
  dsimp
  have hk : AEMeasurable
      (fun x : ℕ × ℕ → α ↦ ((S ×ˢ T \ {c}).domRestrict x,
        ({c}ᶜ : Set (ℕ × ℕ)).domRestrict x)) ρ :=
    ((Set.measurable_restrict _).prodMk (Set.measurable_restrict _)).aemeasurable
  have hf : AEMeasurable (fun x : ℕ × ℕ → α ↦ x c) ρ :=
    (measurable_pi_apply c).aemeasurable
  exact (condDistrib_ae_eq_iff_measure_eq_compProd hk hf _).mp
    (hρ.condDistrib_cell_rest_ae_eq_local hS hT hc₁ hc₂)

/-- One fresh uniform variable can generate the cell while preserving its joint law with all
other cells. The coding function uses only the local rectangle as a parameter; the full
complement is carried through unchanged. -/
theorem SeparatelyExchangeable.exists_local_cell_coding
    (hρ : SeparatelyExchangeable ρ fun p x ↦ x p)
    {S T : Set ℕ} (hS : S.Infinite) (hT : T.Infinite)
    {c : ℕ × ℕ} (hc₁ : c.1 ∈ S) (hc₂ : c.2 ∈ T) :
    let R : Set (ℕ × ℕ) := S ×ˢ T \ {c}
    let D : Set (ℕ × ℕ) := {c}ᶜ
    ∃ f : (R → α) → I → α, Measurable (Function.uncurry f) ∧
      ((ρ.map fun x : ℕ × ℕ → α ↦ (R.domRestrict x, D.domRestrict x)).prod
          (volume : Measure I)).map
          (fun q ↦ (q.1, f q.1.1 q.2)) =
        ρ.map (fun x : ℕ × ℕ → α ↦ ((R.domRestrict x, D.domRestrict x), x c)) := by
  dsimp
  let κ := condDistrib (fun x : ℕ × ℕ → α ↦ x c)
    (S ×ˢ T \ {c}).domRestrict ρ
  obtain ⟨f, hf, hmap⟩ := Kernel.exists_measurable_map_eq_unitInterval κ
  refine ⟨f, hf, ?_⟩
  have hf' : Measurable (Function.uncurry (fun q :
      (↥(S ×ˢ T \ {c}) → α) × (↥({c}ᶜ : Set (ℕ × ℕ)) → α) ↦ f q.1)) := by
    exact hf.comp (measurable_fst.prodMap measurable_id)
  have hmap' : ∀ q : (↥(S ×ˢ T \ {c}) → α) × (↥({c}ᶜ : Set (ℕ × ℕ)) → α),
      (volume : Measure I).map (f q.1) = (κ.prodMkRight _) q := by
    intro q
    rw [Kernel.prodMkRight_apply]
    exact hmap q.1
  rw [map_prod_volume_eq_compProd_of_map_volume (κ.prodMkRight _)
    (fun q : (↥(S ×ˢ T \ {c}) → α) × (↥({c}ᶜ : Set (ℕ × ℕ)) → α) ↦ f q.1)
    hf' hmap']
  exact (hρ.jointLaw_cell_rest_eq_compProd_local hS hT hc₁ hc₂).symm

end TauCeti.Probability
