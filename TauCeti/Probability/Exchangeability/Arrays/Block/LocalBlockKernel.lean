/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Block.Independence
public import TauCeti.Probability.Kernel.Randomization

/-!
# The local conditional law of a block of array entries

Fix a separately exchangeable array, an infinite rectangle `S ×ˢ T` inside its index set, and a
finite block `C` of entries of that rectangle. The block `C` is the **hidden block** of the
statements below: the sub-block `B ⊆ C` is the part that is read off, and it may be strictly
smaller than `C`. Reading `Cᶜ` gives everything the array has outside the hidden block: the rest
of the rectangle, together with all entries outside the rectangle. Reading `S ×ˢ T \ C` gives
the **reservoir**, the rest of the rectangle alone.

The conditional law of a sub-block `B ⊆ C` of the hidden block, given both the reservoir and the
whole of `Cᶜ`, is the conditional law of `B` given the reservoir alone: the entries outside the
hidden block are irrelevant once the reservoir is known, in any block shape and in any position.
This is the conditional kernel used to generate the cell noise of the Aldous--Hoover
representation, and one fresh uniform variable suffices to generate the whole sub-block while
preserving its joint law with every entry outside the hidden block. The joint-law forms keep the
reservoir and the entries outside the hidden block side by side, so that the kernel can be used
without choosing versions of conditional probabilities at individual array realizations.

The statements carry the reservoir, the entries outside the hidden block and the generated
sub-block `B`, and nothing else: the ungenerated remainder `C \ B` of the hidden block is
deliberately not carried along, so that `C` may be hidden coarsely from the reservoir.

Sub-blocks matter because the hidden block need not be the block that is generated: the reservoir
may be any cofinite part of the rectangle that avoids `B`, and `B ⊆ C` may be as large or as small
as the construction at hand needs. Taking `B = C` recovers the single-block statement, in which the
hidden block and the sub-block that is read off are one and the same.

This is what Aldous's proof of the representation `X i j = f (U, Uᵢ, Vⱼ, Uᵢⱼ)` of separately
exchangeable arrays asks for. Split both axes into a hidden and a visible part, and take `S` and
`T` to be the hidden rows and columns together with the visible row `i` and visible column `j` in
play. The reservoir `S ×ˢ T \ C` is then the background block of hidden rows against hidden
columns together with the hidden parts of row `i` and of column `j`, and the visible sub-block `B`
of the hidden block is generated from it while every entry outside the hidden block is carried
along unchanged; the remainder `C \ B` of the hidden block is omitted. The cell variables `Uᵢⱼ` of
the representation are the randomizations of these conditional laws, which is why the coding
statement is stated for a whole block at once.

## Main results

In the namespace `TauCeti.Probability.SeparatelyExchangeable`:

* `condDistrib_subblock_rest_ae_eq_local`: the conditional law of `B` given the
  reservoir and the entries outside the hidden block is the kernel given the reservoir;
* `jointLaw_subblock_rest_eq_compProd_local`: the joint law of the reservoir, the
  entries outside the hidden block and `B` factors through that kernel;
* `exists_local_subblock_coding`: one fresh uniform variable generates `B` from the reservoir,
  with the joint law of the reservoir, the entries outside the hidden block and `B` intact.

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

/-- **Conditional on the reservoir and the entries outside the hidden block, the law of a
sub-block of the hidden block is the law given the reservoir alone.** The equality is almost
everywhere for the joint law of the two observations, the reservoir and the complement of the
hidden block; the ungenerated remainder of the hidden block is not observed. -/
theorem SeparatelyExchangeable.condDistrib_subblock_rest_ae_eq_local
    (hρ : SeparatelyExchangeable ρ fun p x ↦ x p)
    {S T : Set ℕ} (hS : S.Infinite) (hT : T.Infinite)
    {B C : Set (ℕ × ℕ)} (hC : C.Finite) (hBsub : B ⊆ C) (hCsub : C ⊆ S ×ˢ T) :
    let R : Set (ℕ × ℕ) := S ×ˢ T \ C
    let D : Set (ℕ × ℕ) := Cᶜ
    condDistrib (fun x : ℕ × ℕ → α ↦ B.domRestrict x)
        (fun x ↦ (R.domRestrict x, D.domRestrict x)) ρ
      =ᵐ[ρ.map fun x ↦ (R.domRestrict x, D.domRestrict x)]
        (condDistrib (fun x : ℕ × ℕ → α ↦ B.domRestrict x) R.domRestrict ρ).prodMkRight _ := by
  dsimp
  have hk : Measurable fun x : ℕ × ℕ → α ↦ (S ×ˢ T \ C).domRestrict x :=
    Set.measurable_restrict _
  have hg : Measurable fun x : ℕ × ℕ → α ↦ (Cᶜ : Set (ℕ × ℕ)).domRestrict x :=
    Set.measurable_restrict _
  have hf : Measurable fun x : ℕ × ℕ → α ↦ B.domRestrict x :=
    Set.measurable_restrict _
  exact (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hf hg hk).mp
    (hρ.condIndepFun_domRestrict_subblock_compl_of_finite_block_of_subset hS hT hC hBsub
      hCsub).symm

/-- **The joint law of the reservoir, the entries outside the hidden block and a sub-block of
the hidden block factors through the conditional kernel given the reservoir.** -/
theorem SeparatelyExchangeable.jointLaw_subblock_rest_eq_compProd_local
    (hρ : SeparatelyExchangeable ρ fun p x ↦ x p)
    {S T : Set ℕ} (hS : S.Infinite) (hT : T.Infinite)
    {B C : Set (ℕ × ℕ)} (hC : C.Finite) (hBsub : B ⊆ C) (hCsub : C ⊆ S ×ˢ T) :
    let R : Set (ℕ × ℕ) := S ×ˢ T \ C
    let D : Set (ℕ × ℕ) := Cᶜ
    ρ.map (fun x : ℕ × ℕ → α ↦ ((R.domRestrict x, D.domRestrict x), B.domRestrict x)) =
      (ρ.map fun x ↦ (R.domRestrict x, D.domRestrict x)) ⊗ₘ
        (condDistrib (fun x : ℕ × ℕ → α ↦ B.domRestrict x) R.domRestrict ρ).prodMkRight _ := by
  dsimp
  have hk : AEMeasurable
      (fun x : ℕ × ℕ → α ↦ ((S ×ˢ T \ C).domRestrict x,
        (Cᶜ : Set (ℕ × ℕ)).domRestrict x)) ρ :=
    ((Set.measurable_restrict _).prodMk (Set.measurable_restrict _)).aemeasurable
  have hf : AEMeasurable (fun x : ℕ × ℕ → α ↦ B.domRestrict x) ρ :=
    (Set.measurable_restrict _).aemeasurable
  exact (condDistrib_ae_eq_iff_measure_eq_compProd hk hf _).mp
    (hρ.condDistrib_subblock_rest_ae_eq_local hS hT hC hBsub hCsub)

/-- **One fresh uniform variable can generate a sub-block of the hidden block while preserving
its joint law with every entry outside the hidden block.** The coding function uses only the
reservoir as a parameter; every entry outside the hidden block is carried through unchanged, and
the ungenerated remainder of the hidden block is neither observed nor generated. -/
theorem SeparatelyExchangeable.exists_local_subblock_coding
    (hρ : SeparatelyExchangeable ρ fun p x ↦ x p)
    {S T : Set ℕ} (hS : S.Infinite) (hT : T.Infinite)
    {B C : Set (ℕ × ℕ)} (hC : C.Finite) (hBsub : B ⊆ C) (hCsub : C ⊆ S ×ˢ T) :
    let R : Set (ℕ × ℕ) := S ×ˢ T \ C
    let D : Set (ℕ × ℕ) := Cᶜ
    ∃ f : (R → α) → I → (B → α), Measurable (Function.uncurry f) ∧
      ((ρ.map fun x : ℕ × ℕ → α ↦ (R.domRestrict x, D.domRestrict x)).prod
          (volume : Measure I)).map
          (fun q ↦ (q.1, f q.1.1 q.2)) =
        ρ.map (fun x : ℕ × ℕ → α ↦ ((R.domRestrict x, D.domRestrict x), B.domRestrict x)) := by
  dsimp
  let κ := condDistrib (fun x : ℕ × ℕ → α ↦ B.domRestrict x)
    (S ×ˢ T \ C).domRestrict ρ
  obtain ⟨f, hf, hmap⟩ := Kernel.exists_measurable_map_eq_unitInterval κ
  refine ⟨f, hf, ?_⟩
  have hf' : Measurable (Function.uncurry (fun q :
      (↥(S ×ˢ T \ C) → α) × (↥(Cᶜ : Set (ℕ × ℕ)) → α) ↦ f q.1)) := by
    exact hf.comp (measurable_fst.prodMap measurable_id)
  have hmap' : ∀ q : (↥(S ×ˢ T \ C) → α) × (↥(Cᶜ : Set (ℕ × ℕ)) → α),
      (volume : Measure I).map (f q.1) = (κ.prodMkRight _) q := by
    intro q
    rw [Kernel.prodMkRight_apply]
    exact hmap q.1
  rw [map_prod_volume_eq_compProd_of_map_volume (κ.prodMkRight _)
    (fun q : (↥(S ×ˢ T \ C) → α) × (↥(Cᶜ : Set (ℕ × ℕ)) → α) ↦ f q.1)
    hf' hmap']
  exact (hρ.jointLaw_subblock_rest_eq_compProd_local hS hT hC hBsub hCsub).symm

end TauCeti.Probability

end

end
