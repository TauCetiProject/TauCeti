/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.RestrictedProduct.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.Congr.Right
import TauCeti.MeasureTheory.Group.OpenSubgroup.Basic

/-!
# Functoriality of restricted products of Haar measures

Let `φ i : G i ≃ₜ* H i` be isomorphisms of topological groups carrying the open subgroups `U i`
bijectively onto `U' i` for all but finitely many `i`. They induce the isomorphism
`TauCeti.restrictedProductCongrRight` of restricted products
`Πʳ i, [G i, U i] ≃* Πʳ i, [H i, U' i]`, and this file shows that it carries the normalized
restricted product `∏ʳ μ i` of local Haar measures to the restricted product `∏ʳ (φ i)_* μ i` of
their pushforwards. The proof is by uniqueness (`TauCeti.restrictedHaar_unique`): the preimage of a
coordinate box is the coordinate box of the preimages, so the pushforward has the box masses of
`∏ʳ (φ i)_* μ i`.

## Main results

* `TauCeti.map_restrictedProductCongrRight_restrictedHaar`: `Φ_*(∏ʳ μ i) = ∏ʳ (φ i)_* μ i`, with
  its additive counterpart `TauCeti.map_addRestrictedProductCongrRight_restrictedAddHaar`.
* `TauCeti.eventually_map_mulEquiv_apply_eq_one`: the pushforwards are again normalized
  cofinitely.

## References

* Z. Rosengarten, *Tamagawa numbers and other invariants of pseudo-reductive groups over global
  function fields*, arXiv:1806.10723v3, Lemma 3.5, p. 26, for the specialization to morphisms of
  affine schemes of finite type over a global field.
-/

public section

noncomputable section

open Filter MeasureTheory MeasureTheory.Measure RestrictedProduct Set
open scoped RestrictedProduct

namespace TauCeti

variable {ι : Type*} [Countable ι]
variable {G : ι → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)]
  [∀ i, SecondCountableTopology (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
variable {H : ι → Type*} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
  [∀ i, IsTopologicalGroup (H i)] [∀ i, LocallyCompactSpace (H i)]
  [∀ i, SecondCountableTopology (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]

omit [Countable ι] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)]
  [∀ i, SecondCountableTopology (G i)] [∀ i, IsTopologicalGroup (H i)]
  [∀ i, LocallyCompactSpace (H i)] [∀ i, SecondCountableTopology (H i)] in
/-- If `μ i (U i) = 1` cofinitely and `φ i` carries `U i` onto `U' i` cofinitely, then the
pushforwards satisfy `(φ i)_* μ i (U' i) = 1` cofinitely. -/
@[to_additive eventually_map_addEquiv_apply_eq_one
/-- If `μ i (U i) = 1` cofinitely and `φ i` carries `U i` onto `U' i` cofinitely, then the
pushforwards satisfy `(φ i)_* μ i (U' i) = 1` cofinitely. -/]
theorem eventually_map_mulEquiv_apply_eq_one (U : ∀ i, Subgroup (G i)) (U' : ∀ i, Subgroup (H i))
    (φ : ∀ i, G i ≃ₜ* H i) (hφ : ∀ᶠ i in cofinite, Set.BijOn (φ i) (U i) (U' i))
    (μ : ∀ i, Measure (G i)) (hμU : ∀ᶠ i in cofinite, μ i (U i) = 1) :
    ∀ᶠ i in cofinite, (μ i).map (φ i) (U' i) = 1 := by
  filter_upwards [hφ, hμU] with i hi h
  have hme : MeasurableEmbedding (φ i) := (φ i).toHomeomorph.measurableEmbedding
  rw [← hi.image_eq, hme.map_apply, Set.preimage_image_eq _ (φ i).injective]
  exact h

/-- **Functoriality of restricted products of Haar measures.** Isomorphisms of topological groups
`φ i : G i ≃ₜ* H i` carrying `U i` onto `U' i` cofinitely induce
`Φ : Πʳ i, [G i, U i] ≃* Πʳ i, [H i, U' i]` with `Φ_*(∏ʳ μ i) = ∏ʳ (φ i)_* μ i`. -/
@[to_additive map_addRestrictedProductCongrRight_restrictedAddHaar
/-- **Functoriality of restricted products of additive Haar measures.** Isomorphisms
of topological additive groups `φ i : G i ≃ₜ+ H i` carrying `U i` onto `U' i` cofinitely induce
`Φ : Πʳ i, [G i, U i] ≃+ Πʳ i, [H i, U' i]` with `Φ_*(∏ʳ μ i) = ∏ʳ (φ i)_* μ i`. -/]
theorem map_restrictedProductCongrRight_restrictedHaar (U : ∀ i, Subgroup (G i))
    (U' : ∀ i, Subgroup (H i)) [Fact (∀ i, IsOpen (U i : Set (G i)))]
    [Fact (∀ i, IsOpen (U' i : Set (H i)))] (φ : ∀ i, G i ≃ₜ* H i)
    (hφ : ∀ᶠ i in cofinite, Set.BijOn (φ i) (U i) (U' i))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] (hμU : ∀ᶠ i in cofinite, μ i (U i) = 1) :
    (restrictedHaar U μ hμU).map
        (restrictedProductCongrRight U U' (fun i ↦ (φ i).toMulEquiv) hφ) =
      restrictedHaar U' (fun i ↦ (μ i).map (φ i))
        (eventually_map_mulEquiv_apply_eq_one U U' φ hφ μ hμU) := by
  set Φ := restrictedProductCongrRight U U' (fun i ↦ (φ i).toMulEquiv) hφ
  have hΦ : Continuous Φ :=
    continuous_restrictedProductCongrRight U U' _ hφ fun i ↦ (φ i).continuous
  have hΦsymm : Continuous Φ.symm :=
    continuous_restrictedProductCongrRight_symm U U' _ hφ fun i ↦ (φ i).symm.continuous
  have _ : LocallyCompactSpace (Πʳ i, [H i, (U' i : Set (H i))]) :=
    locallyCompactSpace_of_group H ((eventually_map_mulEquiv_apply_eq_one U U' φ hφ μ hμU).mono
      fun i hi ↦ isCompact_of_isOpen_of_measure_ne_top_of_isMulLeftInvariant
        ((Fact.out : ∀ i, IsOpen (U' i : Set (H i))) i) ((μ i).map (φ i)) (by simp [hi]))
  have _ : ((restrictedHaar U μ hμU).map Φ).IsHaarMeasure :=
    Φ.isHaarMeasure_map (restrictedHaar U μ hμU) hΦ hΦsymm
  refine restrictedHaar_unique U' _ _ fun C hCmeas hCU' ↦ ?_
  have hpre : Φ ⁻¹' (box C : Set (Πʳ i, [H i, (U' i : Set (H i))])) =
      box fun i ↦ φ i ⁻¹' C i := by
    ext x
    simp only [Φ, mem_box, Set.mem_preimage, restrictedProductCongrRight_apply]
    rfl
  rw [map_apply hΦ.measurable (measurableSet_box hCmeas), hpre,
    restrictedHaar_box_eq_finprod U μ hμU (by
      filter_upwards [hCU', hφ] with i h1 h2
      rw [h1, ← h2.image_eq, Set.preimage_image_eq _ (φ i).injective])]
  refine finprod_congr fun i ↦ ?_
  have hme : MeasurableEmbedding (φ i) := (φ i).toHomeomorph.measurableEmbedding
  exact (hme.map_apply _ (C i)).symm

end TauCeti
