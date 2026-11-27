/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.RestrictedProduct.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.Away.Split
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import TauCeti.Algebra.BigOperators.Finprod

/-!
# Fubini for restricted products of Haar measures

Let `(G i)` be a countable family of second-countable locally compact groups with open subgroups
`B i` and left Haar measures `μ i` with `μ i (B i) = 1` for all but finitely many `i`, and let
`restrictedHaar B μ hμB` be the restricted product of the `μ i` on `Πʳ i, [G i, B i]`.

For a finite set `T` of indices, `restrictedProductSplit B T`
(`TauCeti/Topology/Algebra/RestrictedProduct/Away/Split.lean`) splits `Πʳ i, [G i, B i]` as the
product of the finite product `Π i : T, G i` with the restricted product over the complement of
`T`. It carries `restrictedHaar B μ hμB` to the product of `Measure.pi fun i : T ↦ μ i` with the
restricted Haar product over the complement (`measurePreserving_restrictedProductSplit`), so an
integral over the restricted product is an iterated integral over the two factors
(`integral_restrictedHaar_eq_integral_integral`). No condition on `T` is needed.

Splitting off the finitely many indices at which `f i` is not the indicator of `B i`, the integral
of a factorizable function `x ↦ ∏ᶠ i, f i (x i)` is the finitary product `∏ᶠ i, ∫ f i ∂μ i` of
the local integrals (`integral_restrictedHaar_finprod`), and such a function is integrable when
every `f i` is (`integrable_restrictedHaar_finprod`).

## Main definitions and results

* `TauCeti.measurePreserving_restrictedProductSplit`,
  `TauCeti.integral_restrictedHaar_eq_integral_integral`: Fubini for `restrictedHaar`.
* `TauCeti.integral_restrictedHaar_finprod`, `TauCeti.integrable_restrictedHaar_finprod`:
  integrals of factorizable functions.

## References

* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), 5–30, §5.5.
* V. Platonov, A. Rapinchuk, and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. 1,
  2nd ed., Cambridge University Press (2023), Lemma 3.63 and pp. 188–189.
* Z. Rosengarten, *Tamagawa numbers and other invariants of pseudoreductive groups over global
  function fields*, Lemma 3.5.
-/

public section

noncomputable section

open Filter MeasureTheory MeasureTheory.Measure RestrictedProduct Set Topology
open scoped ENNReal RestrictedProduct

namespace TauCeti

section Split

variable {ι : Type*} {G : ι → Type*} {K : ι → Type*} [∀ i, Group (G i)]
  [∀ i, SetLike (K i) (G i)] [∀ i, SubgroupClass (K i) (G i)]

variable (B : ∀ i, K i) (T : Finset ι)

/-- After splitting at a finite set `T` outside which every `f i` is the indicator of `B i`, the
function `x ↦ ∏ᶠ i, f i (x i)` is the product of a function of the coordinates in `T` with the
indicator of the box `Π i ∉ T, B i`. -/
@[to_additive (dont_translate := M₀)]
private theorem finprod_restrictedProductSplit_symm {M₀ : Type*} [CommMonoidWithZero M₀]
    {f : ∀ i, G i → M₀}
    (hT : ∀ i ∉ T, f i = (B i : Set (G i)).indicator 1)
    (y : (Π i : T, G i) × Πʳ i : {i // i ∉ T}, [G i.val, B i.val]) :
    ∏ᶠ i, f i ((restrictedProductSplit B T).symm y i) =
      (∏ i : T, f i (y.1 i)) *
        (box fun i : {i // i ∉ T} ↦ (B i.val : Set (G i.val))).indicator 1 y.2 := by
  have hcompl (i : {i // i ∉ T}) : f i ((restrictedProductSplit B T).symm y i) =
      (B i.val : Set (G i.val)).indicator 1 (y.2 i) := by
    rw [hT i i.property, restrictedProductSplit_symm_apply_of_notMem B T y i.property]
  have hfin : Function.HasFiniteMulSupport fun i ↦ f i ((restrictedProductSplit B T).symm y i) :=
    finite_of_forall_mem_imp_apply_notMem (A := fun i ↦ (B i : Set (G i))) T y.2 fun i h hi hy ↦
      hi ((hcompl ⟨i, h⟩).trans (indicator_of_mem hy 1))
  rw [finprod_eq_prod_mul_finprod_compl hfin T]
  congr 1
  · exact Finset.prod_congr rfl fun i _ ↦ by
      rw [restrictedProductSplit_symm_apply_of_mem B T y i.property]
  · simp_rw [hcompl]
    by_cases hy : y.2 ∈ box fun i : {i // i ∉ T} ↦ (B i.val : Set (G i.val))
    · rw [indicator_of_mem hy]
      exact finprod_eq_one_of_forall_eq_one fun i ↦ indicator_of_mem (mem_box.mp hy i) 1
    · rw [indicator_of_notMem hy]
      obtain ⟨i, hi⟩ := not_forall.mp (mt mem_box.mpr hy)
      refine finprod_eq_zero _ i (indicator_of_notMem hi 1) ?_
      refine ((Filter.eventually_cofinite.mp y.2.property)).subset fun j hj ↦ fun hjB ↦ hj ?_
      exact indicator_of_mem hjB 1

end Split

section Measure

variable {ι : Type*} [Countable ι]
variable {G : ι → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)]
  [∀ i, SecondCountableTopology (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
variable {K : ι → Type*} [∀ i, SetLike (K i) (G i)] [∀ i, SubgroupClass (K i) (G i)]

variable (B : ∀ i, K i) [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
  (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
  (hμB : ∀ᶠ i in cofinite, μ i (B i) = 1)

section Fubini

variable (T : Finset ι)

/-- **Fubini splitting of `restrictedHaar`.** For every finite set `T` of indices,
`restrictedProductSplit B T` carries `restrictedHaar B μ hμB` to the product of the finite
product measure `Measure.pi fun i : T ↦ μ i` with the restricted Haar product over the complement
of `T`. -/
@[to_additive measurePreserving_addRestrictedProductSplit
/-- **Fubini splitting of `restrictedAddHaar`.** For every finite set `T` of indices,
`addRestrictedProductSplit B T` carries `restrictedAddHaar B μ hμB` to the product of the finite
product measure `Measure.pi fun i : T ↦ μ i` with the restricted additive Haar product over the
complement of `T`. -/]
theorem measurePreserving_restrictedProductSplit :
    MeasurePreserving (restrictedProductSplit B T) (restrictedHaar B μ hμB)
      ((Measure.pi fun i : T ↦ μ i.val).prod
        (restrictedHaar (fun i : {i // i ∉ T} ↦ B i.val) (fun i ↦ μ i.val)
          (Subtype.val_injective.tendsto_cofinite.eventually hμB))) := by
  have hΦ := measurable_restrictedProductSplit B T
  have hΨ := measurable_restrictedProductSplit_symm B T
  have key : ((Measure.pi fun i : T ↦ μ i.val).prod
      (restrictedHaar (fun i : {i // i ∉ T} ↦ B i.val) (fun i ↦ μ i.val)
        (Subtype.val_injective.tendsto_cofinite.eventually hμB))).map
          (restrictedProductSplit B T).symm = restrictedHaar B μ hμB := by
    refine eq_restrictedHaar_of_box B μ hμB fun C hC hCB ↦ ?_
    have hfin : (Function.mulSupport fun i ↦ μ i (C i)).Finite :=
      Filter.eventually_cofinite.mp <| (hCB.and hμB).mono fun i hi ↦ by simp [hi.1, hi.2]
    rw [map_apply hΨ (measurableSet_box fun i ↦ (hC i).measurableSet),
      preimage_restrictedProductSplit_symm_box, Measure.prod_prod, Measure.pi_pi,
      restrictedHaar_box_eq_finprod _ _ _ (Subtype.val_injective.tendsto_cofinite.eventually hCB),
      finprod_eq_prod_mul_finprod_compl hfin T]
  refine ⟨hΦ, ?_⟩
  rw [← key, map_map hΦ hΨ, MulEquiv.self_comp_symm, Measure.map_id]

/-- `measurePreserving_restrictedProductSplit` for the inverse of the measurable equivalence
`restrictedProductSplitMeasurableEquiv B T`, the form used to transfer integrals and
integrability. -/
@[to_additive measurePreserving_addRestrictedProductSplitMeasurableEquiv_symm
/-- `measurePreserving_addRestrictedProductSplit` for the inverse of the measurable equivalence
`addRestrictedProductSplitMeasurableEquiv B T`. -/]
private theorem measurePreserving_restrictedProductSplitMeasurableEquiv_symm :
    MeasurePreserving (restrictedProductSplitMeasurableEquiv B T).symm
      ((Measure.pi fun i : T ↦ μ i.val).prod
        (restrictedHaar (fun i : {i // i ∉ T} ↦ B i.val) (fun i ↦ μ i.val)
          (Subtype.val_injective.tendsto_cofinite.eventually hμB))) (restrictedHaar B μ hμB) := by
  have h := measurePreserving_restrictedProductSplit B μ hμB T
  rw [← coe_restrictedProductSplitMeasurableEquiv] at h
  exact h.symm

/-- **Fubini's theorem for `restrictedHaar`.** For every finite set `T` of indices, the integral
of an integrable function over `Πʳ i, [G i, B i]` is the iterated integral over the finite product
`Π i : T, G i` of the integral over the restricted product over the complement of `T`. -/
@[to_additive /-- **Fubini's theorem for `restrictedAddHaar`.** For every finite set `T` of
indices, the integral of an integrable function over `Πʳ i, [G i, B i]` is the iterated integral
over the finite product `Π i : T, G i` of the integral over the restricted product over the
complement of `T`. -/]
theorem integral_restrictedHaar_eq_integral_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : Πʳ i, [G i, B i] → E} (hf : Integrable f (restrictedHaar B μ hμB)) :
    ∫ x, f x ∂restrictedHaar B μ hμB =
      ∫ y, ∫ z, f ((restrictedProductSplit B T).symm (y, z))
        ∂restrictedHaar (fun i : {i // i ∉ T} ↦ B i.val) (fun i ↦ μ i.val)
          (Subtype.val_injective.tendsto_cofinite.eventually hμB)
        ∂Measure.pi fun i : T ↦ μ i.val := by
  have h := measurePreserving_restrictedProductSplitMeasurableEquiv_symm B μ hμB T
  have hf' := (h.integrable_comp_emb
    (restrictedProductSplitMeasurableEquiv B T).symm.measurableEmbedding (g := f)).mpr hf
  rw [← h.integral_comp' f]
  rw [coe_restrictedProductSplitMeasurableEquiv_symm] at hf' ⊢
  exact integral_prod _ hf'

end Fubini

include hμB in
omit [Countable ι] [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)]
  [∀ i, SecondCountableTopology (G i)] [∀ i, BorelSpace (G i)] [∀ i, SubgroupClass (K i) (G i)]
  hBopen [∀ i, (μ i).IsHaarMeasure] in
/-- A finite set of indices outside which `f i` is the indicator of `B i` and `μ i (B i) = 1`. -/
private theorem exists_finset_eq_indicator_and_measure_eq_one {𝕜 : Type*} [One 𝕜] [Zero 𝕜]
    {f : ∀ i, G i → 𝕜} (hfB : ∀ᶠ i in cofinite, f i = (B i : Set (G i)).indicator 1) :
    ∃ T : Finset ι, ∀ i ∉ T, f i = (B i : Set (G i)).indicator 1 ∧ μ i (B i) = 1 :=
  ⟨(mem_cofinite.mp (hfB.and hμB)).toFinset, fun _ hi ↦
    Classical.byContradiction fun hnot ↦ hi ((Set.Finite.mem_toFinset _).mpr hnot)⟩

/-- **Integral of a factorizable function.** Let `f i : G i → 𝕜` be functions with `f i` the
indicator of `B i` for all but finitely many `i`. The integral of `x ↦ ∏ᶠ i, f i (x i)` over
`Πʳ i, [G i, B i]` for `restrictedHaar` is the finitary product of the integrals of the `f i`. -/
@[to_additive (dont_translate := 𝕜) integral_restrictedAddHaar_finprod
/-- **Integral of a factorizable function.** Let
`f i : G i → 𝕜` be functions with `f i` the indicator of `B i` for all but finitely many `i`. The
integral of `x ↦ ∏ᶠ i, f i (x i)` over `Πʳ i, [G i, B i]` for `restrictedAddHaar` is the finitary
product of the integrals of the `f i`. -/]
theorem integral_restrictedHaar_finprod {𝕜 : Type*} [RCLike 𝕜] {f : ∀ i, G i → 𝕜}
    (hfB : ∀ᶠ i in cofinite, f i = (B i : Set (G i)).indicator 1) :
    ∫ x, ∏ᶠ i, f i (x i) ∂restrictedHaar B μ hμB = ∏ᶠ i, ∫ y, f i y ∂μ i := by
  obtain ⟨T, hT⟩ := exists_finset_eq_indicator_and_measure_eq_one B μ hμB hfB
  have hint (i : ι) (hi : i ∉ T) : ∫ y, f i y ∂μ i = 1 := by
    simp [(hT i hi).1, integral_indicator (hBopen.out i).measurableSet, measureReal_def,
      (hT i hi).2]
  -- the local integrals are `1` off `T`
  have hloc : ∏ᶠ i, ∫ y, f i y ∂μ i = ∏ i : T, ∫ y, f i y ∂μ i := by
    rw [Finset.prod_coe_sort T fun i ↦ ∫ y, f i y ∂μ i]
    exact finprod_eq_prod_of_mulSupport_subset _ fun i hi ↦ by_contra fun hiT ↦ hi (hint i hiT)
  -- the indicator of the box `Π i ∉ T, B i` has integral `1` over the complement of `T`
  have hbox : ∫ z, (box fun i : {i // i ∉ T} ↦ (B i.val : Set (G i.val))).indicator 1 z
      ∂restrictedHaar (fun i : {i // i ∉ T} ↦ B i.val) (fun i ↦ μ i.val)
        (Subtype.val_injective.tendsto_cofinite.eventually hμB) = (1 : 𝕜) := by
    rw [integral_indicator (measurableSet_box fun i ↦ (hBopen.out i.val).measurableSet),
      Pi.one_def, setIntegral_const, measureReal_def, restrictedHaar_box_self,
      finprod_eq_one_of_forall_eq_one fun i : {i // i ∉ T} ↦ (hT i.val i.property).2]
    simp
  have h := measurePreserving_restrictedProductSplitMeasurableEquiv_symm B μ hμB T
  rw [← h.integral_comp' fun x ↦ ∏ᶠ i, f i (x i)]
  simp_rw [coe_restrictedProductSplitMeasurableEquiv_symm,
    finprod_restrictedProductSplit_symm B T fun i hi ↦ (hT i hi).1]
  -- Fubini for a product of a function on `Π i : T, G i` and one on the complement
  rw [integral_prod_mul (fun y : Π i : T, G i ↦ ∏ i : T, f i (y i))
      ((box fun i : {i // i ∉ T} ↦ (B i.val : Set (G i.val))).indicator 1),
    integral_fintype_prod_eq_prod, hbox, mul_one, hloc]

/-- A factorizable function `x ↦ ∏ᶠ i, f i (x i)`, with `f i` integrable for every `i` and equal to
the indicator of `B i` for all but finitely many `i`, is integrable for `restrictedHaar`. -/
@[to_additive (dont_translate := 𝕜) integrable_restrictedAddHaar_finprod
/-- A factorizable function `x ↦ ∏ᶠ i, f i (x i)`, with `f i` integrable for every `i` and
equal to the indicator of `B i` for all but finitely many `i`, is integrable for
`restrictedAddHaar`. -/]
theorem integrable_restrictedHaar_finprod {𝕜 : Type*} [RCLike 𝕜] {f : ∀ i, G i → 𝕜}
    (hf : ∀ i, Integrable (f i) (μ i))
    (hfB : ∀ᶠ i in cofinite, f i = (B i : Set (G i)).indicator 1) :
    Integrable (fun x ↦ ∏ᶠ i, f i (x i)) (restrictedHaar B μ hμB) := by
  obtain ⟨T, hT⟩ := exists_finset_eq_indicator_and_measure_eq_one B μ hμB hfB
  have h := measurePreserving_restrictedProductSplitMeasurableEquiv_symm B μ hμB T
  refine (h.integrable_comp_emb (restrictedProductSplitMeasurableEquiv B T).symm.measurableEmbedding
    (g := fun x ↦ ∏ᶠ i, f i (x i))).mp ?_
  have hbox : MeasurableSet (box fun i : {i // i ∉ T} ↦ (B i.val : Set (G i.val)) :
      Set (Πʳ i : {i // i ∉ T}, [G i.val, B i.val])) :=
    measurableSet_box fun i ↦ (hBopen.out i.val).measurableSet
  simp_rw [Function.comp_def, coe_restrictedProductSplitMeasurableEquiv_symm,
    finprod_restrictedProductSplit_symm B T fun i hi ↦ (hT i hi).1]
  refine (Integrable.fintype_prod_dep fun i : T ↦ hf i).mul_prod
    ((integrable_indicator_iff hbox).mpr (integrableOn_const ?_))
  rw [restrictedHaar_box_self,
    finprod_eq_one_of_forall_eq_one fun i : {i // i ∉ T} ↦ (hT i.val i.property).2]
  exact ENNReal.one_ne_top

end Measure

end TauCeti
