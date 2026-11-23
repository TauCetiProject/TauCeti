/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.RestrictedProduct
public import TauCeti.Topology.Algebra.RestrictedProduct.Congr.Right
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import TauCeti.Algebra.BigOperators.Finprod

/-!
# Fubini and functoriality for restricted products of Haar measures

Let `(G i)` be a countable family of second-countable locally compact groups with open subgroups
`B i` and left Haar measures `μ i` with `μ i (B i) = 1` for all but finitely many `i`, and let
`restrictedHaar B μ hμB` be the restricted product of the `μ i` on `Πʳ i, [G i, B i]`.

For a finite set `T` of indices, `restrictedProductSplit B T` splits `Πʳ i, [G i, B i]` as the
product of the finite product `Π i : T, G i` with the restricted product over the complement of
`T`. It carries `restrictedHaar B μ hμB` to the product of `Measure.pi fun i : T ↦ μ i` with the
restricted Haar product over the complement (`measurePreserving_restrictedProductSplit`), so an
integral over the restricted product is an iterated integral over the two factors
(`integral_restrictedHaar_eq_integral_integral`). No condition on `T` is needed.

Splitting off the finitely many indices at which `f i` is not the indicator of `B i`, the integral
of a factorizable function `x ↦ ∏ᶠ i, f i (x i)` is the finitary product `∏ᶠ i, ∫ f i ∂μ i` of
the local integrals (`integral_restrictedHaar_finprod`), and such a function is integrable when
every `f i` is (`integrable_restrictedHaar_finprod`).

A family of isomorphisms of topological groups `φ i : G i ≃ₜ* H i` carrying `B i` onto `B' i` at
almost every index pushes `restrictedHaar` to the restricted product of the pushforwards
`(μ i).map (φ i)` (`map_restrictedProductCongrRight_restrictedHaar`).

## Main definitions and results

* `TauCeti.restrictedProductSplit`: the splitting of a restricted product at a finite set.
* `TauCeti.measurePreserving_restrictedProductSplit`,
  `TauCeti.integral_restrictedHaar_eq_integral_integral`: Fubini for `restrictedHaar`.
* `TauCeti.integral_restrictedHaar_finprod`, `TauCeti.integrable_restrictedHaar_finprod`:
  integrals of factorizable functions.
* `TauCeti.map_restrictedProductCongrRight_restrictedHaar`: functoriality of `restrictedHaar`.

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

/-- Split a finitary product at a finite set `T`: the product over `T` times the finitary product
over the complement of `T`. -/
private theorem finprod_eq_prod_mul_finprod_compl {ι M : Type*} [CommMonoid M] {f : ι → M}
    (hf : (Function.mulSupport f).Finite) (T : Finset ι) :
    ∏ᶠ i, f i = (∏ i : T, f i.val) * ∏ᶠ i : {i // i ∉ T}, f i.val := by
  classical
  rw [← finprod_comp_equiv (Equiv.sumCompl fun i ↦ i ∈ T),
    finprod_sum_type (fun j ↦ f (Equiv.sumCompl (fun i ↦ i ∈ T) j)) (Set.toFinite _)
      (hf.preimage Subtype.val_injective.injOn), finprod_eq_prod_of_fintype]
  simp

section Split

variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} {K : ι → Type*} [∀ i, Group (G i)]
  [∀ i, SetLike (K i) (G i)] [∀ i, SubgroupClass (K i) (G i)]

/-- The splitting of `Πʳ i, [G i, B i]` at a finite set `T` of indices, as the product of the
finite product `Π i : T, G i` with the restricted product over the complement of `T`. -/
@[to_additive addRestrictedProductSplit /-- The splitting of `Πʳ i, [G i, B i]` at a finite set
`T` of indices, as the product of the finite product `Π i : T, G i` with the restricted product
over the complement of `T`. -/]
def restrictedProductSplit (B : ∀ i, K i) (T : Finset ι) :
    (Πʳ i, [G i, B i]) ≃* (Π i : T, G i) × Πʳ i : {i // i ∉ T}, [G i.val, B i.val] where
  toFun x := (fun i ↦ x i.val,
    ⟨fun i ↦ x i.val, Subtype.val_injective.tendsto_cofinite.eventually x.property⟩)
  invFun y := ⟨fun i ↦ if h : i ∈ T then y.1 ⟨i, h⟩ else y.2 ⟨i, h⟩, by
    rw [Filter.eventually_cofinite]
    refine (T.finite_toSet.union
      ((Filter.eventually_cofinite.mp y.2.property).image Subtype.val)).subset fun i hi ↦ ?_
    by_cases h : i ∈ T
    · exact Or.inl h
    · refine Or.inr ⟨⟨i, h⟩, ?_, rfl⟩
      simp only [mem_ofPred_eq, h, ↓reduceDIte] at hi
      exact hi⟩
  left_inv x := by
    ext i
    simp
  right_inv y := by
    ext i
    · simp [i.property]
    · simp [i.property]
  map_mul' _ _ := rfl

variable (B : ∀ i, K i) (T : Finset ι)

/-- The finite component of `restrictedProductSplit B T` reads off the coordinates in `T`. -/
@[to_additive (attr := simp) addRestrictedProductSplit_apply_fst /-- The finite component of
`addRestrictedProductSplit B T` reads off the coordinates in `T`. -/]
theorem restrictedProductSplit_apply_fst (x : Πʳ i, [G i, B i]) (i : T) :
    (restrictedProductSplit B T x).1 i = x i := by
  rfl

/-- The restricted component of `restrictedProductSplit B T` reads off the coordinates outside
`T`. -/
@[to_additive (attr := simp) addRestrictedProductSplit_apply_snd /-- The restricted component of
`addRestrictedProductSplit B T` reads off the coordinates outside `T`. -/]
theorem restrictedProductSplit_apply_snd (x : Πʳ i, [G i, B i]) (i : {i // i ∉ T}) :
    (restrictedProductSplit B T x).2 i = x i := by
  rfl

/-- The inverse of `restrictedProductSplit B T` takes its coordinates in `T` from the finite
component. -/
@[to_additive addRestrictedProductSplit_symm_apply_of_mem /-- The inverse of
`addRestrictedProductSplit B T` takes its coordinates in `T` from the finite component. -/]
theorem restrictedProductSplit_symm_apply_of_mem
    (y : (Π i : T, G i) × Πʳ i : {i // i ∉ T}, [G i.val, B i.val]) {i : ι} (hi : i ∈ T) :
    (restrictedProductSplit B T).symm y i = y.1 ⟨i, hi⟩ := by
  change (if h : i ∈ T then y.1 ⟨i, h⟩ else y.2 ⟨i, h⟩ : G i) = _
  simp [hi]

/-- The inverse of `restrictedProductSplit B T` takes its coordinates outside `T` from the
restricted component. -/
@[to_additive addRestrictedProductSplit_symm_apply_of_notMem /-- The inverse of
`addRestrictedProductSplit B T` takes its coordinates outside `T` from the restricted
component. -/]
theorem restrictedProductSplit_symm_apply_of_notMem
    (y : (Π i : T, G i) × Πʳ i : {i // i ∉ T}, [G i.val, B i.val]) {i : ι} (hi : i ∉ T) :
    (restrictedProductSplit B T).symm y i = y.2 ⟨i, hi⟩ := by
  change (if h : i ∈ T then y.1 ⟨i, h⟩ else y.2 ⟨i, h⟩ : G i) = _
  simp [hi]

/-- The inverse image of a box under the inverse of `restrictedProductSplit B T` is the product
of the box over `T` with the box over the complement. -/
@[to_additive preimage_addRestrictedProductSplit_symm_box /-- The inverse image of a box under the
inverse of `addRestrictedProductSplit B T` is the product of the box over `T` with the box over
the complement. -/]
theorem preimage_restrictedProductSplit_symm_box (C : ∀ i, Set (G i)) :
    (restrictedProductSplit B T).symm ⁻¹' box C =
      (univ.pi fun i : T ↦ C i) ×ˢ box fun i : {i // i ∉ T} ↦ C i := by
  ext y
  simp only [mem_preimage, mem_box, mem_prod, mem_univ_pi]
  refine ⟨fun h ↦ ⟨fun i ↦ ?_, fun i ↦ ?_⟩, fun ⟨h₁, h₂⟩ i ↦ ?_⟩
  · simpa [restrictedProductSplit_symm_apply_of_mem B T y i.property] using h i
  · simpa [restrictedProductSplit_symm_apply_of_notMem B T y i.property] using h i
  · by_cases hi : i ∈ T
    · simpa [restrictedProductSplit_symm_apply_of_mem B T y hi] using h₁ ⟨i, hi⟩
    · simpa [restrictedProductSplit_symm_apply_of_notMem B T y hi] using h₂ ⟨i, hi⟩

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
  have hfin : (Function.mulSupport fun i ↦ f i ((restrictedProductSplit B T).symm y i)).Finite := by
    refine (T.finite_toSet.union
      ((Filter.eventually_cofinite.mp y.2.property).image Subtype.val)).subset fun i hi ↦ ?_
    by_cases h : i ∈ T
    · exact Or.inl h
    · exact Or.inr ⟨⟨i, h⟩, fun hy ↦ hi ((hcompl ⟨i, h⟩).trans (indicator_of_mem hy 1)), rfl⟩
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

variable [Countable ι] [∀ i, TopologicalSpace (G i)] [∀ i, SecondCountableTopology (G i)]
  [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]

/-- `restrictedProductSplit B T` is measurable. -/
@[to_additive (attr := fun_prop) measurable_addRestrictedProductSplit
/-- `addRestrictedProductSplit B T` is measurable. -/]
theorem measurable_restrictedProductSplit : Measurable (restrictedProductSplit B T) := by
  refine Measurable.prodMk ?_ ?_
  · exact measurable_pi_iff.mpr fun i ↦ measurable_eval i.val
  · exact measurable_rng_iff.mpr fun i ↦ measurable_eval (R := G) i.val

/-- The inverse of `restrictedProductSplit B T` is measurable. -/
@[to_additive (attr := fun_prop) measurable_addRestrictedProductSplit_symm
/-- The inverse of `addRestrictedProductSplit B T` is measurable. -/]
theorem measurable_restrictedProductSplit_symm :
    Measurable (restrictedProductSplit B T).symm := by
  refine measurable_rng_iff.mpr fun i ↦ ?_
  by_cases hi : i ∈ T
  · simp_rw [restrictedProductSplit_symm_apply_of_mem B T _ hi]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp_rw [restrictedProductSplit_symm_apply_of_notMem B T _ hi]
    exact (measurable_eval (R := fun i : {i // i ∉ T} ↦ G i.val) ⟨i, hi⟩).comp measurable_snd

/-- `restrictedProductSplit B T` as a measurable equivalence. -/
@[to_additive addRestrictedProductSplitMeasurableEquiv
/-- `addRestrictedProductSplit B T` as a measurable equivalence. -/]
def restrictedProductSplitMeasurableEquiv :
    (Πʳ i, [G i, B i]) ≃ᵐ (Π i : T, G i) × Πʳ i : {i // i ∉ T}, [G i.val, B i.val] where
  toEquiv := (restrictedProductSplit B T).toEquiv
  measurable_toFun := measurable_restrictedProductSplit B T
  measurable_invFun := measurable_restrictedProductSplit_symm B T

/-- The underlying function of `restrictedProductSplitMeasurableEquiv B T` is
`restrictedProductSplit B T`. -/
@[to_additive (attr := simp) coe_addRestrictedProductSplitMeasurableEquiv
/-- The underlying function of `addRestrictedProductSplitMeasurableEquiv B T` is
`addRestrictedProductSplit B T`. -/]
theorem coe_restrictedProductSplitMeasurableEquiv :
    ⇑(restrictedProductSplitMeasurableEquiv B T) = restrictedProductSplit B T := by
  rfl

/-- The inverse of `restrictedProductSplitMeasurableEquiv B T` is the inverse of
`restrictedProductSplit B T`. -/
@[to_additive (attr := simp) coe_addRestrictedProductSplitMeasurableEquiv_symm
/-- The inverse of `addRestrictedProductSplitMeasurableEquiv B T` is the inverse of
`addRestrictedProductSplit B T`. -/]
theorem coe_restrictedProductSplitMeasurableEquiv_symm :
    ⇑(restrictedProductSplitMeasurableEquiv B T).symm = (restrictedProductSplit B T).symm := by
  rfl

end Split

/-- Openness of a family of reference sets passes to its restriction to a subtype of the index
type. -/
instance fact_isOpen_coe_subtype_val {ι : Type*} {G : ι → Type*} {K : ι → Type*}
    [∀ i, TopologicalSpace (G i)] [∀ i, SetLike (K i) (G i)] {B : ∀ i, K i}
    [hB : Fact (∀ i, IsOpen (B i : Set (G i)))] (p : ι → Prop) :
    Fact (∀ i : Subtype p, IsOpen (B i.val : Set (G i.val))) :=
  ⟨fun i ↦ hB.out i.val⟩

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

variable [DecidableEq ι] (T : Finset ι)

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
  have h := (measurePreserving_restrictedProductSplit B μ hμB T).symm
    (restrictedProductSplitMeasurableEquiv B T)
  rw [← h.integral_comp' f]
  refine integral_prod (fun y ↦ f ((restrictedProductSplit B T).symm y)) ?_
  exact (h.integrable_comp_emb (restrictedProductSplitMeasurableEquiv B T).symm.measurableEmbedding
    (g := f)).mpr hf

end Fubini

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
  classical
  let T : Finset ι := (mem_cofinite.mp (hfB.and hμB)).toFinset
  have hT (i : ι) (hi : i ∉ T) : f i = (B i : Set (G i)).indicator 1 ∧ μ i (B i) = 1 :=
    Classical.byContradiction fun hnot ↦ hi ((Set.Finite.mem_toFinset _).mpr hnot)
  have hint (i : ι) (hi : i ∉ T) : ∫ y, f i y ∂μ i = 1 := by
    simp [(hT i hi).1, integral_indicator (hBopen.out i).measurableSet, measureReal_def,
      (hT i hi).2]
  have h := (measurePreserving_restrictedProductSplit B μ hμB T).symm
    (restrictedProductSplitMeasurableEquiv B T)
  rw [← h.integral_comp' fun x ↦ ∏ᶠ i, f i (x i)]
  simp_rw [coe_restrictedProductSplitMeasurableEquiv_symm,
    finprod_restrictedProductSplit_symm B T fun i hi ↦ (hT i hi).1]
  rw [integral_prod_mul (fun y : Π i : T, G i ↦ ∏ i : T, f i (y i))
      ((box fun i : {i // i ∉ T} ↦ (B i.val : Set (G i.val))).indicator 1),
    integral_fintype_prod_eq_prod, integral_indicator (measurableSet_box fun i ↦
      (hBopen.out i.val).measurableSet), Pi.one_def, setIntegral_const,
    measureReal_def, restrictedHaar_box_self,
    finprod_eq_prod_mul_finprod_compl (T.finite_toSet.subset fun i hi ↦ ?_) T]
  · rw [finprod_eq_one_of_forall_eq_one fun i : {i // i ∉ T} ↦ (hT i.val i.property).2,
      finprod_eq_one_of_forall_eq_one fun i : {i // i ∉ T} ↦ hint i.val i.property]
    simp
  · by_contra hiT
    exact hi (hint i hiT)

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
  classical
  let T : Finset ι := (mem_cofinite.mp (hfB.and hμB)).toFinset
  have hT (i : ι) (hi : i ∉ T) : f i = (B i : Set (G i)).indicator 1 ∧ μ i (B i) = 1 :=
    Classical.byContradiction fun hnot ↦ hi ((Set.Finite.mem_toFinset _).mpr hnot)
  have h := (measurePreserving_restrictedProductSplit B μ hμB T).symm
    (restrictedProductSplitMeasurableEquiv B T)
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

section Functoriality

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
/-- If the isomorphisms `φ i : G i ≃ₜ* H i` carry `U i` onto `U' i` for all but finitely many `i`
and `μ i (U i) = 1` for all but finitely many `i`, then the pushforwards `(μ i).map (φ i)` give
`U' i` measure one for all but finitely many `i`. -/
@[to_additive eventually_map_addEquiv_apply_eq_one
/-- If the isomorphisms `φ i : G i ≃ₜ+ H i` carry `U i` onto `U' i` for all but finitely many `i`
and `μ i (U i) = 1` for all but finitely many `i`, then the pushforwards `(μ i).map (φ i)` give
`U' i` measure one for all but finitely many `i`. -/]
theorem eventually_map_mulEquiv_apply_eq_one
    (U : ∀ i, Subgroup (G i)) (U' : ∀ i, Subgroup (H i))
    [Fact (∀ i, IsOpen (U' i : Set (H i)))]
    (φ : ∀ i, G i ≃ₜ* H i) (hφ : ∀ᶠ i in cofinite, Set.BijOn (φ i) (U i) (U' i))
    (μ : ∀ i, Measure (G i)) (hμU : ∀ᶠ i in cofinite, μ i (U i) = 1) :
    ∀ᶠ i in cofinite, (μ i).map (φ i) (U' i) = 1 := by
  filter_upwards [hφ, hμU] with i hbij hi
  rw [map_apply (show Measurable (φ i) from (φ i).continuous.measurable)
    (Fact.out (p := ∀ i, IsOpen (U' i : Set (H i))) i).measurableSet]
  convert hi using 2
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ hbij.mapsTo hx⟩
  obtain ⟨y, hy, hyx⟩ := hbij.surjOn hx
  exact (φ i).injective hyx ▸ hy

/-- **Functoriality of `restrictedHaar`.** Let `φ i : G i ≃ₜ* H i` be isomorphisms of
topological groups carrying `U i` onto `U' i` for all but finitely many `i`. The induced
isomorphism `restrictedProductCongrRight` of restricted products pushes `restrictedHaar U μ` to the
restricted Haar product of the pushforwards `(μ i).map (φ i)`. -/
@[to_additive map_addRestrictedProductCongrRight_restrictedAddHaar
/-- **Functoriality of `restrictedAddHaar`.** Let `φ i : G i ≃ₜ+ H i` be isomorphisms of
topological additive groups carrying `U i` onto `U' i` for all but finitely many `i`. The induced
isomorphism `addRestrictedProductCongrRight` of restricted products pushes `restrictedAddHaar U μ`
to the restricted additive Haar product of the pushforwards `(μ i).map (φ i)`. -/]
theorem map_restrictedProductCongrRight_restrictedHaar
    (U : ∀ i, Subgroup (G i)) (U' : ∀ i, Subgroup (H i))
    [Fact (∀ i, IsOpen (U i : Set (G i)))] [Fact (∀ i, IsOpen (U' i : Set (H i)))]
    (φ : ∀ i, G i ≃ₜ* H i) (hφ : ∀ᶠ i in cofinite, Set.BijOn (φ i) (U i) (U' i))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμU : ∀ᶠ i in cofinite, μ i (U i) = 1) :
    (restrictedHaar U μ hμU).map
        (restrictedProductCongrRight U U' (fun i ↦ (φ i).toMulEquiv) hφ) =
      restrictedHaar U' (fun i ↦ (μ i).map (φ i))
        (eventually_map_mulEquiv_apply_eq_one U U' φ hφ μ hμU) := by
  have hμU' := eventually_map_mulEquiv_apply_eq_one U U' φ hφ μ hμU
  have hΦ := (continuous_restrictedProductCongrRight U U' (fun i ↦ (φ i).toMulEquiv) hφ
    fun i ↦ (φ i).continuous).measurable
  refine eq_restrictedHaar_of_box U' _ hμU' fun C hC hCU' ↦ ?_
  have hpre : restrictedProductCongrRight U U' (fun i ↦ (φ i).toMulEquiv) hφ ⁻¹' box C =
      box fun i ↦ φ i ⁻¹' C i := by
    ext x
    simp only [mem_preimage, mem_box, restrictedProductCongrRight_apply]
    rfl
  have hCU : ∀ᶠ i in cofinite, φ i ⁻¹' C i = U i := by
    filter_upwards [hCU', hφ] with i hi hbij
    rw [hi]
    ext x
    refine ⟨fun hx ↦ ?_, fun hx ↦ hbij.mapsTo hx⟩
    obtain ⟨y, hy, hyx⟩ := hbij.surjOn hx
    exact (φ i).injective hyx ▸ hy
  rw [map_apply hΦ (measurableSet_box fun i ↦ (hC i).measurableSet), hpre,
    restrictedHaar_box_eq_finprod U μ hμU hCU]
  exact finprod_congr fun i ↦ (map_apply (φ i).measurable (hC i).measurableSet).symm

end Functoriality

end TauCeti
