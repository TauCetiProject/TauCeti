/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Support
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The singular support of a distribution

The *singular support* of a distribution `T` on an open set `Ω` consists of the points of `Ω`
near which `T` is not a smooth function: `x ∉ singularSupport T` when there are an open
neighbourhood `U` of `x` and a function `f` smooth on `U` with `T φ = ∫ φ • f` for every real test
function `φ` supported in `U`. It is a relatively closed subset of `Ω` contained in the support of
`T`.

Off its singular support, `T` is one smooth function: the local smooth representatives agree on
overlaps, because a continuous function is determined by its integrals against test functions,
and glue to a function smooth on `Ω \ singularSupport T`. In particular `T` has empty singular
support exactly when it is a function smooth on `Ω`. This is the form in which regularity
theorems, such as elliptic regularity, give smooth solutions.

## Main declarations

* `Distribution.singularSupport`: the singular support of a distribution.
* `Distribution.isOpen_diff_singularSupport`: the singular support is closed in `Ω`.
* `Distribution.singularSupport_subset_dsupport`: it lies in the support.
* `Distribution.singularSupport_ofFun_eq_empty`: a function smooth on `Ω` has empty singular
  support.
* `Distribution.singularSupport_add_subset`, `Distribution.singularSupport_sum_subset`: the
  singular support of a sum lies in the union of the singular supports of the summands.
* `Distribution.singularSupport_smul_subset`: scalar multiplication does not enlarge the singular
  support.
* `IsUnit.singularSupport_smul`, `Distribution.singularSupport_smul`: multiplication by a unit,
  in particular by a nonzero scalar, preserves the singular support.
* `Distribution.apply_eq_integral_of_locally`: local integral representations by one locally
  integrable function glue.
* `Distribution.exists_contDiffOn_apply_eq_integral`: a distribution is a smooth function off its
  singular support.
* `Distribution.singularSupport_eq_empty_iff`: the singular support is empty exactly when the
  distribution is a function smooth on `Ω`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §2.2.
-/

public section

noncomputable section

open Set TopologicalSpace MeasureTheory
open scoped Distributions ContDiff

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E}

/-- The **singular support** of a distribution `T` on `Ω`: the points `x ∈ Ω` having no open
neighbourhood `U` on which `T` is a smooth function, that is, no function `f` smooth on `U` with
`T φ = ∫ φ • f` for every real test function `φ` supported in `U`. -/
def singularSupport (T : 𝓓'(Ω, F)) : Set E :=
  {x | x ∈ Ω ∧ ¬ ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ f : E → F, ContDiffOn ℝ ∞ f U ∧
    ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y}

@[simp]
theorem mem_singularSupport_iff {T : 𝓓'(Ω, F)} {x : E} :
    x ∈ T.singularSupport ↔ x ∈ Ω ∧ ¬ ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ f : E → F,
      ContDiffOn ℝ ∞ f U ∧ ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y :=
  Iff.rfl

/-- A point of `Ω` lies outside the singular support of `T` exactly when `T` is a smooth function
on an open neighbourhood of it. -/
theorem notMem_singularSupport_iff {T : 𝓓'(Ω, F)} {x : E} (hx : x ∈ Ω) :
    x ∉ T.singularSupport ↔ ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ f : E → F,
      ContDiffOn ℝ ∞ f U ∧ ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y := by
  simp [hx]

/-- The singular support lies in `Ω`. -/
theorem singularSupport_subset (T : 𝓓'(Ω, F)) : T.singularSupport ⊆ Ω :=
  fun _ hx ↦ hx.1

/-- The singular support is closed in `Ω`: the points of `Ω` near which `T` is smooth form an
open set. -/
theorem isOpen_diff_singularSupport (T : 𝓓'(Ω, F)) :
    IsOpen ((Ω : Set E) \ T.singularSupport) := by
  refine isOpen_iff_forall_mem_open.2 fun x ⟨hxΩ, hx⟩ ↦ ?_
  obtain ⟨U, hU, hxU, hT⟩ := (notMem_singularSupport_iff hxΩ).1 hx
  exact ⟨U ∩ Ω, fun y ⟨hyU, hyΩ⟩ ↦ ⟨hyΩ, fun hy ↦ hy.2 ⟨U, hU, hyU, hT⟩⟩,
    hU.inter Ω.isOpen, hxU, hxΩ⟩

/-- The singular support lies in the support: `T` is the zero function on the open set where it
vanishes. -/
theorem singularSupport_subset_dsupport (T : 𝓓'(Ω, F)) : T.singularSupport ⊆ dsupport T := by
  intro x hx
  by_contra hxT
  obtain ⟨s, hT, hs, hxs⟩ := (notMem_dsupport_iff x).1 hxT
  exact hx.2 ⟨s, hs, hxs, 0, contDiffOn_const, fun φ hφ ↦ by simpa using hT φ hφ⟩

/-- The zero distribution has empty singular support. -/
@[simp]
theorem singularSupport_zero : (0 : 𝓓'(Ω, F)).singularSupport = ∅ := by
  refine subset_empty_iff.1 ((singularSupport_subset_dsupport 0).trans ?_)
  exact ((dsupport_eq_empty_iff _).2 rfl).subset

/-- A function smooth on `Ω` has empty singular support. -/
theorem singularSupport_ofFun_eq_empty {f : E → F} (hf : ContDiffOn ℝ ∞ f Ω) :
    (ofFun Ω f volume ⊤).singularSupport = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ hx ↦ hx.2 ⟨Ω, Ω.isOpen, hx.1, f, hf, fun _ _ ↦
    ofFun_apply (hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)⟩

/-- The singular support of a sum lies in the union of the singular supports. -/
theorem singularSupport_add_subset (S T : 𝓓'(Ω, F)) :
    (S + T).singularSupport ⊆ S.singularSupport ∪ T.singularSupport := by
  refine fun x hx ↦ by_contra fun h ↦ hx.2 ?_
  rw [mem_union, not_or] at h
  obtain ⟨U, hU, hxU, f, hf, hS⟩ := (notMem_singularSupport_iff hx.1).1 h.1
  obtain ⟨V, hV, hxV, g, hg, hT⟩ := (notMem_singularSupport_iff hx.1).1 h.2
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, f + g, (hf.mono inter_subset_left).add
    (hg.mono inter_subset_right), fun φ hφ ↦ ?_⟩
  have hφU := hφ.trans inter_subset_left
  have hφV := hφ.trans inter_subset_right
  have hfU := hf.continuousOn.locallyIntegrableOn (μ := volume) hU.measurableSet
  have hgV := hg.continuousOn.locallyIntegrableOn (μ := volume) hV.measurableSet
  rw [add_apply, hS φ hφU, hT φ hφV, ← integral_add
    (hfU.integrable_smul_left_of_hasCompactSupport φ.continuous φ.hasCompactSupport hφU)
    (hgV.integrable_smul_left_of_hasCompactSupport φ.continuous φ.hasCompactSupport hφV)]
  simp [smul_add]

/-- The singular support of a finite sum lies in the union of the singular supports. -/
theorem singularSupport_sum_subset {ι : Type*} (s : Finset ι) (T : ι → 𝓓'(Ω, F)) :
    (∑ i ∈ s, T i).singularSupport ⊆ ⋃ i ∈ s, (T i).singularSupport := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.set_biUnion_insert]
    exact (singularSupport_add_subset _ _).trans (union_subset_union_right _ ih)

section SMul

variable {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass ℝ M F]
  [ContinuousConstSMul M F]

/-- A scalar multiple of a distribution has no larger singular support. -/
theorem singularSupport_smul_subset (c : M) (T : 𝓓'(Ω, F)) :
    (c • T).singularSupport ⊆ T.singularSupport := by
  refine fun x hx ↦ ⟨hx.1, fun ⟨U, hU, hxU, f, hf, hT⟩ ↦ hx.2 ⟨U, hU, hxU, fun y ↦ c • f y,
    hf.const_smul c, fun φ hφ ↦ ?_⟩⟩
  have hcv : ∀ v : F, (c • ContinuousLinearMap.id ℝ F) v = c • v := fun _ ↦ rfl
  rw [smul_apply, hT φ hφ]
  by_cases hF : CompleteSpace F
  · have hfU := hf.continuousOn.locallyIntegrableOn (μ := volume) hU.measurableSet
    simp_rw [← hcv, ← map_smul]
    exact (ContinuousLinearMap.integral_comp_comm _
      (hfU.integrable_smul_left_of_hasCompactSupport φ.continuous φ.hasCompactSupport hφ)).symm
  · simp [integral_of_not_completeSpace hF]

/-- Multiplication by a unit does not change the singular support. -/
theorem _root_.IsUnit.singularSupport_smul {c : M} (hc : IsUnit c) (T : 𝓓'(Ω, F)) :
    (c • T).singularSupport = T.singularSupport := by
  obtain ⟨u, rfl⟩ := hc
  refine (singularSupport_smul_subset _ T).antisymm ?_
  simpa [smul_smul] using singularSupport_smul_subset (↑u⁻¹ : M) ((u : M) • T)

end SMul

/-- Multiplication by a nonzero scalar does not change the singular support. -/
@[simp]
theorem singularSupport_smul {G₀ : Type*} [GroupWithZero G₀] [DistribMulAction G₀ F]
    [SMulCommClass ℝ G₀ F] [ContinuousConstSMul G₀ F] {c : G₀} (hc : c ≠ 0)
    (T : 𝓓'(Ω, F)) : (c • T).singularSupport = T.singularSupport :=
  hc.isUnit.singularSupport_smul T

/-- Negation does not change the singular support. -/
@[simp]
theorem singularSupport_neg (T : 𝓓'(Ω, F)) : (-T).singularSupport = T.singularSupport := by
  rw [← neg_one_smul ℝ T, singularSupport_smul (neg_ne_zero.2 one_ne_zero)]

/-- The singular support of a difference lies in the union of the singular supports. -/
theorem singularSupport_sub_subset (S T : 𝓓'(Ω, F)) :
    (S - T).singularSupport ⊆ S.singularSupport ∪ T.singularSupport := by
  simpa [sub_eq_add_neg] using singularSupport_add_subset S (-T)

/-! ### The distribution is a smooth function off its singular support -/

section Gluing

/-- Two functions continuous on an open set `U ⊆ Ω` that give the same integral against every
real test function supported in `U` agree on `U`. -/
theorem eqOn_of_forall_integral_smul_eq [CompleteSpace F] {U : Set E} (hU : IsOpen U)
    (hUΩ : U ⊆ Ω) {f g : E → F} (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (h : ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → ∫ y, φ y • f y = ∫ y, φ y • g y) :
    EqOn f g U := by
  let U' : Opens E := ⟨U, hU⟩
  have hUΩ' : U' ≤ Ω := hUΩ
  have hfU := hf.locallyIntegrableOn (μ := volume) hU.measurableSet
  have hgU := hg.locallyIntegrableOn (μ := volume) hU.measurableSet
  refine Measure.eqOn_open_of_ae_eq (ofFun_injective (Ω := U') (n := ⊤) hfU hgU ?_) hU hf hg
  -- A test function on `U` is a test function on `Ω` supported in `U`.
  ext ψ
  have hψ : (TestFunction.monoCLM ℝ ψ : 𝓓(Ω, ℝ)) = (ψ : E → ℝ) := by
    simp [TestFunction.monoCLM_apply, hUΩ']
  rw [ofFun_apply hfU, ofFun_apply hgU, ← hψ]
  exact h _ (hψ ▸ ψ.tsupport_subset)

/-- **Integral representations glue.** If `f` is locally integrable on an open set `W` and every
point of `W` has an open neighbourhood on whose supported real test functions `T` is integration
against `f`, then `T φ = ∫ φ • f` for every real test function `φ` supported in `W`. -/
theorem apply_eq_integral_of_locally {n : ℕ∞} {T : 𝓓'^{n}(Ω, F)} {W : Set E} (hW : IsOpen W)
    {f : E → F} (hf : LocallyIntegrableOn f W)
    (h : ∀ x ∈ W, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      ∀ φ : 𝓓^{n}(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y)
    {φ : 𝓓^{n}(Ω, ℝ)} (hφ : tsupport φ ⊆ W) : T φ = ∫ y, φ y • f y := by
  classical
  choose U hU hxU hT using fun x : W ↦ h x x.2
  obtain ⟨s, ψ, hψ, hsum, -⟩ := φ.exists_sum_subordinate (fun x : W ↦ U x ∩ W)
    (fun x ↦ (hU x).inter hW) fun y hy ↦ mem_iUnion.2 ⟨⟨y, hφ hy⟩, hxU _, hφ hy⟩
  have hint (i : s) : Integrable fun y ↦ ψ i y • f y :=
    hf.integrable_smul_left_of_hasCompactSupport (ψ i).continuous (ψ i).hasCompactSupport
      ((hψ i).trans inter_subset_right)
  rw [← hsum, map_sum,
    Finset.sum_congr rfl fun (i : s) _ ↦ hT i (ψ i) ((hψ i).trans inter_subset_left),
    ← integral_finsetSum _ fun i _ ↦ hint i]
  simp [Finset.sum_smul]

/-- **A distribution is a smooth function off its singular support.** There is one function `f`,
smooth on `Ω \ singularSupport T`, such that `T φ = ∫ φ • f` for every real test function `φ`
supported in `Ω \ singularSupport T`. -/
theorem exists_contDiffOn_apply_eq_integral (T : 𝓓'(Ω, F)) :
    ∃ f : E → F, ContDiffOn ℝ ∞ f ((Ω : Set E) \ T.singularSupport) ∧
      ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ (Ω : Set E) \ T.singularSupport → T φ = ∫ y, φ y • f y := by
  classical
  set W := (Ω : Set E) \ T.singularSupport
  have hW : IsOpen W := isOpen_diff_singularSupport T
  -- Every point of `W` has an open neighbourhood in `W` on which `T` is a smooth function.
  have hloc (x : W) : ∃ U : Set E, IsOpen U ∧ (x : E) ∈ U ∧ U ⊆ W ∧ ∃ f : E → F,
      ContDiffOn ℝ ∞ f U ∧ ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y := by
    obtain ⟨U, hU, hxU, f, hf, hT⟩ := (notMem_singularSupport_iff x.2.1).1 x.2.2
    exact ⟨U ∩ Ω, hU.inter Ω.isOpen, ⟨hxU, x.2.1⟩,
      fun y hy ↦ ⟨hy.2, fun hys ↦ hys.2 ⟨U, hU, hy.1, f, hf, hT⟩⟩, f,
      hf.mono inter_subset_left, fun φ hφ ↦ hT φ (hφ.trans inter_subset_left)⟩
  choose U hU hxU hUW f hf hT using hloc
  by_cases hF : CompleteSpace F
  swap
  · -- Without completeness every integral vanishes, and so does `T` on `W`.
    refine ⟨0, contDiffOn_const, fun φ hφ ↦ apply_eq_integral_of_locally hW
      locallyIntegrableOn_zero (fun x hx ↦ ⟨U ⟨x, hx⟩, hU _, hxU _, fun ψ hψ ↦ ?_⟩) hφ⟩
    simp [hT _ ψ hψ, integral_of_not_completeSpace hF]
  -- The local representatives agree on overlaps, so they glue to `g`.
  have hcompat (x y : W) : EqOn (f x) (f y) (U x ∩ U y) :=
    eqOn_of_forall_integral_smul_eq ((hU x).inter (hU y))
      ((inter_subset_left.trans (hUW x)).trans sdiff_subset)
      ((hf x).continuousOn.mono inter_subset_left) ((hf y).continuousOn.mono inter_subset_right)
      fun φ hφ ↦ (hT x φ (hφ.trans inter_subset_left)).symm.trans
        (hT y φ (hφ.trans inter_subset_right))
  let g : E → F := fun y ↦ if hy : y ∈ W then f ⟨y, hy⟩ y else 0
  have hg (x : W) : EqOn g (f x) (U x) := fun y hy ↦ by
    simp only [g, hUW x hy, ↓reduceDIte]
    exact hcompat ⟨y, hUW x hy⟩ x ⟨hxU _, hy⟩
  have hgW : ContDiffOn ℝ ∞ g W := fun x hx ↦
    (((hf ⟨x, hx⟩).contDiffAt ((hU _).mem_nhds (hxU _))).congr_of_eventuallyEq
      (Filter.eventually_of_mem ((hU _).mem_nhds (hxU _)) (hg ⟨x, hx⟩))).contDiffWithinAt
  refine ⟨g, hgW, fun φ hφ ↦ apply_eq_integral_of_locally hW
    (hgW.continuousOn.locallyIntegrableOn hW.measurableSet)
    (fun x hx ↦ ⟨U ⟨x, hx⟩, hU _, hxU _, fun ψ hψ ↦ ?_⟩) hφ⟩
  rw [hT _ ψ hψ]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  by_cases hy : ψ y = 0
  · simp [hy]
  · simp only [hg _ (hψ (subset_tsupport _ hy))]

/-- A distribution has empty singular support exactly when it is a function smooth on `Ω`. -/
theorem singularSupport_eq_empty_iff {T : 𝓓'(Ω, F)} :
    T.singularSupport = ∅ ↔ ∃ f : E → F, ContDiffOn ℝ ∞ f Ω ∧ T = ofFun Ω f volume ⊤ := by
  refine ⟨fun h ↦ ?_, fun ⟨f, hf, hT⟩ ↦ hT ▸ singularSupport_ofFun_eq_empty hf⟩
  obtain ⟨f, hf, hT⟩ := exists_contDiffOn_apply_eq_integral T
  rw [h, sdiff_empty] at hf hT
  refine ⟨f, hf, ?_⟩
  ext φ
  rw [hT φ φ.tsupport_subset,
    ofFun_apply (hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)]

end Gluing

end Distribution
