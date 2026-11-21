/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.SingularSupport
public import TauCeti.Analysis.Distribution.WaveFrontSet.VectorValued
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity

/-!
# The Sobolev wave front set of a vector-valued distribution

Let `F` be a complex normed space and `T : 𝓓'(Ω, F)` a distribution with values in `F`. Each
complex-linear functional `ℓ : F →L[ℂ] ℂ` gives a complex component `ℓ ∘ T : 𝓓'(Ω, ℂ)`. As for the
wave front set (`Distribution.vectorWaveFrontSet`), the **`H^s` wave front set** of `T`
(`Distribution.vectorSobolevWaveFrontSet s T`) is the union of the `H^s` wave front sets of these
components, and the **`H^s` singular support** of `T`
(`Distribution.vectorSobolevSingularSupport s T`) is the union of their `H^s` singular supports:
the points near which some component is not `H^s`.

When `F` is finite dimensional and `(bᵢ)` is a basis of `F` (a frame), every component is a linear
combination of the frame components `bᵢ* ∘ T`, so both sets are the unions over the frame
components alone, for any frame (`Distribution.vectorSobolevWaveFrontSet_eq_iUnion_basis`,
`Distribution.vectorSobolevSingularSupport_eq_iUnion_basis`). This is the notion of local Sobolev
regularity of distributions with values in a vector bundle, where `T` is localized in a chart and
trivialized by a frame; the results here show that it does not depend on the frame. A smooth change
of frame `G = ∑ᵢ gᵢ Aᵢ : E → (F →L[ℂ] F')` does not enlarge either set
(`Distribution.vectorSobolevWaveFrontSet_sum_mapCLM_smulLeftCLM_subset`,
`Distribution.vectorSobolevSingularSupport_sum_mapCLM_smulLeftCLM_subset`).

For finite-dimensional `F` a single cutoff witnesses the regularity of all components at once. A
point `x ∈ Ω` lies outside the `H^s` singular support of `T` exactly when some test function `φ`
with `φ x ≠ 0` makes `η ↦ ⟨η⟩ ^ s (ℓ ∘ T) (φ e_η)` square integrable for every `ℓ`, that is,
`φ T ∈ H^s` componentwise (`Distribution.notMem_vectorSobolevSingularSupport_iff`); the microlocal
counterpart, with one cutoff and one cone, is `Distribution.notMem_vectorSobolevWaveFrontSet_iff`.
Consequently both sets are relatively closed (`Distribution.isOpen_diff_vectorSobolevWaveFrontSet`,
`Distribution.isOpen_diff_vectorSobolevSingularSupport`), and every vector-valued distribution has a
finite Sobolev order near every compact set
(`Distribution.exists_disjoint_vectorSobolevSingularSupport`).

## Main declarations

* `Distribution.vectorSobolevWaveFrontSet s T`: the `H^s` wave front set of an `F`-valued
  distribution.
* `Distribution.vectorSobolevSingularSupport s T`: its `H^s` singular support, the projection of
  the `H^s` wave front set (`Distribution.fst_image_vectorSobolevWaveFrontSet`).
* `Distribution.vectorSobolevWaveFrontSet_eq_sobolevWaveFrontSet`,
  `Distribution.vectorSobolevSingularSupport_eq_sobolevSingularSupport`: for `F = ℂ` they are the
  `H^s` wave front set and the `H^s` singular support of `T`.
* `Distribution.vectorSobolevWaveFrontSet_eq_iUnion_basis`,
  `Distribution.vectorSobolevSingularSupport_eq_iUnion_basis`: independence of the frame.
* `Distribution.notMem_vectorSobolevWaveFrontSet_iff`,
  `Distribution.notMem_vectorSobolevSingularSupport_iff`: one cutoff serves all components.
* `Distribution.vectorSobolevWaveFrontSet_sum_mapCLM_smulLeftCLM_subset`,
  `Distribution.vectorSobolevSingularSupport_sum_mapCLM_smulLeftCLM_subset`: smooth changes of
  frame.
* `Distribution.exists_disjoint_vectorSobolevSingularSupport`: the local finite Sobolev order.
* `Distribution.vectorSobolevWaveFrontSet_mapCLM_toSpanSingleton_delta_eq_empty`,
  `Distribution.vectorSobolevSingularSupport_mapCLM_toSpanSingleton_delta_eq_empty`: in dimension
  `d`, the point mass `δ_{x₀} v` is `H^s` for `s < -d / 2`.
* `Distribution.vectorSobolevWaveFrontSet_mapCLM_toSpanSingleton_delta`,
  `Distribution.vectorSobolevSingularSupport_mapCLM_toSpanSingleton_delta`: in dimension `d > 0`,
  the point mass `δ_{x₀} v` at `x₀ ∈ Ω` with `v ≠ 0` is not `H^s` at `x₀` for `s ≥ -d / 2`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.1 (the wave front set of a vector-valued distribution as the union over its
  components).
* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997,
  §11.1 (the `H^s` wave front set).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, Lecture I, §7.
-/

public section

noncomputable section

open Complex Filter Module Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions Topology ContDiff InnerProduct

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}
  {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup F'] [NormedSpace ℂ F']

/-! ### The `H^s` wave front set -/

/-- The **`H^s` wave front set** of a distribution `T` with values in a complex normed space `F`:
the union of the `H^s` wave front sets of its complex components `ℓ ∘ T`, for `ℓ : F →L[ℂ] ℂ`. -/
def vectorSobolevWaveFrontSet (s : ℝ) (T : 𝓓'(Ω, F)) : Set (E × E) :=
  ⋃ ℓ : F →L[ℂ] ℂ, (mapCLM (ℓ.restrictScalars ℝ) T).sobolevWaveFrontSet s

theorem mem_vectorSobolevWaveFrontSet_iff {s : ℝ} {T : 𝓓'(Ω, F)} {p : E × E} :
    p ∈ T.vectorSobolevWaveFrontSet s ↔
      ∃ ℓ : F →L[ℂ] ℂ, p ∈ (mapCLM (ℓ.restrictScalars ℝ) T).sobolevWaveFrontSet s :=
  mem_iUnion

/-- The `H^s` wave front set of each component lies in the `H^s` wave front set. -/
theorem sobolevWaveFrontSet_mapCLM_subset_vectorSobolevWaveFrontSet (s : ℝ) (ℓ : F →L[ℂ] ℂ)
    (T : 𝓓'(Ω, F)) :
    (mapCLM (ℓ.restrictScalars ℝ) T).sobolevWaveFrontSet s ⊆ T.vectorSobolevWaveFrontSet s :=
  subset_iUnion (fun ℓ : F →L[ℂ] ℂ ↦ (mapCLM (ℓ.restrictScalars ℝ) T).sobolevWaveFrontSet s) ℓ

/-- The `H^s` wave front set lies in `Ω × (E \ {0})`. -/
theorem vectorSobolevWaveFrontSet_subset (s : ℝ) (T : 𝓓'(Ω, F)) :
    T.vectorSobolevWaveFrontSet s ⊆ (Ω : Set E) ×ˢ {0}ᶜ :=
  iUnion_subset fun _ ↦ sobolevWaveFrontSet_subset _ _

/-- The `H^s` wave front set is conic in the frequency variable. -/
theorem smul_mem_vectorSobolevWaveFrontSet_iff {s : ℝ} {T : 𝓓'(Ω, F)} {x ξ : E} {t : ℝ}
    (ht : 0 < t) :
    (x, t • ξ) ∈ T.vectorSobolevWaveFrontSet s ↔ (x, ξ) ∈ T.vectorSobolevWaveFrontSet s := by
  simp only [mem_vectorSobolevWaveFrontSet_iff, smul_mem_sobolevWaveFrontSet_iff ht]

/-- The `H^s` wave front set grows with `s`. -/
theorem vectorSobolevWaveFrontSet_mono {s t : ℝ} (hts : t ≤ s) (T : 𝓓'(Ω, F)) :
    T.vectorSobolevWaveFrontSet t ⊆ T.vectorSobolevWaveFrontSet s :=
  iUnion_mono fun _ ↦ sobolevWaveFrontSet_mono hts _

/-- The `H^s` wave front set is contained in the wave front set. -/
theorem vectorSobolevWaveFrontSet_subset_vectorWaveFrontSet (s : ℝ) (T : 𝓓'(Ω, F)) :
    T.vectorSobolevWaveFrontSet s ⊆ T.vectorWaveFrontSet :=
  iUnion_subset fun ℓ ↦ (sobolevWaveFrontSet_subset_waveFrontSet s _).trans
    (waveFrontSet_mapCLM_subset_vectorWaveFrontSet ℓ T)

/-- The `H^s` wave front set lies over the support of `T`. -/
theorem vectorSobolevWaveFrontSet_subset_dsupport (s : ℝ) (T : 𝓓'(Ω, F)) :
    T.vectorSobolevWaveFrontSet s ⊆ dsupport T ×ˢ univ :=
  (vectorSobolevWaveFrontSet_subset_vectorWaveFrontSet s T).trans
    (vectorWaveFrontSet_subset_dsupport T)

/-- For a complex distribution the `H^s` wave front set of `T` as a vector-valued distribution is
its `H^s` wave front set: every component is a scalar multiple of `T`. -/
@[simp]
theorem vectorSobolevWaveFrontSet_eq_sobolevWaveFrontSet (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    T.vectorSobolevWaveFrontSet s = T.sobolevWaveFrontSet s := by
  refine (iUnion_subset fun ℓ ↦ ?_).antisymm ?_
  · rw [mapCLM_restrictScalars_eq_smul]
    exact sobolevWaveFrontSet_smul_subset s _ T
  · exact mapCLM_restrictScalars_id T ▸
      sobolevWaveFrontSet_mapCLM_subset_vectorSobolevWaveFrontSet s (.id ℂ ℂ) T

/-! #### Linear maps of the values and scalar multiples -/

/-- A complex-linear map of the values does not enlarge the `H^s` wave front set. -/
theorem vectorSobolevWaveFrontSet_mapCLM_subset (s : ℝ) (A : F →L[ℂ] F') (T : 𝓓'(Ω, F)) :
    (mapCLM (A.restrictScalars ℝ) T).vectorSobolevWaveFrontSet s ⊆
      T.vectorSobolevWaveFrontSet s :=
  iUnion_subset fun ℓ ↦ sobolevWaveFrontSet_mapCLM_subset_vectorSobolevWaveFrontSet s (ℓ.comp A) T

/-- An isomorphism of the values preserves the `H^s` wave front set. -/
@[simp]
theorem vectorSobolevWaveFrontSet_mapCLM_equiv (s : ℝ) (A : F ≃L[ℂ] F') (T : 𝓓'(Ω, F)) :
    (mapCLM ((A : F →L[ℂ] F').restrictScalars ℝ) T).vectorSobolevWaveFrontSet s =
      T.vectorSobolevWaveFrontSet s := by
  refine (vectorSobolevWaveFrontSet_mapCLM_subset s _ T).antisymm ?_
  conv_lhs => rw [← mapCLM_restrictScalars_symm_mapCLM A T]
  exact vectorSobolevWaveFrontSet_mapCLM_subset s _ _

/-- A scalar multiple of `T` has `H^s` wave front set contained in that of `T`. -/
theorem vectorSobolevWaveFrontSet_smul_subset (s : ℝ) (c : ℂ) (T : 𝓓'(Ω, F)) :
    (c • T).vectorSobolevWaveFrontSet s ⊆ T.vectorSobolevWaveFrontSet s :=
  iUnion_subset fun ℓ ↦ by
    rw [mapCLM_restrictScalars_smul]
    exact (sobolevWaveFrontSet_smul_subset s c _).trans
      (sobolevWaveFrontSet_mapCLM_subset_vectorSobolevWaveFrontSet s ℓ T)

/-- A nonzero scalar multiple of `T` has the same `H^s` wave front set as `T`. -/
@[simp]
theorem vectorSobolevWaveFrontSet_smul (s : ℝ) {c : ℂ} (hc : c ≠ 0) (T : 𝓓'(Ω, F)) :
    (c • T).vectorSobolevWaveFrontSet s = T.vectorSobolevWaveFrontSet s := by
  refine (vectorSobolevWaveFrontSet_smul_subset s c T).antisymm ?_
  simpa [smul_smul, inv_mul_cancel₀ hc] using vectorSobolevWaveFrontSet_smul_subset s c⁻¹ (c • T)

/-- The negative of `T` has the same `H^s` wave front set as `T`. -/
@[simp]
theorem vectorSobolevWaveFrontSet_neg (s : ℝ) (T : 𝓓'(Ω, F)) :
    (-T).vectorSobolevWaveFrontSet s = T.vectorSobolevWaveFrontSet s := by
  rw [← neg_one_smul ℂ T, vectorSobolevWaveFrontSet_smul s (neg_ne_zero.2 one_ne_zero)]

/-- The zero distribution has empty `H^s` wave front set. -/
@[simp]
theorem vectorSobolevWaveFrontSet_zero (s : ℝ) :
    (0 : 𝓓'(Ω, F)).vectorSobolevWaveFrontSet s = ∅ := by
  simp [vectorSobolevWaveFrontSet]

/-! #### Sums -/

/-- The `H^s` wave front set of a sum lies in the union of the `H^s` wave front sets. -/
theorem vectorSobolevWaveFrontSet_add_subset (s : ℝ) (S T : 𝓓'(Ω, F)) :
    (S + T).vectorSobolevWaveFrontSet s ⊆
      S.vectorSobolevWaveFrontSet s ∪ T.vectorSobolevWaveFrontSet s :=
  iUnion_subset fun ℓ ↦ by
    rw [map_add]
    exact (sobolevWaveFrontSet_add_subset s _ _).trans <| union_subset_union
      (sobolevWaveFrontSet_mapCLM_subset_vectorSobolevWaveFrontSet s ℓ S)
      (sobolevWaveFrontSet_mapCLM_subset_vectorSobolevWaveFrontSet s ℓ T)

/-- The `H^s` wave front set of a finite sum lies in the union of the `H^s` wave front sets. -/
theorem vectorSobolevWaveFrontSet_sum_subset (s : ℝ) {ι : Type*} (t : Finset ι)
    (T : ι → 𝓓'(Ω, F)) :
    (∑ i ∈ t, T i).vectorSobolevWaveFrontSet s ⊆ ⋃ i ∈ t, (T i).vectorSobolevWaveFrontSet s :=
  iUnion_subset fun ℓ ↦ by
    rw [map_sum]
    exact (sobolevWaveFrontSet_sum_subset s _ _).trans <| iUnion₂_mono fun i _ ↦
      sobolevWaveFrontSet_mapCLM_subset_vectorSobolevWaveFrontSet s ℓ (T i)

/-- The `H^s` wave front set of a difference lies in the union of the `H^s` wave front sets. -/
theorem vectorSobolevWaveFrontSet_sub_subset (s : ℝ) (S T : 𝓓'(Ω, F)) :
    (S - T).vectorSobolevWaveFrontSet s ⊆
      S.vectorSobolevWaveFrontSet s ∪ T.vectorSobolevWaveFrontSet s := by
  simpa [sub_eq_add_neg] using vectorSobolevWaveFrontSet_add_subset s S (-T)

/-! #### Smooth multiples, restriction and linear changes of coordinates -/

section SmulLeft

variable {g : E → ℝ}

/-- The `H^s` wave front set of a smooth multiple `g T` lies in that of `T` over `tsupport g`. -/
theorem vectorSobolevWaveFrontSet_smulLeftCLM_subset (s : ℝ) (T : 𝓓'(Ω, F))
    (hg : ContDiff ℝ ∞ g) :
    (smulLeftCLM hg T).vectorSobolevWaveFrontSet s ⊆
      T.vectorSobolevWaveFrontSet s ∩ tsupport g ×ˢ univ :=
  iUnion_subset fun ℓ ↦ by
    rw [mapCLM_smulLeftCLM]
    exact (sobolevWaveFrontSet_smulLeftCLM_subset s _ hg).trans <|
      inter_subset_inter_left _ (sobolevWaveFrontSet_mapCLM_subset_vectorSobolevWaveFrontSet s ℓ T)

/-- At a point where `g ≠ 0`, the smooth multiple `g T` has the same `H^s` wave front set as
`T`. -/
theorem mem_vectorSobolevWaveFrontSet_smulLeftCLM_iff {s : ℝ} {T : 𝓓'(Ω, F)} {x ξ : E}
    (hg : ContDiff ℝ ∞ g) (hx : g x ≠ 0) :
    (x, ξ) ∈ (smulLeftCLM hg T).vectorSobolevWaveFrontSet s ↔
      (x, ξ) ∈ T.vectorSobolevWaveFrontSet s := by
  simp only [mem_vectorSobolevWaveFrontSet_iff, mapCLM_smulLeftCLM,
    mem_sobolevWaveFrontSet_smulLeftCLM_iff hg hx]

/-- Multiplying by a smooth function that vanishes nowhere on `Ω` does not change the `H^s` wave
front set. -/
theorem vectorSobolevWaveFrontSet_smulLeftCLM_of_ne_zero (s : ℝ) (T : 𝓓'(Ω, F))
    (hg : ContDiff ℝ ∞ g) (hg0 : ∀ x ∈ Ω, g x ≠ 0) :
    (smulLeftCLM hg T).vectorSobolevWaveFrontSet s = T.vectorSobolevWaveFrontSet s := by
  simp only [vectorSobolevWaveFrontSet, mapCLM_smulLeftCLM,
    sobolevWaveFrontSet_smulLeftCLM_of_ne_zero s _ hg hg0]

/-- **Smooth changes of frame.** For smooth real functions `gᵢ` and complex-linear maps
`Aᵢ : F →L[ℂ] F'`, the distribution `∑ᵢ Aᵢ (gᵢ T)` has `H^s` wave front set contained in that of
`T`. This sum is the product of `T` with the smooth function `G = ∑ᵢ gᵢ Aᵢ : E → (F →L[ℂ] F')`. -/
theorem vectorSobolevWaveFrontSet_sum_mapCLM_smulLeftCLM_subset (s : ℝ) {ι : Type*}
    (t : Finset ι) (A : ι → F →L[ℂ] F') {g : ι → E → ℝ} (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (T : 𝓓'(Ω, F)) :
    (∑ i ∈ t, mapCLM ((A i).restrictScalars ℝ) (smulLeftCLM (hg i) T)).vectorSobolevWaveFrontSet
      s ⊆ T.vectorSobolevWaveFrontSet s :=
  (vectorSobolevWaveFrontSet_sum_subset s _ _).trans <| iUnion₂_subset fun i _ ↦
    (vectorSobolevWaveFrontSet_mapCLM_subset s _ _).trans <|
      (vectorSobolevWaveFrontSet_smulLeftCLM_subset s T (hg i)).trans inter_subset_left

end SmulLeft

section Restriction

variable {Ω' : Opens E}

/-- For an open subset `Ω' ≤ Ω`, the `H^s` wave front set of the restriction `T|_{Ω'}` is the part
of the `H^s` wave front set of `T` lying over `Ω'`. -/
theorem vectorSobolevWaveFrontSet_restrictCLM (h : Ω' ≤ Ω) (s : ℝ) (T : 𝓓'(Ω, F)) :
    (restrictCLM T : 𝓓'(Ω', F)).vectorSobolevWaveFrontSet s =
      T.vectorSobolevWaveFrontSet s ∩ (Ω' : Set E) ×ˢ univ := by
  simp only [vectorSobolevWaveFrontSet, mapCLM_restrictCLM, sobolevWaveFrontSet_restrictCLM h,
    iUnion_inter]

end Restriction

section LinearEquiv

variable {V : Opens E}

/-- **Linear changes of coordinates.** If a linear automorphism `e` of `E` identifies `V` with
`Ω`, then `(x, ξ)` lies in the `H^s` wave front set of the pullback `e^* T` exactly when
`(e x, (e⁻¹)ᵀ ξ)` lies in that of `T`. -/
theorem vectorSobolevWaveFrontSet_compCLMOfContinuousLinearEquiv (s : ℝ) (e : E ≃L[ℝ] E)
    (hVO : MapsTo e V Ω) (hOV : MapsTo e.symm Ω V) (T : 𝓓'(Ω, F)) :
    (compCLMOfContinuousLinearEquiv e hVO T).vectorSobolevWaveFrontSet s =
      Prod.map e ((e.symm : E →L[ℝ] E)†) ⁻¹' T.vectorSobolevWaveFrontSet s := by
  simp only [vectorSobolevWaveFrontSet, mapCLM_compCLMOfContinuousLinearEquiv,
    sobolevWaveFrontSet_compCLMOfContinuousLinearEquiv s e hVO hOV, preimage_iUnion]

end LinearEquiv

/-! ### The `H^s` singular support -/

/-- The **`H^s` singular support** of a distribution `T` with values in a complex normed space `F`:
the union of the `H^s` singular supports of its complex components `ℓ ∘ T`, for `ℓ : F →L[ℂ] ℂ`,
that is, the points of `Ω` near which some component of `T` is not `H^s`. -/
def vectorSobolevSingularSupport (s : ℝ) (T : 𝓓'(Ω, F)) : Set E :=
  ⋃ ℓ : F →L[ℂ] ℂ, (mapCLM (ℓ.restrictScalars ℝ) T).sobolevSingularSupport s

theorem mem_vectorSobolevSingularSupport_iff {s : ℝ} {T : 𝓓'(Ω, F)} {x : E} :
    x ∈ T.vectorSobolevSingularSupport s ↔
      ∃ ℓ : F →L[ℂ] ℂ, x ∈ (mapCLM (ℓ.restrictScalars ℝ) T).sobolevSingularSupport s :=
  mem_iUnion

/-- A point of `Ω` lies outside the `H^s` singular support of `T` exactly when every component of
`T` is `H^s` near it. -/
theorem notMem_vectorSobolevSingularSupport_iff_forall_isLocallySobolevAt {s : ℝ}
    {T : 𝓓'(Ω, F)} {x : E} (hx : x ∈ Ω) :
    x ∉ T.vectorSobolevSingularSupport s ↔
      ∀ ℓ : F →L[ℂ] ℂ, (mapCLM (ℓ.restrictScalars ℝ) T).IsLocallySobolevAt s x := by
  simp [mem_vectorSobolevSingularSupport_iff, hx]

/-- The `H^s` singular support of each component lies in the `H^s` singular support. -/
theorem sobolevSingularSupport_mapCLM_subset_vectorSobolevSingularSupport (s : ℝ)
    (ℓ : F →L[ℂ] ℂ) (T : 𝓓'(Ω, F)) :
    (mapCLM (ℓ.restrictScalars ℝ) T).sobolevSingularSupport s ⊆
      T.vectorSobolevSingularSupport s :=
  subset_iUnion (fun ℓ : F →L[ℂ] ℂ ↦ (mapCLM (ℓ.restrictScalars ℝ) T).sobolevSingularSupport s) ℓ

/-- **The projection of the `H^s` wave front set is the `H^s` singular support.** -/
theorem fst_image_vectorSobolevWaveFrontSet (s : ℝ) (T : 𝓓'(Ω, F)) :
    Prod.fst '' T.vectorSobolevWaveFrontSet s = T.vectorSobolevSingularSupport s := by
  simp only [vectorSobolevWaveFrontSet, vectorSobolevSingularSupport, image_iUnion,
    fst_image_sobolevWaveFrontSet]

/-- A distribution has empty `H^s` singular support exactly when it has empty `H^s` wave front
set. -/
theorem vectorSobolevSingularSupport_eq_empty_iff {s : ℝ} {T : 𝓓'(Ω, F)} :
    T.vectorSobolevSingularSupport s = ∅ ↔ T.vectorSobolevWaveFrontSet s = ∅ := by
  rw [← fst_image_vectorSobolevWaveFrontSet, image_eq_empty]

/-- The `H^s` singular support lies in `Ω`. -/
theorem vectorSobolevSingularSupport_subset (s : ℝ) (T : 𝓓'(Ω, F)) :
    T.vectorSobolevSingularSupport s ⊆ Ω :=
  iUnion_subset fun _ ↦ sobolevSingularSupport_subset _ _

/-- The `H^s` singular support grows with `s`. -/
theorem vectorSobolevSingularSupport_mono {s t : ℝ} (hts : t ≤ s) (T : 𝓓'(Ω, F)) :
    T.vectorSobolevSingularSupport t ⊆ T.vectorSobolevSingularSupport s :=
  iUnion_mono fun _ ↦ sobolevSingularSupport_mono hts _

/-- The `H^s` singular support lies in the support. -/
theorem vectorSobolevSingularSupport_subset_dsupport (s : ℝ) (T : 𝓓'(Ω, F)) :
    T.vectorSobolevSingularSupport s ⊆ dsupport T := by
  rw [← fst_image_vectorSobolevWaveFrontSet]
  exact (image_mono (vectorSobolevWaveFrontSet_subset_dsupport s T)).trans
    (fst_image_prod_subset _ _)

/-- For a complex distribution the `H^s` singular support of `T` as a vector-valued distribution
is its `H^s` singular support. -/
@[simp]
theorem vectorSobolevSingularSupport_eq_sobolevSingularSupport (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    T.vectorSobolevSingularSupport s = T.sobolevSingularSupport s := by
  rw [← fst_image_vectorSobolevWaveFrontSet, vectorSobolevWaveFrontSet_eq_sobolevWaveFrontSet,
    fst_image_sobolevWaveFrontSet]

/-- A complex-linear map of the values does not enlarge the `H^s` singular support. -/
theorem vectorSobolevSingularSupport_mapCLM_subset (s : ℝ) (A : F →L[ℂ] F') (T : 𝓓'(Ω, F)) :
    (mapCLM (A.restrictScalars ℝ) T).vectorSobolevSingularSupport s ⊆
      T.vectorSobolevSingularSupport s := by
  simp only [← fst_image_vectorSobolevWaveFrontSet]
  exact image_mono (vectorSobolevWaveFrontSet_mapCLM_subset s A T)

/-- An isomorphism of the values preserves the `H^s` singular support. -/
@[simp]
theorem vectorSobolevSingularSupport_mapCLM_equiv (s : ℝ) (A : F ≃L[ℂ] F') (T : 𝓓'(Ω, F)) :
    (mapCLM ((A : F →L[ℂ] F').restrictScalars ℝ) T).vectorSobolevSingularSupport s =
      T.vectorSobolevSingularSupport s := by
  simp only [← fst_image_vectorSobolevWaveFrontSet, vectorSobolevWaveFrontSet_mapCLM_equiv]

/-- A scalar multiple of `T` has `H^s` singular support contained in that of `T`. -/
theorem vectorSobolevSingularSupport_smul_subset (s : ℝ) (c : ℂ) (T : 𝓓'(Ω, F)) :
    (c • T).vectorSobolevSingularSupport s ⊆ T.vectorSobolevSingularSupport s := by
  simp only [← fst_image_vectorSobolevWaveFrontSet]
  exact image_mono (vectorSobolevWaveFrontSet_smul_subset s c T)

/-- A nonzero scalar multiple of `T` has the same `H^s` singular support as `T`. -/
@[simp]
theorem vectorSobolevSingularSupport_smul (s : ℝ) {c : ℂ} (hc : c ≠ 0) (T : 𝓓'(Ω, F)) :
    (c • T).vectorSobolevSingularSupport s = T.vectorSobolevSingularSupport s := by
  simp only [← fst_image_vectorSobolevWaveFrontSet, vectorSobolevWaveFrontSet_smul s hc]

/-- The negative of `T` has the same `H^s` singular support as `T`. -/
@[simp]
theorem vectorSobolevSingularSupport_neg (s : ℝ) (T : 𝓓'(Ω, F)) :
    (-T).vectorSobolevSingularSupport s = T.vectorSobolevSingularSupport s := by
  simp only [← fst_image_vectorSobolevWaveFrontSet, vectorSobolevWaveFrontSet_neg]

/-- The zero distribution has empty `H^s` singular support. -/
@[simp]
theorem vectorSobolevSingularSupport_zero (s : ℝ) :
    (0 : 𝓓'(Ω, F)).vectorSobolevSingularSupport s = ∅ := by
  simp [← fst_image_vectorSobolevWaveFrontSet]

/-- The `H^s` singular support of a sum lies in the union of the `H^s` singular supports. -/
theorem vectorSobolevSingularSupport_add_subset (s : ℝ) (S T : 𝓓'(Ω, F)) :
    (S + T).vectorSobolevSingularSupport s ⊆
      S.vectorSobolevSingularSupport s ∪ T.vectorSobolevSingularSupport s := by
  simp only [← fst_image_vectorSobolevWaveFrontSet, ← image_union]
  exact image_mono (vectorSobolevWaveFrontSet_add_subset s S T)

/-- The `H^s` singular support of a finite sum lies in the union of the `H^s` singular
supports. -/
theorem vectorSobolevSingularSupport_sum_subset (s : ℝ) {ι : Type*} (t : Finset ι)
    (T : ι → 𝓓'(Ω, F)) :
    (∑ i ∈ t, T i).vectorSobolevSingularSupport s ⊆
      ⋃ i ∈ t, (T i).vectorSobolevSingularSupport s := by
  simp only [← fst_image_vectorSobolevWaveFrontSet, ← image_iUnion₂]
  exact image_mono (vectorSobolevWaveFrontSet_sum_subset s t T)

/-- The `H^s` singular support of a difference lies in the union of the `H^s` singular
supports. -/
theorem vectorSobolevSingularSupport_sub_subset (s : ℝ) (S T : 𝓓'(Ω, F)) :
    (S - T).vectorSobolevSingularSupport s ⊆
      S.vectorSobolevSingularSupport s ∪ T.vectorSobolevSingularSupport s := by
  simp only [← fst_image_vectorSobolevWaveFrontSet, ← image_union]
  exact image_mono (vectorSobolevWaveFrontSet_sub_subset s S T)

/-- The `H^s` singular support of a smooth multiple `g T` lies in that of `T`, over the support of
`g`. -/
theorem vectorSobolevSingularSupport_smulLeftCLM_subset (s : ℝ) (T : 𝓓'(Ω, F)) {g : E → ℝ}
    (hg : ContDiff ℝ ∞ g) :
    (smulLeftCLM hg T).vectorSobolevSingularSupport s ⊆
      T.vectorSobolevSingularSupport s ∩ tsupport g := by
  rw [← fst_image_vectorSobolevWaveFrontSet, ← fst_image_vectorSobolevWaveFrontSet,
    ← image_inter_preimage, ← prod_univ]
  exact image_mono (vectorSobolevWaveFrontSet_smulLeftCLM_subset s T hg)

/-- At a point where `g ≠ 0`, the smooth multiple `g T` has the same `H^s` singular support as
`T`. -/
theorem mem_vectorSobolevSingularSupport_smulLeftCLM_iff {s : ℝ} {T : 𝓓'(Ω, F)} {g : E → ℝ}
    {x : E} (hg : ContDiff ℝ ∞ g) (hx : g x ≠ 0) :
    x ∈ (smulLeftCLM hg T).vectorSobolevSingularSupport s ↔
      x ∈ T.vectorSobolevSingularSupport s := by
  simp only [mem_vectorSobolevSingularSupport_iff, mapCLM_smulLeftCLM,
    mem_sobolevSingularSupport_smulLeftCLM_iff hg hx]

/-- Multiplying by a smooth function that vanishes nowhere on `Ω` does not change the `H^s`
singular support. -/
theorem vectorSobolevSingularSupport_smulLeftCLM_of_ne_zero (s : ℝ) (T : 𝓓'(Ω, F)) {g : E → ℝ}
    (hg : ContDiff ℝ ∞ g) (hg0 : ∀ x ∈ Ω, g x ≠ 0) :
    (smulLeftCLM hg T).vectorSobolevSingularSupport s = T.vectorSobolevSingularSupport s := by
  simp only [← fst_image_vectorSobolevWaveFrontSet,
    vectorSobolevWaveFrontSet_smulLeftCLM_of_ne_zero s T hg hg0]

/-- **Smooth changes of frame.** For smooth real functions `gᵢ` and complex-linear maps
`Aᵢ : F →L[ℂ] F'`, the distribution `∑ᵢ Aᵢ (gᵢ T)` has `H^s` singular support contained in that
of `T`. -/
theorem vectorSobolevSingularSupport_sum_mapCLM_smulLeftCLM_subset (s : ℝ) {ι : Type*}
    (t : Finset ι) (A : ι → F →L[ℂ] F') {g : ι → E → ℝ} (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (T : 𝓓'(Ω, F)) :
    (∑ i ∈ t, mapCLM ((A i).restrictScalars ℝ) (smulLeftCLM (hg i) T)).vectorSobolevSingularSupport
      s ⊆ T.vectorSobolevSingularSupport s := by
  simp only [← fst_image_vectorSobolevWaveFrontSet]
  exact image_mono (vectorSobolevWaveFrontSet_sum_mapCLM_smulLeftCLM_subset s t A hg T)

/-- **Restriction** to an open subset `Ω' ≤ Ω` cuts the `H^s` singular support down to the points
of `Ω'`. -/
theorem vectorSobolevSingularSupport_restrictCLM {Ω' : Opens E} (h : Ω' ≤ Ω) (s : ℝ)
    (T : 𝓓'(Ω, F)) :
    (restrictCLM T : 𝓓'(Ω', F)).vectorSobolevSingularSupport s =
      T.vectorSobolevSingularSupport s ∩ Ω' := by
  rw [← fst_image_vectorSobolevWaveFrontSet, ← fst_image_vectorSobolevWaveFrontSet,
    vectorSobolevWaveFrontSet_restrictCLM h, prod_univ, image_inter_preimage]

/-! ### Frames -/

section Frame

variable [FiniteDimensional ℂ F] {ι : Type*}

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- If every frame component of `T` has square-integrable weighted localized Fourier transform for
the cutoff `φ`, then so does every component. -/
private theorem memLp_weight_smul_localFourier_mapCLM_of_basis [Finite ι]
    (b : Module.Basis ι ℂ F) {s : ℝ} {T : 𝓓'(Ω, F)} {φ : 𝓓(Ω, ℂ)} {μ : Measure E}
    (h : ∀ i, MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) •
      (mapCLM ((b.coord i).toContinuousLinearMap.restrictScalars ℝ) T).localFourier φ η) 2 μ)
    (ℓ : F →L[ℂ] ℂ) :
    MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) •
      (mapCLM (ℓ.restrictScalars ℝ) T).localFourier φ η) 2 μ := by
  have := Fintype.ofFinite ι
  convert memLp_finsetSum Finset.univ fun i _ ↦ (h i).const_smul (ℓ (b i)) using 1
  funext η
  simp only [mapCLM_eq_sum_basis b ℓ T, localFourier_sum, localFourier_smul, Finset.smul_sum,
    Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **Independence of the frame.** For every basis `b` of `F`, the `H^s` wave front set of `T` is
the union of the `H^s` wave front sets of the frame components `bᵢ* ∘ T`. -/
theorem vectorSobolevWaveFrontSet_eq_iUnion_basis (s : ℝ) (b : Module.Basis ι ℂ F)
    (T : 𝓓'(Ω, F)) :
    T.vectorSobolevWaveFrontSet s =
      ⋃ i, (mapCLM ((b.coord i).toContinuousLinearMap.restrictScalars ℝ) T).sobolevWaveFrontSet
        s := by
  have := FiniteDimensional.fintypeBasisIndex b
  refine (iUnion_subset fun ℓ ↦ ?_).antisymm
    (iUnion_subset fun i ↦ sobolevWaveFrontSet_mapCLM_subset_vectorSobolevWaveFrontSet s _ T)
  rw [mapCLM_eq_sum_basis b]
  exact (sobolevWaveFrontSet_sum_subset s _ _).trans <| iUnion₂_subset fun i _ ↦
    (sobolevWaveFrontSet_smul_subset s _ _).trans (subset_iUnion_of_subset i subset_rfl)

/-- **Independence of the frame.** For every basis `b` of `F`, the `H^s` singular support of `T`
is the union of the `H^s` singular supports of the frame components `bᵢ* ∘ T`. -/
theorem vectorSobolevSingularSupport_eq_iUnion_basis (s : ℝ) (b : Module.Basis ι ℂ F)
    (T : 𝓓'(Ω, F)) :
    T.vectorSobolevSingularSupport s =
      ⋃ i, (mapCLM ((b.coord i).toContinuousLinearMap.restrictScalars ℝ) T).sobolevSingularSupport
        s := by
  simp only [← fst_image_vectorSobolevWaveFrontSet, vectorSobolevWaveFrontSet_eq_iUnion_basis s b,
    image_iUnion, fst_image_sobolevWaveFrontSet]

/-- **A common cutoff and cone.** A point `(x, ξ)` with `x ∈ Ω` and `ξ ≠ 0` lies outside the `H^s`
wave front set of `T` exactly when one test function `φ` with `φ x ≠ 0` and one open cone `Γ`
containing `ξ` witness that every component is microlocally `H^s`: the weighted localized Fourier
transforms `η ↦ ⟨η⟩ ^ s (ℓ ∘ T) (φ e_η)` are all square integrable on `Γ`. -/
theorem notMem_vectorSobolevWaveFrontSet_iff {s : ℝ} {T : 𝓓'(Ω, F)} {x ξ : E} (hx : x ∈ Ω)
    (hξ : ξ ≠ 0) :
    (x, ξ) ∉ T.vectorSobolevWaveFrontSet s ↔
      ∃ φ : 𝓓(Ω, ℂ), φ x ≠ 0 ∧ ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧
        (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧ ∀ ℓ : F →L[ℂ] ℂ,
          MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) •
            (mapCLM (ℓ.restrictScalars ℝ) T).localFourier φ η) 2 (volume.restrict Γ) := by
  refine ⟨fun h ↦ ?_, fun ⟨φ, hφ, Γ, hΓ, hξΓ, hcone, hL⟩ ↦ ?_⟩
  · set b := Module.finBasis ℂ F
    -- Each frame component is microlocally `H^s` at `(x, ξ)`, with a neighbourhood and a cone
    -- serving every cutoff supported in it.
    have hb (i : Fin (finrank ℂ F)) :
        (mapCLM ((b.coord i).toContinuousLinearMap.restrictScalars ℝ) T).IsMicrolocallySobolevAt
          s x ξ := by
      by_contra hi
      exact h (sobolevWaveFrontSet_mapCLM_subset_vectorSobolevWaveFrontSet s _ T
        (mem_sobolevWaveFrontSet_iff.2 ⟨hx, hξ, hi⟩))
    choose U hU Γ hΓ hξΓ hcone hL using fun i ↦ (hb i).exists_nhds_cone
    obtain ⟨φ, hφ, hφx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
      (inter_mem (Filter.iInter_mem.2 hU) (Ω.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
    refine ⟨φ, by simp [hφx], ⋂ i, Γ i, isOpen_iInter_of_finite hΓ, mem_iInter.2 hξΓ,
      fun t ht η hη ↦ mem_iInter.2 fun i ↦ hcone i t ht η (mem_iInter.1 hη i),
      memLp_weight_smul_localFourier_mapCLM_of_basis b fun i ↦ ?_⟩
    exact (hL i φ (hφ.trans (inter_subset_left.trans (iInter_subset U i)))).mono_measure
      (Measure.restrict_mono_set volume (iInter_subset Γ i))
  · rw [mem_vectorSobolevWaveFrontSet_iff, not_exists]
    exact fun ℓ hℓ ↦ (mem_sobolevWaveFrontSet_iff.1 hℓ).2.2
      (isMicrolocallySobolevAt_iff.2 ⟨φ, hφ, Γ, hΓ, hξΓ, hcone, hL ℓ⟩)

/-- The `H^s` wave front set is closed in `Ω × (E \ {0})`. -/
theorem isOpen_diff_vectorSobolevWaveFrontSet (s : ℝ) (T : 𝓓'(Ω, F)) :
    IsOpen (((Ω : Set E) ×ˢ {0}ᶜ) \ T.vectorSobolevWaveFrontSet s) := by
  refine isOpen_iff_mem_nhds.2 fun ⟨x, ξ⟩ ⟨⟨hx, hξ⟩, hp⟩ ↦ ?_
  -- A common cutoff `φ` and cone `Γ` at `(x, ξ)` serve at every point of `{φ ≠ 0} × Γ`.
  obtain ⟨φ, hφ, Γ, hΓ, hξΓ, hcone, hL⟩ := (notMem_vectorSobolevWaveFrontSet_iff hx hξ).1 hp
  have hU : IsOpen {y : E | φ y ≠ 0} := isOpen_ne_fun φ.continuous continuous_const
  filter_upwards [((Ω.isOpen.inter hU).prod (hΓ.inter isOpen_compl_singleton)).mem_nhds
    ⟨⟨hx, hφ⟩, hξΓ, hξ⟩] with q hq
  exact ⟨⟨hq.1.1, hq.2.2⟩, (notMem_vectorSobolevWaveFrontSet_iff hq.1.1 hq.2.2).2
    ⟨φ, hq.1.2, Γ, hΓ, hq.2.1, hcone, hL⟩⟩

/-- **A common cutoff.** A point `x ∈ Ω` lies outside the `H^s` singular support of `T` exactly
when one test function `φ` with `φ x ≠ 0` witnesses that every component is `H^s` near `x`: the
weighted localized Fourier transforms `η ↦ ⟨η⟩ ^ s (ℓ ∘ T) (φ e_η)` are all square integrable, so
that `φ T ∈ H^s` componentwise. -/
theorem notMem_vectorSobolevSingularSupport_iff {s : ℝ} {T : 𝓓'(Ω, F)} {x : E} (hx : x ∈ Ω) :
    x ∉ T.vectorSobolevSingularSupport s ↔
      ∃ φ : 𝓓(Ω, ℂ), φ x ≠ 0 ∧ ∀ ℓ : F →L[ℂ] ℂ,
        MemLp (fun η ↦ (1 + ‖η‖ ^ 2) ^ (s / 2) •
          (mapCLM (ℓ.restrictScalars ℝ) T).localFourier φ η) 2 volume := by
  refine ⟨fun h ↦ ?_, fun ⟨φ, hφ, hL⟩ ↦ ?_⟩
  · set b := Module.finBasis ℂ F
    -- Each frame component is `H^s` near `x`, with a neighbourhood serving every cutoff
    -- supported in it.
    have hb (i : Fin (finrank ℂ F)) :
        (mapCLM ((b.coord i).toContinuousLinearMap.restrictScalars ℝ) T).IsLocallySobolevAt s x :=
      (notMem_vectorSobolevSingularSupport_iff_forall_isLocallySobolevAt hx).1 h _
    choose U hU hL using fun i ↦ (hb i).exists_nhds
    obtain ⟨φ, hφ, hφx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
      (inter_mem (Filter.iInter_mem.2 hU) (Ω.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
    exact ⟨φ, by simp [hφx], memLp_weight_smul_localFourier_mapCLM_of_basis b fun i ↦
      hL i φ (hφ.trans (inter_subset_left.trans (iInter_subset U i)))⟩
  · exact (notMem_vectorSobolevSingularSupport_iff_forall_isLocallySobolevAt hx).2
      fun ℓ ↦ isLocallySobolevAt_iff.2 ⟨φ, hφ, hL ℓ⟩

/-- The `H^s` singular support is closed in `Ω`. -/
theorem isOpen_diff_vectorSobolevSingularSupport (s : ℝ) (T : 𝓓'(Ω, F)) :
    IsOpen ((Ω : Set E) \ T.vectorSobolevSingularSupport s) := by
  refine isOpen_iff_mem_nhds.2 fun x ⟨hx, hT⟩ ↦ ?_
  -- A common cutoff `φ` at `x` serves at every point of `{φ ≠ 0}`.
  obtain ⟨φ, hφ, hL⟩ := (notMem_vectorSobolevSingularSupport_iff hx).1 hT
  filter_upwards [(Ω.isOpen.inter (isOpen_ne_fun φ.continuous continuous_const)).mem_nhds
    ⟨hx, hφ⟩] with y hy
  exact ⟨hy.1, (notMem_vectorSobolevSingularSupport_iff hy.1).2 ⟨φ, hy.2, hL⟩⟩

/-- **Distributions have finite Sobolev order locally.** For every compact set `K ⊆ Ω` there is an
order `s` such that every component of `T` is `H^s` near every point of `K`. -/
theorem exists_disjoint_vectorSobolevSingularSupport (T : 𝓓'(Ω, F)) {K : Set E}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ s : ℝ, Disjoint K (T.vectorSobolevSingularSupport s) := by
  set b := Module.finBasis ℂ F
  choose r hr using fun i : Fin (finrank ℂ F) ↦ exists_forall_isLocallySobolevAt
    (mapCLM ((b.coord i).toContinuousLinearMap.restrictScalars ℝ) T) hK hKΩ
  -- The order `-∑ᵢ |rᵢ|` lies below the order of every frame component.
  refine ⟨-∑ i, |r i|, disjoint_left.2 fun x hx hxs ↦ ?_⟩
  rw [vectorSobolevSingularSupport_eq_iUnion_basis _ b, mem_iUnion] at hxs
  obtain ⟨i, hi⟩ := hxs
  refine (mem_sobolevSingularSupport_iff.1 hi).2 ((hr i x hx).mono ?_)
  calc -∑ j, |r j| ≤ -|r i| :=
        neg_le_neg (Finset.single_le_sum (fun j _ ↦ abs_nonneg (r j)) (Finset.mem_univ i))
    _ ≤ r i := neg_abs_le (r i)

end Frame

/-! ### Point masses -/

/-- **Point masses are `H^s` below the critical order.** In dimension `d`, the point mass
`δ_{x₀} v : φ ↦ φ x₀ • v` has empty `H^s` wave front set for `s < -d / 2`. -/
theorem vectorSobolevWaveFrontSet_mapCLM_toSpanSingleton_delta_eq_empty {s : ℝ}
    (hs : (finrank ℝ E : ℝ) < -2 * s) (x₀ : E) (v : F) :
    (mapCLM (ContinuousLinearMap.toSpanSingleton ℝ v)
      (delta x₀ : 𝓓'(Ω, ℝ))).vectorSobolevWaveFrontSet s = ∅ := by
  refine subset_empty_iff.1 (iUnion_subset fun ℓ ↦ ?_)
  rw [mapCLM_restrictScalars_mapCLM_toSpanSingleton_delta,
    ← sobolevWaveFrontSet_delta_eq_empty hs x₀]
  exact sobolevWaveFrontSet_smul_subset s _ _

/-- **Point masses are `H^s` below the critical order.** In dimension `d`, the point mass
`δ_{x₀} v : φ ↦ φ x₀ • v` has empty `H^s` singular support for `s < -d / 2`. -/
theorem vectorSobolevSingularSupport_mapCLM_toSpanSingleton_delta_eq_empty {s : ℝ}
    (hs : (finrank ℝ E : ℝ) < -2 * s) (x₀ : E) (v : F) :
    (mapCLM (ContinuousLinearMap.toSpanSingleton ℝ v)
      (delta x₀ : 𝓓'(Ω, ℝ))).vectorSobolevSingularSupport s = ∅ :=
  vectorSobolevSingularSupport_eq_empty_iff.2
    (vectorSobolevWaveFrontSet_mapCLM_toSpanSingleton_delta_eq_empty hs x₀ v)

/-- **The `H^s` wave front set of a point mass.** In dimension `d`, the point mass
`δ_{x₀} v : φ ↦ φ x₀ • v` at `x₀ ∈ Ω` with value `v ≠ 0` has `H^s` wave front set
`{x₀} × (E \ {0})` for `s ≥ -d / 2`. -/
theorem vectorSobolevWaveFrontSet_mapCLM_toSpanSingleton_delta {s : ℝ}
    (hs : -2 * s ≤ finrank ℝ E) {x₀ : E} (hx₀ : x₀ ∈ Ω) {v : F} (hv : v ≠ 0) :
    (mapCLM (ContinuousLinearMap.toSpanSingleton ℝ v)
      (delta x₀ : 𝓓'(Ω, ℝ))).vectorSobolevWaveFrontSet s = {x₀} ×ˢ {0}ᶜ := by
  -- Each component is the complex point mass at `x₀` times `ℓ v`, and some `ℓ v` is nonzero.
  refine (iUnion_subset fun ℓ ↦ ?_).antisymm ?_
  · rw [mapCLM_restrictScalars_mapCLM_toSpanSingleton_delta, ← sobolevWaveFrontSet_delta hs hx₀]
    exact sobolevWaveFrontSet_smul_subset s _ _
  · obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℂ v (norm_ne_zero_iff.2 hv)
    have hℓv : ℓ v ≠ 0 := by simp [hℓ, hv]
    have h := sobolevWaveFrontSet_mapCLM_subset_vectorSobolevWaveFrontSet s ℓ
      (mapCLM (ContinuousLinearMap.toSpanSingleton ℝ v) (delta x₀ : 𝓓'(Ω, ℝ)))
    rwa [mapCLM_restrictScalars_mapCLM_toSpanSingleton_delta, sobolevWaveFrontSet_smul s hℓv,
      sobolevWaveFrontSet_delta hs hx₀] at h

/-- **The `H^s` singular support of a point mass.** In dimension `d > 0`, the point mass
`δ_{x₀} v` at `x₀ ∈ Ω` with value `v ≠ 0` has `H^s` singular support `{x₀}` for `s ≥ -d / 2`. -/
theorem vectorSobolevSingularSupport_mapCLM_toSpanSingleton_delta [Nontrivial E] {s : ℝ}
    (hs : -2 * s ≤ finrank ℝ E) {x₀ : E} (hx₀ : x₀ ∈ Ω) {v : F} (hv : v ≠ 0) :
    (mapCLM (ContinuousLinearMap.toSpanSingleton ℝ v)
      (delta x₀ : 𝓓'(Ω, ℝ))).vectorSobolevSingularSupport s = {x₀} := by
  rw [← fst_image_vectorSobolevWaveFrontSet,
    vectorSobolevWaveFrontSet_mapCLM_toSpanSingleton_delta hs hx₀ hv]
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : E)
  exact fst_image_prod _ ⟨ξ, hξ⟩

end Distribution
