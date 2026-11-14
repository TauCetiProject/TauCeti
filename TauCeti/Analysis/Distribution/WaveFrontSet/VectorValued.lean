/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.Distribution.Support
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity

/-!
# The wave front set of a vector-valued distribution

Let `F` be a complex normed space and `T : 𝓓'(Ω, F)` a distribution with values in `F`. Each
complex-linear functional `ℓ : F →L[ℂ] ℂ` gives a complex component `ℓ ∘ T : 𝓓'(Ω, ℂ)`, and the
**wave front set** of `T` (`Distribution.vectorWaveFrontSet`) is the union of the wave front sets
of these components. When `F` is finite dimensional and `(bᵢ)` is a basis of `F` (a frame), every
component is a linear combination of the frame components `bᵢ* ∘ T`, so the wave front set of `T`
is the union of the wave front sets of the frame components, for any frame
(`Distribution.vectorWaveFrontSet_eq_iUnion_basis`). This is the definition used for distributions
with values in a vector bundle, where `T` is localized in a chart and trivialized by a frame; the
results here show that it does not depend on the frame.

Moreover, for finite-dimensional `F`, a single cutoff and a single cone witness microlocal
smoothness of all components at once (`Distribution.notMem_vectorWaveFrontSet_iff`): `(x, ξ)` lies
outside the wave front set of `T` exactly when some test function `φ` with `φ x ≠ 0` has localized
Fourier transforms `η ↦ (ℓ ∘ T) (φ e_η)` rapidly decreasing in one open cone around `ξ` for every
`ℓ`.

A change of frame by a smooth function `G : E → (F →L[ℂ] F')` multiplies `T` by `G`. Writing `G`
in a real basis `(Aᵢ)` of the finite-dimensional space `F →L[ℂ] F'` as `G = ∑ gᵢ Aᵢ` with smooth
real coefficients `gᵢ`, the product `G T` is the distribution `∑ Aᵢ (gᵢ T)`. The wave front set of
such a sum is contained in that of `T`
(`Distribution.vectorWaveFrontSet_sum_mapCLM_smulLeftCLM_subset`).

## Main declarations

* `Distribution.vectorWaveFrontSet T`: the wave front set of an `F`-valued distribution.
* `Distribution.vectorWaveFrontSet_eq_waveFrontSet`: for `F = ℂ` it is the wave front set of `T`.
* `Distribution.vectorWaveFrontSet_eq_iUnion_basis`: it is the union of the wave front sets of the
  frame components, for every basis of a finite-dimensional `F`.
* `Distribution.notMem_vectorWaveFrontSet_iff`: for finite-dimensional `F`, one cutoff and one
  cone serve all components.
* `Distribution.isOpen_diff_vectorWaveFrontSet`, `Distribution.smul_mem_vectorWaveFrontSet_iff`:
  it is closed in `Ω × (E \ {0})` for finite-dimensional `F`, and conic.
* `Distribution.vectorWaveFrontSet_mapCLM_subset`, `Distribution.vectorWaveFrontSet_mapCLM_equiv`:
  a complex-linear map of the values does not enlarge it, and an isomorphism preserves it.
* `Distribution.vectorWaveFrontSet_sum_mapCLM_smulLeftCLM_subset`: a sum `∑ᵢ Aᵢ (gᵢ T)` of
  complex-linear maps `Aᵢ` applied to smooth multiples `gᵢ T` has wave front set contained in
  that of `T`.
* `Distribution.vectorWaveFrontSet_add_subset`,
  `Distribution.vectorWaveFrontSet_smulLeftCLM_subset`,
  `Distribution.vectorWaveFrontSet_restrictCLM`,
  `Distribution.vectorWaveFrontSet_compCLMOfContinuousLinearEquiv`: sums, smooth multiples,
  restriction to open subsets and linear changes of coordinates.
* `Distribution.vectorWaveFrontSet_mapCLM_toSpanSingleton_delta`: the point mass `δ_{x₀} v` with
  `v ≠ 0` has wave front set `{x₀} × (E \ {0})`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.1 (the wave front set of a vector-valued distribution as the union over its
  components).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, Lecture I, §7.
-/

public section

noncomputable section

open Complex Filter Set TopologicalSpace TestFunction
open scoped Distributions Topology ContDiff InnerProduct

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Opens E}
  {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup F'] [NormedSpace ℂ F']

/-- The **wave front set** of a distribution `T` with values in a complex normed space `F`: the
union of the wave front sets of its complex components `ℓ ∘ T`, for `ℓ : F →L[ℂ] ℂ`. -/
def vectorWaveFrontSet (T : 𝓓'(Ω, F)) : Set (E × E) :=
  ⋃ ℓ : F →L[ℂ] ℂ, (mapCLM (ℓ.restrictScalars ℝ) T).waveFrontSet

theorem mem_vectorWaveFrontSet_iff {T : 𝓓'(Ω, F)} {p : E × E} :
    p ∈ T.vectorWaveFrontSet ↔
      ∃ ℓ : F →L[ℂ] ℂ, p ∈ (mapCLM (ℓ.restrictScalars ℝ) T).waveFrontSet :=
  mem_iUnion

/-- The wave front set of each component lies in the wave front set. -/
theorem waveFrontSet_mapCLM_subset_vectorWaveFrontSet (ℓ : F →L[ℂ] ℂ) (T : 𝓓'(Ω, F)) :
    (mapCLM (ℓ.restrictScalars ℝ) T).waveFrontSet ⊆ T.vectorWaveFrontSet :=
  subset_iUnion (fun ℓ : F →L[ℂ] ℂ ↦ (mapCLM (ℓ.restrictScalars ℝ) T).waveFrontSet) ℓ

/-- The wave front set lies in `Ω × (E \ {0})`. -/
theorem vectorWaveFrontSet_subset (T : 𝓓'(Ω, F)) :
    T.vectorWaveFrontSet ⊆ (Ω : Set E) ×ˢ {0}ᶜ :=
  iUnion_subset fun _ ↦ waveFrontSet_subset _

/-- The wave front set is conic in the frequency variable. -/
theorem smul_mem_vectorWaveFrontSet_iff {T : 𝓓'(Ω, F)} {x ξ : E} {t : ℝ} (ht : 0 < t) :
    (x, t • ξ) ∈ T.vectorWaveFrontSet ↔ (x, ξ) ∈ T.vectorWaveFrontSet := by
  simp only [mem_vectorWaveFrontSet_iff, smul_mem_waveFrontSet_iff ht]

/-! ### Scalar distributions -/

/-- For a complex distribution the wave front set of `T` as a vector-valued distribution is its
wave front set: every component is a scalar multiple of `T`. -/
@[simp]
theorem vectorWaveFrontSet_eq_waveFrontSet (T : 𝓓'(Ω, ℂ)) :
    T.vectorWaveFrontSet = T.waveFrontSet := by
  refine (iUnion_subset fun ℓ ↦ ?_).antisymm ?_
  · have h : mapCLM (ℓ.restrictScalars ℝ) T = ℓ 1 • T := by
      ext φ
      simpa [mul_comm] using ℓ.map_smul (T φ) (1 : ℂ)
    rw [h]
    exact waveFrontSet_smul_subset _ T
  · have h : mapCLM ((ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ) T = T := by
      ext φ
      simp
    exact h ▸ waveFrontSet_mapCLM_subset_vectorWaveFrontSet (.id ℂ ℂ) T

/-! ### Linear maps of the values -/

/-- A complex-linear map of the values does not enlarge the wave front set. -/
theorem vectorWaveFrontSet_mapCLM_subset (A : F →L[ℂ] F') (T : 𝓓'(Ω, F)) :
    (mapCLM (A.restrictScalars ℝ) T).vectorWaveFrontSet ⊆ T.vectorWaveFrontSet :=
  iUnion_subset fun ℓ ↦ waveFrontSet_mapCLM_subset_vectorWaveFrontSet (ℓ.comp A) T

/-- An isomorphism of the values preserves the wave front set. -/
@[simp]
theorem vectorWaveFrontSet_mapCLM_equiv (A : F ≃L[ℂ] F') (T : 𝓓'(Ω, F)) :
    (mapCLM ((A : F →L[ℂ] F').restrictScalars ℝ) T).vectorWaveFrontSet =
      T.vectorWaveFrontSet := by
  refine (vectorWaveFrontSet_mapCLM_subset _ T).antisymm ?_
  have h : mapCLM ((A.symm : F' →L[ℂ] F).restrictScalars ℝ)
      (mapCLM ((A : F →L[ℂ] F').restrictScalars ℝ) T) = T := by
    ext φ
    simp
  conv_lhs => rw [← h]
  exact vectorWaveFrontSet_mapCLM_subset _ _

/-! ### Scalar multiples -/

/-- A scalar multiple of `T` has wave front set contained in that of `T`. -/
theorem vectorWaveFrontSet_smul_subset (c : ℂ) (T : 𝓓'(Ω, F)) :
    (c • T).vectorWaveFrontSet ⊆ T.vectorWaveFrontSet :=
  iUnion_subset fun ℓ ↦ by
    have h : mapCLM (ℓ.restrictScalars ℝ) (c • T) = c • mapCLM (ℓ.restrictScalars ℝ) T := by
      ext φ
      simp
    rw [h]
    exact (waveFrontSet_smul_subset c _).trans (waveFrontSet_mapCLM_subset_vectorWaveFrontSet ℓ T)

/-- A nonzero scalar multiple of `T` has the same wave front set as `T`. -/
@[simp]
theorem vectorWaveFrontSet_smul {c : ℂ} (hc : c ≠ 0) (T : 𝓓'(Ω, F)) :
    (c • T).vectorWaveFrontSet = T.vectorWaveFrontSet := by
  refine (vectorWaveFrontSet_smul_subset c T).antisymm ?_
  simpa [smul_smul, inv_mul_cancel₀ hc] using vectorWaveFrontSet_smul_subset c⁻¹ (c • T)

/-- The negative of `T` has the same wave front set as `T`. -/
@[simp]
theorem vectorWaveFrontSet_neg (T : 𝓓'(Ω, F)) :
    (-T).vectorWaveFrontSet = T.vectorWaveFrontSet := by
  rw [← neg_one_smul ℂ T, vectorWaveFrontSet_smul (neg_ne_zero.2 one_ne_zero)]

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The wave front set lies over the support of `T`. -/
theorem vectorWaveFrontSet_subset_dsupport (T : 𝓓'(Ω, F)) :
    T.vectorWaveFrontSet ⊆ dsupport T ×ˢ univ :=
  iUnion_subset fun ℓ ↦ (waveFrontSet_subset_dsupport _).trans <|
    prod_mono (dsupport_comp_subset (g := ℓ.restrictScalars ℝ) T (map_zero _)) subset_rfl

/-- The zero distribution has empty wave front set. -/
@[simp]
theorem vectorWaveFrontSet_zero : (0 : 𝓓'(Ω, F)).vectorWaveFrontSet = ∅ := by
  simp [vectorWaveFrontSet]

/-! ### Sums -/

/-- The wave front set of a sum lies in the union of the wave front sets. -/
theorem vectorWaveFrontSet_add_subset (S T : 𝓓'(Ω, F)) :
    (S + T).vectorWaveFrontSet ⊆ S.vectorWaveFrontSet ∪ T.vectorWaveFrontSet :=
  iUnion_subset fun ℓ ↦ by
    rw [map_add]
    exact (waveFrontSet_add_subset _ _).trans <| union_subset_union
      (waveFrontSet_mapCLM_subset_vectorWaveFrontSet ℓ S)
      (waveFrontSet_mapCLM_subset_vectorWaveFrontSet ℓ T)

/-- The wave front set of a finite sum lies in the union of the wave front sets. -/
theorem vectorWaveFrontSet_sum_subset {ι : Type*} (s : Finset ι) (T : ι → 𝓓'(Ω, F)) :
    (∑ i ∈ s, T i).vectorWaveFrontSet ⊆ ⋃ i ∈ s, (T i).vectorWaveFrontSet :=
  iUnion_subset fun ℓ ↦ by
    rw [map_sum]
    exact (waveFrontSet_sum_subset _ _).trans <| iUnion₂_mono fun i _ ↦
      waveFrontSet_mapCLM_subset_vectorWaveFrontSet ℓ (T i)

/-- The wave front set of a difference lies in the union of the wave front sets. -/
theorem vectorWaveFrontSet_sub_subset (S T : 𝓓'(Ω, F)) :
    (S - T).vectorWaveFrontSet ⊆ S.vectorWaveFrontSet ∪ T.vectorWaveFrontSet := by
  simpa [sub_eq_add_neg] using vectorWaveFrontSet_add_subset S (-T)

/-! ### Smooth multiples, restriction and linear changes of coordinates -/

section SmulLeft

variable {g : E → ℝ}

/-- The wave front set of a smooth multiple `g T` lies in that of `T` over `tsupport g`. -/
theorem vectorWaveFrontSet_smulLeftCLM_subset (T : 𝓓'(Ω, F)) (hg : ContDiff ℝ ∞ g) :
    (smulLeftCLM hg T).vectorWaveFrontSet ⊆ T.vectorWaveFrontSet ∩ tsupport g ×ˢ univ :=
  iUnion_subset fun ℓ ↦ by
    rw [mapCLM_smulLeftCLM]
    exact (waveFrontSet_smulLeftCLM_subset _ hg).trans <|
      inter_subset_inter_left _ (waveFrontSet_mapCLM_subset_vectorWaveFrontSet ℓ T)

/-- At a point where `g ≠ 0`, the smooth multiple `g T` has the same wave front set as `T`. -/
theorem mem_vectorWaveFrontSet_smulLeftCLM_iff {T : 𝓓'(Ω, F)} {x ξ : E} (hg : ContDiff ℝ ∞ g)
    (hx : g x ≠ 0) :
    (x, ξ) ∈ (smulLeftCLM hg T).vectorWaveFrontSet ↔ (x, ξ) ∈ T.vectorWaveFrontSet := by
  simp only [mem_vectorWaveFrontSet_iff, mapCLM_smulLeftCLM, mem_waveFrontSet_smulLeftCLM_iff hg hx]

/-- Multiplying by a smooth function that vanishes nowhere on `Ω` does not change the wave front
set. -/
theorem vectorWaveFrontSet_smulLeftCLM_of_ne_zero (T : 𝓓'(Ω, F)) (hg : ContDiff ℝ ∞ g)
    (hg0 : ∀ x ∈ Ω, g x ≠ 0) : (smulLeftCLM hg T).vectorWaveFrontSet = T.vectorWaveFrontSet := by
  simp only [vectorWaveFrontSet, mapCLM_smulLeftCLM, waveFrontSet_smulLeftCLM_of_ne_zero _ hg hg0]

/-- **Smooth changes of frame.** For smooth real functions `gᵢ` and complex-linear maps
`Aᵢ : F →L[ℂ] F'`, the distribution `∑ᵢ Aᵢ (gᵢ T)` has wave front set contained in that of `T`.
This sum is the product of `T` with the smooth function `G = ∑ᵢ gᵢ Aᵢ : E → (F →L[ℂ] F')`. -/
theorem vectorWaveFrontSet_sum_mapCLM_smulLeftCLM_subset {ι : Type*} (s : Finset ι)
    (A : ι → F →L[ℂ] F') {g : ι → E → ℝ} (hg : ∀ i, ContDiff ℝ ∞ (g i)) (T : 𝓓'(Ω, F)) :
    (∑ i ∈ s, mapCLM ((A i).restrictScalars ℝ) (smulLeftCLM (hg i) T)).vectorWaveFrontSet ⊆
      T.vectorWaveFrontSet :=
  (vectorWaveFrontSet_sum_subset _ _).trans <| iUnion₂_subset fun i _ ↦
    (vectorWaveFrontSet_mapCLM_subset _ _).trans <|
      (vectorWaveFrontSet_smulLeftCLM_subset T (hg i)).trans inter_subset_left

end SmulLeft

section Restriction

variable {Ω' : Opens E}

/-- For an open subset `Ω' ≤ Ω`, the wave front set of the restriction `T|_{Ω'}` is the part of
the wave front set of `T` lying over `Ω'`. -/
theorem vectorWaveFrontSet_restrictCLM (h : Ω' ≤ Ω) (T : 𝓓'(Ω, F)) :
    (restrictCLM T : 𝓓'(Ω', F)).vectorWaveFrontSet =
      T.vectorWaveFrontSet ∩ (Ω' : Set E) ×ˢ univ := by
  have hc (ℓ : F →L[ℂ] ℂ) : mapCLM (ℓ.restrictScalars ℝ) (restrictCLM T : 𝓓'(Ω', F)) =
      restrictCLM (mapCLM (ℓ.restrictScalars ℝ) T) := by
    ext φ
    simp
  simp only [vectorWaveFrontSet, hc, waveFrontSet_restrictCLM h, iUnion_inter]

end Restriction

section LinearEquiv

variable {V : Opens E}

/-- **Linear changes of coordinates.** If a linear automorphism `e` of `E` identifies `V` with
`Ω`, then `(x, ξ)` lies in the wave front set of the pullback `e^* T` exactly when
`(e x, (e⁻¹)ᵀ ξ)` lies in that of `T`. -/
theorem vectorWaveFrontSet_compCLMOfContinuousLinearEquiv (e : E ≃L[ℝ] E) (hVO : MapsTo e V Ω)
    (hOV : MapsTo e.symm Ω V) (T : 𝓓'(Ω, F)) :
    (compCLMOfContinuousLinearEquiv e hVO T).vectorWaveFrontSet =
      Prod.map e ((e.symm : E →L[ℝ] E)†) ⁻¹' T.vectorWaveFrontSet := by
  have hc (ℓ : F →L[ℂ] ℂ) : mapCLM (ℓ.restrictScalars ℝ) (compCLMOfContinuousLinearEquiv e hVO T) =
      compCLMOfContinuousLinearEquiv e hVO (mapCLM (ℓ.restrictScalars ℝ) T) := by
    ext φ
    simp
  simp only [vectorWaveFrontSet, hc, waveFrontSet_compCLMOfContinuousLinearEquiv e hVO hOV,
    preimage_iUnion]

end LinearEquiv

/-! ### Frames -/

section Frame

variable [FiniteDimensional ℂ F] {ι : Type*}

omit [FiniteDimensional ℝ E] in
/-- Every component of `T` is a linear combination of its frame components: in a basis `b`,
`ℓ ∘ T = ∑ᵢ ℓ (bᵢ) • (bᵢ* ∘ T)`. -/
theorem mapCLM_eq_sum_basis [Fintype ι] (b : Module.Basis ι ℂ F) (ℓ : F →L[ℂ] ℂ)
    (T : 𝓓'(Ω, F)) :
    mapCLM (ℓ.restrictScalars ℝ) T =
      ∑ i, ℓ (b i) • mapCLM ((b.coord i).toContinuousLinearMap.restrictScalars ℝ) T := by
  ext φ
  calc ℓ (T φ) = ℓ (∑ i, b.repr (T φ) i • b i) := by rw [b.sum_repr]
    _ = _ := by
      rw [map_sum]
      simp [mul_comm]

/-- **Independence of the frame.** For every basis `b` of `F`, the wave front set of `T` is the
union of the wave front sets of the frame components `bᵢ* ∘ T`. -/
theorem vectorWaveFrontSet_eq_iUnion_basis (b : Module.Basis ι ℂ F) (T : 𝓓'(Ω, F)) :
    T.vectorWaveFrontSet =
      ⋃ i, (mapCLM ((b.coord i).toContinuousLinearMap.restrictScalars ℝ) T).waveFrontSet := by
  have := FiniteDimensional.fintypeBasisIndex b
  refine (iUnion_subset fun ℓ ↦ ?_).antisymm
    (iUnion_subset fun i ↦ waveFrontSet_mapCLM_subset_vectorWaveFrontSet _ T)
  rw [mapCLM_eq_sum_basis b]
  exact (waveFrontSet_sum_subset _ _).trans <| iUnion₂_subset fun i _ ↦
    (waveFrontSet_smul_subset _ _).trans (subset_iUnion_of_subset i subset_rfl)

/-- **A common cutoff.** A point `(x, ξ)` with `x ∈ Ω` and `ξ ≠ 0` lies outside the wave front set
of `T` exactly when one test function `φ` with `φ x ≠ 0` and one open cone `Γ` containing `ξ`
witness the microlocal smoothness of every component: the localized Fourier transforms
`η ↦ (ℓ ∘ T) (φ e_η)` all decay rapidly on `Γ`. -/
theorem notMem_vectorWaveFrontSet_iff {T : 𝓓'(Ω, F)} {x ξ : E} (hx : x ∈ Ω) (hξ : ξ ≠ 0) :
    (x, ξ) ∉ T.vectorWaveFrontSet ↔
      ∃ φ : 𝓓(Ω, ℂ), φ x ≠ 0 ∧ ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧
        (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧ ∀ ℓ : F →L[ℂ] ℂ, ∀ N : ℕ, ∃ C, ∀ η ∈ Γ,
          (1 + ‖η‖) ^ N * ‖(mapCLM (ℓ.restrictScalars ℝ) T).localFourier φ η‖ ≤ C := by
  refine ⟨fun h ↦ ?_, fun ⟨φ, hφ, Γ, hΓ, hξΓ, hcone, hdecay⟩ ↦ ?_⟩
  · set b := Module.finBasis ℂ F
    -- Each frame component is microlocally smooth at `(x, ξ)`, with a neighbourhood and a cone
    -- serving every cutoff supported in it.
    have hb (i : Fin (Module.finrank ℂ F)) :
        (mapCLM ((b.coord i).toContinuousLinearMap.restrictScalars ℝ) T).IsMicrolocallySmoothAt
          x ξ := by
      by_contra hi
      exact h (waveFrontSet_mapCLM_subset_vectorWaveFrontSet _ T
        (mem_waveFrontSet_iff.2 ⟨hx, hξ, hi⟩))
    choose U hU Γ hΓ hξΓ hcone hdecay using fun i ↦ (hb i).exists_nhds_cone
    obtain ⟨φ, hφ, hφx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
      (inter_mem (Filter.iInter_mem.2 hU) (Ω.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
    refine ⟨φ, by simp [hφx], ⋂ i, Γ i, isOpen_iInter_of_finite hΓ, mem_iInter.2 hξΓ,
      fun t ht η hη ↦ mem_iInter.2 fun i ↦ hcone i t ht η (mem_iInter.1 hη i), fun ℓ N ↦ ?_⟩
    -- Expand the component along `ℓ` in the frame components and add up their bounds.
    choose C hC using fun i ↦ hdecay i φ
      (hφ.trans (inter_subset_left.trans (iInter_subset U i))) N
    refine ⟨∑ i, ‖ℓ (b i)‖ * C i, fun η hη ↦ ?_⟩
    rw [mapCLM_eq_sum_basis b, localFourier_sum]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [localFourier_smul, norm_mul, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hC i η (mem_iInter.1 hη i)) (norm_nonneg _)
  · rw [mem_vectorWaveFrontSet_iff, not_exists]
    exact fun ℓ hℓ ↦ (mem_waveFrontSet_iff.1 hℓ).2.2
      (isMicrolocallySmoothAt_iff.2 ⟨φ, hφ, Γ, hΓ, hξΓ, hcone, hdecay ℓ⟩)

/-- The wave front set is closed in `Ω × (E \ {0})`. -/
theorem isOpen_diff_vectorWaveFrontSet (T : 𝓓'(Ω, F)) :
    IsOpen (((Ω : Set E) ×ˢ {0}ᶜ) \ T.vectorWaveFrontSet) := by
  refine isOpen_iff_mem_nhds.2 fun ⟨x, ξ⟩ ⟨⟨hx, hξ⟩, hp⟩ ↦ ?_
  -- A common cutoff `φ` and cone `Γ` at `(x, ξ)` serve at every point of `{φ ≠ 0} × Γ`.
  obtain ⟨φ, hφ, Γ, hΓ, hξΓ, hcone, hdecay⟩ := (notMem_vectorWaveFrontSet_iff hx hξ).1 hp
  have hU : IsOpen {y : E | φ y ≠ 0} := isOpen_ne_fun φ.continuous continuous_const
  filter_upwards [((Ω.isOpen.inter hU).prod (hΓ.inter isOpen_compl_singleton)).mem_nhds
    ⟨⟨hx, hφ⟩, hξΓ, hξ⟩] with q hq
  exact ⟨⟨hq.1.1, hq.2.2⟩, (notMem_vectorWaveFrontSet_iff hq.1.1 hq.2.2).2
    ⟨φ, hq.1.2, Γ, hΓ, hq.2.1, hcone, hdecay⟩⟩

end Frame

/-! ### Point masses -/

/-- The point mass `δ_{x₀} v : φ ↦ φ x₀ • v` at `x₀ ∈ Ω` with value `v ≠ 0` has wave front set
`{x₀} × (E \ {0})`. -/
theorem vectorWaveFrontSet_mapCLM_toSpanSingleton_delta {x₀ : E} (hx₀ : x₀ ∈ Ω) {v : F}
    (hv : v ≠ 0) :
    (mapCLM (ContinuousLinearMap.toSpanSingleton ℝ v) (delta x₀ : 𝓓'(Ω, ℝ))).vectorWaveFrontSet =
      {x₀} ×ˢ {0}ᶜ := by
  -- Each component is the complex point mass at `x₀` times `ℓ v`, and some `ℓ v` is nonzero.
  have hc (ℓ : F →L[ℂ] ℂ) : mapCLM (ℓ.restrictScalars ℝ)
      (mapCLM (ContinuousLinearMap.toSpanSingleton ℝ v) (delta x₀ : 𝓓'(Ω, ℝ))) =
      ℓ v • mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ)) := by
    ext φ
    simp [mul_comm]
  refine (iUnion_subset fun ℓ ↦ ?_).antisymm ?_
  · rw [hc, ← waveFrontSet_delta hx₀]
    exact waveFrontSet_smul_subset _ _
  · obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℂ v (norm_ne_zero_iff.2 hv)
    have hℓv : ℓ v ≠ 0 := by simp [hℓ, hv]
    have h := waveFrontSet_mapCLM_subset_vectorWaveFrontSet ℓ
      (mapCLM (ContinuousLinearMap.toSpanSingleton ℝ v) (delta x₀ : 𝓓'(Ω, ℝ)))
    rwa [hc, waveFrontSet_smul hℓv, waveFrontSet_delta hx₀] at h

end FiniteDimensional

end Distribution
