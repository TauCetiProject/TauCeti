/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Analysis.InnerProductSpace.Euclidean.IntegerPoints
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.Fourier.Torus.UnitCube
import TauCeti.MeasureTheory.Constructions.EuclideanSpace

/-!
# The projection from Euclidean space onto the torus

The projection `π : ℝᵈ → 𝕋ᵈ` (`TauCeti.UnitAddTorus.proj`) reduces each coordinate of a point of
`EuclideanSpace ℝ d` modulo one. It is the map `x ↦ fun i ↦ (x i : UnitAddCircle)` on `d → ℝ` of
`TauCeti.UnitAddTorus.isOpenQuotientMap_coe`, read on the Euclidean space, whose inner product
turns the Fourier modes of the torus into plane waves: `eₙ (π y) = 𝐞 ⟪y, n⟫` for the lattice point
`n ∈ ℤᵈ` (`TauCeti.UnitAddTorus.mFourier_proj`). This is how Fourier multipliers on `ℝᵈ` with
Schwartz kernels are transferred to the torus.

The projection is a continuous additive homomorphism whose kernel is the lattice `ℤᵈ`
(`TauCeti.UnitAddTorus.proj_eq_zero_iff`). It has the right inverse
`UnitAddTorus.toEuclideanSpaceIoc : 𝕋ᵈ → (0, 1]ᵈ ⊆ ℝᵈ`, choosing the representative of each point
in the fundamental domain `(0, 1]ᵈ`, which carries the measure of the torus onto the closed unit
cube `[0, 1]ᵈ` (`UnitAddTorus.measurePreserving_toEuclideanSpaceIoc`), so integrals over the torus
are integrals of periodic functions over the unit cube
(`TauCeti.UnitAddTorus.setLIntegral_cube_comp_proj_add`), or over any of its translates. This
representative map takes a point of the torus, so it and its lemmas live in Mathlib's
`UnitAddTorus` namespace, where dot notation finds them.

## Main declarations

* `TauCeti.UnitAddTorus.proj`: the projection `ℝᵈ → 𝕋ᵈ`, as a continuous additive homomorphism.
* `TauCeti.UnitAddTorus.proj_eq_zero_iff`, `TauCeti.UnitAddTorus.proj_eq_proj_iff`: its kernel
  is the lattice `ℤᵈ`.
* `TauCeti.UnitAddTorus.mFourier_proj`: the Fourier modes read on `ℝᵈ` are plane waves.
* `UnitAddTorus.toEuclideanSpaceIoc`, `UnitAddTorus.proj_toEuclideanSpaceIoc`,
  `UnitAddTorus.toEuclideanSpaceIoc_proj`, `TauCeti.UnitAddTorus.proj_surjective`: the
  representative map `𝕋ᵈ → (0, 1]ᵈ`, a right inverse of the projection and its inverse on
  `(0, 1]ᵈ`.
* `UnitAddTorus.measurableEmbedding_toEuclideanSpaceIoc`,
  `UnitAddTorus.measurePreserving_toEuclideanSpaceIoc`: the representative map is a measurable
  embedding carrying the measure of the torus onto the unit cube.
* `TauCeti.UnitAddTorus.setLIntegral_cube_comp_proj_add`,
  `TauCeti.UnitAddTorus.setLIntegral_box_comp_proj_le`: a periodic function integrates over every
  translate of the unit cube to its integral over the torus, and over the box `(-1, 2]ᵈ` to at
  most `3ᵈ` times it.
-/

public section

noncomputable section

open Complex MeasureTheory Set
open scoped ENNReal Real RealInnerProductSpace FourierTransform

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*}

/-! ### The projection -/

/-- The projection `π : ℝᵈ → 𝕋ᵈ`, reducing each coordinate modulo one. -/
def proj : EuclideanSpace ℝ d →ₜ+ UnitAddTorus d where
  toFun v i := (v i : UnitAddCircle)
  map_zero' := by
    ext i
    simp
  map_add' v w := by
    ext i
    simp
  continuous_toFun :=
    continuous_pi fun i ↦ (AddCircle.continuous_mk' 1).comp (PiLp.continuous_apply 2 _ i)

@[simp]
theorem proj_apply (v : EuclideanSpace ℝ d) (i : d) : proj v i = (v i : UnitAddCircle) :=
  (rfl)

/-- The kernel of the projection is the lattice `ℤᵈ`. -/
theorem proj_eq_zero_iff {v : EuclideanSpace ℝ d} :
    proj v = 0 ↔ ∃ n : d → ℤ, latticePoint n = v := by
  simp only [funext_iff, proj_apply, Pi.zero_apply, AddCircle.coe_eq_zero_iff, zsmul_eq_mul,
    mul_one, Classical.skolem]
  refine exists_congr fun n ↦ ⟨fun h ↦ ?_, fun h i ↦ ?_⟩
  · ext i
    rw [latticePoint_apply, h i]
  · rw [← h, latticePoint_apply]

@[simp]
theorem proj_latticePoint (n : d → ℤ) : proj (latticePoint n) = 0 :=
  proj_eq_zero_iff.2 ⟨n, rfl⟩

/-- Two points of `ℝᵈ` have the same projection exactly when they differ by a lattice point. -/
theorem proj_eq_proj_iff {v w : EuclideanSpace ℝ d} :
    proj v = proj w ↔ ∃ n : d → ℤ, latticePoint n = v - w := by
  rw [← sub_eq_zero, ← map_sub, proj_eq_zero_iff]

/-- The Fourier mode `eₙ`, read on `ℝᵈ`, is the plane wave `y ↦ 𝐞 ⟪y, n⟫`. -/
theorem mFourier_proj [Fintype d] (n : d → ℤ) (y : EuclideanSpace ℝ d) :
    mFourier n (proj y) = (𝐞 ⟪y, latticePoint n⟫ : ℂ) := by
  have hy : proj y = fun i ↦ (WithLp.ofLp y i : UnitAddCircle) := funext (proj_apply y)
  rw [hy, mFourier_coe_apply, Real.fourierChar_apply]
  congr 1
  simp only [PiLp.inner_apply, latticePoint_apply, RCLike.inner_apply, conj_trivial]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-! ### Representatives in the unit cube -/

/-- The representative map `𝕋ᵈ → (0, 1]ᵈ ⊆ ℝᵈ`, sending each point of the torus to its
representative in the fundamental domain `(0, 1]ᵈ`; a right inverse of the projection. -/
def _root_.UnitAddTorus.toEuclideanSpaceIoc (t : UnitAddTorus d) : EuclideanSpace ℝ d :=
  WithLp.toLp 2 ((measurableEquivPiIoc 0 t : _) : d → ℝ)

theorem _root_.UnitAddTorus.toEuclideanSpaceIoc_apply (t : UnitAddTorus d) (i : d) :
    toEuclideanSpaceIoc t i = ((measurableEquivPiIoc 0 t : _) : d → ℝ) i :=
  (rfl)

/-- The coordinates of the representative lie in `(0, 1]`. -/
theorem _root_.UnitAddTorus.toEuclideanSpaceIoc_apply_mem_Ioc (t : UnitAddTorus d) (i : d) :
    toEuclideanSpaceIoc t i ∈ Ioc (0 : ℝ) 1 := by
  have h := (measurableEquivPiIoc 0 t).property i
  simp only [Pi.zero_apply, zero_add] at h
  rwa [toEuclideanSpaceIoc_apply]

@[simp]
theorem _root_.UnitAddTorus.proj_toEuclideanSpaceIoc (t : UnitAddTorus d) :
    proj (toEuclideanSpaceIoc t) = t := by
  ext i
  simp [toEuclideanSpaceIoc_apply]

/-- A point of the fundamental domain `(0, 1]ᵈ` is the representative of its projection. -/
theorem _root_.UnitAddTorus.toEuclideanSpaceIoc_proj {v : EuclideanSpace ℝ d}
    (hv : ∀ i, v i ∈ Ioc (0 : ℝ) 1) : toEuclideanSpaceIoc (proj v) = v := by
  ext i
  simp only [toEuclideanSpaceIoc_apply, coe_measurableEquivPiIoc_apply, Pi.zero_apply, proj_apply]
  exact AddCircle.equivIoc_coe_of_mem (by simpa using hv i)

theorem proj_surjective : Function.Surjective (proj (d := d)) :=
  fun t ↦ ⟨toEuclideanSpaceIoc t, proj_toEuclideanSpaceIoc t⟩

theorem _root_.UnitAddTorus.measurableEmbedding_toEuclideanSpaceIoc [Countable d] :
    MeasurableEmbedding (toEuclideanSpaceIoc (d := d)) :=
  (MeasurableEquiv.toLp 2 (d → ℝ)).measurableEmbedding.comp
    measurableEmbedding_coe_measurableEquivPiIoc

-- The torus carries the product of the Haar probability measures on its circle factors, the
-- measure on which Mathlib's `mFourierBasis` is defined.
attribute [local instance 2000] instMeasureSpaceUnitAddCircle in
/-- The representative map carries the product of the Haar probability measures on the circle
factors of the torus onto Lebesgue measure on the closed unit cube `[0, 1]ᵈ`. -/
theorem _root_.UnitAddTorus.measurePreserving_toEuclideanSpaceIoc [Fintype d] :
    MeasurePreserving (toEuclideanSpaceIoc (d := d)) volume
      (volume.restrict {v : EuclideanSpace ℝ d | ∀ i, v i ∈ Icc (0 : ℝ) 1}) := by
  have h := (PiLp.volume_preserving_toLp d).restrict_preimage
    (EuclideanSpace.measurableSet_setOf_forall_mem fun _ ↦
      measurableSet_Icc (a := (0 : ℝ)) (b := 1))
  have hpre : (WithLp.toLp 2 : (d → ℝ) → EuclideanSpace ℝ d) ⁻¹'
      {v : EuclideanSpace ℝ d | ∀ i, v i ∈ Icc (0 : ℝ) 1} = univ.pi fun _ ↦ Icc (0 : ℝ) 1 := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, mem_univ_pi]
  rw [hpre] at h
  exact h.comp measurePreserving_coe_measurableEquivPiIoc

/-! ### Integrals of periodic functions over the unit cube -/

section Integral

-- The torus carries the product of the Haar probability measures on its circle factors, the
-- measure on which Mathlib's `mFourierBasis` is defined; Mathlib records with a file-local
-- instance that it is a Haar measure.
attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance projectionIsAddHaarMeasureVolume :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The box `(-1, 2]ᵈ` is covered by the `3ᵈ` translates of the unit cube by the integer vectors
with coordinates in `{-1, 0, 1}`. -/
private theorem exists_sub_latticePoint_mem_cube {y : EuclideanSpace ℝ d}
    (hy : ∀ i, y i ∈ Ioc (-1 : ℝ) 2) :
    ∃ ℓ : d → ℤ, (∀ i, ℓ i ∈ ({-1, 0, 1} : Finset ℤ)) ∧ ∀ i, (y - latticePoint ℓ) i ∈ Icc 0 1 := by
  refine ⟨fun i ↦ ⌈y i⌉ - 1, fun i ↦ ?_, fun i ↦ ?_⟩
  · have hc₁ : 0 ≤ ⌈y i⌉ := Int.ceil_nonneg_of_neg_one_lt (hy i).1
    have hc₂ : ⌈y i⌉ ≤ 2 := Int.ceil_le.2 (by exact_mod_cast (hy i).2)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · simp only [PiLp.sub_apply, latticePoint_apply, Int.cast_sub, Int.cast_one, mem_Icc]
    constructor
    · linarith [Int.ceil_lt_add_one (y i)]
    · linarith [Int.le_ceil (y i)]

variable [Fintype d]

/-- A periodic function integrates over every translate of the closed unit cube `[0, 1]ᵈ` to its
integral over the torus. -/
theorem setLIntegral_cube_comp_proj_add (H : UnitAddTorus d → ℝ≥0∞) (z : EuclideanSpace ℝ d) :
    ∫⁻ w in {v : EuclideanSpace ℝ d | ∀ i, v i ∈ Icc (0 : ℝ) 1}, H (proj (w + z)) =
      ∫⁻ t, H t := by
  rw [← measurePreserving_toEuclideanSpaceIoc.lintegral_comp_emb
    measurableEmbedding_toEuclideanSpaceIoc]
  simp_rw [map_add, proj_toEuclideanSpaceIoc]
  exact lintegral_add_right_eq_self H (proj z)

/-- A periodic function integrates over the box `(-1, 2]ᵈ` to at most `3ᵈ` times its integral
over the torus. -/
theorem setLIntegral_box_comp_proj_le (H : UnitAddTorus d → ℝ≥0∞) :
    ∫⁻ y in {v : EuclideanSpace ℝ d | ∀ i, v i ∈ Ioc (-1 : ℝ) 2}, H (proj y) ≤
      3 ^ Fintype.card d * ∫⁻ t, H t := by
  classical
  set cube := {v : EuclideanSpace ℝ d | ∀ i, v i ∈ Icc (0 : ℝ) 1}
  set S := Fintype.piFinset fun _ : d ↦ ({-1, 0, 1} : Finset ℤ)
  have hcover : {v : EuclideanSpace ℝ d | ∀ i, v i ∈ Ioc (-1 : ℝ) 2} ⊆
      ⋃ ℓ : S, (fun y ↦ y - latticePoint (ℓ : d → ℤ)) ⁻¹' cube := fun y hy ↦ by
    obtain ⟨ℓ, hℓ, h⟩ := exists_sub_latticePoint_mem_cube hy
    exact mem_iUnion.2 ⟨⟨ℓ, Fintype.mem_piFinset.2 hℓ⟩, h⟩
  have htrans (ℓ : d → ℤ) : ∫⁻ y in (fun y ↦ y - latticePoint ℓ) ⁻¹' cube, H (proj y) =
      ∫⁻ t, H t := by
    have h := (measurePreserving_sub_right volume (latticePoint ℓ)).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.subRight (latticePoint ℓ)).measurableEmbedding
      (fun w ↦ H (proj (w + latticePoint ℓ))) cube
    simp only [sub_add_cancel] at h
    rw [h, setLIntegral_cube_comp_proj_add]
  have hcard : (S.card : ℝ≥0∞) = 3 ^ Fintype.card d := by
    simp [S, Fintype.card_piFinset, Finset.prod_const]
  calc ∫⁻ y in {v : EuclideanSpace ℝ d | ∀ i, v i ∈ Ioc (-1 : ℝ) 2}, H (proj y)
      ≤ ∫⁻ y in ⋃ ℓ : S, (fun y ↦ y - latticePoint (ℓ : d → ℤ)) ⁻¹' cube, H (proj y) :=
        lintegral_mono_set hcover
    _ ≤ ∑' ℓ : S, ∫⁻ y in (fun y ↦ y - latticePoint (ℓ : d → ℤ)) ⁻¹' cube, H (proj y) :=
        lintegral_iUnion_le _ _
    _ = ∑ ℓ ∈ S, ∫⁻ t, H t := by
        rw [Finset.tsum_subtype S fun ℓ ↦
          ∫⁻ y in (fun y ↦ y - latticePoint ℓ) ⁻¹' cube, H (proj y)]
        exact Finset.sum_congr rfl fun ℓ _ ↦ htrans ℓ
    _ = 3 ^ Fintype.card d * ∫⁻ t, H t := by rw [Finset.sum_const, nsmul_eq_mul, hcard]

end Integral

end TauCeti.UnitAddTorus
