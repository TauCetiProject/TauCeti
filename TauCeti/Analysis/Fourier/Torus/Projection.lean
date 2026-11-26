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
are integrals of periodic functions over the unit cube. This representative map takes a point of
the torus, so it and its lemmas live in Mathlib's `UnitAddTorus` namespace, where dot notation
finds them.

## Main declarations

* `TauCeti.UnitAddTorus.proj`: the projection `ℝᵈ → 𝕋ᵈ`, as a continuous additive homomorphism.
* `TauCeti.UnitAddTorus.proj_eq_zero_iff`, `TauCeti.UnitAddTorus.proj_eq_proj_iff`: its kernel
  is the lattice `ℤᵈ`.
* `TauCeti.UnitAddTorus.mFourier_proj`: the Fourier modes read on `ℝᵈ` are plane waves.
* `UnitAddTorus.toEuclideanSpaceIoc`, `UnitAddTorus.proj_toEuclideanSpaceIoc`,
  `TauCeti.UnitAddTorus.proj_surjective`: the representative map `𝕋ᵈ → (0, 1]ᵈ`, a right inverse
  of the projection.
* `UnitAddTorus.measurableEmbedding_toEuclideanSpaceIoc`,
  `UnitAddTorus.measurePreserving_toEuclideanSpaceIoc`: the representative map is a measurable
  embedding carrying the measure of the torus onto the unit cube.
-/

public section

noncomputable section

open Complex MeasureTheory Set
open scoped Real RealInnerProductSpace FourierTransform

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

end TauCeti.UnitAddTorus
