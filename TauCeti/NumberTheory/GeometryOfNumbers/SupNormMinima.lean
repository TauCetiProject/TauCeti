/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GeometryOfNumbers.MinkowskiSecond
public import TauCeti.NumberTheory.Height.Arakelov.IntMatrix
-- Proof-only: Vaaler's lower bound for the volume of a central slice of the cube.
import TauCeti.MeasureTheory.Measure.Lebesgue.CubeSlice

/-!
# Successive minima in the sup norm are bounded by the covolume

Let `W` be a subspace of dimension `k` of the Euclidean space `ℝ^ι` and let `L` be a full lattice
in `W`. The central slice `W ∩ [-1, 1]^ι` of the cube is a symmetric convex body in `W` whose
gauge is the sup norm, and by Vaaler's cube-slicing theorem its volume is at least `2 ^ k`.
Minkowski's second theorem therefore bounds the product of the successive minima of `L` with
respect to the cube slice by the covolume of `L`, with no constant:

```text
λ₀ ⋯ λₖ₋₁ ≤ covolume L.
```

For the lattice `V ∩ ℤ^ι` of integral points of a subspace `V` of `ℚ^ι` the covolume is the
absolute Euclidean height of `V`. For the integral solutions of `A y = 0`, with `A` an integer
matrix, the covolume times the greatest common divisor `minorGcd A` of the maximal minors of `A` is
`√det (A Aᵀ)`; when the rows of `A` are linearly independent, `minorGcd A` is positive and the
covolume is the quotient `√det (A Aᵀ) / minorGcd A`.
These bounds are the geometric half of Bombieri and Vaaler's version of Siegel's lemma. Since the
gauge of the cube slice is the sup norm, they bound the sup norms of independent integral solutions
attaining the minima (`ZLattice.exists_linearIndependent_gauge_eq_successiveMin`), and of a lattice
basis built from the minima, which loses at most a factor `k! / 2 ^ (k - 1)` against them
(`ZLattice.exists_basis_mem_smul_successiveMin`).

The statements hold for every symmetric convex body containing the cube slice, since enlarging the
body only lowers the minima; the cube slice itself is the case of interest.

## Main results

* `ZLattice.prod_successiveMin_le_covolume_of_setOf_abs_le_one_subset`: the bound for a full
  lattice in a subspace of `ℝ^ι`.
* `Submodule.prod_successiveMin_intLattice_le_subspaceHeight`: for the integral points of a
  subspace `V` of `ℚ^ι`, the product of the minima is at most the height of `V`.
* `Matrix.minorGcd_mul_prod_successiveMin_le_sqrt_det`: for the integral solutions of `A y = 0`,
  the product of the minima times `minorGcd A` is at most `√det (A Aᵀ)`.

## References

* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32, §§2–3.
* J. D. Vaaler, *A geometric inequality with applications to linear forms*, Pacific J. Math. **83**
  (1979), 543–553.
* I. Aliev and M. Henk, *Minkowski's successive minima in convex and discrete geometry*,
  Commun. Math. **31** (2023), no. 2, 35–59, §6.
-/

public section

open MeasureTheory Module

namespace ZLattice

variable {ι : Type*} [Fintype ι] {W : Submodule ℝ (EuclideanSpace ℝ ι)}

/-- **The geometric half of Bombieri–Vaaler.** Let `L` be a full lattice in a subspace `W` of the
Euclidean space `ℝ^ι`, and let `K` be a symmetric convex body in `W` containing the central slice
`W ∩ [-1, 1]^ι` of the cube, for instance that slice itself. Then the successive minima of `L` with
respect to `K` satisfy `λ₀ ⋯ λₖ₋₁ ≤ covolume L`. -/
theorem prod_successiveMin_le_covolume_of_setOf_abs_le_one_subset (L : Submodule ℤ W)
    [DiscreteTopology L] [IsZLattice ℝ L] {K : ConvexBody W}
    (hK : {x : W | ∀ i, |(x : EuclideanSpace ℝ ι) i| ≤ 1} ⊆ K) (hKs : ∀ x ∈ K, -x ∈ K) :
    ∏ i, successiveMin L K i ≤ covolume L := by
  -- The open box `W ∩ (-1, 1)^ι` is a neighbourhood of `0` inside the cube slice.
  have hopen : IsOpen {x : W | ∀ i, |(x : EuclideanSpace ℝ ι) i| < 1} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_lt
      (continuous_abs.comp ((PiLp.continuous_apply 2 _ i).comp continuous_subtype_val))
      continuous_const
  have h0 : (0 : W) ∈ interior (K : Set W) :=
    mem_interior_iff_mem_nhds.2 <| Filter.mem_of_superset (hopen.mem_nhds (by simp))
      fun _ hx ↦ hK fun i ↦ (hx i).le
  exact prod_successiveMin_le_covolume_of_two_pow_finrank_le L volume h0 hKs
    ((W.two_pow_finrank_le_volume_setOf_forall_abs_le_one).trans (measure_mono hK))

end ZLattice

namespace Submodule

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **The minima of the integral points of a rational subspace in the sup norm.** For a subspace
`V` of `ℚ^ι`, the successive minima of the lattice `V ∩ ℤ^ι` in the real span of `V`, with respect
to a symmetric convex body containing the central slice of the cube `[-1, 1]^ι`, have product at
most the absolute Euclidean height of `V`. -/
theorem prod_successiveMin_intLattice_le_subspaceHeight (V : Submodule ℚ (ι → ℚ))
    {K : ConvexBody V.realSpan}
    (hK : {x : V.realSpan | ∀ i, |(x : EuclideanSpace ℝ ι) i| ≤ 1} ⊆ K)
    (hKs : ∀ x ∈ K, -x ∈ K) :
    ∏ i, ZLattice.successiveMin V.intLattice K i ≤ V.subspaceHeight :=
  V.covolume_intLattice ▸
    ZLattice.prod_successiveMin_le_covolume_of_setOf_abs_le_one_subset V.intLattice hK hKs

end Submodule

namespace Matrix

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {p : ℕ}

/-- **The minima of the integral solutions of `A y = 0` in the sup norm.** For an integer matrix
`A`, the successive minima of the lattice of integral solutions of `A y = 0`, with respect to a
symmetric convex body containing the central slice of the cube `[-1, 1]^ι`, satisfy
`minorGcd A · λ₀ ⋯ λₖ₋₁ ≤ √det (A Aᵀ)`. When the rows of `A` are linearly independent,
`minorGcd A` is positive and this bounds the product of the minima by `√det (A Aᵀ) / minorGcd A`;
otherwise both sides vanish. -/
theorem minorGcd_mul_prod_successiveMin_le_sqrt_det (A : Matrix (Fin p) ι ℤ)
    {K : ConvexBody (LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin).realSpan}
    (hK : {x : (LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin).realSpan |
      ∀ i, |(x : EuclideanSpace ℝ ι) i| ≤ 1} ⊆ K)
    (hKs : ∀ x ∈ K, -x ∈ K) :
    (A.minorGcd : ℝ) *
        ∏ i, ZLattice.successiveMin (LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin).intLattice K i ≤
      √((A * Aᵀ).det : ℝ) := by
  rw [← minorGcd_mul_subspaceHeight_ker_mulVecLin]
  gcongr
  · exact_mod_cast A.minorGcd_nonneg
  · exact Submodule.prod_successiveMin_intLattice_le_subspaceHeight _ hK hKs

end Matrix
