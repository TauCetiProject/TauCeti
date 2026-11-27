/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.RingTheory.AlgebraTower

/-!
# Dimensions of Euclidean spaces

The first lemma derives positive ambient dimension from two distinct points, in particular from
a nonzero vector. Distinct points thus supply the dimension hypothesis needed for Newtonian-kernel
monotonicity and Poisson-kernel positivity.

The lemma `TauCeti.finrank_real_euclideanSpace_complex` and the instance
`TauCeti.factFinrankEuclideanSpaceComplex` record the real dimension of `ℂᵏ⁺¹` as `(2k + 1) + 1`.
This is the form of the hypothesis `Fact (finrank ℝ E = n + 1)` under which
Mathlib puts a manifold structure on the unit sphere of `E`
(`EuclideanSpace.instChartedSpaceSphere`), so instance search finds the sphere of `ℂᵏ⁺¹`, and its
quotients, to be manifolds of dimension `2k + 1`; the instance
`TauCeti.factFinrankEuclideanSpaceComplexOneAdd` does the same for the index type `Fin (1 + k)` of
the block decomposition `ℂ¹⁺ᵏ = ℂ ⊕ ℂᵏ`. Likewise,
`TauCeti.instFactCardEqFinrankEuclideanSpace` records `Fintype.card ι = Module.finrank 𝕜
(EuclideanSpace 𝕜 ι)` as a `Fact` for rank-indexed APIs such as
`TauCeti.OrthonormalFrameBundle.orientedFrames`.

The real coordinates of `ℂⁱ` (`TauCeti.complexEuclideanRealCoords`) identify it `ℝ`-linearly with
`ℝ²ⁱ`, the real parts of the coordinates first and then their imaginary parts. They carry the
closed disks in which characteristic maps of CW complexes are defined onto complex Euclidean
disks. The real inner product of `ℂⁱ`, the one for which its unit sphere is a manifold, is the real
part of its complex inner product (`EuclideanSpace.real_inner_eq_re_inner`).
-/

public section

open scoped InnerProductSpace

/-- On `EuclideanSpace ℂ ι`, the real inner product, the sum of the real inner products of the
coordinates, is the real part of the complex inner product. -/
theorem EuclideanSpace.real_inner_eq_re_inner {ι : Type*} [Fintype ι]
    (x y : EuclideanSpace ℂ ι) : ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re := by
  simp [PiLp.inner_apply, Complex.inner, Complex.re_sum]

namespace TauCeti

/-- Two distinct points of `EuclideanSpace 𝕜 (Fin n)` force the dimension to be positive. -/
theorem pos_of_ne_euclideanSpace {𝕜 : Type*} {n : ℕ} {x y : EuclideanSpace 𝕜 (Fin n)}
    (hxy : x ≠ y) : 0 < n :=
  Nat.pos_of_ne_zero (by rintro rfl; exact hxy (Subsingleton.elim x y))

/-- The real dimension of `ℂᵏ⁺¹` is `2k + 2`, written as `(2k + 1) + 1`, so that its unit sphere
is `S²ᵏ⁺¹`. -/
theorem finrank_real_euclideanSpace_complex (k : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin (k + 1))) = 2 * k + 1 + 1 := by
  rw [finrank_real_of_complex, finrank_euclideanSpace_fin]; ring

/-- The real dimension of `ℂᵏ⁺¹` is `2k + 2`, written as `(2k + 1) + 1` so that its unit sphere,
and quotients of the sphere, are found to be manifolds of dimension `2k + 1`. -/
instance factFinrankEuclideanSpaceComplex (k : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin (k + 1))) = 2 * k + 1 + 1) :=
  ⟨finrank_real_euclideanSpace_complex k⟩

/-- The real dimension of `ℂ¹⁺ᵏ`, indexed by `Fin (1 + k)` as in the block decomposition
`ℂ¹⁺ᵏ = ℂ ⊕ ℂᵏ`, is `2k + 2`, written as `(2k + 1) + 1` so that its unit sphere is found to be a
manifold of dimension `2k + 1`. -/
instance factFinrankEuclideanSpaceComplexOneAdd (k : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin (1 + k))) = 2 * k + 1 + 1) :=
  ⟨by rw [add_comm 1 k]; exact finrank_real_euclideanSpace_complex k⟩

/-- The cardinality of `ι` equals the dimension of `EuclideanSpace 𝕜 ι`, recorded as a `Fact` for
rank-indexed APIs such as `TauCeti.OrthonormalFrameBundle.orientedFrames`. -/
instance instFactCardEqFinrankEuclideanSpace (𝕜 ι : Type*) [RCLike 𝕜] [Fintype ι] :
    Fact (Fintype.card ι = Module.finrank 𝕜 (EuclideanSpace 𝕜 ι)) :=
  ⟨(finrank_euclideanSpace (𝕜 := 𝕜) (ι := ι)).symm⟩

/-- The real coordinates of `ℂⁱ`, as a continuous `ℝ`-linear isomorphism onto `ℝᵐ` for `m = 2i`:
coordinate `j + i * a` of the image of `v` is the real part of `vⱼ` for `a = 0` and its imaginary
part for `a = 1` (`complexEuclideanRealCoords_apply`). It is the coordinate isomorphism of the
`ℝ`-basis `{eⱼ, I • eⱼ}` of `ℂⁱ`. -/
noncomputable def complexEuclideanRealCoords {i m : ℕ} (hm : 2 * i = m) :
    EuclideanSpace ℂ (Fin i) ≃L[ℝ] (Fin m → ℝ) :=
  ((Complex.basisOneI.smulTower (EuclideanSpace.basisFun (Fin i) ℂ).toBasis).reindex
    (finProdFinEquiv.trans (finCongr hm))).equivFun.toContinuousLinearEquiv

/-- The coordinates of `complexEuclideanRealCoords hm v` are the real and imaginary parts of the
coordinates of `v`, read through `Complex.basisOneI.repr`. -/
@[simp]
theorem complexEuclideanRealCoords_apply {i m : ℕ} (hm : 2 * i = m) (v : EuclideanSpace ℂ (Fin i))
    (a : Fin 2) (j : Fin i) :
    complexEuclideanRealCoords hm v (Fin.cast hm (finProdFinEquiv (a, j))) =
      Complex.basisOneI.repr (v j) a := by
  simp [complexEuclideanRealCoords, Module.Basis.smulTower_repr]

end TauCeti

end
