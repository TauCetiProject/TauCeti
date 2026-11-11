/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Geometry.Manifold.Complex.Analytic
public import TauCeti.Geometry.Manifold.IsManifold.RestrictScalars
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
public import TauCeti.Geometry.Manifold.Morse.CWModel
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Algebra.Category.ModuleCat.Finrank
import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Compact
import TauCeti.Geometry.Manifold.Morse.EulerCharacteristic

/-!
# Compact complex manifolds have finite CW type

A compact complex manifold `M` of complex dimension `n` is, with the same charts, a compact smooth
boundaryless real manifold of real dimension `2n`. By the Morse-theoretic CW model of compact
manifolds (`TauCeti.FiniteCWType.of_isManifold`) it therefore has finite CW type, so its finite-CW
Euler characteristic `TauCeti.eulerChar M` is defined. This applies in particular to every compact
Riemann surface.

The Euler--Poincaré formula expresses `eulerChar M` as the alternating sum of the dimensions of
the singular homology of `M` over any division ring `k`, and the homology of a compact manifold
vanishes above its real dimension. So `eulerChar M = ∑ᵢ₌₀²ⁿ (-1)ⁱ dim Hᵢ(M; k)`. If `M` is
connected then `H₀(M; k) = k`, and for a compact connected Riemann surface this reads
`eulerChar M = 1 - b₁ + b₂`. These homological statements only use the charts of `M`, so they are
stated for a compact Hausdorff space charted on a complex vector space, with finite CW type as an
instance argument; for a complex manifold it is supplied by
`TauCeti.ComplexManifold.finiteCWType`.

These statements do not assert `b₂ = 1` or that `b₁` is even. The first needs the fundamental
class of the complex orientation, the second Poincaré duality.

With the underlying real manifold structure `IsManifold.restrictScalars`, `eulerChar M` is the
signed count of the critical points of any Morse function on `M`, by
`TauCeti.IsMorse.sum_range_neg_one_pow_mul_toNat_criticalCount_eq_eulerChar` (see the example at
the end of this file).

## Main results

* `TauCeti.ComplexManifold.finiteCWType`: a compact Hausdorff manifold modelled on a boundaryless
  complex model over a finite-dimensional space, of class `C^n` for some `n ≠ 0`, has finite CW
  type.
* `TauCeti.ComplexManifold.instFiniteCWType`: the corresponding low-priority instance for compact
  Riemann surfaces, charted on `ℂ`.
* `TauCeti.ComplexManifold.isZero_singularHomology_of_two_mul_finrank_lt`: the singular homology
  of a compact space charted on `ℂⁿ` vanishes above degree `2n`.
* `TauCeti.ComplexManifold.eulerChar_eq_sum_range_finrank_singularHomology`: the Euler
  characteristic is the alternating sum of the Betti numbers up to twice the complex dimension.
* `TauCeti.ComplexManifold.eulerChar_eq_one_sub_finrank_add_finrank`: a compact connected
  Riemann surface has `eulerChar M = 1 - b₁ + b₂`.

## Checks

* `TauCeti.ComplexManifold.eulerChar_onePoint_complex`: for the Riemann sphere the Euler
  characteristic of this file is `2`, as computed by `TauCeti.eulerChar_onePoint`.
* `TauCeti.ComplexManifold.finrank_singularHomology_two_onePoint_complex`: hence
  `b₂ = b₁ + 1` for the Riemann sphere.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5.
* A. Hatcher, *Algebraic Topology*, Theorem 2.44 and Proposition 3.29.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Module
open scoped Manifold ContDiff

universe u

namespace TauCeti

namespace ComplexManifold

section FiniteCWType

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace H] {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]

variable (I : ModelWithCorners ℂ E H) [I.Boundaryless] (M) [ChartedSpace H M] in
/-- **Compact complex manifolds have finite CW type.** A compact Hausdorff manifold modelled on a
boundaryless complex model `I` over a finite-dimensional space, of class `C^n` for some `n ≠ 0`, is
homotopy equivalent to a finite CW complex. With the same charts it is a compact smooth
boundaryless real manifold, modelled on `I.restrictScalars ℝ`, so this is
`TauCeti.FiniteCWType.of_isManifold`. -/
theorem finiteCWType {n : ℕ∞ω} (hn : n ≠ 0) [h : IsManifold I n M] : FiniteCWType M :=
  have : IsManifold (I.restrictScalars ℝ) ∞ M :=
    I.isManifold_restrictScalars ℝ (h.of_ne_zero ∞ hn)
  FiniteCWType.of_isManifold (I := I.restrictScalars ℝ) M

/-- **Compact Riemann surfaces have finite CW type.** A compact Hausdorff complex manifold charted
on `ℂ` has finite CW type. This is a low-priority instance, the case `I = 𝓘(ℂ)` of
`TauCeti.ComplexManifold.finiteCWType`. Since `TauCeti.FiniteCWType` is a proposition, it agrees
with every other instance, for example on the Riemann sphere. -/
instance (priority := 100) instFiniteCWType [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M] :
    FiniteCWType M :=
  finiteCWType M 𝓘(ℂ) one_ne_zero

end FiniteCWType

section Homology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace E M]

/-- **The homology of a compact complex manifold vanishes above twice its complex dimension.**
For a compact Hausdorff space charted on a complex vector space `E`, `Hₖ(M; N) = 0` for
`k > 2 · dim_ℂ E`, since the real dimension of `E` is `2 · dim_ℂ E`. -/
theorem isZero_singularHomology_of_two_mul_finrank_lt {Λ : Type u} [Ring Λ] (N : ModuleCat.{u} Λ)
    {k : ℕ} (hk : 2 * finrank ℂ E < k) :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{u} Λ) k).obj N).obj (TopCat.of M)) :=
  isZero_singularHomology_of_compactSpace (E := E) N
    (by rw [← finrank_mul_finrank ℝ ℂ E, Complex.finrank_real_complex]) hk

variable [FiniteCWType M] (k : Type u) [DivisionRing k]

variable (M) in
/-- **The Euler characteristic of a compact complex manifold as an alternating sum of Betti
numbers.** For a compact Hausdorff space `M` of finite CW type charted on a complex vector space of
dimension `n`, for instance a compact complex manifold, and any division ring `k`,
`eulerChar M = ∑ᵢ₌₀²ⁿ (-1)ⁱ dim Hᵢ(M; k)`. -/
theorem eulerChar_eq_sum_range_finrank_singularHomology :
    eulerChar M = ∑ i ∈ Finset.range (2 * finrank ℂ E + 1), (-1 : ℤ) ^ i *
      finrank k (((singularHomologyFunctor (ModuleCat.{u} k) i).obj (ModuleCat.of k k)).obj
        (TopCat.of M)) := by
  rw [eulerChar_eq_finsum_finrank_singularHomology M k,
    ModuleCat.finsum_neg_one_pow_finrank_eq_sum_range (N := 2 * finrank ℂ E + 1) fun i hi ↦
      isZero_singularHomology_of_two_mul_finrank_lt (E := E) _ (by omega)]

variable (M) in
/-- **The Euler characteristic of a compact connected Riemann surface is `1 - b₁ + b₂`.** For a
compact connected Hausdorff space `M` of finite CW type charted on a complex line, for instance a
compact connected Riemann surface, and any division ring `k`,
`eulerChar M = 1 - dim H₁(M; k) + dim H₂(M; k)`. The zeroth Betti number is `1` because `M` is
path connected. -/
theorem eulerChar_eq_one_sub_finrank_add_finrank [ConnectedSpace M] (hE : finrank ℂ E = 1) :
    eulerChar M = 1 -
      (finrank k (((singularHomologyFunctor (ModuleCat.{u} k) 1).obj (ModuleCat.of k k)).obj
        (TopCat.of M)) : ℤ) +
      finrank k (((singularHomologyFunctor (ModuleCat.{u} k) 2).obj (ModuleCat.of k k)).obj
        (TopCat.of M)) := by
  have := ChartedSpace.locallyPathConnectedSpace E M
  have : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  have h₀ : finrank k
      (((singularHomologyFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)).obj
        (TopCat.of M)) = 1 := by
    rw [(asIso ((TopCat.of M).singularHomology₀ε (ModuleCat.of k k))).toLinearEquiv.finrank_eq]
    exact finrank_self k
  rw [eulerChar_eq_sum_range_finrank_singularHomology (E := E) M k, hE]
  simp [Finset.sum_range_succ, h₀]
  ring

end Homology

/-! ### Checks -/

section Checks

/-- **Check: the Riemann sphere.** The finite CW type of `OnePoint ℂ` as a compact complex
manifold gives Euler characteristic `2`, the value of `TauCeti.eulerChar_onePoint`. -/
theorem eulerChar_onePoint_complex :
    @eulerChar (OnePoint ℂ) _ (finiteCWType (OnePoint ℂ) 𝓘(ℂ) (n := ω) (by simp)) = 2 := by
  rw [eulerChar_onePoint, Complex.finrank_real_complex]
  norm_num

/-- **Check: Betti numbers of the Riemann sphere.** By
`TauCeti.ComplexManifold.eulerChar_eq_one_sub_finrank_add_finrank` and
`TauCeti.ComplexManifold.eulerChar_onePoint_complex`, the Riemann sphere has `b₂ = b₁ + 1` over
every division ring. -/
theorem finrank_singularHomology_two_onePoint_complex (k : Type) [DivisionRing k] :
    finrank k (((singularHomologyFunctor (ModuleCat.{0} k) 2).obj (ModuleCat.of k k)).obj
        (TopCat.of (OnePoint ℂ))) =
      finrank k (((singularHomologyFunctor (ModuleCat.{0} k) 1).obj (ModuleCat.of k k)).obj
        (TopCat.of (OnePoint ℂ))) + 1 := by
  have := eulerChar_eq_one_sub_finrank_add_finrank (OnePoint ℂ) k (E := ℂ) (by simp)
  rw [eulerChar_onePoint, Complex.finrank_real_complex] at this
  omega

/-- On a compact Riemann surface the Euler characteristic is the signed count of the critical
points of any Morse function on the underlying real surface. -/
example {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ∞ M] {f : M → ℝ} (hf : IsMorse 𝓘(ℝ, ℂ) f) :
    ∑ i ∈ Finset.range (finrank ℝ ℂ + 1), (-1 : ℤ) ^ i * (criticalCount 𝓘(ℝ, ℂ) f i).toNat =
      eulerChar M :=
  have : IsManifold 𝓘(ℝ, ℂ) ∞ M := IsManifold.restrictScalars ℝ ‹_›
  hf.sum_range_neg_one_pow_mul_toNat_criticalCount_eq_eulerChar

end Checks

end ComplexManifold

end TauCeti
