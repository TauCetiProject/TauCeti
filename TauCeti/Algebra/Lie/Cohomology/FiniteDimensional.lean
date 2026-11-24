/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg
public import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# The Chevalley–Eilenberg differential on continuous forms with trivial coefficients

Let `L` be a finite-dimensional Hausdorff topological Lie algebra over a complete nontrivially
normed field `𝕜`, and `N` a topological vector space over `𝕜`. Every alternating map on `L` is
continuous (`AlternatingMap.toContinuousAlternatingMap`), so the Chevalley–Eilenberg differential
`TauCeti.LieModule.Cohomology.d` with coefficients in `N`, regarded as a trivial `L`-module through
Mathlib's type synonym `TrivialLieModule 𝕜 L N`, acts on continuous alternating forms
`L [⋀^Fin n]→L[𝕜] N`. This is `TauCeti.LieModule.Cohomology.trivialD`. No Lie module structure on
`N` itself is needed. Since `L` acts trivially, the differential has only bracket terms:

`(d ω)(x₀, …, xₙ₊₁) = ∑_{i < j} (-1)^(i + j) ω (⁅xᵢ, xⱼ⁆, x₀, …, x̂ᵢ, …, x̂ⱼ, …, xₙ₊₁)`,

and it vanishes in degree zero.

## Main definitions

* `TauCeti.LieModule.Cohomology.trivialD`: the Chevalley–Eilenberg differential with trivial
  coefficients on continuous alternating forms.

## Main results

* `TauCeti.LieModule.Cohomology.trivialD_apply`: `trivialD` is `d` with coefficients in
  `TrivialLieModule 𝕜 L N`, transported along `TrivialLieModule.equiv`.
* `TauCeti.LieModule.Cohomology.trivialD_zero`, `TauCeti.LieModule.Cohomology.trivialD_succ_apply`:
  the explicit formula.
* `TauCeti.LieModule.Cohomology.trivialD_trivialD`: `trivialD` squares to zero.

## References

* C. Chevalley and S. Eilenberg, *Cohomology theory of Lie groups and Lie algebras*,
  Trans. Amer. Math. Soc. 63 (1948), 85–124.
-/

public section

noncomputable section

namespace TauCeti.LieModule.Cohomology

variable (𝕜 L N : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [LieRing L] [LieAlgebra 𝕜 L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul 𝕜 L] [T2Space L] [FiniteDimensional 𝕜 L]
  [AddCommGroup N] [Module 𝕜 N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [ContinuousSMul 𝕜 N]

/-- The Chevalley–Eilenberg differential on continuous alternating forms on a finite-dimensional
Lie algebra `L`, with values in `N` regarded as a trivial `L`-module (`TrivialLieModule`). -/
def trivialD (n : ℕ) : (L [⋀^Fin n]→L[𝕜] N) →ₗ[𝕜] L [⋀^Fin (n + 1)]→L[𝕜] N :=
  AlternatingMap.toContinuousAlternatingMap.toLinearMap ∘ₗ
    (TrivialLieModule.equiv 𝕜 L N).alternatingMapCongrRight.toLinearMap ∘ₗ
    d 𝕜 L (TrivialLieModule 𝕜 L N) n ∘ₗ
    (TrivialLieModule.equiv 𝕜 L N).alternatingMapCongrRight.symm.toLinearMap ∘ₗ
    AlternatingMap.toContinuousAlternatingMap.symm.toLinearMap

variable {𝕜 L N}

/-- `trivialD` is the Chevalley–Eilenberg differential `d` with coefficients in the trivial
module `TrivialLieModule 𝕜 L N`, transported along `TrivialLieModule.equiv`. -/
theorem trivialD_apply {n : ℕ} (ω : L [⋀^Fin n]→L[𝕜] N) (v : Fin (n + 1) → L) :
    trivialD 𝕜 L N n ω v = TrivialLieModule.equiv 𝕜 L N (d 𝕜 L (TrivialLieModule 𝕜 L N) n
      ((TrivialLieModule.equiv 𝕜 L N).alternatingMapCongrRight.symm ω.toAlternatingMap) v) := by
  simp only [trivialD, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    AlternatingMap.toContinuousAlternatingMap_symm_apply,
    AlternatingMap.coe_toContinuousAlternatingMap, LinearEquiv.alternatingMapCongrRight_apply_apply]

/-- With trivial coefficients, the differential vanishes in degree zero. -/
@[simp]
theorem trivialD_zero : trivialD 𝕜 L N 0 = 0 := by
  ext ω v
  simp [trivialD_apply, trivial_lie_zero]

/-- **The Chevalley–Eilenberg formula with trivial coefficients**:
`(d ω)(x₀, …, xₙ₊₁) = ∑_{i < j} (-1)^(i + j) ω (⁅xᵢ, xⱼ⁆, …)`, where the pairs `i < j` are written
as `(i.castSucc, j.succ)` with `i ≤ j`. -/
theorem trivialD_succ_apply {n : ℕ} (ω : L [⋀^Fin (n + 1)]→L[𝕜] N) (v : Fin (n + 2) → L) :
    trivialD 𝕜 L N (n + 1) ω v =
      ∑ i : Fin (n + 1), ∑ j ≥ i, (-1 : ℤ) ^ (i + j + 1 : ℕ) •
        ω (Matrix.vecCons ⁅v i.castSucc, v j.succ⁆ (j.removeNth (i.castSucc.removeNth v))) := by
  simp [trivialD_apply, d_succ_apply, trivial_lie_zero, map_sum, map_zsmul]

/-- The Chevalley–Eilenberg differential with trivial coefficients squares to zero. -/
@[simp]
theorem trivialD_trivialD (n : ℕ) (ω : L [⋀^Fin n]→L[𝕜] N) :
    trivialD 𝕜 L N (n + 1) (trivialD 𝕜 L N n ω) = 0 := by
  ext v
  simp [trivialD]

/-- The Chevalley–Eilenberg differential with trivial coefficients squares to zero, as a composite
of linear maps. -/
theorem trivialD_comp_trivialD (n : ℕ) : trivialD 𝕜 L N (n + 1) ∘ₗ trivialD 𝕜 L N n = 0 :=
  LinearMap.ext (trivialD_trivialD n)

end TauCeti.LieModule.Cohomology
