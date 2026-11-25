/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.ExtendByZero
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Geometry.Manifold.Metrizable

/-!
# Relative primitives

Let `η` be a smooth `(k + 1)`-form on a manifold `W` which is exact on an open subset `U`, say
`η = dθ` on `U`, and let `K ⊆ U` be closed in `W`. Cutting `θ` off by a smooth function equal to
one near `K` and vanishing near the points outside `U`, and extending by zero, gives a smooth
`k`-form `μ` on `W` with `dμ = η` near `K` (`TauCeti.exists_eventuallyEq_mextDerivₗ`). The form
`η - dμ` then has the same exterior derivative and the same de Rham class as `η` when `η` is
closed, and it vanishes near `K`. Multiplying `η` itself by the cut-off function would not do: it
changes the exterior derivative by the wedge product of the differential of the cut-off function
with `η`.

Exactness on `U` is automatic for a `(k + 1)`-form that is closed on `U` once `U` has no de Rham
cohomology in degree `k + 1`
(`TauCeti.exists_eventuallyEq_mextDerivₗ_of_subsingleton_deRhamCohomology`), for instance in degree
one when `U` is simply connected. This is the form in which a primitive of a difference of two
symplectic forms that agree near a set is made to vanish near a smaller set, before a relative
Moser argument.

As elsewhere in the de Rham theory of open subsets, `W` is an open subset of an ambient manifold
`M`, and `U ≤ W`; the case of `M` itself is `W = ⊤`.

## Main results

* `TauCeti.exists_eventuallyEq_mextDerivₗ`: a form exact on `U` is exact near a closed subset of
  `U`, with a primitive vanishing near the points outside `U`.
* `TauCeti.exists_eventuallyEq_mextDerivₗ_of_subsingleton_deRhamCohomology`: a `(k + 1)`-form
  closed on an open subset `U` without cohomology in degree `k + 1` is exact near a closed subset
  of `U`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  proof of Theorem 9.4.7 (a primitive vanishing near the two cap spheres, before the relative
  Moser argument).
-/

public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] {U W : Opens M} (h : U ≤ W)

/-- **Relative primitives.** Let `η` be a smooth `(k + 1)`-form on `W` which is exact on an open
subset `U ≤ W`, and let `K ⊆ U` be closed in `W`. Then there is a smooth `k`-form `μ` on `W`,
vanishing near every point of `W` outside `U`, with `dμ = η` near `K`. So `η - dμ` vanishes near
`K` and differs from `η` by an exact form. -/
theorem exists_eventuallyEq_mextDerivₗ {K : Set W} (hK : IsClosed K)
    (hKU : ∀ x ∈ K, (x : M) ∈ U) {k : ℕ} {η : SmoothForm I W ℝ (k + 1)}
    (hη : SmoothForm.mpullback (Opens.inclusion h) (contMDiff_inclusion h) η ∈
      exactForms I U (k + 1)) :
    ∃ μ : SmoothForm I W ℝ k, (∀ᶠ x in 𝓝ˢ K, (mextDerivₗ I k μ).val x = η.val x) ∧
      ∀ x : W, (x : M) ∉ U → ∀ᶠ y in 𝓝 x, μ.val y = 0 := by
  rw [exactForms_succ] at hη
  obtain ⟨θ, hθ⟩ := hη
  -- The open subset `W` is again a Hausdorff σ-compact manifold, hence normal.
  have := Manifold.sigmaCompactSpace_opens I W
  have := Manifold.normalSpace_opens I W
  -- A cut-off function vanishing near the points outside `U` and equal to one near `K`.
  have hA : IsClosed {x : W | (x : M) ∉ U} :=
    (U.isOpen.preimage continuous_subtypeVal).isClosed_compl
  have hAK : Disjoint {x : W | (x : M) ∉ U} K :=
    disjoint_left.mpr fun x hxU hxK ↦ hxU (hKU x hxK)
  obtain ⟨ρ, hρ0, hρ1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed I (n := ⊤) hA hK hAK
  have hρU : ∀ x : W, (x : M) ∉ U → ∀ᶠ y in 𝓝 x, ρ y = 0 :=
    fun x hx ↦ hρ0.filter_mono (nhds_le_nhdsSet hx)
  -- The cut-off primitive `ρ θ`, extended by zero from `U` to `W`.
  refine ⟨⟨RoughForm.extendByZero W fun y : U ↦ ρ (Opens.inclusion h y) • θ.val y,
      (θ.isSmoothForm.extendByZero_smul h ρ.contMDiff hρU).mem_smoothBundleForms⟩, ?_,
    fun x hx ↦ RoughForm.eventually_extendByZero_smul_eq_zero h θ.val (hρU x hx)⟩
  filter_upwards [hρ1.eventually_nhdsSet] with x hx
  rw [mextDerivₗ_apply]
  exact mextDeriv_extendByZero_smul_apply_of_eventuallyEq_one h hρU hθ hx

/-- **Relative primitives of closed forms.** Let `U ≤ W` be an open subset without de Rham
cohomology in degree `k + 1` and `η` a smooth `(k + 1)`-form on `W` which is closed on `U`; in
degree one, `U` may for instance be simply connected. For every `K ⊆ U` closed in `W` there is a
smooth `k`-form `μ` on `W`, vanishing near every point of `W` outside `U`, with `dμ = η` near
`K`. -/
theorem exists_eventuallyEq_mextDerivₗ_of_subsingleton_deRhamCohomology {k : ℕ}
    (hU : Subsingleton (deRhamCohomology I U (k + 1))) {K : Set W} (hK : IsClosed K)
    (hKU : ∀ x ∈ K, (x : M) ∈ U) {η : SmoothForm I W ℝ (k + 1)}
    (hη : SmoothForm.mpullback (Opens.inclusion h) (contMDiff_inclusion h) η ∈
      closedForms I U (k + 1)) :
    ∃ μ : SmoothForm I W ℝ k, (∀ᶠ x in 𝓝ˢ K, (mextDerivₗ I k μ).val x = η.val x) ∧
      ∀ x : W, (x : M) ∉ U → ∀ᶠ y in 𝓝 x, μ.val y = 0 :=
  exists_eventuallyEq_mextDerivₗ h hK hKU <|
    (deRhamCohomology.mk_eq_zero_iff I (k + 1) ⟨_, hη⟩).mp (hU.elim _ _)

end TauCeti
