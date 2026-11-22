/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Generic.Universal.Differential
import TauCeti.Analysis.Normed.Module.FiniteDimension
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Banach
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.SecondCountable
import TauCeti.Geometry.Manifold.ExtChartAt.Basic
/-!
# Generic `C^k` functions are Morse, by the Sard–Smale theorem

Let `M` be a compact Hausdorff manifold without boundary modelled on a real normed space `E`,
which is then finite-dimensional unless `M` is empty, and `k ≥ 2` a natural number. This file
proves that the `C^k` functions on `M` all of whose critical points are nondegenerate form a
residual set in the Banach space of `C^k` functions, by parametric transversality for the
**universal differential** `S(x, f) = df_x` (`TauCeti.universalDifferential`), a section of the
cotangent bundle along `M × C^k(M, ℝ) → M`.

Give `C^k(M, ℝ)` the norm of a finite chart atlas
(`ContMDiffMap.finiteAtlasNormedAddCommGroup`), which exists on a compact manifold
(`TauCeti.exists_finite_compact_chart_cover`), is complete
(`ContMDiffMap.completeSpace_finiteAtlas`) and induces the weak Whitney topology. The hypotheses
of the Sard–Smale form of parametric transversality,
`TauCeti.mem_residual_setOf_isRegularSectionParameter`, then hold as follows.

* The section `S` is `C^(k - 1)` (`TauCeti.contMDiff_universalDifferential`), and `k - 1 ≥ 1`.
* At a zero `(x, f)`, the linearization of the slice `y ↦ df_y` is the critical Hessian of `f` at
  `x` (`TauCeti.sectionLinearization_mvfderiv`), a linear map from `T_x M` to its dual. Both are
  finite-dimensional of the same dimension, so it is Fredholm of index zero, and Smale's regularity
  threshold `k - 1 > max (0, 0)` is met.
* The total linearization `(v, h) ↦ Hess_x f (v) + dh_x` is onto
  (`TauCeti.surjective_sectionLinearization_universalDifferential`).
* The zero set of `S` is second countable, as a subspace of the product of the compact manifold `M`
  and the separable Banach space `C^k(M, ℝ)`
  (`ContMDiffMap.secondCountableTopology_manifoldWeakWhitney_of_sigmaCompact`).

The regular parameters of `S` are exactly the functions whose critical points are nondegenerate
(`TauCeti.isRegularSectionParameter_universalDifferential_iff`). Residuality refers only to the
topology, so it is stated for the weak Whitney topology and does not depend on the chosen atlas.

The same set is also open and dense, by the persistence of nondegenerate critical points
(`TauCeti.isOpen_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint`) and by
local linear perturbations in charts
(`TauCeti.dense_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint`). The
argument here instead runs the general transversality machinery on a Banach space of functions
at index zero, with the actual regularity `k - 1` of the universal section.

## Main results

* `TauCeti.mem_residual_setOf_isRegularSectionParameter_universalDifferential`: the regular
  parameters of the universal differential form a residual set of `C^k` functions.
* `TauCeti.mem_residual_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint`:
  the `C^k` functions all of whose critical points are nondegenerate form a residual set.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications **52**, 2012, Appendix A.3 (Theorem A.3.6, generic regularity of universal
  Fredholm sections).
* S. Smale, *An infinite dimensional version of Sard's theorem*, Amer. J. Math. **87** (1965),
  861–866.
* M. Hirsch, *Differential Topology*, GTM 33, Springer, 1976, Chapter 6, §1 (genericity of Morse
  functions).
-/

public section

open Bundle Function Set Filter
open scoped Manifold ContDiff Topology TauCeti.ManifoldWeakWhitney

namespace TauCeti

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

/-- **Sard–Smale for the universal differential.** On a compact Hausdorff manifold without
boundary modelled on a real normed space, and for `k ≥ 2`, the `C^k` functions that are
regular parameters of the universal differential `(x, f) ↦ df_x` form a residual set for the weak
Whitney topology, the topology of the Banach space of `C^k` functions. -/
theorem mem_residual_setOf_isRegularSectionParameter_universalDifferential {k : ℕ}
    (hk : 2 ≤ k) :
    {f : C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ | IsRegularSectionParameter (F := E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) E Prod.fst
        (universalDifferential 𝓘(ℝ, E)) f} ∈ residual C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ := by
  -- On the empty manifold every function is regular. Otherwise the compact manifold `M` is locally
  -- compact, so its model `E` is finite-dimensional.
  rcases isEmpty_or_nonempty M with hM | hM
  · exact univ_mem' fun f ↦ isRegularSectionParameter_iff.2 fun x ↦ isEmptyElim x
  have := FiniteDimensional.of_locallyCompact_manifold M 𝓘(ℝ, E)
  obtain ⟨N, c, K, hK⟩ := exists_finite_compact_chart_cover (I := 𝓘(ℝ, E)) (M := M)
  let := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
  let := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
  have := ContMDiffMap.completeSpace_finiteAtlas (F := ℝ) k hK
  have := ChartedSpace.secondCountable_of_sigmaCompact E M
  -- The universal section is `C^(k - 1)`, and `k - 1 ≥ 1` is Smale's threshold at index zero.
  have hcont := contMDiff_universalDifferential (I := 𝓘(ℝ, E)) k hK (m := ((k - 1 : ℕ) : ℕ∞ω))
    (by norm_cast; omega)
  refine mem_residual_setOf_isRegularSectionParameter (n := ((k - 1 : ℕ) : ℕ∞ω))
    (fun z _ ↦ hcont z) (fun z _ ↦ ?_)
    (fun z _ ↦ surjective_sectionLinearization_universalDifferential k hK hk z) (fun z _ ↦ ?_)
  · -- The slice linearization is a map between finite-dimensional spaces.
    exact ContinuousLinearMap.isFredholm_of_finiteDimensional _
  · -- The slice linearization maps `T_x M`, which is `E`, to its dual, so it has index zero.
    have hdual : Module.finrank ℝ (TangentSpace 𝓘(ℝ, E) z.1 →L[ℝ] ℝ) =
        Module.finrank ℝ (TangentSpace 𝓘(ℝ, E) z.1) :=
      ContinuousLinearMap.dual_finrank_eq (𝕜 := ℝ) (E := E)
    rw [LinearMap.index_eq_of_finiteDimensional, hdual, sub_self]
    norm_cast
    omega

/-- **Generic `C^k` functions are Morse.** On a compact Hausdorff manifold without boundary
modelled on a real normed space, and for `k ≥ 2`, the `C^k` functions all of whose critical
points are nondegenerate form a residual set for the weak Whitney topology, the topology of the
Banach space of `C^k` functions. This is the Sard–Smale theorem applied to the universal
differential, `TauCeti.mem_residual_setOf_isRegularSectionParameter_universalDifferential`. -/
theorem mem_residual_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint {k : ℕ}
    (hk : 2 ≤ k) :
    {f : C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ | ∀ x ∈ criticalPoints 𝓘(ℝ, E) f,
      IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x} ∈ residual C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact univ_mem' fun f x ↦ isEmptyElim x
  have := FiniteDimensional.of_locallyCompact_manifold M 𝓘(ℝ, E)
  filter_upwards [mem_residual_setOf_isRegularSectionParameter_universalDifferential (M := M) hk]
    with f hf
  exact (isRegularSectionParameter_universalDifferential_iff (by exact_mod_cast hk) f).1 hf

end TauCeti
