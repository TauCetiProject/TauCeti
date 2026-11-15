/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Banach
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.SecondCountable
public import TauCeti.Geometry.Manifold.Morse.Generic.Universal.Differential
import TauCeti.Analysis.Normed.Module.FiniteDimension

/-!
# Generic Morse functions by the Sard–Smale theorem

Let `M` be a compact boundaryless Hausdorff manifold modelled on a real normed space `E`, and
`k ≥ 2`. Unless `M` is empty, in which case every statement below is trivial, `E` is
finite-dimensional, since `M` is locally compact. The universal differential `S(x, f) = df_x`
(`TauCeti.universalDifferential`) is a section of the cotangent bundle along the projection
`M × C^k(M, ℝ) → M`. Give `C^k(M, ℝ)` the norm of a finite chart atlas
(`ContMDiffMap.finiteAtlasNormedAddCommGroup`). Then:

* `C^k(M, ℝ)` is a Banach space (`ContMDiffMap.completeSpace_finiteAtlas`), and `M × C^k(M, ℝ)`
  is second countable (`ContMDiffMap.secondCountableTopology_manifoldWeakWhitney_of_sigmaCompact`),
  hence so is the zero set of `S`;
* `S` is `C^(k - 1)` (`TauCeti.contMDiff_universalDifferential`);
* its linearization in the point direction is the critical Hessian, a map between the
  finite-dimensional spaces `T_x M` and `T*_x M` of equal dimension, hence Fredholm of index `0`;
* its total linearization is onto (`TauCeti.surjective_sectionLinearization_universalDifferential`).

Smale's regularity threshold at index `0` asks for `C¹`, and `k - 1 ≥ 1`. Parametric
transversality for Fredholm bundle sections (`TauCeti.mem_residual_setOf_isRegularSectionParameter`)
therefore applies: the regular parameters of `S` form a residual set of `C^k` functions
(`TauCeti.mem_residual_setOf_isRegularSectionParameter_universalDifferential`). These are exactly
the functions all of whose critical points are nondegenerate
(`TauCeti.isRegularSectionParameter_universalDifferential_iff`).

The residual filter depends only on the topology of `C^k(M, ℝ)`, which for every finite atlas is
the weak Whitney topology. The statement is therefore made for the weak Whitney topology and does
not mention an atlas; one is chosen in the proof (`TauCeti.exists_finite_compact_chart_cover`).

The same set of functions is open
(`TauCeti.isOpen_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint`) and dense
(`TauCeti.dense_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint`, by linear
perturbations in charts), for any boundaryless model and any regularity `2 ≤ n`, so its
residuality as such already follows by `residual_of_dense_open`. The result here exhibits it
instead as the set of regular parameters of a transverse Fredholm section, the form in which
genericity is obtained for moduli spaces cut out by sections.

## References

* M. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976, Chapter 6,
  §1 (genericity of Morse functions).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications **52**, 2012, Appendix A.3 (Theorem A.3.6, universal sections and their regular
  parameters).
* S. Smale, *An infinite dimensional version of Sard's theorem*, Amer. J. Math. 87 (1965),
  861–866.
-/

public section

open Bundle Function Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology TauCeti.ManifoldWeakWhitney

namespace TauCeti

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  {k : ℕ}

/-- **Sard–Smale for the universal differential.** On a compact boundaryless Hausdorff manifold
modelled on a real normed space and for `k ≥ 2`, the regular parameters of the
universal differential `(x, f) ↦ df_x` form a residual set of `C^k` functions, for the weak Whitney
topology. -/
theorem mem_residual_setOf_isRegularSectionParameter_universalDifferential (hk : 2 ≤ k) :
    {f : C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ | IsRegularSectionParameter (F := E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) E Prod.fst
        (universalDifferential 𝓘(ℝ, E)) f} ∈ residual C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ := by
  -- On the empty manifold every function is a regular parameter; otherwise the model space of
  -- the compact manifold is locally compact, hence finite-dimensional.
  rcases isEmpty_or_nonempty M with hM | hM
  · exact Filter.mem_of_superset univ_mem fun f _ ↦
      isRegularSectionParameter_iff.2 fun x ↦ isEmptyElim x
  have := FiniteDimensional.of_locallyCompact_manifold M 𝓘(ℝ, E)
  obtain ⟨N, c, K, hK⟩ := exists_finite_compact_chart_cover (I := 𝓘(ℝ, E)) (M := M)
  let := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
  let := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
  have := ContMDiffMap.completeSpace_finiteAtlas (F := ℝ) k hK
  have : IsManifold 𝓘(ℝ, E) 1 M := .of_le (n := ∞) (WithTop.coe_le_coe.2 le_top)
  -- The zero set of the universal differential lies in the second countable space
  -- `M × C^k(M, ℝ)`.
  have := ChartedSpace.secondCountable_of_sigmaCompact E M
  -- The point-direction linearization maps `T_x M` to `T*_x M`, of the same finite dimension.
  have hindex (z : M × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) :
      LinearMap.index (sectionLinearization (F := E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) 𝓘(ℝ, E) (fun y ↦ (y, z.2).1)
        (fun y ↦ universalDifferential 𝓘(ℝ, E) (y, z.2)) z.1).toLinearMap = 0 := by
    rw [index_sectionLinearization_of_finiteDimensional, ContinuousLinearMap.dual_finrank_eq,
      sub_self]
  refine mem_residual_setOf_isRegularSectionParameter (n := ((k - 1 : ℕ) : ℕ∞ω))
    (fun z _ ↦ (contMDiff_universalDifferential k hK ?_).contMDiffAt)
    (fun z _ ↦ ContinuousLinearMap.isFredholm_of_finiteDimensional _)
    (fun z _ ↦ surjective_sectionLinearization_universalDifferential k hK hk z)
    (fun z _ ↦ ?_)
  · -- Regularity `C^(k - 1)`.
    exact_mod_cast (Nat.sub_add_cancel (one_le_two.trans hk)).le
  · -- Smale's threshold at index `0` is `C¹`, and `k - 1 ≥ 1`.
    rw [hindex z]
    exact_mod_cast Nat.le_sub_of_add_le hk

end TauCeti
