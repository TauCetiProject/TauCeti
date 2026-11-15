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
# Generic functions are Morse, by the Sard–Smale theorem

Let `M` be a compact smooth manifold without boundary, modelled on a finite-dimensional real
space `E`, and `k ≥ 2` an integer. This file shows that the `C^k` functions on `M` all of whose
critical points are nondegenerate form a residual set, by applying parametric transversality for
Fredholm sections, `TauCeti.isMeagre_setOf_not_isRegularSectionParameter`, which rests on the
Sard–Smale theorem, to the universal differential `S(x, f) = df_x`
(`TauCeti.universalDifferential`). Its hypotheses hold as follows.

* **Parameter space.** On the compact manifold `M` a finite chart atlas with compact pieces makes
  `C^k(M, ℝ)` a Banach space (`ContMDiffMap.finiteAtlasNormedAddCommGroup`,
  `ContMDiffMap.completeSpace_finiteAtlas`) whose topology is the weak Whitney topology.
* **Regularity.** The universal differential is `C^(k-1)`, in particular `C¹`, as a map into the
  cotangent bundle (`TauCeti.contMDiff_universalDifferential`).
* **Fredholm slices of index zero.** For a fixed function `f`, the linearization of `x ↦ df_x`
  at a point `x` maps the tangent space `T_x M` to the cotangent space `T*_x M`. Both have the
  dimension of `E`, so it is Fredholm of index zero
  (`TauCeti.index_sectionLinearization_of_finiteDimensional`), and Smale's regularity bound
  `k - 1 > max (0, 0)` is `k ≥ 2`.
* **Transversality.** The total linearization `(v, h) ↦ Hess_x f (v) + dh_x` is onto
  (`TauCeti.surjective_sectionLinearization_universalDifferential`).
* **Separability.** The universal zero set `{(x, f) | df_x = 0}` is second countable, as a subset
  of the product of the compact manifold `M` with the separable space `C^k(M, ℝ)`
  (`ContMDiffMap.secondCountableTopology_manifoldWeakWhitney_of_sigmaCompact`).

So the regular parameters of the universal differential form a residual set
(`TauCeti.mem_residual_setOf_isRegularSectionParameter_universalDifferential`). They are exactly
the functions whose critical points are all nondegenerate
(`TauCeti.isRegularSectionParameter_universalDifferential_iff`), which gives
`TauCeti.mem_residual_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint`.

This is the Banach-space route to the genericity of Morse functions. The same set is also open, by
the persistence of nondegenerate critical points under `C²`-small perturbations
(`TauCeti.isOpen_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint`), and
dense, by finitely many local linear perturbations, each made generic in one chart
(`TauCeti.dense_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint`). That
route proves the stronger statement that the set is open and dense, and it also applies to smooth
functions, whose space is not a Banach space. The route here proves only residuality, but it
treats all functions at once, with no chart patching, and uses only that the universal
differential is a `C¹` Fredholm section of index zero transverse to the zero section. This is the
form in which genericity is proved for moduli spaces cut out by Fredholm sections, where no local
linear perturbations are available.

## Main results

* `TauCeti.mem_residual_setOf_isRegularSectionParameter_universalDifferential`: the regular
  parameters of the universal differential form a residual set.
* `TauCeti.mem_residual_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint`:
  the `C^k` functions all of whose critical points are nondegenerate form a residual set.

## References

* S. Smale, *An infinite dimensional version of Sard's theorem*, Amer. J. Math. **87** (1965),
  861–866.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications **52**, 2012, Appendix A.3 (universal sections and their regular parameters).
* M. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976, Chapter 6,
  §1 (genericity of Morse functions).
-/

public section

open Bundle Function Module Set Filter
open scoped Manifold ContDiff Topology TauCeti.ManifoldWeakWhitney

namespace TauCeti

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

/-- **Regular parameters of the universal differential are generic.** On a compact smooth
manifold without boundary and for `k ≥ 2`, the `C^k` functions which are regular parameters of
the universal differential `(x, f) ↦ df_x` form a residual set in the weak Whitney topology, the
topology of the Banach space of `C^k` functions normed by a finite chart atlas. This is
parametric transversality for the universal differential, a `C^(k-1)` section of the cotangent
bundle over `M × C^k(M, ℝ)` with Fredholm slices of index zero and surjective total
linearization. -/
theorem mem_residual_setOf_isRegularSectionParameter_universalDifferential {k : ℕ}
    (hk : 2 ≤ k) :
    {f : C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ | IsRegularSectionParameter (F := E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) E Prod.fst
        (universalDifferential 𝓘(ℝ, E)) f} ∈ residual C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ := by
  -- Make `C^k(M, ℝ)` a Banach space with the norm of a finite chart atlas; its topology is the
  -- weak Whitney topology.
  obtain ⟨N, c, K, hK⟩ := exists_finite_compact_chart_cover (I := 𝓘(ℝ, E)) (M := M)
  let := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
  let := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
  have := ContMDiffMap.completeSpace_finiteAtlas (F := ℝ) k hK
  -- The universal zero set lies in the second-countable space `M × C^k(M, ℝ)`.
  have := ChartedSpace.secondCountable_of_sigmaCompact E M
  have hk1 : ((1 : ℕ) : WithTop ℕ∞) + 1 ≤ k := by exact_mod_cast hk
  refine mem_residual_setOf_isRegularSectionParameter (n := 1) (X := E)
    (I := 𝓘(ℝ, E)) (F := E →L[ℝ] ℝ) (E := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ)
    (fun z _ ↦ (contMDiff_universalDifferential k hK hk1) z)
    (fun _ _ ↦ ContinuousLinearMap.isFredholm_of_finiteDimensional _)
    (fun z _ ↦ surjective_sectionLinearization_universalDifferential k hK hk z) fun _ _ ↦ ?_
  -- Smale's bound `1 > max (index, 0)` holds: the slices map the tangent space to the cotangent
  -- space, of the same finite dimension, so they have index zero.
  rw [index_sectionLinearization_of_finiteDimensional,
    ContinuousLinearMap.dual_finrank_eq (𝕜 := ℝ) (E := E), sub_self]
  simp

/-- **Generic functions are Morse.** On a compact smooth manifold without boundary and for
`k ≥ 2`, the `C^k` functions all of whose critical points are nondegenerate form a residual set in
the weak Whitney topology, that is, in the Banach space of `C^k` functions normed by a finite chart
atlas. The set is moreover open and dense
(`TauCeti.isOpen_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint`,
`TauCeti.dense_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint`). -/
theorem mem_residual_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint {k : ℕ}
    (hk : 2 ≤ k) :
    {f : C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ | ∀ x ∈ criticalPoints 𝓘(ℝ, E) f,
        IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x} ∈
      residual C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ := by
  have hk' : (2 : WithTop ℕ∞) ≤ k := by exact_mod_cast hk
  simpa only [isRegularSectionParameter_universalDifferential_iff hk'] using
    mem_residual_setOf_isRegularSectionParameter_universalDifferential (E := E) (M := M) hk

end TauCeti
