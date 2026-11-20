/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Generic.Universal.Differential
import TauCeti.Analysis.Fredholm.Basic
import TauCeti.Analysis.Normed.Module.FiniteDimension
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Banach

/-!
# Genericity of Morse functions by the Sard–Smale theorem

Let `M` be a compact manifold modelled on a finite-dimensional real space `E`, and let `k ≥ 2`.
Give the `C^k` functions on `M` the norm of a finite chart atlas, so that they form a Banach
space. The universal differential `S(x, h) = dh_x` (`TauCeti.universalDifferential`) is then a
`C^(k - 1)` section of the cotangent bundle along `M × C^k(M, ℝ) → M`.

This file perturbs a fixed `C^k` function `f` along a continuous linear family
`T : Λ →L[ℝ] C^k(M, ℝ)` on a separable Banach space `Λ`, and pulls `S` back to the section
`(x, l) ↦ d(f + T l)_x` along `M × Λ → M`. If the differentials of the functions `T l` at each
point `x` realize every covector at `x`, this section is transverse to the zero section, already in
the parameter directions. For a fixed parameter its linearization in the point maps `T_x M` to
`T*_x M`, so it is Fredholm of index zero, and Smale's threshold `k - 1 > max (0, 0)` holds exactly
when `k ≥ 2`. Parametric transversality for Fredholm sections
(`TauCeti.mem_residual_setOf_isRegularSectionParameter`) then shows that the regular parameters form
a residual set, and a parameter `l` is regular exactly when all critical points of `f + T l` are
nondegenerate (`TauCeti.isRegularSectionParameter_universalDifferential_iff`).

Two families are of interest. The identity of the Banach space of `C^k` functions realizes every
covector by `ContMDiffMap.surjective_mvfderivCLM`; for it the theorem says that the `C^k` functions
with only nondegenerate critical points form a residual set, which also follows from the openness
theorem
`TauCeti.isOpen_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint` and the
density theorem
`TauCeti.dense_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint`. Finitely
many functions whose differentials span every cotangent space give the other: for a residual set
of coefficients `a`, the function `f + ∑ i, a i • g i` has only nondegenerate critical points. This
is the manifold form of the linear perturbations of
`TauCeti.dense_setOfPred_hasNondegenerateCriticalPointsOn_sub`, and it is not a consequence of
genericity in the space of all `C^k` functions.

## Main results

* `mem_residual_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint_add`: for a
  continuous linear family `T` of `C^k` functions, `k ≥ 2`, whose differentials realize every
  covector, `f + T l` has only nondegenerate critical points for a residual set of `l`.
* `mem_residual_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint_add_sum`: the
  same for the finite linear family `a ↦ ∑ i, a i • g i`, when the differentials of the `g i`
  span every cotangent space.

## References

* S. Smale, *An infinite dimensional version of Sard's theorem*, Amer. J. Math. 87 (1965),
  861--866.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications **52**, 2012, Appendix A.3 (universal sections and their regular parameters).
* M. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976, Chapter 6,
  §1 (genericity of Morse functions).
* V. Guillemin and A. Pollack, *Differential Topology*, Prentice-Hall, 1974, Chapter 1, §7
  (Morse functions from linear perturbations).
-/

public section

open Bundle Function Set Filter
open scoped Manifold ContDiff Topology TauCeti.ManifoldWeakWhitney

namespace TauCeti

variable {E M Λ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M] {k : ℕ}

/-- **Morse functions along a family of perturbations, by Sard–Smale.** On a compact manifold
modelled on a finite-dimensional space, let `k ≥ 2`, let `f` be a `C^k`
function, and let `T` be a continuous linear map from a separable Banach space `Λ` to the `C^k`
functions whose differentials at each point `x` realize every covector at `x`. Then for a residual
set of parameters `l`, all critical points of `f + T l` are nondegenerate. -/
theorem mem_residual_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint_add
    [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [CompleteSpace Λ] [SecondCountableTopology Λ]
    [IsManifold 𝓘(ℝ, E) k M] (hk : 2 ≤ k) (f : C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
    (T : Λ →L[ℝ] C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
    (hT : ∀ (x : M) (ξ : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ), ∃ l, mvfderiv 𝓘(ℝ, E) (T l) x = ξ) :
    {l : Λ | ∀ x ∈ criticalPoints 𝓘(ℝ, E) (f + T l),
      IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) (f + T l) x} ∈ residual Λ := by
  -- Give the `C^k` functions the norm of a finite chart atlas. It induces the weak Whitney
  -- topology, so `T` stays continuous, and makes the universal differential `C^(k - 1)`.
  obtain ⟨N, c, K, hK⟩ := exists_finite_compact_chart_cover (I := 𝓘(ℝ, E)) (M := M)
  let := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
  let := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
  have := ChartedSpace.secondCountable_of_sigmaCompact E M
  have : IsManifold 𝓘(ℝ, E) 1 M := .of_le (n := k) (by exact_mod_cast one_le_two.trans hk)
  have hm : ((k - 1 : ℕ) : WithTop ℕ∞) + 1 ≤ k := by
    have : k - 1 + 1 = k := by omega
    exact_mod_cast this.le
  -- Pull the universal differential back along `Φ (x, l) = (x, f + T l)`.
  let Φ : M × Λ → M × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ := fun z ↦ (z.1, f + T z.2)
  have hΦ (z : M × Λ) : HasMFDerivAt (𝓘(ℝ, E).prod 𝓘(ℝ, Λ))
      (𝓘(ℝ, E).prod 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)) Φ z
      ((ContinuousLinearMap.fst ℝ E Λ).prod (T.comp (ContinuousLinearMap.snd ℝ E Λ))) :=
    (hasMFDerivAt_fst z).prodMk ((T.hasFDerivAt.const_add f).hasMFDerivAt.comp z
      (hasMFDerivAt_snd z))
  have hΦc : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Λ)) (𝓘(ℝ, E).prod 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯))
      ((k - 1 : ℕ) : WithTop ℕ∞) Φ :=
    contMDiff_fst.prodMk ((contDiff_const.add T.contDiff).contMDiff.comp contMDiff_snd)
  have h := mem_residual_setOf_isRegularSectionParameter (X := E) (F := E →L[ℝ] ℝ)
    (E := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) (I := 𝓘(ℝ, E)) (b := Prod.fst ∘ Φ)
    (s := fun z ↦ universalDifferential 𝓘(ℝ, E) (Φ z)) (n := ((k - 1 : ℕ) : WithTop ℕ∞))
    (fun z _ ↦ ((contMDiff_universalDifferential k hK hm).comp hΦc).contMDiffAt)
    (fun _ _ ↦ ContinuousLinearMap.isFredholm_of_finiteDimensional _)
    (fun z _ ↦ ?_) (fun z _ ↦ ?_)
  · -- A regular parameter is one for which `f + T l` has only nondegenerate critical points.
    have : IsManifold 𝓘(ℝ, E) 2 M := .of_le (n := k) (by exact_mod_cast hk)
    filter_upwards [h] with l hl
    rw [← isRegularSectionParameter_universalDifferential_iff
      (show (2 : WithTop ℕ∞) ≤ k by exact_mod_cast hk)]
    simpa only [isRegularSectionParameter_iff, Φ, Function.comp_apply] using hl
  · -- The total linearization is onto, already on the parameter directions.
    rw [sectionLinearization_comp (hΦ z).mdifferentiableAt
      (mdifferentiableAt_trivializationAt_universalDifferential k hK hk (Φ z)), (hΦ z).mfderiv]
    intro ξ
    obtain ⟨l, hl⟩ := hT z.1 ξ
    refine ⟨((0 : E), l), ?_⟩
    -- On `(0, T l)` the linearization of the universal differential is `d(T l)`. The zero
    -- point direction is a vector of `E`, so `map_zero` is stated at that type.
    have hH : criticalHessian 𝓘(ℝ, E) (Φ z).2 (Φ z).1 (0 : E) = 0 := map_zero _
    have h0 := sectionLinearization_universalDifferential_apply k hK hk (Φ z) ((0 : E), T l)
    dsimp only at h0
    rw [hH, zero_add] at h0
    -- The derivative of `Φ` sends `(0, l)` to `(0, T l)` by unfolding `comp` and `prod`. The
    -- tangent spaces of the products are `E × Λ` and `E × C^k(M, ℝ)` only by definition, so
    -- `rw` and `simp` cannot rewrite the goal, and the unfolding is left to `exact`.
    exact h0.trans hl
  · -- The linearization in the point maps `T_x M` to its dual, so it has index zero.
    rw [index_sectionLinearization_of_finiteDimensional,
      ContinuousLinearMap.dual_finrank_eq (𝕜 := ℝ) (E := E), sub_self]
    exact_mod_cast Nat.le_sub_of_add_le hk

/-- **Morse functions along a finite linear family, by Sard–Smale.** On a compact manifold
modelled on a finite-dimensional space, let `k ≥ 2`, let `f` be a `C^k` function, and let `g` be
finitely many `C^k` functions whose differentials span the cotangent space at every point. Then
for a residual set of coefficients `a`, all critical points of `f + ∑ i, a i • g i` are
nondegenerate. -/
theorem mem_residual_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint_add_sum
    {ι : Type*} [Fintype ι] [IsManifold 𝓘(ℝ, E) k M] (hk : 2 ≤ k)
    (f : C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) (g : ι → C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
    (hg : ∀ x : M, Submodule.span ℝ (range fun i ↦ mvfderiv 𝓘(ℝ, E) (g i) x) = ⊤) :
    {a : ι → ℝ | ∀ x ∈ criticalPoints 𝓘(ℝ, E) (f + ∑ i, a i • g i),
      IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) (f + ∑ i, a i • g i) x} ∈ residual (ι → ℝ) := by
  have h1 : 1 ≤ ((k : ℕ∞) : ℕ∞ω) := by exact_mod_cast one_le_two.trans hk
  let T : (ι → ℝ) →L[ℝ] C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ :=
    ∑ i, (ContinuousLinearMap.proj i).smulRight (g i)
  have hT (a : ι → ℝ) : T a = ∑ i, a i • g i := by simp [T]
  simpa only [hT] using
    mem_residual_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint_add hk f T
      fun x ξ ↦ by
        -- Every covector is a combination of the differentials of the `g i`.
        obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1
          ((hg x).symm ▸ Submodule.mem_top (x := ξ))
        refine ⟨a, ?_⟩
        rw [← ContMDiffMap.mvfderivCLM_apply h1, hT, map_sum]
        simpa only [map_smul, ContMDiffMap.mvfderivCLM_apply] using ha

end TauCeti
