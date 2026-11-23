/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IsManifold.Prod
public import TauCeti.Geometry.Manifold.Morse.Generic.Universal.Differential
public import TauCeti.Geometry.Manifold.VectorBundle.Section.SmoothZero
import Mathlib.Topology.Algebra.Module.Equiv.Submodule
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Banach
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# The universal zero manifold of the universal differential

Let `M` be a Hausdorff manifold without boundary modelled on a finite-dimensional real space `E`,
covered by finitely many compact chart pieces, and let `k ≥ 2`. Give the `C^k` functions on `M`
the norm of that finite atlas (`ContMDiffMap.finiteAtlasNormedAddCommGroup`), so that they form a
Banach space `C^k(M, ℝ)`. The **universal zero set**

`Z = {(x, f) ∈ M × C^k(M, ℝ) | df_x = 0}`

of the universal differential `S(x, f) = df_x` (`TauCeti.universalDifferential`) collects the
critical points of all `C^k` functions at once. This file shows that `Z` is a `C^(k - 1)` Banach
manifold and compares the derivative of its projection `π(x, f) = f` to the space of functions
with the parameter projection of the universal linearization.

**The zero manifold.** At a zero `(x, f)` the linearization of `S` is
`L(v, h) = Hess_x f (v) + dh_x` (`TauCeti.sectionLinearization_universalDifferential_apply`). It is
onto, already on the function directions, and its kernel is complemented, since its target
`T*_x M` is finite-dimensional. The kernel is infinite-dimensional, so `S` is not Fredholm, but
all these kernels are isomorphic to `C^k(M, ℝ)` itself. Indeed `h ↦ dh_x` has the continuous linear
right inverse `ξ ↦ β ξ` given by bump functions (`ContMDiffMap.mvfderivCLM_comp_bumpCovectorCLM`),
so `ker L ≃ T_x M × ker (h ↦ dh_x)`
(`ContinuousLinearMap.kerCoprodEquivOfRightInverse`) and
`C^k(M, ℝ) ≃ T*_x M × ker (h ↦ dh_x)` (`ContinuousLinearEquiv.equivOfRightInverse`), while `T_x M`
and `T*_x M` have the same finite dimension
(`TauCeti.nonempty_continuousLinearEquiv_ker_criticalHessian_coprod_mvfderivCLM`). The atlas of
regular zeros of sections with complemented kernels,
`TauCeti.exists_isManifold_sectionZero_of_contMDiff_of_closedComplemented`, applied with the model
`C^k(M, ℝ)`, then makes `Z` a `C^(k - 1)` manifold modelled on `C^k(M, ℝ)`, embedded in
`M × C^k(M, ℝ)` by a `C^(k - 1)` immersion whose tangent image at `(x, f)` is `ker L`
(`TauCeti.exists_isManifold_sectionZero_universalDifferential`). Here `M × C^k(M, ℝ)` carries the
product charts with values in `E × C^k(M, ℝ)` (`TauCeti.chartedSpaceProd`), for the model
`𝓘(ℝ, E × C^k(M, ℝ))` that the atlas theorem uses.

**The parameter projection.** For any charted-space structure on `Z` modelled on `C^k(M, ℝ)` whose
inclusion has injective derivative at `(x, f)` with image `ker L`, as for the manifold structure
above, the derivative of the projection `π(x, f) = f` at `(x, f)` is the parameter projection of the
universal linearization,
`ContinuousLinearMap.parameterProj (Hess_x f) (h ↦ dh_x)`, read through a continuous linear
isomorphism of the model `C^k(M, ℝ)` with `ker L`
(`TauCeti.exists_mfderiv_snd_eq_parameterProj_comp_universalDifferential`). Hence it is Fredholm of
index zero (`TauCeti.isFredholm_mfderiv_snd_universalDifferential`,
`TauCeti.index_mfderiv_snd_universalDifferential`), and it is onto exactly when `x` is a
nondegenerate critical point of `f`
(`TauCeti.surjective_mfderiv_snd_universalDifferential_iff`). So the regular values of `π` are
exactly the `C^k` functions all of whose critical points are nondegenerate, the residual set of
`TauCeti.mem_residual_setOf_forall_mem_criticalPoints_isManifoldNondegenerateCriticalPoint`.

## Main results

* `TauCeti.nonempty_continuousLinearEquiv_ker_criticalHessian_coprod_mvfderivCLM`: every kernel of
  the universal linearization is isomorphic to `C^k(M, ℝ)`.
* `TauCeti.exists_isManifold_sectionZero_universalDifferential`: the universal zero set is a
  `C^(k - 1)` manifold modelled on `C^k(M, ℝ)`, immersed in `M × C^k(M, ℝ)` with tangent image the
  kernel of the universal linearization, and its projection to `C^k(M, ℝ)` is `C^(k - 1)`.
* `TauCeti.exists_mfderiv_snd_eq_parameterProj_comp_universalDifferential`: the derivative of the
  projection is the parameter projection, up to an isomorphism of its source.
* `TauCeti.isFredholm_mfderiv_snd_universalDifferential`,
  `TauCeti.index_mfderiv_snd_universalDifferential`: the projection is Fredholm of index zero.
* `TauCeti.surjective_mfderiv_snd_universalDifferential_iff`: its derivative at `(x, f)` is onto
  exactly when `x` is a nondegenerate critical point of `f`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications **52**, 2012, Appendix A.3 (the universal moduli space and the Fredholm projection
  to the parameter space, proof of Theorem A.3.6).
* S. Lang, *Fundamentals of Differential Geometry*, Graduate Texts in Mathematics 191, Springer,
  1999, Chapter II, §2 (submanifolds cut out by maps with surjective derivative and split kernel).
* M. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976, Chapter 6,
  §1 (genericity of Morse functions).
-/

public section

open Bundle Function Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {ι : Type*} [Fintype ι] {c : ι → M}
  {K : ∀ i, TopologicalSpace.Compacts (extChartAt 𝓘(ℝ, E) (c i)).target}
  (k : ℕ)
  (hK : ∀ y : M, ∃ i, ∃ hy : y ∈ (extChartAt 𝓘(ℝ, E) (c i)).source,
    (⟨extChartAt 𝓘(ℝ, E) (c i) y, (extChartAt 𝓘(ℝ, E) (c i)).map_source hy⟩ :
      (extChartAt 𝓘(ℝ, E) (c i)).target) ∈ interior (K i : Set (extChartAt 𝓘(ℝ, E) (c i)).target))

attribute [local instance] chartedSpaceProd

include hK in
/-- For the product charts of `M × C^k(M, ℝ)` with values in `E × C^k(M, ℝ)`, the linearization of
the universal differential at `(x, f)` is `(v, h) ↦ Hess_x f (v) + dh_x`. -/
private theorem sectionLinearization_universalDifferential_eq_coprod (hk : 2 ≤ k)
    (z : M × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) :
    letI := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
    letI := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
    sectionLinearization (F := E →L[ℝ] ℝ) (E := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ)
        𝓘(ℝ, E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) Prod.fst (universalDifferential 𝓘(ℝ, E)) z =
      (criticalHessian 𝓘(ℝ, E) z.2 z.1).coprod
        (ContMDiffMap.mvfderivCLM (F := ℝ) (n := k) (by exact_mod_cast one_le_two.trans hk)
          z.1) := by
  let := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
  let := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
  have h := sectionLinearization_universalDifferential_apply k hK hk z
  rw [← modelWithCornersSelf_prod] at h
  refine ContinuousLinearMap.ext fun p ↦ (h p).trans ?_
  exact ((ContinuousLinearMap.coprod_apply (R := ℝ) _ _ p).trans
    (congrArg _ (ContMDiffMap.mvfderivCLM_apply _ _ _))).symm

variable [T2Space M]

include hK in
/-- **The kernels of the universal linearization all model `C^k(M, ℝ)`.** For `k ≥ 1`, every
`x : M` and every `C^k` function `f`, the kernel of `(v, h) ↦ Hess_x f (v) + dh_x` is
isomorphic to `C^k(M, ℝ)`. Bump functions give a continuous linear right inverse of
`h ↦ dh_x`, so the kernel is `T_x M × ker (h ↦ dh_x)` and `C^k(M, ℝ)` is
`T*_x M × ker (h ↦ dh_x)`, while `T_x M` and `T*_x M` have the same finite dimension. -/
theorem nonempty_continuousLinearEquiv_ker_criticalHessian_coprod_mvfderivCLM (hk : 1 ≤ k)
    (x : M) (f : C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) :
    letI := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
    letI := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
    Nonempty (((criticalHessian 𝓘(ℝ, E) f x).coprod
        (ContMDiffMap.mvfderivCLM (F := ℝ) (n := k) (by exact_mod_cast hk) x)).ker ≃L[ℝ]
      C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) := by
  let := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
  let := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
  have hσ := ContMDiffMap.mvfderivCLM_comp_bumpCovectorCLM (F := ℝ) (n := k)
    (by exact_mod_cast hk) (Classical.arbitrary (SmoothBumpFunction 𝓘(ℝ, E) x))
  have hdual : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.dual_finrank_eq (𝕜 := ℝ) (E := E)).symm
  exact ⟨(ContinuousLinearMap.kerCoprodEquivOfRightInverse _ _
    (fun ξ ↦ congrArg (· ξ) hσ)).trans
    (((ContinuousLinearEquiv.ofFinrankEq hdual).prodCongr
      (ContinuousLinearEquiv.refl ℝ _)).trans
      (ContinuousLinearEquiv.equivOfRightInverse _ _ (fun ξ ↦ congrArg (· ξ) hσ)).symm)⟩

include hK in
/-- **The universal zero manifold.** For `k ≥ 2`, the zero set `{(x, f) | df_x = 0}` of the
universal differential on `M × C^k(M, ℝ)` is a `C^(k - 1)` manifold modelled on the Banach space
`C^k(M, ℝ)` of `C^k` functions with a finite-atlas norm. Its inclusion into `M × C^k(M, ℝ)`, with
the product charts, is a `C^(k - 1)` immersion whose tangent image at `(x, f)` is the kernel of the
universal linearization `(v, h) ↦ Hess_x f (v) + dh_x`, and its projection `(x, f) ↦ f` to
`C^k(M, ℝ)` is `C^(k - 1)`. -/
theorem exists_isManifold_sectionZero_universalDifferential (hk : 2 ≤ k) :
    letI := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
    letI := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
    ∃ cs : ChartedSpace C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯
        ↥{z : M × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ | universalDifferential 𝓘(ℝ, E) z = 0},
      letI := cs
      IsManifold 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) ((k - 1 : ℕ) : ℕ∞ω)
          ↥{z : M × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ | universalDifferential 𝓘(ℝ, E) z = 0} ∧
        Manifold.IsImmersionOfComplement (E →L[ℝ] ℝ) 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
          𝓘(ℝ, E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) ((k - 1 : ℕ) : ℕ∞ω)
          (Subtype.val : ↥{z : M × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ |
            universalDifferential 𝓘(ℝ, E) z = 0} → M × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) ∧
        (∀ z : ↥{z : M × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ | universalDifferential 𝓘(ℝ, E) z = 0},
          (mfderiv 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) 𝓘(ℝ, E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
            Subtype.val z).range =
            ((criticalHessian 𝓘(ℝ, E) z.val.2 z.val.1).coprod
              (ContMDiffMap.mvfderivCLM (F := ℝ) (n := k) (by exact_mod_cast one_le_two.trans hk)
                z.val.1)).ker) ∧
        ContMDiff 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
          ((k - 1 : ℕ) : ℕ∞ω)
          (fun z : ↥{z : M × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ |
            universalDifferential 𝓘(ℝ, E) z = 0} ↦ z.val.2) := by
  let := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
  let := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
  have := ContMDiffMap.completeSpace_finiteAtlas (F := ℝ) k hK
  have hm : ((k - 1 : ℕ) : ℕ∞ω) ≠ 0 := by norm_cast; omega
  have : IsManifold 𝓘(ℝ, E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) ((k - 1 : ℕ) : ℕ∞ω)
      (M × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) := isManifold_chartedSpaceProd
  -- The universal differential is `C^(k - 1)` for the product model, hence for its self model.
  have hcont := contMDiff_universalDifferential (I := 𝓘(ℝ, E)) k hK (m := ((k - 1 : ℕ) : ℕ∞ω))
    (by norm_cast; omega)
  rw [← modelWithCornersSelf_prod] at hcont
  have hL := sectionLinearization_universalDifferential_eq_coprod k hK hk
  obtain ⟨cs, hZ, hval, hrange⟩ :=
    exists_isManifold_sectionZero_of_contMDiff_of_closedComplemented
      (Y := C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) hm (fun z _ ↦ hcont z)
      (fun z _ ↦ hL z ▸ surjective_criticalHessian_coprod_mvfderivCLM _ _ _)
      (fun z _ ↦ ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range _)
      (fun z _ ↦ hL z ▸
        nonempty_continuousLinearEquiv_ker_criticalHessian_coprod_mvfderivCLM k hK
          (one_le_two.trans hk) z.1 z.2)
  let := cs
  -- The projection is the second factor of the inclusion.
  have hsnd : ContMDiff 𝓘(ℝ, E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
      ((k - 1 : ℕ) : ℕ∞ω) (Prod.snd : M × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ → _) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  exact ⟨cs, hZ, hval, fun z ↦ (hrange z).trans (congrArg (fun L : _ →L[ℝ] _ ↦ L.ker) (hL z)),
    hsnd.comp hval.contMDiff⟩

omit [T2Space M] in
include hK in
/-- **The projection of the universal zero manifold is the parameter projection.** For `k ≥ 1`,
let the universal zero set `{(x, f) | df_x = 0}` carry a charted-space structure modelled on
`C^k(M, ℝ)`, and let `(x, f)` be a point at which the derivative of its inclusion into
`M × C^k(M, ℝ)` is injective with range the kernel of the universal linearization, as holds at every
point for the manifold structure of `TauCeti.exists_isManifold_sectionZero_universalDifferential`.
Then the derivative at `(x, f)` of the projection `(x, f) ↦ f` is the parameter projection of
`(v, h) ↦ Hess_x f (v) + dh_x`, composed with a continuous linear isomorphism of the model onto
the kernel of that map. -/
theorem exists_mfderiv_snd_eq_parameterProj_comp_universalDifferential (hk : 1 ≤ k) :
    letI := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
    letI := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
    ∀ (cs : ChartedSpace C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯
        ↥{z : M × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ | universalDifferential 𝓘(ℝ, E) z = 0})
      (z : ↥{z : M × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ | universalDifferential 𝓘(ℝ, E) z = 0}),
      letI := cs
      Injective (mfderiv 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) 𝓘(ℝ, E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
          Subtype.val z) →
        (mfderiv 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) 𝓘(ℝ, E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
            Subtype.val z).range =
          ((criticalHessian 𝓘(ℝ, E) z.val.2 z.val.1).coprod
            (ContMDiffMap.mvfderivCLM (F := ℝ) (n := k) (by exact_mod_cast hk)
              z.val.1)).ker →
        ∃ T : C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ ≃L[ℝ] ((criticalHessian 𝓘(ℝ, E) z.val.2 z.val.1).coprod
            (ContMDiffMap.mvfderivCLM (F := ℝ) (n := k) (by exact_mod_cast hk)
              z.val.1)).ker,
          mfderiv 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
            (fun z ↦ z.val.2) z =
            ContinuousLinearMap.parameterProj (criticalHessian 𝓘(ℝ, E) z.val.2 z.val.1)
              (ContMDiffMap.mvfderivCLM (F := ℝ) (n := k) (by exact_mod_cast hk)
                z.val.1) ∘L (T : C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ →L[ℝ] _) := by
  let := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
  let := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
  have := ContMDiffMap.completeSpace_finiteAtlas (F := ℝ) k hK
  intro cs z hinj hrange
  set L : E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ →L[ℝ] E →L[ℝ] ℝ :=
    (criticalHessian 𝓘(ℝ, E) z.val.2 z.val.1).coprod
      (ContMDiffMap.mvfderivCLM (F := ℝ) (n := k) (by exact_mod_cast hk) z.val.1)
  set D : C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ →L[ℝ] E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ :=
    mfderiv 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) 𝓘(ℝ, E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) Subtype.val z
  -- The derivative `D` of the inclusion is injective with closed range `ker L`, so it is an
  -- isomorphism onto `ker L` by the open mapping theorem.
  have hR : (D : C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ →ₗ[ℝ] E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯).range =
      (L : E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ →ₗ[ℝ] E →L[ℝ] ℝ).ker := hrange
  have hclo : IsClosed (range D) := by
    rw [← ContinuousLinearMap.coe_coe, ← LinearMap.coe_range, hR]
    exact L.isClosed_ker
  let T := (D.equivRange hinj hclo).trans (ContinuousLinearEquiv.ofEq _ _ hR)
  refine ⟨T, ?_⟩
  -- By the chain rule the derivative of the projection is the second component of `D`.
  have hd : MDifferentiableAt 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
      𝓘(ℝ, E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) Subtype.val z :=
    mdifferentiableAt_of_mfderiv_injective hinj
  have hsd : MDifferentiableAt 𝓘(ℝ, E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
      𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) Prod.snd z.val := by
    rw [modelWithCornersSelf_prod]
    exact mdifferentiableAt_snd
  have hsnd : mfderiv 𝓘(ℝ, E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
      Prod.snd z.val = ContinuousLinearMap.snd ℝ E C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ := by
    rw [modelWithCornersSelf_prod]
    exact mfderiv_snd
  refine (mfderiv_comp (I' := 𝓘(ℝ, E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)) z hsd hd).trans ?_
  rw [hsnd]
  -- Both sides send `v` to the second component of `D v`.
  have hT (v : C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) : (T v : E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) = D v := by
    rw [ContinuousLinearEquiv.trans_apply]
    -- `ContinuousLinearEquiv.ofEq` is `LinearEquiv.ofEq` with continuity proofs attached.
    exact (LinearEquiv.coe_ofEq_apply hR _).trans
      ((congrArg Subtype.val (congrFun (D.coe_equivRange hinj hclo) v)).trans
        (D.coe_codRestrict_apply _ _ v))
  -- The tangent spaces of the models are the models, and `comp` applies definitionally.
  refine ContinuousLinearMap.ext fun v ↦ ?_
  exact ((ContinuousLinearMap.parameterProj_apply _ _ (T v)).trans
    (congrArg Prod.snd (hT v))).symm

omit [T2Space M] in
include hK in
/-- **The projection of the universal zero manifold is Fredholm.** At any point of the universal
zero set where its inclusion has injective derivative with range the kernel of the universal
linearization, as in `TauCeti.exists_mfderiv_snd_eq_parameterProj_comp_universalDifferential`, the
derivative of the projection `(x, f) ↦ f` is a Fredholm operator. -/
theorem isFredholm_mfderiv_snd_universalDifferential (hk : 1 ≤ k) :
    letI := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
    letI := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
    ∀ (cs : ChartedSpace C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯
        ↥{z : M × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ | universalDifferential 𝓘(ℝ, E) z = 0})
      (z : ↥{z : M × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ | universalDifferential 𝓘(ℝ, E) z = 0}),
      letI := cs
      Injective (mfderiv 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) 𝓘(ℝ, E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
          Subtype.val z) →
        (mfderiv 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) 𝓘(ℝ, E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
            Subtype.val z).range =
          ((criticalHessian 𝓘(ℝ, E) z.val.2 z.val.1).coprod
            (ContMDiffMap.mvfderivCLM (F := ℝ) (n := k) (by exact_mod_cast hk)
              z.val.1)).ker →
        (mfderiv 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
          (fun z ↦ z.val.2) z).IsFredholm := by
  let := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
  let := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
  intro cs z hinj hrange
  obtain ⟨T, hT⟩ :=
    exists_mfderiv_snd_eq_parameterProj_comp_universalDifferential k hK hk cs z hinj hrange
  rw [hT]
  -- The parameter projection is Fredholm because the critical Hessian, a map between
  -- finite-dimensional spaces, is.
  exact ContinuousLinearMap.isFredholm_comp_equiv.2 (ContinuousLinearMap.isFredholm_parameterProj
    _ _ (ContinuousLinearMap.isFredholm_of_finiteDimensional _))

include hK in
/-- **The projection of the universal zero manifold has index zero.** At any point of the
universal zero set where its inclusion has injective derivative with range the kernel of the
universal linearization, as in
`TauCeti.exists_mfderiv_snd_eq_parameterProj_comp_universalDifferential`, the derivative of the
projection `(x, f) ↦ f` has Fredholm index zero. -/
theorem index_mfderiv_snd_universalDifferential (hk : 1 ≤ k) :
    letI := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
    letI := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
    ∀ (cs : ChartedSpace C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯
        ↥{z : M × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ | universalDifferential 𝓘(ℝ, E) z = 0})
      (z : ↥{z : M × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ | universalDifferential 𝓘(ℝ, E) z = 0}),
      letI := cs
      Injective (mfderiv 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) 𝓘(ℝ, E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
          Subtype.val z) →
        (mfderiv 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) 𝓘(ℝ, E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
            Subtype.val z).range =
          ((criticalHessian 𝓘(ℝ, E) z.val.2 z.val.1).coprod
            (ContMDiffMap.mvfderivCLM (F := ℝ) (n := k) (by exact_mod_cast hk)
              z.val.1)).ker →
        ContinuousLinearMap.index
          (mfderiv 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
            (fun z ↦ z.val.2) z) = 0 := by
  let := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
  let := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
  intro cs z hinj hrange
  obtain ⟨T, hT⟩ :=
    exists_mfderiv_snd_eq_parameterProj_comp_universalDifferential k hK hk cs z hinj hrange
  rw [hT]
  exact (ContinuousLinearMap.index_comp_equiv _ _).trans
    (index_parameterProj_criticalHessian_mvfderivCLM _ _ _)

include hK in
/-- **The regular points of the projection are the nondegenerate critical points.** At any point
`(x, f)` of the universal zero set where its inclusion has injective derivative with range the
kernel of the universal linearization, as in
`TauCeti.exists_mfderiv_snd_eq_parameterProj_comp_universalDifferential`, the derivative of the
projection `(x, f) ↦ f` at `(x, f)` is onto exactly when `x` is a nondegenerate critical point of
`f`. So for the manifold structure of `TauCeti.exists_isManifold_sectionZero_universalDifferential`,
a `C^k` function is a regular value of the projection exactly when all of its critical points are
nondegenerate. -/
theorem surjective_mfderiv_snd_universalDifferential_iff (hk : 2 ≤ k) :
    letI := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
    letI := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
    ∀ (cs : ChartedSpace C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯
        ↥{z : M × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ | universalDifferential 𝓘(ℝ, E) z = 0})
      (z : ↥{z : M × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯ | universalDifferential 𝓘(ℝ, E) z = 0}),
      letI := cs
      Injective (mfderiv 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) 𝓘(ℝ, E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
          Subtype.val z) →
        (mfderiv 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) 𝓘(ℝ, E × C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
            Subtype.val z).range =
          ((criticalHessian 𝓘(ℝ, E) z.val.2 z.val.1).coprod
            (ContMDiffMap.mvfderivCLM (F := ℝ) (n := k) (by exact_mod_cast one_le_two.trans hk)
              z.val.1)).ker →
        (Surjective (mfderiv 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) 𝓘(ℝ, C^k⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯)
            (fun z ↦ z.val.2) z) ↔
          IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) z.val.2 z.val.1) := by
  let := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
  let := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
  intro cs z hinj hrange
  obtain ⟨T, hT⟩ :=
    exists_mfderiv_snd_eq_parameterProj_comp_universalDifferential k hK (one_le_two.trans hk) cs z
      hinj hrange
  rw [hT]
  exact (Surjective.of_comp_iff _ T.surjective).trans
    (surjective_parameterProj_criticalHessian_mvfderivCLM_iff (n := k) (by exact_mod_cast hk)
      (universalDifferential_eq_zero_iff.1 z.property))

end TauCeti
