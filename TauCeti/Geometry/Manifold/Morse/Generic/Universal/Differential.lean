/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.SmoothEvaluation
public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.Morse.Generic.Universal.Linearization
public import TauCeti.Geometry.Manifold.Morse.Linearization
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Parametric

/-!
# The universal differential

On a manifold `M` without boundary, the **universal differential** is the section
`S(x, f) = df_x` of the cotangent bundle along the projection `M × C^k(M, ℝ) → M`
(`TauCeti.universalDifferential`). Its zeros are the pairs `(x, f)` with `x` a critical point of
`f`, and a function is a regular parameter of `S` exactly when its critical points are
nondegenerate. Genericity of such functions is then an instance of parametric transversality for
Fredholm sections (`TauCeti.isMeagre_setOf_not_isRegularSectionParameter`). This file establishes
the regularity, linearization and transversality of `S` that this application uses; the
application itself is `TauCeti.mem_residual_setOf_isRegularSectionParameter_universalDifferential`.

* The differential `df` of a single function, read as a section of the cotangent bundle, has
  intrinsic linearization the critical Hessian, which is onto exactly at nondegenerate critical
  points; this is `TauCeti.Geometry.Manifold.Morse.Linearization`.
* For the norm of a finite chart atlas on the `C^k` functions
  (`ContMDiffMap.finiteAtlasNormedAddCommGroup`), `S` is `C^m` whenever `m + 1 ≤ k`
  (`TauCeti.contMDiff_universalDifferential`). This rests on the joint regularity of evaluation,
  `ContMDiffMap.contMDiff_eval_finiteAtlas`.
* For `k ≥ 2`, the intrinsic linearization of `S` at `(x, f)` is
  `(v, h) ↦ Hess_x f (v) + dh_x` (`TauCeti.sectionLinearization_universalDifferential_apply`),
  the linear map of `TauCeti.surjective_criticalHessian_coprod_mvfderivCLM`. It is onto, already
  on the function directions (`TauCeti.surjective_sectionLinearization_universalDifferential`), so
  `S` is transverse to the zero section.
* On a manifold modelled on `E`, the regular parameters of `S` are the `C^n` functions all of whose
  critical points are nondegenerate
  (`TauCeti.isRegularSectionParameter_universalDifferential_iff`).

## References

* M. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976, Chapter 6,
  §1 (genericity of Morse functions).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications **52**, 2012, Appendix A.3 (universal sections and their regular parameters).
-/

public section

open Bundle Function Set Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

section Universal

variable (I) in
/-- The **universal differential** `S(x, f) = df_x`. It is the section of the cotangent bundle of
`M` along the projection `M × C^n(M, ℝ) → M` which records the differentials of all `C^n`
functions at once. Its zeros are the pairs `(x, f)` with `x` a critical point of `f`. -/
noncomputable def universalDifferential {n : WithTop ℕ∞} (z : M × C^n⟮I, M; 𝓘(ℝ), ℝ⟯) :
    TangentSpace I z.1 →L[ℝ] ℝ :=
  mvfderiv I z.2 z.1

/-- The universal differential at `(x, f)` is the differential of `f` at `x`. -/
@[simp]
theorem universalDifferential_apply {n : WithTop ℕ∞} (z : M × C^n⟮I, M; 𝓘(ℝ), ℝ⟯) :
    universalDifferential I z = mvfderiv I z.2 z.1 :=
  (rfl)

/-- The zeros of the universal differential are the pairs `(x, f)` with `x` a critical point
of `f`. -/
theorem universalDifferential_eq_zero_iff {n : WithTop ℕ∞} {z : M × C^n⟮I, M; 𝓘(ℝ), ℝ⟯} :
    universalDifferential I z = 0 ↔ z.1 ∈ criticalPoints I z.2 :=
  mem_criticalPoints.symm

variable [LocallyCompactSpace E] [I.Boundaryless]
  {ι : Type*} [Fintype ι] {c : ι → M}
  {K : ∀ i, TopologicalSpace.Compacts (extChartAt I (c i)).target}
  (k : ℕ)
  (hK : ∀ y : M, ∃ i, ∃ hy : y ∈ (extChartAt I (c i)).source,
    (⟨extChartAt I (c i) y, (extChartAt I (c i)).map_source hy⟩ :
      (extChartAt I (c i)).target) ∈ interior (K i : Set (extChartAt I (c i)).target))

section FiniteRegularity

variable [IsManifold I k M] [IsManifold I 1 M]

include hK in
/-- **The universal differential is `C^(k - 1)`.** Give the `C^k` functions on `M` the norm of a
finite chart atlas whose compact pieces have relative interiors covering `M`. Then the universal
differential `(x, f) ↦ df_x` is a `C^m` map from `M × C^k(M, ℝ)` to the cotangent bundle for every
`m` with `m + 1 ≤ k`. -/
theorem contMDiff_universalDifferential {m : WithTop ℕ∞} (hm : m + 1 ≤ k) :
    letI := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
    letI := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
    ContMDiff (I.prod 𝓘(ℝ, C^k⟮I, M; 𝓘(ℝ), ℝ⟯)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) m
      (fun z : M × C^k⟮I, M; 𝓘(ℝ), ℝ⟯ ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) z.1 (universalDifferential I z)) := by
  let := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
  let := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
  -- Evaluation `(f, x) ↦ f x` is `C^k`, so its differentials in `x` are `C^m`.
  have h := ContMDiff.contMDiff_totalSpaceMk_mvfderiv_uncurry
    (f := fun (φ : C^k⟮I, M; 𝓘(ℝ), ℝ⟯) (y : M) ↦ φ y)
    ((ContMDiffMap.contMDiff_eval_finiteAtlas (F := ℝ) k hK).of_le hm)
  exact h.comp (contMDiff_snd.prodMk contMDiff_fst)

include hK in
/-- For `k ≥ 2`, the coordinates of the universal differential in the trivialization of the
cotangent bundle at `x` are differentiable at every point `z = (x, f)`, since the universal
differential is then `C¹`. -/
theorem mdifferentiableAt_trivializationAt_universalDifferential (hk : 2 ≤ k)
    (z : M × C^k⟮I, M; 𝓘(ℝ), ℝ⟯) :
    letI := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
    letI := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
    MDifferentiableAt (I.prod 𝓘(ℝ, C^k⟮I, M; 𝓘(ℝ), ℝ⟯)) 𝓘(ℝ, E →L[ℝ] ℝ)
      (fun w ↦ (trivializationAt (E →L[ℝ] ℝ) (fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) z.1
        ⟨w.1, universalDifferential I w⟩).2) z := by
  let := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
  let := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
  exact ((contMDiffAt_totalSpace_iff.1 (contMDiff_universalDifferential k hK (m := 1)
    (by exact_mod_cast hk) z)).2).mdifferentiableAt one_ne_zero

include hK in
/-- **The linearization of the universal differential.** For `k ≥ 2`, at every point `(x, f)` of
`M × C^k(M, ℝ)`, the intrinsic linearization of the universal differential sends `(v, h)` to
`Hess_x f (v) + dh_x`: the critical Hessian of `f` in the direction of the point, and the
differential of `h` in the direction of the function. -/
theorem sectionLinearization_universalDifferential_apply (hk : 2 ≤ k)
    (z : M × C^k⟮I, M; 𝓘(ℝ), ℝ⟯) :
    letI := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
    letI := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
    ∀ p : TangentSpace (I.prod 𝓘(ℝ, C^k⟮I, M; 𝓘(ℝ), ℝ⟯)) z,
      sectionLinearization (F := E →L[ℝ] ℝ) (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
        (I.prod 𝓘(ℝ, C^k⟮I, M; 𝓘(ℝ), ℝ⟯)) Prod.fst (universalDifferential I) z p =
        criticalHessian I z.2 z.1 p.1 + mvfderiv I p.2 z.1 := by
  let := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
  let := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
  have : IsManifold I 2 M := IsManifold.of_le (n := k) (by exact_mod_cast hk)
  obtain ⟨x, f⟩ := z
  intro p
  set e := trivializationAt (E →L[ℝ] ℝ) (fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) x
  have hd : MDifferentiableAt (I.prod 𝓘(ℝ, C^k⟮I, M; 𝓘(ℝ), ℝ⟯)) 𝓘(ℝ, E →L[ℝ] ℝ)
      (fun w ↦ (e ⟨w.1, universalDifferential I w⟩).2) (x, f) :=
    mdifferentiableAt_trivializationAt_universalDifferential k hK hk (x, f)
  -- In the function direction the coordinates are `h ↦ dh_x`, a continuous linear map: the
  -- finite-atlas norm induces the weak Whitney topology, for which `h ↦ dh_x` is continuous.
  let L : C^k⟮I, M; 𝓘(ℝ), ℝ⟯ →L[ℝ] E →L[ℝ] ℝ :=
    ContMDiffMap.mvfderivCLM (F := ℝ) (by exact_mod_cast one_le_two.trans hk) x
  have hlin : (fun φ : C^k⟮I, M; 𝓘(ℝ), ℝ⟯ ↦ (e ⟨x, universalDifferential I (x, φ)⟩).2) = L := by
    funext φ
    ext w
    rw [universalDifferential_apply, CotangentBundle.trivializationAt_mk_snd,
      ContinuousLinearMap.comp_apply, Manifold.symmL_trivializationAt_self]
    exact (congrArg (· w) (ContMDiffMap.mvfderivCLM_apply _ x φ)).symm
  -- In the point direction the coordinates are those of `df`, whose derivative is the Hessian.
  have h₁ (w : E) : mvfderiv I (fun y ↦ (e ⟨y, universalDifferential I (y, f)⟩).2) x p.1 w =
      criticalHessian I f x p.1 w :=
    mvfderiv_trivializationAt_mvfderiv_apply_apply ((f.contMDiff.of_le (by exact_mod_cast hk)) x)
      p.1 w
  have h₂ (w : E) : mvfderiv 𝓘(ℝ, C^k⟮I, M; 𝓘(ℝ), ℝ⟯)
      (fun φ ↦ (e ⟨x, universalDifferential I (x, φ)⟩).2) f p.2 w = mvfderiv I p.2 x w := by
    rw [hlin, mvfderiv_eq_fderiv, L.fderiv]
    exact congrArg (· w) (ContMDiffMap.mvfderivCLM_apply _ x p.2)
  ext w
  rw [sectionLinearization_def]
  -- The trivialization at `x` is the identity on the fibre over `x`, and the derivative of the
  -- coordinates is the sum of the two partial derivatives.
  rw [ContinuousLinearMap.comp_apply, CotangentBundle.symmL_trivializationAt_self,
    hd.mvfderiv_prod_eq_add_apply]
  exact congrArg₂ (· + ·) (h₁ w) (h₂ w)

end FiniteRegularity

omit [LocallyCompactSpace E] in
include hK in
/-- **The universal differential is transverse to the zero section.** On a smooth Hausdorff
manifold and for `k ≥ 2`, its intrinsic linearization is surjective at every point of
`M × C^k(M, ℝ)`, already on the function directions: every covector at `x` is the differential of a
`C^k` function supported near `x`. Its target is finite-dimensional,
so its kernel is automatically complemented
(`ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range`). -/
theorem surjective_sectionLinearization_universalDifferential [FiniteDimensional ℝ E]
    [IsManifold I ∞ M] [T2Space M] (hk : 2 ≤ k)
    (z : M × C^k⟮I, M; 𝓘(ℝ), ℝ⟯) :
    letI := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
    letI := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
    Surjective (sectionLinearization (F := E →L[ℝ] ℝ) (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
      (I.prod 𝓘(ℝ, C^k⟮I, M; 𝓘(ℝ), ℝ⟯)) Prod.fst (universalDifferential I) z) := by
  let := ContMDiffMap.finiteAtlasNormedAddCommGroup (F := ℝ) k hK
  let := ContMDiffMap.finiteAtlasNormedSpace (F := ℝ) k hK
  intro ξ
  obtain ⟨h, hh⟩ := ContMDiffMap.surjective_mvfderivCLM (F := ℝ) (I := I) (M := M) (n := k)
    (by exact_mod_cast one_le_two.trans hk) z.1 ξ
  -- The direction `(0, h)` is sent to `Hess_x f (0) + dh_x = ξ`.
  refine ⟨((0 : E), h), (sectionLinearization_universalDifferential_apply k hK hk z _).trans ?_⟩
  rw [← hh, ContMDiffMap.mvfderivCLM_apply]
  exact (congrArg (· + _) (map_zero (criticalHessian I z.2 z.1))).trans (zero_add _)

end Universal

section Regular

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 2 M]

/-- **The regular parameters of the universal differential are the Morse functions.** On a
manifold modelled on `E`, a `C^n` function, `n ≥ 2`, is a regular parameter of the universal
differential, in the sense of parametric transversality, exactly when all of its critical points
are nondegenerate. -/
theorem isRegularSectionParameter_universalDifferential_iff {n : WithTop ℕ∞} (hn : 2 ≤ n)
    (f : C^n⟮𝓘(ℝ, E), M; 𝓘(ℝ), ℝ⟯) :
    IsRegularSectionParameter (F := E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) E Prod.fst
        (universalDifferential 𝓘(ℝ, E)) f ↔
      ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x := by
  simp only [isRegularSectionParameter_iff, universalDifferential_apply]
  refine forall_congr' fun x ↦ ?_
  rw [← mem_criticalPoints]
  exact imp_congr_right fun hx ↦
    surjective_sectionLinearization_mvfderiv_iff ((f.contMDiff.of_le hn) x) hx

end Regular

end TauCeti
