/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.FormOperator
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Eigenspace
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Isometry
import TauCeti.Analysis.InnerProductSpace.LaxMilgram
import TauCeti.Geometry.Manifold.Riemannian.Poisson
import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Rellich
import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.Equiv

/-!
# The Laplacian of a closed manifold as a self-adjoint operator on `L²`

Let `M` be a closed manifold with a Riemannian metric, its Riemannian volume `dV`, the Sobolev space
`H¹(M)` (`TauCeti.Manifold.SobolevH1`) with its value map `J : H¹(M) → L²(M)` and its Dirichlet
form `D`, the continuous extension of `∫ ⟪∇u, ∇v⟫ dV` from smooth functions. This file realizes the
negative Laplacian `Δ⁺ = -div grad`, a nonnegative operator, as an unbounded operator on `L²(M)`,
the partial linear map `TauCeti.Manifold.SobolevH1.negLaplacian`. A pair `(f, g)` lies on its
graph exactly when

`f = J w` for some `w ∈ H¹(M)` with `D(w, v) = ⟪g, J v⟫_{L²}` for every `v ∈ H¹(M)`,

that is, when `Δ⁺ f = g` weakly (`TauCeti.Manifold.SobolevH1.mem_graph_negLaplacian_iff`). It
is the operator of the form `D` (`IsCoercive.formOperator`): the `H¹` inner product is the shifted
form `D + ⟪J ·, J ·⟫_{L²}`, which is coercive, so `Δ⁺ + 1` is the inverse of its Lax–Milgram
solution operator.

* `Δ⁺` is self-adjoint (`TauCeti.Manifold.SobolevH1.isSelfAdjoint_negLaplacian`) and
  nonnegative (`TauCeti.Manifold.SobolevH1.inner_negLaplacian_self_nonneg`), since `D` is
  symmetric and nonnegative.
* Its resolvent is compact (`TauCeti.Manifold.SobolevH1.hasCompactResolvent_negLaplacian`), by
  the Rellich–Kondrachov theorem.
* Its eigenvectors are the values of the weak eigenfunctions
  (`TauCeti.Manifold.SobolevH1.exists_negLaplacian_apply_eq_smul_iff`), so the eigenfunction
  expansion of `TauCeti.Geometry.Manifold.Riemannian.Sobolev.Eigenbasis` is an orthonormal
  eigenbasis of `Δ⁺`, with finite multiplicities.
* On a connected manifold its kernel consists of the constants
  (`TauCeti.Manifold.SobolevH1.exists_negLaplacian_apply_eq_zero_iff`) and its range of the
  functions of integral zero (`TauCeti.Manifold.SobolevH1.mem_range_negLaplacian_iff`), by the
  weak Poisson theory of `TauCeti.Geometry.Manifold.Riemannian.Poisson`. For instance on the circle
  `Δ⁺ f = 1` has no solution, since `1` does not have integral zero.
* For a `C¹` metric, if `f = J w` lies in the domain then `D(w, v) = ⟪Δ⁺ f, J v⟫_{L²}`
  (`TauCeti.Manifold.SobolevH1.dirichletForm_eq_inner_negLaplacian`). For a smooth metric, the
  smooth functions lie in the domain, where `Δ⁺` is minus the Laplace–Beltrami operator
  (`TauCeti.Manifold.SobolevH1.toLp_ofSmooth_mem_domain_negLaplacian`,
  `TauCeti.Manifold.SobolevH1.negLaplacian_toLp_ofSmooth`).
* `Δ⁺` is natural under Riemannian isometries `Φ : M → N`: composition with `Φ` maps the graph of
  `Δ⁺` on `N` onto that on `M`
  (`TauCeti.Manifold.SobolevH1.mem_graph_negLaplacian_compMeasurePreserving_iff`), so it
  preserves the domain and commutes with `Δ⁺`
  (`TauCeti.Manifold.SobolevH1.negLaplacian_compMeasurePreserving`). In particular a group
  acting by isometries acts on `L²(M)` by unitaries preserving the domain of `Δ⁺` and commuting
  with it.

The domain is the maximal weak domain `{J w | v ↦ D(w, v) is L²-bounded}`
(`TauCeti.Manifold.SobolevH1.mem_domain_negLaplacian_iff`). For a smooth metric, elliptic
regularity identifies it with the Sobolev space `H²(M)`.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Chapter VI, §2 (the representation
  theorems for closed semibounded forms).
* I. Chavel, *Eigenvalues in Riemannian Geometry*, Academic Press, 1984, Chapter I (the
  Laplacian of a closed manifold and its discrete spectrum).
* P. Bérard, *Transplantation et isospectralité. I*, Math. Ann. 292 (1992), §II (isometry
  invariance of the Laplacian).
-/

public section

open Bundle MeasureTheory
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace TauCeti.Manifold.SobolevH1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable (I M) in
/-- **The negative Laplacian** `Δ⁺ = -div grad` of a closed manifold, as an unbounded operator
on `L²(M)`: the operator of the Dirichlet form `D` along the value map `H¹(M) → L²(M)`. Its graph
consists of the pairs `(J w, g)` with `D(w, v) = ⟪g, J v⟫_{L²}` for every `v ∈ H¹(M)`
(`TauCeti.Manifold.SobolevH1.mem_graph_negLaplacian_iff`). -/
def negLaplacian : Lp ℝ 2 (riemannianVolume I M) →ₗ.[ℝ] Lp ℝ 2 (riemannianVolume I M) :=
  isCoercive_innerSL.formOperator toLp 1

/-- The `H¹` inner product is the Dirichlet form shifted by the `L²` inner product. -/
private theorem inner_eq_dirichletForm_add (w v : SobolevH1 I M) :
    innerSL ℝ w v = dirichletForm w v + 1 * ⟪toLp w, toLp v⟫_ℝ := by
  rw [dirichletForm_apply, innerSL_apply_apply]
  ring

/-- The right-hand side `0` of the Poisson equation has integral zero. -/
private theorem integral_coeFn_zero :
    ∫ x, (0 : Lp ℝ 2 (riemannianVolume I M)) x ∂riemannianVolume I M = 0 :=
  integral_eq_zero_of_ae (Lp.coeFn_zero ℝ 2 _)

/-- The weak right-hand side `0` of the Poisson equation. -/
private theorem integral_zero_mul_toLp (v : SobolevH1 I M) :
    ∫ x, (0 : Lp ℝ 2 (riemannianVolume I M)) x * toLp v x ∂riemannianVolume I M = 0 := by
  refine integral_eq_zero_of_ae ?_
  filter_upwards [Lp.coeFn_zero ℝ 2 (riemannianVolume I M)] with x hx
  rw [hx, Pi.zero_apply, zero_mul]

/-- `Δ⁺ f = g` for some proof that `f` lies in the domain exactly when `(f, g)` is on the graph. -/
private theorem exists_negLaplacian_apply_eq_iff {f g : Lp ℝ 2 (riemannianVolume I M)} :
    (∃ hf : f ∈ (negLaplacian I M).domain, negLaplacian I M ⟨f, hf⟩ = g) ↔
      (f, g) ∈ (negLaplacian I M).graph := by
  simp only [LinearPMap.mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left]

section Closed

variable [IsManifold I ∞ M] [T2Space M]

/-- **The graph of the Laplacian.** `(f, g)` lies on the graph of `Δ⁺` exactly when `f` is the
value of some `w ∈ H¹(M)` with `D(w, v) = ⟪g, J v⟫_{L²}` for every `v ∈ H¹(M)`, that is, when
`Δ⁺ f = g` weakly. -/
theorem mem_graph_negLaplacian_iff {f g : Lp ℝ 2 (riemannianVolume I M)} :
    (f, g) ∈ (negLaplacian I M).graph ↔
      ∃ w : SobolevH1 I M, toLp w = f ∧ ∀ v, dirichletForm w v = ⟪g, toLp v⟫_ℝ :=
  isCoercive_innerSL.mem_graph_formOperator_iff denseRange_toLp inner_eq_dirichletForm_add

/-- **The domain of the Laplacian** is the maximal weak domain: `f` lies in it exactly when `f` is
the value of some `w ∈ H¹(M)` for which `v ↦ D(w, v)` is bounded by a multiple of the `L²` norm
of `v`. -/
theorem mem_domain_negLaplacian_iff {f : Lp ℝ 2 (riemannianVolume I M)} :
    f ∈ (negLaplacian I M).domain ↔
      ∃ w : SobolevH1 I M, toLp w = f ∧ ∃ C : ℝ, ∀ v, |dirichletForm w v| ≤ C * ‖toLp v‖ :=
  isCoercive_innerSL.mem_domain_formOperator_iff denseRange_toLp inner_eq_dirichletForm_add

/-- Every element `f` of the domain is the value of some `w ∈ H¹(M)` with
`D(w, v) = ⟪Δ⁺ f, J v⟫_{L²}` for every `v ∈ H¹(M)`. -/
theorem exists_dirichletForm_eq_inner_negLaplacian (f : (negLaplacian I M).domain) :
    ∃ w : SobolevH1 I M, toLp w = f ∧
      ∀ v, dirichletForm w v = ⟪negLaplacian I M f, toLp v⟫_ℝ :=
  mem_graph_negLaplacian_iff.1 ((negLaplacian I M).mem_graph f)

/-- **The Laplacian is self-adjoint.** -/
theorem isSelfAdjoint_negLaplacian : IsSelfAdjoint (negLaplacian I M) :=
  isCoercive_innerSL.isSelfAdjoint_formOperator denseRange_toLp inner_eq_dirichletForm_add
    dirichletForm_comm

/-- **The Laplacian is nonnegative**: `⟪Δ⁺ f, f⟫_{L²} ≥ 0` for every `f` in its domain. -/
theorem inner_negLaplacian_self_nonneg (f : (negLaplacian I M).domain) :
    0 ≤ ⟪negLaplacian I M f, (f : Lp ℝ 2 (riemannianVolume I M))⟫_ℝ := by
  obtain ⟨w, hw, hD⟩ := exists_dirichletForm_eq_inner_negLaplacian f
  rw [← hw, ← hD]
  exact dirichletForm_self_nonneg w

/-- **The eigenvectors of the Laplacian are the weak eigenfunctions.** `f` lies in the domain of
`Δ⁺` with `Δ⁺ f = μ f` exactly when `f` is the value of a weak `μ`-eigenfunction `w ∈ H¹(M)`. -/
theorem exists_negLaplacian_apply_eq_smul_iff {μ : ℝ} {f : Lp ℝ 2 (riemannianVolume I M)} :
    (∃ hf : f ∈ (negLaplacian I M).domain, negLaplacian I M ⟨f, hf⟩ = μ • f) ↔
      ∃ w ∈ weakEigenspace I M μ, toLp w = f := by
  rw [exists_negLaplacian_apply_eq_iff, mem_graph_negLaplacian_iff]
  refine exists_congr fun w ↦ ⟨fun ⟨hw, hD⟩ ↦ ⟨mem_weakEigenspace_iff.2 fun v ↦ ?_, hw⟩,
    fun ⟨hμ, hw⟩ ↦ ⟨hw, fun v ↦ ?_⟩⟩
  · rw [hD, ← hw, real_inner_smul_left]
  · rw [mem_weakEigenspace_iff.1 hμ, ← hw, real_inner_smul_left]

/-- The constant functions lie in the kernel of the Laplacian. -/
theorem mem_graph_negLaplacian_smul_toLp_ofSmooth_one (c : ℝ) :
    (c • toLp (ofSmooth (1 : C^∞⟮I, M; ℝ⟯)), 0) ∈ (negLaplacian I M).graph := by
  refine mem_graph_negLaplacian_iff.2 ⟨c • ofSmooth 1, by rw [map_smul], fun v ↦ ?_⟩
  rw [inner_zero_left, map_smul]
  simp [dirichletForm_comm (ofSmooth (1 : C^∞⟮I, M; ℝ⟯)) v]

section Boundaryless

variable [I.Boundaryless]

/-- **The Laplacian has compact resolvent**, by the Rellich–Kondrachov theorem. -/
theorem hasCompactResolvent_negLaplacian : (negLaplacian I M).HasCompactResolvent :=
  isCoercive_innerSL.hasCompactResolvent_formOperator isCompactOperator_toLp denseRange_toLp

section Connected

variable [PreconnectedSpace M]

/-- **The kernel of the Laplacian consists of the constants.** On a closed connected manifold,
`f` lies in the domain of `Δ⁺` with `Δ⁺ f = 0` exactly when `f` is the value of a constant
function. -/
theorem exists_negLaplacian_apply_eq_zero_iff {f : Lp ℝ 2 (riemannianVolume I M)} :
    (∃ hf : f ∈ (negLaplacian I M).domain, negLaplacian I M ⟨f, hf⟩ = 0) ↔
      ∃ c : ℝ, c • toLp (ofSmooth (1 : C^∞⟮I, M; ℝ⟯)) = f := by
  rw [exists_negLaplacian_apply_eq_iff]
  refine ⟨fun h ↦ ?_, fun ⟨c, hc⟩ ↦ hc ▸ mem_graph_negLaplacian_smul_toLp_ofSmooth_one c⟩
  obtain ⟨w, rfl, hD⟩ := mem_graph_negLaplacian_iff.1 h
  -- Subtract from `w` its mean value; the difference is a weak solution of `Δ⁺ w' = 0` of
  -- integral zero, hence zero by uniqueness of the weak Poisson problem.
  set e := toLp (ofSmooth (1 : C^∞⟮I, M; ℝ⟯)) with he_def
  have hint (u : SobolevH1 I M) : ∫ x, toLp u x ∂riemannianVolume I M = ⟪toLp u, e⟫_ℝ := by
    rw [he_def, inner_toLp_ofSmooth_right]
    simp
  have hc : ⟪toLp w, e⟫_ℝ - ⟪toLp w, e⟫_ℝ / ‖e‖ ^ 2 * ‖e‖ ^ 2 = 0 := by
    rcases eq_or_ne e 0 with he | he
    · simp [he]
    · rw [div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.2 he)), sub_self]
  set c := ⟪toLp w, e⟫_ℝ / ‖e‖ ^ 2
  have hzero : w - c • ofSmooth (1 : C^∞⟮I, M; ℝ⟯) = 0 :=
    (existsUnique_dirichletForm_eq 0 integral_coeFn_zero).unique
      ⟨by
          rw [hint]
          simpa only [map_sub, map_smul, ← he_def, inner_sub_left, real_inner_smul_left,
            real_inner_self_eq_norm_sq] using hc,
        fun v ↦ by
          rw [integral_zero_mul_toLp]
          simp [hD, dirichletForm_comm (ofSmooth (1 : C^∞⟮I, M; ℝ⟯)) v]⟩
      ⟨by rw [map_zero]; exact integral_coeFn_zero,
        fun v ↦ by rw [integral_zero_mul_toLp]; simp⟩
  exact ⟨c, by rw [sub_eq_zero.1 hzero, map_smul]⟩

/-- **The range of the Laplacian consists of the functions of integral zero.** On a closed
connected manifold, `Δ⁺ f = g` has a solution `f` in the domain exactly when `∫ g dV = 0`. -/
theorem mem_range_negLaplacian_iff {g : Lp ℝ 2 (riemannianVolume I M)} :
    g ∈ LinearMap.range (negLaplacian I M).toFun ↔ ∫ x, g x ∂riemannianVolume I M = 0 := by
  have hinner (w v : SobolevH1 I M) : (dirichletForm w v = ⟪g, toLp v⟫_ℝ) ↔
      dirichletForm w v = ∫ x, g x * toLp v x ∂riemannianVolume I M := by
    simp [L2.inner_def, mul_comm]
  rw [LinearMap.mem_range, ← exists_forall_dirichletForm_eq_iff]
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨w, -, hD⟩ := exists_dirichletForm_eq_inner_negLaplacian f
    refine ⟨w, fun v ↦ (hinner w v).1 ?_⟩
    rw [← hf]
    exact hD v
  · rintro ⟨w, hw⟩
    obtain ⟨f, -, hf⟩ := (negLaplacian I M).mem_graph_iff.1
      (mem_graph_negLaplacian_iff.2 ⟨w, rfl, fun v ↦ (hinner w v).2 (hw v)⟩)
    exact ⟨f, hf⟩

end Connected

section C1

variable [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **The Laplacian represents the Dirichlet form.** For a `C¹` metric, if the value `J w` of
`w ∈ H¹(M)` lies in the domain of `Δ⁺`, then `D(w, v) = ⟪Δ⁺ (J w), J v⟫_{L²}` for every
`v ∈ H¹(M)`. -/
theorem dirichletForm_eq_inner_negLaplacian {w : SobolevH1 I M}
    (hw : toLp w ∈ (negLaplacian I M).domain) (v : SobolevH1 I M) :
    dirichletForm w v = ⟪negLaplacian I M ⟨toLp w, hw⟩, toLp v⟫_ℝ := by
  obtain ⟨w', hw', hD⟩ := exists_dirichletForm_eq_inner_negLaplacian ⟨toLp w, hw⟩
  obtain rfl : w' = w := toLp_injective hw'
  exact hD v

end C1

end Boundaryless

end Closed

/-! ### Naturality under Riemannian isometries -/

section Isometry

variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [CompactSpace N] [IsManifold I' 1 N]
  [MeasurableSpace N] [BorelSpace N]
  [RiemannianBundle (fun y : N ↦ TangentSpace I' y)]
  [IsContinuousRiemannianBundle E (fun y : N ↦ TangentSpace I' y)]

/-- Composing with a Riemannian isometry `Φ` and then with its inverse is the identity on `L²`. -/
private theorem compMeasurePreserving_symm_compMeasurePreserving
    (Φ : RiemannianIsometry I I' M N) (u : Lp ℝ 2 (riemannianVolume I' N)) :
    Lp.compMeasurePreserving Φ.symm Φ.symm.measurePreserving_riemannianVolume
      (Lp.compMeasurePreserving Φ Φ.measurePreserving_riemannianVolume u) = u :=
  Lp.leftInverse_compMeasurePreserving _ _ (.of_forall Φ.apply_symm_apply) u

variable [IsManifold I ∞ M] [T2Space M] [IsManifold I' ∞ N] [T2Space N]

/-- Composition with a Riemannian isometry `Φ : M → N` maps the graph of `Δ⁺` on `N` into that
on `M`. -/
private theorem mem_graph_negLaplacian_compMeasurePreserving
    (Φ : RiemannianIsometry I I' M N) {f g : Lp ℝ 2 (riemannianVolume I' N)}
    (h : (f, g) ∈ (negLaplacian I' N).graph) :
    (Lp.compMeasurePreserving Φ Φ.measurePreserving_riemannianVolume f,
      Lp.compMeasurePreserving Φ Φ.measurePreserving_riemannianVolume g) ∈
        (negLaplacian I M).graph := by
  obtain ⟨w, rfl, hD⟩ := mem_graph_negLaplacian_iff.1 h
  refine mem_graph_negLaplacian_iff.2
    ⟨compRiemannianIsometry Φ w, toLp_compRiemannianIsometry Φ w, fun v ↦ ?_⟩
  obtain ⟨v, rfl⟩ := (compRiemannianIsometry Φ).surjective v
  rw [dirichletForm_compRiemannianIsometry, hD, toLp_compRiemannianIsometry]
  exact ((Lp.compMeasurePreservingₗᵢ ℝ Φ Φ.measurePreserving_riemannianVolume).inner_map_map
    g (toLp v)).symm

/-- **The Laplacian is natural under Riemannian isometries.** For a Riemannian isometry
`Φ : M → N`, `(f ∘ Φ, g ∘ Φ)` lies on the graph of `Δ⁺` on `M` exactly when `(f, g)` lies on the
graph of `Δ⁺` on `N`. -/
theorem mem_graph_negLaplacian_compMeasurePreserving_iff (Φ : RiemannianIsometry I I' M N)
    {f g : Lp ℝ 2 (riemannianVolume I' N)} :
    (Lp.compMeasurePreserving Φ Φ.measurePreserving_riemannianVolume f,
      Lp.compMeasurePreserving Φ Φ.measurePreserving_riemannianVolume g) ∈
        (negLaplacian I M).graph ↔ (f, g) ∈ (negLaplacian I' N).graph := by
  refine ⟨fun h ↦ ?_, mem_graph_negLaplacian_compMeasurePreserving Φ⟩
  simpa only [compMeasurePreserving_symm_compMeasurePreserving] using
    mem_graph_negLaplacian_compMeasurePreserving Φ.symm h

/-- A Riemannian isometry `Φ : M → N` preserves the domain of the Laplacian: `f ∘ Φ` lies in the
domain of `Δ⁺` on `M` exactly when `f` lies in the domain of `Δ⁺` on `N`. -/
theorem compMeasurePreserving_mem_domain_negLaplacian_iff (Φ : RiemannianIsometry I I' M N)
    {f : Lp ℝ 2 (riemannianVolume I' N)} :
    Lp.compMeasurePreserving Φ Φ.measurePreserving_riemannianVolume f ∈
        (negLaplacian I M).domain ↔ f ∈ (negLaplacian I' N).domain := by
  refine ⟨fun h ↦ ?_, fun h ↦ LinearPMap.mem_domain_of_mem_graph
    (mem_graph_negLaplacian_compMeasurePreserving Φ ((negLaplacian I' N).mem_graph ⟨f, h⟩))⟩
  have hgraph :=
    mem_graph_negLaplacian_compMeasurePreserving Φ.symm ((negLaplacian I M).mem_graph ⟨_, h⟩)
  rw [compMeasurePreserving_symm_compMeasurePreserving] at hgraph
  exact LinearPMap.mem_domain_of_mem_graph hgraph

/-- **Riemannian isometries commute with the Laplacian.** For a Riemannian isometry
`Φ : M → N` and `f` in the domain of `Δ⁺` on `N`, `Δ⁺ (f ∘ Φ) = (Δ⁺ f) ∘ Φ`. -/
theorem negLaplacian_compMeasurePreserving (Φ : RiemannianIsometry I I' M N)
    (f : (negLaplacian I' N).domain) :
    negLaplacian I M ⟨Lp.compMeasurePreserving Φ Φ.measurePreserving_riemannianVolume f,
        (compMeasurePreserving_mem_domain_negLaplacian_iff Φ).2 f.property⟩ =
      Lp.compMeasurePreserving Φ Φ.measurePreserving_riemannianVolume
        (negLaplacian I' N f) :=
  (negLaplacian I M).mem_graph_snd_inj (LinearPMap.mem_graph _ _)
    (mem_graph_negLaplacian_compMeasurePreserving Φ ((negLaplacian I' N).mem_graph f)) rfl

end Isometry

/-! ### Smooth metrics: the Laplacian on smooth functions -/

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I ∞ M]
  [T2Space M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

attribute [local instance] instIsContinuousRiemannianBundleOfContMDiffInfty

/-- **The Laplacian on smooth functions.** For a smooth metric, the value of every smooth function
`u` lies in the domain of `Δ⁺`, and `Δ⁺ u = -Δu`, where `Δ = div grad` is the Laplace–Beltrami
operator. -/
theorem mem_graph_negLaplacian_toLp_ofSmooth (u : C^∞⟮I, M; ℝ⟯) :
    (toLp (ofSmooth u), -toLp (ofSmooth (smoothLaplaceBeltrami I M u))) ∈
      (negLaplacian I M).graph := by
  refine mem_graph_negLaplacian_iff.2 ⟨ofSmooth u, rfl, fun v ↦ ?_⟩
  rw [dirichletForm_comm, dirichletForm_ofSmooth_right, inner_neg_left, real_inner_comm,
    inner_toLp_ofSmooth_right, ← integral_neg]
  simp

/-- For a smooth metric, the value of every smooth function lies in the domain of `Δ⁺`. -/
theorem toLp_ofSmooth_mem_domain_negLaplacian (u : C^∞⟮I, M; ℝ⟯) :
    toLp (ofSmooth u) ∈ (negLaplacian I M).domain :=
  LinearPMap.mem_domain_of_mem_graph (mem_graph_negLaplacian_toLp_ofSmooth u)

/-- For a smooth metric, `Δ⁺ u = -Δu` for every smooth function `u`, where `Δ = div grad` is the
Laplace–Beltrami operator. -/
theorem negLaplacian_toLp_ofSmooth (u : C^∞⟮I, M; ℝ⟯) :
    negLaplacian I M ⟨toLp (ofSmooth u), toLp_ofSmooth_mem_domain_negLaplacian u⟩ =
      -toLp (ofSmooth (smoothLaplaceBeltrami I M u)) :=
  (negLaplacian I M).mem_graph_snd_inj (LinearPMap.mem_graph _ _)
    (mem_graph_negLaplacian_toLp_ofSmooth u) rfl

end Smooth

end TauCeti.Manifold.SobolevH1
