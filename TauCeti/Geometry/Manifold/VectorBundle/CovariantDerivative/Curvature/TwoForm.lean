/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ExteriorSquare
public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Smoothness
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# The curvature endomorphism on real two-forms

The musical identification `TauCeti.alternatingFormEquiv` carries the curvature endomorphism
on bivectors to the existing continuous alternating two-form fibres. Its normalization is
`Rop(u♭ ∧ v♭)(w,z) = ⟨R(u,v)z,w⟩`; constant curvature κ therefore gives κ times the identity.
This is the curvature operator on two-forms, rather than the curvature of the induced
connection on forms or the Weitzenböck potential.

We give its evaluation in any basis, prove symmetry for torsion-free metric connections,
and prove smoothness in the native two-form endomorphism bundle. The basis formula uses
the metric dual basis, so it also applies to nonorthonormal frames.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapters 7–8.
* The construction transports `CovariantDerivative.curvatureEndomorphism` through
  `TauCeti.alternatingFormEquiv`, with the Gram pairing `TauCeti.alternatingFormInner`.
  The inverse-metric regularity argument follows `TauCeti.IsSmoothForm.hodgeStar`.
-/

public section

open Bundle Module exteriorPower TauCeti
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]

section Basic

variable [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  (hcov : CovariantDerivative.IsMetricCompatible
    (V := fun x : M ↦ TangentSpace I x) cov)

/-- The curvature endomorphism on real two-forms, identified musically with the
curvature endomorphism on bivectors. The norm on forms remains their existing operator norm;
symmetry below is with respect to the Gram inner product. -/
def curvatureFormEndomorphism (x : M) :
    (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ]
      TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((alternatingFormEquiv (TangentSpace I x) 2).conj
    (cov.curvatureEndomorphism hcov x))

/-- The musical identification intertwines the two curvature endomorphisms. -/
@[simp]
theorem curvatureFormEndomorphism_alternatingFormEquiv (x : M)
    (a : ⋀[ℝ]^2 (TangentSpace I x)) :
    cov.curvatureFormEndomorphism hcov x (alternatingFormEquiv (TangentSpace I x) 2 a) =
      alternatingFormEquiv (TangentSpace I x) 2 (cov.curvatureEndomorphism hcov x a) := by
  simp [curvatureFormEndomorphism, LinearEquiv.conj_apply]

/-- Evaluation of the two-form curvature operator in an arbitrary basis. The arguments
of curvature are the metric dual basis, not the original basis. -/
theorem curvatureFormEndomorphism_apply_eq_sum {ι : Type*} [Fintype ι] [LinearOrder ι]
    (x : M) (b : Basis ι ℝ (TangentSpace I x))
    (α : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) (v : Fin 2 → TangentSpace I x) :
    cov.curvatureFormEndomorphism hcov x α v =
      ∑ s : Set.powersetCard ι 2, α (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s) *
        ⟪cov.curvatureTensor x
          (LinearMap.BilinForm.dualBasis (innerₗ (TangentSpace I x)) nondegenerate_inner b
            (Set.powersetCard.ofFinEmbEquiv.symm s 0))
          (LinearMap.BilinForm.dualBasis (innerₗ (TangentSpace I x)) nondegenerate_inner b
            (Set.powersetCard.ofFinEmbEquiv.symm s 1)) (v 1), v 0⟫ := by
  conv_lhs => rw [← (alternatingFormEquiv (TangentSpace I x) 2).apply_symm_apply α,
    b.alternatingFormEquiv_symm_eq_sum]
  simp only [map_sum, map_smul, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    curvatureFormEndomorphism_alternatingFormEquiv, alternatingFormEquiv_apply,
    inner_curvatureEndomorphism_ιMulti, Function.comp_apply]

/-- The two-form curvature operator of a torsion-free metric connection is symmetric
for the Gram inner product. -/
theorem alternatingFormInner_curvatureFormEndomorphism (ht : cov.torsion = 0) (x : M)
    (α β : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :
    alternatingFormInner (TangentSpace I x) 2 (cov.curvatureFormEndomorphism hcov x α) β =
      alternatingFormInner (TangentSpace I x) 2 α (cov.curvatureFormEndomorphism hcov x β) := by
  obtain ⟨a, rfl⟩ := (alternatingFormEquiv (TangentSpace I x) 2).surjective α
  obtain ⟨b, rfl⟩ := (alternatingFormEquiv (TangentSpace I x) 2).surjective β
  simp only [curvatureFormEndomorphism_alternatingFormEquiv,
    alternatingFormInner_alternatingFormEquiv]
  exact cov.isSymmetric_curvatureEndomorphism hcov ht x a b

/-- Constant sectional curvature at a point is equivalent to the scalar two-form curvature
operator. Below dimension two both sides hold for every κ, so this does not identify κ. -/
theorem hasSectionalCurvatureAt_iff_curvatureFormEndomorphism_eq_smul_id
    (ht : cov.torsion = 0) (x : M) (κ : ℝ) :
    cov.HasSectionalCurvatureAt hcov x κ ↔
      cov.curvatureFormEndomorphism hcov x =
        κ • ContinuousLinearMap.id ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) := by
  rw [cov.hasSectionalCurvatureAt_iff_curvatureEndomorphism_eq_smul_id hcov ht]
  constructor
  · intro h
    ext α v
    obtain ⟨a, rfl⟩ := (alternatingFormEquiv (TangentSpace I x) 2).surjective α
    simp [h]
  · intro h
    apply LinearMap.ext
    intro a
    apply (alternatingFormEquiv (TangentSpace I x) 2).injective
    rw [← curvatureFormEndomorphism_alternatingFormEquiv, h]
    simp

end Basic

section Smooth

variable [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
  (hcov : CovariantDerivative.IsMetricCompatible
    (V := fun x : M ↦ TangentSpace I x) cov)

/-- The curvature endomorphism sends smooth real two-forms to smooth real two-forms. -/
theorem isSmoothForm_curvatureFormEndomorphism {α : RoughForm I M ℝ 2}
    (hα : IsSmoothForm I ∞ α) :
    IsSmoothForm I ∞ (fun y ↦ cov.curvatureFormEndomorphism hcov y (α y)) := by
  classical
  have : IsManifold I (∞ + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  rw [isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply] at hα ⊢
  intro x v
  let e := trivializationAt E (TangentSpace I) x
  let b := Module.finBasis ℝ E
  let D (i : Fin (finrank ℝ E)) (y : M) : TangentSpace I y :=
    ∑ j, Riemannian.Tensor.chartInvGramMatrix (I := I) x y i j • e.symmL ℝ y (b j)
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  have hbase := e.open_baseSet.mem_nhds hx
  have hframe (w : E) : CMDiffAt ∞ (T% (fun y ↦ e.symmL ℝ y w)) x :=
    (e.contMDiffAt_symmL hx).clm_bundle_apply (by
      rw [contMDiffAt_section]
      simpa using (contMDiffAt_const (I := I) (c := w) (n := ∞) (x := x)))
  -- The inverse metric makes the metric dual frame smooth, without choosing orthonormal
  -- frames smoothly as the point varies.
  have hD (i : Fin (finrank ℝ E)) : CMDiffAt ∞ (T% (D i)) x := by
    exact ContMDiffAt.sum_section fun j _ ↦
      ((Riemannian.Tensor.contMDiffOn_chartInvGramMatrix_entry (I := I) (n := ∞)
        x i j).contMDiffAt hbase).smul_section (hframe (b j))
  -- Cache the iterated operator fibres to keep typeclass search within its default budget.
  let _ : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
  let _ : ∀ y : M, NormedAddCommGroup (TangentSpace I y →L[ℝ] TangentSpace I y) :=
    fun y ↦ inferInstance
  let _ : ∀ y : M, NormedSpace ℝ (TangentSpace I y →L[ℝ] TangentSpace I y) :=
    fun y ↦ inferInstance
  let _ : ∀ y : M, NormedAddCommGroup
      (TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y) :=
    fun y ↦ inferInstance
  let _ : ∀ y : M, NormedSpace ℝ
      (TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y) :=
    fun y ↦ inferInstance
  let _ : ∀ y : M, AddCommMonoid
      (TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y) :=
    fun y ↦ (inferInstance : NormedAddCommGroup
      (TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y)).toAddCommMonoid
  have hR (i j : Fin (finrank ℝ E)) :
      CMDiffAt ∞ (T% (fun y ↦ cov.curvatureTensor y (D i y) (D j y)
        (e.symmL ℝ y (v 1)))) x := by
    simpa only [curvatureTensorCLM_apply] using
      (((contMDiff_curvatureTensorCLM (F := E) (V := fun y : M ↦ TangentSpace I y)
        (fiberNorm := fun y ↦ inferInstanceAs (NormedAddCommGroup (TangentSpace I y)))
        cov x).clm_bundle_apply (hD i)).clm_bundle_apply (hD j)).clm_bundle_apply (hframe (v 1))
  have hsum : ContMDiffAt I 𝓘(ℝ) ∞ (fun y ↦
      ∑ s : Set.powersetCard (Fin (finrank ℝ E)) 2,
        α y (e.symmL ℝ y ∘ (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s)) *
          ⟪cov.curvatureTensor y (D (Set.powersetCard.ofFinEmbEquiv.symm s 0) y)
            (D (Set.powersetCard.ofFinEmbEquiv.symm s 1) y) (e.symmL ℝ y (v 1)),
              e.symmL ℝ y (v 0)⟫) x :=
    contMDiffAt_finsetSum fun s _ ↦ (hα x _).mul
      ((hR _ _).inner_bundle (IB := I) (F := E) (E := fun y : M ↦ TangentSpace I y)
        (b := fun y : M ↦ y)
        (h := (inferInstance : IsContMDiffRiemannianBundle I ∞ E
          (fun y : M ↦ TangentSpace I y))) (hframe (v 0)))
  -- On the chart domain, this is exactly the arbitrary-basis evaluation formula.
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hbase] with y hy
  let B := e.basisAt b hy
  have hB : ⇑B = e.symmL ℝ y ∘ b :=
    funext (TauCeti.Manifold.basisAt_apply b hy)
  have hG : Matrix.gram ℝ B = Riemannian.Tensor.chartGramMatrix (I := I) x y := by
    simpa [B, b, e] using
      Riemannian.Tensor.gram_basisAt_finBasis_reindex (I := I) (Equiv.refl _) x hy
  have hdual (i) :
      LinearMap.BilinForm.dualBasis (innerₗ (TangentSpace I y)) nondegenerate_inner B i =
        D i y := by
    rw [B.dualBasis_innerₗ_eq_sum, hG, ← Riemannian.Tensor.chartInvGramMatrix_def, hB]
    rfl
  rw [cov.curvatureFormEndomorphism_apply_eq_sum hcov y B]
  simp only [hdual, hB, Function.comp_apply, Function.comp_assoc]
  rfl

/-- The curvature endomorphism is a smooth section of the native endomorphism bundle of
real two-forms. No additional exterior-power bundle or topology is installed. -/
theorem contMDiff_curvatureFormEndomorphism :
    ContMDiff I (I.prod 𝓘(ℝ, (E [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin 2]→L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' ((E [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin 2]→L[ℝ] ℝ)
        x (cov.curvatureFormEndomorphism hcov x)) := by
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro α hα
  exact (cov.isSmoothForm_curvatureFormEndomorphism hcov
    ((isSmoothForm_def ∞ α).2 hα)).contMDiff

end Smooth

end CovariantDerivative
