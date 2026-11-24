/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Family
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Section

/-!
# Joint Hessian continuity for metric families

For native smooth Riemannian metrics whose pairings are jointly `C¹` on `univ ×ˢ U`,
the Hessian of a locally `C²` scalar paired with locally `C¹` fields is jointly continuous
on that domain. The proof uses local regularity of the family Levi–Civita connection.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, Chapter 5.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP 1 P]
  (g : P → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))

private def frozenConnection (p : P) : CovariantDerivative I E (TangentSpace I : M → Type _) :=
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g p).toRiemannianMetric⟩
  leviCivitaConnection I M

/-- Local first-order metric regularity and second-order scalar regularity give continuous
Hessians paired with locally `C¹` tangent fields. -/
theorem contMDiffOn_hessian_family
    {U : Set M}
    (hg : ContMDiffOn (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun p : P × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        p.2 ((g p.1).inner p.2)) (univ ×ˢ U))
    (hU : IsOpen U) {f : M → ℝ} (hf : ContMDiffOn I 𝓘(ℝ) 2 f U)
    {X Y : Π x : M, TangentSpace I x}
    (hX : ContMDiffOn I I.tangent 1 (T% X) U)
    (hY : ContMDiffOn I I.tangent 1 (T% Y) U) :
    ContMDiffOn (IP.prod I) 𝓘(ℝ) 0
      (fun p : P × M ↦
        let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g p.1).toRiemannianMetric⟩
        hessian I f p.2 (X p.2) (Y p.2)) (univ ×ˢ U) := by
  have hmetric (p : P) (x : M) :
      (g p).toNondegenerateMetric x = (g p).inner x := by
    ext v w
    exact ContMDiffRiemannianMetric.toNondegenerateMetric_apply (g p) x v w
  have hcov (p : P) : (g p).toNondegenerateMetric.IsLeviCivitaConnection
      (frozenConnection g p) := by
    let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g p).toRiemannianMetric⟩
    exact ((g p).toNondegenerateMetric.isLeviCivitaConnection_iff_of_apply_eq_inner
      (fun x v w ↦ by
        simp only [ContMDiffRiemannianMetric.toNondegenerateMetric_apply]
        rfl)).mpr (isLeviCivitaConnection_leviCivitaConnection I)
  have hC := TauCeti.Manifold.contMDiffOn_covariantDerivative_of_isLeviCivitaConnection
    (IP := IP) (g := fun p ↦ (g p).toNondegenerateMetric) (cov := frozenConnection g)
    hcov (n := 0) (by simp) hU (by simpa [hmetric] using hg) (by simpa using hY)
  have hXP : ContMDiffOn (IP.prod I) I.tangent 0
      (fun p : P × M ↦ TotalSpace.mk' E p.2 (X p.2)) (univ ×ˢ U) :=
    (hX.of_le (by norm_num)).comp contMDiffOn_snd (fun _ hp ↦ hp.2)
  have hCY := hC.clm_bundle_apply hXP
  have hdY : ContMDiffOn I 𝓘(ℝ) 1 (fun x ↦ mvfderiv I f x (Y x)) U :=
    hf.contMDiffOn_mvfderiv_apply hU hY (by norm_num)
  have hdXY : ContMDiffOn (IP.prod I) 𝓘(ℝ) 0
      (fun p : P × M ↦ mvfderiv I (fun x ↦ mvfderiv I f x (Y x)) p.2 (X p.2))
      (univ ×ˢ U) :=
    (hdY.contMDiffOn_mvfderiv_apply hU (hX.of_le (by norm_num))
      (by norm_num)).comp
      contMDiffOn_snd (fun _ hp ↦ hp.2)
  have hdCY : ContMDiffOn (IP.prod I) 𝓘(ℝ) 0
      (fun p : P × M ↦ mvfderiv I f p.2 (frozenConnection g p.1 Y p.2 (X p.2)))
      (univ ×ˢ U) := by
    intro p hp
    exact ((hf.contMDiffAt (hU.mem_nhds hp.2)).contMDiffAt_mvfderiv_apply (by simp)).comp
      p ((hCY p hp).contMDiffAt ((isOpen_univ.prod hU).mem_nhds hp)) |>.contMDiffWithinAt
  refine (hdXY.sub hdCY).congr fun p hp ↦ ?_
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g p.1).toRiemannianMetric⟩
  simpa only [frozenConnection] using (hessian_apply_eq_mvfderiv_sub p.2
    ((hf.contMDiffAt (hU.mem_nhds hp.2)).of_le (by simp)) X Y
    ((hY.contMDiffAt (hU.mem_nhds hp.2)).mdifferentiableAt (by simp)))

end TauCeti.Manifold
