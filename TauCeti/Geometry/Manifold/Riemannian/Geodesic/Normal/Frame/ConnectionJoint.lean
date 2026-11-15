/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Frame.Connection
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Dependence of the normal-frame connection matrix on its direction

The connection matrix in a normal orthonormal frame is linear in the tangent direction.
Expanding that direction in the orthonormal basis reduces joint regularity questions to
the already available smoothness of finitely many connection matrices on the normal
neighbourhood.
-/

public noncomputable section

open Bundle CovariantDerivative
open scoped ContDiff InnerProductSpace Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
  {p : M} {U : Set (TangentSpace I p)}

/-- The normal-frame connection matrix at a fixed point, as a linear function of the
initial tangent direction. -/
def normalFrameConnectionLinearMap
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (q : M) :
    TangentSpace I p →ₗ[ℝ] (TangentSpace I p →L[ℝ] TangentSpace I p) where
  toFun v := b.normalFrameConnectionOperator (U := U) v q
  map_add' v w := b.normalFrameConnectionOperator_add (U := U) v w q
  map_smul' c v := b.normalFrameConnectionOperator_smul (U := U) c v q

/-- Every normal-frame connection matrix is a finite sum of the matrices in the initial
orthonormal basis directions. -/
theorem normalFrameConnectionOperator_eq_sum
    (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (v : TangentSpace I p) (q : M) :
    b.normalFrameConnectionOperator (U := U) v q =
      ∑ i, ⟪b i, v⟫_ℝ • b.normalFrameConnectionOperator (U := U) (b i) q := by
  let L := normalFrameConnectionLinearMap (U := U) b q
  calc
    _ = L v := rfl
    _ = L (∑ i, ⟪b i, v⟫_ℝ • b i) := by rw [b.sum_repr']
    _ = ∑ i, ⟪b i, v⟫_ℝ • b.normalFrameConnectionOperator (U := U) (b i) q := by
      simpa only [map_sum, map_smul] using
        (show ∑ i, ⟪b i, v⟫_ℝ • L (b i) =
          ∑ i, ⟪b i, v⟫_ℝ • b.normalFrameConnectionOperator (U := U) (b i) q from rfl)

variable [I.Boundaryless] [T2Space M]

omit [I.Boundaryless] [T2Space M] in
/-- The normal-frame connection matrix is jointly smooth in the tangent direction and the
base point, on the product of the tangent space and the normal neighbourhood. -/
theorem IsNormalDomain.contMDiffOn_normalFrameConnectionOperator_joint
    (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) :
    ContMDiffOn (𝓘(ℝ, TangentSpace I p).prod I)
      𝓘(ℝ, TangentSpace I p →L[ℝ] TangentSpace I p) ∞
      (fun x : TangentSpace I p × M ↦
        b.normalFrameConnectionOperator (U := U) x.1 x.2)
      (Set.univ ×ˢ (riemannianExp I M p '' U)) := by
  have heq : (fun x : TangentSpace I p × M ↦
      b.normalFrameConnectionOperator (U := U) x.1 x.2) =
      (fun x ↦ ∑ i, ⟪b i, x.1⟫_ℝ •
        b.normalFrameConnectionOperator (U := U) (b i) x.2) := by
    funext x
    exact normalFrameConnectionOperator_eq_sum b x.1 x.2
  rw [heq]
  apply contMDiffOn_finsetSum
  intro i _
  have hconst : ContDiff ℝ ∞ (fun _ : TangentSpace I p ↦ b i) := contDiff_const
  have hid : ContDiff ℝ ∞ (fun v : TangentSpace I p ↦ v) := contDiff_id
  have hs₀ : ContDiff ℝ ∞
      (fun v : TangentSpace I p ↦ ⟪b i, v⟫_ℝ) :=
    hconst.inner ℝ hid
  have hs : ContMDiff 𝓘(ℝ, TangentSpace I p) 𝓘(ℝ) ∞
      (fun v : TangentSpace I p ↦ ⟪b i, v⟫_ℝ) :=
    hs₀.contMDiff
  have hscalar : ContMDiffOn (𝓘(ℝ, TangentSpace I p).prod I) 𝓘(ℝ) ∞
      (fun x : TangentSpace I p × M ↦ ⟪b i, x.1⟫_ℝ)
      (Set.univ ×ˢ (riemannianExp I M p '' U)) :=
    (hs.contMDiffOn (s := Set.univ)).comp contMDiffOn_fst (fun _ _ ↦ by simp)
  have hop : ContMDiffOn (𝓘(ℝ, TangentSpace I p).prod I)
      𝓘(ℝ, TangentSpace I p →L[ℝ] TangentSpace I p) ∞
      (fun x : TangentSpace I p × M ↦
        b.normalFrameConnectionOperator (U := U) (b i) x.2)
      (Set.univ ×ˢ (riemannianExp I M p '' U)) :=
    (h.contMDiffOn_normalFrameConnectionOperator b (b i)).comp contMDiffOn_snd
      (fun _ hx ↦ hx.2)
  exact hscalar.smul hop

/-- The linear parallel-transport equation has coefficients jointly smooth in its radial
endpoint and time wherever the corresponding radial point lies in the normal domain. -/
theorem IsNormalDomain.contMDiffOn_radialConnectionOperator_joint
    (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) :
    ContMDiffOn (𝓘(ℝ, TangentSpace I p).prod 𝓘(ℝ))
      𝓘(ℝ, TangentSpace I p →L[ℝ] TangentSpace I p) ∞
      (fun x : TangentSpace I p × ℝ ↦
        b.normalFrameConnectionOperator (U := U) x.1
          (riemannianExp I M p (x.2 • x.1)))
      {x | x.2 • x.1 ∈ U} := by
  have hmul : ContMDiffOn (𝓘(ℝ, TangentSpace I p).prod 𝓘(ℝ))
      𝓘(ℝ, TangentSpace I p) ∞
      (fun x : TangentSpace I p × ℝ ↦ x.2 • x.1) {x | x.2 • x.1 ∈ U} :=
    contMDiffOn_snd.smul contMDiffOn_fst
  have hexp : ContMDiffOn (𝓘(ℝ, TangentSpace I p).prod 𝓘(ℝ)) I ∞
      (fun x : TangentSpace I p × ℝ ↦ riemannianExp I M p (x.2 • x.1))
      {x | x.2 • x.1 ∈ U} :=
    (contMDiffOn_riemannianExp p).comp hmul (fun x hx ↦ h.subset_expDomain hx)
  have hpair : ContMDiffOn (𝓘(ℝ, TangentSpace I p).prod 𝓘(ℝ))
      (𝓘(ℝ, TangentSpace I p).prod I) ∞
      (fun x : TangentSpace I p × ℝ ↦
        (x.1, riemannianExp I M p (x.2 • x.1))) {x | x.2 • x.1 ∈ U} :=
    contMDiffOn_fst.prodMk hexp
  exact (h.contMDiffOn_normalFrameConnectionOperator_joint b).comp hpair
    (fun x hx ↦ ⟨Set.mem_univ _, Set.mem_image_of_mem _ hx⟩)

end TauCeti.Manifold
