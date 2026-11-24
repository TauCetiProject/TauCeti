/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Diagonal.Orientation
import TauCeti.Topology.VectorBundle.Orientation.FiberwiseEquiv
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
import TauCeti.AlgebraicTopology.Cohomology.FundamentalClass

/-!
# Native clients of the diagonal normal comparison

The actual quotient normal fibre vanishes in dimension zero and is nontrivial in dimension one.
The smooth comparison also applies to a disconnected base. In dimension two, the transported
normal Euler class evaluates on the canonical smooth-to-homological fundamental class as the
tangent Euler class does. This uses the existing normalized Euler class and homological
orientation, without asserting a diagonal self-intersection or a product fundamental-class
calibration.
-/

public noncomputable section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti.Examples.DiagonalNormal

/-- The zero-dimensional real model. -/
abbrev ZeroModel := Fin 0 → ℝ
/-- A two-dimensional real model with its native product norm. -/
abbrev PlaneModel := Fin 2 → ℝ

/-- The genuine quotient normal fibre in dimension zero has just its zero vector. -/
theorem zero_normal_eq_zero
    (q : (SmoothEmbedding.diagonal (I := 𝓘(ℝ, ZeroModel)) (M := ZeroModel)).NormalSpace 0
      (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) : q = 0 := by
  apply (SmoothEmbedding.diagonalNormalEquiv (I := 𝓘(ℝ, ZeroModel)) 0).injective
  apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ZeroModel)).injective
  exact Subsingleton.elim _ _

-- The zero-dimensional quotient fibre has an actual H₀ local generator, obtained through the
-- native point-chart construction, with no assumed normal identification.
example : Nonempty (LocalOrientation
    ((SmoothEmbedding.diagonal (I := 𝓘(ℝ, ZeroModel)) (M := ZeroModel)).NormalSpace 0
      (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) 0 0) := by
  let f := (SmoothEmbedding.diagonalNormalEquiv (I := 𝓘(ℝ, ZeroModel)) (0 : ZeroModel)).trans
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ZeroModel))
  exact ⟨localOrientationOfZeroDimChart f.toHomeomorph.toOpenPartialHomeomorph
    (by simp) (by simp : finrank ℝ ZeroModel = 0)⟩

/-- The actual quotient normal fibre in dimension one is nontrivial. -/
theorem real_normal_nontrivial :
    Nontrivial ((SmoothEmbedding.diagonal (I := 𝓘(ℝ, ℝ)) (M := ℝ)).NormalSpace 0
      (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) := by
  have : Nontrivial (TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ)) :=
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).surjective.nontrivial
  exact (SmoothEmbedding.diagonalNormalEquiv (I := 𝓘(ℝ, ℝ)) 0).surjective.nontrivial

/-- The actual quotient normal fibre of the complex line has complex dimension one. -/
theorem complex_normal_finrank :
    finrank ℂ ((SmoothEmbedding.diagonal (I := 𝓘(ℂ, ℂ)) (M := ℂ)).NormalSpace 0
      (WithTop.coe_ne_zero.2 ENat.top_ne_zero)) = 1 :=
  ((SmoothEmbedding.diagonalNormalEquiv (I := 𝓘(ℂ, ℂ)) (0 : ℂ)).trans
    (NormedSpace.fromTangentSpace (𝕜 := ℂ) (0 : ℂ))).toLinearEquiv.finrank_eq.trans
      (Module.finrank_self ℂ)

-- The same native quotient and smooth bundle comparison are complex linear over ℂ.
example (v w : TangentSpace 𝓘(ℂ, ℂ) (0 : ℂ)) :
    (SmoothEmbedding.diagonalNormalEquiv (I := 𝓘(ℂ, ℂ)) 0).symm (w - v) =
      (SmoothEmbedding.diagonal (I := 𝓘(ℂ, ℂ))).normalClass 0
        (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
        ((TauCeti.Manifold.tangentSpaceProdEquiv (I := 𝓘(ℂ, ℂ)) (J := 𝓘(ℂ, ℂ)) (0, 0)).symm
          (v, w)) := by
  apply (SmoothEmbedding.diagonalNormalEquiv (I := 𝓘(ℂ, ℂ)) 0).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  -- The quotient uses the tangent instance at `diagonal 0`; the representative uses `(0,0)`.
  erw [SmoothEmbedding.diagonalNormalEquiv_normalClass, ContinuousLinearEquiv.apply_symm_apply]

example :
    letI := SmoothEmbedding.instTopologicalSpaceNormalBundle
      (SmoothEmbedding.diagonal (I := 𝓘(ℂ, ℂ)) (M := ℂ)) (K := ℂ)
        (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
    letI := SmoothEmbedding.normalSpaceFiberBundle
      (SmoothEmbedding.diagonal (I := 𝓘(ℂ, ℂ)) (M := ℂ)) (P := ℂ)
        (WithTop.coe_ne_zero.2 ENat.top_ne_zero) (by simp [Module.finrank_prod])
    Nonempty (TotalSpace ℂ
      ((SmoothEmbedding.diagonal (I := 𝓘(ℂ, ℂ)) (M := ℂ)).NormalSpace ·
        (WithTop.coe_ne_zero.2 ENat.top_ne_zero))
      ≃ₘ^∞⟮(𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ), (𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ)⟯ TangentBundle 𝓘(ℂ, ℂ) ℂ) :=
  ⟨SmoothEmbedding.diagonalNormalBundleDiffeomorph (I := 𝓘(ℂ, ℂ))⟩

-- The source is the native quotient bundle, including on a two-component manifold.
example :
    letI := SmoothEmbedding.instTopologicalSpaceNormalBundle
      (SmoothEmbedding.diagonal (I := 𝓘(ℝ, ℝ)) (M := ℝ ⊕ ℝ)) (K := ℝ)
        (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
    letI := SmoothEmbedding.normalSpaceFiberBundle
      (SmoothEmbedding.diagonal (I := 𝓘(ℝ, ℝ)) (M := ℝ ⊕ ℝ)) (P := ℝ)
        (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (by simp [Module.finrank_prod])
    Nonempty (TotalSpace ℝ
      ((SmoothEmbedding.diagonal (I := 𝓘(ℝ, ℝ)) (M := ℝ ⊕ ℝ)).NormalSpace ·
        (WithTop.coe_ne_zero.2 ENat.top_ne_zero))
      ≃ₘ^∞⟮(𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ), (𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)⟯
        TangentBundle 𝓘(ℝ, ℝ) (ℝ ⊕ ℝ)) :=
  ⟨SmoothEmbedding.diagonalNormalBundleDiffeomorph (I := 𝓘(ℝ, ℝ)) (M := ℝ ⊕ ℝ)⟩

-- The smooth comparison itself also retains the zero-dimensional base.
example :
    letI := SmoothEmbedding.instTopologicalSpaceNormalBundle
      (SmoothEmbedding.diagonal (I := 𝓘(ℝ, ZeroModel)) (M := ZeroModel)) (K := ZeroModel)
        (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
    letI := SmoothEmbedding.normalSpaceFiberBundle
      (SmoothEmbedding.diagonal (I := 𝓘(ℝ, ZeroModel)) (M := ZeroModel)) (P := ZeroModel)
        (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (by simp [Module.finrank_prod])
    Nonempty (TotalSpace ZeroModel
      ((SmoothEmbedding.diagonal (I := 𝓘(ℝ, ZeroModel)) (M := ZeroModel)).NormalSpace ·
        (WithTop.coe_ne_zero.2 ENat.top_ne_zero))
      ≃ₘ^∞⟮(𝓘(ℝ, ZeroModel)).prod 𝓘(ℝ, ZeroModel),
        (𝓘(ℝ, ZeroModel)).prod 𝓘(ℝ, ZeroModel)⟯ TangentBundle 𝓘(ℝ, ZeroModel) ZeroModel) :=
  ⟨SmoothEmbedding.diagonalNormalBundleDiffeomorph (I := 𝓘(ℝ, ZeroModel))⟩

-- Both rank-zero normal orientation signs survive the canonical quotient comparison.
example (o : Manifold.Orientation 𝓘(ℝ, ZeroModel) ZeroModel (Fin 0)) :
    letI := SmoothEmbedding.instTopologicalSpaceNormalBundle
      (SmoothEmbedding.diagonal (I := 𝓘(ℝ, ZeroModel)) (M := ZeroModel)) (K := ZeroModel)
        (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
    letI := SmoothEmbedding.normalSpaceFiberBundle
      (SmoothEmbedding.diagonal (I := 𝓘(ℝ, ZeroModel)) (M := ZeroModel)) (P := ZeroModel)
        (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (by simp [Module.finrank_prod])
    letI := SmoothEmbedding.normalSpaceVectorBundle
      (SmoothEmbedding.diagonal (I := 𝓘(ℝ, ZeroModel)) (M := ZeroModel)) (P := ZeroModel)
        (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (by simp [Module.finrank_prod])
    SmoothEmbedding.diagonalNormalOrientation o (0 : ZeroModel) ≠
      SmoothEmbedding.diagonalNormalOrientation (-o) (0 : ZeroModel) := by
  let := SmoothEmbedding.instTopologicalSpaceNormalBundle
    (SmoothEmbedding.diagonal (I := 𝓘(ℝ, ZeroModel)) (M := ZeroModel)) (K := ZeroModel)
      (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
  let := SmoothEmbedding.normalSpaceFiberBundle
    (SmoothEmbedding.diagonal (I := 𝓘(ℝ, ZeroModel)) (M := ZeroModel)) (P := ZeroModel)
      (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
    (by simp [Module.finrank_prod])
  let := SmoothEmbedding.normalSpaceVectorBundle
    (SmoothEmbedding.diagonal (I := 𝓘(ℝ, ZeroModel)) (M := ZeroModel)) (P := ZeroModel)
      (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
    (by simp [Module.finrank_prod])
  intro h
  have hh := congrArg (Orientation.map (Fin 0)
    (SmoothEmbedding.diagonalNormalEquiv (I := 𝓘(ℝ, ZeroModel)) (0 : ZeroModel)).toLinearEquiv) h
  rw [SmoothEmbedding.diagonalNormalOrientation_map,
    SmoothEmbedding.diagonalNormalOrientation_map, Manifold.Orientation.orientationAt_neg] at hh
  exact Module.Ray.ne_neg_self _ hh

section Euler

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace PlaneModel M] [IsManifold 𝓘(ℝ, PlaneModel) ∞ M]

-- The normalized Euler class is unchanged on the native normal bundle. Evaluate it on the
-- homological orientation actually obtained from the given smooth orientation.
example (o : Manifold.Orientation 𝓘(ℝ, PlaneModel) M (Fin 2)) :
    letI := SmoothEmbedding.instTopologicalSpaceNormalBundle
      (SmoothEmbedding.diagonal (I := 𝓘(ℝ, PlaneModel)) (M := M)) (K := PlaneModel)
        (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
    letI := SmoothEmbedding.normalSpaceFiberBundle
      (SmoothEmbedding.diagonal (I := 𝓘(ℝ, PlaneModel)) (M := M)) (P := PlaneModel)
        (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (by simp [Module.finrank_prod])
    letI := SmoothEmbedding.normalSpaceVectorBundle
      (SmoothEmbedding.diagonal (I := 𝓘(ℝ, PlaneModel)) (M := M)) (P := PlaneModel)
        (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
      (Nat.eq_sub_of_add_eq
        (Module.finrank_prod (R := ℝ) (M := PlaneModel) (M' := PlaneModel)).symm)
    (o.toHomologicalOrientation (by simp : finrank ℝ PlaneModel = 1 + 1)).evalFundamentalClass
        (by simp) (ModuleCat.of ℤ (ULift ℤ)) (ContinuousMap.id M)
        ((SmoothEmbedding.diagonalNormalOrientation o).eulerClass (by simp)) =
      (o.toHomologicalOrientation (by simp : finrank ℝ PlaneModel = 1 + 1)).evalFundamentalClass
        (by simp) (ModuleCat.of ℤ (ULift ℤ)) (ContinuousMap.id M)
        (o.toVectorBundleOrientation.eulerClass (by simp)) := by
  let := SmoothEmbedding.instTopologicalSpaceNormalBundle
    (SmoothEmbedding.diagonal (I := 𝓘(ℝ, PlaneModel)) (M := M)) (K := PlaneModel)
      (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
  let := SmoothEmbedding.normalSpaceFiberBundle
    (SmoothEmbedding.diagonal (I := 𝓘(ℝ, PlaneModel)) (M := M)) (P := PlaneModel)
      (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
    (by simp [Module.finrank_prod])
  let := SmoothEmbedding.normalSpaceVectorBundle
    (SmoothEmbedding.diagonal (I := 𝓘(ℝ, PlaneModel)) (M := M)) (P := PlaneModel)
      (WithTop.coe_ne_zero.2 ENat.top_ne_zero)
    (by simp [Module.finrank_prod])
  apply congrArg
    ((o.toHomologicalOrientation (by simp : finrank ℝ PlaneModel = 1 + 1)).evalFundamentalClass
      (by simp) (ModuleCat.of ℤ (ULift ℤ)) (ContinuousMap.id M))
  exact o.toVectorBundleOrientation.eulerClass_eq_of_fiberwise (by simp)
    (SmoothEmbedding.diagonalNormalOrientation o) (by simp)
    SmoothEmbedding.contMDiff_diagonalNormalEquiv.continuous
    (fun x ↦ (SmoothEmbedding.diagonalNormalOrientation_map o x).trans
      (o.toVectorBundleOrientation_apply x).symm)

end Euler

end TauCeti.Examples.DiagonalNormal
