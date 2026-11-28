/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import Mathlib.Topology.VectorBundle.Riemannian
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative

/-!
# Riemannian metrics on finite-dimensional fibres

A `Bundle.RiemannianMetric` on a family of topological vector spaces `E b` is a family of inner
products on the fibres which defines their given topology: besides symmetry and positivity, its
quadratic forms must be continuous at `0` and have von Neumann bounded unit balls. When every
fibre is a finite-dimensional Hausdorff topological vector space, these two topological conditions
are automatic: a positive definite symmetric bilinear form on such a space is, in suitable linear
coordinates, the Euclidean inner product, and linear maps between finite-dimensional Hausdorff
spaces are continuous
(`LinearMap.BilinForm.exists_continuousLinearEquiv_euclideanSpace_apply_self`). So any family
of positive definite symmetric bilinear forms is a Riemannian metric
(`Bundle.RiemannianMetric.ofFiniteDimensional`), and conditions on the inner products of
Riemannian metrics reduce to conditions on positive definite symmetric forms, fibre by fibre
(`Bundle.RiemannianMetric.exists_forall_toBilinForm_inner_iff`) or at a single fibre
(`Bundle.RiemannianMetric.exists_toBilinForm_inner_iff`).

This applies for instance to fibres that carry a topology but no norm, such as the normal spaces
of an embedding and their subspaces, where it gives fibre norms compatible with the existing
topology. For submodule fibres, which already carry their own topology instance, these norms must
be installed directly through `InnerProductSpace.Core.toNormedAddCommGroupOfTopology`;
`Bundle.RiemannianBundle` serves only fibres where its scoped norm instance applies.
-/

public section

noncomputable section

namespace Bundle.RiemannianMetric

variable {B : Type*} {E : B → Type*} [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousSMul ℝ (E b)]
  [∀ b, FiniteDimensional ℝ (E b)] [∀ b, T2Space (E b)]

/-- **A Riemannian metric on finite-dimensional fibres** from a family of positive definite
symmetric bilinear forms `φ b` on the fibres. Since the fibres are finite-dimensional Hausdorff
topological vector spaces, the inner products `φ b` define their topology. -/
def ofFiniteDimensional (φ : ∀ b, LinearMap.BilinForm ℝ (E b))
    (hsymm : ∀ b, LinearMap.BilinForm.IsSymm (φ b)) (hpos : ∀ b (v : E b), v ≠ 0 → 0 < φ b v v) :
    RiemannianMetric E where
  inner b := (φ b).toContinuousBilinearMap
  symm b v w := by simpa using (hsymm b).eq v w
  pos b v hv := by simpa using hpos b v hv
  continuousAt b := by
    obtain ⟨e, he⟩ :=
      LinearMap.BilinForm.exists_continuousLinearEquiv_euclideanSpace_apply_self (hsymm b)
        (hpos b)
    simp only [LinearMap.toContinuousBilinearMap_apply, he]
    exact ((continuous_norm.comp e.symm.continuous).pow 2).continuousAt
  isVonNBounded b := by
    obtain ⟨e, he⟩ :=
      LinearMap.BilinForm.exists_continuousLinearEquiv_euclideanSpace_apply_self (hsymm b)
        (hpos b)
    -- The unit ball of `φ b` is the image of the Euclidean unit ball.
    have : {v : E b | (φ b).toContinuousBilinearMap v v < 1} =
        (e : EuclideanSpace ℝ (Fin (Module.finrank ℝ (E b))) →L[ℝ] E b) '' Metric.ball 0 1 := by
      ext v
      simp only [Set.mem_ofPred_eq, LinearMap.toContinuousBilinearMap_apply, he,
        sq_lt_one_iff₀ (norm_nonneg _), ContinuousLinearEquiv.coe_coe, Set.mem_image,
        Metric.mem_ball, dist_zero_right]
      exact ⟨fun h ↦ ⟨_, h, e.apply_symm_apply v⟩, by rintro ⟨x, hx, rfl⟩; simpa using hx⟩
    rw [this]
    exact (NormedSpace.isVonNBounded_ball ℝ _ 1).image _

/-- The inner products of `Bundle.RiemannianMetric.ofFiniteDimensional φ` are the forms `φ b`. -/
@[simp]
theorem ofFiniteDimensional_inner (φ : ∀ b, LinearMap.BilinForm ℝ (E b))
    (hsymm : ∀ b, LinearMap.BilinForm.IsSymm (φ b)) (hpos : ∀ b (v : E b), v ≠ 0 → 0 < φ b v v)
    (b : B) (v w : E b) : (ofFiniteDimensional φ hsymm hpos).inner b v w = φ b v w :=
  (rfl)

/-- The bilinear forms of `Bundle.RiemannianMetric.ofFiniteDimensional φ` are the forms `φ b`. -/
@[simp]
theorem toBilinForm_inner_ofFiniteDimensional (φ : ∀ b, LinearMap.BilinForm ℝ (E b))
    (hsymm : ∀ b, LinearMap.BilinForm.IsSymm (φ b)) (hpos : ∀ b (v : E b), v ≠ 0 → 0 < φ b v v)
    (b : B) : ((ofFiniteDimensional φ hsymm hpos).inner b).toBilinForm = φ b :=
  LinearMap.ext₂ fun _ _ ↦ rfl

/-- **Riemannian metrics on finite-dimensional fibres are families of positive definite forms.**
A family of conditions `P b` on bilinear forms of the fibres is met by the inner products of some
Riemannian metric exactly when each `P b` is met by some positive definite symmetric form. -/
theorem exists_forall_toBilinForm_inner_iff (P : ∀ b, LinearMap.BilinForm ℝ (E b) → Prop) :
    (∃ g : RiemannianMetric E, ∀ b, P b (g.inner b).toBilinForm) ↔
      ∀ b, ∃ φ : LinearMap.BilinForm ℝ (E b), φ.IsSymm ∧ (∀ v, v ≠ 0 → 0 < φ v v) ∧ P b φ := by
  constructor
  · rintro ⟨g, hg⟩ b
    exact ⟨_, LinearMap.BilinForm.isSymm_def.mpr (g.symm b), g.pos b, hg b⟩
  · intro h
    choose φ hsymm hpos hP using h
    exact ⟨ofFiniteDimensional φ hsymm hpos, fun b ↦ by simpa using hP b⟩

/-- **The inner products of Riemannian metrics on one finite-dimensional fibre** are exactly the
positive definite symmetric forms on it, as soon as some Riemannian metric exists: a condition `P`
on bilinear forms of `E b` is met by the inner product at `b` of some Riemannian metric exactly
when it is met by some positive definite symmetric form. -/
theorem exists_toBilinForm_inner_iff [Nonempty (RiemannianMetric E)] (b : B)
    (P : LinearMap.BilinForm ℝ (E b) → Prop) :
    (∃ g : RiemannianMetric E, P (g.inner b).toBilinForm) ↔
      ∃ φ : LinearMap.BilinForm ℝ (E b), φ.IsSymm ∧ (∀ v, v ≠ 0 → 0 < φ v v) ∧ P φ := by
  refine ⟨fun ⟨g, hg⟩ ↦ ⟨_, LinearMap.BilinForm.isSymm_def.mpr (g.symm b), g.pos b, hg⟩, ?_⟩
  rintro ⟨φ, hsymm, hpos, hP⟩
  classical
  obtain ⟨g⟩ := ‹Nonempty (RiemannianMetric E)›
  -- Replace the inner product of `g` at `b` by `φ`.
  obtain ⟨g', hg'⟩ := (exists_forall_toBilinForm_inner_iff fun c ψ ↦
    ψ = Function.update (fun c ↦ (g.inner c).toBilinForm) b φ c).mpr fun c ↦ by
    rcases eq_or_ne c b with rfl | hc
    · exact ⟨φ, hsymm, hpos, by simp⟩
    · exact ⟨(g.inner c).toBilinForm, LinearMap.BilinForm.isSymm_def.mpr (g.symm c), g.pos c,
        by simp [hc]⟩
  exact ⟨g', by simpa [hg' b] using hP⟩

end Bundle.RiemannianMetric
