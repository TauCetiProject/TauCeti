/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.Composition.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Submersion

/-!
# Clean composition through a smooth excess quotient

Let `f : L₁ → M₁ × M₂` and `g : L₂ → M₂ × M₃` be smooth Lagrangian correspondences.
A parametrization `C` of a clean matching manifold, with projections `a : C → L₁` and
`b : C → L₂`, maps onto all tangent pairs whose middle differentials match. The endpoint map is
`c ↦ ((f (a c)).1, (g (b c)).2)`. Its excess tangent vectors are exactly those whose two
outer differentials vanish.

Suppose this endpoint map factors through a surjective smooth submersion `q : C → Q` onto a
boundaryless manifold, with `ker dq` equal to those excess directions. Then the descended
endpoint map is smooth and immersive. If it is a topological embedding, it is a Lagrangian
embedding. The result does not assume transversality, zero excess, or smoothness of the
descended map. It does require a smooth quotient with the stated tangent property; a clean
intersection alone does not make the global leaf space a manifold or its image embedded.

The matching tangent-space condition is the one in `IsLagrangianMap.relComp`. Descent uses
local sections of the quotient submersion, rather than a choice of global section.

## References

* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, Section 3.4.
-/

public section

open Function Manifold
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E₁ H₁ M₁ E₂ H₂ M₂ E₃ H₃ M₃ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁} [I₁.Boundaryless]
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [FiniteDimensional ℝ E₃]
  [TopologicalSpace H₃] {I₃ : ModelWithCorners ℝ E₃ H₃} [I₃.Boundaryless]
  [TopologicalSpace M₃] [ChartedSpace H₃ M₃] [IsManifold I₃ ∞ M₃]
  {σ₁ : SmoothTwoForm I₁ M₁} {σ₂ : SmoothTwoForm I₂ M₂} {σ₃ : SmoothTwoForm I₃ M₃}
  {hσ₁ : σ₁.IsNondegenerate} {hσ₂ : σ₂.IsNondegenerate} {hσ₃ : σ₃.IsNondegenerate}

variable {EL₁ HL₁ L₁ EL₂ HL₂ L₂ EC HC C EQ HQ Q : Type*}
  [NormedAddCommGroup EL₁] [NormedSpace ℝ EL₁] [TopologicalSpace HL₁]
  {K₁ : ModelWithCorners ℝ EL₁ HL₁} [TopologicalSpace L₁] [ChartedSpace HL₁ L₁]
  [NormedAddCommGroup EL₂] [NormedSpace ℝ EL₂] [TopologicalSpace HL₂]
  {K₂ : ModelWithCorners ℝ EL₂ HL₂} [TopologicalSpace L₂] [ChartedSpace HL₂ L₂]
  [NormedAddCommGroup EC] [NormedSpace ℝ EC] [TopologicalSpace HC]
  {KC : ModelWithCorners ℝ EC HC} [KC.Boundaryless]
  [TopologicalSpace C] [ChartedSpace HC C]
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
  {KQ : ModelWithCorners ℝ EQ HQ} [KQ.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold KQ ∞ Q]
  {f : L₁ → M₁ × M₂} {g : L₂ → M₂ × M₃} {a : C → L₁} {b : C → L₂}
  {q : C → Q} {j : Q → M₁ × M₃}

/-- **Clean composition with a smooth excess quotient.** A smooth matching manifold
parametrizes the full tangent fibre product. If its endpoint map factors through a surjective
smooth submersion removing exactly the excess tangent directions, and the descended endpoint
map is a topological embedding, then it is a Lagrangian embedding. In particular, smoothness
and the immersion property of the descended endpoint map are conclusions.

The kernel condition states the excess in the original correspondence coordinates. It allows
nonzero excess and does not assert existence of a smooth global quotient from cleanliness alone. -/
theorem IsLagrangianMap.isLagrangianEmbedding_relComp_of_submersion
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianMap K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianMap K₂ g)
    (hf : ContMDiff K₁ (I₁.prod I₂) ∞ f) (hg : ContMDiff K₂ (I₂.prod I₃) ∞ g)
    (ha : ContMDiff KC K₁ ∞ a) (hb : ContMDiff KC K₂ ∞ b)
    (hab : ∀ c, (f (a c)).2 = (g (b c)).1)
    (hfib : ∀ c u w, (mfderiv K₁ (I₁.prod I₂) f (a c) u).2 =
        (mfderiv K₂ (I₂.prod I₃) g (b c) w).1 →
      ∃ ξ, mfderiv KC K₁ a c ξ = u ∧ mfderiv KC K₂ b c ξ = w)
    (hq : IsSubmersion KC KQ ∞ q) (hsurj : Surjective q)
    (hfactor : j ∘ q = fun c ↦ ((f (a c)).1, (g (b c)).2))
    (hexc : ∀ c ξ, mfderiv KC KQ q c ξ = 0 ↔
      (mfderiv K₁ (I₁.prod I₂) f (a c) (mfderiv KC K₁ a c ξ)).1 = 0 ∧
        (mfderiv K₂ (I₂.prod I₃) g (b c) (mfderiv KC K₂ b c ξ)).2 = 0)
    (hemb : Topology.IsEmbedding j) : (hσ₁.twistedProd hσ₃).IsLagrangianEmbedding KQ j := by
  have hL : (hσ₁.twistedProd hσ₃).IsLagrangianMap KC (j ∘ q) := by
    rw [hfactor]
    exact hfL.relComp (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃) hgL
      (hf.mdifferentiable (by simp)) (hg.mdifferentiable (by simp))
      (ha.mdifferentiable (by simp)) (hb.mdifferentiable (by simp)) hab hfib
  refine hL.isLagrangianEmbedding_of_comp_submersion hq hsurj ?_ ?_ hemb
  · rw [hfactor]
    exact (hf.fst.comp ha).prodMk (hg.snd.comp hb)
  · intro c
    ext ξ
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_coe, hfactor,
      (hf.mdifferentiable (by simp) (a c)).mfderiv_prodMk_fst_snd_comp_apply
        (hg.mdifferentiable (by simp) (b c)) (ha.mdifferentiable (by simp) c)
        (hb.mdifferentiable (by simp) c)]
    -- The zero tangent vector of the product has zero in both coordinate tangent spaces.
    constructor
    · intro h
      exact (hexc c ξ).mpr ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · intro h
      exact Prod.ext ((hexc c ξ).mp h).1 ((hexc c ξ).mp h).2

end TauCeti.SmoothTwoForm.IsNondegenerate
