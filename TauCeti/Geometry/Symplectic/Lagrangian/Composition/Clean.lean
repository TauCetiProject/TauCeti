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

Let `f : L₁ → M₁ × M₂` and `g : L₂ → M₂ × M₃` be Lagrangian correspondences.
A parametrization `C` of a clean matching manifold, with projections `a : C → L₁` and
`b : C → L₂`, maps onto all tangent pairs whose middle differentials match. The endpoint map is
`c ↦ ((f (a c)).1, (g (b c)).2)`. Its excess tangent vectors are those whose two outer
differentials vanish.

Suppose this endpoint map factors as `j ∘ q` through a surjective submersion `q : C → Q`. Then
`j` is a Lagrangian map (`IsLagrangianMap.relComp_of_isSubmersion`); this needs only
differentiability of the data. If the data are smooth, the models of `M₁`, `M₃` and `Q` are
boundaryless, and `ker dq` contains the excess directions, then `j` is a smooth immersion
(`TauCeti.isImmersion_relComp_of_isSubmersion`), hence a Lagrangian immersion when `Q` is
nonempty (`IsLagrangianMap.isLagrangianImmersion_relComp_of_isSubmersion`). The embedded case is
`IsLagrangianMap.isLagrangianEmbedding_relComp_of_isSubmersion` in
`TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Composition`.

None of these results assumes transversality, zero excess, or smoothness of the descended map.
They do require a quotient manifold with the stated tangent property; a clean intersection alone
does not make the global leaf space a manifold. The matching tangent-space condition is the one
in `IsLagrangianMap.relComp`. Descent uses local sections of the quotient submersion, rather than
a choice of global section.

## References

* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, Section 3.4.
-/

public section

open Function Manifold
open scoped Manifold ContDiff

namespace TauCeti

variable {E₁ H₁ M₁ E₂ H₂ M₂ E₃ H₃ M₃ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [FiniteDimensional ℝ E₃]
  [TopologicalSpace H₃] {I₃ : ModelWithCorners ℝ E₃ H₃}
  [TopologicalSpace M₃] [ChartedSpace H₃ M₃] [IsManifold I₃ ∞ M₃]

variable {EL₁ HL₁ L₁ EL₂ HL₂ L₂ EC HC C EQ HQ Q : Type*}
  [NormedAddCommGroup EL₁] [NormedSpace ℝ EL₁] [TopologicalSpace HL₁]
  {K₁ : ModelWithCorners ℝ EL₁ HL₁} [TopologicalSpace L₁] [ChartedSpace HL₁ L₁]
  [NormedAddCommGroup EL₂] [NormedSpace ℝ EL₂] [TopologicalSpace HL₂]
  {K₂ : ModelWithCorners ℝ EL₂ HL₂} [TopologicalSpace L₂] [ChartedSpace HL₂ L₂]
  [NormedAddCommGroup EC] [NormedSpace ℝ EC] [TopologicalSpace HC]
  {KC : ModelWithCorners ℝ EC HC} [KC.Boundaryless]
  [TopologicalSpace C] [ChartedSpace HC C]
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
  {KQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
  {f : L₁ → M₁ × M₂} {g : L₂ → M₂ × M₃} {a : C → L₁} {b : C → L₂}
  {q : C → Q} {j : Q → M₁ × M₃}

omit [IsManifold I₂ ∞ M₂] [FiniteDimensional ℝ E₂] in
/-- **The descended endpoint map is an immersion.** If the endpoint map
`c ↦ ((f (a c)).1, (g (b c)).2)` of smooth data factors as `j ∘ q` through a surjective smooth
submersion with boundaryless models, and every excess direction, killed by both outer
differentials, lies in `ker dq`, then `j` is a smooth immersion. No symplectic or fibre-product
hypothesis is needed. -/
theorem isImmersion_relComp_of_isSubmersion [I₁.Boundaryless] [I₃.Boundaryless]
    [KQ.Boundaryless] [IsManifold KQ ∞ Q]
    (hf : ContMDiff K₁ (I₁.prod I₂) ∞ f) (hg : ContMDiff K₂ (I₂.prod I₃) ∞ g)
    (ha : ContMDiff KC K₁ ∞ a) (hb : ContMDiff KC K₂ ∞ b)
    (hq : IsSubmersion KC KQ ∞ q) (hsurj : Surjective q)
    (hfactor : j ∘ q = fun c ↦ ((f (a c)).1, (g (b c)).2))
    (hexc : ∀ c ξ, (mfderiv K₁ (I₁.prod I₂) f (a c) (mfderiv KC K₁ a c ξ)).1 = 0 →
      (mfderiv K₂ (I₂.prod I₃) g (b c) (mfderiv KC K₂ b c ξ)).2 = 0 →
        mfderiv KC KQ q c ξ = 0) :
    IsImmersion KQ (I₁.prod I₃) ∞ j := by
  refine (hq.isImmersion_iff_ker_mfderiv_comp_le hsurj (by simp) le_rfl).mpr
    ⟨?_, fun c ξ hξ ↦ ?_⟩
  · rw [hfactor]
    exact (hf.fst.comp ha).prodMk (hg.snd.comp hb)
  · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hfactor,
      (hf.mdifferentiable (by simp) (a c)).mfderiv_prodMk_fst_snd_comp_apply
        (hg.mdifferentiable (by simp) (b c)) (ha.mdifferentiable (by simp) c)
        (hb.mdifferentiable (by simp) c)] at hξ
    -- The zero tangent vector of the product has zero in both coordinate tangent spaces.
    exact LinearMap.mem_ker.mpr (hexc c ξ (congrArg Prod.fst hξ) (congrArg Prod.snd hξ))

namespace SmoothTwoForm.IsNondegenerate

variable {σ₁ : SmoothTwoForm I₁ M₁} {σ₂ : SmoothTwoForm I₂ M₂} {σ₃ : SmoothTwoForm I₃ M₃}
  {hσ₁ : σ₁.IsNondegenerate} {hσ₂ : σ₂.IsNondegenerate} {hσ₃ : σ₃.IsNondegenerate}

/-- **Clean composition descends to a Lagrangian map.** Under the hypotheses of
`IsLagrangianMap.relComp`, if the endpoint map factors as `j ∘ q` through a surjective
submersion `q`, then `j` is a Lagrangian map. Only differentiability of the data is assumed;
no excess, immersion or smoothness condition on `j` is needed. -/
theorem IsLagrangianMap.relComp_of_isSubmersion {n : ℕ∞ω}
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianMap K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianMap K₂ g)
    (hf : MDifferentiable K₁ (I₁.prod I₂) f) (hg : MDifferentiable K₂ (I₂.prod I₃) g)
    (ha : MDifferentiable KC K₁ a) (hb : MDifferentiable KC K₂ b)
    (hab : ∀ c, (f (a c)).2 = (g (b c)).1)
    (hfib : ∀ c u w, (mfderiv K₁ (I₁.prod I₂) f (a c) u).2 =
        (mfderiv K₂ (I₂.prod I₃) g (b c) w).1 →
      ∃ ξ, mfderiv KC K₁ a c ξ = u ∧ mfderiv KC K₂ b c ξ = w)
    (hq : IsSubmersion KC KQ n q) (hn : n ≠ 0) (hsurj : Surjective q)
    (hfactor : j ∘ q = fun c ↦ ((f (a c)).1, (g (b c)).2)) :
    (hσ₁.twistedProd hσ₃).IsLagrangianMap KQ j := by
  refine ((hσ₁.twistedProd hσ₃).isLagrangianMap_comp_isSubmersion_iff hq hn hsurj).mp ?_
  rw [hfactor]
  exact hfL.relComp (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃) hgL hf hg ha hb hab hfib

/-- **Clean composition with a smooth excess quotient, immersed case.** Under the hypotheses
of `IsLagrangianMap.relComp` for smooth data, if the endpoint map factors as `j ∘ q` through a
surjective smooth submersion onto a nonempty manifold `Q`, with boundaryless models, whose
kernel contains every excess direction, then `j` is a Lagrangian immersion. Self-intersections
of `j` are allowed. -/
theorem IsLagrangianMap.isLagrangianImmersion_relComp_of_isSubmersion [I₁.Boundaryless]
    [I₃.Boundaryless] [KQ.Boundaryless] [IsManifold KQ ∞ Q] [Nonempty Q]
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
    (hexc : ∀ c ξ, (mfderiv K₁ (I₁.prod I₂) f (a c) (mfderiv KC K₁ a c ξ)).1 = 0 →
      (mfderiv K₂ (I₂.prod I₃) g (b c) (mfderiv KC K₂ b c ξ)).2 = 0 →
        mfderiv KC KQ q c ξ = 0) :
    (hσ₁.twistedProd hσ₃).IsLagrangianImmersion KQ j :=
  isLagrangianImmersion_iff.mpr
    ⟨isImmersion_relComp_of_isSubmersion hf hg ha hb hq hsurj hfactor hexc,
      hfL.relComp_of_isSubmersion (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃) hgL
        (hf.mdifferentiable (by simp)) (hg.mdifferentiable (by simp))
        (ha.mdifferentiable (by simp)) (hb.mdifferentiable (by simp)) hab hfib hq (by simp) hsurj
        hfactor⟩

end SmoothTwoForm.IsNondegenerate

end TauCeti
