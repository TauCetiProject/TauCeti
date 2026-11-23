/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Clean
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
boundaryless manifold, with `ker dq` equal to those excess directions. These are the data of a
clean composite `TauCeti.IsCleanComposite`, for which the descended endpoint map `j` is smooth and
immersive. It is a Lagrangian map (`TauCeti.IsCleanComposite.isLagrangianMap`), also when it is
not embedded, and if it is a topological embedding, it is a Lagrangian embedding
(`TauCeti.IsCleanComposite.isLagrangianEmbedding`). The result does not assume transversality,
zero excess, or smoothness of the descended map. It does require a smooth quotient with the stated
tangent property; a clean intersection alone does not make the global leaf space a manifold or its
image embedded.

The matching tangent-space condition is the one in `IsLagrangianMap.relComp`. Descent uses
local sections of the quotient submersion, rather than a choice of global section.

For three Lagrangian correspondences `f`, `g` and `k`, the intermediate clean composites of the
two groupings are therefore Lagrangian maps, so when both final composites are topological
embeddings they are Lagrangian correspondences `M₁ ⇝ M₄`, and the associativity theorem
`TauCeti.IsCleanComposite.exists_diffeomorph_assoc` identifies them up to a diffeomorphism of
their sources.

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

omit [I₁.Boundaryless] [I₃.Boundaryless] [KQ.Boundaryless] [IsManifold KQ ∞ Q] in
/-- **Clean composites of Lagrangian correspondences are Lagrangian.** The clean composite of two
smooth Lagrangian correspondences is a Lagrangian map for `pr₁*σ₁ - pr₂*σ₃`, also when it is not
a topological embedding. -/
theorem _root_.TauCeti.IsCleanComposite.isLagrangianMap
    (h : IsCleanComposite I₁ I₂ I₃ K₁ K₂ KC KQ f g a b q j)
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianMap K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianMap K₂ g)
    (hf : ContMDiff K₁ (I₁.prod I₂) ∞ f) (hg : ContMDiff K₂ (I₂.prod I₃) ∞ g) :
    (hσ₁.twistedProd hσ₃).IsLagrangianMap KQ j := by
  refine ((hσ₁.twistedProd hσ₃).isLagrangianMap_comp_submersion_iff h.isSubmersion h.surjective
    ((h.contMDiff hf hg).comp h.isSubmersion.contMDiff)).1 ?_
  rw [h.comp_eq]
  exact hfL.relComp (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃) hgL (hf.mdifferentiable (by simp))
    (hg.mdifferentiable (by simp)) (h.contMDiff_left.mdifferentiable (by simp))
    (h.contMDiff_right.mdifferentiable (by simp)) h.snd_eq_fst h.exists_mfderiv_eq

/-- **Clean composition with a smooth excess quotient.** A clean composite of two smooth
Lagrangian correspondences which is a topological embedding is a Lagrangian embedding, a
Lagrangian correspondence `M₁ ⇝ M₃`. In particular, smoothness and the immersion property of the
descended endpoint map are conclusions.

The excess condition is stated in the original correspondence coordinates. It allows nonzero
excess and does not assert existence of a smooth global quotient from cleanliness alone. -/
theorem _root_.TauCeti.IsCleanComposite.isLagrangianEmbedding
    (h : IsCleanComposite I₁ I₂ I₃ K₁ K₂ KC KQ f g a b q j)
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianMap K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianMap K₂ g)
    (hf : ContMDiff K₁ (I₁.prod I₂) ∞ f) (hg : ContMDiff K₂ (I₂.prod I₃) ∞ g)
    (hemb : Topology.IsEmbedding j) : (hσ₁.twistedProd hσ₃).IsLagrangianEmbedding KQ j :=
  ⟨h.isImmersion hf hg, hemb,
    h.isLagrangianMap (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃) hfL hgL hf hg⟩

end TauCeti.SmoothTwoForm.IsNondegenerate
