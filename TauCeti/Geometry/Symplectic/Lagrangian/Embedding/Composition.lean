/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.Composition.Clean
public import TauCeti.Geometry.Symplectic.Lagrangian.Composition.Transverse
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Basic
import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Composition of embedded Lagrangian correspondences

Let `f : L₁ → M₁ × M₂` and `g : L₂ → M₂ × M₃` be Lagrangian maps for the twisted products, and let
`a : C → L₁`, `b : C → L₂` present their fibre product as in
`TauCeti.Geometry.Symplectic.Lagrangian.Composition.Basic`. When the composite map
`h c = ((f (a c)).1, (g (b c)).2)` is a smooth embedding, it is a Lagrangian correspondence
`M₁ ⇝ M₃`
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.isLagrangianEmbedding_relComp`).

When `x ↦ (f x).2` and `y ↦ (g y).1` are transverse, the fibre product itself is a manifold
(`TauCeti.transverseFiberProductChartedSpace`), and a transverse composite without excess that is
a topological embedding is a Lagrangian correspondence `M₁ ⇝ M₃`
(`IsLagrangianMap.isLagrangianEmbedding_relComp_transverseFiberProduct`, building on
`TauCeti.Geometry.Symplectic.Lagrangian.Composition.Transverse`). For Lagrangian immersions
transversality already removes the excess, so the transverse composite is a Lagrangian
correspondence exactly when it is a topological embedding
(`IsLagrangianImmersion.isLagrangianEmbedding_relComp_transverseFiberProduct_iff`). The
composite need not be injective, even for embedded `f` and `g`, so the embedding hypothesis is
kept separate.

For a clean composition with excess, the composite may instead factor as `j ∘ q` through a
surjective smooth submersion `q` whose kernel contains every excess direction. Then `j` is a
Lagrangian correspondence `M₁ ⇝ M₃` exactly when it is a topological embedding
(`IsLagrangianMap.isLagrangianEmbedding_relComp_of_isSubmersion`, building on
`TauCeti.Geometry.Symplectic.Lagrangian.Composition.Clean`).

## References

* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, Section 3.4.
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

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
  {σ₁ : SmoothTwoForm I₁ M₁} {σ₂ : SmoothTwoForm I₂ M₂} {σ₃ : SmoothTwoForm I₃ M₃}
  {hσ₁ : σ₁.IsNondegenerate} {hσ₂ : σ₂.IsNondegenerate} {hσ₃ : σ₃.IsNondegenerate}

variable {EL₁ HL₁ L₁ EL₂ HL₂ L₂ EC HC C : Type*}
  [NormedAddCommGroup EL₁] [NormedSpace ℝ EL₁] [TopologicalSpace HL₁]
  {K₁ : ModelWithCorners ℝ EL₁ HL₁} [TopologicalSpace L₁] [ChartedSpace HL₁ L₁]
  [NormedAddCommGroup EL₂] [NormedSpace ℝ EL₂] [TopologicalSpace HL₂]
  {K₂ : ModelWithCorners ℝ EL₂ HL₂} [TopologicalSpace L₂] [ChartedSpace HL₂ L₂]
  [NormedAddCommGroup EC] [NormedSpace ℝ EC] [TopologicalSpace HC]
  {KC : ModelWithCorners ℝ EC HC} [TopologicalSpace C] [ChartedSpace HC C]
  {f : L₁ → M₁ × M₂} {g : L₂ → M₂ × M₃} {a : C → L₁} {b : C → L₂}

/-- **Composition of Lagrangian correspondences, embedded case.** Under the hypotheses of
`IsLagrangianMap.relComp`, if the composite `c ↦ ((f (a c)).1, (g (b c)).2)` is moreover a smooth
embedding, it is a Lagrangian correspondence `M₁ ⇝ M₃`. -/
theorem IsLagrangianMap.isLagrangianEmbedding_relComp
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianMap K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianMap K₂ g) (hf : MDifferentiable K₁ (I₁.prod I₂) f)
    (hg : MDifferentiable K₂ (I₂.prod I₃) g) (ha : MDifferentiable KC K₁ a)
    (hb : MDifferentiable KC K₂ b) (hab : ∀ c, (f (a c)).2 = (g (b c)).1)
    (hfib : ∀ c u w, (mfderiv K₁ (I₁.prod I₂) f (a c) u).2 =
        (mfderiv K₂ (I₂.prod I₃) g (b c) w).1 →
      ∃ ξ, mfderiv KC K₁ a c ξ = u ∧ mfderiv KC K₂ b c ξ = w)
    (hemb : Manifold.IsSmoothEmbedding KC (I₁.prod I₃) ∞
      (fun c ↦ ((f (a c)).1, (g (b c)).2))) :
    (hσ₁.twistedProd hσ₃).IsLagrangianEmbedding KC (fun c ↦ ((f (a c)).1, (g (b c)).2)) :=
  (isLagrangianEmbedding_iff_of_isSmoothEmbedding hemb).mpr
    (hfL.relComp (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃) hgL hf hg ha hb hab hfib)

section Transverse

variable [I₂.Boundaryless] [FiniteDimensional ℝ EL₁] [K₁.Boundaryless] [IsManifold K₁ ∞ L₁]
  [FiniteDimensional ℝ EL₂] [K₂.Boundaryless] [IsManifold K₂ ∞ L₂]

/-- The model of the transverse fibre product `L₁ ×_{M₂} L₂`, of dimension
`dim L₁ + dim L₂ - dim M₂`. -/
local notation "KF" => 𝓘(ℝ, Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ)

variable (hf : ContMDiff K₁ (I₁.prod I₂) ∞ f) (hg : ContMDiff K₂ (I₂.prod I₃) ∞ g)
  (htrans : ∀ p : L₁ × L₂, (f p.1).2 = (g p.2).1 →
    (mfderiv K₁ I₂ (fun x ↦ (f x).2) p.1).range ⊔
      (((tangentSpaceCast I₂ (g p.2).1 (f p.1).2).toContinuousLinearMap).comp
        (mfderiv K₂ I₂ (fun y ↦ (g y).1) p.2)).range = ⊤)

include hf hg htrans

/-- **Embedded transverse composition of Lagrangian correspondences.** Let `f : L₁ → M₁ × M₂` and
`g : L₂ → M₂ × M₃` be smooth Lagrangian maps for the twisted products, such that `x ↦ (f x).2`
and `y ↦ (g y).1` are transverse, and suppose the composition has no excess: every tangent pair
`(u, w)` with `(df u).2 = (dg w).1`, `(df u).1 = 0` and `(dg w).2 = 0` is zero. If the composite
`(x, y) ↦ ((f x).1, (g y).2)` on the fibre product `L₁ ×_{M₂} L₂` is a topological embedding, it
is a Lagrangian correspondence `M₁ ⇝ M₃`. -/
theorem IsLagrangianMap.isLagrangianEmbedding_relComp_transverseFiberProduct
    [I₁.Boundaryless] [I₃.Boundaryless] (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianMap K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianMap K₂ g)
    (hexc : ∀ (p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1}) u w,
      (mfderiv K₁ (I₁.prod I₂) f p.1.1 u).2 = (mfderiv K₂ (I₂.prod I₃) g p.1.2 w).1 →
        (mfderiv K₁ (I₁.prod I₂) f p.1.1 u).1 = 0 → (mfderiv K₂ (I₂.prod I₃) g p.1.2 w).2 = 0 →
          u = 0 ∧ w = 0)
    (hemb : Topology.IsEmbedding
      (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2))) :
    letI := transverseFiberProductChartedSpace (by simp) hf.snd hg.fst htrans
    (hσ₁.twistedProd hσ₃).IsLagrangianEmbedding KF
      (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2)) := by
  let := transverseFiberProductChartedSpace (by simp) hf.snd hg.fst htrans
  have := isManifold_transverseFiberProduct (by simp) hf.snd hg.fst htrans
  exact ⟨(contMDiff_relComp_transverseFiberProduct hf hg htrans).isImmersion_of_injective_mfderiv
      (by simp) fun p ↦
        (injective_mfderiv_relComp_transverseFiberProduct_iff hf hg htrans p).2 (hexc p),
    hemb, hfL.relComp_transverseFiberProduct (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃) hf hg htrans
      hgL⟩

omit hf hg in
/-- **Transverse composition of Lagrangian correspondences, embedded case.** Under the hypotheses
of `IsLagrangianImmersion.relComp_transverseFiberProduct`, the composite
`(x, y) ↦ ((f x).1, (g y).2)` on the transverse fibre-product manifold is a Lagrangian
correspondence `M₁ ⇝ M₃` exactly when it is a topological embedding. -/
theorem IsLagrangianImmersion.isLagrangianEmbedding_relComp_transverseFiberProduct_iff
    [I₁.Boundaryless] [I₃.Boundaryless]
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianImmersion K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianImmersion K₂ g) :
    letI := transverseFiberProductChartedSpace (by simp)
      hfL.isImmersion.contMDiff.snd hgL.isImmersion.contMDiff.fst htrans
    (hσ₁.twistedProd hσ₃).IsLagrangianEmbedding KF
        (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2)) ↔
      Topology.IsEmbedding
        (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2)) := by
  let := transverseFiberProductChartedSpace (by simp)
    hfL.isImmersion.contMDiff.snd hgL.isImmersion.contMDiff.fst htrans
  have h := IsLagrangianImmersion.relComp_transverseFiberProduct (hσ₁ := hσ₁) (hσ₂ := hσ₂)
    (hσ₃ := hσ₃) htrans hfL hgL
  exact ⟨fun he ↦ he.isEmbedding, fun he ↦ ⟨h.isImmersion, he, h.isLagrangianMap⟩⟩

end Transverse

section Clean

variable {EQ HQ Q : Type*} [KC.Boundaryless]
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
  {KQ : ModelWithCorners ℝ EQ HQ} [KQ.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold KQ ∞ Q] {q : C → Q} {j : Q → M₁ × M₃}

/-- **Clean composition with a smooth excess quotient.** Under the hypotheses of
`IsLagrangianMap.relComp` for smooth data, suppose the endpoint map
`c ↦ ((f (a c)).1, (g (b c)).2)` factors as `j ∘ q` through a surjective smooth submersion `q`,
with boundaryless models, whose kernel contains every excess direction: every tangent vector
killed by both outer differentials. If `j` is a topological embedding, it is a Lagrangian
correspondence `M₁ ⇝ M₃`. Smoothness and the immersion property of `j` are conclusions, and `Q`
may be empty.

The excess condition is stated in the original correspondence coordinates. It allows nonzero
excess and does not assert existence of a smooth global quotient from cleanliness alone. -/
theorem IsLagrangianMap.isLagrangianEmbedding_relComp_of_isSubmersion
    [I₁.Boundaryless] [I₃.Boundaryless]
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianMap K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianMap K₂ g)
    (hf : ContMDiff K₁ (I₁.prod I₂) ∞ f) (hg : ContMDiff K₂ (I₂.prod I₃) ∞ g)
    (ha : ContMDiff KC K₁ ∞ a) (hb : ContMDiff KC K₂ ∞ b)
    (hab : ∀ c, (f (a c)).2 = (g (b c)).1)
    (hfib : ∀ c u w, (mfderiv K₁ (I₁.prod I₂) f (a c) u).2 =
        (mfderiv K₂ (I₂.prod I₃) g (b c) w).1 →
      ∃ ξ, mfderiv KC K₁ a c ξ = u ∧ mfderiv KC K₂ b c ξ = w)
    (hq : Manifold.IsSubmersion KC KQ ∞ q) (hsurj : Function.Surjective q)
    (hfactor : j ∘ q = fun c ↦ ((f (a c)).1, (g (b c)).2))
    (hexc : ∀ c ξ, (mfderiv K₁ (I₁.prod I₂) f (a c) (mfderiv KC K₁ a c ξ)).1 = 0 →
      (mfderiv K₂ (I₂.prod I₃) g (b c) (mfderiv KC K₂ b c ξ)).2 = 0 →
        mfderiv KC KQ q c ξ = 0)
    (hemb : Topology.IsEmbedding j) : (hσ₁.twistedProd hσ₃).IsLagrangianEmbedding KQ j :=
  ⟨isImmersion_relComp_of_isSubmersion hf hg ha hb hq hsurj hfactor hexc, hemb,
    hfL.relComp_of_isSubmersion (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃) hgL
      (hf.mdifferentiable (by simp)) (hg.mdifferentiable (by simp))
      (ha.mdifferentiable (by simp)) (hb.mdifferentiable (by simp)) hab hfib hq (by simp) hsurj
      hfactor⟩

end Clean

end TauCeti.SmoothTwoForm.IsNondegenerate
