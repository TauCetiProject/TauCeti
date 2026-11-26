/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.LineSplitting
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FirstChernClass.Prod

/-!
# The first Chern class of the line summand of a smooth splitting

Let `V` be a smooth complex vector bundle with an `i`-invariant smooth metric `g` and a pointwise
orthonormal family `s` of smooth sections. The splitting `V ≅ (B × ℂ^ι) ⊕ s^⊥`
(`Bundle.ContMDiffRiemannianMetric.trivialProdOrthogonalSpanFamilyDiffeomorph`) is complex linear
on fibres, so the orthogonal complement `s^⊥` has the first Chern class of `V`
(`Bundle.ContMDiffRiemannianMetric.firstChernClass_orthogonalSpanFamily`). When `s^⊥` is a line,
as for the splitting of `TauCeti.exists_trivialProdLineSubbundle_diffeomorph` over a closed
surface, this reads `c₁(L) = c₁(V)` for the line bundle `L = s^⊥`
(`Bundle.ContMDiffRiemannianMetric.lineFirstChernClass_orthogonalSpanFamily`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  proof of Theorem C.1.10 (the reduction of the Riemann–Roch formula to line bundles).
-/

public section

noncomputable section

open Bundle Module Set TauCeti
open scoped Manifold ContDiff InnerProductSpace

namespace Bundle.ContMDiffRiemannianMetric

variable {X H : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace H] {IB : ModelWithCorners ℝ X H}
  {B : Type} [TopologicalSpace B] [ChartedSpace H B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]
  {V : B → Type}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]
  {n : ℕ∞ω} {ι : Type} [Finite ι] {r : ℕ}

local instance instVectorBundleRealLineSplitting : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle n F V IB] (g : ContMDiffRiemannianMetric IB n F V)
  (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
  (s : ι → ∀ x, V x)
  (hs : ∀ i, ContMDiff IB (IB.prod 𝓘(ℝ, F)) n (fun x ↦ (⟨x, s i x⟩ : TotalSpace F V)))
  (hV : HasLocalContMDiffSubbundleFrames IB n F (Fin r) (g.orthogonalSpanFamily hI s))

include hs in
/-- **The orthogonal complement of an orthonormal family has the first Chern class of the bundle.**
For a pointwise orthonormal family `s` of smooth sections of a smooth Hermitian bundle `V`,
`c₁(s^⊥) = c₁(V)`: the splitting `V ≅ (B × ℂ^ι) ⊕ s^⊥` is complex linear on fibres and the trivial
summand does not change `c₁`. -/
theorem firstChernClass_orthogonalSpanFamily
    (hon : letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
      letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
      ∀ x, Orthonormal ℂ fun i ↦ s i x) :
    letI := hV.fiberBundle
    letI := hV.vectorBundle
    firstChernClass (Fin r → ℂ) (fun x ↦ g.orthogonalSpanFamily hI s x) = firstChernClass F V := by
  let := hV.fiberBundle
  let := hV.vectorBundle
  let := Fintype.ofFinite ι
  let D := g.trivialProdOrthogonalSpanFamilyDiffeomorph hI s hs hV hon
  let P := Trivial B (ι → ℂ) ×ᵇ fun x ↦ g.orthogonalSpanFamily hI s x
  -- The splitting on the fibre over `x`, `(c, w) ↦ ∑ i, c i • s i x + w`.
  let ϕ (x : B) : (ι → ℂ) × g.orthogonalSpanFamily hI s x →ₗ[ℂ] V x :=
    Fintype.linearCombination ℂ (fun i ↦ s i x) ∘ₗ LinearMap.fst ℂ _ _ +
      (g.orthogonalSpanFamily hI s x).subtype ∘ₗ LinearMap.snd ℂ _ _
  have hD (x : B) (v : P x) : D ⟨x, v⟩ = ⟨x, ϕ x v⟩ := by
    rw [g.trivialProdOrthogonalSpanFamilyDiffeomorph_apply hI s hs hV hon]
    simp only [ϕ, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, Fintype.linearCombination_apply, Submodule.subtype_apply]
  have hbij (x : B) : Function.Bijective (ϕ x) := by
    refine ⟨fun v w h ↦ ?_, fun w ↦ ?_⟩
    · exact (TotalSpace.mk_inj (E := P)).mp
        (D.injective ((hD x v).trans ((congrArg (TotalSpace.mk x) h).trans (hD x w).symm)))
    · obtain ⟨⟨y, v⟩, hv⟩ := D.surjective ⟨x, w⟩
      have hv' := (hD y v).symm.trans hv
      obtain rfl : y = x := congrArg TotalSpace.proj hv'
      exact ⟨v, (TotalSpace.mk_inj (E := V)).mp hv'⟩
  have := VectorBundle.isTopologicalAddGroup ℂ ((ι → ℂ) × (Fin r → ℂ)) P
  have := VectorBundle.continuousSMul ℂ ((ι → ℂ) × (Fin r → ℂ)) P
  have := VectorBundle.continuousSMul ℂ F V
  have := FiberBundle.t2Space ((ι → ℂ) × (Fin r → ℂ)) P
  have := FiberBundle.t2Space F V
  have := VectorBundle.finiteDimensional ℂ ((ι → ℂ) × (Fin r → ℂ)) P
  let φ (x : B) : P x ≃L[ℂ] V x := (LinearEquiv.ofBijective (ϕ x) (hbij x)).toContinuousLinearEquiv
  refine firstChernClass_eq_of_fiberwise_trivialProd (φ := φ) (D.continuous.congr fun v ↦ ?_)
  simp only [φ, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.ofBijective_apply]
  exact hD v.proj v.snd

include hs in
/-- **The line summand of a smooth splitting has the first Chern class of the bundle.** If the
orthogonal complement `L = s^⊥` of a pointwise orthonormal family `s` of smooth sections of a
smooth Hermitian bundle `V` is a line bundle, then `c₁(L) = c₁(V)`. This applies to the splitting
`V ≅ (B × ℂⁿ) ⊕ L` of `TauCeti.exists_trivialProdLineSubbundle_diffeomorph`. -/
theorem lineFirstChernClass_orthogonalSpanFamily
    (hV : HasLocalContMDiffSubbundleFrames IB n F (Fin 1) (g.orthogonalSpanFamily hI s))
    (hon : letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
      letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
      ∀ x, Orthonormal ℂ fun i ↦ s i x) :
    letI := hV.fiberBundle
    letI := hV.vectorBundle
    lineFirstChernClass (Fin 1 → ℂ) (fun x ↦ g.orthogonalSpanFamily hI s x)
      (by simp) = firstChernClass F V := by
  let := hV.fiberBundle
  let := hV.vectorBundle
  rw [← firstChernClass_eq_lineFirstChernClass,
    g.firstChernClass_orthogonalSpanFamily hI s hs hV hon]

end Bundle.ContMDiffRiemannianMetric
