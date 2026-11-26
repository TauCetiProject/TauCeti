/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.FundamentalClass
public import TauCeti.Geometry.Symplectic.JHolomorphic.AreaWindow
public import TauCeti.Geometry.Symplectic.Manifold.CurvePairing
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
import TauCeti.Geometry.Symplectic.Manifold.Flat
import TauCeti.Topology.VectorBundle.Riemannian.Comparison

/-!
# Comass bounds for the classes of closed pseudoholomorphic curves

Let `X` be a manifold with a smooth almost complex structure `J`, tamed by a closed two-form `σ`:
`σ(v, J v) > 0` for every nonzero tangent vector `v`. This file proves, for the actual closed
`J`-holomorphic curves of `X`, the two inequalities behind Gromov's finiteness of curve classes:
their integral homology classes have positive symplectic area, and when `X` is compact the period
of every closed two-form on them is bounded by a constant, independent of the curve, times that
area. So the curve classes of a compact `X` form a comass bounded set (`TauCeti.IsComassBounded`),
the input of the finiteness statements for the bounded-window compactness in Taubes's count of
pseudoholomorphic curves.

**The comparison constant.** For every two-form `θ` there is a constant `K ≥ 0` with

`|θ(v, J v)| ≤ K σ(v, J v)` for all tangent vectors `v` of `X`

(`TauCeti.SmoothTwoForm.Tames.exists_abs_eval₂_le_mul_eval₂`). Only taming is used. In an
auxiliary continuous Riemannian metric, `θ(·, J ·)` is bounded by `C |v|²`
(`IsCompact.exists_bound_of_continuousOn_bilinear_bundle`) and `σ(·, J ·)` is coercive,
`c |v|² ≤ σ(v, J v)` (`IsCompact.exists_pos_forall_mul_norm_sq_le_bundle`), uniformly over the
compact `X`, so `K = C / c` works. When `σ` is compatible with `J` and `X` carries the metric
`σ(·, J ·)`, any bound for the comass of `θ` is such a `K`.

**Curve classes.** A class `A ∈ H₂(X; ℤ)` is a *curve class* of `J`, for surfaces modelled on
`I'` (`TauCeti.SmoothAlmostComplexStructure.IsCurveClass`), if it is the image `u_* μ` of an
integral fundamental class `μ` of a closed connected surface `C` under a nonconstant smooth
`J`-holomorphic map `u : (C, j) → (X, J)`, where `μ` is the fundamental class of the complex
orientation of `C`: the period of every closed two-form `β` of `X` on `A` is the integral
`∫_C u^* β` over `C` oriented by the frames `(e, j e)`. Every nonconstant closed connected curve
has such a class: for either fundamental class `μ` of `C`, one of `u_* μ` and `-u_* μ` is a curve
class (`TauCeti.SmoothAlmostComplexStructure.isCurveClass_or_isCurveClass_neg`), because the
periods on `u_* μ` are `±` the integrals
(`TauCeti.exists_closedFormHomologyPeriod_singularHomologyMap_eq_mul_integralTopForm`).

**Area and periods of curve classes.** The period of `σ` on a curve class `A`, its symplectic area,
is positive (`TauCeti.SmoothAlmostComplexStructure.IsCurveClass.closedFormHomologyPeriod_pos`).
If `X` is compact, the period of any closed two-form `θ` is bounded by a constant times the area,
`|⟨[θ], A⟩| ≤ K ⟨[σ], A⟩` with `K` independent of the curve
(`TauCeti.SmoothAlmostComplexStructure.exists_abs_closedFormHomologyPeriod_le_mul`): indeed
`⟨[θ], A⟩ = ∫_C u^* θ`, which `TauCeti.abs_integralTopForm_mpullback_le` bounds by `K ∫_C u^* σ`.

For finitely many closed two-forms, the curve classes are therefore comass bounded in the sense of
`TauCeti.IsComassBounded` (`TauCeti.SmoothAlmostComplexStructure.exists_isComassBounded`), with
the symplectic area as area. When the periods of these forms have injective real extension, the
consequences of `TauCeti.IsComassBounded` hold for the curves of `X`: only finitely many curve
classes have area at most `R`, torsion parts included
(`TauCeti.IsComassBounded.finite_setOf_area_le`), their areas are bounded below by a positive
constant, and the total multiplicity of a cycle of curve classes in a given class is bounded. By
de Rham's theorem the periods of closed two-forms whose classes span `H²(X; ℝ)` have injective
real extension; that comparison is not available here.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347, §1.
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893, §2.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 2.2.
-/

public section

noncomputable section

open Bundle Set Module
open scoped Manifold ContDiff

namespace TauCeti

/-! ### The comparison constant -/

section Comparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- **The comparison constant of a taming form.** On a compact manifold, let the two-form `σ` tame
the smooth almost complex structure `J`. For every two-form `θ` there is a constant `K ≥ 0` with
`|θ(v, J v)| ≤ K σ(v, J v)` for every tangent vector `v`. When `σ` is compatible with `J`, `K` can
be any bound for the comass of `θ` in the metric `σ(·, J ·)`. -/
theorem SmoothTwoForm.Tames.exists_abs_eval₂_le_mul_eval₂ [FiniteDimensional ℝ E] [T2Space M]
    [CompactSpace M] {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
    (hσ : σ.Tames J) (θ : SmoothTwoForm I M) :
    ∃ K, 0 ≤ K ∧ ∀ x (v : TangentSpace I x),
      |θ.eval₂ x v (J x v)| ≤ K * σ.eval₂ x v (J x v) := by
  -- Measure tangent vectors in an auxiliary continuous Riemannian metric.
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := I) (n := ⊤) (F := E)
    (E := fun x : M ↦ TangentSpace I x)
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    Bundle.instIsContMDiffRiemannianBundle g
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
      (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)
  -- The bilinear forms `β(-J ·, ·)` are `β(·, J ·)` on the diagonal.
  have hdiag (β : SmoothTwoForm I M) (x : M) (v : TangentSpace I x) :
      β.flatComp (-J.toEndomorphism) x v v = β.eval₂ x v (J x v) := by
    rw [SmoothTwoForm.flatComp_apply, ContinuousLinearMap.comp_apply, SmoothTwoForm.flat_apply]
    simp only [ContMDiffSection.coe_neg, Pi.neg_apply, neg_apply]
    rw [SmoothBundleForm.eval₂_neg_left, SmoothBundleForm.eval₂_swap, neg_neg]
  obtain ⟨c, hc, hcσ⟩ := isCompact_univ.exists_pos_forall_mul_norm_sq_le_bundle (b := id)
    (φ := fun x ↦ σ.flatComp (-J.toEndomorphism) x)
    ((σ.flatComp (-J.toEndomorphism)).contMDiff.continuous.continuousOn)
    fun x _ v hv ↦ by rw [hdiag]; exact SmoothTwoForm.tames_iff.1 hσ x v hv
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn_bilinear_bundle (b := id)
    (φ := fun x ↦ θ.flatComp (-J.toEndomorphism) x)
    ((θ.flatComp (-J.toEndomorphism)).contMDiff.continuous.continuousOn)
  refine ⟨max C 0 / c, by positivity, fun x v ↦ ?_⟩
  have hθ : |θ.eval₂ x v (J x v)| ≤ max C 0 * ‖v‖ * ‖v‖ := by
    rw [← hdiag, ← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_
    gcongr
    exact (hC x (mem_univ x)).trans (le_max_left C 0)
  calc |θ.eval₂ x v (J x v)| ≤ max C 0 / c * (c * ‖v‖ ^ 2) := by
        rw [← mul_assoc, div_mul_cancel₀ _ hc.ne', sq, ← mul_assoc]
        exact hθ
    _ ≤ max C 0 / c * σ.eval₂ x v (J x v) := by
        gcongr
        rw [← hdiag]
        exact hcσ x (mem_univ x) v

end Comparison

/-! ### Curve classes -/

variable {E H X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
  [IsManifold I ∞ X] [T2Space X] [SigmaCompactSpace X]
  {W H' : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ W H'}

namespace SmoothAlmostComplexStructure

/-- A class `A ∈ H₂(X; ℤ)` is a **curve class** of the smooth almost complex structure `J`, for
surfaces modelled on `I'`, if it is the image `u_* μ` of an integral fundamental class `μ` of a
closed connected surface `C` under a nonconstant smooth `J`-holomorphic map `u : (C, j) → (X, J)`,
with `μ` the fundamental class of the complex orientation `o` of `C`, the orientation of the
frames `(e, j e)`: the period of every closed two-form `β` of `X` on `A` is `∫_C u^* β` for `o`. -/
def IsCurveClass (J : SmoothAlmostComplexStructure I X) (I' : ModelWithCorners ℝ W H')
    (A : ((singularChains ℤ).obj (TopCat.of X)).homology 2) : Prop :=
  ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace H' C) (_ : IsManifold I' ∞ C)
    (_ : BoundarylessManifold I' C) (_ : T2Space C) (_ : CompactSpace C) (_ : ConnectedSpace C)
    (j : SmoothAlmostComplexStructure I' C) (o : Manifold.Orientation I' C (Fin 2)) (u : C → X)
    (hu : ContMDiff I' I ∞ u) (μ : ((singularChains ℤ).obj (TopCat.of C)).homology 2),
    (∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c) ∧
    (∀ c, IsPseudoholomorphicAt j J u c) ∧ (∃ c c', u c ≠ u c') ∧
    IsFundamentalClass (M := C) (N := ModuleCat.of ℤ ℤ) μ ∧
    A = ContinuousMap.singularHomologyMap ℤ 2 ⟨u, hu.continuous⟩ μ ∧
    ∀ β : closedForms I X 2,
      closedFormHomologyPeriod β A = integralTopForm o (SmoothForm.mpullback u hu β.val).val

variable {J : SmoothAlmostComplexStructure I X}

/-- The defining property of a curve class: the image `u_* μ` of a fundamental class of a closed
connected surface under a nonconstant `J`-holomorphic map, whose periods are the integrals over
the complex-oriented surface. -/
theorem isCurveClass_iff {A : ((singularChains ℤ).obj (TopCat.of X)).homology 2} :
    J.IsCurveClass I' A ↔
      ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace H' C) (_ : IsManifold I' ∞ C)
        (_ : BoundarylessManifold I' C) (_ : T2Space C) (_ : CompactSpace C)
        (_ : ConnectedSpace C) (j : SmoothAlmostComplexStructure I' C)
        (o : Manifold.Orientation I' C (Fin 2)) (u : C → X) (hu : ContMDiff I' I ∞ u)
        (μ : ((singularChains ℤ).obj (TopCat.of C)).homology 2),
        (∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
          b.orientation = o.orientationAt c) ∧
        (∀ c, IsPseudoholomorphicAt j J u c) ∧ (∃ c c', u c ≠ u c') ∧
        IsFundamentalClass (M := C) (N := ModuleCat.of ℤ ℤ) μ ∧
        A = ContinuousMap.singularHomologyMap ℤ 2 ⟨u, hu.continuous⟩ μ ∧
        ∀ β : closedForms I X 2,
          closedFormHomologyPeriod β A = integralTopForm o (SmoothForm.mpullback u hu β.val).val :=
  Iff.rfl

/-- **Every closed curve has a curve class.** Let `u : (C, j) → (X, J)` be a nonconstant smooth
`J`-holomorphic map from a closed connected surface, oriented by the frames `(e, j e)`. For either
integral fundamental class `μ` of `C`, one of `u_* μ` and `-u_* μ` is a curve class of `J`. -/
theorem isCurveClass_or_isCurveClass_neg [I'.Boundaryless] (hW : finrank ℝ W = 2) {C : Type}
    [TopologicalSpace C] [ChartedSpace H' C] [IsManifold I' ∞ C] [T2Space C] [CompactSpace C]
    [ConnectedSpace C] {j : SmoothAlmostComplexStructure I' C}
    {o : Manifold.Orientation I' C (Fin 2)} {u : C → X} (hu : ContMDiff I' I ∞ u)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j J u c) (hnc : ∃ c c', u c ≠ u c')
    {μ : ((singularChains ℤ).obj (TopCat.of C)).homology 2}
    (hμ : IsFundamentalClass (M := C) (N := ModuleCat.of ℤ ℤ) μ) :
    J.IsCurveClass I' (ContinuousMap.singularHomologyMap ℤ 2 ⟨u, hu.continuous⟩ μ) ∨
      J.IsCurveClass I' (-ContinuousMap.singularHomologyMap ℤ 2 ⟨u, hu.continuous⟩ μ) := by
  obtain ⟨s, hs, hper⟩ :=
    exists_closedFormHomologyPeriod_singularHomologyMap_eq_mul_integralTopForm hW o hμ hu
  rcases hs with rfl | rfl
  · refine .inl ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, j, o, u, hu, μ, ho, hhol, hnc, hμ, rfl, fun β ↦ ?_⟩
    simpa using hper β
  · refine .inr ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, j, o, u, hu, -μ, ho, hhol, hnc,
      isFundamentalClass_neg_iff.2 hμ, (map_neg _ μ).symm, fun β ↦ ?_⟩
    rw [map_neg, hper β, SmoothForm.coe_mpullback]
    push_cast
    ring

/-- **Curve classes have positive area.** If the closed two-form `σ` tames `J`, its period on
every curve class, the symplectic area of the curve, is positive. -/
theorem IsCurveClass.closedFormHomologyPeriod_pos {σ : closedForms I X 2}
    (hσ : SmoothTwoForm.Tames σ.val J) {A : ((singularChains ℤ).obj (TopCat.of X)).homology 2}
    (hA : J.IsCurveClass I' A) : 0 < closedFormHomologyPeriod σ A := by
  obtain ⟨C, _, _, _, _, _, _, _, j, o, u, hu, μ, ho, hhol, ⟨c₀, c₁, hne⟩, -, -, hper⟩ := hA
  rw [hper σ]
  have hσu (c : C) (v : TangentSpace I (u c)) (hv : v ≠ 0) :
      0 < SmoothBundleForm.eval₂ σ.val (u c) v (J (u c) v) :=
    SmoothTwoForm.tames_iff.1 hσ (u c) v hv
  refine (integralTopForm_mpullback_nonneg hu ho hhol fun c v ↦ ?_).lt_of_ne fun h ↦ hne ?_
  · rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact (hσu c v hv).le
  · exact (hu.mdifferentiable (by simp)).apply_eq_of_mfderiv_eq_zero
      (mfderiv_eq_zero_of_integralTopForm_mpullback_eq_zero hu ho hhol hσu h.symm) c₀ c₁

variable [CompactSpace X]

/-- **Periods of curve classes are bounded by their area.** On a compact manifold, let the closed
two-form `σ` tame `J`. For every closed two-form `θ` there is a constant `K ≥ 0`, independent of
the curve, such that `|⟨[θ], A⟩| ≤ K ⟨[σ], A⟩` for every curve class `A` of `J`. -/
theorem exists_abs_closedFormHomologyPeriod_le_mul {σ : closedForms I X 2}
    (hσ : SmoothTwoForm.Tames σ.val J) (θ : closedForms I X 2) :
    ∃ K, 0 ≤ K ∧ ∀ A, J.IsCurveClass I' A →
      |closedFormHomologyPeriod θ A| ≤ K * closedFormHomologyPeriod σ A := by
  obtain ⟨K, hK, hθ⟩ := hσ.exists_abs_eval₂_le_mul_eval₂ θ.val
  refine ⟨K, hK, fun A hA ↦ ?_⟩
  obtain ⟨C, _, _, _, _, _, _, _, j, o, u, hu, μ, ho, hhol, -, -, -, hper⟩ := hA
  rw [hper θ, hper σ]
  exact abs_integralTopForm_mpullback_le hu ho hhol fun c v ↦ hθ (u c) v

/-- **Curve classes are comass bounded.** On a compact manifold, let the closed two-form `σ` tame
`J`. For finitely many closed two-forms `ζ i`, the curve classes of `J` form a comass bounded set
for the period map `A ↦ (⟨[ζ i], A⟩)ᵢ` and the area `A ↦ ⟨[σ], A⟩`. -/
theorem exists_isComassBounded {ι : Type*} [Fintype ι] {σ : closedForms I X 2}
    (hσ : SmoothTwoForm.Tames σ.val J) (ζ : ι → closedForms I X 2) :
    ∃ K, IsComassBounded (AddMonoidHom.pi fun i ↦ closedFormHomologyPeriod (ζ i)).toIntLinearMap
      (closedFormHomologyPeriod σ) K {A | J.IsCurveClass I' A} := by
  choose K hK hζ using fun i ↦ exists_abs_closedFormHomologyPeriod_le_mul (I' := I') hσ (ζ i)
  refine ⟨∑ i, K i, fun A hA ↦ hA.closedFormHomologyPeriod_pos hσ, fun A hA ↦ ?_⟩
  have harea := (hA.closedFormHomologyPeriod_pos hσ).le
  refine (pi_norm_le_iff_of_nonneg
    (mul_nonneg (Finset.sum_nonneg fun i _ ↦ hK i) harea)).2 fun i ↦ ?_
  rw [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.pi_apply, Real.norm_eq_abs]
  have hKi : K i ≤ ∑ i, K i := Finset.single_le_sum (fun i _ ↦ hK i) (Finset.mem_univ i)
  exact (hζ i A hA).trans (mul_le_mul_of_nonneg_right hKi harea)

end SmoothAlmostComplexStructure

end TauCeti
