/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Pullback
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Symplectic.PolarCompatible
import TauCeti.Analysis.InnerProductSpace.Positive.MetricChange.Smooth
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.Riemannian.Invariant
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
import TauCeti.Geometry.Symplectic.Manifold.Flat

/-!
# Compatible almost complex structures from a Riemannian metric

Let `σ` be a fiberwise nondegenerate smooth two-form on a manifold `M` with a smooth Riemannian
metric `g`. At each point `x`, the polar normalization
`TauCeti.SymplecticForm.polarComplexStructure` of the symplectic form `σ_x` on the inner product
space `(T_x M, g_x)` is an almost complex structure on `T_x M` compatible with `σ_x`: if `A` is the
operator with `g(A u, v) = σ(u, v)`, it is the polar factor `J = A (-A²)^(-1/2)`. This file shows
that these structures depend smoothly on `x`, so that they form a smooth almost complex structure
`TauCeti.SmoothTwoForm.IsNondegenerate.polarComplexStructure`, compatible with `σ` and orthogonal
for `g`. Since every σ-compact Hausdorff manifold carries a smooth Riemannian metric, every
nondegenerate two-form, in particular every symplectic form, admits a compatible smooth almost
complex structure (`TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible`). Compatible structures
are tame, so the spaces of tame and of compatible smooth almost complex structures are nonempty;
this is the input for choosing the almost complex structures with which pseudoholomorphic curves are
defined.

The construction is natural in the metric: if `g` is the compatible metric `σ(·, J ·)` of a
smooth almost complex structure `J`, the polar normalization of `σ` is `J` itself
(`TauCeti.SmoothTwoForm.IsNondegenerate.polarComplexStructure_eq_of_inner_eq`).

It is also natural under maps preserving both the metric and the form: a map between manifolds of
the same dimension whose differentials preserve them is complex linear for the two polar
normalizations
(`TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_polarComplexStructure_apply`), and such a
diffeomorphism pulls one polar normalization back to the other
(`TauCeti.SmoothTwoForm.IsNondegenerate.pullback_polarComplexStructure`). This is what produces
almost complex structures invariant under a group of symplectomorphisms: averaging an arbitrary
compatible `J` over the group does not preserve `J² = -1`, but averaging a metric gives an
invariant metric, whose polar normalization is then invariant. For a finite group acting smoothly
by symplectomorphisms, averaging the pullbacks of a smooth metric
(`TauCeti.averageRiemannianMetric`) thus gives a compatible smooth almost complex structure for
which every action map is complex linear
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible_mfderiv_smul_apply`).

Smoothness is checked in a trivialization of the tangent bundle. There `g` and `σ` become smooth
families of bilinear forms on a model fibre, and the polar normalization becomes the expression of
`TauCeti.SymplecticForm.conjContinuousAlgEquiv_toContinuousLinearMap_polarComplexStructure`,
built from the metric change transport, the square root of the continuous functional calculus and
inversion, each of which depends smoothly on its argument.

## Main definitions

* `TauCeti.SmoothTwoForm.IsNondegenerate.polarComplexStructure`: the polar normalization of a
  nondegenerate smooth two-form for the metric of `M`.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.polarComplexStructure_apply`: at each point it is the
  polar normalization of the form on the tangent space.
* `TauCeti.SmoothTwoForm.IsNondegenerate.compatible_polarComplexStructure`: it is compatible with
  the form.
* `TauCeti.SmoothTwoForm.IsNondegenerate.inner_polarComplexStructure_apply_apply`: it is
  orthogonal for the metric.
* `TauCeti.SmoothTwoForm.IsNondegenerate.polarComplexStructure_eq_of_inner_eq`: it fixes a
  structure whose compatible metric is the metric of `M`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible`: every nondegenerate smooth two-form on
  a σ-compact Hausdorff manifold admits a compatible smooth almost complex structure.
* `TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_polarComplexStructure_apply`,
  `TauCeti.SmoothTwoForm.IsNondegenerate.pullback_polarComplexStructure`: maps preserving the
  metric and the form intertwine the polar normalizations.
* `TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible_mfderiv_smul_apply`: a finite group
  acting smoothly by symplectomorphisms preserves some compatible smooth almost complex structure.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, Section 2.5 (polar normalization of a symplectic form against an inner
  product) and Section 4.1 (compatible almost complex structures on symplectic manifolds, from a
  Riemannian metric).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  American Mathematical Society, 2012, Section 2.2.
-/

public section

noncomputable section

open Bundle Module Filter InnerProductSpace
open scoped ContDiff Manifold RealInnerProductSpace Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M}

namespace SmoothTwoForm.IsNondegenerate

local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- Smooth dependence of polar normalization in coordinates: if `g` and `s` are families of
bilinear forms on `F` which are smooth at `x₀`, with `g♯` and `-A²` strictly positive near `x₀`,
where `R = (g♯)^(-1/2)` is the metric change transport and `A = R s♯ R`, then
`R A (√(-A²))⁻¹ √(g♯)` is smooth at `x₀`. -/
private theorem contMDiffAt_metricChangeTransport_mul_mul_sqrt {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {g s : M → F →L[ℝ] F →L[ℝ] ℝ} {x₀ : M} {U : Set M} (hU : U ∈ 𝓝 x₀)
    (hg : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) ∞ g x₀)
    (hs : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) ∞ s x₀)
    (hgpos : ∀ y ∈ U, IsStrictlyPositive (g y)♯)
    (hApos : ∀ y ∈ U, IsStrictlyPositive (-((g y).metricChangeTransport * (s y)♯ *
      (g y).metricChangeTransport * ((g y).metricChangeTransport * (s y)♯ *
        (g y).metricChangeTransport)))) :
    ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F) ∞ (fun y ↦ (g y).metricChangeTransport *
      ((g y).metricChangeTransport * (s y)♯ * (g y).metricChangeTransport *
        Ring.inverse (CFC.sqrt (-((g y).metricChangeTransport * (s y)♯ *
          (g y).metricChangeTransport * ((g y).metricChangeTransport * (s y)♯ *
            (g y).metricChangeTransport))))) * CFC.sqrt (g y)♯) x₀ := by
  set R : M → F →L[ℝ] F := fun y ↦ (g y).metricChangeTransport
  set A : M → F →L[ℝ] F := fun y ↦ R y * (s y)♯ * R y
  have hx₀ := mem_of_mem_nhds hU
  -- The transport, its inverse `√(g♯)` and `√(-A²)` are smooth on the strictly positive
  -- operators, inversion is smooth at units, and products are smooth.
  have hR : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F) ∞ R x₀ :=
    ((ContinuousLinearMap.contDiffOn_metricChangeTransport.contDiffWithinAt
      (hgpos x₀ hx₀)).comp_contMDiffWithinAt hg.contMDiffWithinAt hgpos).contMDiffAt hU
  have hQ : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F) ∞ (fun y ↦ CFC.sqrt (g y)♯) x₀ :=
    ((ContinuousLinearMap.contDiffOn_sqrt_continuousLinearMapOfBilin.contDiffWithinAt
      (hgpos x₀ hx₀)).comp_contMDiffWithinAt hg.contMDiffWithinAt hgpos).contMDiffAt hU
  have hA : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F) ∞ A x₀ :=
    (hR.clm_comp (contDiff_continuousLinearMapOfBilin.comp_contMDiffAt hs)).clm_comp hR
  have hAA : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F) ∞ (fun y ↦ -(A y * A y)) x₀ := (hA.clm_comp hA).neg
  -- The point is named explicitly: the strictly positive value `-(A x₀ * A x₀)` alone does not
  -- determine the function it is a value of.
  have hsqrt : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F) ∞ (fun y ↦ CFC.sqrt (-(A y * A y))) x₀ :=
    (ContDiffWithinAt.comp_contMDiffWithinAt (f := fun y ↦ -(A y * A y)) (x := x₀)
      (ContinuousLinearMap.contDiffOn_sqrt.contDiffWithinAt (hApos x₀ hx₀))
      hAA.contMDiffWithinAt hApos).contMDiffAt hU
  obtain ⟨u, hu⟩ := (CFC.isUnit_sqrt_iff _ (hApos x₀ hx₀).nonneg).2 (hApos x₀ hx₀).isUnit
  have hinv := contDiffAt_ringInverse ℝ (n := ∞) u
  rw [hu] at hinv
  exact (hR.clm_comp ((hA.clm_comp (ContDiffAt.comp_contMDiffAt
    (f := fun y ↦ CFC.sqrt (-(A y * A y))) (x := x₀) hinv hsqrt)))).clm_comp hQ

section Metric

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The polar normalization of `σ` at `x` for the metric of `M`, as a continuous endomorphism of
`T_x M`. -/
private def polarEnd (h : σ.IsNondegenerate) (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap (h.symplecticFormAt x).polarComplexStructure.toLinearMap

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The pointwise polar normalizations of `σ` form a smooth section of the endomorphism bundle of
the tangent bundle. -/
private theorem contMDiff_polarEnd (h : σ.IsNondegenerate) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞ (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) x (polarEnd h x)) := by
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  set e := trivializationAt E (TangentSpace I) x₀
  have hU : e.baseSet ∈ 𝓝 x₀ :=
    e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (TangentSpace I) x₀)
  -- Read the metric and the form in the trivialization `e`, then on an inner product space `F`
  -- through an isomorphism `T : E ≃ F`, where the functional calculus is available.
  obtain ⟨g, hg, hgi⟩ := (inferInstance :
    IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)).exists_contMDiff
  obtain ⟨gc, hgc, hgc_apply⟩ := Manifold.exists_contMDiffAt_apply_eq_apply_symm (hg x₀)
  obtain ⟨sc, hsc, hsc_apply⟩ :=
    Manifold.exists_contMDiffAt_apply_eq_apply_symm (σ.contMDiff_flat x₀)
  obtain ⟨F, _, _, _, ⟨T⟩⟩ : ∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
      (_ : FiniteDimensional ℝ F), Nonempty (E ≃L[ℝ] F) :=
    ⟨EuclideanSpace ℝ (Fin (finrank ℝ E)), inferInstance, inferInstance, inferInstance,
      ⟨ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm⟩⟩
  let Ts : F →L[ℝ] E := T.symm
  let pull : (E →L[ℝ] ℝ) →L[ℝ] F →L[ℝ] ℝ := (ContinuousLinearMap.compL ℝ F E ℝ).flip Ts
  let gF (y : M) : F →L[ℝ] F →L[ℝ] ℝ := pull.comp ((gc y).comp Ts)
  let sF (y : M) : F →L[ℝ] F →L[ℝ] ℝ := pull.comp ((sc y).comp Ts)
  -- Over the base set, `gF` and `sF` are the metric and the form read through `K y : T_y M ≃ F`.
  let K (y : M) (hy : y ∈ e.baseSet) : TangentSpace I y ≃L[ℝ] F :=
    (e.continuousLinearEquivAt ℝ y hy).trans T
  have hgF_apply (y : M) (hy : y ∈ e.baseSet) (c d : F) :
      gF y c d = ⟪(K y hy).symm c, (K y hy).symm d⟫ := by
    rw [hgi]
    exact hgc_apply y hy _ _
  have hsF_apply (y : M) (hy : y ∈ e.baseSet) (c d : F) :
      sF y c d = h.symplecticFormAt y ((K y hy).symm c) ((K y hy).symm d) := by
    rw [symplecticFormAt_apply, ← flat_apply]
    exact hsc_apply y hy _ _
  have hgpos (y : M) (hy : y ∈ e.baseSet) : IsStrictlyPositive (gF y)♯ :=
    isStrictlyPositive_continuousLinearMapOfBilin_of_injective
      (K := (K y hy).symm.toLinearEquiv.toLinearMap) (K y hy).symm.injective (hgF_apply y hy)
  have hApos (y : M) (hy : y ∈ e.baseSet) := ((h.symplecticFormAt y).transport
    (K y hy).toLinearEquiv).isStrictlyPositive_neg_mul_self_metricChangeTransport (hgpos y hy)
      fun c d ↦ by rw [hsF_apply y hy, SymplecticForm.transport_apply]; rfl
  -- In these coordinates the polar normalization is the smooth expression in `gF` and `sF`.
  refine (((contMDiffAt_const (c := Ts)).clm_comp (contMDiffAt_metricChangeTransport_mul_mul_sqrt
    hU (contMDiffAt_const.clm_comp (hgc.clm_comp contMDiffAt_const))
    (contMDiffAt_const.clm_comp (hsc.clm_comp contMDiffAt_const)) hgpos hApos)).clm_comp
      (contMDiffAt_const (c := (T : E →L[ℝ] F)))).congr_of_eventuallyEq ?_
  filter_upwards [hU] with y hy
  rw [ContinuousLinearMap.inCoordinates_eq hy hy,
    ← SymplecticForm.conjContinuousAlgEquiv_toContinuousLinearMap_polarComplexStructure _
      (K y hy) (hgF_apply y hy) (hsF_apply y hy)]
  ext u
  simp only [polarEnd, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Trivialization.continuousLinearEquivAt_symm_apply, LinearMap.coe_toContinuousLinearMap',
    Trivialization.continuousLinearEquivAt_apply,
    ContinuousLinearEquiv.conjContinuousAlgEquiv_apply,
    ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.trans_apply, Ts, K, e]

/-- **Polar normalization** of a fiberwise nondegenerate smooth two-form `σ` for the metric `g`
of `M`: the smooth almost complex structure whose value at each point `x` is the polar
normalization of `σ_x` for the inner product `g_x`
(`TauCeti.SmoothTwoForm.IsNondegenerate.polarComplexStructure_apply`). It is compatible with `σ`
and orthogonal for `g`. -/
def polarComplexStructure (h : σ.IsNondegenerate) : SmoothAlmostComplexStructure I M where
  toEndomorphism := ⟨polarEnd h, contMDiff_polarEnd h⟩
  square_neg x := by
    ext v
    exact (h.symplecticFormAt x).polarComplexStructure.apply_apply v

/-- At each point, the polar normalization of `σ` is the polar normalization of `σ_x` for the
inner product `g_x`. -/
theorem almostComplexStructureAt_polarComplexStructure (h : σ.IsNondegenerate) (x : M) :
    h.polarComplexStructure.almostComplexStructureAt x =
      (h.symplecticFormAt x).polarComplexStructure :=
  AlmostComplexStructure.toLinearMap_injective <| by
    rw [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap]
    -- The endomorphism of `polarComplexStructure` at `x` is `polarEnd h x` by definition, the
    -- continuous version of the pointwise polar normalization.
    change (polarEnd h x).toLinearMap = _
    exact LinearMap.coe_toContinuousLinearMap _

/-- Applying the polar normalization of `σ` at `x` applies the polar normalization of `σ_x` for
the inner product `g_x`. -/
@[simp]
theorem polarComplexStructure_apply (h : σ.IsNondegenerate) (x : M) (v : TangentSpace I x) :
    h.polarComplexStructure x v = (h.symplecticFormAt x).polarComplexStructure v := by
  rw [← SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
    almostComplexStructureAt_polarComplexStructure]

/-- **The polar normalization is compatible** with the form. -/
theorem compatible_polarComplexStructure (h : σ.IsNondegenerate) :
    σ.Compatible h.polarComplexStructure :=
  h.compatible_iff.2 fun x ↦ by
    rw [almostComplexStructureAt_polarComplexStructure]
    exact (h.symplecticFormAt x).compatible_polarComplexStructure

/-- The polar normalization of `σ` is orthogonal for the metric: `g(J u, J v) = g(u, v)`. -/
theorem inner_polarComplexStructure_apply_apply (h : σ.IsNondegenerate) (x : M)
    (u v : TangentSpace I x) :
    ⟪h.polarComplexStructure x u, h.polarComplexStructure x v⟫ = ⟪u, v⟫ := by
  rw [polarComplexStructure_apply, polarComplexStructure_apply]
  exact (h.symplecticFormAt x).inner_polarComplexStructure_apply_apply u v

/-- **Polar normalization fixes metric structures.** If the metric of `M` is the compatible metric
`σ(·, J ·)` of a smooth almost complex structure `J`, then the polar normalization of `σ` is
`J`. -/
theorem polarComplexStructure_eq_of_inner_eq (h : σ.IsNondegenerate)
    {J : SmoothAlmostComplexStructure I M} (hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v)) :
    h.polarComplexStructure = J :=
  SmoothAlmostComplexStructure.ext fun x v ↦ by
    rw [polarComplexStructure_apply,
      (h.symplecticFormAt x).polarComplexStructure_eq_of_apply_eq_inner
        (J := J.almostComplexStructureAt x) fun u w ↦ by
          rw [symplecticFormAt_apply, SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
            hJ]]
    exact J.almostComplexStructureAt_apply x v

section Naturality

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' ∞ N] {τ : SmoothTwoForm I' N} [RiemannianBundle (fun y : N ↦ TangentSpace I' y)]
  [IsContMDiffRiemannianBundle I' ∞ E' (fun y : N ↦ TangentSpace I' y)]

/-- **Naturality of polar normalization.** Let `f : M → N` be a map between manifolds of the same
dimension. If its differential at `x` carries the metric and the form `σ` of `M` at `x` to the
metric and the form `τ` of `N` at `f x`, then it intertwines their polar normalizations:
`df_x ∘ J_x = J_(f x) ∘ df_x`. -/
theorem mfderiv_polarComplexStructure_apply (h : σ.IsNondegenerate) (hτ : τ.IsNondegenerate)
    (hE : finrank ℝ E = finrank ℝ E') {f : M → N} {x : M}
    (hg : ∀ u v : TangentSpace I x, ⟪mfderiv I I' f x u, mfderiv I I' f x v⟫ = ⟪u, v⟫)
    (hσ : ∀ u v : TangentSpace I x,
      τ.eval₂ (f x) (mfderiv I I' f x u) (mfderiv I I' f x v) = σ.eval₂ x u v)
    (v : TangentSpace I x) :
    mfderiv I I' f x (h.polarComplexStructure x v) =
      hτ.polarComplexStructure (f x) (mfderiv I I' f x v) := by
  -- The differential is a linear isometry between spaces of equal dimension, hence a linear
  -- isometric equivalence, and it is a linear symplectomorphism.
  let e : TangentSpace I x ≃ₗᵢ[ℝ] TangentSpace I' (f x) :=
    ((mfderiv I I' f x).toLinearMap.isometryOfInner hg).toLinearIsometryEquiv hE
  have he : SymplecticForm.IsSymplectomorphism (h.symplecticFormAt x)
      (hτ.symplecticFormAt (f x)) e.toLinearEquiv :=
    SymplecticForm.isSymplectomorphism_iff.2 fun u w ↦ by
      rw [symplecticFormAt_apply, symplecticFormAt_apply]
      exact hσ u w
  rw [polarComplexStructure_apply, polarComplexStructure_apply]
  exact (he.polarComplexStructure_apply v).symm

/-- **Naturality of polar normalization under diffeomorphisms.** A diffeomorphism `ψ : M → N`
which pulls `τ` back to `σ` and is an isometry pulls the polar normalization of `τ` back to the
polar normalization of `σ`. In particular, symplectic isometries of `M` preserve the polar
normalization of its form. -/
theorem pullback_polarComplexStructure (h : σ.IsNondegenerate) (hτ : τ.IsNondegenerate)
    (ψ : M ≃ₘ⟮I, I'⟯ N) (hψ : SmoothForm.mpullback ψ ψ.contMDiff τ = σ)
    (hg : ∀ (x : M) (u v : TangentSpace I x), ⟪mfderiv I I' ψ x u, mfderiv I I' ψ x v⟫ = ⟪u, v⟫) :
    hτ.polarComplexStructure.pullback ψ = h.polarComplexStructure :=
  ((SmoothAlmostComplexStructure.eq_pullback_iff ψ _).2 fun x v ↦
    h.mfderiv_polarComplexStructure_apply hτ
      (ψ.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv.finrank_eq (hg x)
      (fun u w ↦ by rw [← SmoothForm.eval₂_mpullback ψ ψ.contMDiff τ, hψ]) v).symm

end Naturality

end Metric

/-- **Existence of compatible almost complex structures.** On a Hausdorff σ-compact manifold
modelled on a finite-dimensional space, every fiberwise nondegenerate smooth two-form, in
particular every symplectic form, admits a compatible smooth almost complex structure: the polar
normalization of the form for any smooth Riemannian metric. -/
theorem exists_compatible [T2Space M] [SigmaCompactSpace M] (h : σ.IsNondegenerate) :
    ∃ J : SmoothAlmostComplexStructure I M, σ.Compatible J := by
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := I) (n := ⊤) (F := E)
    (E := fun x : M ↦ TangentSpace I x)
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    Bundle.instIsContMDiffRiemannianBundle g
  exact ⟨h.polarComplexStructure, h.compatible_polarComplexStructure⟩

/-- **Existence of invariant compatible almost complex structures for finite groups.** If a finite
group acts smoothly on a Hausdorff σ-compact manifold by maps preserving a fiberwise nondegenerate
smooth two-form `σ`, then `σ` admits a compatible smooth almost complex structure `J` for which
every action map is complex linear: `d(a •)_x ∘ J_x = J_(a • x) ∘ d(a •)_x`. It is the polar
normalization of `σ` for the average of the pullbacks of a smooth Riemannian metric. -/
theorem exists_compatible_mfderiv_smul_apply [T2Space M] [SigmaCompactSpace M] {G : Type*}
    [Group G] [Finite G] [MulAction G M] [ContMDiffConstSMul I ∞ G M] (h : σ.IsNondegenerate)
    (hσ : ∀ (a : G) (x : M) (u v : TangentSpace I x),
      σ.eval₂ (a • x) (mfderiv I I (a • ·) x u) (mfderiv I I (a • ·) x v) = σ.eval₂ x u v) :
    ∃ J : SmoothAlmostComplexStructure I M, σ.Compatible J ∧
      ∀ (a : G) (x : M) (v : TangentSpace I x),
        mfderiv I I (a • ·) x (J x v) = J (a • x) (mfderiv I I (a • ·) x v) := by
  -- The averaged metric is smooth when the action maps are `C^(∞ + 1)`, that is, smooth.
  have : ENat.LEInfty ((∞ : ℕ∞ω) + 1) := ⟨by simp⟩
  have := Fintype.ofFinite G
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := I) (n := ⊤) (F := E)
    (E := fun x : M ↦ TangentSpace I x)
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(averageRiemannianMetric G g).toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    Bundle.instIsContMDiffRiemannianBundle (averageRiemannianMetric G g)
  exact ⟨h.polarComplexStructure, h.compatible_polarComplexStructure, fun a x v ↦
    h.mfderiv_polarComplexStructure_apply h rfl (averageRiemannianMetric_inner_mfderiv G g a x)
      (hσ a x) v⟩

end SmoothTwoForm.IsNondegenerate

end TauCeti
