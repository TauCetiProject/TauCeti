/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent
public import TauCeti.Geometry.Manifold.VectorBundle.Euler
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# The norm of covectors on a Riemannian manifold

A Riemannian metric `g` on a finite-dimensional manifold `M` induces a norm on each cotangent
space `T*ₓM`: the operator norm of a covector `p` for the norm of `g` on `TₓM`, which is the norm
of its Riesz dual, `‖p‖² = p(p♯)`. This file studies the function `z ↦ ‖z.2‖` on the total space
of the cotangent bundle `T*M = TauCeti.CotangentBundle I M`.

In the chart-local frame `(eᵢ)` of `TM` at a point, `‖p‖² = Σᵢⱼ gⁱʲ p(eᵢ) p(eⱼ)`, where `gⁱʲ` is
the inverse Gram matrix of the frame. The components `p(eᵢ)` are the bundle coordinates of `p`,
so this formula shows that `z ↦ ‖z.2‖²` is `C^n` on `T*M` when `g` is
(`TauCeti.CotangentBundle.contMDiff_norm_snd_sq`). Consequently the norm itself is continuous, and
`C^n` away from the zero section.

Along the fibre ray `t ↦ t • z` the norm is `t ↦ |t| ‖z.2‖`, so its differential does not vanish
off the zero section: every nonzero value is a regular value of `z ↦ ‖z.2‖`
(`TauCeti.CotangentBundle.isRegularValue_norm_snd`). Its levels are the cosphere bundles of `g`,
which are therefore smooth hypersurfaces of `T*M` when `M` has no boundary.

## Main results

* `TauCeti.CotangentBundle.contMDiff_norm_snd_sq`: the squared norm of covectors is as smooth as
  the metric.
* `TauCeti.CotangentBundle.continuous_norm_snd`: the norm of covectors is continuous on `T*M`.
* `TauCeti.CotangentBundle.contMDiffAt_norm_snd`: it is as smooth as the metric off the zero
  section.
* `TauCeti.CotangentBundle.mfderiv_norm_snd_vectorBundleEulerField`: the differential of the norm
  sends the Euler vector field `p ∂_p` to the norm.
* `TauCeti.CotangentBundle.isRegularPoint_norm_snd` and
  `TauCeti.CotangentBundle.isRegularValue_norm_snd`: every covector other than zero is a regular
  point, and every nonzero value a regular value.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2 (unit cotangent bundles).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2 (the metric on covectors).
-/

public section

noncomputable section

open Bundle Set Filter Riemannian.Tensor
open scoped Manifold Topology ContDiff Matrix

namespace TauCeti

namespace CotangentBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The components of a covector in the chart-local frame at `a` are its bundle coordinates at
`a`, evaluated on the basis of the model space. -/
private theorem inCoordinates_apply_finBasis (a : M) (z : CotangentBundle I M)
    (j : Fin (Module.finrank ℝ E)) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I) ℝ (Bundle.Trivial M ℝ) a z.proj a
        z.proj z.2 (Module.finBasis ℝ E j) =
      z.2 (chartLocalFrame (I := I) a j z.proj) := by
  simp only [ContinuousLinearMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
    Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_apply, chartLocalFrame_eq_symmL]

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

section Smooth

variable {n : ℕ∞ω} [IsManifold I (n + 1) M]
  [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]

/-- **The squared norm of covectors is smooth.** For a `C^n` Riemannian metric, the function
`z ↦ ‖z.2‖²` on the cotangent bundle is `C^n`. -/
theorem contMDiff_norm_snd_sq :
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) n
      (fun z : CotangentBundle I M ↦ ‖z.2‖ ^ 2) := by
  intro z₀
  set a := z₀.proj
  have hbase : (chartAt H a).source ∈ 𝓝 a :=
    (chartAt H a).open_source.mem_nhds (mem_chart_source H a)
  -- The components `z.2 (eⱼ)` in the chart-local frame at `a` are bundle coordinates of `z`.
  have hc (j : Fin (Module.finrank ℝ E)) :
      ContMDiffAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) n
        (fun z : CotangentBundle I M ↦ z.2 (chartLocalFrame (I := I) a j z.proj)) z₀ := by
    have h := (((contMDiffAt_hom_bundle (IB := I) (n := n) (id : CotangentBundle I M → _)).1
      (contMDiffAt_id (x := z₀))).2).clm_apply (contMDiffAt_const (c := Module.finBasis ℝ E j))
    exact h.congr_of_eventuallyEq
      (Eventually.of_forall fun z ↦ (inCoordinates_apply_finBasis a z j).symm)
  -- The inverse Gram entries at the base point are smooth near `a`.
  have hG (i j : Fin (Module.finrank ℝ E)) :
      ContMDiffAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) n
        (fun z : CotangentBundle I M ↦ chartInvGramMatrix (I := I) a z.proj i j) z₀ := by
    have h := contMDiffOn_chartInvGramMatrix_entry (I := I) (n := n) a i j
    rw [TangentBundle.trivializationAt_baseSet] at h
    exact (h.contMDiffAt hbase).comp z₀
      (Bundle.contMDiff_proj (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) z₀)
  have hsum : ContMDiffAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) n
      (fun z : CotangentBundle I M ↦ ∑ i, (∑ j, chartInvGramMatrix (I := I) a z.proj i j *
        z.2 (chartLocalFrame (I := I) a j z.proj)) * z.2 (chartLocalFrame (I := I) a i z.proj))
      z₀ :=
    contMDiffAt_finsetSum fun i _ ↦
      (contMDiffAt_finsetSum fun j _ ↦ (hG i j).mul (hc j)).mul (hc i)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [(FiberBundle.continuous_proj (E →L[ℝ] ℝ)
    (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)).continuousAt.preimage_mem_nhds hbase] with z hz
  rw [norm_sq_eq_dotProduct_chartInvGramMatrix_mulVec (I := I) a hz]
  simp only [dotProduct, Matrix.mulVec, mul_comm]

/-- Off the zero section, the norm of covectors is as smooth as the metric. -/
theorem contMDiffAt_norm_snd {z : CotangentBundle I M} (hz : z.2 ≠ 0) :
    ContMDiffAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) n (fun z : CotangentBundle I M ↦ ‖z.2‖) z := by
  have hne : ‖z.2‖ ^ 2 ≠ 0 := pow_ne_zero 2 ((norm_ne_zero_iff (a := z.2)).2 hz)
  refine ((Real.contDiffAt_sqrt hne).comp_contMDiffAt
    (f := fun z : CotangentBundle I M ↦ ‖z.2‖ ^ 2) (contMDiff_norm_snd_sq z)).congr_of_eventuallyEq
    (Eventually.of_forall fun z ↦ ?_)
  exact (Real.sqrt_sq (norm_nonneg z.2)).symm

end Smooth

/-- The norm of covectors is continuous on the cotangent bundle of a manifold with a continuous
Riemannian metric. -/
theorem continuous_norm_snd [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)] :
    Continuous fun z : CotangentBundle I M ↦ ‖z.2‖ := by
  have : IsManifold I (0 + 1) M := by rwa [zero_add]
  exact (contMDiff_norm_snd_sq (I := I) (M := M) (n := 0)).continuous.sqrt.congr fun z ↦
    Real.sqrt_sq (norm_nonneg z.2)

section Regular

variable [IsManifold I 2 M] [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **The norm of covectors along the Euler vector field.** At a covector `z` other than zero,
the differential of `z ↦ ‖z.2‖` sends the Euler vector field `p ∂_p` to `‖z.2‖`: along the fibre
ray `t ↦ t • z` the norm is `t ↦ |t| ‖z.2‖`. -/
theorem mfderiv_norm_snd_vectorBundleEulerField {z : CotangentBundle I M} (hz : z.2 ≠ 0) :
    mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) (fun z : CotangentBundle I M ↦ ‖z.2‖) z
      (vectorBundleEulerField I z) = ‖z.2‖ := by
  set f : CotangentBundle I M → ℝ := fun z ↦ ‖z.2‖
  set γ : ℝ → CotangentBundle I M := fun t ↦ ⟨z.proj, t • z.2⟩
  have hγ : HasMFDerivAt 𝓘(ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) γ 1
      ((1 : ℝ →L[ℝ] ℝ).smulRight (vectorBundleEulerField I z)) :=
    hasMFDerivAt_vectorBundleEulerField z
  have hγ1 : γ 1 = z := by simp [γ]
  have hf : MDifferentiableAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) f (γ 1) := by
    rw [hγ1]
    have : IsManifold I (1 + 1) M := by norm_num; infer_instance
    exact (contMDiffAt_norm_snd (n := 1) hz).mdifferentiableAt one_ne_zero
  -- Near `t = 1`, the norm along the ray is `t ↦ t * ‖z.2‖`.
  have hray : HasDerivAt (f ∘ γ) ‖z.2‖ 1 := by
    refine (hasDerivAt_mul_const ‖z.2‖).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds one_pos] with t ht
    -- This is `norm_smul`; instance search does not find `NormSMulClass` for covectors of the
    -- Riemannian fibre norm, so it is supplied from the `NormedSpace` instance.
    exact ((NormedSpace.toNormSMulClass (𝕜 := ℝ) (E := TangentSpace I z.proj →L[ℝ] ℝ)).norm_smul
      t z.2).trans (by rw [Real.norm_of_nonneg ht.le])
  -- The velocity of the ray at `t = 1`, for the unit tangent vector of `ℝ`, is the Euler field.
  have hv : mfderiv 𝓘(ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) γ 1
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (1 : ℝ)).symm 1) = vectorBundleEulerField I z := by
    rw [hγ.mfderiv]
    exact one_smul ℝ _
  have hd : mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) f (γ 1) (mfderiv 𝓘(ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      γ 1 ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (1 : ℝ)).symm 1)) = ‖z.2‖ := by
    rw [← ContinuousLinearMap.comp_apply, ← mfderiv_comp 1 hf hγ.mdifferentiableAt,
      mfderiv_eq_fderiv, hray.hasFDerivAt.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul]
    -- `NormedSpace.fromTangentSpace` is the identity of `ℝ`.
    rfl
  rwa [hv, hγ1] at hd

/-- **Covectors other than zero are regular points of the norm.** Every covector `z` with
`z.2 ≠ 0` is a regular point of `z ↦ ‖z.2‖`. -/
theorem isRegularPoint_norm_snd {z : CotangentBundle I M} (hz : z.2 ≠ 0) :
    IsRegularPoint (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ)
      (fun z : CotangentBundle I M ↦ ‖z.2‖) z := by
  -- The differential of the norm sends the Euler vector field to `‖z.2‖ ≠ 0`, so it is
  -- surjective; the tangent spaces of `ℝ` are `ℝ` itself, read through
  -- `NormedSpace.fromTangentSpace`.
  rw [isRegularPoint_iff]
  intro y
  refine ⟨(NormedSpace.fromTangentSpace (𝕜 := ℝ) ‖z.2‖ y / ‖z.2‖) • vectorBundleEulerField I z, ?_⟩
  rw [map_smul, mfderiv_norm_snd_vectorBundleEulerField hz]
  exact div_mul_cancel₀ _ ((norm_ne_zero_iff (a := z.2)).2 hz)

/-- **Every nonzero value is a regular value of the norm of covectors.** Its levels are the
cosphere bundles of the metric. -/
theorem isRegularValue_norm_snd {c : ℝ} (hc : c ≠ 0) :
    IsRegularValue (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ)
      (fun z : CotangentBundle I M ↦ ‖z.2‖) c := by
  rw [isRegularValue_iff]
  rintro z rfl
  exact isRegularPoint_norm_snd fun h ↦ hc ((ContinuousLinearMap.opNorm_zero_iff z.2).2 h)

end Regular

end CotangentBundle

end TauCeti
