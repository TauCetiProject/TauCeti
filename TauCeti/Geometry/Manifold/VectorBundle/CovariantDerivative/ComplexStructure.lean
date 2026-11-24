/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Affine
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Hom
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity

/-!
# The complex-linear part of a connection

Let `V` be a real vector bundle with a complex structure `J`, a section of `End(V)` with
`J² = -1`, and let `∇` be a covariant derivative on `V`. In general `J` is not parallel, and
`∇_v (J σ) - J ∇_v σ = (∇_v J) σ` measures the failure of `∇` to be complex linear. The
**complex-linear part** of `∇` is the connection

`∇ᶜ_v σ = ∇_v σ - (1 / 2) J (∇_v J) σ`

(`CovariantDerivative.complexLinearPart`). Where `J` is differentiable it is the average of `∇`
and its conjugate by `J`, `∇ᶜ_v σ = (∇_v σ - J ∇_v (J σ)) / 2`
(`CovariantDerivative.complexLinearPart_apply_eq`), the formula of the complex-linear part
`(F - J F J) / 2` of a real-linear map `F`. It has the following properties.

* `J` is parallel for `∇ᶜ`, equivalently `∇ᶜ` is complex linear:
  `∇ᶜ_v (J σ) = J ∇ᶜ_v σ` (`CovariantDerivative.complexLinearPart_apply_comm`,
  `CovariantDerivative.hom_complexLinearPart_eq_zero`).
* `∇ᶜ = ∇` exactly when `J` is already parallel for `∇`
  (`CovariantDerivative.complexLinearPart_eq_self_iff`).
* The difference `∇ᶜ - ∇ = -(1 / 2) J (∇J)` anticommutes with `J`
  (`CovariantDerivative.difference_complexLinearPart_apply_anticomm`). Conversely, every
  connection for which `J` is parallel and whose difference from `∇` anticommutes with `J` agrees
  with `∇ᶜ` on differentiable sections (`CovariantDerivative.apply_eq_complexLinearPart_apply`).
  The anticommutation comes from that of `∇J` with `J`
  (`CovariantDerivative.hom_apply_apply_anticomm`), the derivative of `J² = -1`.
* If `V` carries a metric for which `∇` is metric and `J` is orthogonal, equivalently
  skew-adjoint, then `∇J` is skew-adjoint
  (`CovariantDerivative.IsMetricCompatible.inner_hom_eq_neg`) and `∇ᶜ` is again metric
  (`CovariantDerivative.IsMetricCompatible.complexLinearPart`). So `∇ᶜ` is a Hermitian
  connection on the complex vector bundle `(V, J)` with the Hermitian metric induced by the real
  one.
* If `∇` and `J` are smooth, so is `∇ᶜ`
  (`CovariantDerivative.contMDiffCovariantDerivative_complexLinearPart`).

For the tangent bundle of an almost Hermitian manifold, its almost complex structure and the
Levi-Civita connection, `∇ᶜ` is the first canonical Hermitian connection, whose difference from
the Levi-Civita connection is the intrinsic torsion `-(1 / 2) J (∇J)`. No integrability of `J`
and no torsion condition on `∇` are assumed. In Taubes's analysis of the Seiberg–Witten
equations on a symplectic four-manifold, the canonical connection on the anticanonical line is
the one induced by this Hermitian connection.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. II, Chapter IX,
  Section 3 (almost complex connections).
* P. Gauduchon, *Hermitian connections and Dirac operators*, Boll. Un. Mat. Ital. B (7) 11
  (1997), 257–288.
* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1
  (1994), 809–822.
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 1 F V I]
  (cov : CovariantDerivative I F V) (J : Π x : M, V x →L[ℝ] V x)

/-- The **complex-linear part** `∇ᶜ_v σ = ∇_v σ - (1 / 2) J (∇_v J) σ` of a covariant derivative
`∇` with respect to a section `J` of `End(V)`. When `J` is a complex structure, `J` is parallel
for `∇ᶜ` (`CovariantDerivative.hom_complexLinearPart_eq_zero`). -/
def complexLinearPart : CovariantDerivative I F V :=
  cov.addOneForm fun x ↦
    letI := (VectorBundle.continuousLinearEquivAt ℝ F V x).isNormableSpace
    letI := (VectorBundle.continuousLinearEquivAt ℝ E (TangentSpace I) x).isNormableSpace
    ((ContinuousLinearMap.postcomp (V x) ((-(2⁻¹ : ℝ)) • J x)).comp (cov.hom cov J x)).flip

/-- The defining formula of the complex-linear part. -/
@[simp]
theorem complexLinearPart_apply (σ : Π x : M, V x) (x : M) (v : TangentSpace I x) :
    cov.complexLinearPart J σ x v = cov σ x v - (2⁻¹ : ℝ) • J x (cov.hom cov J x v (σ x)) := by
  simp [complexLinearPart, sub_eq_add_neg]

variable {cov J}

/-- An endomorphism squaring to `-1` sends `T (T w)` to `-w`. -/
private theorem apply_apply_eq_neg_of_comp_eq_neg_id {W : Type*} [AddCommGroup W] [Module ℝ W]
    [TopologicalSpace W] [IsTopologicalAddGroup W] {T : W →L[ℝ] W}
    (h : T.comp T = -ContinuousLinearMap.id ℝ W) (w : W) : T (T w) = -w := by
  simpa using DFunLike.congr_fun h w

/-- The induced connection on `End(V)` differentiates `J² = -1` to `(∇J) J = -J (∇J)`. -/
theorem hom_apply_apply_anticomm {x : M}
    (hJ : MDiffAt (fun y ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun z ↦ V z →L[ℝ] V z) y (J y)) x)
    (hJ2 : ∀ y, (J y).comp (J y) = -ContinuousLinearMap.id ℝ (V y))
    (v : TangentSpace I x) (u : V x) :
    cov.hom cov J x v (J x u) = -J x (cov.hom cov J x v u) := by
  have hs : MDiffAt (T% (extend F u)) x := mdifferentiableAt_extend ..
  have hJJs : (fun y ↦ J y (J y (extend F u y))) = -extend F u := by
    funext y
    exact apply_apply_eq_neg_of_comp_eq_neg_id (hJ2 y) _
  have h₁ := hom_apply cov cov hJ (hJ.clm_bundle_apply hs) v
  have h₂ := hom_apply cov cov hJ hs v
  simp only [extend_apply_self] at h₁ h₂
  rw [h₁, h₂, hJJs, cov.isCovariantDerivativeOnUniv.neg hs, (J x).map_sub,
    apply_apply_eq_neg_of_comp_eq_neg_id (hJ2 x), neg_apply]
  abel

/-- Where `J` is a complex structure differentiable at `x`, the complex-linear part of `∇` is the
average of `∇` and its conjugate `-J ∇ J`: `∇ᶜ_v σ = (∇_v σ - J ∇_v (J σ)) / 2`. -/
theorem complexLinearPart_apply_eq {x : M}
    (hJ : MDiffAt (fun y ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun z ↦ V z →L[ℝ] V z) y (J y)) x)
    (hJ2 : (J x).comp (J x) = -ContinuousLinearMap.id ℝ (V x))
    {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) (v : TangentSpace I x) :
    cov.complexLinearPart J σ x v =
      (2⁻¹ : ℝ) • (cov σ x v - J x (cov (fun y ↦ J y (σ y)) x v)) := by
  rw [complexLinearPart_apply, hom_apply cov cov hJ hσ, (J x).map_sub,
    apply_apply_eq_neg_of_comp_eq_neg_id hJ2]
  module

/-- **The complex-linear part is complex linear.** If `J` is a complex structure differentiable
at `x`, then `∇ᶜ_v (J σ) = J ∇ᶜ_v σ` for every section `σ` differentiable at `x`. -/
theorem complexLinearPart_apply_comm {x : M}
    (hJ : MDiffAt (fun y ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun z ↦ V z →L[ℝ] V z) y (J y)) x)
    (hJ2 : ∀ y, (J y).comp (J y) = -ContinuousLinearMap.id ℝ (V y))
    {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) (v : TangentSpace I x) :
    cov.complexLinearPart J (fun y ↦ J y (σ y)) x v = J x (cov.complexLinearPart J σ x v) := by
  have h := hom_apply cov cov hJ hσ v
  rw [complexLinearPart_apply, complexLinearPart_apply, hom_apply_apply_anticomm hJ hJ2]
  simp only [map_sub, map_smul, map_neg, apply_apply_eq_neg_of_comp_eq_neg_id (hJ2 x), neg_neg]
  rw [h]
  module

/-- **`J` is parallel for the complex-linear part.** If `J` is a complex structure differentiable
at `x`, its covariant derivative for the connection induced on `End(V)` by `∇ᶜ` vanishes at
`x`. -/
theorem hom_complexLinearPart_eq_zero {x : M}
    (hJ : MDiffAt (fun y ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun z ↦ V z →L[ℝ] V z) y (J y)) x)
    (hJ2 : ∀ y, (J y).comp (J y) = -ContinuousLinearMap.id ℝ (V y)) :
    (cov.complexLinearPart J).hom (cov.complexLinearPart J) J x = 0 := by
  ext v u
  rw [hom_apply_eq_extend _ _ hJ, complexLinearPart_apply_comm hJ hJ2
    (mdifferentiableAt_extend ..), sub_self, zero_apply, zero_apply]

/-- **The complex-linear part of `∇` is `∇` exactly when `J` is parallel for `∇`.** -/
theorem complexLinearPart_eq_self_iff
    (hJ2 : ∀ y, (J y).comp (J y) = -ContinuousLinearMap.id ℝ (V y)) :
    cov.complexLinearPart J = cov ↔ ∀ x, cov.hom cov J x = 0 := by
  refine ⟨fun h x ↦ ?_, fun h ↦ ?_⟩
  · ext v u
    have hσ := congrArg (fun c : CovariantDerivative I F V ↦ c (extend F u) x v) h
    simp only [complexLinearPart_apply, extend_apply_self, sub_eq_self, smul_eq_zero,
      inv_eq_zero, OfNat.ofNat_ne_zero, false_or] at hσ
    simpa [hσ] using (apply_apply_eq_neg_of_comp_eq_neg_id (hJ2 x) (cov.hom cov J x v u)).symm
  · ext σ x v
    simp [h]

/-- The difference of the complex-linear part from `∇` is the one-form `-(1 / 2) J (∇J)`. -/
@[simp]
theorem difference_complexLinearPart (x : M) (u : V x) (v : TangentSpace I x) :
    (cov.complexLinearPart J).difference cov x u v = -(2⁻¹ : ℝ) • J x (cov.hom cov J x v u) := by
  rw [difference_apply_eq_extend, sub_apply, complexLinearPart_apply,
    extend_apply_self]
  module

/-- The difference of the complex-linear part from `∇` anticommutes with a complex structure `J`
differentiable at `x`. -/
theorem difference_complexLinearPart_apply_anticomm {x : M}
    (hJ : MDiffAt (fun y ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun z ↦ V z →L[ℝ] V z) y (J y)) x)
    (hJ2 : ∀ y, (J y).comp (J y) = -ContinuousLinearMap.id ℝ (V y))
    (u : V x) (v : TangentSpace I x) :
    (cov.complexLinearPart J).difference cov x (J x u) v =
      -J x ((cov.complexLinearPart J).difference cov x u v) := by
  rw [difference_complexLinearPart, difference_complexLinearPart, hom_apply_apply_anticomm hJ hJ2]
  simp

/-- **Uniqueness of the complex-linear part.** Let `J` be a complex structure differentiable at
`x`. If `J` is parallel at `x` for a connection `∇'` whose difference from `∇` anticommutes with
`J` at `x`, then `∇'` agrees at `x` with the complex-linear part of `∇` on every section
differentiable at `x`. -/
theorem apply_eq_complexLinearPart_apply {cov' : CovariantDerivative I F V} {x : M}
    (hJ : MDiffAt (fun y ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun z ↦ V z →L[ℝ] V z) y (J y)) x)
    (hJ2 : (J x).comp (J x) = -ContinuousLinearMap.id ℝ (V x))
    (hpar : cov'.hom cov' J x = 0)
    (hanti : ∀ (u : V x) (v : TangentSpace I x),
      cov'.difference cov x (J x u) v = -J x (cov'.difference cov x u v))
    {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) :
    cov' σ x = cov.complexLinearPart J σ x := by
  ext v
  have hJσ := hJ.clm_bundle_apply hσ
  -- `J` parallel for `∇'` gives `∇'_v (J σ) = J ∇'_v σ`.
  have h' := hom_apply cov' cov' hJ hσ v
  rw [hpar, zero_apply, zero_apply] at h'
  have hd := cov'.difference_apply cov hσ
  have hdJ := cov'.difference_apply cov hJσ
  have hdv := congrArg (fun T ↦ T v) hd
  have hdJv := congrArg (fun T ↦ T v) hdJ
  simp only [sub_apply] at hdv hdJv
  rw [hanti] at hdJv
  rw [complexLinearPart_apply, hom_apply cov cov hJ hσ]
  -- Substitute `∇' = ∇ + B` and solve `(∇J) σ = 2 J B σ` for `B σ`.
  have hB : cov' σ x v = cov σ x v + cov'.difference cov x (σ x) v := by rw [hdv]; abel
  have hBJ : cov' (fun y ↦ J y (σ y)) x v =
      cov (fun y ↦ J y (σ y)) x v - J x (cov'.difference cov x (σ x) v) := by
    rw [eq_sub_iff_add_eq] at hdJv
    rw [← hdJv]
    abel
  rw [hBJ, hB, map_add] at h'
  have hE := h'.symm
  rw [sub_eq_zero, sub_eq_iff_eq_add'] at hE
  rw [hB, hE]
  simp only [map_add, map_sub, apply_apply_eq_neg_of_comp_eq_neg_id hJ2]
  module

end General

section Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
  [IsContMDiffRiemannianBundle I 1 F V]
  {cov : CovariantDerivative I F V} {J : Π x : M, V x →L[ℝ] V x}

/-- **The complex-linear part of a metric connection is metric.** If `∇` is metric and `J` is a
skew-adjoint complex structure, equivalently an orthogonal one, differentiable everywhere, then
the complex-linear part `∇ᶜ` of `∇` is metric. Since `J` is parallel for `∇ᶜ`
(`CovariantDerivative.hom_complexLinearPart_eq_zero`), `∇ᶜ` is a Hermitian connection on
`(V, J)`. -/
theorem IsMetricCompatible.complexLinearPart (hcov : cov.IsMetricCompatible)
    (hJ : ∀ x, MDiffAt (fun y ↦ TotalSpace.mk' (F →L[ℝ] F)
      (E := fun z ↦ V z →L[ℝ] V z) y (J y)) x)
    (hJ2 : ∀ y, (J y).comp (J y) = -ContinuousLinearMap.id ℝ (V y))
    (hskew : ∀ y (u w : V y), inner ℝ (J y u) w = -inner ℝ u (J y w)) :
    (cov.complexLinearPart J).IsMetricCompatible := by
  refine (isMetricCompatible_iff_inner_difference_add_inner_difference_eq_zero hcov).2
    fun x v u w ↦ ?_
  -- The one-form `-(1 / 2) J (∇J)` is skew-adjoint because `∇J` is and anticommutes with `J`.
  have h₁ := hskew x (cov.hom cov J x v u) w
  have h₂ := hcov.inner_hom_eq_neg (hJ x) (.of_forall hskew) v u (J x w)
  rw [hom_apply_apply_anticomm (hJ x) hJ2, inner_neg_right] at h₂
  rw [difference_complexLinearPart, difference_complexLinearPart, real_inner_smul_left,
    real_inner_smul_right]
  linarith

end Metric

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  {cov : CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]
  {J : Π x : M, V x →L[ℝ] V x}

/-- The complex-linear part of a smooth connection with respect to a smooth section `J` of
`End(V)` is smooth. -/
theorem contMDiffCovariantDerivative_complexLinearPart
    (hJ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun y ↦ V y →L[ℝ] V y) x (J x))) :
    ContMDiffCovariantDerivative (cov.complexLinearPart J) ∞ where
  contMDiff.contMDiff {σ} hσ := by
    rw [contMDiffOn_univ] at hσ ⊢
    refine (TauCeti.Manifold.contMDiff_hom_iff _).2 fun X hX ↦ ?_
    have h₁ := cov.contMDiff_apply hX (by simpa using hσ)
    have h₂ := hJ.clm_bundle_apply
      (((contMDiff_hom cov cov hJ).clm_bundle_apply hX).clm_bundle_apply (by simpa using hσ))
    refine (h₁.sub_section ((contMDiff_const (c := (2⁻¹ : ℝ))).smul_section h₂)).congr
      fun x ↦ ?_
    simp

end Smooth

end CovariantDerivative
