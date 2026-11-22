/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.InnerProductSpace.PartialIsometry
import TauCeti.Analysis.InnerProductSpace.Projection.Completeness
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.IdempotentRange

/-!
# The orthogonal projection onto the range of an operator

If `B : F →L[𝕜] V` is an operator between inner product spaces whose Gram operator `B† B` is
invertible, the orthogonal projection of `V` onto the range of `B` is `B (B† B)⁻¹ B†`. When `F` is
finite-dimensional, `B† B` is invertible exactly when `B` is injective.

Over `ℝ` or `ℂ` this formula gives continuity for arbitrary topological parameter spaces
(`ContinuousAt.starProjection_range`), with no inner product required on the source model.
Over `ℝ` or `ℂ` it also shows that the projection depends smoothly on the operator: for a
real `C^n` family of injective operators `A u : E →L[𝕜] V` out of a finite-dimensional normed
space `E`, the orthogonal projections of `V` onto the ranges of `A u` form a `C^n` family. Applied
to the derivative of an immersion into a Euclidean space, this says that the tangent spaces, and
hence the normal spaces, of an immersed submanifold vary smoothly. Neither result needs `V` to be
complete: the formula is applied after embedding `V` into its completion.

Similarly, for an operator `ι : E →L[𝕜] V` into a Hilbert space, for instance the inclusion of a
Sobolev space into `L²`, and `κ : F →L[𝕜] E` with `A = ι κ`, when the Gram operator `A† A` is
invertible (for finite-dimensional `F`, when `ι κ` is injective), the operator `κ (A† A)⁻¹ A† ι` is
the projection of `E` onto the range of `κ` along its `ι`-orthogonal complement. Near such `κ` it
depends continuously, and over `ℝ` or `ℂ` real-smoothly, on `κ`.

## Main results

* `ContinuousLinearMap.isClosed_range_of_isUnit_adjoint_comp`,
  `ContinuousLinearMap.hasOrthogonalProjection_range_of_isUnit_adjoint_comp`: an operator with
  invertible Gram operator `B† B` has closed range and admits an orthogonal projection onto it.
* `ContinuousLinearMap.starProjection_range_eq_comp_comp_adjoint`: if `B† B G B† = B†`, the
  orthogonal projection onto the range of `B` is `B G B†`.
* `ContinuousLinearMap.starProjection_range_eq`: the formula `B (B† B)⁻¹ B†` for the orthogonal
  projection onto the range of `B`.
* `ContinuousLinearMap.comp_adjoint_eq_starProjection_range`: for an isometry `B` it reduces to
  `B B†`.
* `ContinuousLinearMap.gramLeftInverse`: the left inverse `(A† A)⁻¹ A†`
  (`ContinuousLinearMap.gramLeftInverse_def`) of `A` when `A† A` is invertible
  (`ContinuousLinearMap.gramLeftInverse_comp_self`,
  `ContinuousLinearMap.gramLeftInverse_apply_apply`), with
  `ContinuousLinearMap.continuousAt_gramLeftInverse` and
  `ContinuousLinearMap.contDiffAt_gramLeftInverse`.
* `ContinuousLinearMap.gramProjection`: the projection `κ (A† A)⁻¹ A† ι`
  (`ContinuousLinearMap.gramProjection_def`) onto the range of `κ` along its `ι`-orthogonal
  complement (`ContinuousLinearMap.gramProjection_apply_apply`,
  `ContinuousLinearMap.gramProjection_inner_eq_zero`), continuous and real `C^n` in `κ`
  (`ContinuousLinearMap.continuousAt_gramProjection`,
  `ContinuousLinearMap.contDiffAt_gramProjection`).
* `LinearMap.finrank_orthogonal_range_of_injective`: the dimension of the orthogonal
  complement of the range of an injective operator.
* `Submodule.starProjection_inverse_apply`: if the compression to `W` of the orthogonal projection
  onto `K` is invertible, it inverts the projection from `W` onto `K`.
* `ContinuousAt.starProjection_range`: the orthogonal projection onto the range of a family of
  operators out of a finite-dimensional space is continuous at each point where the family is
  continuous and the operator is injective; the parameter space is any topological space.
* `LinearIsometry.starProjection_range_comp_comm`: the projection onto the range of an operator
  commutes with a linear isometry.
* `ContDiffAt.starProjection_range`, `ContDiffAt.starProjection_orthogonal_range`: the orthogonal
  projections onto the range of a `C^n` family of injective operators, and onto its orthogonal
  complement, are `C^n`.
* `ContinuousLinearMap.starProjection_range_comp_eq`: for a star projection `P`, the orthogonal
  projection onto the image `L (range P)` is `Q A⁻¹ Q†`, where `Q = L P` and `A = Q† Q + (1 - P)`.
* `ContinuousLinearMap.isUnit_adjoint_comp_add_one_sub_iff_injOn`: on a finite-dimensional space,
  `A` is invertible exactly when `L` is injective on the range of `P`; `L` itself need not be
  injective.
* `ContinuousLinearMap.isOpen_setOf_injOn_range`,
  `ContinuousLinearMap.continuousOn_starProjection_range_comp`: when `E` is finite-dimensional, the
  pairs `(L, P)` with `L` injective on the range of `P` form an open set, on which the orthogonal
  projection onto `L (range P)` depends continuously on `(L, P)`.
* `ContinuousLinearMap.comp_comp_adjoint_eq_starProjection_range_comp`: for an isometry `B`, this
  projection is `B P B†`.

Recording a subspace by its orthogonal projection, `starProjection_range_comp_eq`,
`isOpen_setOf_injOn_range`, `continuousOn_starProjection_range_comp` and
`comp_comp_adjoint_eq_starProjection_range_comp` describe how a linear map moves subspaces: this is
the map on Grassmannians induced by `L` (L. Simon, *Lectures on
Geometric Measure Theory*, §38), used to push forward measures on spaces of planes along maps whose
differentials are injective only on the planes concerned.
-/

public section

open Function Filter Topology

namespace ContinuousLinearMap

variable {𝕜 F V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

section Adjoint

variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] [CompleteSpace V]

/-- The left inverse `(A† A)⁻¹ A†` of an operator `A` whose Gram operator `A† A` is invertible
(`ContinuousLinearMap.gramLeftInverse_comp_self`). Its composite with `A` on the left is the
orthogonal projection onto the range of `A` (`ContinuousLinearMap.starProjection_range_eq`). -/
noncomputable def gramLeftInverse (A : F →L[𝕜] V) : V →L[𝕜] F :=
  Ring.inverse (adjoint A ∘L A) ∘L adjoint A

/-- The defining formula `(A† A)⁻¹ A†` of `ContinuousLinearMap.gramLeftInverse`. -/
theorem gramLeftInverse_def (A : F →L[𝕜] V) :
    gramLeftInverse A = Ring.inverse (adjoint A ∘L A) ∘L adjoint A := by
  rw [gramLeftInverse]

/-- `(A† A)⁻¹ A†` is a left inverse of `A` when `A† A` is invertible. -/
@[simp]
theorem gramLeftInverse_comp_self {A : F →L[𝕜] V} (hA : IsUnit (adjoint A ∘L A)) :
    gramLeftInverse A ∘L A = 1 := by
  rw [gramLeftInverse, comp_assoc, ← mul_def, Ring.inverse_mul_cancel _ hA]

/-- `(A† A)⁻¹ A†` recovers `v` from `A v` when `A† A` is invertible. -/
@[simp]
theorem gramLeftInverse_apply_apply {A : F →L[𝕜] V} (hA : IsUnit (adjoint A ∘L A)) (v : F) :
    gramLeftInverse A (A v) = v :=
  congr($(gramLeftInverse_comp_self hA) v)

/-- `A† A (A† A)⁻¹ A† = A†` when `A† A` is invertible: `v - A (A† A)⁻¹ A† v` lies in the kernel
of `A†`. -/
theorem adjoint_comp_self_comp_gramLeftInverse {A : F →L[𝕜] V} (hA : IsUnit (adjoint A ∘L A)) :
    adjoint A ∘L A ∘L gramLeftInverse A = adjoint A := by
  simp [gramLeftInverse, ← comp_assoc, ← mul_def, Ring.mul_inverse_cancel _ hA, one_def]

/-- The left inverse `(A† A)⁻¹ A†` depends continuously on `A` where `A† A` is invertible. -/
theorem continuousAt_gramLeftInverse {A : F →L[𝕜] V}
    (hA : IsUnit (adjoint A ∘L A)) :
    ContinuousAt (gramLeftInverse : (F →L[𝕜] V) → V →L[𝕜] F) A := by
  have ha : ContinuousAt (adjoint : (F →L[𝕜] V) → V →L[𝕜] F) A :=
    adjoint.continuous.continuousAt
  have hi := NormedRing.inverse_continuousAt hA.unit
  rw [hA.unit_spec] at hi
  unfold gramLeftInverse
  exact (hi.comp (f := fun B : F →L[𝕜] V ↦ adjoint B ∘L B)
    (ha.clm_comp continuousAt_id)).clm_comp ha

/-- The left inverse `(A† A)⁻¹ A†` is a real `C^n` function of `A` where `A† A` is invertible, also
for complex operators. -/
theorem contDiffAt_gramLeftInverse
    [NormedSpace ℝ F] [NormedSpace ℝ V]
    {A : F →L[𝕜] V} (hA : IsUnit (adjoint A ∘L A)) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (gramLeftInverse : (F →L[𝕜] V) → V →L[𝕜] F) A := by
  have ha : ContDiff ℝ n (adjoint : (F →L[𝕜] V) → V →L[𝕜] F) := contDiff_id.clm_adjoint
  have hgram : ContDiff ℝ n (fun B : F →L[𝕜] V ↦ adjoint B ∘L B) := by
    simpa using
      (((compL 𝕜 F V F).bilinearRestrictScalars ℝ).contDiff.comp ha).clm_apply contDiff_id
  have hi := (contDiffAt_ringInverse 𝕜 (n := n) hA.unit).restrict_scalars ℝ
  rw [hA.unit_spec] at hi
  unfold gramLeftInverse
  exact (((compL 𝕜 V F F).bilinearRestrictScalars ℝ).contDiff.contDiffAt.comp A
    (hi.comp (f := fun B : F →L[𝕜] V ↦ adjoint B ∘L B) A hgram.contDiffAt)).clm_apply
      ha.contDiffAt

/-- An operator whose Gram operator `B† B` is invertible has closed range. -/
theorem isClosed_range_of_isUnit_adjoint_comp {B : F →L[𝕜] V}
    (hB : IsUnit (adjoint B ∘L B)) : IsClosed (Set.range B) :=
  (show Function.LeftInverse (gramLeftInverse B) B from
    gramLeftInverse_apply_apply hB).isClosed_range (gramLeftInverse B).continuous B.continuous

/-- The range of an operator whose Gram operator `B† B` is invertible admits an orthogonal
projection. -/
theorem hasOrthogonalProjection_range_of_isUnit_adjoint_comp {B : F →L[𝕜] V}
    (hB : IsUnit (adjoint B ∘L B)) : B.range.HasOrthogonalProjection :=
  Submodule.hasOrthogonalProjection_iff_isClosed.mpr
    (by simpa only [LinearMap.coe_range, coe_coe] using isClosed_range_of_isUnit_adjoint_comp hB)

/-- If `B† B G B† = B†`, the orthogonal projection onto the range of `B` is `B G B†`. -/
theorem starProjection_range_eq_comp_comp_adjoint {B : F →L[𝕜] V} {G : F →L[𝕜] F}
    (hG : adjoint B ∘L B ∘L G ∘L adjoint B = adjoint B) :
    letI : B.range.HasOrthogonalProjection := ⟨fun v ↦ ⟨(B ∘L G ∘L adjoint B) v,
      LinearMap.mem_range_self _ _, by
      rintro _ ⟨x, rfl⟩
      rw [coe_coe, ← adjoint_inner_right, map_sub]
      have h := congr($hG v)
      simp only [comp_apply] at h ⊢
      rw [h, sub_self, inner_zero_right]⟩⟩
    B.range.starProjection = B ∘L G ∘L adjoint B := by
  let : B.range.HasOrthogonalProjection := ⟨fun v ↦ ⟨(B ∘L G ∘L adjoint B) v,
    LinearMap.mem_range_self _ _, by
    rintro _ ⟨x, rfl⟩
    rw [coe_coe, ← adjoint_inner_right, map_sub]
    have h := congr($hG v)
    simp only [comp_apply] at h ⊢
    rw [h, sub_self, inner_zero_right]⟩⟩
  ext v
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (LinearMap.mem_range_self _ _) ?_
  rintro _ ⟨x, rfl⟩
  -- Move `B` across the inner product: `B† (v - B G B† v) = B† v - B† v = 0`.
  rw [coe_coe, ← adjoint_inner_left, map_sub]
  have h := congr($hG v)
  simp only [comp_apply] at h ⊢
  rw [h, sub_self, inner_zero_left]

/-- The orthogonal projection onto the range of `B` is `B (B† B)⁻¹ B†`, that is `B` composed with
`ContinuousLinearMap.gramLeftInverse B`, when the Gram operator `B† B` is invertible. -/
theorem starProjection_range_eq {B : F →L[𝕜] V} (hB : IsUnit (adjoint B ∘L B)) :
    letI := hasOrthogonalProjection_range_of_isUnit_adjoint_comp hB
    B.range.starProjection = B ∘L gramLeftInverse B := by
  rw [gramLeftInverse_def]
  exact starProjection_range_eq_comp_comp_adjoint <| by
    simpa only [gramLeftInverse_def] using adjoint_comp_self_comp_gramLeftInverse hB

/-- For an isometry `B`, the operator `B B†` is the orthogonal projection onto the range of `B`. -/
theorem comp_adjoint_eq_starProjection_range {B : F →L[𝕜] V} (hB : Isometry B) :
    letI := hasOrthogonalProjection_range_of_isUnit_adjoint_comp
      ((isometry_iff_adjoint_comp_self B).1 hB ▸ isUnit_one)
    B ∘L adjoint B = B.range.starProjection := by
  have h := (isometry_iff_adjoint_comp_self B).1 hB
  rw [starProjection_range_eq (h ▸ isUnit_one), gramLeftInverse_def, h, Ring.inverse_one,
    one_def, id_comp]

end Adjoint

section GramProjection

open scoped InnerProductSpace

variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] [CompleteSpace V]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The projection `κ (A† A)⁻¹ A† ι` with `A = ι κ`, for an operator `ι : E →L[𝕜] V` into a Hilbert
space and `κ : F →L[𝕜] E`. Where `A† A` is invertible, it projects `E` onto the range of `κ` along
the `ι`-orthogonal complement of that range (`ContinuousLinearMap.gramProjection_apply_apply`,
`ContinuousLinearMap.gramProjection_inner_eq_zero`). -/
noncomputable def gramProjection (ι : E →L[𝕜] V) (κ : F →L[𝕜] E) : E →L[𝕜] E :=
  κ ∘L gramLeftInverse (ι ∘L κ) ∘L ι

/-- The defining formula `κ (A† A)⁻¹ A† ι` of `ContinuousLinearMap.gramProjection`. -/
theorem gramProjection_def (ι : E →L[𝕜] V) (κ : F →L[𝕜] E) :
    gramProjection ι κ = κ ∘L gramLeftInverse (ι ∘L κ) ∘L ι := by
  rw [gramProjection]

/-- The projection `κ (A† A)⁻¹ A† ι` takes values in the range of `κ`. -/
theorem gramProjection_apply_mem_range (ι : E →L[𝕜] V) (κ : F →L[𝕜] E) (e : E) :
    gramProjection ι κ e ∈ κ.range :=
  LinearMap.mem_range_self _ _

/-- The projection `κ (A† A)⁻¹ A† ι` fixes the range of `κ` when `A† A` is invertible. -/
theorem gramProjection_apply_apply {ι : E →L[𝕜] V} {κ : F →L[𝕜] E}
    (hG : IsUnit (adjoint (ι ∘L κ) ∘L (ι ∘L κ))) (v : F) :
    gramProjection ι κ (κ v) = κ v := by
  simpa [gramProjection] using congr(κ ($(gramLeftInverse_comp_self hG) v))

/-- When `A† A` is invertible, `ι (e - κ (A† A)⁻¹ A† ι e)` is orthogonal to the image under `ι` of
the range of `κ`. -/
theorem gramProjection_inner_eq_zero {ι : E →L[𝕜] V} {κ : F →L[𝕜] E}
    (hG : IsUnit (adjoint (ι ∘L κ) ∘L (ι ∘L κ))) (e : E) (v : F) :
    ⟪ι (e - gramProjection ι κ e), ι (κ v)⟫_𝕜 = 0 := by
  have h := congr($(adjoint_comp_self_comp_gramLeftInverse hG) (ι e))
  simp only [comp_apply] at h
  rw [← comp_apply ι κ, ← adjoint_inner_left]
  simp [gramProjection, h]

/-- The projection `κ (A† A)⁻¹ A† ι` depends continuously on `κ` where `A† A` is invertible. -/
theorem continuousAt_gramProjection (ι : E →L[𝕜] V) {κ₀ : F →L[𝕜] E}
    (hG : IsUnit (adjoint (ι ∘L κ₀) ∘L (ι ∘L κ₀))) :
    ContinuousAt (gramProjection ι) κ₀ := by
  have hA : Continuous fun κ : F →L[𝕜] E ↦ ι ∘L κ := (compL 𝕜 F E V ι).continuous
  unfold gramProjection
  exact continuousAt_id.clm_comp
    (((continuousAt_gramLeftInverse hG).comp hA.continuousAt).clm_comp continuousAt_const)

/-- The projection `κ (A† A)⁻¹ A† ι` is a real `C^n` function of `κ` where `A† A` is invertible,
also for complex operators. -/
theorem contDiffAt_gramProjection [NormedSpace ℝ F] [NormedSpace ℝ V] [NormedSpace ℝ E]
    (ι : E →L[𝕜] V) {κ₀ : F →L[𝕜] E} (hG : IsUnit (adjoint (ι ∘L κ₀) ∘L (ι ∘L κ₀)))
    {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (gramProjection ι) κ₀ := by
  have hA : ContDiff ℝ n fun κ : F →L[𝕜] E ↦ ι ∘L κ :=
    ((compL 𝕜 F E V ι).restrictScalars ℝ).contDiff
  have hL := (contDiffAt_gramLeftInverse hG (n := n)).comp κ₀ hA.contDiffAt
  have hLι : ContDiffAt ℝ n (fun κ : F →L[𝕜] E ↦ gramLeftInverse (ι ∘L κ) ∘L ι) κ₀ :=
    ((((compL 𝕜 E V F).flip ι).restrictScalars ℝ).contDiff.contDiffAt.comp κ₀ hL)
  unfold gramProjection
  exact (((compL 𝕜 E F E).bilinearRestrictScalars ℝ).contDiff.contDiffAt.comp κ₀
    contDiffAt_id).clm_apply hLι

end GramProjection

section Range

variable [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]

/-- The orthogonal projection onto the range of `B` fixes every value of `B`. -/
@[simp]
theorem starProjection_range_apply (B : F →L[𝕜] V) [B.range.HasOrthogonalProjection] (x : F) :
    B.range.starProjection (B x) = B x :=
  Submodule.starProjection_eq_self_iff.2 (LinearMap.mem_range_self (B : F →ₗ[𝕜] V) x)

/-- The orthogonal projection onto the complement of the range of `B` kills every value of `B`. -/
theorem starProjection_orthogonal_range_apply (B : F →L[𝕜] V) [B.range.HasOrthogonalProjection]
    (x : F) : B.rangeᗮ.starProjection (B x) = 0 :=
  Submodule.starProjection_orthogonal_apply_eq_zero (LinearMap.mem_range_self (B : F →ₗ[𝕜] V) x)

/-- An operator followed by the orthogonal projection onto its range is unchanged. -/
@[simp]
theorem starProjection_range_comp (B : F →L[𝕜] V) [B.range.HasOrthogonalProjection] :
    B.range.starProjection ∘L B = B := by
  ext x
  simp

/-- An operator followed by the orthogonal projection onto the complement of its range is zero. -/
@[simp]
theorem starProjection_orthogonal_range_comp (B : F →L[𝕜] V) [B.range.HasOrthogonalProjection] :
    B.rangeᗮ.starProjection ∘L B = 0 := by
  ext x
  simp

end Range

end ContinuousLinearMap

section LinearMap

variable {𝕜 E V : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- The orthogonal complement of the range of an injective operator into a finite-dimensional
inner product space has the expected dimension. -/
theorem LinearMap.finrank_orthogonal_range_of_injective {A : E →ₗ[𝕜] V}
    (hA : Injective A) :
    Module.finrank 𝕜 A.rangeᗮ = Module.finrank 𝕜 V - Module.finrank 𝕜 E := by
  have h := Submodule.finrank_add_finrank_orthogonal A.range
  rw [LinearMap.finrank_range_of_inj hA] at h
  omega

end LinearMap

section Submodule

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- Let `K` be a finite-dimensional subspace and `W` a projected subspace of the same dimension.
If the compression `R = π_W ∘ P_K ∘ ι_W` of the orthogonal projection onto `K` is invertible, then
`P_K` maps `W` onto `K`, and the preimage of `v ∈ K` is `R⁻¹ (π_W v)`. -/
theorem Submodule.starProjection_inverse_apply {K W : Submodule 𝕜 V}
    [FiniteDimensional 𝕜 K] [W.HasOrthogonalProjection]
    (hrank : Module.finrank 𝕜 W = Module.finrank 𝕜 K)
    (hR : IsUnit (W.orthogonalProjectionOnto ∘L K.starProjection ∘L W.subtypeL)) {v : V}
    (hv : v ∈ K) :
    K.starProjection (Ring.inverse (W.orthogonalProjectionOnto ∘L K.starProjection ∘L W.subtypeL)
      (W.orthogonalProjectionOnto v)) = v := by
  set R := W.orthogonalProjectionOnto ∘L K.starProjection ∘L W.subtypeL
  have hRR (y : W) : R (Ring.inverse R y) = y := by
    rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel _ hR, one_apply_eq_self]
  -- `R` factors through `σ = π_W ∘ ι_K`, so `σ` is onto `W`, hence injective by the dimension
  -- count. Both `P_K (R⁻¹ (π_W v))` and `v` lie in `K` and have the same image under `σ`.
  let σ : K →ₗ[𝕜] W := W.orthogonalProjectionOnto.toLinearMap ∘ₗ K.subtype
  have hσ : Surjective σ := fun y => ⟨K.orthogonalProjectionOnto (Ring.inverse R y), by
    simpa [R, σ] using hRR y⟩
  have : FiniteDimensional 𝕜 W := .of_surjective σ hσ
  have hσ' := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank.symm).2 hσ
  exact congrArg Subtype.val <| hσ' (show σ ⟨_, K.starProjection_apply_mem _⟩ = σ ⟨v, hv⟩ by
    simpa [R, σ] using hRR (W.orthogonalProjectionOnto v))

end Submodule

section LinearIsometry

variable {𝕜 E V W : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

/-- The orthogonal projection onto the range of an operator commutes with a linear isometry:
projecting onto the range of `f ∘L A` after applying `f` is applying `f` after projecting onto the
range of `A`. -/
theorem LinearIsometry.starProjection_range_comp_comm (f : V →ₗᵢ[𝕜] W) (A : E →L[𝕜] V)
    [A.range.HasOrthogonalProjection]
    [(f.toContinuousLinearMap ∘L A).range.HasOrthogonalProjection] :
    (f.toContinuousLinearMap ∘L A).range.starProjection ∘L f.toContinuousLinearMap =
      f.toContinuousLinearMap ∘L A.range.starProjection := by
  ext v
  have hrange : (f.toContinuousLinearMap ∘L A).range = A.range.map f.toLinearMap :=
    LinearMap.range_comp _ _
  have : (A.range.map f.toLinearMap).HasOrthogonalProjection := hrange ▸ inferInstance
  refine Eq.symm ((f.map_starProjection A.range v).trans ?_)
  simp only [hrange, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]

end LinearIsometry

section GramFormula

open ContinuousLinearMap UniformSpace UniformSpace.Completion

variable {𝕜 E F V : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- Near an injective operator `T₀` out of a finite-dimensional space `E`, the orthogonal projection
onto the range of `T` is the Gram projection `T j (B† B)⁻¹ B† ι`, where `ι = toComplL` embeds `V`
into its completion and `B = ι T j`. Here `j : F ≃L E` identifies `E` with a complete inner product
space `F`, so that the adjoint of `B` exists although `V` need not be complete. -/
private theorem eventuallyEq_starProjection_range (j : F ≃L[𝕜] E) {T₀ : E →L[𝕜] V}
    (hT₀ : Injective T₀) :
    (fun T : E →L[𝕜] V ↦ T.range.starProjection) =ᶠ[𝓝 T₀] fun T ↦
      gramProjection toComplL (T ∘L (j : F →L[𝕜] E)) := by
  have : FiniteDimensional 𝕜 F := j.symm.toLinearEquiv.finiteDimensional
  filter_upwards [isOpen_injective.mem_nhds hT₀] with T hT
  set B := toComplL ∘L T ∘L (j : F →L[𝕜] E) with hB
  have hrange : B.range = (toComplL ∘L T).range := by
    rw [hB, ← ContinuousLinearMap.comp_assoc]
    exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr j.surjective)
  have hP := starProjection_range_eq ((isUnit_adjoint_comp_self_iff B).2
    ((coe_injective V).comp (hT.comp j.injective)))
  simp only [hrange] at hP
  -- Compare both sides after embedding `V` into its completion, where the projection onto the
  -- range of `toComplL ∘L T` is given by `hP`.
  ext v
  refine coe_injective V ?_
  have hcomm := congr($(LinearIsometry.starProjection_range_comp_comm toComplₗᵢ T) v)
  simp only [toContinuousLinearMap_toComplₗᵢ, hP] at hcomm
  simpa [B, gramProjection_def, comp_assoc] using hcomm.symm

end GramFormula

section ContinuousAt

open ContinuousLinearMap UniformSpace UniformSpace.Completion

variable {𝕜 X E V : Type*} [RCLike 𝕜] [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- Orthogonal projection onto the range depends continuously on an operator out of a
finite-dimensional space at every injective operator. The parameter space is arbitrary. The
inner product space `V` need not be complete. -/
theorem ContinuousAt.starProjection_range {A : X → E →L[𝕜] V} {x : X}
    (hA : ContinuousAt A x) (hinj : Injective (A x)) :
    ContinuousAt (fun y ↦ (A y).range.starProjection) x := by
  -- Use Euclidean coordinates on the source to take adjoints without choosing a metric on `E`.
  let F := EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 E))
  let j : F ≃L[𝕜] E := .ofFinrankEq (by simp [F])
  have hj : ContinuousAt (fun y ↦ A y ∘L (j : F →L[𝕜] E)) x := hA.clm_comp continuousAt_const
  have hG := (isUnit_adjoint_comp_self_iff
    ((toComplL : V →L[𝕜] Completion V) ∘L A x ∘L (j : F →L[𝕜] E))).2
    ((coe_injective V).comp (hinj.comp j.injective))
  refine ((continuousAt_gramProjection toComplL hG).comp
    (f := fun y ↦ A y ∘L (j : F →L[𝕜] E)) hj).congr_of_eventuallyEq ?_
  exact (eventuallyEq_starProjection_range j hinj).comp_tendsto hA

end ContinuousAt

section ContDiffAt

open ContinuousLinearMap UniformSpace UniformSpace.Completion

variable {𝕜 X E V : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedSpace ℝ V]

/-- The orthogonal projection onto the range of a real `C^n` family of real or complex operators
out of a finite-dimensional space is real `C^n` wherever the operator is injective. The inner
product space `V` need not be complete. -/
theorem ContDiffAt.starProjection_range {A : X → E →L[𝕜] V} {u₀ : X} {n : WithTop ℕ∞}
    (hA : ContDiffAt ℝ n A u₀) (hinj : Injective (A u₀)) :
    ContDiffAt ℝ n (fun u => (A u).range.starProjection) u₀ := by
  -- Precompose with a linear isomorphism from a Euclidean space, so that adjoints exist.
  let F := EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 E))
  let j : F ≃L[𝕜] E := .ofFinrankEq (by simp [F])
  have hj : ContDiffAt ℝ n (fun u ↦ A u ∘L (j : F →L[𝕜] E)) u₀ :=
    (((compL 𝕜 F E V).flip (j : F →L[𝕜] E)).restrictScalars ℝ).contDiff.contDiffAt.comp u₀ hA
  have hG := (isUnit_adjoint_comp_self_iff
    ((toComplL : V →L[𝕜] Completion V) ∘L A u₀ ∘L (j : F →L[𝕜] E))).2
    ((coe_injective V).comp (hinj.comp j.injective))
  refine ((contDiffAt_gramProjection toComplL hG).comp u₀
    (f := fun u ↦ A u ∘L (j : F →L[𝕜] E)) hj).congr_of_eventuallyEq ?_
  exact (eventuallyEq_starProjection_range j hinj).comp_tendsto hA.continuousAt

/-- The orthogonal projection onto the orthogonal complement of the range of a real `C^n` family
of real or complex operators out of a finite-dimensional space is real `C^n` wherever the
operator is injective. -/
theorem ContDiffAt.starProjection_orthogonal_range {A : X → E →L[𝕜] V} {u₀ : X} {n : WithTop ℕ∞}
    (hA : ContDiffAt ℝ n A u₀) (hinj : Injective (A u₀)) :
    ContDiffAt ℝ n (fun u => (A u).rangeᗮ.starProjection) u₀ := by
  refine (contDiffAt_const (c := (1 : V →L[𝕜] V))).sub (hA.starProjection_range hinj)
    |>.congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun u => Submodule.starProjection_orthogonal' _

end ContDiffAt

section ImagePlane

/-! ### The projection onto the image of a projected subspace

For a star projection `P` of `E` and an operator `L : E →L F`, the range of `L ∘L P` is the image
under `L` of the range of `P`. The Gram operator of `L ∘L P` is never invertible when `P ≠ 1`, so
the formula `B (B† B)⁻¹ B†` does not apply to it; it is corrected by adding the complementary
projection, giving `A = (L P)† (L P) + (1 - P)`, which commutes with `P` and is the identity on the
kernel of `P`; when `E` is finite-dimensional, `A` is invertible exactly when `L` is injective on
the range of `P`. -/

open ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

namespace ContinuousLinearMap

variable {P : E →L[𝕜] E}

/-- The adjoint of `L ∘L P` takes values in the range of `P`. -/
private theorem starProjection_comp_adjoint_comp (L : E →L[𝕜] F) (hP : IsStarProjection P) :
    P ∘L adjoint (L ∘L P) = adjoint (L ∘L P) := by
  simp [adjoint_comp, hP.isSelfAdjoint.adjoint_eq, ← comp_assoc,
    IsIdempotentElem.comp_self hP.isIdempotentElem]

/-- The corrected Gram operator `(L P)† (L P) + (1 - P)` of `L` and `P`. -/
private noncomputable def imageGram (L : E →L[𝕜] F) (P : E →L[𝕜] E) : E →L[𝕜] E :=
  adjoint (L ∘L P) ∘L (L ∘L P) + (1 - P)

/-- `P` followed by the corrected Gram operator is the Gram operator of `L P`. -/
private theorem starProjection_mul_imageGram (L : E →L[𝕜] F) (hP : IsStarProjection P) :
    P * imageGram L P = adjoint (L ∘L P) ∘L (L ∘L P) := by
  simp only [imageGram, mul_add, mul_sub, mul_one, hP.isIdempotentElem.eq, sub_self, add_zero,
    mul_def, ← comp_assoc, starProjection_comp_adjoint_comp L hP]

/-- `starProjection_range_comp_eq`, stated with the corrected Gram operator `imageGram L P`. -/
private theorem starProjection_range_comp_eq_imageGram (L : E →L[𝕜] F) (hP : IsStarProjection P)
    (hA : IsUnit (imageGram L P)) [(L ∘L P).range.HasOrthogonalProjection] :
    (L ∘L P).range.starProjection =
      (L ∘L P) ∘L Ring.inverse (imageGram L P) ∘L adjoint (L ∘L P) := by
  -- `Q† Q A⁻¹ = P A A⁻¹ = P`, and `P Q† = Q†`.
  have hQQ : adjoint (L ∘L P) ∘L (L ∘L P) ∘L Ring.inverse (imageGram L P) = P := by
    rw [← comp_assoc, ← starProjection_mul_imageGram L hP]
    simp [← mul_def, mul_assoc, Ring.mul_inverse_cancel _ hA]
  exact starProjection_range_eq_comp_comp_adjoint <| by
    simp only [← comp_assoc] at hQQ ⊢
    rw [hQQ, starProjection_comp_adjoint_comp L hP]

/-- The orthogonal projection onto the image `L (range P)` of the range of a star projection `P`
is `Q A⁻¹ Q†`, where `Q = L ∘L P` and `A = Q† Q + (1 - P)`, when `A` is invertible. -/
theorem starProjection_range_comp_eq (L : E →L[𝕜] F) (hP : IsStarProjection P)
    (hA : IsUnit (adjoint (L ∘L P) ∘L (L ∘L P) + (1 - P)))
    [(L ∘L P).range.HasOrthogonalProjection] :
    (L ∘L P).range.starProjection =
      (L ∘L P) ∘L Ring.inverse (adjoint (L ∘L P) ∘L (L ∘L P) + (1 - P)) ∘L adjoint (L ∘L P) := by
  rw [← imageGram] at hA ⊢
  exact starProjection_range_comp_eq_imageGram L hP hA

/-- `isUnit_adjoint_comp_add_one_sub_iff_injOn`, stated with the corrected Gram operator
`imageGram L P`. -/
private theorem isUnit_imageGram_iff [FiniteDimensional 𝕜 E] (L : E →L[𝕜] F)
    (hP : IsStarProjection P) : IsUnit (imageGram L P) ↔ Set.InjOn L (P.range : Set E) := by
  have hPA := starProjection_mul_imageGram L hP
  have hinj : Set.InjOn L (P.range : Set E) ↔
      Disjoint P.range (LinearMap.ker (L : E →ₗ[𝕜] F)) := by
    rw [LinearMap.disjoint_ker_iff_injOn, coe_coe]
  have hPP (y : E) : P (P y) = P y :=
    congr($(IsIdempotentElem.comp_self hP.isIdempotentElem) y)
  rw [hinj, isUnit_iff_isUnit_toLinearMap,
    LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot', Submodule.disjoint_def]
  simp only [coe_coe, LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro h _ ⟨y, rfl⟩ hy
    -- On the range of `P`, the corrected Gram operator is `Q† L`, which vanishes on `ker L`.
    exact h _ (by simp [imageGram, hPP, hy])
  · intro h x hx
    -- Applying `P` gives `Q† Q x = 0`, so `Q x = 0`; then `x - P x = 0`, so `x = P x`.
    have h1 : (adjoint (L ∘L P) ∘L (L ∘L P)) x = 0 := by rw [← hPA, mul_apply_eq_comp, hx, map_zero]
    have hQ : (L ∘L P) x = 0 := (ker_adjoint_comp_self (L ∘L P)).le h1
    have hxP : x = P x := by simpa [imageGram, sub_eq_zero] using congr($hx - $h1)
    refine h x ⟨x, hxP.symm⟩ ?_
    rw [hxP]
    exact hQ

/-- For a star projection `P` of a finite-dimensional space, the corrected Gram operator
`(L P)† (L P) + (1 - P)` is invertible exactly when `L` is injective on the range of `P`. -/
theorem isUnit_adjoint_comp_add_one_sub_iff_injOn [FiniteDimensional 𝕜 E] (L : E →L[𝕜] F)
    (hP : IsStarProjection P) :
    IsUnit (adjoint (L ∘L P) ∘L (L ∘L P) + (1 - P)) ↔ Set.InjOn L (P.range : Set E) := by
  rw [← imageGram]
  exact isUnit_imageGram_iff L hP

omit [CompleteSpace E] [CompleteSpace F] in
private theorem continuous_comp_fst_snd :
    Continuous fun x : (E →L[𝕜] F) × (E →L[𝕜] E) ↦ x.1 ∘L x.2 :=
  continuous_fst.clm_comp continuous_snd

omit [CompleteSpace F] in
private theorem continuous_fst_val_snd :
    Continuous fun x : (E →L[𝕜] F) × {P : E →L[𝕜] E // IsStarProjection P} ↦
      (x.1, (x.2 : E →L[𝕜] E)) :=
  continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd)

private theorem continuous_imageGram :
    Continuous fun x : (E →L[𝕜] F) × {P : E →L[𝕜] E // IsStarProjection P} ↦
      imageGram x.1 x.2 := by
  have h : Continuous fun x : (E →L[𝕜] F) × (E →L[𝕜] E) ↦ imageGram x.1 x.2 := by
    unfold imageGram
    exact ((adjoint.continuous.comp continuous_comp_fst_snd).clm_comp continuous_comp_fst_snd).add
      (continuous_const.sub continuous_snd)
  exact h.comp continuous_fst_val_snd

/-- For finite-dimensional `E`, the pairs `(L, P)` of an operator and a star projection such that
`L` is injective on the range of `P` form an open set. -/
theorem isOpen_setOf_injOn_range [FiniteDimensional 𝕜 E] :
    IsOpen {x : (E →L[𝕜] F) × {P : E →L[𝕜] E // IsStarProjection P} |
      Set.InjOn x.1 ((x.2 : E →L[𝕜] E).range : Set E)} := by
  convert Units.isOpen.preimage (continuous_imageGram (𝕜 := 𝕜) (E := E) (F := F)) using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  exact (isUnit_imageGram_iff x.1 x.2.property).symm

/-- For finite-dimensional `E`, the orthogonal projection onto the image `L (range P)` depends
continuously on the operator `L` and the star projection `P`, on the pairs where `L` is injective
on the range of `P`. -/
theorem continuousOn_starProjection_range_comp [FiniteDimensional 𝕜 E] :
    ContinuousOn (fun x : (E →L[𝕜] F) × {P : E →L[𝕜] E // IsStarProjection P} ↦
        (x.1 ∘L (x.2 : E →L[𝕜] E)).range.starProjection)
      {x | Set.InjOn x.1 ((x.2 : E →L[𝕜] E).range : Set E)} := by
  have hu {x : (E →L[𝕜] F) × {P : E →L[𝕜] E // IsStarProjection P}}
      (hx : Set.InjOn x.1 ((x.2 : E →L[𝕜] E).range : Set E)) : IsUnit (imageGram x.1 x.2) :=
    (isUnit_imageGram_iff x.1 x.2.property).2 hx
  have hQ : Continuous fun x : (E →L[𝕜] F) × {P : E →L[𝕜] E // IsStarProjection P} ↦
      x.1 ∘L (x.2 : E →L[𝕜] E) :=
    continuous_comp_fst_snd.comp continuous_fst_val_snd
  refine ContinuousOn.congr (f := fun x ↦ (x.1 ∘L (x.2 : E →L[𝕜] E)) ∘L
      Ring.inverse (imageGram x.1 x.2) ∘L adjoint (x.1 ∘L (x.2 : E →L[𝕜] E)))
    (fun x hx ↦ ?_) fun x hx ↦ starProjection_range_comp_eq_imageGram x.1 x.2.property (hu hx)
  -- The formula is continuous wherever the corrected Gram operator is invertible.
  have hi := NormedRing.inverse_continuousAt (hu hx).unit
  rw [(hu hx).unit_spec] at hi
  exact (hQ.continuousAt.clm_comp ((hi.comp_of_eq continuous_imageGram.continuousAt rfl).clm_comp
    (adjoint.continuous.comp hQ).continuousAt)).continuousWithinAt

/-- For an isometry `B` and a star projection `P`, the operator `B P B†` is the orthogonal
projection onto the image under `B` of the range of `P`. -/
theorem comp_comp_adjoint_eq_starProjection_range_comp {B : E →L[𝕜] F} (hB : Isometry B)
    (hP : IsStarProjection P) [(B ∘L P).range.HasOrthogonalProjection] :
    B ∘L P ∘L adjoint B = (B ∘L P).range.starProjection := by
  have hBB (X : E →L[𝕜] E) : (X ∘L adjoint B) ∘L B = X := by
    rw [comp_assoc, (isometry_iff_adjoint_comp_self B).1 hB, one_def, comp_id]
  -- `Q = B P` is a partial isometry, since `Q Q† Q = B P (B† B) P = B P`, and `Q Q† = B P B†`.
  have hQ : (B ∘L P).IsPartialIsometry := by
    simp [isPartialIsometry_iff, adjoint_comp, hP.isSelfAdjoint.adjoint_eq, ← comp_assoc, hBB,
      IsIdempotentElem.comp_comp_self hP.isIdempotentElem]
  have h := hQ.comp_adjoint_eq_starProjection
  simp only [hQ.isClosed_range.submodule_topologicalClosure_eq] at h
  simpa [adjoint_comp, hP.isSelfAdjoint.adjoint_eq, ← comp_assoc,
    IsIdempotentElem.comp_comp_self hP.isIdempotentElem] using h

end ContinuousLinearMap

end ImagePlane
