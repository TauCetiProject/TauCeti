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

/-!
# The orthogonal projection onto the range of an operator

If `B : F →L[𝕜] V` is an operator between inner product spaces whose Gram operator `B† B` is
invertible, the orthogonal projection of `V` onto the range of `B` is `B (B† B)⁻¹ B†`. When `F` is
finite-dimensional, `B† B` is invertible exactly when `B` is injective.

Over `ℝ` or `ℂ` this formula gives continuity for arbitrary topological parameter spaces
(`ContinuousAt.starProjection_range`), with no inner product required on the source model.
Over `ℝ` it also shows that the projection depends smoothly on the operator: for a
`C^n` family of injective operators `A u : E →L[ℝ] V` out of a finite-dimensional real normed
space `E`, the orthogonal projections of `V` onto the ranges of `A u` form a `C^n` family. Applied
to the derivative of an immersion into a Euclidean space, this says that the tangent spaces, and
hence the normal spaces, of an immersed submanifold vary smoothly. Neither result needs `V` to be
complete: the formula is applied after embedding `V` into its completion.

## Main results

* `ContinuousLinearMap.isUnit_adjoint_comp_self_iff`: the Gram operator of an operator out of a
  finite-dimensional space is invertible exactly when the operator is injective.
* `ContinuousLinearMap.starProjection_range_eq`: the formula `B (B† B)⁻¹ B†` for the orthogonal
  projection onto the range of `B`.
* `ContinuousLinearMap.comp_adjoint_eq_starProjection_range`: for an isometry `B` it reduces to
  `B B†`.
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
-/

public section

open Function Filter Topology

namespace ContinuousLinearMap

variable {𝕜 F V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

section Adjoint

variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] [CompleteSpace V]

/-- The Gram operator `B† B` of an operator out of a finite-dimensional space is invertible
exactly when `B` is injective. -/
theorem isUnit_adjoint_comp_self_iff [FiniteDimensional 𝕜 F] (B : F →L[𝕜] V) :
    IsUnit (adjoint B ∘L B) ↔ Injective B := by
  simp only [isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
    ker_adjoint_comp_self, LinearMap.ker_eq_bot, coe_coe]

/-- The orthogonal projection onto the range of `B` is `B (B† B)⁻¹ B†`, when the Gram operator
`B† B` is invertible. -/
theorem starProjection_range_eq {B : F →L[𝕜] V} [B.range.HasOrthogonalProjection]
    (hB : IsUnit (adjoint B ∘L B)) :
    B.range.starProjection = B ∘L Ring.inverse (adjoint B ∘L B) ∘L adjoint B := by
  ext v
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (LinearMap.mem_range_self _ _) ?_
  rintro _ ⟨x, rfl⟩
  -- Move `B` across the inner product: `B† (v - B (B† B)⁻¹ B† v) = 0`.
  rw [coe_coe, ← adjoint_inner_left, map_sub]
  simp [← comp_apply (adjoint B), ← mul_apply_eq_comp, Ring.mul_inverse_cancel _ hB]

/-- For an isometry `B`, the operator `B B†` is the orthogonal projection onto the range of `B`. -/
theorem comp_adjoint_eq_starProjection_range {B : F →L[𝕜] V} (hB : Isometry B)
    [B.range.HasOrthogonalProjection] : B ∘L adjoint B = B.range.starProjection := by
  have h := (isometry_iff_adjoint_comp_self B).1 hB
  rw [starProjection_range_eq (h ▸ isUnit_one), h, Ring.inverse_one, one_def, id_comp]

end Adjoint

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
onto the range of `T` is `T j (B† B)⁻¹ B† ι`, where `ι = toComplL` embeds `V` into its completion
and `B = ι T j`. Here `j : F ≃L E` identifies `E` with a complete inner product space `F`, so that
the adjoint of `B` exists although `V` need not be complete. -/
private theorem eventuallyEq_starProjection_range (j : F ≃L[𝕜] E) {T₀ : E →L[𝕜] V}
    (hT₀ : Injective T₀) :
    (fun T : E →L[𝕜] V ↦ T.range.starProjection) =ᶠ[𝓝 T₀] fun T ↦
      T ∘L (j : F →L[𝕜] E) ∘L
        Ring.inverse (adjoint (toComplL ∘L T ∘L (j : F →L[𝕜] E)) ∘L
          toComplL ∘L T ∘L (j : F →L[𝕜] E)) ∘L
        adjoint (toComplL ∘L T ∘L (j : F →L[𝕜] E)) ∘L toComplL := by
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
  simpa [B] using hcomm.symm

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
  have hB : ContinuousAt (fun y ↦ toComplL ∘L A y ∘L (j : F →L[𝕜] E)) x :=
    continuousAt_const.clm_comp hj
  have hadj : ContinuousAt (fun y ↦ adjoint (toComplL ∘L A y ∘L (j : F →L[𝕜] E))) x :=
    adjoint.continuous.continuousAt.comp hB
  have hG := (isUnit_adjoint_comp_self_iff
    ((toComplL : V →L[𝕜] Completion V) ∘L A x ∘L (j : F →L[𝕜] E))).2
    ((coe_injective V).comp (hinj.comp j.injective))
  have hinv := (NormedRing.inverse_continuousAt hG.unit).comp_of_eq (hadj.clm_comp hB)
    hG.unit_spec.symm
  refine (hj.clm_comp (hinv.clm_comp (hadj.clm_comp
    (continuousAt_const (y := (toComplL : V →L[𝕜] Completion V)))))).congr_of_eventuallyEq ?_
  exact (eventuallyEq_starProjection_range j hinj).comp_tendsto hA

end ContinuousAt

section ContDiffAt

open ContinuousLinearMap UniformSpace UniformSpace.Completion

variable {X E V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The orthogonal projection onto the range of a `C^n` family of operators out of a
finite-dimensional space is `C^n` at every point where the operator is injective. The inner
product space `V` need not be complete. -/
theorem ContDiffAt.starProjection_range {A : X → E →L[ℝ] V} {u₀ : X} {n : WithTop ℕ∞}
    (hA : ContDiffAt ℝ n A u₀) (hinj : Injective (A u₀)) :
    ContDiffAt ℝ n (fun u => (A u).range.starProjection) u₀ := by
  -- Precompose with a linear isomorphism from a Euclidean space, so that adjoints exist.
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let j : F ≃L[ℝ] E := .ofFinrankEq (by simp [F])
  have hj : ContDiffAt ℝ n (fun u ↦ A u ∘L (j : F →L[ℝ] E)) u₀ := hA.clm_comp contDiffAt_const
  have hB : ContDiffAt ℝ n (fun u ↦ toComplL ∘L A u ∘L (j : F →L[ℝ] E)) u₀ :=
    contDiffAt_const.clm_comp hj
  -- Over `ℝ` the adjoint is linear, hence smooth.
  have hadj : ContDiffAt ℝ n (fun u ↦ adjoint (toComplL ∘L A u ∘L (j : F →L[ℝ] E))) u₀ :=
    (adjoint : (F →L[ℝ] Completion V) ≃ₗᵢ[ℝ] (Completion V →L[ℝ] F)).contDiff
      |>.contDiffAt.comp u₀ hB
  have hG := (isUnit_adjoint_comp_self_iff
    ((toComplL : V →L[ℝ] Completion V) ∘L A u₀ ∘L (j : F →L[ℝ] E))).2
    ((coe_injective V).comp (hinj.comp j.injective))
  have hinv := contDiffAt_ringInverse ℝ (n := n) hG.unit
  rw [hG.unit_spec] at hinv
  refine (hj.clm_comp ((hinv.comp u₀ (hadj.clm_comp hB)).clm_comp (hadj.clm_comp
    (contDiffAt_const (c := (toComplL : V →L[ℝ] Completion V)))))).congr_of_eventuallyEq ?_
  exact (eventuallyEq_starProjection_range j hinj).comp_tendsto hA.continuousAt

/-- The orthogonal projection onto the orthogonal complement of the range of a `C^n` family of
operators out of a finite-dimensional space is `C^n` at every point where the operator is
injective. -/
theorem ContDiffAt.starProjection_orthogonal_range {A : X → E →L[ℝ] V} {u₀ : X} {n : WithTop ℕ∞}
    (hA : ContDiffAt ℝ n A u₀) (hinj : Injective (A u₀)) :
    ContDiffAt ℝ n (fun u => (A u).rangeᗮ.starProjection) u₀ := by
  refine (contDiffAt_const (c := (1 : V →L[ℝ] V))).sub (hA.starProjection_range hinj)
    |>.congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun u => Submodule.starProjection_orthogonal' _

end ContDiffAt
