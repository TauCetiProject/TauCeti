/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Complex.LinearPart
public import TauCeti.Topology.VectorBundle.Complex.Clutching
public import TauCeti.Topology.VectorBundle.Complex.Structure

/-!
# Comparing two complex structures on a real vector bundle

Let `J` and `K` be continuous complex structures on a real vector bundle `V`. The complex-linear
part of the identity of `V b`, from the complex structure `J b` to `K b`, is

`T b = (1 - K b ∘ J b) / 2`

(`TauCeti.Bundle.ContinuousComplexStructure.intertwiner`). It intertwines the two structures,
`K b ∘ T b = T b ∘ J b`, and depends continuously on `b`. So wherever it is invertible it is a
complex-linear isomorphism `J.Fiber b ≃ K.Fiber b`
(`TauCeti.Bundle.ContinuousComplexStructure.intertwinerEquiv`), and when it is invertible
everywhere these isomorphisms form an isomorphism of complex vector bundles. Isomorphic complex
vector bundles have the same clutching numbers
(`TauCeti.clutchingNumberHom_eq_of_continuousLinearEquiv`), so `J.Fiber` and `K.Fiber` then have
the same clutching number homomorphism on `π₂`
(`TauCeti.Bundle.ContinuousComplexStructure.clutchingNumberHom_eq_of_isUnit_intertwiner`), whatever
model fibres are used for them.

The intertwiner is invertible when `J b` and `K b` are tamed by a common symplectic form, since
then `1 - K b ∘ J b` is injective; this is how the first Chern number of a symplectic manifold
is seen not to depend on the choice of tame almost complex structure. With `J = K` the intertwiner
is the identity, which shows that the clutching number of a single complex structure does not
depend on the model fibre (`TauCeti.Bundle.ContinuousComplexStructure.clutchingNumberHom_model_eq`).

## Main definitions

* `TauCeti.Bundle.ContinuousComplexStructure.intertwiner J K b`: the operator
  `(1 - K b ∘ J b) / 2` on `V b`.
* `TauCeti.Bundle.ContinuousComplexStructure.intertwinerEquiv J K b h`: the intertwiner, when it
  is invertible, as a complex-linear isomorphism `J.Fiber b ≃ K.Fiber b`.

## Main results

* `TauCeti.Bundle.ContinuousComplexStructure.apply_intertwiner`: `K b (T b v) = T b (J b v)`.
* `TauCeti.Bundle.ContinuousComplexStructure.continuous_intertwiner`: the intertwiner is
  continuous on the total space of `V`.
* `TauCeti.Bundle.ContinuousComplexStructure.clutchingNumberHom_eq_of_isUnit_intertwiner`: if the
  intertwiner is invertible everywhere, `J` and `K` have the same clutching number homomorphism.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford (2017),
  Section 2.6 (the space of tame complex structures and the first Chern class).
-/

public section

noncomputable section

open Bundle FiberBundle Set Topology Module

namespace TauCeti.Bundle.ContinuousComplexStructure

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)]
  [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousSMul ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  (J K : ContinuousComplexStructure F V)

/-- The **intertwiner** of two complex structures `J` and `K` at `b`: the complex-linear part
`(1 - K b ∘ J b) / 2` of the identity of `V b`, from the complex structure `J b` to `K b`. -/
def intertwiner (b : B) : V b →L[ℝ] V b :=
  (2⁻¹ : ℝ) • (1 - K b * J b)

theorem intertwiner_apply (b : B) (v : V b) :
    J.intertwiner K b v = (2⁻¹ : ℝ) • (v - K b (J b v)) :=
  (rfl)

/-- As a linear map, the intertwiner is the complex-linear part of the identity of `V b`, from
the complex structure `J b` to `K b`. -/
theorem coe_intertwiner (b : B) :
    (J.intertwiner K b : V b →ₗ[ℝ] V b) =
      TauCeti.complexLinearPart (J b : V b →ₗ[ℝ] V b) (K b) LinearMap.id :=
  LinearMap.ext fun v ↦ by simp [intertwiner_apply]

/-- The intertwiner of a complex structure with itself is the identity. -/
@[simp]
theorem intertwiner_self (b : B) : J.intertwiner J b = 1 := by
  ext v
  simp only [intertwiner_apply, apply_apply, sub_neg_eq_add, one_apply_eq_self]
  module

/-- The intertwiner is invertible exactly when `1 - K b ∘ J b` is. -/
theorem isUnit_intertwiner_iff (b : B) :
    IsUnit (J.intertwiner K b) ↔ IsUnit (1 - K b * J b) :=
  isUnit_smul_iff (Units.mk0 (2⁻¹ : ℝ) (by norm_num)) (1 - K b * J b)

/-- **The intertwiner intertwines.** `K b ∘ T b = T b ∘ J b`. -/
theorem apply_intertwiner (b : B) (v : V b) :
    K b (J.intertwiner K b v) = J.intertwiner K b (J b v) := by
  simp only [intertwiner_apply, map_smul, map_sub, map_neg, apply_apply, sub_neg_eq_add]
  module

/-- The intertwiner, at a point where it is invertible, as a complex-linear isomorphism from the
fibre of `J.Fiber` to that of `K.Fiber`. -/
def intertwinerEquiv (b : B) (h : IsUnit (J.intertwiner K b)) : J.Fiber b ≃L[ℂ] K.Fiber b :=
  -- The real isomorphism `J.Fiber b ≃ V b ≃ V b ≃ K.Fiber b`, which is complex linear.
  let R : J.Fiber b ≃L[ℝ] K.Fiber b := (J.fiberEquiv b).trans
    ((ContinuousLinearEquiv.unitsEquiv ℝ (V b) h.unit).trans (K.fiberEquiv b).symm)
  have hR (v : J.Fiber b) : K.fiberEquiv b (R v) = J.intertwiner K b (J.fiberEquiv b v) := by
    simp [R, ContinuousLinearEquiv.unitsEquiv_apply]
  { toFun := R
    invFun := R.symm
    map_add' := R.map_add
    map_smul' z v := (K.fiberEquiv b).injective <| by
      simp only [RingHom.id_apply, hR, fiberEquiv_smul, map_add, map_smul, apply_intertwiner]
    left_inv := R.symm_apply_apply
    right_inv := R.apply_symm_apply
    continuous_toFun := R.continuous
    continuous_invFun := R.symm.continuous }

@[simp]
theorem fiberEquiv_intertwinerEquiv (b : B) (h : IsUnit (J.intertwiner K b)) (v : J.Fiber b) :
    K.fiberEquiv b (J.intertwinerEquiv K b h v) = J.intertwiner K b (J.fiberEquiv b v) := by
  simp [intertwinerEquiv, ContinuousLinearEquiv.unitsEquiv_apply]

/-- The intertwiner is continuous on the total space of `V`. -/
theorem continuous_intertwiner :
    Continuous fun p : TotalSpace F V ↦
      TotalSpace.mk' F p.proj (J.intertwiner K p.proj p.snd) := by
  refine continuous_iff_continuousAt.mpr fun q₀ ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj F V).continuousAt, ?_⟩
  -- In the trivialization `e` at `q₀.proj`, the intertwiner reads `w ↦ (w - K' (J' w)) / 2`, where
  -- `J'` and `K'` are `J` and `K` in the coordinates of `e`.
  have hU : (trivializationAt F V q₀.proj).baseSet ∈ 𝓝 q₀.proj :=
    (trivializationAt F V q₀.proj).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F V q₀.proj)
  have hproj := (FiberBundle.continuous_proj F V).continuousAt (x := q₀)
  have hJ := ((J.continuousOn_coord q₀.proj).continuousAt hU).comp hproj
  have hK := ((K.continuousOn_coord q₀.proj).continuousAt hU).comp hproj
  have he : ContinuousAt (fun q ↦ (trivializationAt F V q₀.proj q).snd) q₀ :=
    ((trivializationAt F V q₀.proj).continuousAt FiberBundle.mem_trivializationAt_proj_source).snd
  refine ((he.sub (hK.clm_apply (hJ.clm_apply he))).const_smul (2⁻¹ : ℝ)).congr_of_eventuallyEq ?_
  filter_upwards [hproj.preimage_mem_nhds hU] with q hq
  have hq' : (trivializationAt F V q₀.proj q).snd =
      (trivializationAt F V q₀.proj).continuousLinearMapAt ℝ q.proj q.snd :=
    ((trivializationAt F V q₀.proj).continuousLinearMapAt_apply_of_mem (R := ℝ) hq q.snd).symm
  simp only [Pi.smul_apply, Pi.sub_apply, Function.comp_apply, hq',
    ← (trivializationAt F V q₀.proj).continuousLinearMapAt_apply_of_mem (R := ℝ) hq,
    intertwiner_apply, map_smul, map_sub, J.coord_apply hq, K.coord_apply hq]

/-! ### Clutching numbers -/

variable (G G' : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [NormedAddCommGroup G'] [NormedSpace ℂ G'] [FiniteDimensional ℂ G'] [FiniteDimensional ℝ F]
  [Fact (finrank ℝ F = 2 * finrank ℂ G)] [Fact (finrank ℝ F = 2 * finrank ℂ G')]

/-- **Clutching numbers of two complex structures.** If the intertwiner of `J` and `K` is
invertible at every point, then the complex vector bundles `J.Fiber` and `K.Fiber` have the same
clutching number homomorphism `π₂(B, x) → ℤ`, for any choice of model fibres `G` and `G'`. -/
theorem clutchingNumberHom_eq_of_isUnit_intertwiner (h : ∀ b, IsUnit (J.intertwiner K b))
    (x : B) : clutchingNumberHom G' K.Fiber x = clutchingNumberHom G J.Fiber x := by
  refine clutchingNumberHom_eq_of_continuousLinearEquiv (F := G) (F' := G') (E := J.Fiber)
    (E' := K.Fiber) (fun b ↦ J.intertwinerEquiv K b (h b)) ?_ x
  refine ((K.totalSpaceHomeomorph G').symm.continuous.comp
    ((J.continuous_intertwiner K).comp (J.totalSpaceHomeomorph G).continuous)).congr fun v ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, J.totalSpaceHomeomorph_apply G v,
    totalSpaceHomeomorph_symm_apply]
  exact congrArg (TotalSpace.mk' G' v.proj)
    ((ContinuousLinearEquiv.symm_apply_eq _).2 (J.fiberEquiv_intertwinerEquiv K _ _ _).symm)

/-- The clutching number homomorphism of a complex structure does not depend on the model fibre.
-/
theorem clutchingNumberHom_model_eq (x : B) :
    clutchingNumberHom G' J.Fiber x = clutchingNumberHom G J.Fiber x :=
  J.clutchingNumberHom_eq_of_isUnit_intertwiner J G G' (fun b ↦ by simp) x

end TauCeti.Bundle.ContinuousComplexStructure
