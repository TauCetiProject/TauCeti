/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Complex.Clutching
public import TauCeti.Topology.VectorBundle.Complex.Structure
import TauCeti.Topology.VectorBundle.Hom
import TauCeti.Topology.VectorBundle.Section
import TauCeti.Topology.VectorBundle.Smul

/-!
# Changing the complex structure of a real vector bundle

Let `V` be a real vector bundle over `B` with finite-dimensional model fibre `F`, and let `J` and
`K` be two continuous complex structures on `V`. At each point `b`, the complex-linear part of the
identity of `V b` from `J b` to `K b` is

`A b v = (v - K b (J b v)) / 2`,

and it intertwines the two structures: `A b (J b v) = K b (A b v)`. Suppose that no nonzero vector
satisfies `K b (J b v) = v`, which is exactly the injectivity of every `A b`. Then `A` is an
isomorphism of complex vector bundles from `J.Fiber` to `K.Fiber`
(`TauCeti.Bundle.ContinuousComplexStructure.complexLinearPartEquiv`), continuous on total spaces
(`TauCeti.Bundle.ContinuousComplexStructure.continuous_complexLinearPartEquiv`). So `J.Fiber` and
`K.Fiber` have the same clutching number on every sphere
(`TauCeti.Bundle.ContinuousComplexStructure.clutchingNumber_fiber_eq`): the first Chern number of
`(V, J)` on spheres does not change when `J` is replaced by such a `K`.

The hypothesis holds when `J` and `K` are tamed by a common family of bilinear forms `ω_b`, that is,
`ω_b (v, J_b v) > 0` and `ω_b (v, K_b v) > 0` for `v ≠ 0`. Indeed `K (J v) = v` gives
`K v = -J v`, and then `ω_b (v, K_b v) = -ω_b (v, J_b v)`, so `v = 0`. This is how the first Chern
number of a symplectic manifold is independent of the tame almost complex structure used to define
it. With `K = J` the hypothesis always holds, and the result says that the clutching numbers of
`J.Fiber` do not depend on its complex model fibre.

## Main definitions

* `TauCeti.Bundle.ContinuousComplexStructure.complexLinearPartEquiv`: the complex-linear part of
  the identity, as a complex-linear isomorphism `J.Fiber b ≃ K.Fiber b`.

## Main results

* `TauCeti.Bundle.ContinuousComplexStructure.continuous_complexLinearPartEquiv`: it is continuous
  on total spaces, for any complex model fibres of `J.Fiber` and `K.Fiber`.
* `TauCeti.Bundle.ContinuousComplexStructure.clutchingNumber_fiber_eq`,
  `TauCeti.Bundle.ContinuousComplexStructure.clutchingNumberHom_fiber_eq`: `J.Fiber` and `K.Fiber`
  have the same clutching numbers.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford (2017),
  Section 2.6 (the space of complex structures tamed by a symplectic form, and the Chern classes of
  a symplectic vector bundle).
-/

public section

noncomputable section

open Bundle Module
open scoped Topology.Homotopy

namespace TauCeti.Bundle.ContinuousComplexStructure

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)]
  [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousSMul ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  (J K : ContinuousComplexStructure F V)

/-- The complex-linear part `v ↦ (v - K b (J b v)) / 2` of the identity of `V b`, from the complex
structure `J b` to `K b`; as a linear map it is
`TauCeti.complexLinearPart (J b) (K b) LinearMap.id`. -/
private def complexLinearPartTo (b : B) : V b →L[ℝ] V b :=
  (2⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ (V b) - (K b).comp (J b))

private theorem complexLinearPartTo_apply (b : B) (v : V b) :
    J.complexLinearPartTo K b v = (2⁻¹ : ℝ) • (v - K b (J b v)) :=
  (rfl)

/-- The complex-linear part intertwines `J` and `K`. -/
private theorem complexLinearPartTo_apply_apply (b : B) (v : V b) :
    J.complexLinearPartTo K b (J b v) = K b (J.complexLinearPartTo K b v) := by
  simp only [complexLinearPartTo_apply, apply_apply, map_smul, map_sub, map_neg]
  module

variable [FiniteDimensional ℝ F]

/-- The complex-linear part is continuous on total spaces. -/
private theorem continuous_complexLinearPartTo :
    Continuous fun q : TotalSpace F V ↦
      TotalSpace.mk' F q.proj (J.complexLinearPartTo K q.proj q.snd) := by
  have hJ : Continuous fun q : TotalSpace F V ↦ TotalSpace.mk' F q.proj (J q.proj q.snd) :=
    (continuous_hom_bundle_iff (fun b ↦ J b)).1 J.continuous
  have hKJ : Continuous fun q : TotalSpace F V ↦
      TotalSpace.mk' F q.proj (K q.proj (J q.proj q.snd)) :=
    ((continuous_hom_bundle_iff (fun b ↦ K b)).1 K.continuous).comp hJ
  have h₁ : Continuous fun q : TotalSpace F V ↦ TotalSpace.mk' F q.proj ((2⁻¹ : ℝ) • q.snd) :=
    continuous_const.smul_totalSpace continuous_id
  have h₂ : Continuous fun q : TotalSpace F V ↦
      TotalSpace.mk' F q.proj ((-2⁻¹ : ℝ) • K q.proj (J q.proj q.snd)) :=
    continuous_const.smul_totalSpace hKJ
  refine (h₁.add_totalSpace ℝ h₂).congr fun q ↦ ?_
  rw [complexLinearPartTo_apply]
  congr 1
  module

variable {J K} (h : ∀ b (v : V b), K b (J b v) = v → v = 0)
include h

omit [FiniteDimensional ℝ F] in
private theorem injective_complexLinearPartTo (b : B) :
    Function.Injective (J.complexLinearPartTo K b) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦ h b v ?_
  rw [complexLinearPartTo_apply, smul_eq_zero, sub_eq_zero] at hv
  exact (hv.resolve_left (by norm_num)).symm

/-- The complex-linear part, as a real linear automorphism of `V b`. Its inverse is continuous
because `V b` is finite-dimensional: it is read in the trivialization of `V` at `b`. -/
private def complexLinearPartRealEquiv (b : B) : V b ≃L[ℝ] V b :=
  let τ := (trivializationAt F V b).continuousLinearEquivAt ℝ b
    (mem_baseSet_trivializationAt F V b)
  τ.trans ((LinearEquiv.ofInjectiveEndo
    ((τ : V b →L[ℝ] F).comp ((J.complexLinearPartTo K b).comp (τ.symm : F →L[ℝ] V b)) : F →ₗ[ℝ] F)
    (τ.injective.comp ((injective_complexLinearPartTo h b).comp
      τ.symm.injective))).toContinuousLinearEquiv.trans τ.symm)

private theorem complexLinearPartRealEquiv_apply (b : B) (v : V b) :
    complexLinearPartRealEquiv h b v = J.complexLinearPartTo K b v := by
  simp [complexLinearPartRealEquiv,
    Trivialization.symm_apply_apply_mk _ (mem_baseSet_trivializationAt F V b)]

/-- **The complex-linear part of the identity, as an isomorphism of complex vector spaces** from
`V b` with the complex structure `J b` to `V b` with the complex structure `K b`: it sends `v` to
`(v - K b (J b v)) / 2`
(`TauCeti.Bundle.ContinuousComplexStructure.fiberEquiv_complexLinearPartEquiv`). -/
def complexLinearPartEquiv (b : B) : J.Fiber b ≃L[ℂ] K.Fiber b where
  toFun v := (K.fiberEquiv b).symm (J.complexLinearPartTo K b (J.fiberEquiv b v))
  invFun v := (J.fiberEquiv b).symm ((complexLinearPartRealEquiv h b).symm (K.fiberEquiv b v))
  map_add' v w := by simp
  map_smul' c v := by
    apply (K.fiberEquiv b).injective
    simp only [ContinuousLinearEquiv.apply_symm_apply, RingHom.id_apply, fiberEquiv_smul, map_add,
      map_smul, complexLinearPartTo_apply_apply]
  left_inv v := by
    simp [← complexLinearPartRealEquiv_apply h]
  right_inv v := by
    simp [← complexLinearPartRealEquiv_apply h]
  continuous_toFun := (K.fiberEquiv b).symm.continuous.comp
    ((J.complexLinearPartTo K b).continuous.comp (J.fiberEquiv b).continuous)
  continuous_invFun := (J.fiberEquiv b).symm.continuous.comp
    ((complexLinearPartRealEquiv h b).symm.continuous.comp (K.fiberEquiv b).continuous)

private theorem complexLinearPartEquiv_apply (b : B) (v : J.Fiber b) :
    complexLinearPartEquiv h b v =
      (K.fiberEquiv b).symm (J.complexLinearPartTo K b (J.fiberEquiv b v)) :=
  (rfl)

/-- `TauCeti.Bundle.ContinuousComplexStructure.complexLinearPartEquiv` sends `v` to
`(v - K b (J b v)) / 2`. -/
@[simp]
theorem fiberEquiv_complexLinearPartEquiv (b : B) (v : J.Fiber b) :
    K.fiberEquiv b (complexLinearPartEquiv h b v) =
      (2⁻¹ : ℝ) • (J.fiberEquiv b v - K b (J b (J.fiberEquiv b v))) := by
  simp [complexLinearPartEquiv, complexLinearPartTo_apply]

variable (G G' : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ F = 2 * finrank ℂ G)] [NormedAddCommGroup G'] [NormedSpace ℂ G']
  [FiniteDimensional ℂ G'] [Fact (finrank ℝ F = 2 * finrank ℂ G')]

/-- The complex-linear part of the identity is continuous on total spaces, for any complex model
fibres `G` of `J.Fiber` and `G'` of `K.Fiber`. -/
theorem continuous_complexLinearPartEquiv :
    Continuous fun p : TotalSpace G J.Fiber ↦
      TotalSpace.mk' G' p.proj (complexLinearPartEquiv h p.proj p.snd) := by
  refine ((K.totalSpaceHomeomorph G').symm.continuous.comp
    ((J.continuous_complexLinearPartTo K).comp (J.totalSpaceHomeomorph G).continuous)).congr
      fun ⟨b, v⟩ ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, totalSpaceHomeomorph_apply,
    totalSpaceHomeomorph_symm_apply, complexLinearPartEquiv_apply]

/-- **Changing the complex structure does not change the clutching number.** If no nonzero
vector satisfies `K b (J b v) = v`, then the complex vector bundles `J.Fiber` and `K.Fiber` have
the same clutching number on every sphere, for any complex model fibres `G` and `G'`. -/
theorem clutchingNumber_fiber_eq {x : B} (p : Ω^ (Fin 2) B x) :
    clutchingNumber G' K.Fiber p = clutchingNumber G J.Fiber p :=
  clutchingNumber_eq_of_continuousLinearEquiv (complexLinearPartEquiv h)
    (continuous_complexLinearPartEquiv h G G') p

/-- **Changing the complex structure does not change the clutching number homomorphism.** If no
nonzero vector satisfies `K b (J b v) = v`, then `J.Fiber` and `K.Fiber` have the same clutching
number homomorphism `π₂(B, x) → ℤ`, for any complex model fibres `G` and `G'`. -/
theorem clutchingNumberHom_fiber_eq (x : B) :
    clutchingNumberHom G' K.Fiber x = clutchingNumberHom G J.Fiber x :=
  clutchingNumberHom_eq_of_continuousLinearEquiv (complexLinearPartEquiv h)
    (continuous_complexLinearPartEquiv h G G') x

end TauCeti.Bundle.ContinuousComplexStructure
