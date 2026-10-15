/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.Basic
public import TauCeti.GroupTheory.Perm.WreathProduct.ChangeTransversal

/-!
# Tensor induction is independent of the transversal

The tensor-induced representations attached to two left transversals of a subgroup are
isomorphic. The isomorphism acts on the tensor power by the base-group element comparing their
monomial embeddings. On a pure tensor, it applies the difference of the two chosen
representatives at each coset to the corresponding factor.

The construction is algebraic and needs neither finite index nor topology. Its factorwise
formula supplies the comparison of continuous tensor-induced actions for open subgroups.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), §§2–3.
-/

public section

namespace Subgroup

open TauCeti
open scoped TensorProduct

universe u v w

variable {R : Type u} [CommSemiring R] {G : Type v} [Group G]
  (U : Subgroup G) (s t : U.LeftTransversal)
  {M : Type w} [AddCommMonoid M] [Module R M]
  (ρ : Representation R U M)

/-- The tensor-power linear equivalence induced by changing the transversal. It acts by the
comparison element in the base group of the wreath product. -/
noncomputable def tensorInducedChangeTransversalLinearEquiv :
    (⨂[R] _ : G ⧸ U, M) ≃ₗ[R] (⨂[R] _ : G ⧸ U, M) := by
  let W := ρ.wreathTensor (G ⧸ U)
  let c := monomialChangeTransversal U s t
  have hbij : Function.Bijective (W c) := by
    constructor
    · intro x y h
      have h' := congrArg (W c⁻¹) h
      simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply] using h'
    · intro y
      refine ⟨W c⁻¹ y, ?_⟩
      simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
  exact LinearEquiv.ofBijective (W c) hbij

/-- The change-of-transversal linear equivalence acts by the wreath tensor representation of
the comparison element. -/
theorem tensorInducedChangeTransversalLinearEquiv_apply (z : ⨂[R] _ : G ⧸ U, M) :
    tensorInducedChangeTransversalLinearEquiv U s t ρ z =
      ρ.wreathTensor (G ⧸ U) (monomialChangeTransversal U s t) z :=
  by
    unfold tensorInducedChangeTransversalLinearEquiv
    exact LinearEquiv.ofBijective_apply _ z

/-- On a pure tensor, the comparison applies the transversal difference in each coordinate. -/
@[simp] theorem tensorInducedChangeTransversalLinearEquiv_apply_tprod
    (m : G ⧸ U → M) :
    tensorInducedChangeTransversalLinearEquiv U s t ρ (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun x ↦
        ρ ((monomialChangeTransversal U s t).left x) (m x) := by
  rw [tensorInducedChangeTransversalLinearEquiv_apply]
  rw [Representation.wreathTensor_apply_tprod]
  simp only [monomialChangeTransversal_right, ← Equiv.Perm.inv_def, inv_one,
    Equiv.Perm.coe_one, id_eq]

/-- Changing the transversal yields an equivalence of tensor-induced representations. -/
noncomputable def tensorInducedChangeTransversal :
    (U.tensorInducedRepresentation t ρ).Equiv
      (U.tensorInducedRepresentation s ρ) :=
  Representation.Equiv.mk (tensorInducedChangeTransversalLinearEquiv U s t ρ) (fun g ↦ by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, tensorInducedRepresentation_apply]
    simp only [LinearEquiv.coe_coe]
    rw [tensorInducedChangeTransversalLinearEquiv_apply,
      tensorInducedChangeTransversalLinearEquiv_apply]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      monomialChangeTransversal_mul_monomialHom])

/-- The underlying linear equivalence of the representation comparison is the named
change-of-transversal linear equivalence. -/
theorem tensorInducedChangeTransversal_toLinearEquiv :
    (tensorInducedChangeTransversal U s t ρ).toLinearEquiv =
      tensorInducedChangeTransversalLinearEquiv U s t ρ :=
  by simp only [tensorInducedChangeTransversal, Representation.Equiv.toLinearEquiv_mk']

/-- The representation equivalence has the named factorwise linear equivalence as its
underlying map. -/
theorem tensorInducedChangeTransversal_apply (z : ⨂[R] _ : G ⧸ U, M) :
    tensorInducedChangeTransversal U s t ρ z =
      tensorInducedChangeTransversalLinearEquiv U s t ρ z :=
  by simp only [tensorInducedChangeTransversal, Representation.Equiv.mk_apply]

/-- On a pure tensor, changing the transversal applies the difference of representatives to
each factor at its coset. -/
@[simp] theorem tensorInducedChangeTransversal_apply_tprod (m : G ⧸ U → M) :
    tensorInducedChangeTransversal U s t ρ (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun x ↦
        ρ ((monomialChangeTransversal U s t).left x) (m x) := by
  rw [tensorInducedChangeTransversal_apply]
  exact tensorInducedChangeTransversalLinearEquiv_apply_tprod U s t ρ m

end Subgroup
