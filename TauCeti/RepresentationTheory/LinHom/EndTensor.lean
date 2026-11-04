/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.LinearMap.BaseChange
public import TauCeti.RepresentationTheory.BaseChange
import TauCeti.RepresentationTheory.Intertwining
import TauCeti.RepresentationTheory.Invariants
import TauCeti.RepresentationTheory.LinHom.Basic

/-!
# Endomorphism-valued linear maps as invariant tensors

Let `R → A` be a map of commutative rings, `V` a finitely generated projective `R`-module and `E`
a finitely generated projective `A`-module. An `R`-linear map `c : V → End_A E`, for instance
Clifford multiplication of a real vector space on a complex module, extends `A`-linearly to
`A ⊗[R] V` (`LinearMap.liftBaseChange`), and the finite Hom/tensor identifications
`dualTensorHomEquiv` turn that extension into a tensor

  `t(c) ∈ (A ⊗[R] V)* ⊗[A] (E* ⊗[A] E)`

(`TauCeti.endValuedTensorEquiv`, in `TauCeti.LinearAlgebra.LinearMap.BaseChange`). It is
characterized by contraction: the pure tensor `φ ⊗ (ψ ⊗ e)` corresponds to the map
`v ↦ (x ↦ φ (1 ⊗ v) • ψ x • e)`.

Now let a group `G` act on `V` by `ρ` and on `E` by `μ`. Then `G` acts on the tensor space by the
tensor product representation `(ρ_A)* ⊗ (μ* ⊗ μ)` of the dual of the base-changed representation
`ρ_A = ρ.baseChange A`, the dual of `μ`, and `μ`; on pure tensors,

  `g · (φ ⊗ (ψ ⊗ e)) = (φ ∘ ρ_A(g⁻¹)) ⊗ ((ψ ∘ μ(g⁻¹)) ⊗ μ(g) e)`.

The main result, `TauCeti.endValuedTensorEquiv_mem_invariants_iff`, says that `t(c)` is fixed by
this representation exactly when `c` satisfies the intertwining equation

  `c (ρ(g) v) = μ(g) ∘ c(v) ∘ μ(g)⁻¹`.

This is the form in which equivariance of a Clifford multiplication is used to build Clifford
module bundles associated to a principal bundle: the intertwining equation is what makes `c`
descend, and a fixed tensor is what an invariant-section argument consumes.

## Main results

* `TauCeti.endValuedTensorEquiv_mem_invariants_iff`: the tensor of `c` is invariant if and only
  if `c` intertwines `ρ` with the conjugation action of `μ`.
-/

public section

namespace TauCeti

open TensorProduct

noncomputable section

-- Rings and additive groups, unlike for `endValuedTensorEquiv`: Mathlib's
-- `Representation.invariants` is only defined in that setting.
variable {R A V E : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Projective R V]
  [AddCommGroup E] [Module A E] [Module.Finite A E] [Module.Projective A E]
  [Module R E] [IsScalarTower R A E]

variable {G : Type*} [Group G] (ρ : Representation R G V) (μ : Representation A G E)

/-- The contraction `(A ⊗[R] V)* ⊗ (E* ⊗ E) ≃ Hom_A(A ⊗[R] V, End_A E)` intertwines the tensor
product representation `(ρ_A)* ⊗ (μ* ⊗ μ)` with the conjugation representation: it contracts
`E* ⊗ E` and then `(A ⊗[R] V)* ⊗ End_A E`. -/
private def dualTensorEndRepEquiv :
    ((ρ.baseChange A).dual.tprod (μ.dual.tprod μ)).Equiv
      (Representation.linHom (ρ.baseChange A) (Representation.linHom μ μ)) :=
  ((Representation.Equiv.refl _).tprod (Representation.Equiv.dualTensorHomOfProjective μ μ)).trans
    (Representation.Equiv.dualTensorHomOfProjective (ρ.baseChange A) (Representation.linHom μ μ))

/-- **Equivariance of `c` is invariance of its tensor.** The tensor of an `R`-linear map
`c : V → End_A E` is fixed by the tensor product representation `(ρ_A)* ⊗ (μ* ⊗ μ)`, where `ρ_A`
is the scalar extension of `ρ` to `A`, if and only if `c (ρ g v) = μ g ∘ c v ∘ μ g⁻¹` for all
`g` and `v`. -/
theorem endValuedTensorEquiv_mem_invariants_iff (c : V →ₗ[R] Module.End A E) :
    endValuedTensorEquiv R A V E c ∈ ((ρ.baseChange A).dual.tprod (μ.dual.tprod μ)).invariants ↔
      ∀ g v, c (ρ g v) = μ g ∘ₗ c v ∘ₗ μ g⁻¹ := by
  rw [← (dualTensorEndRepEquiv ρ μ).apply_mem_invariants_iff]
  -- Both sides contract a pure tensor `φ ⊗ (ψ ⊗ e)` to the same map.
  have he : (dualTensorEndRepEquiv ρ μ).toLinearEquiv.toLinearMap =
      (LinearMap.liftBaseChangeEquiv A).toLinearMap ∘ₗ
        (endValuedTensorEquiv R A V E).symm.toLinearMap := by
    ext φ ψ e v x
    simp [dualTensorEndRepEquiv]
  -- `liftBaseChange` abbreviates `liftBaseChangeEquiv`, so `simpa` closes this goal.
  have hc : dualTensorEndRepEquiv ρ μ (endValuedTensorEquiv R A V E c) = c.liftBaseChange A := by
    simpa using LinearMap.congr_fun he (endValuedTensorEquiv R A V E c)
  rw [hc, Representation.mem_invariants]
  simp only [Representation.linHom_apply]
  rw [Representation.mem_linHom_invariants_iff_isIntertwining,
    LinearMap.isIntertwiningMap_liftBaseChange_iff]
  simp only [Representation.linHom_apply]

end

end TauCeti
