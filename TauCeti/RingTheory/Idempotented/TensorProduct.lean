/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import TauCeti.RingTheory.Idempotented.Basic

/-!
# The multiplication map `H ⊗_H M → M` of a nondegenerate module

Let `A` be a commutative ring, `H` a nonunital `A`-algebra and `M` a module over the unitization
`A ⊕ H` (a left `H`-module) whose `A`-module structure is the restriction of scalars. The tensor
product `H ⊗_H M` is the quotient of `H ⊗_A M` by the elements `h h' ⊗ m - h ⊗ h' m`
(`TauCeti.TensorOverSelf A H M`), and the action of `H` on `M` induces the multiplication map
`TauCeti.TensorOverSelf.mulMap : H ⊗_H M → M`, `h ⊗ m ↦ h m`.

When `H` is idempotented, the multiplication map is injective for every `M`: an element of
`H ⊗_H M` is `g ⊗ x` where `g` is a common local unit of its left factors and `x` its image in `M`.
Its range is the nondegenerate part `H M`, so it is bijective exactly when `M` is nondegenerate
(`TauCeti.TensorOverSelf.mulMap_bijective`), and its inverse sends `m` to `e ⊗ m` for any `e : H`
with `e m = m` (`TauCeti.TensorOverSelf.mulEquiv_symm_apply`). The relations
`h h' ⊗ m - h ⊗ h' m` are needed for this: in `H ⊗_A M` itself, `e ⊗ m` can depend on the local
unit `e`.

## Main definitions

* `TauCeti.TensorOverSelf A H M`: the tensor product `H ⊗_H M`.
* `TauCeti.TensorOverSelf.mulMap`: the multiplication map `H ⊗_H M → M`.
* `TauCeti.TensorOverSelf.mulEquiv`: for nondegenerate `M`, the isomorphism `H ⊗_H M ≃ M`.

## Main results

* `TauCeti.TensorOverSelf.mulMap_injective`: the multiplication map is injective.
* `TauCeti.TensorOverSelf.range_mulMap`: its range is the nondegenerate part `H M`.
* `TauCeti.TensorOverSelf.mulMap_bijective`: it is bijective for nondegenerate `M`.
* `TauCeti.TensorOverSelf.mulEquiv_symm_apply`: its inverse is `m ↦ e ⊗ m` for any local unit
  `e` of `m`.

## References

* J. N. Bernstein, *Le "centre" de Bernstein*, edited by P. Deligne, in *Représentations des groupes
  réductifs sur un corps local*, Hermann, Paris (1984), §1.1–§1.2.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable (A H : Type*) [CommRing A] [NonUnitalRing H] [Module A H] [IsScalarTower A H H]
  [SMulCommClass A H H] (M : Type*) [AddCommGroup M] [Module (Unitization A H) M] [Module A M]

/-- The relations `h h' ⊗ m - h ⊗ h' m` of `H ⊗_H M` inside `H ⊗_A M`. -/
def tensorOverSelfRelations : Submodule A (H ⊗[A] M) :=
  Submodule.span A {z | ∃ (h h' : H) (m : M),
    z = (h * h') ⊗ₜ[A] m - h ⊗ₜ[A] ((h' : Unitization A H) • m)}

/-- **The tensor product `H ⊗_H M`**: the quotient of `H ⊗_A M` by the elements
`h h' ⊗ m - h ⊗ h' m`. -/
abbrev TensorOverSelf := (H ⊗[A] M) ⧸ tensorOverSelfRelations A H M

namespace TensorOverSelf

variable {A H M}

/-- The class of `h ⊗ m` in `H ⊗_H M`. -/
abbrev mk (h : H) (m : M) : TensorOverSelf A H M :=
  Submodule.Quotient.mk (h ⊗ₜ[A] m)

theorem mk_mul (h h' : H) (m : M) :
    (mk (h * h') m : TensorOverSelf A H M) = mk h ((h' : Unitization A H) • m) := by
  rw [Submodule.Quotient.eq]
  exact Submodule.subset_span ⟨h, h', m, rfl⟩

variable [IsScalarTower A (Unitization A H) M]

/-- The scalars of `A` commute with the action of `H` on `M`. -/
private theorem inr_smul_smul (h : H) (a : A) (m : M) :
    (h : Unitization A H) • a • m = a • (h : Unitization A H) • m := by
  rw [← smul_one_smul (Unitization A H) a m, smul_smul, mul_smul_comm, mul_one, smul_assoc]

variable (A H M) in
/-- The action map `H ⊗_A M → M`, `h ⊗ m ↦ h m`. -/
def actionMap : H ⊗[A] M →ₗ[A] M :=
  TensorProduct.lift <| LinearMap.mk₂ A (fun (h : H) (m : M) ↦ (h : Unitization A H) • m)
    (fun h₁ h₂ m ↦ by rw [Unitization.inr_add, add_smul])
    (fun a h m ↦ by rw [Unitization.inr_smul, smul_assoc])
    (fun h m₁ m₂ ↦ smul_add _ m₁ m₂)
    (fun a h m ↦ inr_smul_smul h a m)

@[simp]
theorem actionMap_tmul (h : H) (m : M) :
    actionMap A H M (h ⊗ₜ[A] m) = (h : Unitization A H) • m :=
  TensorProduct.lift.tmul _ _

variable (A H M) in
/-- **The multiplication map `H ⊗_H M → M`**, `h ⊗ m ↦ h m`. -/
def mulMap : TensorOverSelf A H M →ₗ[A] M :=
  (tensorOverSelfRelations A H M).liftQ (actionMap A H M) <| Submodule.span_le.2 <| by
    rintro _ ⟨h, h', m, rfl⟩
    simp [Unitization.inr_mul, mul_smul]

@[simp]
theorem mulMap_mk (h : H) (m : M) : mulMap A H M (mk h m) = (h : Unitization A H) • m :=
  actionMap_tmul h m

variable [IsIdempotented H]

/-- Every element of `H ⊗_H M` is `g ⊗ x`, for `x` its image in `M` and a suitable `g : H` with
`g x = x`. -/
theorem exists_eq_mk_mulMap (z : TensorOverSelf A H M) :
    ∃ g : H, z = mk g (mulMap A H M z) ∧
      (g : Unitization A H) • mulMap A H M z = mulMap A H M z := by
  classical
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  induction z using TensorProduct.inductionOn with
  | tmul h m =>
    obtain ⟨g, -, hg⟩ := IsIdempotented.exists_isIdempotentElem {h}
    have hgh := (hg h (by simp)).1
    refine ⟨g, ?_, ?_⟩
    · change mk h m = mk g (mulMap A H M (mk h m))
      rw [mulMap_mk, ← mk_mul, hgh]
    · change (g : Unitization A H) • mulMap A H M (mk h m) = mulMap A H M (mk h m)
      rw [mulMap_mk, smul_smul, ← Unitization.inr_mul, hgh]
  | add z₁ z₂ ih₁ ih₂ =>
    obtain ⟨g₁, h₁, hg₁⟩ := ih₁
    obtain ⟨g₂, h₂, hg₂⟩ := ih₂
    obtain ⟨g, -, hg⟩ := IsIdempotented.exists_isIdempotentElem {g₁, g₂}
    have e₁ := (hg g₁ (by simp)).1
    have e₂ := (hg g₂ (by simp)).1
    -- `g₁ ⊗ x₁ = g g₁ ⊗ x₁ = g ⊗ g₁ x₁ = g ⊗ x₁`, and likewise for `z₂`
    have k₁ : (mk g₁ (mulMap A H M (Submodule.Quotient.mk z₁)) : TensorOverSelf A H M) =
        mk g (mulMap A H M (Submodule.Quotient.mk z₁)) := by
      conv_lhs => rw [← e₁, mk_mul, hg₁]
    have k₂ : (mk g₂ (mulMap A H M (Submodule.Quotient.mk z₂)) : TensorOverSelf A H M) =
        mk g (mulMap A H M (Submodule.Quotient.mk z₂)) := by
      conv_lhs => rw [← e₂, mk_mul, hg₂]
    refine ⟨g, ?_, ?_⟩
    · calc Submodule.Quotient.mk (z₁ + z₂)
          = Submodule.Quotient.mk (p := tensorOverSelfRelations A H M) z₁ +
              Submodule.Quotient.mk z₂ := Submodule.Quotient.mk_add _
        _ = mk g (mulMap A H M (Submodule.Quotient.mk z₁)) +
              mk g (mulMap A H M (Submodule.Quotient.mk z₂)) := by
          rw [← k₁, ← k₂]
          exact congrArg₂ (· + ·) h₁ h₂
        _ = mk g (mulMap A H M (Submodule.Quotient.mk (z₁ + z₂))) := by
          rw [Submodule.Quotient.mk_add, map_add]
          simp only [mk, TensorProduct.tmul_add, Submodule.Quotient.mk_add]
    · rw [Submodule.Quotient.mk_add, map_add, smul_add, ← hg₁, ← hg₂, smul_smul, smul_smul,
        ← Unitization.inr_mul, ← Unitization.inr_mul, e₁, e₂]

/-- **The multiplication map `H ⊗_H M → M` is injective** for idempotented `H`. -/
theorem mulMap_injective : Function.Injective (mulMap A H M) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz ↦ ?_
  obtain ⟨g, hg, -⟩ := exists_eq_mk_mulMap z
  rw [hg, hz, mk, TensorProduct.tmul_zero, Submodule.Quotient.mk_zero]

/-- **The range of the multiplication map is the nondegenerate part `H M`.** -/
theorem range_mulMap :
    (LinearMap.range (mulMap A H M) : Set M) = nondegeneratePart A H M := by
  ext m
  refine ⟨?_, fun hm ↦ ?_⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨g, -, hg⟩ := exists_eq_mk_mulMap z
    rw [SetLike.mem_coe, ← hg]
    exact inr_smul_mem_nondegeneratePart g _
  · obtain ⟨e, -, he⟩ := mem_nondegeneratePart_iff.1 hm
    exact ⟨mk e m, by rw [mulMap_mk, he]⟩

/-- **`H ⊗_H M ≃ M` for nondegenerate `M`**: the multiplication map is bijective. -/
theorem mulMap_bijective (hM : IsNondegenerate A H M) : Function.Bijective (mulMap A H M) := by
  refine ⟨mulMap_injective, fun m ↦ ?_⟩
  have h := range_mulMap (A := A) (H := H) (M := M)
  rw [hM.nondegeneratePart_eq_top, Submodule.top_coe, LinearMap.coe_range,
    Set.range_eq_univ] at h
  exact h m

/-- **The isomorphism `H ⊗_H M ≃ M`** of a nondegenerate module, given by multiplication. -/
noncomputable def mulEquiv (hM : IsNondegenerate A H M) : TensorOverSelf A H M ≃ₗ[A] M :=
  LinearEquiv.ofBijective (mulMap A H M) (mulMap_bijective hM)

@[simp]
theorem mulEquiv_apply (hM : IsNondegenerate A H M) (z : TensorOverSelf A H M) :
    mulEquiv hM z = mulMap A H M z :=
  (rfl)

/-- **The inverse of `H ⊗_H M ≃ M` is `m ↦ e ⊗ m`** for any `e : H` with `e m = m`. -/
theorem mulEquiv_symm_apply (hM : IsNondegenerate A H M) {e : H} {m : M}
    (he : (e : Unitization A H) • m = m) : (mulEquiv hM).symm m = mk e m :=
  (mulEquiv hM).symm_apply_eq.2 (by rw [mulEquiv_apply, mulMap_mk, he])

end TensorOverSelf

end TauCeti
