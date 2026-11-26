/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic
public import TauCeti.RingTheory.Idempotented.Basic

/-!
# The multiplication map `H ⊗_H M → M` of a nondegenerate module

Let `A` be a commutative ring, `H` a nonunital `A`-algebra and `M` a module over the unitization
`A ⊕ H` (a left `H`-module) whose `A`-module structure is the restriction of scalars. The tensor
product `H ⊗_H M` is the quotient of `H ⊗_A M` by the elements `h h' ⊗ m - h ⊗ h' m`
(`TauCeti.TensorOverSelf A H M`). It is the tensor product `TauCeti.BalancedTensorProduct` balanced
over the unitization, which acts on `H` on the right by multiplication, so the `A`-part of the
relations holds already in `H ⊗_A M`. Linear maps out of it are induced by bilinear maps balanced
over `H` (`TauCeti.TensorOverSelf.lift`). The action of `H` on `M` induces the multiplication map
`TauCeti.TensorOverSelf.mulMap : H ⊗_H M → M`, `h ⊗ m ↦ h m`, whose range is the nondegenerate part
`H M` (`TauCeti.TensorOverSelf.range_mulMap`).

When `H` is idempotented, the multiplication map is injective for every `M`: an element of
`H ⊗_H M` is `g ⊗ x` where `g` is a common local unit of its left factors and `x` its image in `M`.
So it is bijective when `M` is nondegenerate (`TauCeti.TensorOverSelf.mulMap_bijective`), and its
inverse sends `m` to `e ⊗ m` for any `e : H` with `e m = m`
(`TauCeti.TensorOverSelf.mulLinearEquiv_symm_apply`). The relations
`h h' ⊗ m - h ⊗ h' m` are needed for this: in `H ⊗_A M` itself, `e ⊗ m` can depend on the local
unit `e`.

## Main definitions

* `TauCeti.TensorOverSelf A H M`: the tensor product `H ⊗_H M`.
* `TauCeti.TensorOverSelf.lift`: the linear map `H ⊗_H M → N` induced by a balanced bilinear map.
* `TauCeti.TensorOverSelf.mulMap`: the multiplication map `H ⊗_H M → M`.
* `TauCeti.TensorOverSelf.mulLinearEquiv`: for nondegenerate `M`, the isomorphism `H ⊗_H M ≃ M`.

## Main results

* `TauCeti.TensorOverSelf.mulMap_injective`: the multiplication map is injective.
* `TauCeti.TensorOverSelf.range_mulMap`: its range is the nondegenerate part `H M`.
* `TauCeti.TensorOverSelf.mulMap_bijective`: it is bijective for nondegenerate `M`.
* `TauCeti.TensorOverSelf.mulLinearEquiv_symm_apply`: its inverse is `m ↦ e ⊗ m` for any local unit
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

/-- **The tensor product `H ⊗_H M`**: the quotient of `H ⊗_A M` by the elements
`h h' ⊗ m - h ⊗ h' m`, as the tensor product balanced over the unitization `A ⊕ H`, which acts on
`H` on the right by multiplication (`Unitization.instModuleMulOpposite`). -/
abbrev TensorOverSelf := BalancedTensorProduct A (Unitization A H) H M

namespace TensorOverSelf

open BalancedTensorProduct (tmul)

variable {A H M}

/-- `h h' ⊗ m = h ⊗ h' m` in `H ⊗_H M`. -/
theorem tmul_mul (h h' : H) (m : M) :
    tmul A (Unitization A H) (h * h') m =
      tmul A (Unitization A H) h ((h' : Unitization A H) • m) := by
  rw [← Unitization.op_inr_smul (R := A), BalancedTensorProduct.balance]

/-- If `g g₁ = g₁` and `g₁ x = x`, then `g₁ ⊗ x = g ⊗ x`. -/
theorem tmul_eq_tmul_of_mul_eq {g g₁ : H} {x : M} (hg : g * g₁ = g₁)
    (hx : (g₁ : Unitization A H) • x = x) :
    tmul A (Unitization A H) g₁ x = tmul A (Unitization A H) g x := by
  conv_lhs => rw [← hg, tmul_mul, hx]

variable [IsScalarTower A (Unitization A H) M]

/-- **The universal property of `H ⊗_H M`**: a bilinear map `f : H → M → N` which is balanced,
`f (h h') m = f h (h' m)`, induces a linear map `H ⊗_H M → N`, `h ⊗ m ↦ f h m`. -/
def lift {N : Type*} [AddCommGroup N] [Module A N] (f : H →ₗ[A] M →ₗ[A] N)
    (hf : ∀ (h h' : H) (m : M), f (h * h') m = f h ((h' : Unitization A H) • m)) :
    TensorOverSelf A H M →ₗ[A] N :=
  BalancedTensorProduct.lift f fun r h m ↦ by
    -- `r = a + h'` with `a : A` and `h' : H`, and `A` acts on `M` by restriction of scalars
    conv_rhs => rw [← r.inl_fst_add_inr_snd_eq, add_smul, ← Unitization.algebraMap_eq_inl,
      algebraMap_smul]
    simp [Unitization.op_smul_eq, hf]

@[simp]
theorem lift_tmul {N : Type*} [AddCommGroup N] [Module A N] (f : H →ₗ[A] M →ₗ[A] N)
    (hf : ∀ (h h' : H) (m : M), f (h * h') m = f h ((h' : Unitization A H) • m)) (h : H)
    (m : M) : lift f hf (tmul A (Unitization A H) h m) = f h m :=
  BalancedTensorProduct.lift_tmul _ _ _ _

variable (A H M) in
/-- **The multiplication map `H ⊗_H M → M`**, `h ⊗ m ↦ h m`. -/
def mulMap : TensorOverSelf A H M →ₗ[A] M :=
  lift ((Algebra.lsmul A A M).toLinearMap ∘ₗ Unitization.inrHom A A H) fun h h' m ↦ by
    simp [Unitization.inr_mul]

@[simp]
theorem mulMap_tmul (h : H) (m : M) :
    mulMap A H M (tmul A (Unitization A H) h m) = (h : Unitization A H) • m :=
  lift_tmul _ _ h m

/-- **The range of the multiplication map is the nondegenerate part `H M`.** -/
theorem range_mulMap :
    LinearMap.range (mulMap A H M) = (nondegeneratePart A H M).restrictScalars A := by
  -- the range is stable under `A ⊕ H`, as `r (h m) = (r h) m`
  let N : Submodule (Unitization A H) M :=
    { LinearMap.range (mulMap A H M) with
      smul_mem' := by
        rintro r _ ⟨z, rfl⟩
        induction z using BalancedTensorProduct.induction_on with
        | ht h m =>
          exact ⟨tmul A (Unitization A H) (r.fst • h + r.snd * h) m, by
            rw [mulMap_tmul, mulMap_tmul, smul_smul, Unitization.mul_inr]⟩
        | ha x y hx hy =>
          rw [map_add, smul_add]
          exact (LinearMap.range (mulMap A H M)).add_mem hx hy }
  refine le_antisymm ?_ fun x hx ↦ (nondegeneratePart_le_iff (N := N)).2
    (fun h m ↦ ⟨tmul A (Unitization A H) h m, mulMap_tmul h m⟩) hx
  rintro _ ⟨z, rfl⟩
  induction z using BalancedTensorProduct.induction_on with
  | ht h m => simp
  | ha x y hx hy => simpa only [map_add] using add_mem hx hy

variable [IsIdempotented H]

/-- Every element of `H ⊗_H M` is `g ⊗ x`, for `x` its image in `M` and a suitable `g : H` with
`g x = x`. -/
theorem exists_eq_tmul_mulMap (z : TensorOverSelf A H M) :
    ∃ g : H, z = tmul A (Unitization A H) g (mulMap A H M z) ∧
      (g : Unitization A H) • mulMap A H M z = mulMap A H M z := by
  classical
  induction z using BalancedTensorProduct.induction_on with
  | ht h m =>
    obtain ⟨g, -, hg⟩ := IsIdempotented.exists_isIdempotentElem {h}
    have hgh := (hg h (by simp)).1
    refine ⟨g, ?_, ?_⟩
    · rw [mulMap_tmul, ← tmul_mul, hgh]
    · rw [mulMap_tmul, smul_smul, ← Unitization.inr_mul, hgh]
  | ha z₁ z₂ ih₁ ih₂ =>
    obtain ⟨g₁, h₁, hg₁⟩ := ih₁
    obtain ⟨g₂, h₂, hg₂⟩ := ih₂
    obtain ⟨g, -, hg⟩ := IsIdempotented.exists_isIdempotentElem {g₁, g₂}
    have e₁ := (hg g₁ (by simp)).1
    have e₂ := (hg g₂ (by simp)).1
    refine ⟨g, ?_, ?_⟩
    · conv_lhs => rw [h₁, h₂, tmul_eq_tmul_of_mul_eq e₁ hg₁,
        tmul_eq_tmul_of_mul_eq e₂ hg₂]
      rw [map_add, BalancedTensorProduct.tmul_add]
    · rw [map_add, smul_add, inr_smul_eq_of_mul_eq hg₁ e₁, inr_smul_eq_of_mul_eq hg₂ e₂]

/-- **The multiplication map `H ⊗_H M → M` is injective** for idempotented `H`. -/
theorem mulMap_injective : Function.Injective (mulMap A H M) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz ↦ ?_
  obtain ⟨g, hg, -⟩ := exists_eq_tmul_mulMap z
  rw [hg, hz, BalancedTensorProduct.tmul_zero]

/-- **`H ⊗_H M ≃ M` for nondegenerate `M`**: the multiplication map is bijective. -/
theorem mulMap_bijective (hM : IsNondegenerate A H M) : Function.Bijective (mulMap A H M) :=
  ⟨mulMap_injective, LinearMap.range_eq_top.1 <| by
    rw [range_mulMap, hM.nondegeneratePart_eq_top, Submodule.restrictScalars_top]⟩

/-- **The isomorphism `H ⊗_H M ≃ M`** of a nondegenerate module, given by multiplication. -/
noncomputable def mulLinearEquiv (hM : IsNondegenerate A H M) : TensorOverSelf A H M ≃ₗ[A] M :=
  LinearEquiv.ofBijective (mulMap A H M) (mulMap_bijective hM)

@[simp]
theorem mulLinearEquiv_apply (hM : IsNondegenerate A H M) (z : TensorOverSelf A H M) :
    mulLinearEquiv hM z = mulMap A H M z :=
  LinearEquiv.ofBijective_apply _ _

/-- **The inverse of `H ⊗_H M ≃ M` is `m ↦ e ⊗ m`** for any `e : H` with `e m = m`. -/
theorem mulLinearEquiv_symm_apply (hM : IsNondegenerate A H M) {e : H} {m : M}
    (he : (e : Unitization A H) • m = m) :
    (mulLinearEquiv hM).symm m = tmul A (Unitization A H) e m :=
  (mulLinearEquiv hM).symm_apply_eq.2 (by rw [mulLinearEquiv_apply, mulMap_tmul, he])

end TensorOverSelf

end TauCeti
