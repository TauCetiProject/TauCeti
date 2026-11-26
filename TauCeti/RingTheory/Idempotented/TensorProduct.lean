/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import TauCeti.RingTheory.Idempotented.Basic

/-!
# The multiplication map `H ⊗_H M → M` of a nondegenerate module

Let `A` be a commutative ring, `H` a nonunital `A`-algebra and `M` a module over the unitization
`A ⊕ H` (a left `H`-module) whose `A`-module structure is the restriction of scalars. The tensor
product `H ⊗_H M` is the quotient of `H ⊗_A M` by the elements `h h' ⊗ m - h ⊗ h' m`
(`TauCeti.TensorOverSelf A H M`); linear maps out of it are induced by balanced bilinear maps
(`TauCeti.TensorOverSelf.lift`). The action of `H` on `M` induces the multiplication map
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

/-- If `g g₁ = g₁` and `g₁ x = x`, then `g₁ ⊗ x = g ⊗ x`. -/
theorem mk_eq_mk_of_mul_eq {g g₁ : H} {x : M} (hg : g * g₁ = g₁)
    (hx : (g₁ : Unitization A H) • x = x) : (mk g₁ x : TensorOverSelf A H M) = mk g x := by
  conv_lhs => rw [← hg, mk_mul, hx]

@[simp]
theorem mk_add_left (h₁ h₂ : H) (m : M) :
    (mk (h₁ + h₂) m : TensorOverSelf A H M) = mk h₁ m + mk h₂ m := by
  rw [mk, TensorProduct.add_tmul, Submodule.Quotient.mk_add]

@[simp]
theorem mk_add_right (h : H) (m₁ m₂ : M) :
    (mk h (m₁ + m₂) : TensorOverSelf A H M) = mk h m₁ + mk h m₂ := by
  rw [mk, TensorProduct.tmul_add, Submodule.Quotient.mk_add]

@[simp]
theorem mk_smul_left (a : A) (h : H) (m : M) :
    (mk (a • h) m : TensorOverSelf A H M) = a • mk h m := by
  rw [mk, ← TensorProduct.smul_tmul', Submodule.Quotient.mk_smul]

@[simp]
theorem mk_smul_right (a : A) (h : H) (m : M) :
    (mk h (a • m) : TensorOverSelf A H M) = a • mk h m := by
  rw [mk, TensorProduct.tmul_smul, Submodule.Quotient.mk_smul]

@[simp]
theorem mk_zero_left (m : M) : (mk 0 m : TensorOverSelf A H M) = 0 := by
  rw [mk, TensorProduct.zero_tmul, Submodule.Quotient.mk_zero]

@[simp]
theorem mk_zero_right (h : H) : (mk h 0 : TensorOverSelf A H M) = 0 := by
  rw [mk, TensorProduct.tmul_zero, Submodule.Quotient.mk_zero]

/-- Induction on `H ⊗_H M`: a property holding for every `h ⊗ m` and closed under addition holds
everywhere. -/
@[elab_as_elim]
theorem induction_on {motive : TensorOverSelf A H M → Prop} (z : TensorOverSelf A H M)
    (mk : ∀ (h : H) (m : M), motive (mk h m))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  induction z using TensorProduct.inductionOn with
  | tmul h m => exact mk h m
  | add z₁ z₂ ih₁ ih₂ => exact add _ _ ih₁ ih₂

/-- Two linear maps out of `H ⊗_H M` agreeing on every `h ⊗ m` are equal. -/
@[ext]
theorem ext {N : Type*} [AddCommGroup N] [Module A N] {f g : TensorOverSelf A H M →ₗ[A] N}
    (hfg : ∀ (h : H) (m : M), f (mk h m) = g (mk h m)) : f = g :=
  Submodule.linearMap_qext _ <| TensorProduct.ext' hfg

/-- **The universal property of `H ⊗_H M`**: a bilinear map `f : H → M → N` which is balanced,
`f (h h') m = f h (h' m)`, induces a linear map `H ⊗_H M → N`, `h ⊗ m ↦ f h m`. -/
def lift {N : Type*} [AddCommGroup N] [Module A N] (f : H →ₗ[A] M →ₗ[A] N)
    (hf : ∀ (h h' : H) (m : M), f (h * h') m = f h ((h' : Unitization A H) • m)) :
    TensorOverSelf A H M →ₗ[A] N :=
  (tensorOverSelfRelations A H M).liftQ (TensorProduct.lift f) <| Submodule.span_le.2 <| by
    rintro _ ⟨h, h', m, rfl⟩
    simp [hf]

@[simp]
theorem lift_mk {N : Type*} [AddCommGroup N] [Module A N] (f : H →ₗ[A] M →ₗ[A] N)
    (hf : ∀ (h h' : H) (m : M), f (h * h') m = f h ((h' : Unitization A H) • m)) (h : H)
    (m : M) : lift f hf (mk h m) = f h m :=
  TensorProduct.lift.tmul _ _

variable [IsScalarTower A (Unitization A H) M]

variable (A H M) in
/-- **The multiplication map `H ⊗_H M → M`**, `h ⊗ m ↦ h m`. -/
def mulMap : TensorOverSelf A H M →ₗ[A] M :=
  lift ((Algebra.lsmul A A M).toLinearMap ∘ₗ Unitization.inrHom A A H) fun h h' m ↦ by
    simp [Unitization.inr_mul]

@[simp]
theorem mulMap_mk (h : H) (m : M) : mulMap A H M (mk h m) = (h : Unitization A H) • m :=
  lift_mk _ _ h m

/-- **The range of the multiplication map is the nondegenerate part `H M`.** -/
theorem range_mulMap :
    LinearMap.range (mulMap A H M) = (nondegeneratePart A H M).restrictScalars A := by
  -- the range is stable under `A ⊕ H`, as `r (h m) = (r h) m`
  let N : Submodule (Unitization A H) M :=
    { LinearMap.range (mulMap A H M) with
      smul_mem' := by
        rintro r _ ⟨z, rfl⟩
        induction z using induction_on with
        | mk h m =>
          exact ⟨mk (r.fst • h + r.snd * h) m, by
            rw [mulMap_mk, mulMap_mk, smul_smul, Unitization.mul_inr]⟩
        | add x y hx hy =>
          rw [map_add, smul_add]
          exact (LinearMap.range (mulMap A H M)).add_mem hx hy }
  refine le_antisymm ?_ fun x hx ↦ (nondegeneratePart_le_iff (N := N)).2
    (fun h m ↦ ⟨mk h m, mulMap_mk h m⟩) hx
  rintro _ ⟨z, rfl⟩
  induction z using induction_on with
  | mk h m => simp
  | add x y hx hy => simpa only [map_add] using add_mem hx hy

variable [IsIdempotented H]

/-- Every element of `H ⊗_H M` is `g ⊗ x`, for `x` its image in `M` and a suitable `g : H` with
`g x = x`. -/
theorem exists_eq_mk_mulMap (z : TensorOverSelf A H M) :
    ∃ g : H, z = mk g (mulMap A H M z) ∧
      (g : Unitization A H) • mulMap A H M z = mulMap A H M z := by
  classical
  induction z using induction_on with
  | mk h m =>
    obtain ⟨g, -, hg⟩ := IsIdempotented.exists_isIdempotentElem {h}
    have hgh := (hg h (by simp)).1
    refine ⟨g, ?_, ?_⟩
    · rw [mulMap_mk, ← mk_mul, hgh]
    · rw [mulMap_mk, smul_smul, ← Unitization.inr_mul, hgh]
  | add z₁ z₂ ih₁ ih₂ =>
    obtain ⟨g₁, h₁, hg₁⟩ := ih₁
    obtain ⟨g₂, h₂, hg₂⟩ := ih₂
    obtain ⟨g, -, hg⟩ := IsIdempotented.exists_isIdempotentElem {g₁, g₂}
    have e₁ := (hg g₁ (by simp)).1
    have e₂ := (hg g₂ (by simp)).1
    refine ⟨g, ?_, ?_⟩
    · conv_lhs => rw [h₁, h₂, mk_eq_mk_of_mul_eq e₁ hg₁, mk_eq_mk_of_mul_eq e₂ hg₂]
      rw [map_add, mk_add_right]
    · rw [map_add, smul_add, inr_smul_eq_of_mul_eq hg₁ e₁, inr_smul_eq_of_mul_eq hg₂ e₂]

/-- **The multiplication map `H ⊗_H M → M` is injective** for idempotented `H`. -/
theorem mulMap_injective : Function.Injective (mulMap A H M) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz ↦ ?_
  obtain ⟨g, hg, -⟩ := exists_eq_mk_mulMap z
  rw [hg, hz, mk_zero_right]

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
    (he : (e : Unitization A H) • m = m) : (mulLinearEquiv hM).symm m = mk e m :=
  (mulLinearEquiv hM).symm_apply_eq.2 (by rw [mulLinearEquiv_apply, mulMap_mk, he])

end TensorOverSelf

end TauCeti
