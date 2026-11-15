/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Linear maps induced by permutations of the index type

A permutation `π` of `α` induces the linear endomorphism `Finsupp.lmapDomain M R π` of `α →₀ M`,
which moves the coefficient at `a` to `π a`. This file records that the powers of this
endomorphism are induced by the powers of `π`, together with injectivity of affine combinations of
`Finsupp.lmapDomain` maps along strictly monotone shifts or disjoint-range injections.

## Main results

* `Equiv.Perm.lmapDomain_pow`: `lmapDomain M R π ^ n = lmapDomain M R (π ^ n)`.
* `Finsupp.one_sub_smul_id_add_smul_lmapDomain_injective` and
  `Finsupp.one_sub_smul_lmapDomain_comp_add_smul_lmapDomain_comp_injective`.
-/

public section

namespace Equiv.Perm

variable {R M α : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- The powers of the linear map induced by a permutation are induced by its powers. -/
theorem lmapDomain_pow (π : Perm α) (n : ℕ) :
    Finsupp.lmapDomain M R π ^ n = Finsupp.lmapDomain M R ⇑(π ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, coe_one, Finsupp.lmapDomain_id, Module.End.one_eq_id]
  | succ n ih =>
    rw [pow_succ, ih, pow_succ, coe_mul, Finsupp.lmapDomain_comp, Module.End.mul_eq_comp]

end Equiv.Perm

namespace Finsupp

/-- Over a torsion-free module `M`, `(1 - c) • id + c • lmapDomain M R s` is injective for any
strictly monotone inflationary shift `s : α → α` (`∀ a, a ≤ s a`). -/
theorem one_sub_smul_id_add_smul_lmapDomain_injective
    {α R M : Type*} [LinearOrder α] [CommRing R] [IsCancelMulZero R] [AddCommGroup M] [Module R M]
    [Module.IsTorsionFree R M] {s : α → α} (hs : StrictMono s) (hle : ∀ a, a ≤ s a) (c : R) :
    Function.Injective
      ((1 - c) • (LinearMap.id : (α →₀ M) →ₗ[R] (α →₀ M)) + c • lmapDomain M R s) := by
  intro u w huw; let v : α →₀ M := u - w
  have hv : (((1 - c) • (LinearMap.id : (α →₀ M) →ₗ[R] (α →₀ M)) + c • lmapDomain M R s)) v = 0 :=
    by rw [map_sub, huw, sub_self]
  suffices hv0 : v = 0 from sub_eq_zero.1 hv0
  by_contra hv0
  let m := v.support.max' (support_nonempty_iff.2 hv0)
  have hvm : v m ≠ 0 := mem_support_iff.1 (Finset.max'_mem _ _)
  rcases (hle m).eq_or_lt with h_eq | h_lt
  · have heval := congrArg (· m) hv
    have hmap : mapDomain s v m = v m :=
      (congrArg (mapDomain s v) h_eq).trans (mapDomain_apply_of_injective hs.injective v m)
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, coe_add, coe_smul,
      Pi.add_apply, Pi.smul_apply, zero_apply, lmapDomain_apply, hmap, ← add_smul,
      sub_add_cancel, one_smul] at heval
    exact hvm heval
  · by_cases hc : c = 0
    · exact hv0 (by simpa [hc] using hv)
    · have heval := congrArg (· (s m)) hv
      have hv_sm : v (s m) = 0 := notMem_support_iff.1 fun hsm ↦
        (lt_irrefl m) (h_lt.trans_le (Finset.le_max' _ _ hsm))
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, coe_add, coe_smul,
        Pi.add_apply, Pi.smul_apply, zero_apply, lmapDomain_apply, hv_sm, smul_zero, zero_add,
        mapDomain_apply_of_injective hs.injective v m] at heval
      exact hvm ((smul_eq_zero.1 heval).resolve_left hc)

/-- Any affine combination `(1 - c) • (lmapDomain N R s₀).comp f₀ + c • (lmapDomain N R s₁).comp f₁`
of injective linear maps followed by disjoint-range coordinate embeddings is injective. -/
theorem one_sub_smul_lmapDomain_comp_add_smul_lmapDomain_comp_injective
    {α₀ α₁ β R M N : Type*} [CommRing R] [IsCancelMulZero R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Module.IsTorsionFree R N] {s₀ : α₀ → β} {s₁ : α₁ → β}
    (hs₀ : Function.Injective s₀) (hs₁ : Function.Injective s₁)
    (hdisj : Disjoint (Set.range s₀) (Set.range s₁)) {f₀ : M →ₗ[R] (α₀ →₀ N)}
    {f₁ : M →ₗ[R] (α₁ →₀ N)} (hf₀ : Function.Injective f₀) (hf₁ : Function.Injective f₁) (c : R) :
    Function.Injective
      ((1 - c) • (lmapDomain N R s₀).comp f₀ + c • (lmapDomain N R s₁).comp f₁) := fun v w hvw ↦ by
  by_cases hc : c = 0
  · subst hc; refine hf₀ ((mapDomain_injective hs₀) ?_)
    simpa only [sub_zero, one_smul, zero_smul, add_zero, LinearMap.comp_apply, lmapDomain_apply]
      using hvw
  · refine hf₁ <| Finsupp.ext fun a ↦ smul_right_injective N hc ?_
    have heval := congrArg (· (s₁ a)) hvw
    have hs₀_zero (u : α₀ →₀ N) : mapDomain s₀ u (s₁ a) = 0 :=
      mapDomain_of_notMem_range u _ (Set.disjoint_right.1 hdisj ⟨a, rfl⟩)
    simpa only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, coe_add,
      coe_smul, Pi.add_apply, Pi.smul_apply, lmapDomain_apply, hs₀_zero, smul_zero, zero_add,
      mapDomain_apply_of_injective hs₁] using heval

end Finsupp
