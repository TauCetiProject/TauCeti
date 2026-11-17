/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Order.Preorder.Finite

/-!
# Linear maps induced by index maps on finitely supported functions

An index map `s : α → β` induces `Finsupp.lmapDomain M R s : (α →₀ M) →ₗ[R] (β →₀ M)`, sending the
coefficient at `a` to `s a` (summed on fibres). This file records that powers of a permutation
endomorphism `Finsupp.lmapDomain M R π` agree with powers of `π`, together with injectivity over
torsion-free modules of affine combinations `(1 - c) • id + c • lmapDomain M R s` along injective
inflationary shifts (`∀ a, a ≤ s a`) and of nontrivial linear combinations of `Finsupp.lmapDomain`
maps along disjoint-range injections.

## Main results

* `Equiv.Perm.lmapDomain_pow`: `lmapDomain M R π ^ n = lmapDomain M R (π ^ n)`.
* `Finsupp.one_sub_smul_id_add_smul_lmapDomain_injective`,
  `Finsupp.smul_lmapDomain_comp_add_smul_lmapDomain_comp_injective`, and
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
injective inflationary shift `s : α → α` (`∀ a, a ≤ s a`) on a partial order `α`. -/
theorem one_sub_smul_id_add_smul_lmapDomain_injective
    {α R M : Type*} [PartialOrder α] [CommRing R] [IsCancelMulZero R] [AddCommGroup M] [Module R M]
    [Module.IsTorsionFree R M] {s : α → α} (hs : Function.Injective s) (hle : ∀ a, a ≤ s a)
    (c : R) :
    Function.Injective
      ((1 - c) • (LinearMap.id : (α →₀ M) →ₗ[R] (α →₀ M)) + c • lmapDomain M R s) := by
  intro u w huw; let v : α →₀ M := u - w
  have hv : ((1 - c) • (LinearMap.id : (α →₀ M) →ₗ[R] (α →₀ M)) + c • lmapDomain M R s) v = 0 := by
    rw [map_sub, huw, sub_self]
  suffices v = 0 from sub_eq_zero.1 this
  by_contra hv0
  obtain ⟨m, hm⟩ := v.support.exists_maximal (support_nonempty_iff.2 hv0)
  have hvm : v m ≠ 0 := mem_support_iff.1 hm.prop
  rcases (hle m).eq_or_lt with h_eq | h_lt
  · have hmap : mapDomain s v m = v m :=
      (congrArg (mapDomain s v) h_eq).trans (mapDomain_apply_of_injective hs v m)
    exact hvm (by simpa [hmap, ← add_smul] using congrArg (· m) hv)
  · by_cases hc : c = 0
    · exact hv0 (by simpa [hc] using hv)
    · have hv_sm : v (s m) = 0 := notMem_support_iff.1 fun hsm ↦
        h_lt.ne (hm.eq_of_le hsm h_lt.le)
      have hsm : c • v m = 0 := by
        simpa [hv_sm, mapDomain_apply_of_injective hs] using congrArg (· (s m)) hv
      exact hvm ((smul_eq_zero.1 hsm).resolve_left hc)

/-- Over a torsion-free module `N`,
`a • (lmapDomain N R s₀).comp f₀ + b • (lmapDomain N R s₁).comp f₁` is injective whenever `f₀, f₁`
are injective, `s₀, s₁` are injective with disjoint ranges, and `a ≠ 0 ∨ b ≠ 0`. -/
theorem smul_lmapDomain_comp_add_smul_lmapDomain_comp_injective
    {α₀ α₁ β R M N : Type*} [CommSemiring R] [IsCancelMulZero R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Module.IsTorsionFree R N] {s₀ : α₀ → β} {s₁ : α₁ → β}
    (hs₀ : Function.Injective s₀) (hs₁ : Function.Injective s₁)
    (hdisj : Disjoint (Set.range s₀) (Set.range s₁)) {f₀ : M →ₗ[R] (α₀ →₀ N)}
    {f₁ : M →ₗ[R] (α₁ →₀ N)} (hf₀ : Function.Injective f₀) (hf₁ : Function.Injective f₁)
    {a b : R} (hab : a ≠ 0 ∨ b ≠ 0) :
    Function.Injective
      (a • (lmapDomain N R s₀).comp f₀ + b • (lmapDomain N R s₁).comp f₁) := by
  rcases hab with ha | hb
  · exact fun _ _ hvw ↦ hf₀ <| Finsupp.ext fun x ↦ smul_right_injective N ha <| by
      simpa [fun u ↦ mapDomain_of_notMem_range u _ (Set.disjoint_left.1 hdisj ⟨x, rfl⟩),
        mapDomain_apply_of_injective hs₀] using congrArg (· (s₀ x)) hvw
  · exact fun _ _ hvw ↦ hf₁ <| Finsupp.ext fun x ↦ smul_right_injective N hb <| by
      simpa [fun u ↦ mapDomain_of_notMem_range u _ (Set.disjoint_right.1 hdisj ⟨x, rfl⟩),
        mapDomain_apply_of_injective hs₁] using congrArg (· (s₁ x)) hvw

/-- Any affine combination `(1 - c) • (lmapDomain N R s₀).comp f₀ + c • (lmapDomain N R s₁).comp f₁`
of injective linear maps followed by disjoint-range coordinate embeddings is injective. -/
theorem one_sub_smul_lmapDomain_comp_add_smul_lmapDomain_comp_injective
    {α₀ α₁ β R M N : Type*} [CommRing R] [IsCancelMulZero R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Module.IsTorsionFree R N] {s₀ : α₀ → β} {s₁ : α₁ → β}
    (hs₀ : Function.Injective s₀) (hs₁ : Function.Injective s₁)
    (hdisj : Disjoint (Set.range s₀) (Set.range s₁)) {f₀ : M →ₗ[R] (α₀ →₀ N)}
    {f₁ : M →ₗ[R] (α₁ →₀ N)} (hf₀ : Function.Injective f₀) (hf₁ : Function.Injective f₁) (c : R) :
    Function.Injective
      ((1 - c) • (lmapDomain N R s₀).comp f₀ + c • (lmapDomain N R s₁).comp f₁) := by
  by_cases hc : c = 0
  · subst hc; intro v w hvw; exact hf₀ ((mapDomain_injective hs₀) (by simpa using hvw))
  · exact smul_lmapDomain_comp_add_smul_lmapDomain_comp_injective hs₀ hs₁ hdisj hf₀ hf₁ (.inr hc)
end Finsupp
