/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Order.Preorder.Finite

/-!
# Linear maps induced by index maps on finitely supported functions

An index map `s : α → β` induces `Finsupp.lmapDomain M R s : (α →₀ M) →ₗ[R] (β →₀ M)`, sending the
coefficient at `a` to `s a` (summed on fibres). This file records that the powers of the
endomorphism `Finsupp.lmapDomain M R f` induced by `f : α → α` are induced by the iterates of
`f`, together with injectivity criteria over any commutative ring `R`: for the affine
combinations `(1 - c) • id + c • lmapDomain M R s` along an injective inflationary shift `s`
(`∀ a, a ≤ s a`), and for the combinations
`a • (lmapDomain N R s₀).comp f₀ + b • (lmapDomain N R s₁).comp f₁` of injective linear maps
followed by injections with disjoint ranges, exactly when `v ↦ (a • v, b • v)` is injective on
the source (for instance when `a = 1 - b`, or when `a` or `b` acts regularly).

## Main results

* `Finsupp.lmapDomain_pow`: `lmapDomain M R f ^ n = lmapDomain M R f^[n]`.
* `Finsupp.one_sub_smul_id_add_smul_lmapDomain_injective`,
  `Finsupp.smul_lmapDomain_comp_add_smul_lmapDomain_comp_injective`, and
  `Finsupp.one_sub_smul_lmapDomain_comp_add_smul_lmapDomain_comp_injective`.
-/

public section

namespace Finsupp

/-- The powers of the linear map induced by an endofunction of the index type are induced by its
iterates. -/
theorem lmapDomain_pow {R M α : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (f : α → α)
    (n : ℕ) : lmapDomain M R f ^ n = lmapDomain M R f^[n] := by
  induction n with
  | zero => rw [pow_zero, Function.iterate_zero, lmapDomain_id, Module.End.one_eq_id]
  | succ n ih => rw [pow_succ, ih, Function.iterate_succ, lmapDomain_comp, Module.End.mul_eq_comp]

/-- Over any commutative ring `R`, `(1 - c) • id + c • lmapDomain M R s` is injective for any
injective inflationary shift `s : α → α` (`∀ a, a ≤ s a`) on a partial order `α`. -/
theorem one_sub_smul_id_add_smul_lmapDomain_injective
    {α R M : Type*} [PartialOrder α] [CommRing R] [AddCommGroup M] [Module R M] {s : α → α}
    (hs : Function.Injective s) (hle : ∀ a, a ≤ s a) (c : R) :
    Function.Injective
      ((1 - c) • (LinearMap.id : (α →₀ M) →ₗ[R] (α →₀ M)) + c • lmapDomain M R s) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
  -- Strong induction on the size of the support: `c • v` lies in the kernel too, and has smaller
  -- support, so `c • v = 0`, and then the map sends `v` to itself.
  induction hn : v.support.card using Nat.strong_induction_on generalizing v with | _ n ih
  rcases v.support.eq_empty_or_nonempty with h | h
  · exact support_eq_empty.1 h
  obtain ⟨m, hm⟩ := v.support.exists_maximal h
  -- `c` kills the coefficient at a maximal point `m` of the support of `v`.
  have hcm : c • v m = 0 := by
    rcases (hle m).eq_or_lt with h_eq | h_lt
    · have hmap : mapDomain s v m = v m :=
        (congrArg (mapDomain s v) h_eq).trans (mapDomain_apply_of_injective hs v m)
      rw [show v m = 0 by simpa [hmap, ← add_smul] using congrArg (· m) hv, smul_zero]
    · have hv_sm : v (s m) = 0 := notMem_support_iff.1 fun hsm ↦
        h_lt.ne (hm.eq_of_le hsm h_lt.le)
      simpa [hv_sm, mapDomain_apply_of_injective hs] using congrArg (· (s m)) hv
  have hsupp : (c • v).support ⊂ v.support :=
    (Finset.ssubset_iff_of_subset support_smul).2 ⟨m, hm.prop, by simpa using hcm⟩
  have hcv : c • v = 0 :=
    ih _ (hn ▸ Finset.card_lt_card hsupp) _ (by rw [map_smul, hv, smul_zero]) rfl
  simpa [sub_smul, hcv, ← mapDomain_smul] using hv

/-- The `s₀`-coordinates of `(a • (lmapDomain N R s₀).comp f₀ + b • (lmapDomain N R s₁).comp f₁) v`
determine `a • v`, when `f₀` and `s₀` are injective and `s₀, s₁` have disjoint ranges. -/
private theorem smul_eq_smul_of_apply_eq
    {α₀ α₁ β R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] {s₀ : α₀ → β} {s₁ : α₁ → β} (hs₀ : Function.Injective s₀)
    (hdisj : Disjoint (Set.range s₀) (Set.range s₁)) {f₀ : M →ₗ[R] (α₀ →₀ N)}
    {f₁ : M →ₗ[R] (α₁ →₀ N)} (hf₀ : Function.Injective f₀) {a b : R} {v w : M}
    (hvw : (a • (lmapDomain N R s₀).comp f₀ + b • (lmapDomain N R s₁).comp f₁) v =
      (a • (lmapDomain N R s₀).comp f₀ + b • (lmapDomain N R s₁).comp f₁) w) :
    a • v = a • w :=
  hf₀ <| by
    rw [map_smul, map_smul]
    ext x
    simpa [fun u ↦ mapDomain_of_notMem_range u _ (Set.disjoint_left.1 hdisj ⟨x, rfl⟩),
      mapDomain_apply_of_injective hs₀] using congrArg (· (s₀ x)) hvw

/-- `a • (lmapDomain N R s₀).comp f₀ + b • (lmapDomain N R s₁).comp f₁` is injective whenever
`f₀, f₁` are injective, `s₀, s₁` are injective with disjoint ranges, and `v ↦ (a • v, b • v)` is
injective on `M`. The last condition is also necessary, and holds when `a` or `b` acts regularly on
`M`; over a ring without zero divisors and a torsion-free `M`, it follows from `a ≠ 0 ∨ b ≠ 0`
(see `IsSMulRegular.of_ne_zero`). -/
theorem smul_lmapDomain_comp_add_smul_lmapDomain_comp_injective
    {α₀ α₁ β R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] {s₀ : α₀ → β} {s₁ : α₁ → β}
    (hs₀ : Function.Injective s₀) (hs₁ : Function.Injective s₁)
    (hdisj : Disjoint (Set.range s₀) (Set.range s₁)) {f₀ : M →ₗ[R] (α₀ →₀ N)}
    {f₁ : M →ₗ[R] (α₁ →₀ N)} (hf₀ : Function.Injective f₀) (hf₁ : Function.Injective f₁)
    {a b : R} (hab : Function.Injective fun v : M ↦ (a • v, b • v)) :
    Function.Injective
      (a • (lmapDomain N R s₀).comp f₀ + b • (lmapDomain N R s₁).comp f₁) := by
  intro v w hvw
  have h₀ := smul_eq_smul_of_apply_eq hs₀ hdisj hf₀ hvw
  rw [add_comm] at hvw
  exact hab (Prod.ext h₀ (smul_eq_smul_of_apply_eq hs₁ hdisj.symm hf₁ hvw))

/-- Over any commutative ring `R`, every affine combination
`(1 - c) • (lmapDomain N R s₀).comp f₀ + c • (lmapDomain N R s₁).comp f₁` of injective linear maps
followed by disjoint-range coordinate embeddings is injective. -/
theorem one_sub_smul_lmapDomain_comp_add_smul_lmapDomain_comp_injective
    {α₀ α₁ β R M N : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] {s₀ : α₀ → β} {s₁ : α₁ → β}
    (hs₀ : Function.Injective s₀) (hs₁ : Function.Injective s₁)
    (hdisj : Disjoint (Set.range s₀) (Set.range s₁)) {f₀ : M →ₗ[R] (α₀ →₀ N)}
    {f₁ : M →ₗ[R] (α₁ →₀ N)} (hf₀ : Function.Injective f₀) (hf₁ : Function.Injective f₁) (c : R) :
    Function.Injective
      ((1 - c) • (lmapDomain N R s₀).comp f₀ + c • (lmapDomain N R s₁).comp f₁) :=
  smul_lmapDomain_comp_add_smul_lmapDomain_comp_injective hs₀ hs₁ hdisj hf₀ hf₁ fun v w h ↦ by
    simpa [← add_smul] using congrArg (fun p : M × M ↦ p.1 + p.2) h

end Finsupp
