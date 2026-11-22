/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Data.Finsupp.NeLocus
import Mathlib.Order.Preorder.Finite

/-!
# Linear maps induced by index maps on finitely supported functions

An index map `s : α → β` induces `Finsupp.lmapDomain M R s : (α →₀ M) →ₗ[R] (β →₀ M)`, sending the
coefficient at `a` to `s a` (summed on fibres). This file records that the powers of the
endomorphism `Finsupp.lmapDomain M R f` induced by `f : α → α` are induced by the iterates of
`f`, together with injectivity results over a commutative semiring `R`.

* For an injective inflationary shift `s : α → α` (`∀ a, a ≤ s a`) and `a + b = 1`, the
  combination `a • id + b • lmapDomain M R s` is injective when `M` is additively cancellative.
* For injections `s₀, s₁` with disjoint ranges, `a • (lmapDomain N R s₀).comp f₀ +
  b • (lmapDomain N R s₁).comp f₁` is injective if and only if `v ↦ (f₀ (a • v), f₁ (b • v))` is.
  In particular it is injective when `f₀, f₁` are injective and `a + b = 1`.

## Main results

* `Finsupp.lmapDomain_pow`: `lmapDomain M R f ^ n = lmapDomain M R f^[n]`.
* `Finsupp.smul_id_add_smul_lmapDomain_injective`.
* `Finsupp.smul_lmapDomain_comp_add_smul_lmapDomain_comp_injective_iff` and its corollary
  `Finsupp.smul_lmapDomain_comp_add_smul_lmapDomain_comp_injective`.
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

/-- Over a commutative semiring `R`, if `a + b = 1`, then `a • id + b • lmapDomain M R s` is
injective on `α →₀ M` for any additively cancellative `M` and any injective inflationary shift
`s : α → α` (`∀ x, x ≤ s x`) on a partial order `α`. -/
theorem smul_id_add_smul_lmapDomain_injective
    {α R M : Type*} [PartialOrder α] [CommSemiring R] [AddCancelCommMonoid M] [Module R M]
    {s : α → α} (hs : Function.Injective s) (hle : ∀ x, x ≤ s x) {a b : R} (hab : a + b = 1) :
    Function.Injective
      (a • (LinearMap.id : (α →₀ M) →ₗ[R] (α →₀ M)) + b • lmapDomain M R s) := by
  classical
  intro v w hvw
  -- Strong induction on the number of points where `v` and `w` differ: `b • v` and `b • w` have
  -- the same image too, and differ at fewer points, so `b • v = b • w`, and then `a • v = a • w`.
  induction hn : (v.neLocus w).card using Nat.strong_induction_on generalizing v w with | _ n ih
  rcases (v.neLocus w).eq_empty_or_nonempty with h | h
  · exact neLocus_eq_empty.1 h
  obtain ⟨m, hm⟩ := (v.neLocus w).exists_maximal h
  -- The point `m` is not fixed by `s`: at a fixed point the map returns the coefficient itself, so
  -- `v` and `w` would agree at `m`.
  have h_lt : m < s m := by
    refine (hle m).lt_of_ne fun h_eq ↦ mem_neLocus.1 hm.prop ?_
    have hfix (u : α →₀ M) :
        (a • (LinearMap.id : (α →₀ M) →ₗ[R] (α →₀ M)) + b • lmapDomain M R s) u m = u m := by
      have hmap : mapDomain s u m = u m :=
        (congrArg (mapDomain s u) h_eq).trans (mapDomain_apply_of_injective hs u m)
      simp [hmap, ← add_smul, hab]
    simpa only [hfix] using congrArg (· m) hvw
  -- By maximality of `m`, `v` and `w` agree at `s m`, so evaluating at `s m` gives
  -- `b • v m = b • w m`.
  have hsm : v (s m) = w (s m) := by
    by_contra hne
    exact h_lt.ne (hm.eq_of_le (mem_neLocus.2 hne) h_lt.le)
  have hbm : b • v m = b • w m := by
    have h' := congrArg (· (s m)) hvw
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, lmapDomain_apply,
      coe_add, coe_smul, Pi.add_apply, Pi.smul_apply, mapDomain_apply_of_injective hs, hsm] at h'
    exact add_left_cancel h'
  have hsub : (b • v).neLocus (b • w) ⊂ v.neLocus w :=
    (Finset.ssubset_iff_of_subset fun x hx ↦
      mem_neLocus.2 fun h ↦ mem_neLocus.1 hx (by simp [h])).2
      ⟨m, hm.prop, by simpa [mem_neLocus] using hbm⟩
  have hbvw : b • v = b • w :=
    ih ((b • v).neLocus (b • w)).card (hn ▸ Finset.card_lt_card hsub)
      (by rw [map_smul, map_smul, hvw]) rfl
  have hav : a • v = a • w := by
    have h' : a • v + mapDomain s (b • v) = a • w + mapDomain s (b • w) := by
      simpa [mapDomain_smul] using hvw
    rw [hbvw] at h'
    exact add_right_cancel h'
  rw [← one_smul R v, ← one_smul R w, ← hab, add_smul, add_smul, hav, hbvw]

/-- Over a commutative semiring `R`, if `s₀, s₁` are injective with disjoint ranges, then
`a • (lmapDomain N R s₀).comp f₀ + b • (lmapDomain N R s₁).comp f₁` is injective if and only if
`v ↦ (f₀ (a • v), f₁ (b • v))` is injective. -/
theorem smul_lmapDomain_comp_add_smul_lmapDomain_comp_injective_iff
    {α₀ α₁ β R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] {s₀ : α₀ → β} {s₁ : α₁ → β}
    (hs₀ : Function.Injective s₀) (hs₁ : Function.Injective s₁)
    (hdisj : Disjoint (Set.range s₀) (Set.range s₁)) {f₀ : M →ₗ[R] (α₀ →₀ N)}
    {f₁ : M →ₗ[R] (α₁ →₀ N)} {a b : R} :
    Function.Injective (a • (lmapDomain N R s₀).comp f₀ + b • (lmapDomain N R s₁).comp f₁) ↔
      Function.Injective fun v : M ↦ (f₀ (a • v), f₁ (b • v)) := by
  -- The map factors through `v ↦ (f₀ (a • v), f₁ (b • v))`, followed by gluing the two blocks into
  -- a function on `α₀ ⊕ α₁` and mapping along the injection `Sum.elim s₀ s₁`.
  have hinj : Function.Injective
      (mapDomain (M := N) (Sum.elim s₀ s₁) ∘ sumFinsuppEquivProdFinsupp.symm) :=
    (mapDomain_injective (hs₀.sumElim hs₁ fun x y h ↦
      Set.disjoint_left.1 hdisj ⟨x, rfl⟩ ⟨y, h.symm⟩)).comp
      sumFinsuppEquivProdFinsupp.symm.injective
  have hfac : ⇑(a • (lmapDomain N R s₀).comp f₀ + b • (lmapDomain N R s₁).comp f₁) =
      (mapDomain (Sum.elim s₀ s₁) ∘ sumFinsuppEquivProdFinsupp.symm) ∘
        fun v : M ↦ (f₀ (a • v), f₁ (b • v)) := by
    ext v : 1
    simp [sumElim_eq_add, mapDomain_add, ← mapDomain_comp, mapDomain_smul]
  rw [hfac, hinj.of_comp_iff]

/-- Over a commutative semiring `R`, if `a + b = 1`, then
`a • (lmapDomain N R s₀).comp f₀ + b • (lmapDomain N R s₁).comp f₁` is injective whenever `f₀, f₁`
are injective and `s₀, s₁` are injective with disjoint ranges. -/
theorem smul_lmapDomain_comp_add_smul_lmapDomain_comp_injective
    {α₀ α₁ β R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] {s₀ : α₀ → β} {s₁ : α₁ → β}
    (hs₀ : Function.Injective s₀) (hs₁ : Function.Injective s₁)
    (hdisj : Disjoint (Set.range s₀) (Set.range s₁)) {f₀ : M →ₗ[R] (α₀ →₀ N)}
    {f₁ : M →ₗ[R] (α₁ →₀ N)} (hf₀ : Function.Injective f₀) (hf₁ : Function.Injective f₁)
    {a b : R} (hab : a + b = 1) :
    Function.Injective
      (a • (lmapDomain N R s₀).comp f₀ + b • (lmapDomain N R s₁).comp f₁) :=
  (smul_lmapDomain_comp_add_smul_lmapDomain_comp_injective_iff hs₀ hs₁ hdisj).2 fun v w h ↦ by
    rw [← one_smul R v, ← one_smul R w, ← hab, add_smul, add_smul,
      hf₀ (congrArg Prod.fst h), hf₁ (congrArg Prod.snd h)]

end Finsupp
