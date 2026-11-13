/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.PseudoCoherent.Basic

import Mathlib.LinearAlgebra.Basis.Prod
import TauCeti.LinearAlgebra.Exact

/-!
# Two-out-of-three for pseudocoherent modules

Let `0 → M₁ → M → M₂ → 0` be a short exact sequence of modules over a ring `R`, given by an
injective `f : M₁ →ₗ[R] M` and a surjective `g : M →ₗ[R] M₂` with `Function.Exact f g`. This file
shows how `m`-pseudocoherence (`TauCeti.Huber.IsPseudoCoherentOver`) moves along it:

* an extension of `m`-pseudocoherent modules is `m`-pseudocoherent;
* a cokernel loses at most one degree: if `M₁` is `(m - 1)`-pseudocoherent and `M` is
  `m`-pseudocoherent, then `M₂` is `m`-pseudocoherent, and in degree `0` nothing is asked of `M₁`;
* a kernel loses at most one degree: if `M` is `m`-pseudocoherent and `M₂` is
  `(m + 1)`-pseudocoherent, then `M₁` is `m`-pseudocoherent.

The degree `m` ranges over `ℕ∞`. Since `⊤ + 1 = ⊤ - 1 = ⊤`, the case `m = ⊤` says that if two of
`M₁`, `M`, `M₂` are pseudocoherent then so is the third, so pseudocoherent modules are closed under
extensions, kernels of surjections and cokernels of injections. This is the module theory that
makes pseudocoherent modules, unlike finitely presented ones, behave well over rings that are not
coherent.

## Main results

* `TauCeti.Huber.IsPseudoCoherentOver.extension`: extensions of `m`-pseudocoherent modules are
  `m`-pseudocoherent.
* `TauCeti.Huber.IsPseudoCoherentOver.cokernel`: the cokernel of an injection from an
  `(m - 1)`-pseudocoherent module into an `m`-pseudocoherent module is `m`-pseudocoherent.
* `TauCeti.Huber.IsPseudoCoherentOver.kernel`: the kernel of a surjection from an
  `m`-pseudocoherent module onto an `(m + 1)`-pseudocoherent module is `m`-pseudocoherent.
* `TauCeti.Huber.IsPseudoCoherentOver.of_prod_left`,
  `TauCeti.Huber.IsPseudoCoherentOver.of_prod_right`,
  `TauCeti.Huber.IsPseudoCoherentOver.prod_iff`,
  `TauCeti.Huber.IsPseudoCoherentOver.of_retract`: direct summands and retracts of
  `m`-pseudocoherent modules are `m`-pseudocoherent.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory, II: Imperfect period rings*, §1.1,
  Lemma 1.1.5.
* The Stacks Project, Lemmas 15.66.2 and 15.66.6 (Tags 064R and 064V, with the index negated).
-/

public section

namespace TauCeti.Huber.IsPseudoCoherentOver

open LinearMap

universe u

variable {R : Type u} [Ring R]

section ShortExact

/- The extension statement is proved one degree at a time: surjections `Rᵃ → M₁` and `Rᵇ → M₂`
combine, after lifting `Rᵇ → M₂` along `g`, to a surjection `Rᵃ × Rᵇ → M` whose kernel is an
extension of the two kernels (the horseshoe step `TauCeti.exists_surjective_ker_exact`). The other
two statements reduce to it through the short exact sequence `0 → ker π → ker (g ∘ π) → ker g → 0`
attached to a surjection `π : Rᵏ → M` (`TauCeti.exact_ker_comp`). -/

variable {M₁ M M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M] [Module R M]
  [AddCommGroup M₂] [Module R M₂] {f : M₁ →ₗ[R] M} {g : M →ₗ[R] M₂}

/-- Degree `0` of the extension statement: an extension of finitely generated modules is finitely
generated. -/
private theorem extension_zero (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (h₁ : IsPseudoCoherentOver R M₁ 0) (h₂ : IsPseudoCoherentOver R M₂ 0) :
    IsPseudoCoherentOver R M 0 :=
  have := zero_iff.mp h₁
  have := zero_iff.mp h₂
  zero_iff.mpr (.of_exact hfg hg)

/-- The inductive step of the extension statement: if extensions of `n`-pseudocoherent modules in
the universe of `R` are `n`-pseudocoherent, then extensions of `(n + 1)`-pseudocoherent modules are
`(n + 1)`-pseudocoherent. The kernels of the horseshoe step lie in the universe of `R`. -/
private theorem extension_succ {n : ℕ}
    (ih : ∀ {N₁ N N₂ : Type u} [AddCommGroup N₁] [Module R N₁] [AddCommGroup N] [Module R N]
      [AddCommGroup N₂] [Module R N₂] {f : N₁ →ₗ[R] N} {g : N →ₗ[R] N₂},
      Function.Injective f → Function.Exact f g → Function.Surjective g →
      IsPseudoCoherentOver R N₁ n → IsPseudoCoherentOver R N₂ n → IsPseudoCoherentOver R N n)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (h₁ : IsPseudoCoherentOver R M₁ (n + 1 : ℕ)) (h₂ : IsPseudoCoherentOver R M₂ (n + 1 : ℕ)) :
    IsPseudoCoherentOver R M (n + 1 : ℕ) := by
  rw [Nat.cast_succ] at h₁ h₂ ⊢
  rw [succ_iff] at h₁ h₂
  obtain ⟨a, π₁, hπ₁, h₁⟩ := h₁
  obtain ⟨b, π₂, hπ₂, h₂⟩ := h₂
  obtain ⟨π, hπ, i, p, hi, hip, hp⟩ := exists_surjective_ker_exact hf hfg hg hπ₁ hπ₂
  exact (succ_iff_ker hπ).mpr (ih hi hip hp h₁ h₂)

/-- The extension statement in degree `n`, for modules in the universe of `R`. -/
private theorem extension_nat (n : ℕ) :
    ∀ {N₁ N N₂ : Type u} [AddCommGroup N₁] [Module R N₁] [AddCommGroup N] [Module R N]
      [AddCommGroup N₂] [Module R N₂] {f : N₁ →ₗ[R] N} {g : N →ₗ[R] N₂},
      Function.Injective f → Function.Exact f g → Function.Surjective g →
      IsPseudoCoherentOver R N₁ n → IsPseudoCoherentOver R N₂ n → IsPseudoCoherentOver R N n := by
  induction n with
  | zero => exact fun _ hfg hg h₁ h₂ ↦ extension_zero hfg hg h₁ h₂
  | succ n ih => exact fun hf hfg hg h₁ h₂ ↦ extension_succ ih hf hfg hg h₁ h₂

/-- **Extensions of `m`-pseudocoherent modules are `m`-pseudocoherent.** If
`0 → M₁ → M → M₂ → 0` is exact and `M₁` and `M₂` are `m`-pseudocoherent, so is `M` (Kedlaya–Liu II,
Lemma 1.1.5(a); Stacks, Tag 064R). -/
theorem extension (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) {m : ℕ∞} (h₁ : IsPseudoCoherentOver R M₁ m)
    (h₂ : IsPseudoCoherentOver R M₂ m) : IsPseudoCoherentOver R M m := by
  have hnat (n : ℕ) (h₁ : IsPseudoCoherentOver R M₁ n) (h₂ : IsPseudoCoherentOver R M₂ n) :
      IsPseudoCoherentOver R M n := by
    cases n with
    | zero => exact extension_zero hfg hg h₁ h₂
    | succ n => exact extension_succ (extension_nat n) hf hfg hg h₁ h₂
  induction m using ENat.recTopCoe with
  | top => exact top_iff.mpr fun n ↦ hnat n (top_iff.mp h₁ n) (top_iff.mp h₂ n)
  | coe n => exact hnat n h₁ h₂

/-- **A cokernel loses at most one degree of pseudocoherence.** If `0 → M₁ → M → M₂ → 0` is exact,
`M` is `m`-pseudocoherent and, when `m > 0`, `M₁` is `(m - 1)`-pseudocoherent, then `M₂` is
`m`-pseudocoherent; in degree `0` this only says that a quotient of a finitely generated module is
finitely generated (Kedlaya–Liu II, Lemma 1.1.5(b); Stacks, Tag 064R). -/
theorem cokernel (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) {m : ℕ∞} (h₁ : 0 < m → IsPseudoCoherentOver R M₁ (m - 1))
    (hM : IsPseudoCoherentOver R M m) : IsPseudoCoherentOver R M₂ m := by
  have := hM.finite
  have e : M₁ ≃ₗ[R] ker g :=
    (LinearEquiv.ofInjective f hf).trans (.ofEq _ _ (exact_iff.mp hfg).symm)
  rcases eq_zero_or_pos m with rfl | hm
  · exact zero_iff.mpr (.of_surjective g hg)
  -- For a surjection `π : Rᵏ → M`, `ker (g ∘ π)` is an extension of `ker g ≃ M₁` by `ker π`.
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' R M
  obtain ⟨hi, hip, hp⟩ := exact_ker_comp hπ g
  rw [← tsub_add_cancel_of_le (Order.one_le_iff_pos.mpr hm)] at hM ⊢
  exact (succ_iff_ker (f := g ∘ₗ π) (hg.comp hπ)).mpr
    (extension hi hip hp (hM.ker_of_projective hπ) ((h₁ hm).of_equiv e))

/-- **A kernel loses at most one degree of pseudocoherence.** If `0 → M₁ → M → M₂ → 0` is exact,
`M` is `m`-pseudocoherent and `M₂` is `(m + 1)`-pseudocoherent, then `M₁` is `m`-pseudocoherent
(Kedlaya–Liu II, Lemma 1.1.5(c); Stacks, Tag 064R). -/
theorem kernel (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) {m : ℕ∞} (hM : IsPseudoCoherentOver R M m)
    (h₂ : IsPseudoCoherentOver R M₂ (m + 1)) : IsPseudoCoherentOver R M₁ m := by
  -- For a surjection `π : Rᵏ → M`, `ker g ≃ M₁` is the cokernel of `ker π → ker (g ∘ π)`.
  have := hM.finite
  have e : M₁ ≃ₗ[R] ker g :=
    (LinearEquiv.ofInjective f hf).trans (.ofEq _ _ (exact_iff.mp hfg).symm)
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' R M
  obtain ⟨hi, hip, hp⟩ := exact_ker_comp hπ g
  refine (cokernel hi hip hp (fun hm ↦ ?_)
    (h₂.ker_of_projective (f := g ∘ₗ π) (hg.comp hπ))).of_equiv e.symm
  rw [← tsub_add_cancel_of_le (Order.one_le_iff_pos.mpr hm)] at hM
  exact hM.ker_of_projective hπ

end ShortExact

section Retract

variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

private theorem of_prod_nat : ∀ {n : ℕ}, IsPseudoCoherentOver R (M × N) n →
    IsPseudoCoherentOver R M n ∧ IsPseudoCoherentOver R N n
  | 0, h =>
    have := h.finite
    ⟨zero_iff.mpr (.of_surjective (fst R M N) Prod.fst_surjective),
      zero_iff.mpr (.of_surjective (snd R M N) Prod.snd_surjective)⟩
  | n + 1, h => by
    obtain ⟨hM, hN⟩ := of_prod_nat (h.mono (Nat.cast_le.mpr n.le_succ))
    have hsub : ((n + 1 : ℕ) : ℕ∞) - 1 = n := by simp
    have exact_inr_fst : Function.Exact (inr R M N) (fst R M N) := fun x ↦
      ⟨fun hx ↦ ⟨x.2, Prod.ext hx.symm rfl⟩, by rintro ⟨_, rfl⟩; rfl⟩
    have exact_inl_snd : Function.Exact (inl R M N) (snd R M N) := fun x ↦
      ⟨fun hy ↦ ⟨x.1, Prod.ext rfl hy.symm⟩, by rintro ⟨_, rfl⟩; rfl⟩
    exact ⟨cokernel inr_injective exact_inr_fst Prod.fst_surjective (fun _ ↦ hsub ▸ hN) h,
      cokernel inl_injective exact_inl_snd Prod.snd_surjective (fun _ ↦ hsub ▸ hM) h⟩

/-- The first factor of an `m`-pseudocoherent product module is `m`-pseudocoherent
(Stacks, Tag 064V). -/
theorem of_prod_left {m : ℕ∞} (h : IsPseudoCoherentOver R (M × N) m) :
    IsPseudoCoherentOver R M m := by
  induction m using ENat.recTopCoe with
  | top => exact top_iff.mpr fun n ↦ (of_prod_nat (top_iff.mp h n)).1
  | coe n => exact (of_prod_nat h).1

/-- The second factor of an `m`-pseudocoherent product module is `m`-pseudocoherent
(Stacks, Tag 064V). -/
theorem of_prod_right {m : ℕ∞} (h : IsPseudoCoherentOver R (M × N) m) :
    IsPseudoCoherentOver R N m := by
  induction m using ENat.recTopCoe with
  | top => exact top_iff.mpr fun n ↦ (of_prod_nat (top_iff.mp h n)).2
  | coe n => exact (of_prod_nat h).2

/-- A product of two modules is `m`-pseudocoherent if and only if both factors are
`m`-pseudocoherent (Stacks, Tag 064V). -/
@[simp]
theorem prod_iff {m : ℕ∞} :
    IsPseudoCoherentOver R (M × N) m ↔
      IsPseudoCoherentOver R M m ∧ IsPseudoCoherentOver R N m :=
  ⟨fun h ↦ ⟨h.of_prod_left, h.of_prod_right⟩, fun ⟨hM, hN⟩ ↦ hM.prod hN⟩

/-- **A direct summand of an `m`-pseudocoherent module is `m`-pseudocoherent.** If `i : M →ₗ[R] N`
and `r : N →ₗ[R] M` satisfy `r ∘ₗ i = id` and `N` is `m`-pseudocoherent, then `M` is
`m`-pseudocoherent (Stacks, Lemma 15.66.6, Tag 064V). -/
theorem of_retract {i : M →ₗ[R] N} {r : N →ₗ[R] M} (hri : r ∘ₗ i = LinearMap.id)
    {m : ℕ∞} (h : IsPseudoCoherentOver R N m) : IsPseudoCoherentOver R M m := by
  have hr (x : M) : r (i x) = x := LinearMap.congr_fun hri x
  let e : (M × ker r) ≃ₗ[R] N :=
    { toFun x := i x.1 + x.2.1
      map_add' x y := by simp [add_add_add_comm]
      map_smul' a x := by simp [smul_add]
      invFun y := (r y, ⟨y - i (r y), by simp [hr]⟩)
      left_inv := fun ⟨x, k, hk⟩ ↦ Prod.ext (by simp [hr, mem_ker.mp hk])
        (Subtype.ext (by simp [hr, mem_ker.mp hk]))
      right_inv y := by simp }
  exact (h.of_equiv e.symm).of_prod_left

end Retract

end TauCeti.Huber.IsPseudoCoherentOver

end
