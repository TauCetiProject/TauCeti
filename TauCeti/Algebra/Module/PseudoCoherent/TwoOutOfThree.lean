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

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory, II: Imperfect period rings*, §1.1,
  Lemma 1.1.5.
* The Stacks Project, Lemma 15.66.2, Tag 064R (with the index negated).
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

end TauCeti.Huber.IsPseudoCoherentOver

end
